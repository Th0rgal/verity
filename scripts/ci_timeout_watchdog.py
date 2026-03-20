#!/usr/bin/env python3
"""Warn when recent GitHub Actions jobs trend too close to their timeouts."""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path

from workflow_jobs import extract_job_body, extract_top_level_jobs, strip_yaml_inline_comment

ROOT = Path(__file__).resolve().parents[1]
VERIFY_YML = ROOT / ".github" / "workflows" / "verify.yml"
ISO_8601 = "%Y-%m-%dT%H:%M:%SZ"


@dataclass(frozen=True)
class Sample:
    run_id: int
    title: str
    duration_minutes: float
    timeout_minutes: int
    ratio: float
    conclusion: str


def _extract_top_level_job_value(job_body: str, key: str) -> str | None:
    for line in job_body.splitlines():
        if not line.strip():
            continue
        if len(line) - len(line.lstrip(" ")) != 4:
            continue
        match = re.match(rf"^\s*{re.escape(key)}:\s*(?P<value>.*?)\s*$", line)
        if match:
            raw = strip_yaml_inline_comment(match.group("value"))
            return raw or ""
    return None


def load_timeouts(workflow_path: Path = VERIFY_YML) -> dict[str, int]:
    workflow_text = workflow_path.read_text(encoding="utf-8")
    timeouts: dict[str, int] = {}
    for job in extract_top_level_jobs(workflow_text, workflow_path):
        raw = _extract_top_level_job_value(extract_job_body(workflow_text, job, workflow_path), "timeout-minutes")
        if raw is None:
            continue
        timeouts[job] = int(raw)
    return timeouts


def _job_name_matches(job_name: str, workflow_job: str) -> bool:
    return job_name == workflow_job or job_name.startswith(f"{workflow_job} ")


def _parse_timestamp(raw: str | None) -> datetime | None:
    if not raw:
        return None
    return datetime.strptime(raw, ISO_8601)


def _duration_minutes(started_at: str | None, completed_at: str | None) -> float | None:
    started = _parse_timestamp(started_at)
    completed = _parse_timestamp(completed_at)
    if started is None or completed is None:
        return None
    return max((completed - started).total_seconds() / 60.0, 0.0)


class GitHubActionsClient:
    def __init__(self, repo: str, token: str) -> None:
        self.repo = repo
        self.base_url = f"https://api.github.com/repos/{repo}"
        self.headers = {
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {token}",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "verity-ci-timeout-watchdog",
        }

    def get_json(self, path: str, params: dict[str, str | int] | None = None) -> dict:
        url = self.base_url + path
        if params:
            url += "?" + urllib.parse.urlencode(params)
        req = urllib.request.Request(url, headers=self.headers)
        with urllib.request.urlopen(req) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def list_workflow_runs(self, workflow: str, branch: str, limit: int) -> list[dict]:
        payload = self.get_json(
            f"/actions/workflows/{workflow}/runs",
            {"branch": branch, "status": "completed", "per_page": limit},
        )
        return payload.get("workflow_runs", [])

    def list_run_jobs(self, run_id: int) -> list[dict]:
        jobs: list[dict] = []
        page = 1
        while True:
            payload = self.get_json(f"/actions/runs/{run_id}/jobs", {"per_page": 100, "page": page})
            jobs.extend(payload.get("jobs", []))
            if len(jobs) >= payload.get("total_count", 0) or not payload.get("jobs"):
                return jobs
            page += 1


def collect_timeout_risk_samples(
    runs: list[dict],
    run_jobs: dict[int, list[dict]],
    tracked_timeouts: dict[str, int],
) -> dict[str, list[Sample]]:
    samples: dict[str, list[Sample]] = {job: [] for job in tracked_timeouts}
    for run in runs:
        run_id = run["id"]
        for workflow_job, timeout in tracked_timeouts.items():
            matching_jobs = [
                job for job in run_jobs.get(run_id, []) if _job_name_matches(job.get("name", ""), workflow_job)
            ]
            for job in matching_jobs:
                duration = _duration_minutes(job.get("started_at"), job.get("completed_at"))
                if duration is None:
                    continue
                samples[workflow_job].append(
                    Sample(
                        run_id=run_id,
                        title=run.get("display_title", ""),
                        duration_minutes=duration,
                        timeout_minutes=timeout,
                        ratio=duration / timeout,
                        conclusion=job.get("conclusion") or "unknown",
                    )
                )
    return samples


def summarize_risk(
    samples: dict[str, list[Sample]],
    *,
    threshold: float,
    min_risk_samples: int,
) -> list[str]:
    warnings: list[str] = []
    for job_name, job_samples in samples.items():
        risky = [sample for sample in job_samples if sample.ratio >= threshold]
        if len(risky) < min_risk_samples:
            continue
        latest = risky[0]
        warnings.append(
            f"{job_name}: {len(risky)}/{len(job_samples)} recent samples hit >= {threshold:.0%} "
            f"of timeout; latest run {latest.run_id} used {latest.duration_minutes:.1f}/"
            f"{latest.timeout_minutes} minutes ({latest.ratio:.0%}, {latest.conclusion})"
        )
    return warnings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="owner/name GitHub repository")
    parser.add_argument("--workflow", default="verify.yml", help="Workflow file name")
    parser.add_argument("--branch", default="main", help="Branch to inspect")
    parser.add_argument("--limit-runs", type=int, default=8, help="How many recent runs to inspect")
    parser.add_argument("--threshold", type=float, default=0.8, help="Warn at or above this timeout ratio")
    parser.add_argument(
        "--min-risk-samples",
        type=int,
        default=2,
        help="Minimum number of high-ratio samples before warning",
    )
    parser.add_argument(
        "--min-timeout-minutes",
        type=int,
        default=20,
        help="Only inspect workflow jobs at or above this timeout",
    )
    parser.add_argument(
        "--fail-on-risk",
        action="store_true",
        help="Exit non-zero when risk warnings are found",
    )
    args = parser.parse_args()

    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if not token:
        print("GH_TOKEN or GITHUB_TOKEN is required", file=sys.stderr)
        return 1

    tracked_timeouts = {
        job: timeout
        for job, timeout in load_timeouts().items()
        if timeout >= args.min_timeout_minutes
    }
    if not tracked_timeouts:
        print("No workflow jobs met the timeout threshold; nothing to inspect.")
        return 0

    client = GitHubActionsClient(args.repo, token)
    try:
        runs = client.list_workflow_runs(args.workflow, args.branch, args.limit_runs)
        run_jobs = {run["id"]: client.list_run_jobs(run["id"]) for run in runs}
    except urllib.error.URLError as exc:
        print(f"::warning::ci-timeout-watchdog could not query GitHub Actions: {exc}", file=sys.stderr)
        return 0

    samples = collect_timeout_risk_samples(runs, run_jobs, tracked_timeouts)
    warnings = summarize_risk(
        samples,
        threshold=args.threshold,
        min_risk_samples=args.min_risk_samples,
    )
    if not warnings:
        print(
            f"ci-timeout-watchdog: no jobs exceeded {args.threshold:.0%} timeout usage "
            f"in at least {args.min_risk_samples} of the last {len(runs)} runs"
        )
        return 0

    for line in warnings:
        print(f"::warning::{line}")
        print(line)

    return 1 if args.fail_on_risk else 0


if __name__ == "__main__":
    raise SystemExit(main())
