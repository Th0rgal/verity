#!/usr/bin/env python3
"""Profile a CI command with host-level resource samples.

The script is intentionally dependency-free so it can run on self-hosted
GitHub runners and ad-hoc hosts. It records wall time, GNU time output when
available, CPU/iowait samples from /proc/stat, memory from /proc/meminfo, disk
I/O deltas from /proc/diskstats, optional NVIDIA GPU utilization from
nvidia-smi, and the command log.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import statistics
import subprocess
import sys
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


CPU_FIELDS = ("user", "nice", "system", "idle", "iowait", "irq", "softirq", "steal")

@dataclass
class CpuSnapshot:
    total: int
    idle: int
    iowait: int


def read_cpu_snapshot() -> CpuSnapshot:
    parts = Path("/proc/stat").read_text(encoding="utf-8").splitlines()[0].split()
    values = {field: int(parts[index + 1]) for index, field in enumerate(CPU_FIELDS)}
    total = sum(values.values())
    idle = values["idle"] + values["iowait"]
    return CpuSnapshot(total=total, idle=idle, iowait=values["iowait"])


def cpu_delta(prev: CpuSnapshot, cur: CpuSnapshot) -> dict[str, float]:
    total = max(cur.total - prev.total, 1)
    idle = cur.idle - prev.idle
    iowait = cur.iowait - prev.iowait
    return {
        "cpu_percent": max(0.0, min(100.0, 100.0 * (1.0 - idle / total))),
        "iowait_percent": max(0.0, min(100.0, 100.0 * iowait / total)),
    }


def read_meminfo() -> dict[str, int]:
    data: dict[str, int] = {}
    for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
        key, raw_value = line.split(":", 1)
        value = raw_value.strip().split()[0]
        data[key] = int(value)
    return data


def read_diskstats() -> dict[str, dict[str, int]]:
    stats: dict[str, dict[str, int]] = {}
    for line in Path("/proc/diskstats").read_text(encoding="utf-8").splitlines():
        parts = line.split()
        if len(parts) < 14:
            continue
        name = parts[2]
        if name.startswith(("loop", "ram", "zram")):
            continue
        stats[name] = {
            "reads_completed": int(parts[3]),
            "read_sectors": int(parts[5]),
            "writes_completed": int(parts[7]),
            "write_sectors": int(parts[9]),
            "io_ms": int(parts[12]),
        }
    return stats


def disk_delta(before: dict[str, dict[str, int]], after: dict[str, dict[str, int]]) -> dict[str, Any]:
    devices: dict[str, dict[str, float]] = {}
    total_read_sectors = 0
    total_write_sectors = 0
    total_io_ms = 0
    for name, end in after.items():
        start = before.get(name)
        if start is None:
            continue
        read_sectors = max(0, end["read_sectors"] - start["read_sectors"])
        write_sectors = max(0, end["write_sectors"] - start["write_sectors"])
        io_ms = max(0, end["io_ms"] - start["io_ms"])
        if read_sectors or write_sectors or io_ms:
            devices[name] = {
                "read_mb": read_sectors * 512 / 1_000_000,
                "write_mb": write_sectors * 512 / 1_000_000,
                "io_ms": io_ms,
            }
            total_read_sectors += read_sectors
            total_write_sectors += write_sectors
            total_io_ms += io_ms
    return {
        "read_mb": total_read_sectors * 512 / 1_000_000,
        "write_mb": total_write_sectors * 512 / 1_000_000,
        "io_ms": total_io_ms,
        "devices": devices,
    }


def read_gpu_sample() -> dict[str, float] | None:
    if shutil.which("nvidia-smi") is None:
        return None
    query = "utilization.gpu,utilization.memory,power.draw"
    result = subprocess.run(
        ["nvidia-smi", f"--query-gpu={query}", "--format=csv,noheader,nounits"],
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0 or not result.stdout.strip():
        return None
    first = result.stdout.splitlines()[0]
    values = [part.strip() for part in first.split(",")]
    if len(values) < 3:
        return None
    parsed: list[float] = []
    for value in values[:3]:
        try:
            parsed.append(float(value))
        except ValueError:
            parsed.append(0.0)
    return {"gpu_percent": parsed[0], "gpu_mem_percent": parsed[1], "gpu_power_w": parsed[2]}


def summarize(values: list[float]) -> dict[str, float]:
    if not values:
        return {"avg": 0.0, "max": 0.0}
    return {"avg": statistics.fmean(values), "max": max(values)}


def parse_gnu_time(log_text: str) -> dict[str, str]:
    parsed: dict[str, str] = {}
    has_markers = "PROFILE_CI_RESOURCES_TIME_BEGIN" in log_text
    in_block = not has_markers
    for line in log_text.splitlines():
        if line == "PROFILE_CI_RESOURCES_TIME_BEGIN":
            in_block = True
            continue
        if line == "PROFILE_CI_RESOURCES_TIME_END":
            in_block = False
            continue
        if not in_block:
            continue
        if ": " not in line:
            continue
        key, value = line.rsplit(": ", 1)
        parsed[key.strip()] = value.strip()
    return parsed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True, help="Short benchmark name.")
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--interval", type=float, default=1.0)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    if args.command and args.command[0] == "--":
        args.command = args.command[1:]
    if not args.command:
        raise SystemExit("missing command after --")

    args.output_dir.mkdir(parents=True, exist_ok=True)
    log_path = args.output_dir / f"{args.name}.log"
    json_path = args.output_dir / f"{args.name}.json"
    time_path = args.output_dir / f"{args.name}.time"

    command = args.command
    if shutil.which("/usr/bin/time"):
        command = ["/usr/bin/time", "-v", "-o", str(time_path), *command]

    samples: list[dict[str, float]] = []
    stop = threading.Event()
    start_cpu = read_cpu_snapshot()
    last_cpu = start_cpu
    start_mem = read_meminfo()
    start_disk = read_diskstats()

    def sampler() -> None:
        nonlocal last_cpu
        while not stop.wait(args.interval):
            cur_cpu = read_cpu_snapshot()
            cpu = cpu_delta(last_cpu, cur_cpu)
            last_cpu = cur_cpu
            mem = read_meminfo()
            sample = {
                **cpu,
                "mem_used_mb": (mem["MemTotal"] - mem["MemAvailable"]) / 1024,
            }
            gpu = read_gpu_sample()
            if gpu is not None:
                sample.update(gpu)
            samples.append(sample)

    thread = threading.Thread(target=sampler, daemon=True)
    thread.start()

    start = time.perf_counter()
    with log_path.open("w", encoding="utf-8") as log_file:
        process = subprocess.Popen(
            command,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            start_new_session=True,
        )
        assert process.stdout is not None
        for line in process.stdout:
            sys.stdout.write(line)
            log_file.write(line)
        returncode = process.wait()
    elapsed = time.perf_counter() - start
    stop.set()
    thread.join(timeout=2.0)

    end_mem = read_meminfo()
    end_disk = read_diskstats()
    time_text = time_path.read_text(encoding="utf-8", errors="replace") if time_path.exists() else ""

    summary = {
        "name": args.name,
        "command": args.command,
        "returncode": returncode,
        "elapsed_seconds": elapsed,
        "sample_count": len(samples),
        "cpu_percent": summarize([sample["cpu_percent"] for sample in samples]),
        "iowait_percent": summarize([sample["iowait_percent"] for sample in samples]),
        "mem_used_mb": {
            "start": (start_mem["MemTotal"] - start_mem["MemAvailable"]) / 1024,
            "end": (end_mem["MemTotal"] - end_mem["MemAvailable"]) / 1024,
            **summarize([sample["mem_used_mb"] for sample in samples]),
        },
        "disk": disk_delta(start_disk, end_disk),
        "gpu_percent": summarize([sample["gpu_percent"] for sample in samples if "gpu_percent" in sample]),
        "gpu_mem_percent": summarize(
            [sample["gpu_mem_percent"] for sample in samples if "gpu_mem_percent" in sample]
        ),
        "gpu_power_w": summarize([sample["gpu_power_w"] for sample in samples if "gpu_power_w" in sample]),
        "gnu_time": parse_gnu_time(time_text),
        "log_path": str(log_path),
        "time_path": str(time_path) if time_path.exists() else None,
    }
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True), encoding="utf-8")
    print(f"Wrote {json_path}")
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())
