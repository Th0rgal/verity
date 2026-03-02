#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

WITH_BUILD="false"
if [[ "${1:-}" == "--with-build" ]]; then
  WITH_BUILD="true"
fi

echo "[1060-pr-fast] gh default repo"
gh repo set-default Th0rgal/verity

echo "[1060-pr-fast] fetch remotes"
git fetch --all --prune

echo "[1060-pr-fast] PR metadata"
gh pr view 1065 --repo Th0rgal/verity --json state,isDraft,headRefName,baseRefName,url,reviewDecision

echo "[1060-pr-fast] PR checks"
gh pr checks 1065 --repo Th0rgal/verity || true

echo "[1060-pr-fast] recent review comments (latest 20)"
gh api repos/Th0rgal/verity/pulls/1065/comments --paginate --jq '.[-20:] | .[] | "- [" + .user.login + "] " + (.path // "") + ":" + ((.line|tostring) // "") + " :: " + (.body|gsub("\\n";" ")|.[0:180])'

echo "[1060-pr-fast] unresolved review threads"
GRAPHQL_QUERY='query { repository(owner:"Th0rgal", name:"verity") { pullRequest(number:1065) { reviewThreads(first:100) { nodes { isResolved comments(first:1) { nodes { author { login } body path line } } } } } } }'
gh api graphql -f query="$GRAPHQL_QUERY" --jq '.data.repository.pullRequest.reviewThreads.nodes
| map(select(.isResolved == false))
| .[]
| "- [" + (.comments.nodes[0].author.login // "unknown") + "] "
  + ((.comments.nodes[0].path // "") + ":" + ((.comments.nodes[0].line|tostring) // ""))
  + " :: " + ((.comments.nodes[0].body // "") | gsub("\\n";" ") | .[0:180])' || true

if [[ "$WITH_BUILD" == "true" ]]; then
  echo "[1060-pr-fast] run fast gate with build"
  scripts/run_1060_fast_gate.sh --with-build
else
  echo "[1060-pr-fast] run fast gate"
  scripts/run_1060_fast_gate.sh
fi

echo "[1060-pr-fast] PASS"
