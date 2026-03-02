#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

WITH_BUILD="false"
if [[ "${1:-}" == "--with-build" ]]; then
  WITH_BUILD="true"
fi

REPO="Th0rgal/verity"
PR_NUMBER="1065"
BRANCH="roadmap/1060-hybrid-migration"

# Mandatory startup sequence.
echo "[1060-pr-sync] gh default repo"
gh repo set-default "$REPO"

echo "[1060-pr-sync] fetch remotes"
git fetch --all --prune

echo "[1060-pr-sync] PR metadata"
gh pr view "$PR_NUMBER" --repo "$REPO" --json state,isDraft,headRefName,baseRefName,url,reviewDecision

echo "[1060-pr-sync] PR checks"
gh pr checks "$PR_NUMBER" --repo "$REPO"

echo "[1060-pr-sync] latest review comments"
gh api "repos/$REPO/pulls/$PR_NUMBER/comments" --paginate --jq '.[-20:] | .[] | "- [" + .user.login + "] " + (.path // "") + ":" + ((.line|tostring) // "") + " :: " + (.body|gsub("\\n";" ")|.[0:180])'

echo "[1060-pr-sync] unresolved review threads"
GRAPHQL_QUERY='query { repository(owner:"Th0rgal", name:"verity") { pullRequest(number:1065) { reviewThreads(first:100) { nodes { isResolved comments(first:1) { nodes { author { login } body path line } } } } } } }'
gh api graphql -f query="$GRAPHQL_QUERY" --jq '.data.repository.pullRequest.reviewThreads.nodes
| map(select(.isResolved == false))
| .[]
| "- [" + (.comments.nodes[0].author.login // "unknown") + "] "
  + ((.comments.nodes[0].path // "") + ":" + ((.comments.nodes[0].line|tostring) // ""))
  + " :: " + ((.comments.nodes[0].body // "") | gsub("\\n";" ") | .[0:180])'

echo "[1060-pr-sync] checkout PR branch"
git checkout "$BRANCH"

echo "[1060-pr-sync] pull latest PR branch"
git pull --ff-only origin "$BRANCH"

echo "[1060-pr-sync] merge origin/main"
git fetch origin main
git merge --no-edit origin/main

if [[ "$WITH_BUILD" == "true" ]]; then
  echo "[1060-pr-sync] run fast gate with build"
  scripts/run_1060_fast_gate.sh --with-build
else
  echo "[1060-pr-sync] run fast gate"
  scripts/run_1060_fast_gate.sh
fi

echo "[1060-pr-sync] PASS"
