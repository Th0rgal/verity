#!/bin/bash
# Script to create GitHub issues for Layer 3 statement equivalence proofs
# Usage: ./scripts/create_layer3_issues.sh

set -e

REPO="Th0rgal/dumbcontracts"

echo "Creating GitHub issues for Layer 3 statement equivalence proofs..."
echo "Repository: $REPO"
echo ""

# Check if gh is installed and authenticated
if ! command -v gh &> /dev/null; then
    echo "Error: GitHub CLI (gh) is not installed."
    echo "Install from: https://cli.github.com/"
    exit 1
fi

# Check if gh is authenticated
if ! gh auth status &> /dev/null; then
    echo "Error: GitHub CLI is not authenticated."
    echo "Run: gh auth login"
    exit 1
fi

# Fetch existing issues to check for duplicates
echo "Fetching existing Layer 3 issues..."
EXISTING_ISSUES=$(gh issue list --repo "$REPO" --label "layer-3" --state all --limit 1000 --json title --jq '.[].title')
# Count issues - use wc -l to avoid grep -c exit code issues with set -e
ISSUE_COUNT=$(echo "$EXISTING_ISSUES" | wc -l | tr -d ' ')
echo "Found $ISSUE_COUNT existing Layer 3 issues"
echo ""

# Array of statement proofs to create issues for
declare -a statements=(
    "1:Variable Assignment:assign_equiv:Low:1h:None:70"
    "2:Storage Load:storageLoad_equiv:Low:1h:None:107"
    "3:Storage Store:storageStore_equiv:Low:1h:None:127"
    "4:Mapping Load:mappingLoad_equiv:Medium:2-4h:Mapping slot calculation lemma:147"
    "5:Mapping Store:mappingStore_equiv:Medium:2-4h:Mapping slot calculation lemma:167"
    "6:Conditional (if):conditional_equiv:Medium-High:4-8h:Recursive equivalence for branches:187"
    "7:Return:return_equiv:Low:1-2h:None:218"
    "8:Revert:revert_equiv:Low-Medium:2-3h:Rollback state alignment:236"
)

# Function to create issue
create_issue() {
    local num=$1
    local name=$2
    local theorem=$3
    local difficulty=$4
    local effort=$5
    local deps=$6
    local line=$7

    local title="[Layer 3] Prove ${name,,} statement equivalence"

    # Check if issue already exists (exact match)
    if echo "$EXISTING_ISSUES" | grep -qFx "$title"; then
        echo "⊘ Issue already exists: ${title}"
        echo "  Skipping..."
        echo ""
        return 0
    fi

    local body=$(cat <<EOF
## Statement Type

**Statement**: \`${name}\`
**Theorem**: \`${theorem}\`
**File**: \`Compiler/Proofs/YulGeneration/StatementEquivalence.lean:${line}\`

## Description

Prove that executing ${name,,} statements in IR matches executing them in Yul when states are aligned.

**IR Semantics**: See \`Compiler/Proofs/IRGeneration/IRInterpreter.lean\`
**Yul Semantics**: See \`Compiler/Proofs/YulGeneration/Semantics.lean\`

## Proof Strategy

See theorem stub in \`StatementEquivalence.lean\` for detailed proof strategy and the worked example (variable assignment) for proof pattern.

## Difficulty & Effort

- **Difficulty**: ${difficulty}
- **Estimated Effort**: ${effort}
- **Dependencies**: ${deps}

## Acceptance Criteria

- [ ] Replace \`sorry\` in theorem stub with complete proof
- [ ] Add tests in \`Compiler/Proofs/YulGeneration/SmokeTests.lean\` demonstrating equivalence
- [ ] Update roadmap progress table (docs/ROADMAP.md) to mark as ✅ Complete
- [ ] CI passes (all proofs check, no new sorries)
- [ ] PR review approved

## References

- **Roadmap**: \`docs/ROADMAP.md\` - Layer 3 section
- **IR Semantics**: \`Compiler/Proofs/IRGeneration/IRInterpreter.lean\`
- **Yul Semantics**: \`Compiler/Proofs/YulGeneration/Semantics.lean\`
- **Equivalence Definitions**: \`Compiler/Proofs/YulGeneration/Equivalence.lean\`
- **Theorem Stub**: \`Compiler/Proofs/YulGeneration/StatementEquivalence.lean:${line}\`
- **Preservation Theorem**: \`Compiler/Proofs/YulGeneration/Preservation.lean\`

## Getting Started

1. Read the roadmap context in \`docs/ROADMAP.md\`
2. Review the theorem stub in \`StatementEquivalence.lean:${line}\`
3. Study the worked example (variable assignment) for proof patterns
4. Review IR and Yul semantics for this statement type
5. Replace \`sorry\` with your proof
6. Add smoke tests to verify your proof works
7. Submit PR referencing this issue

## Questions?

Ask in the PR or open a discussion. See \`Compiler/Proofs/README.md\` for proof development guide.

---

**Part of**: Layer 3 (IR → Yul) verification completion
**Blocks**: End-to-end verification EDSL → Bytecode
**Related**: All 8 statement proofs must be completed before composition theorem
EOF
)

    echo "Creating issue #${num}: ${title}"

    # Create the issue with appropriate labels
    local labels="layer-3,proof,lean,help-wanted"
    if [[ "${difficulty,,}" == "low" ]]; then
        labels="${labels},good-first-issue"
    fi

    gh issue create \
        --repo "$REPO" \
        --title "$title" \
        --body "$body" \
        --label "$labels"

    echo "✓ Issue created"
    echo ""
}

# Create issues for each statement
for stmt in "${statements[@]}"; do
    IFS=':' read -r num name theorem difficulty effort deps line <<< "$stmt"
    create_issue "$num" "$name" "$theorem" "$difficulty" "$effort" "$deps" "$line"

    # Rate limit protection
    sleep 2
done

echo "Done!"
echo ""
echo "Summary: Script is idempotent - existing issues are skipped."
echo ""
echo "Next steps:"
echo "1. Review created issues on GitHub"
echo "2. Add milestone: 'Layer 3 Completion'"
echo "3. Consider pinning high-priority issues"
echo "4. Share with potential contributors"
