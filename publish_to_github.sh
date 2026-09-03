#!/usr/bin/env bash
set -euo pipefail

repo='sebastienpalcoux/sqrt6-kissing-bound'
old_repo='sebastienpalcoux/Fusion-Categories'
old_branch='gpt-pro/sqrt6-kissing-certificate'

if ! command -v gh >/dev/null 2>&1; then
  echo 'GitHub CLI (gh) is required: https://cli.github.com/' >&2
  exit 1
fi

gh auth status

if [ ! -d .git ]; then
  git init -b main
fi

git add .
if ! git diff --cached --quiet; then
  login=$(gh api user --jq '.login')
  user_id=$(gh api user --jq '.id')
  display_name=$(gh api user --jq '.name // .login')
  git -c user.name="$display_name" \
      -c user.email="${user_id}+${login}@users.noreply.github.com" \
      commit -m 'Initial dedicated Lean certificate for the sqrt(6) kissing bound'
fi

if gh repo view "$repo" >/dev/null 2>&1; then
  echo "Repository $repo already exists."
else
  gh repo create "$repo" --public --description \
    'Proof and conditional Lean certificate for the universal sqrt(6) kissing-number bound'
fi

if git remote get-url origin >/dev/null 2>&1; then
  git remote set-url origin "https://github.com/$repo.git"
else
  git remote add origin "https://github.com/$repo.git"
fi

git push -u origin main

# Wait until the push-triggered workflow appears, then require it to pass.
run_id=''
for _ in $(seq 1 30); do
  run_id=$(gh run list --repo "$repo" --workflow lean.yml --limit 1 \
    --json databaseId --jq '.[0].databaseId // empty')
  [ -n "$run_id" ] && break
  sleep 2
done

if [ -z "$run_id" ]; then
  echo 'No Lean workflow run appeared; the old branch has not been deleted.' >&2
  exit 1
fi

gh run watch "$run_id" --repo "$repo" --exit-status

# Delete the temporary source branch only after the new repository passes CI.
gh api --method DELETE \
  "repos/$old_repo/git/refs/heads/$old_branch"

echo "Moved successfully to https://github.com/$repo"
