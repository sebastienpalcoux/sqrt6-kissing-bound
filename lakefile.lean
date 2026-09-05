import Lake

open Lake DSL

package «sqrt6-kissing-bound» where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib Sqrt6KissingBound where
  roots := #[`Sqrt6KissingBound]

lean_lib Challenge where
  roots := #[`Challenge]

lean_lib Solution where
  roots := #[`Solution]
