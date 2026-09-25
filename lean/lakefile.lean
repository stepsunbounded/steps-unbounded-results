import Lake
open Lake DSL

package «steps-unbounded-results» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "v4.32.0"

lean_lib StepsUnboundedResults where
  globs := #[.submodules `StepsUnboundedResults]
