import Mathlib

/-!
# Foundation

Small baseline theorem used to verify that the pinned Lean/mathlib project builds
correctly before result-specific formalizations are added.
-/

namespace StepsUnboundedResults

/-- A minimal sanity theorem for the repository's Lean CI. -/
theorem sanity : True := by
  trivial

end StepsUnboundedResults
