/-
HSC/SolvableReduction.lean

Result **R006** (Steps Unbounded), the reduction theorem:

> If `LI_p(Q)` holds for every finite solvable group `Q` and every prime `p`, then every finite
> solvable group is HS.

The page proves this through R004's lifting theorem.  In this development a *stronger* input is
already available: `HSC.isHS_of_licosets` shows `LI_p(Q) ⟹ Q` is HS directly, for **every** finite
group `Q` and **one** prime `p` (the covering relation is an `𝔽_p`-relation for every `p`, so a
single prime suffices).  The reduction therefore needs no induction and no lifting step: apply the
hypothesis to `G` itself.

The hypothesis remains exactly what R006 leaves open (its range is a computation, not a theorem);
what is unconditional here is the implication.
-/
import StepsUnboundedResults.HSC.Lifting
import Mathlib.Tactic

open scoped Classical

namespace HSC

/-- **R006, the solvable-case reduction**: if `LI_p(Q)` holds for every finite solvable group `Q`
and every prime `p`, then every finite solvable group is HS.

No lifting theorem is needed in this development: `isHS_of_licosets` consumes `LI_p` of the group
itself, so the reduction is immediate (and works for non-solvable `G` as well, whenever the
hypothesis is available for it). -/
theorem isHS_of_isSolvable_of_licosets
    (h : ∀ (Q : Type) [Group Q] [Finite Q], IsSolvable Q → ∀ (p : ℕ), p.Prime → LICosets p Q)
    {G : Type} [Group G] [Finite G] (hG : IsSolvable G) : IsHS G :=
  isHS_of_licosets Nat.prime_two (h G hG 2 Nat.prime_two)

/-- The same reduction in its "one prime" form: a single prime per group suffices. -/
theorem isHS_of_forall_licosets
    (h : ∀ (Q : Type) [Group Q] [Finite Q], ∃ p : ℕ, p.Prime ∧ LICosets p Q)
    {G : Type} [Group G] [Finite G] : IsHS G := by
  obtain ⟨p, hp, hLI⟩ := h G
  exact isHS_of_licosets hp hLI

end HSC
