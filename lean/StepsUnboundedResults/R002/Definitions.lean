import Mathlib

/-!
# Base-two Wieferich definitions

This module contains only definitions and elementary interface lemmas.  Hard
or conditional research statements belong in explicitly named target modules.
-/

namespace StepsUnboundedResults.R002

/-- `p` is a base-two Wieferich number in the elementary divisibility sense. -/
def IsWieferich (p : ℕ) : Prop := p ^ 2 ∣ 2 ^ (p - 1) - 1

instance instDecidableIsWieferich (p : ℕ) : Decidable (IsWieferich p) := by
  unfold IsWieferich
  infer_instance

/-- A coprime square-divisor certificate with base `2`. -/
def IsCoprimeSquareCertificate (N L : ℕ) : Prop :=
  1 < N ∧ Nat.Coprime N L ∧ N ^ 2 ∣ 2 ^ L - 1

end StepsUnboundedResults.R002
