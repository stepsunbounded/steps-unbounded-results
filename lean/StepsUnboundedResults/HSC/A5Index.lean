/-
HSC/A5Index.lean

The subgroup index set of `A₅` is contained in the explicit nine-element set
`a5IndexSet = {1, 5, 6, 10, 12, 15, 20, 30, 60}`.
-/
import StepsUnboundedResults.HSC.Defs
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.GroupAction.Quotient

open scoped Classical

namespace HSC

theorem nat_card_alt5 : Nat.card Alt5 = 60 := by
  rw [Alt5, nat_card_alternatingGroup]
  norm_num [Nat.card_fin, Nat.factorial]

theorem eq_top_or_card_le_factorial {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (H : Subgroup G) : H = ⊤ ∨ Nat.card G ≤ H.index.factorial := by
  rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with h | h
  · right
    have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
      rw [← Subgroup.normalCore_eq_ker]
      exact h
    have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ H)) :=
      (MonoidHom.ker_eq_bot_iff (MulAction.toPermHom G (G ⧸ H))).mp hker
    calc Nat.card G ≤ Nat.card (Equiv.Perm (G ⧸ H)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = (Nat.card (G ⧸ H)).factorial := Nat.card_perm
      _ = H.index.factorial := by rw [Subgroup.index_eq_card]
  · left
    exact top_le_iff.mp (h ▸ Subgroup.normalCore_le H)

theorem mem_a5IndexSet_of_dvd {n : ℕ} (h : n ∣ 60) (h5 : 5 ≤ n) : n ∈ a5IndexSet := by
  have h60 : n ≤ 60 := Nat.le_of_dvd (by norm_num) h
  have key : ∀ m ∈ Finset.range 61, m ∣ 60 → 5 ≤ m → m ∈ a5IndexSet := by decide
  exact key n (Finset.mem_range.mpr (Nat.lt_succ_of_le h60)) h h5

theorem a5_indexSet_subset : ∀ n, n ∈ indexSet Alt5 → n ∈ a5IndexSet := by
  intro n hn
  rw [mem_indexSet] at hn
  obtain ⟨hdvd, H, hHi⟩ := hn
  have hcard : Nat.card Alt5 = 60 := nat_card_alt5
  rcases eq_top_or_card_le_factorial H with htop | hfac
  · have hone : H.index = 1 := by rw [htop]; exact Subgroup.index_top
    rw [← hHi, hone]
    simp [a5IndexSet]
  · have hfac' : 60 ≤ n.factorial := by
      rw [hcard, hHi] at hfac
      exact hfac
    have hdvd60 : n ∣ 60 := by rw [← hcard]; exact hdvd
    have h5 : 5 ≤ n := by
      by_contra hlt
      push_neg at hlt
      interval_cases n <;> norm_num [Nat.factorial] at hfac'
    exact mem_a5IndexSet_of_dvd hdvd60 h5

end HSC
