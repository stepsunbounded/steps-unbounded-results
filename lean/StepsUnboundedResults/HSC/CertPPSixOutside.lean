import StepsUnboundedResults.HSC.CertPPSixArithmetic

open scoped BigOperators
open Finset

namespace HSC.CertPP

variable {G : Type*} [Group G] [Fintype G]

theorem outside_sieve' {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (D : ι → Set G)
    (H : Set G) (m : ι) (hm : m ∈ s)
    (hcover : ∀ g : G, g ∉ H → Nat.card {i : ι // g ∈ D i} ≠ 1)
    (hset : ∀ i ∉ s, D i ⊆ H) :
    (D m \ H).ncard ≤ ∑ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H)).ncard := by
  classical
  have hsub : (D m \ H) ⊆ ⋃ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H)) := by
    intro g hg
    have hg1 : 1 ≤ Nat.card {i : ι // g ∈ D i} := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨m, hg.1⟩⟩
    have hg2 : 2 ≤ Nat.card {i : ι // g ∈ D i} := by
      have := hcover g hg.2; omega
    rw [Nat.card_eq_fintype_card] at hg2
    have hmem : ∃ a ∈ s, g ∈ D a ∧ a ≠ m := by
      by_contra hc
      push Not at hc
      have hkey : ∀ x : {i : ι // g ∈ D i}, x.1 = m := by
        rintro ⟨i, hi⟩
        by_contra him
        have his : i ∈ s := by
          by_contra hs
          exact hg.2 (hset i hs hi)
        exact absurd (hc i his hi) him
      have hcard : Nat.card {i : ι // g ∈ D i} ≤ 1 := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b =>
          Subtype.ext ((hkey a).trans (hkey b).symm)⟩
      rw [Nat.card_eq_fintype_card] at hcard
      exact absurd hcard (by omega)
    obtain ⟨a, has, hga, ham⟩ := hmem
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr
      ⟨Finset.mem_erase.mpr ⟨ham, has⟩, hg, ⟨hga, hg.2⟩⟩⟩
  calc (D m \ H).ncard
      ≤ (⋃ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H))).ncard := Set.ncard_le_ncard hsub
    _ ≤ ∑ n ∈ s.erase m, ((D m \ H) ∩ (D n \ H)).ncard := ncard_iUnion_finset_le _ _

end HSC.CertPP
