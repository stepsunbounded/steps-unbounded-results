/-
HSC/Assembly.lean

The composition-factor layer: monoid containment plus a reciprocal-mass bound implies HS.
-/
import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Criterion
import StepsUnboundedResults.HSC.Extension
import Mathlib.Tactic

open scoped Classical
open Finset

namespace HSC

variable {G : Type*}

section Abstract
variable [Group G] [Finite G]

theorem le_card_of_mem_indexSet {n : ℕ} (h : n ∈ indexSet G) : n ≤ Nat.card G := by
  obtain ⟨hdvd, -⟩ := mem_indexSet.mp h
  exact Nat.le_of_dvd (Nat.card_pos) hdvd

theorem J_le_one_add {A : Finset ℕ} {c : ℚ} (hsub : ∀ n ∈ indexSet G, n ∈ MonoidGen A)
    (hMass : MassBound A c) : J G ≤ 1 + c := by
  classical
  rw [J_eq_one_add]
  have hle :
      ∑ n ∈ (indexSet G).filter (fun n => 1 < n), (1 : ℚ) / n
        ≤ ∑ n ∈ (monoidUpTo A (Nat.card G)).filter (fun n => 1 < n), (1 : ℚ) / n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      exact ⟨mem_monoidUpTo.mpr ⟨le_card_of_mem_indexSet hn.1, hsub n hn.1⟩, hn.2⟩
    · intro n _ _
      exact div_nonneg (zero_le_one' ℚ) (Nat.cast_nonneg n)
  have := hMass (Nat.card G)
  linarith

theorem isHS_of_indexSet_subset {A : Finset ℕ} {c : ℚ}
    (hsub : ∀ n ∈ indexSet G, n ∈ MonoidGen A) (hMass : MassBound A c) (hc : c < 1) :
    IsHS G := by
  refine isHS_of_J_lt_two ?_
  have h := J_le_one_add hsub hMass
  linarith

theorem J_le_mul_J (N : Subgroup G) [N.Normal] :
    J G ≤ J ↥N * J (G ⧸ N) := by
  classical
  have key : ∀ n ∈ indexSet G, ∃ a ∈ indexSet (G ⧸ N), ∃ b ∈ indexSet N, n = a * b :=
    fun n hn => index_mem_mul_indexSet N n hn
  let f : ℕ → ℕ × ℕ := fun n =>
    if h : n ∈ indexSet G then
      (Classical.choose (key n h), Classical.choose (Classical.choose_spec (key n h)).2)
    else (0, 0)
  have hf : ∀ n ∈ indexSet G, n = (f n).1 * (f n).2 := by
    intro n hn
    have h1 := Classical.choose_spec (key n hn)
    have h2 := Classical.choose_spec h1.2
    simp only [f, dif_pos hn]
    exact h2.2
  have hf_inj : Set.InjOn f ↑(indexSet G) := by
    intro m hm n hn hmn
    rw [hf m hm, hf n hn, hmn]
  have hsubset : (indexSet G).image f
      ⊆ (indexSet (G ⧸ N)).product (indexSet N) := by
    intro t ht
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
    have h1 := Classical.choose_spec (key n hn)
    have h2 := Classical.choose_spec h1.2
    simp only [f, dif_pos hn]
    exact Finset.mem_product.mpr ⟨h1.1, h2.1⟩
  have hnonneg : ∀ t ∈ (indexSet (G ⧸ N)).product (indexSet N), t ∉ (indexSet G).image f →
      0 ≤ (1 : ℚ) / (t.1 * t.2) := by
    intro t _ _
    exact div_nonneg (zero_le_one' ℚ) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc J G = ∑ n ∈ indexSet G, (1 : ℚ) / n := rfl
    _ = ∑ n ∈ indexSet G, (1 : ℚ) / ((f n).1 * (f n).2) :=
        Finset.sum_congr rfl fun n hn =>
          by simpa only [Nat.cast_mul] using congrArg (fun m : ℕ => (1 : ℚ) / m) (hf n hn)
    _ = ∑ t ∈ (indexSet G).image f, (1 : ℚ) / (t.1 * t.2) := by
        rw [Finset.sum_image]
        intro m hm n hn hmn
        exact hf_inj hm hn hmn
    _ ≤ ∑ t ∈ (indexSet (G ⧸ N)).product (indexSet N), (1 : ℚ) / (t.1 * t.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    _ = J (G ⧸ N) * J ↥N := by
        refine (Finset.sum_product (indexSet (G ⧸ N)) (indexSet ↥N)
          (fun t : ℕ × ℕ => (1 : ℚ) / (t.1 * t.2))).trans ?_
        simp only [J]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [div_mul_div_comm, one_mul]
    _ = J ↥N * J (G ⧸ N) := mul_comm _ _

end Abstract

section BuiltFrom
variable {S : Type} [Group S] [Finite S] {A : Finset ℕ}

theorem indexSet_subset_monoidGen_of_builtFrom (hS : ∀ n ∈ indexSet S, n ∈ MonoidGen A) :
    ∀ {G : Type} [Group G], BuiltFrom S G → ∀ (hG : Finite G), ∀ n ∈ @indexSet G _ hG,
      n ∈ MonoidGen A := by
  intro G _ hb
  induction hb with
  | iso G e =>
      intro hG n hn
      exact hS n (indexSet_subset_of_mulEquiv e hn)
  | ext G N hN hQ ihN ihQ =>
      intro hG n hn
      haveI : Finite G := hG
      haveI : Finite ↥N := inferInstance
      haveI : Finite (G ⧸ N) := inferInstance
      obtain ⟨a, ha, b, hb', rfl⟩ := index_mem_mul_indexSet N n hn
      exact MonoidGen.mul_mem (ihQ inferInstance a ha) (ihN inferInstance b hb')

theorem isHS_of_builtFrom (hS : ∀ n ∈ indexSet S, n ∈ MonoidGen A) {c : ℚ}
    (hMass : MassBound A c) (hc : c < 1) {G : Type} [Group G] [Finite G]
    (hb : BuiltFrom S G) : IsHS G :=
  isHS_of_indexSet_subset
    (fun n hn => indexSet_subset_monoidGen_of_builtFrom hS hb inferInstance n hn) hMass hc

end BuiltFrom

end HSC
