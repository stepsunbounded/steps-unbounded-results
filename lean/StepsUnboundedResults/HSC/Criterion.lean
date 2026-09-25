/-
HSC/Criterion.lean

Lemma 2.1(1) of Garonzi–Margolis, *The Herzog–Schönheim conjecture for simple and symmetric
groups* (arXiv 2509.25118): if `J(G) < 2` then `G` is HS.

The proof is the paper's: a coset partition gives `∑ 1/[G:Hᵢ] = 1`; if all the indices were
distinct they would be distinct elements of `I(G) \ {1}`, so `1 = ∑ 1/[G:Hᵢ] ≤ J(G) - 1 < 1`.
-/
import StepsUnboundedResults.HSC.Defs
import Mathlib.Tactic

open scoped Classical
open Finset

namespace HSC

variable {G : Type*}

section Finite

variable [Group G] [Finite G]

theorem one_mem_indexSet : 1 ∈ indexSet G := by
  simpa using index_mem_indexSet G (⊤ : Subgroup G)

theorem ne_zero_of_mem_indexSet {n : ℕ} (h : n ∈ indexSet G) : n ≠ 0 := by
  obtain ⟨hdvd, -⟩ := mem_indexSet.mp h
  rintro rfl
  rw [Nat.zero_dvd] at hdvd
  exact (Nat.card_ne_zero.mpr ⟨⟨1⟩, ‹Finite G›⟩) hdvd

theorem one_le_of_mem_indexSet {n : ℕ} (h : n ∈ indexSet G) : 1 ≤ n :=
  Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_indexSet h)

theorem eq_one_or_one_lt_of_mem_indexSet {n : ℕ} (h : n ∈ indexSet G) : n = 1 ∨ 1 < n := by
  rcases Nat.eq_or_lt_of_le (one_le_of_mem_indexSet h) with h1 | h1
  · exact Or.inl h1.symm
  · exact Or.inr h1

theorem J_eq_one_add :
    J G = 1 + ∑ n ∈ (indexSet G).filter (fun n => 1 < n), (1 : ℚ) / n := by
  classical
  have h1 : 1 ∈ indexSet G := one_mem_indexSet
  have hfilter : (indexSet G).filter (fun n => 1 < n) = (indexSet G).erase 1 := by
    ext n
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨h, hlt⟩
      exact ⟨hlt.ne', h⟩
    · rintro ⟨hne, hmem⟩
      refine ⟨hmem, ?_⟩
      rcases eq_one_or_one_lt_of_mem_indexSet hmem with h | h
      · exact absurd h hne
      · exact h
  rw [J, ← Finset.sum_erase_add _ _ h1, hfilter, one_div]
  ring

omit [Finite G] in
theorem natCard_leftCoset (x : G) (H : Subgroup G) :
    Nat.card ↥(leftCoset x H) = Nat.card ↥H := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun g => ⟨x⁻¹ * (g : G), g.2⟩
      invFun := fun h => ⟨x * (h : G), mem_leftCoset.mpr (by simp [h.2])⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro g
    ext
    simp
  · intro h
    ext
    simp

theorem card_eq_sum_card (P : CosetPartition G) :
    Nat.card G = ∑ i : P.ι, Nat.card ↥(P.H i) := by
  classical
  let f : G → Σ i : P.ι, ↥(leftCoset (P.x i) (P.H i)) :=
    fun g => ⟨Classical.choose (P.cover g), g, Classical.choose_spec (P.cover g)⟩
  have hf_apply : ∀ g : G,
      f g = ⟨Classical.choose (P.cover g), g, Classical.choose_spec (P.cover g)⟩ := fun g => rfl
  have hf_inj : Function.Injective f := by
    intro g g' h
    exact congrArg (fun t : Σ i : P.ι, ↥(leftCoset (P.x i) (P.H i)) => (t.2 : G)) h
  have hf_surj : Function.Surjective f := by
    rintro ⟨i, g, hg⟩
    have hchoose : Classical.choose (P.cover g) = i := by
      by_contra hne
      have h1 : g ∈ leftCoset (P.x (Classical.choose (P.cover g)))
          (P.H (Classical.choose (P.cover g))) := Classical.choose_spec (P.cover g)
      have h2 : g ∈ leftCoset (P.x i) (P.H i) := hg
      have hd := P.disjoint (Classical.choose (P.cover g)) i hne
      have hbot : g ∈ (⊥ : Set G) := hd.le_bot ⟨h1, h2⟩
      simp at hbot
    refine ⟨g, ?_⟩
    rw [hf_apply g]
    cases hchoose
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext rfl))
  have hcard : Nat.card G = Nat.card (Σ i : P.ι, ↥(leftCoset (P.x i) (P.H i))) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [hcard, Nat.card_sigma]
  exact Finset.sum_congr rfl fun i _ => natCard_leftCoset (P.x i) (P.H i)

theorem sum_inv_index_eq_one (P : CosetPartition G) :
    ∑ i : P.ι, (1 : ℚ) / (P.H i).index = 1 := by
  classical
  have hGne : (Nat.card G : ℚ) ≠ 0 := by
    exact_mod_cast Nat.card_ne_zero.mpr ⟨⟨1⟩, ‹Finite G›⟩
  have hterm : ∀ i : P.ι, (1 : ℚ) / (P.H i).index = (Nat.card ↥(P.H i) : ℚ) / Nat.card G := by
    intro i
    have hidx : ((P.H i).index : ℚ) ≠ 0 := by
      have : (P.H i).index ≠ 0 :=
        Subgroup.index_ne_zero_of_finite (G := G) (H := P.H i)
      exact_mod_cast this
    have hcard : ((P.H i).index : ℚ) * (Nat.card ↥(P.H i) : ℚ) = (Nat.card G : ℚ) := by
      exact_mod_cast Subgroup.index_mul_card (P.H i)
    field_simp
    linarith [hcard]
  calc ∑ i : P.ι, (1 : ℚ) / (P.H i).index
      = ∑ i : P.ι, (Nat.card ↥(P.H i) : ℚ) / Nat.card G := Finset.sum_congr rfl fun i _ => hterm i
    _ = (∑ i : P.ι, (Nat.card ↥(P.H i) : ℚ)) / Nat.card G := (Finset.sum_div _ _ _).symm
    _ = (Nat.card G : ℚ) / Nat.card G := by
          rw [← Nat.cast_sum, ← card_eq_sum_card P]
    _ = 1 := div_self hGne

theorem sum_inv_index_le (P : CosetPartition G)
    (hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index) :
    ∑ i : P.ι, (1 : ℚ) / (P.H i).index
      ≤ ∑ n ∈ (indexSet G).filter (fun n => 1 < n), (1 : ℚ) / n := by
  classical
  have hinj : Function.Injective (fun i : P.ι => (P.H i).index) := by
    intro i j hij
    by_contra hne
    exact hdist i j hne hij
  have hsubset : (Finset.univ.image fun i : P.ι => (P.H i).index)
      ⊆ (indexSet G).filter (fun n => 1 < n) := by
    intro n hn
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_filter.mpr ⟨index_mem_indexSet G (P.H i), ?_⟩
    have hne : (P.H i).index ≠ 1 := by
      intro h
      exact P.proper i (Subgroup.index_eq_one.mp h)
    have h0 : (P.H i).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨h0, hne⟩
  calc ∑ i : P.ι, (1 : ℚ) / (P.H i).index
      = ∑ n ∈ Finset.univ.image (fun i : P.ι => (P.H i).index), (1 : ℚ) / n := by
        rw [Finset.sum_image]
        intro i _ j _ hij
        exact hinj hij
    _ ≤ ∑ n ∈ (indexSet G).filter (fun n => 1 < n), (1 : ℚ) / n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro n _ _
        exact div_nonneg (zero_le_one' ℚ) (Nat.cast_nonneg n)

theorem isHS_of_J_lt_two (hJ : J G < 2) : IsHS G := by
  classical
  intro P
  by_contra hcon
  push_neg at hcon
  have hdist : ∀ i j : P.ι, i ≠ j → (P.H i).index ≠ (P.H j).index :=
    fun i j hij h => hcon i j hij h
  have h1 := sum_inv_index_eq_one P
  have hle := sum_inv_index_le P hdist
  have hsplit := J_eq_one_add (G := G)
  have htwo : (2 : ℚ) ≤ J G := by
    rw [hsplit]
    have : (1 : ℚ) ≤ ∑ n ∈ (indexSet G).filter (fun n => 1 < n), (1 : ℚ) / n :=
      calc (1 : ℚ) = ∑ i : P.ι, (1 : ℚ) / (P.H i).index := h1.symm
        _ ≤ _ := hle
    linarith
  linarith

end Finite

end HSC
