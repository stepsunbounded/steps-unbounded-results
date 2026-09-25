import StepsUnboundedResults.HSC.A5MonoidBoundsAB

open scoped Classical
open Finset

namespace HSC

theorem cseq_sub_odd (M : ℕ) :
    ∑ i ∈ range (2 * M + 1), (cseq i - dseq i)
      ≤ 24 / 209 - (3 / 11) * (1 / 12)^M + (3 / 19) * (1 / 20)^M := by
  have h1 : cseq (2 * M) = (1 / 12)^M := cseq_two M
  have h2 : dseq (2 * M) = (1 / 20)^M := dseq_two M
  calc ∑ i ∈ range (2 * M + 1), (cseq i - dseq i)
      = ∑ i ∈ range (2 * M), (cseq i - dseq i) + (cseq (2 * M) - dseq (2 * M)) := by
        rw [Finset.sum_range_succ]
    _ ≤ (24 / 209 - (14 / 11) * (1 / 12)^M + (22 / 19) * (1 / 20)^M)
          + ((1 / 12)^M - (1 / 20)^M) := by
        rw [h1, h2]; linarith [cseq_sub_even M]
    _ = 24 / 209 - (3 / 11) * (1 / 12)^M + (3 / 19) * (1 / 20)^M := by ring

theorem cseq_sub_le (I : ℕ) : ∑ i ∈ range I, (cseq i - dseq i) ≤ 24 / 209 := by
  have htail : ∀ M : ℕ, (22 / 19 : ℚ) * (1 / 20)^M ≤ (14 / 11) * (1 / 12)^M := by
    intro M
    have hx : (1 / 12 : ℚ)^M = (1 / 20)^M * (5 / 3)^M := by rw [← mul_pow]; norm_num
    have h1 : (1 : ℚ) ≤ (5 / 3)^M := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℚ) < (1 / 20)^M := by positivity
    have h3 : (1 / 20 : ℚ)^M ≤ (1 / 20)^M * (5 / 3)^M := by
      simpa using mul_le_mul_of_nonneg_left h1 (le_of_lt h2)
    rw [hx]
    nlinarith [h1, h2, h3]
  have htail3 : ∀ M : ℕ, (3 / 19 : ℚ) * (1 / 20)^M ≤ (3 / 11) * (1 / 12)^M := by
    intro M
    have hx : (1 / 12 : ℚ)^M = (1 / 20)^M * (5 / 3)^M := by rw [← mul_pow]; norm_num
    have h1 : (1 : ℚ) ≤ (5 / 3)^M := one_le_pow₀ (by norm_num)
    have h2 : (0 : ℚ) < (1 / 20)^M := by positivity
    have h3 : (1 / 20 : ℚ)^M ≤ (1 / 20)^M * (5 / 3)^M := by
      simpa using mul_le_mul_of_nonneg_left h1 (le_of_lt h2)
    rw [hx]
    nlinarith [h1, h2, h3]
  rcases Nat.even_or_odd I with ⟨M, hM⟩ | ⟨M, hM⟩
  · rw [hM, ← two_mul]
    have := cseq_sub_even M
    linarith [htail M]
  · rw [hM]
    have := cseq_sub_odd M
    linarith [htail3 M]

theorem gC_geom (m : ℕ) :
    ∑ j ∈ range m, ((1 / 3 : ℚ)^j * (1 / 5)^(m - j)) = (3 / 2) * ((1 / 3)^m - (1 / 5)^m) := by
  have hcongr : ∑ j ∈ range m, ((1 / 3 : ℚ)^j * (1 / 5)^(m - j))
      = (1 / 5)^m * ∑ j ∈ range m, (5 / 3 : ℚ)^j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact pow_mul_pow_sub' j m (by have := Finset.mem_range.mp hj; omega)
  rw [hcongr, geom_sum_eq (show (5 / 3 : ℚ) ≠ 1 by norm_num)]
  have h2 : (1 / 5 : ℚ)^m * (5 / 3)^m = (1 / 3)^m := by rw [← mul_pow]; norm_num
  rw [← h2]
  field_simp
  ring

theorem gC_inner (i J : ℕ) : ∑ j ∈ range J, gC i j ≤ (15 / 8) * (cseq i - dseq i) := by
  have hC : ∑ j ∈ range J, gC i j
      = (5 / 4) * (1 / 2)^i *
          ∑ j ∈ (range J).filter (fun j => j < (i + 1) / 2),
            ((1 / 3 : ℚ)^j * (1 / 5)^((i + 1) / 2 - j)) := by
    unfold gC
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hC]
  have hle : ∑ j ∈ (range J).filter (fun j => j < (i + 1) / 2),
        ((1 / 3 : ℚ)^j * (1 / 5)^((i + 1) / 2 - j))
      ≤ (3 / 2) * ((1 / 3)^((i + 1) / 2) - (1 / 5)^((i + 1) / 2)) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (le_of_eq (gC_geom ((i + 1) / 2)))
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_range]
      exact hj.2
    · intro j _ _; positivity
  calc (5 / 4 : ℚ) * (1 / 2)^i * _
      ≤ (5 / 4) * (1 / 2)^i *
          ((3 / 2) * ((1 / 3)^((i + 1) / 2) - (1 / 5)^((i + 1) / 2))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (15 / 8) * (cseq i - dseq i) := by unfold cseq dseq; ring

theorem gC_bound (I J : ℕ) : ∑ i ∈ range I, ∑ j ∈ range J, gC i j ≤ 45 / 209 := by
  calc ∑ i ∈ range I, ∑ j ∈ range J, gC i j
      ≤ ∑ i ∈ range I, (15 / 8) * (cseq i - dseq i) := Finset.sum_le_sum fun i _ => gC_inner i J
    _ = (15 / 8) * ∑ i ∈ range I, (cseq i - dseq i) := by rw [Finset.mul_sum]
    _ ≤ (15 / 8) * (24 / 209) := mul_le_mul_of_nonneg_left (cseq_sub_le I) (by norm_num)
    _ = 45 / 209 := by norm_num

theorem gG_bound (I J : ℕ) : ∑ i ∈ range I, ∑ j ∈ range J, gG i j ≤ 11463 / 5852 := by
  have hsplit : ∑ i ∈ range I, ∑ j ∈ range J, gG i j
      = (∑ i ∈ range I, ∑ j ∈ range J, gA i j) + (∑ i ∈ range I, ∑ j ∈ range J, gB i j)
        + (∑ i ∈ range I, ∑ j ∈ range J, gC i j) := by
    rw [show ∑ i ∈ range I, ∑ j ∈ range J, gG i j
          = ∑ i ∈ range I, ∑ j ∈ range J, (gA i j + gB i j + gC i j) from
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => gG_eq i j]
    simp only [Finset.sum_add_distrib]
  rw [hsplit]
  linarith [gA_bound I J, gB_bound I J, gC_bound I J]

def tripleRange (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1)) ×ˢ ((range (N + 1)) ×ˢ (range (N + 1)))

def tripleGood (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (tripleRange N).filter (fun t => kappa t.1 t.2.1 ≤ t.2.2)

theorem inner_geom (K κ : ℕ) :
    ∑ k ∈ (range K).filter (fun k => κ ≤ k), (1 / 5 : ℚ)^k ≤ (5 / 4) * (1 / 5)^κ := by
  have hsub : (range K).filter (fun k => κ ≤ k) ⊆ Ico κ K := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ico]
    exact ⟨hk.2, hk.1⟩
  calc ∑ k ∈ (range K).filter (fun k => κ ≤ k), (1 / 5 : ℚ)^k
      ≤ ∑ k ∈ Ico κ K, (1 / 5 : ℚ)^k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ (1 / 5)^κ * (1 / (1 - 1 / 5)) := geom_Ico_le _ (by norm_num) (by norm_num) κ K
    _ = (5 / 4) * (1 / 5)^κ := by
        field_simp
        ring

theorem triple_good_bound (N : ℕ) : ∑ t ∈ tripleGood N, term t ≤ 11463 / 5852 := by
  have hexp : ∑ t ∈ tripleGood N, term t
      = ∑ i ∈ range (N + 1), ∑ j ∈ range (N + 1), ∑ k ∈ range (N + 1),
          (if kappa i j ≤ k then term (i, j, k) else 0) := by
    simp only [tripleGood, tripleRange, Finset.sum_filter, Finset.sum_product]
  rw [hexp]
  refine le_trans ?_ (gG_bound (N + 1) (N + 1))
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have h1 : ∑ k ∈ range (N + 1), (if kappa i j ≤ k then term (i, j, k) else 0)
      = (1 / 2)^i * (1 / 3)^j *
          ∑ k ∈ (range (N + 1)).filter (fun k => kappa i j ≤ k), (1 / 5 : ℚ)^k := by
    rw [Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold term
    ring
  rw [h1]
  calc (1 / 2 : ℚ)^i * (1 / 3)^j *
        ∑ k ∈ (range (N + 1)).filter (fun k => kappa i j ≤ k), (1 / 5 : ℚ)^k
      ≤ (1 / 2)^i * (1 / 3)^j * ((5 / 4) * (1 / 5)^(kappa i j)) :=
        mul_le_mul_of_nonneg_left (inner_geom (N + 1) (kappa i j)) (by positivity)
    _ = gG i j := by unfold gG; ring

end HSC
