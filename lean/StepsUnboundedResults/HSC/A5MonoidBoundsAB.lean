import StepsUnboundedResults.HSC.A5MonoidRegions

open scoped Classical
open Finset

namespace HSC

theorem gA_bound (I J : ℕ) : ∑ i ∈ range I, ∑ j ∈ range J, gA i j ≤ 3 / 28 := by
  have inner : ∀ i, ∑ j ∈ range J, gA i j ≤ (5 / 4) * (1 / 2)^i * ((1 / 3)^i / 14) := by
    intro i
    have hA : ∑ j ∈ range J, gA i j
        = (5 / 4) * (1 / 2)^i *
            ∑ j ∈ (range J).filter (fun j => i < j), ((1 / 3 : ℚ)^j * (1 / 5)^(j - i)) := by
      unfold gA
      rw [← Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hA]
    have hb : ∑ j ∈ (range J).filter (fun j => i < j), ((1 / 3 : ℚ)^j * (1 / 5)^(j - i))
        ≤ (1 / 3)^i / 14 := by
      have hcongr : ∑ j ∈ (range J).filter (fun j => i < j),
            ((1 / 3 : ℚ)^j * (1 / 5)^(j - i))
          = (5 : ℚ)^i * ∑ j ∈ (range J).filter (fun j => i < j), (1 / 15 : ℚ)^j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        exact pow_mul_pow_sub i j (by have h := (Finset.mem_filter.mp hj).2; omega)
      rw [hcongr]
      have hgeom : ∑ j ∈ (range J).filter (fun j => i < j), (1 / 15 : ℚ)^j
          ≤ (1 / 15)^(i + 1) * (1 / (1 - 1 / 15)) :=
        geom_tail_le (1 / 15) (by norm_num) (by norm_num) _ (i + 1) J
          (fun k hk => (Finset.mem_filter.mp hk).1)
          (fun k hk => by have h := (Finset.mem_filter.mp hk).2; omega)
      calc (5 : ℚ)^i * _
          ≤ (5 : ℚ)^i * ((1 / 15)^(i + 1) * (1 / (1 - 1 / 15))) :=
            mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = (1 / 3)^i / 14 := by
            have h : (5 : ℚ)^i * (1 / 15)^i = (1 / 3)^i := by rw [← mul_pow]; norm_num
            rw [pow_succ, ← h]
            field_simp
            ring
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  calc ∑ i ∈ range I, ∑ j ∈ range J, gA i j
      ≤ ∑ i ∈ range I, (5 / 4) * (1 / 2)^i * ((1 / 3)^i / 14) :=
        Finset.sum_le_sum fun i _ => inner i
    _ = (5 / 56) * ∑ i ∈ range I, (1 / 6 : ℚ)^i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h : (1 / 2 : ℚ)^i * (1 / 3)^i = (1 / 6)^i := by rw [← mul_pow]; norm_num
        rw [← h]; ring
    _ ≤ (5 / 56) * (1 / (1 - 1 / 6)) :=
        mul_le_mul_of_nonneg_left (geom_range_le (1 / 6) (by norm_num) (by norm_num) I)
          (by norm_num)
    _ = 3 / 28 := by norm_num

theorem gB_inner (j I : ℕ) :
    ∑ i ∈ range I, gB i j ≤ (5 / 4) * (1 / 3)^j * ((1 / 2)^j * (2 - (1 / 2)^j)) := by
  have hB : ∑ i ∈ range I, gB i j
      = (5 / 4) * (1 / 3)^j *
          ∑ i ∈ (range I).filter (fun i => j ≤ i ∧ (i + 1) / 2 ≤ j), (1 / 2 : ℚ)^i := by
    unfold gB
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hB]
  have hle : ∑ i ∈ (range I).filter (fun i => j ≤ i ∧ (i + 1) / 2 ≤ j), (1 / 2 : ℚ)^i
      ≤ (1 / 2)^j * (2 - (1 / 2)^j) := by
    have hsub : (range I).filter (fun i => j ≤ i ∧ (i + 1) / 2 ≤ j) ⊆ Ico j (2 * j + 1) := by
      intro i hi
      have h1 := (Finset.mem_filter.mp hi).2.1
      have h2 := (Finset.mem_filter.mp hi).2.2
      simp only [Finset.mem_Ico]
      exact ⟨h1, by omega⟩
    calc ∑ i ∈ (range I).filter (fun i => j ≤ i ∧ (i + 1) / 2 ≤ j), (1 / 2 : ℚ)^i
        ≤ ∑ i ∈ Ico j (2 * j + 1), (1 / 2 : ℚ)^i :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ = (1 / 2)^j * (2 - (1 / 2)^j) := geom_half_Ico j
  exact mul_le_mul_of_nonneg_left hle (by positivity)

theorem gB_bound (I J : ℕ) : ∑ i ∈ range I, ∑ j ∈ range J, gB i j ≤ 18 / 11 := by
  rw [Finset.sum_comm]
  have hstep : ∀ j ∈ range J, (5 / 4 : ℚ) * (1 / 3)^j * ((1 / 2)^j * (2 - (1 / 2)^j))
      = (5 / 2) * (1 / 6)^j - (5 / 4) * (1 / 12)^j := by
    intro j _
    have h1 : (1 / 3 : ℚ)^j * (1 / 2)^j = (1 / 6)^j := by rw [← mul_pow]; norm_num
    have h2 : (1 / 6 : ℚ)^j * (1 / 2)^j = (1 / 12)^j := by rw [← mul_pow]; norm_num
    calc (5 / 4 : ℚ) * (1 / 3)^j * ((1 / 2)^j * (2 - (1 / 2)^j))
        = (5 / 4) * ((1 / 3)^j * (1 / 2)^j) * (2 - (1 / 2)^j) := by ring
      _ = (5 / 4) * (1 / 6)^j * (2 - (1 / 2)^j) := by rw [h1]
      _ = (5 / 2) * (1 / 6)^j - (5 / 4) * ((1 / 6)^j * (1 / 2)^j) := by ring
      _ = (5 / 2) * (1 / 6)^j - (5 / 4) * (1 / 12)^j := by rw [h2]
  calc ∑ j ∈ range J, ∑ i ∈ range I, gB i j
      ≤ ∑ j ∈ range J, (5 / 4) * (1 / 3)^j * ((1 / 2)^j * (2 - (1 / 2)^j)) :=
        Finset.sum_le_sum fun j _ => gB_inner j I
    _ = (5 / 2) * ∑ j ∈ range J, (1 / 6 : ℚ)^j - (5 / 4) * ∑ j ∈ range J, (1 / 12 : ℚ)^j := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl hstep
    _ = (5 / 2) * ((1 - (1 / 6)^J) / (1 - 1 / 6))
          - (5 / 4) * ((1 - (1 / 12)^J) / (1 - 1 / 12)) := by
        rw [geom_range_eq (1 / 6) (by norm_num) J, geom_range_eq (1 / 12) (by norm_num) J]
    _ ≤ 18 / 11 := by
        have hs1 : ((1 - (1 / 6 : ℚ)^J) / (1 - 1 / 6)) = (6 / 5) * (1 - (1 / 6)^J) := by
          field_simp; ring
        have hs2 : ((1 - (1 / 12 : ℚ)^J) / (1 - 1 / 12)) = (12 / 11) * (1 - (1 / 12)^J) := by
          field_simp; ring
        have hx : (1 / 12 : ℚ)^J = (1 / 6)^J * (1 / 2)^J := by rw [← mul_pow]; norm_num
        have h1 : (1 / 2 : ℚ)^J ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        have h2 : (0 : ℚ) < (1 / 6)^J := by positivity
        have h3 : (1 / 6 : ℚ)^J * (1 / 2)^J ≤ (1 / 6)^J := by
          simpa using mul_le_mul_of_nonneg_left h1 (le_of_lt h2)
        nlinarith [hs1, hs2, hx, h1, h2, h3]

def cseq (i : ℕ) : ℚ := (1 / 2)^i * (1 / 3)^((i + 1) / 2)
def dseq (i : ℕ) : ℚ := (1 / 2)^i * (1 / 5)^((i + 1) / 2)

theorem cseq_two (M : ℕ) : cseq (2 * M) = (1 / 12)^M := by
  unfold cseq
  have h : (2 * M + 1) / 2 = M := by omega
  rw [h, pow_mul, ← mul_pow]
  congr 1
  norm_num

theorem cseq_two_succ (M : ℕ) : cseq (2 * M + 1) = (1 / 6) * (1 / 12)^M := by
  unfold cseq
  have h : (2 * M + 1 + 1) / 2 = M + 1 := by omega
  rw [h]
  have h2 : (1 / 2 : ℚ)^(2 * M + 1) = (1 / 4)^M * (1 / 2) := by
    rw [pow_succ, pow_mul]; norm_num
  have h3 : (1 / 3 : ℚ)^(M + 1) = (1 / 3)^M * (1 / 3) := by rw [pow_succ]
  have h4 : (1 / 4 : ℚ)^M * (1 / 3)^M = (1 / 12)^M := by rw [← mul_pow]; norm_num
  rw [h2, h3, ← h4]
  ring

theorem dseq_two (M : ℕ) : dseq (2 * M) = (1 / 20)^M := by
  unfold dseq
  have h : (2 * M + 1) / 2 = M := by omega
  rw [h, pow_mul, ← mul_pow]
  congr 1
  norm_num

theorem dseq_two_succ (M : ℕ) : dseq (2 * M + 1) = (1 / 10) * (1 / 20)^M := by
  unfold dseq
  have h : (2 * M + 1 + 1) / 2 = M + 1 := by omega
  rw [h]
  have h2 : (1 / 2 : ℚ)^(2 * M + 1) = (1 / 4)^M * (1 / 2) := by
    rw [pow_succ, pow_mul]; norm_num
  have h3 : (1 / 5 : ℚ)^(M + 1) = (1 / 5)^M * (1 / 5) := by rw [pow_succ]
  have h4 : (1 / 4 : ℚ)^M * (1 / 5)^M = (1 / 20)^M := by rw [← mul_pow]; norm_num
  rw [h2, h3, ← h4]
  ring

theorem cseq_sub_even (M : ℕ) :
    ∑ i ∈ range (2 * M), (cseq i - dseq i)
      ≤ 24 / 209 - (14 / 11) * (1 / 12)^M + (22 / 19) * (1 / 20)^M := by
  induction M with
  | zero =>
      simp only [Nat.mul_zero, Finset.sum_range_zero, pow_zero, mul_one]
      norm_num
  | succ M ih =>
      have h1 : cseq (2 * M) = (1 / 12)^M := cseq_two M
      have h2 : dseq (2 * M) = (1 / 20)^M := dseq_two M
      have h3 : cseq (2 * M + 1) = (1 / 6) * (1 / 12)^M := cseq_two_succ M
      have h4 : dseq (2 * M + 1) = (1 / 10) * (1 / 20)^M := dseq_two_succ M
      calc ∑ i ∈ range (2 * (M + 1)), (cseq i - dseq i)
          = ∑ i ∈ range (2 * M), (cseq i - dseq i) + (cseq (2 * M) - dseq (2 * M))
              + (cseq (2 * M + 1) - dseq (2 * M + 1)) := by
            rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ]
        _ ≤ (24 / 209 - (14 / 11) * (1 / 12)^M + (22 / 19) * (1 / 20)^M)
              + ((1 / 12)^M - (1 / 20)^M)
              + ((1 / 6) * (1 / 12)^M - (1 / 10) * (1 / 20)^M) := by
            rw [h1, h2, h3, h4]; linarith
        _ = 24 / 209 - (14 / 11) * (1 / 12)^(M + 1) + (22 / 19) * (1 / 20)^(M + 1) := by
            rw [pow_succ, pow_succ]; ring

end HSC
