import StepsUnboundedResults.HSC.A5MonoidCore

open scoped Classical
open Finset

namespace HSC

theorem geom_tail_le (x : ℚ) (h0 : 0 ≤ x) (h1 : x < 1) (s : Finset ℕ) (m J : ℕ)
    (hs : s ⊆ range J) (hm : ∀ k ∈ s, m ≤ k) : ∑ k ∈ s, x^k ≤ x^m * (1 / (1 - x)) := by
  have hsub : s ⊆ Ico m J := by
    intro k hk
    simp only [Finset.mem_Ico]
    exact ⟨hm k hk, by simpa using hs hk⟩
  exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg h0 k))
    (geom_Ico_le x h0 h1 m J)

theorem pow_mul_pow_sub (i j : ℕ) (h : i ≤ j) :
    (1 / 3 : ℚ)^j * (1 / 5)^(j - i) = (5 : ℚ)^i * (1 / 15)^j := by
  have h1 : (1 / 5 : ℚ)^(j - i) * (1 / 5)^i = (1 / 5)^j := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have h2 : (5 : ℚ)^i * (1 / 5)^i = 1 := by rw [← mul_pow]; norm_num
  calc (1 / 3 : ℚ)^j * (1 / 5)^(j - i)
      = (1 / 3)^j * (1 / 5)^(j - i) * ((5 : ℚ)^i * (1 / 5)^i) := by rw [h2, mul_one]
    _ = (1 / 3)^j * ((1 / 5)^(j - i) * (1 / 5)^i) * (5 : ℚ)^i := by ring
    _ = (1 / 3)^j * (1 / 5)^j * (5 : ℚ)^i := by rw [h1]
    _ = (5 : ℚ)^i * ((1 / 3) * (1 / 5))^j := by rw [← mul_pow]; ring
    _ = (5 : ℚ)^i * (1 / 15)^j := by norm_num

theorem pow_mul_pow_sub' (j m : ℕ) (h : j ≤ m) :
    (1 / 3 : ℚ)^j * (1 / 5)^(m - j) = (1 / 5 : ℚ)^m * (5 / 3)^j := by
  have h1 : (1 / 5 : ℚ)^(m - j) * (1 / 5)^j = (1 / 5)^m := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have h2 : (5 : ℚ)^j * (1 / 5)^j = 1 := by rw [← mul_pow]; norm_num
  calc (1 / 3 : ℚ)^j * (1 / 5)^(m - j)
      = (1 / 3)^j * (1 / 5)^(m - j) * ((5 : ℚ)^j * (1 / 5)^j) := by rw [h2, mul_one]
    _ = (1 / 5)^m * ((1 / 3 : ℚ)^j * (5 : ℚ)^j) := by rw [← h1]; ring
    _ = (1 / 5)^m * ((1 / 3) * (5 : ℚ))^j := by rw [mul_pow]
    _ = (1 / 5)^m * (5 / 3)^j := by norm_num

theorem geom_half_Ico (j : ℕ) :
    ∑ i ∈ Ico j (2 * j + 1), (1 / 2 : ℚ)^i = (1 / 2)^j * (2 - (1 / 2)^j) := by
  rw [geom_Ico_eq (1 / 2) (by norm_num) j (2 * j + 1)]
  have h : 2 * j + 1 - j = j + 1 := by omega
  rw [h, pow_succ]
  field_simp
  ring

def term (t : ℕ × ℕ × ℕ) : ℚ := (1 / 2)^t.1 * (1 / 3)^t.2.1 * (1 / 5)^t.2.2

theorem term_nonneg (t : ℕ × ℕ × ℕ) : 0 ≤ term t := by unfold term; positivity

theorem one_div_pow_mul (i j k : ℕ) :
    (1 : ℚ) / ((2^i * 3^j * 5^k : ℕ) : ℚ) = (1 / 2)^i * (1 / 3)^j * (1 / 5)^k := by
  have h1 : ((2^i * 3^j * 5^k : ℕ) : ℚ) = (2 : ℚ)^i * 3^j * 5^k := by push_cast; ring
  rw [h1, one_div, mul_inv_rev, mul_inv_rev]
  simp only [← inv_pow, one_div]
  ring

def gG (i j : ℕ) : ℚ := (5 / 4) * (1 / 2)^i * (1 / 3)^j * (1 / 5)^(kappa i j)

def gA (i j : ℕ) : ℚ := if i < j then (5 / 4) * (1 / 2)^i * (1 / 3)^j * (1 / 5)^(j - i) else 0

def gB (i j : ℕ) : ℚ := if j ≤ i ∧ (i + 1) / 2 ≤ j then (5 / 4) * (1 / 2)^i * (1 / 3)^j else 0

def gC (i j : ℕ) : ℚ :=
  if j < (i + 1) / 2 then (5 / 4) * (1 / 2)^i * (1 / 3)^j * (1 / 5)^((i + 1) / 2 - j) else 0

theorem gG_eq (i j : ℕ) : gG i j = gA i j + gB i j + gC i j := by
  unfold gG gA gB gC
  by_cases h1 : i < j
  · have hk : kappa i j = j - i := by unfold kappa; rw [if_pos h1]
    have hB : ¬ (j ≤ i ∧ (i + 1) / 2 ≤ j) := by omega
    have hC : ¬ j < (i + 1) / 2 := by omega
    rw [hk, if_neg hB, if_neg hC, if_pos h1]; ring
  · have hk : kappa i j = max 0 ((i + 1) / 2 - j) := by unfold kappa; rw [if_neg h1]
    have hA : ¬ i < j := h1
    by_cases h2 : (i + 1) / 2 ≤ j
    · have hk2 : kappa i j = 0 := by
        rw [hk, Nat.sub_eq_zero_of_le h2]; exact max_eq_left (Nat.zero_le _)
      have hC : ¬ j < (i + 1) / 2 := by omega
      rw [hk2, if_neg hA, if_pos ⟨by omega, h2⟩, if_neg hC]; ring
    · have h2' : j < (i + 1) / 2 := by omega
      have hk2 : kappa i j = (i + 1) / 2 - j := by rw [hk, max_eq_right (Nat.zero_le _)]
      have hB : ¬ (j ≤ i ∧ (i + 1) / 2 ≤ j) := by omega
      rw [hk2, if_neg hA, if_neg hB, if_pos h2']; ring

end HSC
