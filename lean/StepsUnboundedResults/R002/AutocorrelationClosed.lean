import StepsUnboundedResults.R002.AutocorrelationPairing

namespace StepsUnboundedResults.R002

open scoped BigOperators

theorem sum_harmonicMod
    {r n : ℕ} (hr : r.Prime) (hn : n < r) :
    ∑ j ∈ Finset.range n, harmonicMod r (j + 1) =
      ((n + 1 : ℕ) : ZMod r) * harmonicMod r n - (n : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < r := Nat.lt_trans (Nat.lt_succ_self n) hn
      have hsucc_lt : n + 1 < r := by omega
      have hcast : ((n + 1 : ℕ) : ZMod r) ≠ 0 := by
        intro hz
        have hdvd : r ∣ n + 1 :=
          (ZMod.natCast_eq_zero_iff (n + 1) r).1 hz
        exact (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hsucc_lt) hdvd
      rw [Finset.sum_range_succ, ih hnlt, harmonicMod_succ]
      push_cast
      have hcast' : (n : ZMod r) + 1 ≠ 0 := by simpa using hcast
      field_simp [hcast']
      ring

/-- The harmonic sum stopping one term before `h` has the same value as
the elementary weighted reciprocal sum. -/
theorem sum_harmonicMod_before_last
    {r h : ℕ} (hr : r.Prime) (hh0 : 1 ≤ h) (hhr : h < r) :
    ∑ j ∈ Finset.range (h - 1), harmonicMod r (j + 1) =
      (h : ZMod r) * harmonicMod r h - (h : ZMod r) := by
  have hs := sum_harmonicMod hr hhr
  have hsplit :
      (∑ j ∈ Finset.range h, harmonicMod r (j + 1)) =
        (∑ j ∈ Finset.range (h - 1), harmonicMod r (j + 1)) +
          harmonicMod r h := by
    have hback : h - 1 + 1 = h := by omega
    calc
      (∑ j ∈ Finset.range h, harmonicMod r (j + 1)) =
          ∑ j ∈ Finset.range (h - 1 + 1), harmonicMod r (j + 1) := by
        rw [hback]
      _ = (∑ j ∈ Finset.range (h - 1), harmonicMod r (j + 1)) +
          harmonicMod r h := by
        rw [Finset.sum_range_succ, hback]
  rw [hsplit] at hs
  push_cast at hs ⊢
  linear_combination hs

/-- Expanding `(h-D)/D` evaluates the third sum in the doubling formula. -/
theorem sum_weighted_harmonic_gap
    {r h : ℕ} (hr : r.Prime) (hhr : h < r) :
    ∑ d ∈ Finset.range h,
        ((h - (d + 1) : ℕ) : ZMod r) *
          ((d + 1 : ℕ) : ZMod r)⁻¹ =
      (h : ZMod r) * harmonicMod r h - (h : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  calc
    (∑ d ∈ Finset.range h,
        ((h - (d + 1) : ℕ) : ZMod r) *
          ((d + 1 : ℕ) : ZMod r)⁻¹) =
        ∑ d ∈ Finset.range h,
          ((h : ZMod r) * ((d + 1 : ℕ) : ZMod r)⁻¹ - 1) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdlt : d < h := Finset.mem_range.mp hd
      have hdle : d + 1 ≤ h := by omega
      have hdpos : 0 < d + 1 := by omega
      have hdr : d + 1 < r := lt_of_le_of_lt hdle hhr
      have hcast : ((d + 1 : ℕ) : ZMod r) ≠ 0 := by
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff (d + 1) r).1 hz
        exact (Nat.not_dvd_of_pos_of_lt hdpos hdr) hdvd
      rw [Nat.cast_sub hdle]
      push_cast
      have hcast' : (d : ZMod r) + 1 ≠ 0 := by simpa using hcast
      rw [sub_mul, mul_inv_cancel₀ hcast']
    _ = (h : ZMod r) * harmonicMod r h - (h : ZMod r) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        harmonicMod]
      push_cast
      ring

/-- Closed harmonic evaluation of the doubling autocorrelation. -/
theorem blockAutocorrelationTwo_eq_harmonicClosed
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c =
      (c : ZMod r) *
        ((2 : ZMod r) * harmonicMod r (halfIndex r) -
          harmonicMod r (halfIndex r / 2) - 2) := by
  let h := halfIndex r
  let H : ZMod r := harmonicMod r h
  let Hm : ZMod r := harmonicMod r (h / 2)
  let S : ZMod r :=
    ∑ j ∈ Finset.range (h - 1), harmonicMod r (j + 1)
  let C : ZMod r :=
    ∑ d ∈ Finset.range h,
      ((h - (d + 1) : ℕ) : ZMod r) *
        ((d + 1 : ℕ) : ZMod r)⁻¹
  have hh0 : 1 ≤ h := by
    simp only [h, halfIndex]
    omega
  have hhr : h < r := by
    simp only [h, halfIndex]
    omega
  have hpair := paired_harmonicMod_sum r h hh0
  change
    (∑ d ∈ Finset.range h, harmonicMod r ((d + 1) / 2)) +
      (∑ d ∈ Finset.range h,
        harmonicMod r (h - ceilHalf (d + 1))) = 2 * S + Hm at hpair
  have hS := sum_harmonicMod_before_last hr hh0 hhr
  change S = (h : ZMod r) * H - (h : ZMod r) at hS
  have hC := sum_weighted_harmonic_gap hr hhr
  change C = (h : ZMod r) * H - (h : ZMod r) at hC
  have htwosum :
      (∑ d ∈ Finset.range h,
        (2 : ZMod r) * ((h - (d + 1) : ℕ) : ZMod r) *
          ((d + 1 : ℕ) : ZMod r)⁻¹) = 2 * C := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [blockAutocorrelationTwo_eq_intermediateSum hr hr3 hc]
  change (c : ZMod r) *
      (∑ d ∈ Finset.range h,
        (-harmonicMod r ((d + 1) / 2) -
          harmonicMod r (h - ceilHalf (d + 1)) -
          2 * ((h - (d + 1) : ℕ) : ZMod r) *
            ((d + 1 : ℕ) : ZMod r)⁻¹)) = _
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, htwosum]
  change (c : ZMod r) *
    (-(∑ d ∈ Finset.range h, harmonicMod r ((d + 1) / 2)) -
      (∑ d ∈ Finset.range h,
        harmonicMod r (h - ceilHalf (d + 1))) - 2 * C) = _
  rw [show
      -(∑ d ∈ Finset.range h, harmonicMod r ((d + 1) / 2)) -
          (∑ d ∈ Finset.range h,
            harmonicMod r (h - ceilHalf (d + 1))) =
        -((∑ d ∈ Finset.range h, harmonicMod r ((d + 1) / 2)) +
          (∑ d ∈ Finset.range h,
            harmonicMod r (h - ceilHalf (d + 1)))) by ring,
    hpair, hC, hS]
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hrdecomp : 2 * h + 1 = r := by
    simpa [h] using two_mul_halfIndex_add_one hrodd
  have hlinear : (2 : ZMod r) * (h : ZMod r) + 1 = 0 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hrdecomp
    push_cast at hcast
    rw [ZMod.natCast_self] at hcast
    simpa using hcast
  change (c : ZMod r) *
      (-(2 * ((h : ZMod r) * H - (h : ZMod r)) + Hm) -
        2 * ((h : ZMod r) * H - (h : ZMod r))) =
    (c : ZMod r) * (2 * H - Hm - 2)
  linear_combination (c : ZMod r) * 2 * (1 - H) * hlinear

/-- The elementary finite logarithm at two. -/
def harmonicFermatQuotientTwo (r : ℕ) : ZMod r :=
  harmonicMod r (halfIndex r / 2) -
    (2 : ZMod r) * harmonicMod r (halfIndex r)

/-- The unconditional finite-log form of the doubling autocorrelation identity. -/
theorem blockAutocorrelationTwo_sub_one_eq_neg_harmonicFermatQuotientTwo
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c - blockAutocorrelationOne r c =
      -(c : ZMod r) * harmonicFermatQuotientTwo r := by
  rw [blockAutocorrelationTwo_eq_harmonicClosed hr hr3 hc,
    blockAutocorrelationOne_eq_neg_two_mul hr hr3 hc]
  simp only [harmonicFermatQuotientTwo]
  ring

/-- Version carrying the prime-modulus hypotheses of the chapter. -/
theorem primeRealModulus_autocorrelation_finiteLog
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hP : (2 * c * r - 1).Prime) :
    blockAutocorrelationTwo r c - blockAutocorrelationOne r c =
      -(c : ZMod r) * harmonicFermatQuotientTwo r := by
  have hc : 0 < c := by
    by_contra hc0
    have : c = 0 := Nat.eq_zero_of_not_pos hc0
    subst c
    norm_num at hP
  exact blockAutocorrelationTwo_sub_one_eq_neg_harmonicFermatQuotientTwo
    hr hr3 hc

end StepsUnboundedResults.R002
