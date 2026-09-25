import StepsUnboundedResults.R002.AutocorrelationThresholds

namespace StepsUnboundedResults.R002

open scoped BigOperators

/-- Summing a function of `x / q` over complete blocks repeats every value
exactly `q` times. -/
theorem sum_range_mul_div
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {q : ℕ} (hq : 0 < q) (m : ℕ) :
    ∑ x ∈ Finset.range (q * m), f (x / q) =
      q • ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih,
        Finset.sum_range_succ, smul_add]
      congr 1
      calc
        ∑ x ∈ Finset.range q, f ((q * m + x) / q) =
            ∑ _x ∈ Finset.range q, f m := by
          apply Finset.sum_congr rfl
          intro x hx
          have hxq : x < q := Finset.mem_range.mp hx
          rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hxq, add_zero]
        _ = q • f m := by simp

/-- A terminal partial block of length at most `q` has constant quotient. -/
theorem sum_range_tail_div
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    {q : ℕ} (hq : 0 < q) (m t : ℕ) (ht : t ≤ q) :
    ∑ x ∈ Finset.range t, f ((q * m + x) / q) = t • f m := by
  calc
    ∑ x ∈ Finset.range t, f ((q * m + x) / q) =
        ∑ _x ∈ Finset.range t, f m := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxt : x < t := Finset.mem_range.mp hx
      have hxq : x < q := lt_of_lt_of_le hxt ht
      rw [Nat.mul_add_div hq, Nat.div_eq_of_lt hxq, add_zero]
    _ = t • f m := by simp

theorem two_mul_halfIndex_add_one
    {r : ℕ} (hr : Odd r) : 2 * halfIndex r + 1 = r := by
  obtain ⟨k, rfl⟩ := hr
  simp [halfIndex]

/-- Exact block decomposition of the identity autocorrelation. -/
theorem blockAutocorrelationOne_eq_blocks
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationOne r c =
      ((2 * c : ℕ) : ZMod r) *
          (∑ j ∈ Finset.range (halfIndex r), harmonicMod r j ^ 2) +
        (c : ZMod r) * harmonicMod r (halfIndex r) ^ 2 := by
  have hrpos : 0 < r := hr.pos
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hrdecomp := two_mul_halfIndex_add_one hrodd
  have hcr : 0 < c * r := Nat.mul_pos hc hrpos
  have hq : 0 < 2 * c := by positivity
  have hctwo : c ≤ 2 * c := by omega
  have hset :
      positiveRepresentatives (realResidueCount r c) =
        (Finset.range (c * r)).erase 0 := by
    ext x
    simp only [positiveRepresentatives, realResidueCount,
      Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  rw [blockAutocorrelationOne, hset]
  have hzero :
      blockHarmonic r c 0 * blockHarmonic r c 0 = 0 := by
    simp [blockHarmonic]
  have herase := Finset.sum_erase (Finset.range (c * r))
    (f := fun x ↦ blockHarmonic r c x * blockHarmonic r c x)
    (a := 0) hzero
  rw [herase]
  simp only [blockHarmonic]
  have hlength : c * r = (2 * c) * halfIndex r + c := by
    calc
      c * r = c * (2 * halfIndex r + 1) := by rw [hrdecomp]
      _ = (2 * c) * halfIndex r + c := by ring
  rw [hlength, Finset.sum_range_add,
    sum_range_mul_div (fun j ↦ harmonicMod r j * harmonicMod r j) hq,
    sum_range_tail_div (fun j ↦ harmonicMod r j * harmonicMod r j)
      hq (halfIndex r) c hctwo]
  simp only [nsmul_eq_mul]
  push_cast
  simp only [pow_two]

/-- Shift a range sum by one when the zeroth term vanishes. -/
theorem sum_range_shift_eq_sum_add_last
    {A : Type*} [AddCommMonoid A] (f : ℕ → A)
    (h : ℕ) (hf0 : f 0 = 0) :
    ∑ j ∈ Finset.range h, f (j + 1) =
      (∑ j ∈ Finset.range h, f j) + f h := by
  induction h with
  | zero => simp [hf0]
  | succ h ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]

/-- Split a range of even length into consecutive pairs. -/
theorem sum_range_two_mul
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (m : ℕ) :
    ∑ d ∈ Finset.range (2 * m), f d =
      ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih,
        Finset.sum_range_succ]
      simp [Finset.sum_range_succ]

/-- A range sum is its first term followed by the shifted tail. -/
theorem first_add_sum_range_shift
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) (n : ℕ) :
    f 0 + (∑ j ∈ Finset.range n, f (j + 1)) =
      ∑ j ∈ Finset.range (n + 1), f j := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
      ac_rfl

/-- The identity autocorrelation has the universal value `-2*c`. -/
theorem blockAutocorrelationOne_eq_neg_two_mul
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationOne r c = (-2 : ZMod r) * (c : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  let h := halfIndex r
  let S : ZMod r :=
    ∑ j ∈ Finset.range h, harmonicMod r j ^ 2
  let H : ZMod r := harmonicMod r h
  have hh_lt : h < r := by
    dsimp [h, halfIndex]
    omega
  have hsquare := sum_harmonicMod_sq hr hh_lt
  change
    (∑ j ∈ Finset.range h, harmonicMod r (j + 1) ^ 2) = _
      at hsquare
  have hshift :
      (∑ j ∈ Finset.range h, harmonicMod r (j + 1) ^ 2) =
        S + H ^ 2 := by
    simpa [S, H] using
      sum_range_shift_eq_sum_add_last
        (fun j ↦ harmonicMod r j ^ 2) h (by simp)
  rw [hshift] at hsquare
  change
    S + H ^ 2 =
      ((h + 1 : ℕ) : ZMod r) * H ^ 2 -
        ((2 * h + 1 : ℕ) : ZMod r) * H +
          ((2 * h : ℕ) : ZMod r) at hsquare
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hrdecomp : 2 * h + 1 = r := by
    simpa [h] using two_mul_halfIndex_add_one hrodd
  have hchar : ((2 * h + 1 : ℕ) : ZMod r) = 0 := by
    rw [hrdecomp]
    exact ZMod.natCast_self r
  have hfour : ((4 * h : ℕ) : ZMod r) = -2 := by
    have hcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hrdecomp
    push_cast at hcast ⊢
    rw [ZMod.natCast_self] at hcast
    linear_combination 2 * hcast
  rw [blockAutocorrelationOne_eq_blocks hr hr3 hc]
  change ((2 * c : ℕ) : ZMod r) * S + (c : ZMod r) * H ^ 2 = _
  push_cast
  calc
    (2 : ZMod r) * (c : ZMod r) * S + (c : ZMod r) * H ^ 2 =
        (c : ZMod r) * (2 * (S + H ^ 2) - H ^ 2) := by ring
    _ = (c : ZMod r) *
        (2 * (((h + 1 : ℕ) : ZMod r) * H ^ 2 -
          ((2 * h + 1 : ℕ) : ZMod r) * H +
            ((2 * h : ℕ) : ZMod r)) - H ^ 2) := by rw [hsquare]
    _ = (c : ZMod r) * (-2) := by
      rw [hchar, zero_mul, sub_zero]
      have hlinear : (2 : ZMod r) * (h : ZMod r) + 1 = 0 := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one] using hchar
      have hcastFour : (4 : ZMod r) * (h : ZMod r) = -2 := by
        simpa using hfour
      push_cast
      linear_combination
        (c : ZMod r) * H ^ 2 * hlinear + (c : ZMod r) * hcastFour
    _ = (-2 : ZMod r) * (c : ZMod r) := by ring

/-- Substitute the exact interval cardinality into the doubling
autocorrelation. -/
theorem blockAutocorrelationTwo_eq_weightedCount
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c =
      ∑ b ∈ Finset.range (halfIndex r),
        ∑ d ∈ Finset.range (halfIndex r),
          ((b + 1 : ℕ) : ZMod r)⁻¹ *
            ((d + 1 : ℕ) : ZMod r)⁻¹ * (c : ZMod r) *
              ((r - (d + 1) - max (2 * (b + 1)) (d + 1) : ℕ) :
                ZMod r) := by
  rw [blockAutocorrelationTwo_eq_thresholdCount hr.pos hc]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 1 ≤ d + 1 := by omega
  have hdh : d + 1 ≤ halfIndex r := by
    exact Finset.mem_range.mp hd
  rw [card_blockDoublingThreshold hc hr3 hd0 hdh]
  push_cast
  ring

end StepsUnboundedResults.R002
