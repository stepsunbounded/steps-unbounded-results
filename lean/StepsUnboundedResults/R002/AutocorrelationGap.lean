import StepsUnboundedResults.R002.AutocorrelationBlocks

namespace StepsUnboundedResults.R002

open scoped BigOperators

def ceilHalf (d : ℕ) : ℕ := (d + 1) / 2

theorem floorHalf_add_ceilHalf (d : ℕ) :
    d / 2 + ceilHalf d = d := by
  simp only [ceilHalf]
  omega

/-- A shifted interval of reciprocal terms is a difference of harmonic sums. -/
theorem sum_shifted_inv_eq_harmonicMod_sub
    (r a n : ℕ) :
    ∑ x ∈ Finset.range n, (((a + x + 1 : ℕ) : ZMod r)⁻¹) =
      harmonicMod r (a + n) - harmonicMod r a := by
  unfold harmonicMod
  rw [Finset.sum_range_add]
  ring

/-- Evaluation of the inner threshold-count sum for a fixed target threshold `d`. -/
theorem weightedGap_inner
    {r d : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hd0 : 1 ≤ d) (hdh : d ≤ halfIndex r) :
    (∑ b ∈ Finset.range (halfIndex r),
      ((b + 1 : ℕ) : ZMod r)⁻¹ *
        ((r - d - max (2 * (b + 1)) d : ℕ) : ZMod r)) =
      -(d : ZMod r) * harmonicMod r (d / 2) -
        (d : ZMod r) * harmonicMod r (halfIndex r - ceilHalf d) -
          (2 : ZMod r) * ((halfIndex r - d : ℕ) : ZMod r) := by
  letI : Fact r.Prime := ⟨hr⟩
  let h := halfIndex r
  let a := d / 2
  let e := ceilHalf d
  let n := h - d
  let B := h - e
  have hh_lt : h < r := by
    dsimp [h, halfIndex]
    omega
  have hade : a + e = d := by
    simpa [a, e] using floorHalf_add_ceilHalf d
  have he_le : e ≤ d := by
    rw [← hade]
    exact Nat.le_add_left e a
  have hB : a + n = B := by
    dsimp [n, B]
    omega
  have hh : h = a + n + e := by
    dsimp [n]
    omega
  have hBe : h = B + e := by omega
  have hrdecomp : 2 * h + 1 = r := by
    simpa [h] using two_mul_halfIndex_add_one
      (hr.odd_of_ne_two (by omega))
  have hrzero : (r : ZMod r) = 0 := ZMod.natCast_self r
  rw [show halfIndex r = h by rfl, hh, Finset.sum_range_add,
    Finset.sum_range_add]
  have hfirst :
      (∑ b ∈ Finset.range a,
        ((b + 1 : ℕ) : ZMod r)⁻¹ *
          ((r - d - max (2 * (b + 1)) d : ℕ) : ZMod r)) =
        harmonicMod r a * (-(2 : ZMod r) * (d : ZMod r)) := by
    calc
      (∑ b ∈ Finset.range a,
        ((b + 1 : ℕ) : ZMod r)⁻¹ *
          ((r - d - max (2 * (b + 1)) d : ℕ) : ZMod r)) =
          ∑ b ∈ Finset.range a,
            ((b + 1 : ℕ) : ZMod r)⁻¹ *
              (-(2 : ZMod r) * (d : ZMod r)) := by
        apply Finset.sum_congr rfl
        intro b hb
        have hb_lt : b < a := Finset.mem_range.mp hb
        have hmax : max (2 * (b + 1)) d = d := by
          apply max_eq_right
          dsimp [a] at hb_lt
          omega
        have h2d : 2 * d ≤ r := by omega
        rw [hmax, show r - d - d = r - 2 * d by omega,
          Nat.cast_sub h2d, hrzero, zero_sub]
        push_cast
        ring_nf
      _ = harmonicMod r a * (-(2 : ZMod r) * (d : ZMod r)) := by
        rw [harmonicMod, Finset.sum_mul]
  have hmiddle :
      (∑ x ∈ Finset.range n,
        (((a + x) + 1 : ℕ) : ZMod r)⁻¹ *
          ((r - d - max (2 * ((a + x) + 1)) d : ℕ) : ZMod r)) =
        -(d : ZMod r) *
            (harmonicMod r B - harmonicMod r a) -
          (2 : ZMod r) * (n : ZMod r) := by
    calc
      (∑ x ∈ Finset.range n,
        (((a + x) + 1 : ℕ) : ZMod r)⁻¹ *
          ((r - d - max (2 * ((a + x) + 1)) d : ℕ) : ZMod r)) =
        ∑ x ∈ Finset.range n,
          (-(d : ZMod r) *
            (((a + x) + 1 : ℕ) : ZMod r)⁻¹ - 2) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxlt : x < n := Finset.mem_range.mp hx
        have hlow : d < 2 * (a + x + 1) := by
          dsimp [a]
          omega
        have hupper : d + 2 * (a + x + 1) ≤ r := by
          rw [← hrdecomp]
          dsimp [n] at hxlt
          omega
        have hmax : max (2 * (a + x + 1)) d = 2 * (a + x + 1) :=
          max_eq_left hlow.le
        have hpos : 0 < a + x + 1 := by omega
        have hlt : a + x + 1 < r := by omega
        have hcast : ((a + x + 1 : ℕ) : ZMod r) ≠ 0 := by
          intro hz
          have hdvd := (ZMod.natCast_eq_zero_iff (a + x + 1) r).1 hz
          exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdvd
        have hcast' :
            (1 : ZMod r) + (a : ZMod r) + (x : ZMod r) ≠ 0 := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
            add_left_comm] using hcast
        rw [hmax,
          show r - d - 2 * (a + x + 1) =
            r - (d + 2 * (a + x + 1)) by omega,
          Nat.cast_sub hupper, hrzero, zero_sub]
        push_cast
        have hinv :
            ((1 : ZMod r) + (a : ZMod r) + (x : ZMod r))⁻¹ *
                ((1 : ZMod r) + (a : ZMod r) + (x : ZMod r)) = 1 :=
          inv_mul_cancel₀ hcast'
        linear_combination -2 * hinv
      _ = -(d : ZMod r) *
            (∑ x ∈ Finset.range n,
              (((a + x) + 1 : ℕ) : ZMod r)⁻¹) -
          (2 : ZMod r) * (n : ZMod r) := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      _ = -(d : ZMod r) *
            (harmonicMod r B - harmonicMod r a) -
          (2 : ZMod r) * (n : ZMod r) := by
        rw [← hB, sum_shifted_inv_eq_harmonicMod_sub]
  have hlast :
      (∑ x ∈ Finset.range e,
        ((((a + n) + x) + 1 : ℕ) : ZMod r)⁻¹ *
          ((r - d - max (2 * (((a + n) + x) + 1)) d : ℕ) :
            ZMod r)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hxlt : x < e := Finset.mem_range.mp hx
    have hlarge : r - d ≤ 2 * (a + n + x + 1) := by
      rw [← hrdecomp]
      omega
    have : r - d - max (2 * (a + n + x + 1)) d = 0 := by
      omega
    rw [this, Nat.cast_zero, mul_zero]
  rw [hfirst, hmiddle, hlast, add_zero]
  have haeq : d / 2 = a := rfl
  have hidxB : a + n + e - ceilHalf d = B := by
    rw [show ceilHalf d = e by rfl]
    omega
  have hidxn : a + n + e - d = n := by omega
  rw [haeq, hidxB, hidxn]
  ring

/-- Doubling autocorrelation after evaluating its inner threshold sum. -/
theorem blockAutocorrelationTwo_eq_innerEvaluation
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c =
      (c : ZMod r) *
        ∑ d ∈ Finset.range (halfIndex r),
          ((d + 1 : ℕ) : ZMod r)⁻¹ *
            (-(d + 1 : ZMod r) * harmonicMod r ((d + 1) / 2) -
              (d + 1 : ZMod r) *
                harmonicMod r (halfIndex r - ceilHalf (d + 1)) -
              (2 : ZMod r) *
                ((halfIndex r - (d + 1) : ℕ) : ZMod r)) := by
  rw [blockAutocorrelationTwo_eq_weightedCount hr hr3 hc,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : 1 ≤ d + 1 := by omega
  have hdh : d + 1 ≤ halfIndex r := Finset.mem_range.mp hd
  calc
    (∑ b ∈ Finset.range (halfIndex r),
      ((b + 1 : ℕ) : ZMod r)⁻¹ *
        ((d + 1 : ℕ) : ZMod r)⁻¹ * (c : ZMod r) *
          ((r - (d + 1) - max (2 * (b + 1)) (d + 1) : ℕ) :
            ZMod r)) =
      ((d + 1 : ℕ) : ZMod r)⁻¹ * (c : ZMod r) *
        (∑ b ∈ Finset.range (halfIndex r),
          ((b + 1 : ℕ) : ZMod r)⁻¹ *
            ((r - (d + 1) - max (2 * (b + 1)) (d + 1) : ℕ) :
              ZMod r)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        ring
    _ = ((d + 1 : ℕ) : ZMod r)⁻¹ * (c : ZMod r) *
        (-(d + 1 : ZMod r) * harmonicMod r ((d + 1) / 2) -
          (d + 1 : ZMod r) *
            harmonicMod r (halfIndex r - ceilHalf (d + 1)) -
          (2 : ZMod r) *
            ((halfIndex r - (d + 1) : ℕ) : ZMod r)) := by
      rw [weightedGap_inner hr hr3 hd0 hdh]
      push_cast
      rfl
    _ = (c : ZMod r) *
        (((d + 1 : ℕ) : ZMod r)⁻¹ *
          (-(d + 1 : ZMod r) * harmonicMod r ((d + 1) / 2) -
            (d + 1 : ZMod r) *
              harmonicMod r (halfIndex r - ceilHalf (d + 1)) -
            (2 : ZMod r) *
              ((halfIndex r - (d + 1) : ℕ) : ZMod r))) := by ring

end StepsUnboundedResults.R002
