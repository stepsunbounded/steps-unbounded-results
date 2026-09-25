import StepsUnboundedResults.R002.AutocorrelationCore

namespace StepsUnboundedResults.R002

open scoped BigOperators

theorem le_two_mul_halfIndex_succ {r : ℕ} (hr : 0 < r) :
    r ≤ 2 * (halfIndex r + 1) := by
  simp only [halfIndex]
  omega

/-- The harmonic block index of a positive representative never exceeds
`(r-1)/2`. -/
theorem blockIndex_le_halfIndex
    {r c x : ℕ} (hr : 0 < r) (hc : 0 < c)
    (hx : x ≤ realResidueCount r c) :
    x / (2 * c) ≤ halfIndex r := by
  have hcr : 0 < c * r := Nat.mul_pos hc hr
  have hxlt : x < c * r := by
    rw [realResidueCount] at hx
    omega
  have hrle := le_two_mul_halfIndex_succ hr
  have hmul : c * r ≤ (halfIndex r + 1) * (2 * c) := by
    calc
      c * r ≤ c * (2 * (halfIndex r + 1)) :=
        Nat.mul_le_mul_left c hrle
      _ = (halfIndex r + 1) * (2 * c) := by ring
  have hxbound : x < (halfIndex r + 1) * (2 * c) :=
    lt_of_lt_of_le hxlt hmul
  have hden : 0 < 2 * c := by positivity
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hden]
  exact hxbound

/-- The block-harmonic staircase on positive representatives. -/
def blockHarmonic (r c x : ℕ) : ZMod r :=
  harmonicMod r (x / (2 * c))

/-- Threshold expansion of the block-harmonic staircase. -/
theorem blockHarmonic_threshold
    {r c x : ℕ} (hr : 0 < r) (hc : 0 < c)
    (hx : x ≤ realResidueCount r c) :
    blockHarmonic r c x =
      ∑ b ∈ Finset.range (halfIndex r),
        if 2 * c * (b + 1) ≤ x then
          ((b + 1 : ℕ) : ZMod r)⁻¹ else 0 := by
  rw [blockHarmonic,
    harmonicMod_eq_sum_range_indicator (blockIndex_le_halfIndex hr hc hx)]
  apply Finset.sum_congr rfl
  intro b hb
  have hiff : b < x / (2 * c) ↔ 2 * c * (b + 1) ≤ x := by
    rw [show b < x / (2 * c) ↔ b + 1 ≤ x / (2 * c) by omega,
      Nat.le_div_iff_mul_le (by positivity : 0 < 2 * c)]
    simp only [Nat.mul_comm, Nat.mul_left_comm]
  simp only [hiff]

/-- Autocorrelation at the identity. -/
def blockAutocorrelationOne (r c : ℕ) : ZMod r :=
  ∑ x ∈ positiveRepresentatives (realResidueCount r c),
    blockHarmonic r c x * blockHarmonic r c x

/-- Autocorrelation at doubling. -/
def blockAutocorrelationTwo (r c : ℕ) : ZMod r :=
  ∑ x ∈ positiveRepresentatives (realResidueCount r c),
    blockHarmonic r c x *
      blockHarmonic r c (reflectedDouble (realResidueCount r c) x)

theorem reflectedDouble_le
    {M x : ℕ} (hxM : x ≤ M) :
    reflectedDouble M x ≤ M := by
  simp only [reflectedDouble, min_le_iff]
  omega

/-- Expanding two threshold sums turns their correlation into the cardinality
of the joint threshold locus. -/
theorem sum_mul_indicator_sums
    {K X B D : Type*} [CommSemiring K]
    [DecidableEq X] [DecidableEq B] [DecidableEq D]
    (s : Finset X) (tb : Finset B) (td : Finset D)
    (wb : B → K) (wd : D → K)
    (p : B → X → Prop) (q : D → X → Prop)
    [DecidableRel p] [DecidableRel q] :
    (∑ x ∈ s,
        (∑ b ∈ tb, if p b x then wb b else 0) *
          (∑ d ∈ td, if q d x then wd d else 0)) =
      ∑ b ∈ tb, ∑ d ∈ td,
        wb b * wd d *
          ((s.filter fun x ↦ p b x ∧ q d x).card : K) := by
  classical
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  calc
    (∑ x ∈ s, if q d x then if p b x then wb b * wd d else 0 else 0) =
        ∑ x ∈ s, if p b x ∧ q d x then wb b * wd d else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hp : p b x <;> by_cases hq : q d x <;> simp [hp, hq]
    _ = ∑ x ∈ (s.filter fun x ↦ p b x ∧ q d x), wb b * wd d := by
      exact (Finset.sum_filter (fun x ↦ p b x ∧ q d x)
        (fun _ ↦ wb b * wd d)).symm
    _ = wb b * wd d *
        ((s.filter fun x ↦ p b x ∧ q d x).card : K) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Exact threshold-count expansion of the doubling autocorrelation. -/
theorem blockAutocorrelationTwo_eq_thresholdCount
    {r c : ℕ} (hr : 0 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c =
      ∑ b ∈ Finset.range (halfIndex r),
        ∑ d ∈ Finset.range (halfIndex r),
          ((b + 1 : ℕ) : ZMod r)⁻¹ *
            ((d + 1 : ℕ) : ZMod r)⁻¹ *
              ((doublingThresholdSet (realResidueCount r c)
                (2 * c * (b + 1)) (c * (d + 1))).card : ZMod r) := by
  classical
  rw [blockAutocorrelationTwo]
  calc
    (∑ x ∈ positiveRepresentatives (realResidueCount r c),
        blockHarmonic r c x *
          blockHarmonic r c
            (reflectedDouble (realResidueCount r c) x)) =
      ∑ x ∈ positiveRepresentatives (realResidueCount r c),
        (∑ b ∈ Finset.range (halfIndex r),
          if 2 * c * (b + 1) ≤ x then
            ((b + 1 : ℕ) : ZMod r)⁻¹ else 0) *
        (∑ d ∈ Finset.range (halfIndex r),
          if 2 * c * (d + 1) ≤
              reflectedDouble (realResidueCount r c) x then
            ((d + 1 : ℕ) : ZMod r)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxIcc := (Finset.mem_Icc.mp hx)
      rw [blockHarmonic_threshold hr hc hxIcc.2,
        blockHarmonic_threshold hr hc
          (reflectedDouble_le hxIcc.2)]
    _ = _ := by
      rw [sum_mul_indicator_sums
        (positiveRepresentatives (realResidueCount r c))
        (Finset.range (halfIndex r)) (Finset.range (halfIndex r))
        (fun b ↦ ((b + 1 : ℕ) : ZMod r)⁻¹)
        (fun d ↦ ((d + 1 : ℕ) : ZMod r)⁻¹)
        (fun b x ↦ 2 * c * (b + 1) ≤ x)
        (fun d x ↦ 2 * c * (d + 1) ≤
          reflectedDouble (realResidueCount r c) x)]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro d hd
      congr 3
      ext x
      simp only [positiveRepresentatives, Finset.mem_filter, Finset.mem_Icc,
        doublingThresholdSet, reflectedDouble, Nat.mul_assoc]

end StepsUnboundedResults.R002
