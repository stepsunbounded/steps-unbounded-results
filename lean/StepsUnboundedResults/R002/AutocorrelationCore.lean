import StepsUnboundedResults.R002.CRTUnitFormula
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite harmonic autocorrelation

This file contains the elementary finite part of the reflected
autocorrelation program. All sums are explicit sums in `ZMod r`.
-/

namespace StepsUnboundedResults.R002

open scoped BigOperators

/-- The finite harmonic sum `H_n` in `ZMod r`. -/
def harmonicMod (r n : ℕ) : ZMod r :=
  ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ZMod r)⁻¹

@[simp]
theorem harmonicMod_zero (r : ℕ) : harmonicMod r 0 = 0 := by
  simp [harmonicMod]

theorem harmonicMod_succ (r n : ℕ) :
    harmonicMod r (n + 1) =
      harmonicMod r n + ((n + 1 : ℕ) : ZMod r)⁻¹ := by
  simp [harmonicMod, Finset.sum_range_succ]

/-- The elementary telescoping identity for sums of harmonic squares,
valid before the characteristic is reached. -/
theorem sum_harmonicMod_sq
    {r n : ℕ} (hr : r.Prime) (hn : n < r) :
    ∑ j ∈ Finset.range n, harmonicMod r (j + 1) ^ 2 =
      ((n + 1 : ℕ) : ZMod r) * harmonicMod r n ^ 2 -
        ((2 * n + 1 : ℕ) : ZMod r) * harmonicMod r n +
          ((2 * n : ℕ) : ZMod r) := by
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
      have hcast' : (n : ZMod r) + 1 ≠ 0 := by
        simpa using hcast
      field_simp [hcast']
      ring

/-- The positive representative range has size `M`. -/
def positiveRepresentatives (M : ℕ) : Finset ℕ :=
  Finset.Icc 1 M

/-- For an odd modulus `2M+1`, the positive representative of twice `x`
modulo sign. -/
def reflectedDouble (M x : ℕ) : ℕ :=
  min (2 * x) (2 * M + 1 - 2 * x)

/-- Joint source/target threshold set for doubling. -/
def doublingThresholdSet (M L D : ℕ) : Finset ℕ :=
  (positiveRepresentatives M).filter fun x ↦
    L ≤ x ∧ 2 * D ≤ reflectedDouble M x

/-- The doubling threshold inequalities cut out one ordinary interval. -/
theorem doublingThresholdSet_eq_Icc
    {M L D : ℕ} (hD : 1 ≤ D) (hDM : D ≤ M) :
    doublingThresholdSet M L D = Finset.Icc (max L D) (M - D) := by
  ext x
  simp only [doublingThresholdSet, positiveRepresentatives,
    Finset.mem_filter, Finset.mem_Icc, reflectedDouble,
    le_min_iff, max_le_iff]
  omega

/-- Exact threshold count in endpoint form. -/
theorem card_doublingThresholdSet
    {M L D : ℕ} (hD : 1 ≤ D) (hDM : D ≤ M) :
    (doublingThresholdSet M L D).card =
      M - D + 1 - max L D := by
  rw [doublingThresholdSet_eq_Icc hD hDM, Nat.card_Icc]

/-- Half the nonzero residues for an odd prime. -/
def halfIndex (r : ℕ) : ℕ := (r - 1) / 2

/-- Number of positive representatives in the real residue group for
`P = 2*c*r-1`. -/
def realResidueCount (r c : ℕ) : ℕ := c * r - 1

/-- The exact block-threshold count used by the doubling autocorrelation. -/
theorem card_blockDoublingThreshold
    {r c b d : ℕ} (hc : 0 < c) (hr : 3 < r)
    (hd0 : 1 ≤ d) (hdh : d ≤ halfIndex r) :
    (doublingThresholdSet (realResidueCount r c) (2 * c * b) (c * d)).card =
      c * (r - d - max (2 * b) d) := by
  have hh_lt : halfIndex r < r := by
    simp only [halfIndex]
    omega
  have hdlt : d < r := lt_of_le_of_lt hdh hh_lt
  have hD : 1 ≤ c * d := by
    have hdpos : 0 < d := by omega
    exact Nat.mul_pos hc hdpos
  have hDM : c * d ≤ realResidueCount r c := by
    rw [realResidueCount]
    have : c * d < c * r := Nat.mul_lt_mul_of_pos_left hdlt hc
    omega
  rw [card_doublingThresholdSet hD hDM, realResidueCount]
  have hmax : max (2 * c * b) (c * d) = c * max (2 * b) d := by
    calc
      max (2 * c * b) (c * d) = max (c * (2 * b)) (c * d) := by
        congr 1
        ring
      _ = c * max (2 * b) d := max_mul_mul_left c (2 * b) d
  rw [hmax]
  have hcd_le : c * d ≤ c * r := Nat.mul_le_mul_left c hdlt.le
  calc
    c * r - 1 - c * d + 1 - c * max (2 * b) d =
        (c * r - c * d) - c * max (2 * b) d := by omega
    _ = c * (r - d) - c * max (2 * b) d := by
      rw [Nat.mul_sub_left_distrib]
    _ = c * (r - d - max (2 * b) d) := by
      exact (Nat.mul_sub_left_distrib c (r - d) (max (2 * b) d)).symm

/-- A finite harmonic sum can be padded to any larger range by threshold
indicators. -/
theorem harmonicMod_eq_sum_range_indicator
    {r n h : ℕ} (hnh : n ≤ h) :
    harmonicMod r n =
      ∑ b ∈ Finset.range h,
        if b < n then ((b + 1 : ℕ) : ZMod r)⁻¹ else 0 := by
  rw [harmonicMod]
  calc
    ∑ b ∈ Finset.range n, ((b + 1 : ℕ) : ZMod r)⁻¹ =
        ∑ b ∈ (Finset.range h).filter (fun b ↦ b < n),
          ((b + 1 : ℕ) : ZMod r)⁻¹ := by
      congr 1
      ext b
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    _ = ∑ b ∈ Finset.range h,
          if b < n then ((b + 1 : ℕ) : ZMod r)⁻¹ else 0 := by
      exact Finset.sum_filter (fun b ↦ b < n)
        (fun b ↦ ((b + 1 : ℕ) : ZMod r)⁻¹)

end StepsUnboundedResults.R002
