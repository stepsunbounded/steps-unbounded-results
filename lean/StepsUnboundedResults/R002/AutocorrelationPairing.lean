import StepsUnboundedResults.R002.AutocorrelationGap

namespace StepsUnboundedResults.R002

open scoped BigOperators

/-- Cancellation of the target threshold against its reciprocal gives the
intermediate harmonic expression from the elementary proof. -/
theorem blockAutocorrelationTwo_eq_intermediateSum
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c =
      (c : ZMod r) *
        ∑ d ∈ Finset.range (halfIndex r),
          (-harmonicMod r ((d + 1) / 2) -
            harmonicMod r (halfIndex r - ceilHalf (d + 1)) -
            (2 : ZMod r) *
              ((halfIndex r - (d + 1) : ℕ) : ZMod r) *
                ((d + 1 : ℕ) : ZMod r)⁻¹) := by
  letI : Fact r.Prime := ⟨hr⟩
  rw [blockAutocorrelationTwo_eq_innerEvaluation hr hr3 hc]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdlt : d + 1 < r := by
    have hdh : d + 1 ≤ halfIndex r := Finset.mem_range.mp hd
    have hh : halfIndex r < r := by
      simp only [halfIndex]
      omega
    exact lt_of_le_of_lt hdh hh
  have hdpos : 0 < d + 1 := by omega
  have hcast : ((d + 1 : ℕ) : ZMod r) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff (d + 1) r).1 hz
    exact (Nat.not_dvd_of_pos_of_lt hdpos hdlt) hdvd
  push_cast
  have hcast' : (d : ZMod r) + 1 ≠ 0 := by simpa using hcast
  field_simp [hcast']

/-- Pairing odd and even thresholds evaluates the two floor/ceiling harmonic sums. -/
theorem paired_harmonicMod_sum
    (r h : ℕ) (hh : 1 ≤ h) :
    (∑ d ∈ Finset.range h, harmonicMod r ((d + 1) / 2)) +
        (∑ d ∈ Finset.range h,
          harmonicMod r (h - ceilHalf (d + 1))) =
      (2 : ZMod r) *
          (∑ j ∈ Finset.range (h - 1), harmonicMod r (j + 1)) +
        harmonicMod r (h / 2) := by
  rcases Nat.even_or_odd h with heven | hodd
  · obtain ⟨m, rfl⟩ := heven
    have hm : 1 ≤ m := by omega
    let F : ℕ → ZMod r := harmonicMod r
    let A0 : ZMod r := ∑ k ∈ Finset.range m, F k
    let A1 : ZMod r := ∑ k ∈ Finset.range m, F (k + 1)
    let C : ZMod r := ∑ k ∈ Finset.range m, F (m + k)
    let T : ZMod r :=
      ∑ j ∈ Finset.range (m + m - 1), F (j + 1)
    have hAshift : A1 = A0 + F m := by
      simpa [A0, A1, F] using
        sum_range_shift_eq_sum_add_last F m (by simp [F])
    have hCreflect :
        (∑ k ∈ Finset.range m, F (m + m - k - 1)) = C := by
      calc
        (∑ k ∈ Finset.range m, F (m + m - k - 1)) =
            ∑ k ∈ Finset.range m, F (m + (m - 1 - k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt := Finset.mem_range.mp hk
          congr 2
          omega
        _ = ∑ k ∈ Finset.range m, F (m + k) := by
          exact Finset.sum_range_reflect (fun k ↦ F (m + k)) m
        _ = C := rfl
    let Tail : ZMod r :=
      ∑ k ∈ Finset.range (m - 1), F (m + k + 1)
    have hCtail : C = F m + Tail := by
      have hs := first_add_sum_range_shift (fun k ↦ F (m + k)) (m - 1)
      have hmback : m - 1 + 1 = m := by omega
      rw [hmback] at hs
      change F m + Tail = C at hs
      exact hs.symm
    have hT : T = A1 + C - F m := by
      have hlen : m + m - 1 = m + (m - 1) := by omega
      change (∑ j ∈ Finset.range (m + m - 1), F (j + 1)) =
        A1 + C - F m
      rw [hlen, Finset.sum_range_add]
      change A1 + Tail = A1 + C - F m
      rw [hCtail]
      ring
    rw [← Finset.sum_add_distrib]
    let g : ℕ → ZMod r := fun d ↦
      F ((d + 1) / 2) + F (m + m - ceilHalf (d + 1))
    change (∑ d ∈ Finset.range (m + m), g d) =
      (2 : ZMod r) * T + F ((m + m) / 2)
    calc
      (∑ d ∈ Finset.range (m + m), g d) =
          ∑ d ∈ Finset.range (2 * m), g d := by
        congr 2
        omega
      _ = ∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1)) :=
        sum_range_two_mul g m
      _ = ∑ k ∈ Finset.range m,
          (F k + F (k + 1) +
            (2 : ZMod r) * F (m + m - k - 1)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt := Finset.mem_range.mp hk
        simp only [g, ceilHalf]
        have h1 : (2 * k + 1) / 2 = k := by omega
        have h2 : (2 * k + 2) / 2 = k + 1 := by omega
        have h3 : (2 * k + 2 + 1) / 2 = k + 1 := by omega
        rw [h1, h2, h3]
        have hidx : m + m - (k + 1) = m + m - k - 1 := by omega
        rw [hidx]
        ring
      _ = A0 + A1 + (2 : ZMod r) * C := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, hCreflect]
      _ = (2 : ZMod r) * T + F ((m + m) / 2) := by
        have hmhalf : (m + m) / 2 = m := by omega
        rw [hmhalf, hT, hAshift]
        ring
  · obtain ⟨m, rfl⟩ := hodd
    rw [show 2 * m + 1 = m + m + 1 by omega]
    let F : ℕ → ZMod r := harmonicMod r
    let A0 : ZMod r := ∑ k ∈ Finset.range m, F k
    let A1 : ZMod r := ∑ k ∈ Finset.range m, F (k + 1)
    let C : ZMod r := ∑ k ∈ Finset.range m, F (m + 1 + k)
    let T : ZMod r :=
      ∑ j ∈ Finset.range (m + m), F (j + 1)
    have hAshift : A1 = A0 + F m := by
      simpa [A0, A1, F] using
        sum_range_shift_eq_sum_add_last F m (by simp [F])
    have hCreflect :
        (∑ k ∈ Finset.range m, F (m + m - k)) = C := by
      calc
        (∑ k ∈ Finset.range m, F (m + m - k)) =
            ∑ k ∈ Finset.range m, F (m + 1 + (m - 1 - k)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hklt := Finset.mem_range.mp hk
          congr 2
          omega
        _ = ∑ k ∈ Finset.range m, F (m + 1 + k) := by
          exact Finset.sum_range_reflect (fun k ↦ F (m + 1 + k)) m
        _ = C := rfl
    have hT : T = A1 + C := by
      change (∑ j ∈ Finset.range (m + m), F (j + 1)) = A1 + C
      rw [show m + m = m + m by rfl, Finset.sum_range_add]
      change A1 + (∑ x ∈ Finset.range m, F (m + x + 1)) = A1 + C
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    rw [← Finset.sum_add_distrib]
    let g : ℕ → ZMod r := fun d ↦
      F ((d + 1) / 2) + F (m + m + 1 - ceilHalf (d + 1))
    change (∑ d ∈ Finset.range (m + m + 1), g d) =
      (2 : ZMod r) * T + F ((m + m + 1) / 2)
    rw [show m + m + 1 = 2 * m + 1 by omega,
      Finset.sum_range_succ, sum_range_two_mul]
    calc
      (∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1))) +
          g (2 * m) =
        A0 + A1 + (2 : ZMod r) * C + (2 : ZMod r) * F m := by
          have hpairs :
              (∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1))) =
                A0 + A1 + (2 : ZMod r) * C := by
            calc
              (∑ k ∈ Finset.range m, (g (2 * k) + g (2 * k + 1))) =
                  ∑ k ∈ Finset.range m,
                    (F k + F (k + 1) +
                      (2 : ZMod r) * F (m + m - k)) := by
                apply Finset.sum_congr rfl
                intro k hk
                have hklt := Finset.mem_range.mp hk
                simp only [g, ceilHalf]
                have h1 : (2 * k + 1) / 2 = k := by omega
                have h2 : (2 * k + 2) / 2 = k + 1 := by omega
                have h3 : (2 * k + 2 + 1) / 2 = k + 1 := by omega
                rw [h1, h2, h3]
                have hidx : m + m + 1 - (k + 1) = m + m - k := by omega
                rw [hidx]
                ring
              _ = A0 + A1 + (2 : ZMod r) * C := by
                rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
                  ← Finset.mul_sum, hCreflect]
          rw [hpairs]
          have hlast : g (2 * m) = (2 : ZMod r) * F m := by
            simp only [g, ceilHalf]
            have h1 : (2 * m + 1) / 2 = m := by omega
            have h2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
            rw [h1, h2]
            have hidx : m + m + 1 - (m + 1) = m := by omega
            rw [hidx]
            ring
          rw [hlast]
      _ = (2 : ZMod r) * T + F ((2 * m + 1) / 2) := by
        have hmhalf : (2 * m + 1) / 2 = m := by omega
        rw [hmhalf, hT, hAshift]
        ring

end StepsUnboundedResults.R002
