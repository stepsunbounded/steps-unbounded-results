import StepsUnboundedResults.R002.EisensteinBinomial

namespace StepsUnboundedResults.R002

open scoped BigOperators

/-- The first `n` alternating reciprocals are `H_n-H_⌊n/2⌋`. -/
theorem alternating_harmonicMod_eq_sub_half
    {r n : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hn : n < r) :
    (∑ d ∈ Finset.range n,
      (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹) =
        harmonicMod r n - harmonicMod r (n / 2) := by
  letI : Fact r.Prime := ⟨hr⟩
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < r := Nat.lt_trans (Nat.lt_succ_self n) hn
      rw [Finset.sum_range_succ, ih hnlt, harmonicMod_succ]
      rcases Nat.even_or_odd n with heven | hodd
      · obtain ⟨m, rfl⟩ := heven
        have hprev : (m + m) / 2 = m := by omega
        have hnext : (m + m + 1) / 2 = m := by omega
        rw [hprev, hnext, (Even.add_self m).neg_one_pow]
        ring
      · obtain ⟨m, rfl⟩ := hodd
        have hprev : (2 * m + 1) / 2 = m := by omega
        have hnext : (2 * m + 1 + 1) / 2 = m + 1 := by omega
        have hoddexp : Odd (2 * m + 1) := by use m
        rw [hprev, hnext, harmonicMod_succ, hoddexp.neg_one_pow]
        have hmpos : 0 < m + 1 := by omega
        have hmlt : m + 1 < r := by omega
        have htwomlt : m + m + 2 < r := by omega
        have hmcast : ((m + 1 : ℕ) : ZMod r) ≠ 0 := by
          intro hz
          have hdvd := (ZMod.natCast_eq_zero_iff (m + 1) r).1 hz
          exact (Nat.not_dvd_of_pos_of_lt hmpos hmlt) hdvd
        have htwocast : ((m + m + 2 : ℕ) : ZMod r) ≠ 0 := by
          intro hz
          have hdvd := (ZMod.natCast_eq_zero_iff (m + m + 2) r).1 hz
          exact (Nat.not_dvd_of_pos_of_lt (by omega) htwomlt) hdvd
        have hinv :
            (2 : ZMod r) * ((m + m + 2 : ℕ) : ZMod r)⁻¹ =
              ((m + 1 : ℕ) : ZMod r)⁻¹ := by
          have htwo : (2 : ZMod r) ≠ 0 := by
            intro hz
            have hdvd := (ZMod.natCast_eq_zero_iff 2 r).1 hz
            exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
          have hden : ((m + m + 2 : ℕ) : ZMod r) =
              (2 : ZMod r) * ((m + 1 : ℕ) : ZMod r) := by
            push_cast
            ring
          rw [hden, mul_inv_rev]
          calc
            (2 : ZMod r) *
                (((m + 1 : ℕ) : ZMod r)⁻¹ * (2 : ZMod r)⁻¹) =
                ((m + 1 : ℕ) : ZMod r)⁻¹ *
                  ((2 : ZMod r) * (2 : ZMod r)⁻¹) := by ring
            _ = ((m + 1 : ℕ) : ZMod r)⁻¹ := by
              rw [mul_inv_cancel₀ htwo, mul_one]
        have hidx : 2 * m + 1 + 1 = m + m + 2 := by omega
        rw [hidx, harmonicMod_succ]
        linear_combination -hinv

end StepsUnboundedResults.R002
