import StepsUnboundedResults.R002.AutocorrelationClosed

namespace StepsUnboundedResults.R002

open scoped BigOperators

theorem choose_prime_sub_one_mod
    {r k : ℕ} (hr : r.Prime) (hk : k < r) :
    (((r - 1).choose k : ℕ) : ZMod r) = (-1 : ZMod r) ^ k := by
  letI : Fact r.Prime := ⟨hr⟩
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < r := Nat.lt_trans (Nat.lt_succ_self k) hk
      have hkpos : 0 < k + 1 := by omega
      have hcast : ((k + 1 : ℕ) : ZMod r) ≠ 0 := by
        intro hz
        have hdvd := (ZMod.natCast_eq_zero_iff (k + 1) r).1 hz
        exact (Nat.not_dvd_of_pos_of_lt hkpos hk) hdvd
      have hchoose := congrArg (fun n : ℕ ↦ (n : ZMod r))
        (Nat.choose_succ_right_eq (r - 1) k)
      push_cast at hchoose
      rw [ih hklt] at hchoose
      have hsub : (((r - 1 - k : ℕ) : ZMod r)) =
          -((k + 1 : ℕ) : ZMod r) := by
        have hnat : r - 1 - k + (k + 1) = r := by omega
        have hnatcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hnat
        push_cast at hnatcast ⊢
        rw [ZMod.natCast_self] at hnatcast
        linear_combination hnatcast
      push_cast at hcast hsub ⊢
      apply mul_right_cancel₀ hcast
      rw [hchoose, hsub, pow_succ]
      ring

theorem choose_div_prime_mod
    {r k : ℕ} (hr : r.Prime) (hk0 : 0 < k) (hkr : k < r) :
    ((r.choose k / r : ℕ) : ZMod r) =
      (-1 : ZMod r) ^ (k - 1) * ((k : ℕ) : ZMod r)⁻¹ := by
  letI : Fact r.Prime := ⟨hr⟩
  have hdiv : r ∣ r.choose k := hr.dvd_choose_self (by omega) hkr
  have hmul : r * (r.choose k / r) = r.choose k := Nat.mul_div_cancel' hdiv
  have hchoose := Nat.add_one_mul_choose_eq (r - 1) (k - 1)
  have hrback : r - 1 + 1 = r := by omega
  have hkback : k - 1 + 1 = k := by omega
  rw [hrback, hkback] at hchoose
  have hrel : (r - 1).choose (k - 1) = (r.choose k / r) * k := by
    apply Nat.mul_left_cancel hr.pos
    calc
      r * (r - 1).choose (k - 1) = r.choose k * k := hchoose
      _ = (r * (r.choose k / r)) * k := congrArg (fun n : ℕ ↦ n * k) hmul.symm
      _ = r * ((r.choose k / r) * k) := by rw [Nat.mul_assoc]
  have hrelcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hrel
  push_cast at hrelcast
  have hkcast : ((k : ℕ) : ZMod r) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff k r).1 hz
    exact (Nat.not_dvd_of_pos_of_lt hk0 hkr) hdvd
  apply mul_right_cancel₀ hkcast
  calc
    ((r.choose k / r : ℕ) : ZMod r) * (k : ZMod r) =
        (((r - 1).choose (k - 1) : ℕ) : ZMod r) := hrelcast.symm
    _ = (-1 : ZMod r) ^ (k - 1) := choose_prime_sub_one_mod hr (by omega)
    _ = ((-1 : ZMod r) ^ (k - 1) * (k : ZMod r)⁻¹) * (k : ZMod r) := by
      rw [mul_assoc, inv_mul_cancel₀ hkcast, mul_one]

theorem two_mul_fermatQuotientTwo_eq_alternating
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    (2 : ZMod r) * (fermatQuotientTwo r : ZMod r) =
      ∑ d ∈ Finset.range (r - 1),
        (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹ := by
  let A : ℕ := ∑ d ∈ Finset.range (r - 1), r.choose (d + 1) / r
  let I : ℕ := ∑ d ∈ Finset.range (r - 1), r.choose (d + 1)
  have hrback : r - 1 + 1 = r := by omega
  have hfirst := first_add_sum_range_shift (fun k ↦ r.choose k) (r - 1)
  rw [hrback] at hfirst
  have hall := Nat.sum_range_choose r
  rw [Finset.sum_range_succ] at hall
  have hI : I = 2 ^ r - 2 := by
    change (∑ d ∈ Finset.range (r - 1), r.choose (d + 1)) = _
    simp only [Nat.choose_zero_right] at hfirst
    rw [← hfirst] at hall
    simp only [Nat.choose_self] at hall
    omega
  have hrA : r * A = I := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hdlt : d < r - 1 := Finset.mem_range.mp hd
    exact Nat.mul_div_cancel' (hr.dvd_choose_self (by omega) (by omega))
  have hcop : Nat.Coprime 2 r :=
    (Nat.coprime_primes Nat.prime_two hr).2 (by omega)
  have hdivN : r ∣ 2 ^ (r - 1) - 1 :=
    Nat.dvd_of_mod_eq_zero (Nat.pow_card_sub_one_sub_one_mod_card hr hcop)
  have hrq : r * fermatQuotientTwo r = 2 ^ (r - 1) - 1 := by
    exact Nat.mul_div_cancel' hdivN
  have hpow : 2 ^ r = 2 * 2 ^ (r - 1) := by
    conv_lhs => rw [← hrback, pow_succ]
    ring
  have hAq : A = 2 * fermatQuotientTwo r := by
    apply Nat.mul_left_cancel hr.pos
    rw [hrA, hI, hpow]
    have hone : 1 ≤ 2 ^ (r - 1) := one_le_pow₀ (by omega)
    calc
      2 * 2 ^ (r - 1) - 2 = 2 * (2 ^ (r - 1) - 1) := by omega
      _ = 2 * (r * fermatQuotientTwo r) := by rw [hrq]
      _ = r * (2 * fermatQuotientTwo r) := by ring
  have hAqcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hAq
  push_cast at hAqcast
  rw [← hAqcast]
  change
    ((∑ d ∈ Finset.range (r - 1), r.choose (d + 1) / r : ℕ) : ZMod r) = _
  push_cast
  apply Finset.sum_congr rfl
  intro d hd
  have hdlt : d < r - 1 := Finset.mem_range.mp hd
  simpa using choose_div_prime_mod hr (k := d + 1) (by omega) (by omega)

end StepsUnboundedResults.R002
