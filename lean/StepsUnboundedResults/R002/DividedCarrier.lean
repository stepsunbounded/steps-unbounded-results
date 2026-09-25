import StepsUnboundedResults.R002.LocalCriterion
import Mathlib.Data.Nat.Squarefree

/-!
# The divided-carrier selector

For a squarefree divisor `Y` of `2 ^ L - 1`, coprime to `L`, the divided
quotient `(2 ^ L - 1) / Y` contains a carrier prime `q` exactly when `q` is
base-two Wieferich.  This is the prime-support content of the CRT
diagonalization theorem; it avoids choosing inverses or CRT idempotents.
-/

namespace StepsUnboundedResults.R002

/-- The integral divided quotient attached to a candidate carrier. -/
def dividedCarrier (Y L : ℕ) : ℕ :=
  (2 ^ L - 1) / Y

/-- A prime divisor of a Mersenne value sees an exponent divisible by the order of two. -/
theorem orderOf_two_dvd_of_prime_dvd_mersenne
    {q L : ℕ} (hqdiv : q ∣ 2 ^ L - 1) :
    orderOf (2 : ZMod q) ∣ L := by
  have hmod : 2 ^ L ≡ 1 [MOD q] :=
    ((Nat.modEq_iff_dvd' (one_le_pow₀ one_le_two)).mpr hqdiv).symm
  have hpow : (2 : ZMod q) ^ L = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff (2 ^ L) 1 q).mpr hmod
  exact orderOf_dvd_of_pow_eq_one hpow

/--
Prime-support form of the exact CRT selector: among the prime factors of a
squarefree coprime carrier, the divided quotient selects precisely the
Wieferich primes.
-/
theorem prime_dvd_dividedCarrier_iff_wieferich
    {Y L q : ℕ} (hY : 1 < Y) (hYsq : Squarefree Y)
    (hYL : Nat.Coprime Y L) (hYdiv : Y ∣ 2 ^ L - 1)
    (hq : q.Prime) (hqY : q ∣ Y) :
    q ∣ dividedCarrier Y L ↔ IsWieferich q := by
  have hL : L ≠ 0 := by
    intro hL0
    subst L
    have : Y = 1 := by simpa using hYL
    omega
  have hqL : Nat.Coprime q L := Nat.Coprime.of_dvd_left hqY hYL
  have hqM : q ∣ 2 ^ L - 1 := hqY.trans hYdiv
  have hqne2 : q ≠ 2 := by
    intro hq2
    subst q
    have heven : Even (2 ^ L - 1) := by
      rw [even_iff_two_dvd]
      exact hqM
    have hodd : Odd (2 ^ L - 1) := by
      simpa [mersenne] using (mersenne_odd (p := L)).2 hL
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  letI : Fact q.Prime := ⟨hq⟩
  have hproduct : Y * dividedCarrier Y L = 2 ^ L - 1 := by
    exact Nat.mul_div_cancel' hYdiv
  constructor
  · intro hqT
    obtain ⟨R, hYR⟩ := hqY
    obtain ⟨S, hTS⟩ := hqT
    have hqSq : q ^ 2 ∣ 2 ^ L - 1 := by
      refine ⟨R * S, ?_⟩
      calc
        2 ^ L - 1 = Y * dividedCarrier Y L := hproduct.symm
        _ = Y * (q * S) := by rw [hTS]
        _ = (q * R) * (q * S) := by rw [hYR]
        _ = q ^ 2 * (R * S) := by ring
    exact prime_divisor_isWieferich_of_coprime_squareCertificate
      ⟨hq.one_lt, hqL, hqSq⟩ hq dvd_rfl
  · intro hwieferich
    have horder : orderOf (2 : ZMod q) ∣ L :=
      orderOf_two_dvd_of_prime_dvd_mersenne hqM
    have hfermatNe : 2 ^ (q - 1) - 1 ≠ 0 := by
      exact Nat.sub_ne_zero_of_lt
        (one_lt_pow₀ one_lt_two (Nat.sub_ne_zero_of_lt hq.one_lt))
    have hdepth : 2 ≤ padicValNat q (2 ^ (q - 1) - 1) :=
      (padicValNat_dvd_iff_le hfermatNe).mp hwieferich
    have hqSq : q ^ 2 ∣ 2 ^ L - 1 := by
      have hlocal :=
        (primePower_dvd_two_pow_sub_one_iff (e := 1) hq hqne2 (by omega) hL hqL).mpr
          ⟨horder, by simpa using hdepth⟩
      simpa using hlocal
    obtain ⟨R, hYR⟩ := hqY
    have hcop : Nat.Coprime q R := by
      rw [hYR] at hYsq
      exact Nat.coprime_of_squarefree_mul hYsq
    obtain ⟨K, hK⟩ := hqSq
    have heq : q * (R * dividedCarrier Y L) = q * (q * K) := by
      calc
        q * (R * dividedCarrier Y L) =
            Y * dividedCarrier Y L := by rw [hYR]; ring
        _ = 2 ^ L - 1 := hproduct
        _ = q ^ 2 * K := hK
        _ = q * (q * K) := by ring
    have hRT : R * dividedCarrier Y L = q * K := by
      exact Nat.eq_of_mul_eq_mul_left hq.pos heq
    apply hcop.dvd_of_dvd_mul_left
    exact ⟨K, hRT⟩

/-- The gcd with the divided quotient has exactly the same prime support. -/
theorem prime_dvd_gcd_dividedCarrier_iff_wieferich
    {Y L q : ℕ} (hY : 1 < Y) (hYsq : Squarefree Y)
    (hYL : Nat.Coprime Y L) (hYdiv : Y ∣ 2 ^ L - 1)
    (hq : q.Prime) (hqY : q ∣ Y) :
    q ∣ Nat.gcd Y (dividedCarrier Y L) ↔ IsWieferich q := by
  rw [Nat.dvd_gcd_iff]
  simp only [hqY, true_and]
  exact prime_dvd_dividedCarrier_iff_wieferich hY hYsq hYL hYdiv hq hqY

end StepsUnboundedResults.R002
