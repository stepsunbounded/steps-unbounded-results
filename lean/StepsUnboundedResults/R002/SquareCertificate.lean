import StepsUnboundedResults.R002.Definitions

namespace StepsUnboundedResults.R002

/-- A prime divisor of the carrier of a coprime square certificate is odd. -/
theorem prime_divisor_ne_two_of_coprime_squareCertificate
    {N L q : ℕ} (hcert : IsCoprimeSquareCertificate N L)
    (hq : q.Prime) (hqN : q ∣ N) : q ≠ 2 := by
  rcases hcert with ⟨hN, hNL, hsq⟩
  have hL0 : L ≠ 0 := by
    intro hL
    subst L
    have : N = 1 := by simpa using hNL
    omega
  have hqSq : q ^ 2 ∣ 2 ^ L - 1 :=
    (pow_dvd_pow_of_dvd hqN 2).trans hsq
  intro hq2
  subst q
  have heven : Even (2 ^ L - 1) := by
    rw [even_iff_two_dvd]
    exact (by norm_num : 2 ∣ 2 ^ 2) |>.trans hqSq
  have hodd : Odd (2 ^ L - 1) := by
    simpa [mersenne] using (mersenne_odd (p := L)).2 hL0
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/--
The elementary core of the square-certificate implication.  The proof uses the order of `2`
in `(ZMod (q^2))ˣ`: it divides both `L` and `q(q-1)`, and coprimality with `q` removes the
extra factor `q`.
-/
theorem prime_divisor_isWieferich_of_coprime_squareCertificate
    {N L q : ℕ} (hcert : IsCoprimeSquareCertificate N L)
    (hq : q.Prime) (hqN : q ∣ N) : IsWieferich q := by
  rcases hcert with ⟨hN, hNL, hsq⟩
  have hqL : Nat.Coprime q L := Nat.Coprime.of_dvd_left hqN hNL
  have hqSq : q ^ 2 ∣ 2 ^ L - 1 :=
    (pow_dvd_pow_of_dvd hqN 2).trans hsq
  have hqne2 : q ≠ 2 :=
    prime_divisor_ne_two_of_coprime_squareCertificate ⟨hN, hNL, hsq⟩ hq hqN
  have hqndiv2 : ¬ q ∣ 2 := by
    intro hq2
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
    exact hqne2 (Nat.le_antisymm hqle hq.two_le)
  have htwoqSq : Nat.Coprime 2 (q ^ 2) :=
    (hq.coprime_iff_not_dvd.mpr hqndiv2).symm.pow_right 2
  let u : (ZMod (q ^ 2))ˣ := ZMod.unitOfCoprime 2 htwoqSq
  have hmodL : 1 ≡ 2 ^ L [MOD q ^ 2] := by
    exact (Nat.modEq_iff_dvd' (one_le_pow₀ one_le_two)).2 hqSq
  have huL : u ^ L = 1 := by
    apply Units.ext
    simpa [u, ZMod.coe_unitOfCoprime] using
      (ZMod.natCast_eq_natCast_iff (2 ^ L) 1 (q ^ 2)).2 hmodL.symm
  have horderL : orderOf u ∣ L := orderOf_dvd_of_pow_eq_one huL
  letI : NeZero (q ^ 2) := ⟨pow_ne_zero 2 hq.ne_zero⟩
  have horderCard : orderOf u ∣ Fintype.card (ZMod (q ^ 2))ˣ :=
    orderOf_dvd_card
  have htotient : Nat.totient (q ^ 2) = q * (q - 1) := by
    rw [Nat.totient_prime_pow (n := 2) hq (by norm_num)]
    norm_num
  have horderProd : orderOf u ∣ q * (q - 1) := by
    rw [ZMod.card_units_eq_totient, htotient] at horderCard
    exact horderCard
  have hqOrder : Nat.Coprime q (orderOf u) :=
    Nat.Coprime.of_dvd_right horderL hqL
  have horderSub : orderOf u ∣ q - 1 :=
    hqOrder.symm.dvd_of_dvd_mul_left horderProd
  have huSub : u ^ (q - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp horderSub
  have hmodSub : 2 ^ (q - 1) ≡ 1 [MOD q ^ 2] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa [u, ZMod.coe_unitOfCoprime] using congrArg Units.val huSub
  exact (Nat.modEq_iff_dvd' (one_le_pow₀ one_le_two)).mp hmodSub.symm

/-- Every prime divisor of the carrier in a coprime square certificate is Wieferich. -/
theorem all_prime_divisors_wieferich_of_coprime_squareCertificate
    {N L : ℕ} (hcert : IsCoprimeSquareCertificate N L) :
    ∀ q, q.Prime → q ∣ N → IsWieferich q := by
  intro q hq hqN
  exact prime_divisor_isWieferich_of_coprime_squareCertificate hcert hq hqN

end StepsUnboundedResults.R002
