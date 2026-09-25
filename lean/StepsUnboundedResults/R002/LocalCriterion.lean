import StepsUnboundedResults.R002.SquareCertificate
import Mathlib.NumberTheory.Multiplicity

namespace StepsUnboundedResults.R002

/-- A positive Mersenne number is nonzero. -/
private theorem two_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) : 2 ^ n - 1 ≠ 0 := by
  exact Nat.sub_ne_zero_of_lt (one_lt_pow₀ one_lt_two hn)

/--
LTE at the exact order: when `q` is coprime to the exponent, passing from
`ord_q(2)` to any multiple `n` does not change the `q`-adic depth.
-/
theorem padicValNat_two_pow_sub_one_eq_at_order
    {q n : ℕ} (hq : q.Prime) (hqne2 : q ≠ 2) (hn : n ≠ 0)
    (hcop : Nat.Coprime q n)
    (horder : orderOf (2 : ZMod q) ∣ n) :
    padicValNat q (2 ^ n - 1) =
      padicValNat q (2 ^ orderOf (2 : ZMod q) - 1) := by
  let d := orderOf (2 : ZMod q)
  let k := n / d
  haveI : Fact q.Prime := ⟨hq⟩
  have hqOdd : Odd q := Nat.odd_iff.mpr (hq.eq_two_or_odd.resolve_left hqne2)
  have hqndiv2 : ¬q ∣ 2 := by
    intro hq2
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
    exact hqne2 (Nat.le_antisymm hqle hq.two_le)
  have htwo : (2 : ZMod q) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 2 q).not.mpr hqndiv2
  have horderSub : d ∣ q - 1 := by
    dsimp [d]
    exact ZMod.orderOf_dvd_card_sub_one htwo
  have hsubpos : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos horderSub hsubpos
  have hdne : d ≠ 0 := hdpos.ne'
  have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hn.bot_lt horder) hdpos
  have hkne : k ≠ 0 := hkpos.ne'
  have hdk : d * k = n := by
    dsimp [k]
    simpa [mul_comm] using Nat.div_mul_cancel horder
  have hqBase : q ∣ 2 ^ d - 1 := by
    have hpow : (2 : ZMod q) ^ d = 1 := by
      dsimp [d]
      exact pow_orderOf_eq_one (2 : ZMod q)
    have hmod : 2 ^ d ≡ 1 [MOD q] := by
      exact (ZMod.natCast_eq_natCast_iff (2 ^ d) 1 q).mp (by simpa using hpow)
    exact (Nat.modEq_iff_dvd' (one_le_pow₀ one_le_two)).mp hmod.symm
  have hqNotDvdPow : ¬q ∣ 2 ^ d := by
    intro h
    exact hqndiv2 (hq.dvd_of_dvd_pow h)
  have hkDvdN : k ∣ n := ⟨d, by simpa [mul_comm] using hdk.symm⟩
  have hqNotDvdN : ¬q ∣ n := hq.coprime_iff_not_dvd.mp hcop
  have hqNotDvdK : ¬q ∣ k := fun hqk => hqNotDvdN (hqk.trans hkDvdN)
  have hkVal : padicValNat q k = 0 := padicValNat.eq_zero_of_not_dvd hqNotDvdK
  have hlte := padicValNat.pow_sub_pow (p := q) hqOdd
    (x := 2 ^ d) (y := 1) (one_lt_pow₀ one_lt_two hdne)
    hqBase hqNotDvdPow hkne
  rw [hkVal, add_zero] at hlte
  simpa [d, ← pow_mul, hdk] using hlte

/--
For a prime `q` coprime to `n`, every exponent divisible by `ord_q(2)` has
the same `q`-adic depth as the Fermat exponent `q-1`.
-/
theorem padicValNat_two_pow_sub_one_eq_fermat
    {q n : ℕ} (hq : q.Prime) (hqne2 : q ≠ 2) (hn : n ≠ 0)
    (hcop : Nat.Coprime q n)
    (horder : orderOf (2 : ZMod q) ∣ n) :
    padicValNat q (2 ^ n - 1) = padicValNat q (2 ^ (q - 1) - 1) := by
  have hqndiv2 : ¬q ∣ 2 := by
    intro hq2
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
    exact hqne2 (Nat.le_antisymm hqle hq.two_le)
  have htwo : (2 : ZMod q) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 2 q).not.mpr hqndiv2
  have horderSub : orderOf (2 : ZMod q) ∣ q - 1 := by
    letI : Fact q.Prime := ⟨hq⟩
    exact ZMod.orderOf_dvd_card_sub_one htwo
  have hsubne : q - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hq.one_lt
  have hqNotDvdSub : ¬q ∣ q - 1 := by
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hcopSub : Nat.Coprime q (q - 1) := hq.coprime_iff_not_dvd.mpr hqNotDvdSub
  rw [padicValNat_two_pow_sub_one_eq_at_order hq hqne2 hn hcop horder,
    padicValNat_two_pow_sub_one_eq_at_order hq hqne2 hsubne hcopSub horderSub]

/-- The exact prime-power local criterion for a coprime exponent. -/
theorem primePower_dvd_two_pow_sub_one_iff
    {q e L : ℕ} (hq : q.Prime) (hqne2 : q ≠ 2) (he : 0 < e) (hL : L ≠ 0)
    (hcop : Nat.Coprime q L) :
    q ^ (2 * e) ∣ 2 ^ L - 1 ↔
      orderOf (2 : ZMod q) ∣ L ∧
        2 * e ≤ padicValNat q (2 ^ (q - 1) - 1) := by
  letI : Fact q.Prime := ⟨hq⟩
  have hMne : 2 ^ L - 1 ≠ 0 := two_pow_sub_one_ne_zero hL
  constructor
  · intro hdiv
    have hqDivM : q ∣ 2 ^ L - 1 := by
      exact (dvd_pow_self q (by omega)).trans hdiv
    have hmod : (2 : ZMod q) ^ L = 1 := by
      have hmodNat : 2 ^ L ≡ 1 [MOD q] :=
        ((Nat.modEq_iff_dvd' (one_le_pow₀ one_le_two)).mpr hqDivM).symm
      have hcast := (ZMod.natCast_eq_natCast_iff (2 ^ L) 1 q).mpr hmodNat
      simpa using hcast
    have horder : orderOf (2 : ZMod q) ∣ L := orderOf_dvd_of_pow_eq_one hmod
    refine ⟨horder, ?_⟩
    have hval : 2 * e ≤ padicValNat q (2 ^ L - 1) :=
      (padicValNat_dvd_iff_le hMne).mp hdiv
    rwa [padicValNat_two_pow_sub_one_eq_fermat hq hqne2 hL hcop horder] at hval
  · rintro ⟨horder, hdepth⟩
    apply (padicValNat_dvd_iff_le hMne).mpr
    rwa [padicValNat_two_pow_sub_one_eq_fermat hq hqne2 hL hcop horder]

/--
Exact global coprime square-modulus criterion, with the exponent of each
prime read directly from `N.factorization`.
-/
theorem square_dvd_two_pow_sub_one_iff_localCriterion
    {N L : ℕ} (hN : 1 < N) (hNL : Nat.Coprime N L) :
    N ^ 2 ∣ 2 ^ L - 1 ↔
      ∀ q, q.Prime → q ∣ N →
        q ≠ 2 ∧ orderOf (2 : ZMod q) ∣ L ∧
          2 * N.factorization q ≤ padicValNat q (2 ^ (q - 1) - 1) := by
  have hNne : N ≠ 0 := by omega
  have hLne : L ≠ 0 := by
    intro hL
    subst L
    have : N = 1 := by simpa using hNL
    omega
  have hMne : 2 ^ L - 1 ≠ 0 := two_pow_sub_one_ne_zero hLne
  constructor
  · intro hsq q hq hqN
    have hcert : IsCoprimeSquareCertificate N L := ⟨hN, hNL, hsq⟩
    have hqne2 := prime_divisor_ne_two_of_coprime_squareCertificate hcert hq hqN
    have hqL : Nat.Coprime q L := Nat.Coprime.of_dvd_left hqN hNL
    have hpowN : q ^ N.factorization q ∣ N :=
      (hq.pow_dvd_iff_le_factorization hNne).mpr le_rfl
    have hfacpos : 0 < N.factorization q :=
      hq.factorization_pos_of_dvd hNne hqN
    have hlocal : q ^ (2 * N.factorization q) ∣ 2 ^ L - 1 := by
      have := (pow_dvd_pow_of_dvd hpowN 2).trans hsq
      simpa [← pow_mul, mul_comm] using this
    exact ⟨hqne2,
      (primePower_dvd_two_pow_sub_one_iff hq hqne2 hfacpos hLne hqL).mp hlocal⟩
  · intro hlocal
    apply (Nat.factorization_prime_le_iff_dvd (pow_ne_zero 2 hNne) hMne).mp
    intro q hq
    by_cases hqN : q ∣ N
    · rcases hlocal q hq hqN with ⟨hqne2, horder, hdepth⟩
      have hqL : Nat.Coprime q L := Nat.Coprime.of_dvd_left hqN hNL
      have hfacpos : 0 < N.factorization q :=
        hq.factorization_pos_of_dvd hNne hqN
      have hprimePower : q ^ (2 * N.factorization q) ∣ 2 ^ L - 1 :=
        (primePower_dvd_two_pow_sub_one_iff hq hqne2 hfacpos hLne hqL).mpr
          ⟨horder, hdepth⟩
      have hfacM : 2 * N.factorization q ≤ (2 ^ L - 1).factorization q :=
        (hq.pow_dvd_iff_le_factorization hMne).mp hprimePower
      simpa [Nat.factorization_pow] using hfacM
    · have hfacN : N.factorization q = 0 :=
        Nat.factorization_eq_zero_of_not_dvd hqN
      simp [Nat.factorization_pow, hfacN]

/-- The existing square certificate is exactly the local order/depth package. -/
theorem coprimeSquareCertificate_iff_localCriterion {N L : ℕ} :
    IsCoprimeSquareCertificate N L ↔
      1 < N ∧ Nat.Coprime N L ∧
        ∀ q, q.Prime → q ∣ N →
          q ≠ 2 ∧ orderOf (2 : ZMod q) ∣ L ∧
            2 * N.factorization q ≤ padicValNat q (2 ^ (q - 1) - 1) := by
  constructor
  · rintro ⟨hN, hNL, hsq⟩
    exact ⟨hN, hNL,
      (square_dvd_two_pow_sub_one_iff_localCriterion hN hNL).mp hsq⟩
  · rintro ⟨hN, hNL, hlocal⟩
    exact ⟨hN, hNL,
      (square_dvd_two_pow_sub_one_iff_localCriterion hN hNL).mpr hlocal⟩

end StepsUnboundedResults.R002
