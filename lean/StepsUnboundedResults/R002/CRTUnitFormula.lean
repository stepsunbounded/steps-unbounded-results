import StepsUnboundedResults.R002.DividedCarrier

/-!
# Divided-power and CRT unit formulas

This file refines the zero-set selector to its first-order local digit.  The
central lemma divides the geometric-series factorization integrally before
reducing modulo `q`; no inverse in the natural numbers is used.
-/

namespace StepsUnboundedResults.R002

/-- Exact integral quotient of a power difference by a known divisor. -/
theorem dividedPowerSubOne_eq_digit_mul_geomSum
    {q A k : ℕ} (hq : 0 < q) (hA : 1 ≤ A) (hqA : q ∣ A - 1) :
    (A ^ k - 1) / q =
      ((A - 1) / q) * ∑ i ∈ Finset.range k, A ^ i := by
  have hfactor :
      A ^ k - 1 =
        q * (((A - 1) / q) * ∑ i ∈ Finset.range k, A ^ i) := by
    calc
      A ^ k - 1 =
          (∑ i ∈ Finset.range k, A ^ i) * (A - 1) :=
        (geom_sum_mul_of_one_le hA k).symm
      _ = (∑ i ∈ Finset.range k, A ^ i) *
          (q * ((A - 1) / q)) := by
        rw [Nat.mul_div_cancel' hqA]
      _ = q * (((A - 1) / q) *
          ∑ i ∈ Finset.range k, A ^ i) := by ring
  rw [hfactor, Nat.mul_div_cancel_left _ hq]

/--
Modulo `q`, the divided power difference is `k` times the first lift digit.
-/
theorem dividedPowerSubOne_cast
    {q A k : ℕ} (hq : 0 < q) (hA : 1 ≤ A) (hqA : q ∣ A - 1) :
    ((A ^ k - 1) / q : ZMod q) =
      (k : ZMod q) * ((A - 1) / q : ℕ) := by
  rw [dividedPowerSubOne_eq_digit_mul_geomSum hq hA hqA]
  have hAmod : (A : ZMod q) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff A 1 q).2
      (((Nat.modEq_iff_dvd' hA).2 hqA).symm)
  push_cast
  simp [hAmod, mul_comm]

/-- Multiplicative order of two modulo `q`. -/
noncomputable def twoOrder (q : ℕ) : ℕ :=
  orderOf (2 : ZMod q)

/-- Quotient of the carrier exponent by the local order. -/
noncomputable def carrierOrderMultiplier (q L : ℕ) : ℕ :=
  L / twoOrder q

/-- Quotient of `q-1` by the local order. -/
noncomputable def fermatOrderMultiplier (q : ℕ) : ℕ :=
  (q - 1) / twoOrder q

/-- The cofactor of a carrier at one of its prime divisors. -/
def carrierPrimeCofactor (Y q : ℕ) : ℕ :=
  Y / q

/-- The ordinary base-two Fermat quotient, represented integrally. -/
def fermatQuotientTwo (q : ℕ) : ℕ :=
  (2 ^ (q - 1) - 1) / q

/-- The first lift digit at the exact order of two modulo `q`. -/
noncomputable def orderLiftDigitTwo (q : ℕ) : ℕ :=
  (2 ^ twoOrder q - 1) / q

/--
Cross-multiplied CRT digit formula.  This is equivalent to the usual formula
with inverses once the three displayed multipliers are known to be units.
-/
theorem dividedCarrier_crt_cross_formula
    {Y L q : ℕ} (hY : 1 < Y)
    (hYL : Nat.Coprime Y L) (hYdiv : Y ∣ 2 ^ L - 1)
    (hq : q.Prime) (hqY : q ∣ Y) :
    (carrierPrimeCofactor Y q : ZMod q) *
        (fermatOrderMultiplier q : ZMod q) *
        (dividedCarrier Y L : ZMod q) =
      (carrierOrderMultiplier q L : ZMod q) *
        (fermatQuotientTwo q : ZMod q) := by
  have hL : L ≠ 0 := by
    intro hL0
    subst L
    have : Y = 1 := by simpa using hYL
    omega
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
  have hqndiv2 : ¬ q ∣ 2 := by
    intro hq2
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
    exact hqne2 (Nat.le_antisymm hqle hq.two_le)
  have htwo : (2 : ZMod q) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 2 q).not.mpr hqndiv2
  have hdL : twoOrder q ∣ L :=
    orderOf_two_dvd_of_prime_dvd_mersenne hqM
  have hdq : twoOrder q ∣ q - 1 := by
    exact ZMod.orderOf_dvd_card_sub_one htwo
  have hdpos : 0 < twoOrder q :=
    Nat.pos_of_dvd_of_pos hdq (Nat.sub_pos_of_lt hq.one_lt)
  have hqdigit : q ∣ 2 ^ twoOrder q - 1 := by
    apply (ZMod.natCast_eq_zero_iff (2 ^ twoOrder q - 1) q).1
    rw [Nat.cast_sub (one_le_pow₀ one_le_two)]
    push_cast
    exact sub_eq_zero.mpr (pow_orderOf_eq_one (2 : ZMod q))
  have hglobal := dividedPowerSubOne_cast
    (q := q) (A := 2 ^ twoOrder q) (k := carrierOrderMultiplier q L)
    hq.pos (one_le_pow₀ one_le_two) hqdigit
  have hglobalPow :
      (2 ^ twoOrder q) ^ carrierOrderMultiplier q L = 2 ^ L := by
    rw [← pow_mul, carrierOrderMultiplier, Nat.mul_div_cancel' hdL]
  rw [hglobalPow] at hglobal
  have hfermat := dividedPowerSubOne_cast
    (q := q) (A := 2 ^ twoOrder q) (k := fermatOrderMultiplier q)
    hq.pos (one_le_pow₀ one_le_two) hqdigit
  have hfermatPow :
      (2 ^ twoOrder q) ^ fermatOrderMultiplier q = 2 ^ (q - 1) := by
    rw [← pow_mul, fermatOrderMultiplier, Nat.mul_div_cancel' hdq]
  rw [hfermatPow] at hfermat
  have hcofactor :
      carrierPrimeCofactor Y q * dividedCarrier Y L =
        (2 ^ L - 1) / q := by
    apply Nat.eq_of_mul_eq_mul_left hq.pos
    calc
      q * (carrierPrimeCofactor Y q * dividedCarrier Y L) =
          Y * dividedCarrier Y L := by
        rw [← mul_assoc, carrierPrimeCofactor,
          Nat.mul_div_cancel' hqY]
      _ = 2 ^ L - 1 := Nat.mul_div_cancel' hYdiv
      _ = q * ((2 ^ L - 1) / q) :=
        (Nat.mul_div_cancel' hqM).symm
  have hcofactorCast := congrArg (fun n : ℕ => (n : ZMod q)) hcofactor
  push_cast at hcofactorCast
  change
    (carrierPrimeCofactor Y q : ZMod q) *
        (fermatOrderMultiplier q : ZMod q) *
        (dividedCarrier Y L : ZMod q) =
      (carrierOrderMultiplier q L : ZMod q) *
        (fermatQuotientTwo q : ZMod q)
  calc
    (carrierPrimeCofactor Y q : ZMod q) *
          (fermatOrderMultiplier q : ZMod q) *
          (dividedCarrier Y L : ZMod q) =
        (fermatOrderMultiplier q : ZMod q) *
          ((2 ^ L - 1) / q : ℕ) := by
            rw [← hcofactorCast]
            ring
    _ = (fermatOrderMultiplier q : ZMod q) *
          ((carrierOrderMultiplier q L : ZMod q) *
            (orderLiftDigitTwo q : ZMod q)) := by
            simpa [orderLiftDigitTwo] using congrArg
              (fun z : ZMod q => (fermatOrderMultiplier q : ZMod q) * z)
              hglobal
    _ = (carrierOrderMultiplier q L : ZMod q) *
          ((fermatOrderMultiplier q : ZMod q) *
            (orderLiftDigitTwo q : ZMod q)) := by ring
    _ = (carrierOrderMultiplier q L : ZMod q) *
          (fermatQuotientTwo q : ZMod q) := by
            simpa [orderLiftDigitTwo, fermatQuotientTwo] using congrArg
              (fun z : ZMod q => (carrierOrderMultiplier q L : ZMod q) * z)
              hfermat.symm

/--
The exponent multiplier, Fermat multiplier, and carrier cofactor in the CRT
formula are all units modulo the selected prime.
-/
theorem dividedCarrier_crt_multipliers_isUnit
    {Y L q : ℕ} (hY : 1 < Y) (hYsq : Squarefree Y)
    (hYL : Nat.Coprime Y L) (hYdiv : Y ∣ 2 ^ L - 1)
    (hq : q.Prime) (hqY : q ∣ Y) :
    IsUnit (carrierPrimeCofactor Y q : ZMod q) ∧
      IsUnit (fermatOrderMultiplier q : ZMod q) ∧
      IsUnit (carrierOrderMultiplier q L : ZMod q) := by
  have hL : L ≠ 0 := by
    intro hL0
    subst L
    have : Y = 1 := by simpa using hYL
    omega
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
  have hqndiv2 : ¬ q ∣ 2 := by
    intro hq2
    have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) hq2
    exact hqne2 (Nat.le_antisymm hqle hq.two_le)
  have htwo : (2 : ZMod q) ≠ 0 :=
    (ZMod.natCast_eq_zero_iff 2 q).not.mpr hqndiv2
  have hdL : twoOrder q ∣ L :=
    orderOf_two_dvd_of_prime_dvd_mersenne hqM
  have hdq : twoOrder q ∣ q - 1 :=
    ZMod.orderOf_dvd_card_sub_one htwo
  have hqsubpos : 0 < q - 1 := Nat.sub_pos_of_lt hq.one_lt
  have hdpos : 0 < twoOrder q :=
    Nat.pos_of_dvd_of_pos hdq hqsubpos
  have hkL : carrierOrderMultiplier q L ∣ L := by
    exact Nat.div_dvd_of_dvd hdL
  have hqk : ¬ q ∣ carrierOrderMultiplier q L := by
    intro hqk'
    exact (hq.coprime_iff_not_dvd.1 (hYL.of_dvd_left hqY))
      (hqk'.trans hkL)
  have hgpos : 0 < fermatOrderMultiplier q := by
    exact Nat.div_pos (Nat.le_of_dvd hqsubpos hdq) hdpos
  have hglt : fermatOrderMultiplier q < q := by
    have hgle : fermatOrderMultiplier q ≤ q - 1 :=
      Nat.div_le_self _ _
    omega
  have hqg : ¬ q ∣ fermatOrderMultiplier q :=
    Nat.not_dvd_of_pos_of_lt hgpos hglt
  obtain ⟨R, hYR⟩ := hqY
  have hcop : Nat.Coprime q R := by
    rw [hYR] at hYsq
    exact Nat.coprime_of_squarefree_mul hYsq
  have hcofactor : carrierPrimeCofactor Y q = R := by
    rw [carrierPrimeCofactor, hYR, Nat.mul_div_cancel_left _ hq.pos]
  have hqR : ¬ q ∣ carrierPrimeCofactor Y q := by
    rw [hcofactor]
    exact hq.coprime_iff_not_dvd.1 hcop
  have castUnit (n : ℕ) (hn : ¬ q ∣ n) : IsUnit (n : ZMod q) := by
    have hne : (n : ZMod q) ≠ 0 :=
      (ZMod.natCast_eq_zero_iff n q).not.mpr hn
    exact hne.isUnit
  exact ⟨castUnit _ hqR, castUnit _ hqg, castUnit _ hqk⟩

/-- The inverse form of the exact CRT diagonalization theorem. -/
theorem dividedCarrier_crt_unit_formula
    {Y L q : ℕ} (hY : 1 < Y) (hYsq : Squarefree Y)
    (hYL : Nat.Coprime Y L) (hYdiv : Y ∣ 2 ^ L - 1)
    (hq : q.Prime) (hqY : q ∣ Y) :
    (dividedCarrier Y L : ZMod q) =
      (carrierOrderMultiplier q L : ZMod q) *
        (fermatOrderMultiplier q : ZMod q)⁻¹ *
        (carrierPrimeCofactor Y q : ZMod q)⁻¹ *
        (fermatQuotientTwo q : ZMod q) := by
  letI : Fact q.Prime := ⟨hq⟩
  have hcross := dividedCarrier_crt_cross_formula
    hY hYL hYdiv hq hqY
  obtain ⟨hRunit, hgunit, _⟩ :=
    dividedCarrier_crt_multipliers_isUnit
      hY hYsq hYL hYdiv hq hqY
  have hR : (carrierPrimeCofactor Y q : ZMod q) ≠ 0 :=
    isUnit_iff_ne_zero.1 hRunit
  have hg : (fermatOrderMultiplier q : ZMod q) ≠ 0 :=
    isUnit_iff_ne_zero.1 hgunit
  calc
    (dividedCarrier Y L : ZMod q) =
        (carrierPrimeCofactor Y q : ZMod q)⁻¹ *
          (fermatOrderMultiplier q : ZMod q)⁻¹ *
          ((carrierPrimeCofactor Y q : ZMod q) *
            (fermatOrderMultiplier q : ZMod q) *
            (dividedCarrier Y L : ZMod q)) := by
              symm
              calc
                (carrierPrimeCofactor Y q : ZMod q)⁻¹ *
                      (fermatOrderMultiplier q : ZMod q)⁻¹ *
                      ((carrierPrimeCofactor Y q : ZMod q) *
                        (fermatOrderMultiplier q : ZMod q) *
                        (dividedCarrier Y L : ZMod q)) =
                    ((carrierPrimeCofactor Y q : ZMod q)⁻¹ *
                      (carrierPrimeCofactor Y q : ZMod q)) *
                    ((fermatOrderMultiplier q : ZMod q)⁻¹ *
                      (fermatOrderMultiplier q : ZMod q)) *
                    (dividedCarrier Y L : ZMod q) := by ring
                _ = (dividedCarrier Y L : ZMod q) := by
                  rw [inv_mul_cancel₀ hR, inv_mul_cancel₀ hg]
                  simp
    _ = (carrierPrimeCofactor Y q : ZMod q)⁻¹ *
          (fermatOrderMultiplier q : ZMod q)⁻¹ *
          ((carrierOrderMultiplier q L : ZMod q) *
            (fermatQuotientTwo q : ZMod q)) := by rw [hcross]
    _ = (carrierOrderMultiplier q L : ZMod q) *
          (fermatOrderMultiplier q : ZMod q)⁻¹ *
          (carrierPrimeCofactor Y q : ZMod q)⁻¹ *
          (fermatQuotientTwo q : ZMod q) := by ring

end StepsUnboundedResults.R002
