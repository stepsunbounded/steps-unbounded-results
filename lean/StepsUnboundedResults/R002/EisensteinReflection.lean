import StepsUnboundedResults.R002.EisensteinAlternating

namespace StepsUnboundedResults.R002

open scoped BigOperators

/-- Reflection `k ↦ r-k` makes the second half of the alternating reciprocal sum equal to the first half. -/
theorem alternating_full_eq_two_half
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    (∑ d ∈ Finset.range (r - 1),
      (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹) =
        (2 : ZMod r) *
          ∑ d ∈ Finset.range (halfIndex r),
            (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹ := by
  letI : Fact r.Prime := ⟨hr⟩
  let h := halfIndex r
  let f : ℕ → ZMod r := fun d ↦
    (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹
  have hh0 : 1 ≤ h := by
    simp only [h, halfIndex]
    omega
  have hrodd : Odd r := hr.odd_of_ne_two (by omega)
  have hrdecomp : 2 * h + 1 = r := by
    simpa [h] using two_mul_halfIndex_add_one hrodd
  have hlen : r - 1 = h + h := by omega
  have htail :
      (∑ d ∈ Finset.range h, f (h + d)) =
        ∑ d ∈ Finset.range h, f d := by
    calc
      (∑ d ∈ Finset.range h, f (h + d)) =
          ∑ d ∈ Finset.range h, f (h + (h - 1 - d)) := by
        exact (Finset.sum_range_reflect (fun d ↦ f (h + d)) h).symm
      _ = ∑ d ∈ Finset.range h, f d := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdlt : d < h := Finset.mem_range.mp hd
        have hidx : h + (h - 1 - d) = r - 2 - d := by omega
        rw [hidx]
        change
          (-1 : ZMod r) ^ (r - 2 - d) *
              (((r - 2 - d) + 1 : ℕ) : ZMod r)⁻¹ =
            (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹
        have hnat : (r - 2 - d + 1) + (d + 1) = r := by omega
        have hden : ((r - 2 - d + 1 : ℕ) : ZMod r) =
            -((d + 1 : ℕ) : ZMod r) := by
          have hcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hnat
          push_cast at hcast ⊢
          rw [ZMod.natCast_self] at hcast
          linear_combination hcast
        have hoddSum : Odd ((r - 2 - d) + d) := by
          use h - 1
          omega
        have hpowsum :
            (-1 : ZMod r) ^ (r - 2 - d) * (-1 : ZMod r) ^ d = -1 := by
          rw [← pow_add, hoddSum.neg_one_pow]
        have hdpow : (-1 : ZMod r) ^ d ≠ 0 := by simp
        have hsign : (-1 : ZMod r) ^ (r - 2 - d) =
            -((-1 : ZMod r) ^ d) := by
          apply mul_right_cancel₀ hdpow
          calc
            (-1 : ZMod r) ^ (r - 2 - d) * (-1 : ZMod r) ^ d = -1 := hpowsum
            _ = -((-1 : ZMod r) ^ d * (-1 : ZMod r) ^ d) := by
              rw [← pow_add, (Even.add_self d).neg_one_pow]
            _ = (-((-1 : ZMod r) ^ d)) * (-1 : ZMod r) ^ d := by ring
        rw [hden, inv_neg, hsign]
        ring
  change (∑ d ∈ Finset.range (r - 1), f d) =
    (2 : ZMod r) * ∑ d ∈ Finset.range h, f d
  rw [hlen, Finset.sum_range_add]
  change (∑ d ∈ Finset.range h, f d) +
      (∑ d ∈ Finset.range h, f (h + d)) = _
  rw [htail]
  ring

/-- The complete nonzero-residue harmonic sum vanishes modulo a prime. -/
theorem harmonicMod_prime_sub_one_eq_zero
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    harmonicMod r (r - 1) = 0 := by
  letI : Fact r.Prime := ⟨hr⟩
  let f : ℕ → ZMod r := fun d ↦ ((d + 1 : ℕ) : ZMod r)⁻¹
  let S : ZMod r := ∑ d ∈ Finset.range (r - 1), f d
  have hreflect :
      S = ∑ d ∈ Finset.range (r - 1), f (r - 2 - d) := by
    change (∑ d ∈ Finset.range (r - 1), f d) = _
    have href := Finset.sum_range_reflect f (r - 1)
    apply href.symm.trans
    apply Finset.sum_congr rfl
    intro d hd
    congr 2
  have hneg :
      (∑ d ∈ Finset.range (r - 1), f (r - 2 - d)) = -S := by
    calc
      (∑ d ∈ Finset.range (r - 1), f (r - 2 - d)) =
          ∑ d ∈ Finset.range (r - 1), -f d := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdlt : d < r - 1 := Finset.mem_range.mp hd
        have hnat : (r - 2 - d + 1) + (d + 1) = r := by omega
        have hden : ((r - 2 - d + 1 : ℕ) : ZMod r) =
            -((d + 1 : ℕ) : ZMod r) := by
          have hcast := congrArg (fun n : ℕ ↦ (n : ZMod r)) hnat
          push_cast at hcast ⊢
          rw [ZMod.natCast_self] at hcast
          linear_combination hcast
        change (((r - 2 - d) + 1 : ℕ) : ZMod r)⁻¹ =
          -(((d + 1 : ℕ) : ZMod r)⁻¹)
        rw [hden, inv_neg]
      _ = -S := by rw [Finset.sum_neg_distrib]
  have hSneg : S = -S := hreflect.trans hneg
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 2 r).1 hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have htwice : (2 : ZMod r) * S = 0 := by linear_combination hSneg
  have hS : S = 0 := (mul_eq_zero.mp htwice).resolve_left htwo
  simpa [S, f, harmonicMod] using hS

def EisensteinHarmonicCongruences (r : ℕ) : Prop :=
  harmonicMod r (halfIndex r) =
      (-2 : ZMod r) * (fermatQuotientTwo r : ZMod r) ∧
    harmonicMod r (halfIndex r / 2) =
      (-3 : ZMod r) * (fermatQuotientTwo r : ZMod r)

theorem harmonicFermatQuotientTwo_eq_of_eisenstein
    {r : ℕ} (hE : EisensteinHarmonicCongruences r) :
    harmonicFermatQuotientTwo r = (fermatQuotientTwo r : ZMod r) := by
  rcases hE with ⟨hh, hquarter⟩
  simp only [harmonicFermatQuotientTwo]
  rw [hh, hquarter]
  ring

theorem eisensteinHarmonicCongruences
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    EisensteinHarmonicCongruences r := by
  letI : Fact r.Prime := ⟨hr⟩
  let h := halfIndex r
  let q : ZMod r := (fermatQuotientTwo r : ZMod r)
  let A : ZMod r :=
    ∑ d ∈ Finset.range (r - 1),
      (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹
  let Ah : ZMod r :=
    ∑ d ∈ Finset.range h,
      (-1 : ZMod r) ^ d * ((d + 1 : ℕ) : ZMod r)⁻¹
  have hhr : h < r := by
    simp only [h, halfIndex]
    omega
  have htwoq := two_mul_fermatQuotientTwo_eq_alternating hr hr3
  change (2 : ZMod r) * q = A at htwoq
  have hdouble := alternating_full_eq_two_half hr hr3
  change A = (2 : ZMod r) * Ah at hdouble
  have hhalf := alternating_harmonicMod_eq_sub_half hr hr3 hhr
  change Ah = harmonicMod r h - harmonicMod r (h / 2) at hhalf
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 2 r).1 hz
    exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) hdvd
  have hqdiff : q = harmonicMod r h - harmonicMod r (h / 2) := by
    apply mul_left_cancel₀ htwo
    rw [htwoq, hdouble, hhalf]
  have hfullAlt := alternating_harmonicMod_eq_sub_half hr hr3 (n := r - 1) (by omega)
  have hfullZero := harmonicMod_prime_sub_one_eq_zero hr hr3
  have hhalfind : (r - 1) / 2 = h := by rfl
  change A = harmonicMod r (r - 1) - harmonicMod r ((r - 1) / 2) at hfullAlt
  rw [hfullZero, hhalfind, zero_sub] at hfullAlt
  have hh : harmonicMod r h = (-2 : ZMod r) * q := by
    calc
      harmonicMod r h = -A := by linear_combination hfullAlt
      _ = -((2 : ZMod r) * q) := by rw [htwoq]
      _ = (-2 : ZMod r) * q := by ring
  have hquarter : harmonicMod r (h / 2) = (-3 : ZMod r) * q := by
    calc
      harmonicMod r (h / 2) =
          harmonicMod r h - (harmonicMod r h - harmonicMod r (h / 2)) := by ring
      _ = harmonicMod r h - q := by rw [← hqdiff]
      _ = (-2 : ZMod r) * q - q := by rw [hh]
      _ = (-3 : ZMod r) * q := by ring
  exact ⟨hh, hquarter⟩

theorem harmonicFermatQuotientTwo_eq_fermatQuotientTwo
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    harmonicFermatQuotientTwo r = (fermatQuotientTwo r : ZMod r) :=
  harmonicFermatQuotientTwo_eq_of_eisenstein
    (eisensteinHarmonicCongruences hr hr3)

theorem blockAutocorrelationTwo_sub_one_eq_neg_fermatQuotientTwo
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hc : 0 < c) :
    blockAutocorrelationTwo r c - blockAutocorrelationOne r c =
      -(c : ZMod r) * (fermatQuotientTwo r : ZMod r) := by
  rw [blockAutocorrelationTwo_sub_one_eq_neg_harmonicFermatQuotientTwo
      hr hr3 hc,
    harmonicFermatQuotientTwo_eq_fermatQuotientTwo hr hr3]

/-- Chapter-hypothesis version of the universal doubling identity. -/
theorem primeRealModulus_autocorrelation_fermatQuotient
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hP : (2 * c * r - 1).Prime) :
    blockAutocorrelationTwo r c - blockAutocorrelationOne r c =
      -(c : ZMod r) * (fermatQuotientTwo r : ZMod r) := by
  have hc : 0 < c := by
    by_contra hc0
    have : c = 0 := Nat.eq_zero_of_not_pos hc0
    subst c
    norm_num at hP
  exact blockAutocorrelationTwo_sub_one_eq_neg_fermatQuotientTwo hr hr3 hc

theorem fermatQuotientTwo_mod_eq_zero_iff_isWieferich
    {r : ℕ} (hr : r.Prime) (hr3 : 3 < r) :
    (fermatQuotientTwo r : ZMod r) = 0 ↔ IsWieferich r := by
  have hcop : Nat.Coprime 2 r :=
    (Nat.coprime_primes Nat.prime_two hr).2 (by omega)
  have hdiv : r ∣ 2 ^ (r - 1) - 1 :=
    Nat.dvd_of_mod_eq_zero
      (Nat.pow_card_sub_one_sub_one_mod_card hr hcop)
  simp only [fermatQuotientTwo, IsWieferich]
  rw [ZMod.natCast_eq_zero_iff]
  change
    (r ∣ (2 ^ (r - 1) - 1) / r) ↔
      r ^ 2 ∣ 2 ^ (r - 1) - 1
  rw [Nat.dvd_div_iff_mul_dvd hdiv, pow_two]

theorem blockAutocorrelationTwo_eq_one_iff_isWieferich
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r) (hrc : ¬ r ∣ c) :
    blockAutocorrelationTwo r c = blockAutocorrelationOne r c ↔
      IsWieferich r := by
  letI : Fact r.Prime := ⟨hr⟩
  have hc0 : c ≠ 0 := by
    intro hz
    subst c
    exact hrc (dvd_zero r)
  have hc : 0 < c := Nat.pos_of_ne_zero hc0
  have hccast : (c : ZMod r) ≠ 0 := by
    intro hz
    exact hrc ((ZMod.natCast_eq_zero_iff c r).1 hz)
  have hnegc : -(c : ZMod r) ≠ 0 := neg_ne_zero.mpr hccast
  rw [← sub_eq_zero]
  rw [blockAutocorrelationTwo_sub_one_eq_neg_fermatQuotientTwo hr hr3 hc]
  constructor
  · intro hzero
    have hqzero : (fermatQuotientTwo r : ZMod r) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hnegc
    exact (fermatQuotientTwo_mod_eq_zero_iff_isWieferich hr hr3).1 hqzero
  · intro hW
    have hqzero : (fermatQuotientTwo r : ZMod r) = 0 :=
      (fermatQuotientTwo_mod_eq_zero_iff_isWieferich hr hr3).2 hW
    rw [hqzero, mul_zero]

theorem primeRealModulus_autocorrelation_eq_iff_isWieferich
    {r c : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (_hP : (2 * c * r - 1).Prime) (hrc : ¬ r ∣ c) :
    blockAutocorrelationTwo r c = blockAutocorrelationOne r c ↔
      IsWieferich r :=
  blockAutocorrelationTwo_eq_one_iff_isWieferich hr hr3 hrc

end StepsUnboundedResults.R002
