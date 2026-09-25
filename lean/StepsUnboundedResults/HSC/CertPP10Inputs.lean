/-
HSC/CertPP10Inputs.lean

Discharging the five external inputs of the `S = 10` anchor of `Cert-PP(A₅)`.
This is the concrete A₅ layer for the abstract kernel reduction in `CertPP10.lean`.
-/
import StepsUnboundedResults.HSC.CertPP10
import StepsUnboundedResults.HSC.CertPP12Inputs

open scoped Classical
open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace HSC
namespace CertPP10Inputs

abbrev lowerSizes : Finset ℕ := CertPP10.lowerSizes
abbrev allSizes : Finset ℕ := CertPP10.allSizes
abbrev traceCap : ℕ → ℕ := CertPP10.traceCap
abbrev P : Type := Equiv.Perm (Fin 5)
abbrev A5 : Subgroup P := alternatingGroup (Fin 5)
theorem card_A5 : Nat.card A5 = 60 := CertPP12Inputs.card_A5
noncomputable abbrev A5fin : Finset P := CertPP12Inputs.A5fin
theorem mem_A5fin {x : P} : x ∈ A5fin ↔ x ∈ A5 := CertPP12Inputs.mem_A5fin
theorem card_A5fin : A5fin.card = 60 := CertPP12Inputs.card_A5fin
theorem pow_four_A5 : ∀ x ∈ A5fin, x * x * x * x = 1 → x * x = 1 := CertPP12Inputs.pow_four_A5
noncomputable abbrev cos (K : Subgroup P) (x : P) : Finset P := CertPP12Inputs.cos K x
noncomputable abbrev Kfin (K : Subgroup P) : Finset P := CertPP12Inputs.Kfin K
theorem mem_cos {K : Subgroup P} {x y : P} : y ∈ cos K x ↔ x⁻¹ * y ∈ K := CertPP12Inputs.mem_cos
theorem mem_Kfin {K : Subgroup P} {x : P} : x ∈ Kfin K ↔ x ∈ K := CertPP12Inputs.mem_Kfin
theorem cos_eq {K : Subgroup P} {x z : P} (h : x⁻¹ * z ∈ K) : cos K x = cos K z := CertPP12Inputs.cos_eq h
theorem cos_one (K : Subgroup P) : cos K 1 = Kfin K := CertPP12Inputs.cos_one K
theorem card_Kfin (K : Subgroup P) : (Kfin K).card = Nat.card K := CertPP12Inputs.card_Kfin K
theorem card_cos (K : Subgroup P) (x : P) : (cos K x).card = Nat.card K := CertPP12Inputs.card_cos K x
theorem cos_sub (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5) : ∀ y ∈ cos K x, y ∈ A5 :=
  CertPP12Inputs.cos_sub K x hK hx

theorem cos_inter (K L : Subgroup P) (x y : P) :
    ((cos K x) ∩ (cos L y)).card = 0 ∨
      ((cos K x) ∩ (cos L y)).card = Nat.card (K ⊓ L : Subgroup P) :=
  CertPP12Inputs.cos_inter K L x y

theorem cos_eq_of_mem {K : Subgroup P} {x z : P} (hz : z ∈ cos K x) : cos K x = cos K z :=
  cos_eq (mem_cos.mp hz)

def mk (f g : Fin 5 → Fin 5) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) : P := ⟨f, g, h1, h2⟩
def r0 : P := mk ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) (by decide)
def r1 : P := mk ![1, 2, 3, 4, 0] ![4, 0, 1, 2, 3] (by decide) (by decide)
def r2 : P := mk ![2, 3, 4, 0, 1] ![3, 4, 0, 1, 2] (by decide) (by decide)
def r3 : P := mk ![3, 4, 0, 1, 2] ![2, 3, 4, 0, 1] (by decide) (by decide)
def r4 : P := mk ![4, 0, 1, 2, 3] ![1, 2, 3, 4, 0] (by decide) (by decide)
def s0 : P := mk ![0, 4, 3, 2, 1] ![0, 4, 3, 2, 1] (by decide) (by decide)
def s1 : P := mk ![4, 3, 2, 1, 0] ![4, 3, 2, 1, 0] (by decide) (by decide)
def s2 : P := mk ![3, 2, 1, 0, 4] ![3, 2, 1, 0, 4] (by decide) (by decide)
def s3 : P := mk ![2, 1, 0, 4, 3] ![2, 1, 0, 4, 3] (by decide) (by decide)
def s4 : P := mk ![1, 0, 4, 3, 2] ![1, 0, 4, 3, 2] (by decide) (by decide)

def Hset : Finset P := {r0, r1, r2, r3, r4, s0, s1, s2, s3, s4}
def Pset : Finset P := {r0, r1, r2, r3, r4}

theorem Hset_card : Hset.card = 10 := by decide
theorem Pset_card : Pset.card = 5 := by decide
theorem Pset_sub : Pset ⊆ Hset := by decide
theorem Pset_one : (1 : P) ∈ Pset := by decide
theorem Hset_one : (1 : P) ∈ Hset := by decide
theorem Hset_mul : ∀ a ∈ Hset, ∀ b ∈ Hset, a * b ∈ Hset := by decide
theorem Hset_inv : ∀ a ∈ Hset, a⁻¹ ∈ Hset := by decide
theorem Pset_mul : ∀ a ∈ Pset, ∀ b ∈ Pset, a * b ∈ Pset := by decide
theorem Pset_inv : ∀ a ∈ Pset, a⁻¹ ∈ Pset := by decide

theorem Hset_even : ∀ a ∈ Hset, a ∈ A5 := by
  intro a ha
  rw [Equiv.Perm.mem_alternatingGroup]
  simp only [Hset, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem Hset_sub : ∀ y ∈ Hset, y ∈ A5 := Hset_even
theorem Pset_A5 : ∀ y ∈ Pset, y ∈ A5 := fun y hy => Hset_even y (Pset_sub hy)

def H : Subgroup P where
  carrier := {x : P | x ∈ Hset}
  mul_mem' := by intro a b ha hb; exact Hset_mul a (by simpa using ha) b (by simpa using hb)
  one_mem' := Hset_one
  inv_mem' := by intro a ha; exact Hset_inv a (by simpa using ha)

def Psub : Subgroup P where
  carrier := {x : P | x ∈ Pset}
  mul_mem' := by intro a b ha hb; exact Pset_mul a (by simpa using ha) b (by simpa using hb)
  one_mem' := Pset_one
  inv_mem' := by intro a ha; exact Pset_inv a (by simpa using ha)

theorem H_coe : (H : Set P) = ↑Hset := rfl
theorem Psub_coe : (Psub : Set P) = ↑Pset := rfl

theorem mem_H_of_mem_Hset {x : P} (h : x ∈ Hset) : x ∈ H := by
  have h' : x ∈ (H : Set P) := by rwa [H_coe]
  exact h'

theorem mem_Hset_of_mem_H {x : P} (h : x ∈ H) : x ∈ Hset := by
  have h' : x ∈ (H : Set P) := h
  rwa [H_coe] at h'

theorem mem_Psub_of_mem_Pset {x : P} (h : x ∈ Pset) : x ∈ Psub := by
  have h' : x ∈ (Psub : Set P) := by rwa [Psub_coe]
  exact h'

theorem mem_Pset_of_mem_Psub {x : P} (h : x ∈ Psub) : x ∈ Pset := by
  have h' : x ∈ (Psub : Set P) := h
  rwa [Psub_coe] at h'

theorem H_card : Nat.card H = 10 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have e : ↥H ≃ ↥Hset :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, mem_H_of_mem_Hset x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Hset_card]

theorem Psub_card : Nat.card Psub = 5 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have e : ↥Psub ≃ ↥Pset :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, mem_Psub_of_mem_Pset x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Pset_card]

theorem H_le_A5 : H ≤ A5 := fun _ ha => Hset_even _ ha
theorem Psub_le_H : Psub ≤ H := fun _ ha => Pset_sub ha

theorem Kfin_H_eq_Hset : Kfin H = Hset := by
  ext y
  rw [mem_Kfin]
  exact ⟨mem_Hset_of_mem_H, mem_H_of_mem_Hset⟩

theorem Kfin_P_eq_Pset : Kfin Psub = Pset := by
  ext y
  rw [mem_Kfin]
  exact ⟨mem_Pset_of_mem_Psub, mem_Psub_of_mem_Pset⟩

theorem cos_H_one : cos H 1 = Hset := by rw [cos_one, Kfin_H_eq_Hset]

theorem cos_subset_Hset {K : Subgroup P} (hKH : K ≤ H) {h w : P} (hh : h ∈ Hset)
    (hw : w ∈ cos K h) : w ∈ Hset := by
  have h1 : h⁻¹ * w ∈ K := mem_cos.mp hw
  have h2 : h⁻¹ * w ∈ Hset := mem_Hset_of_mem_H (hKH h1)
  have h3 : w = h * (h⁻¹ * w) := by group
  rw [h3]
  exact Hset_mul h hh (h⁻¹ * w) h2

theorem cos_inf (K L : Subgroup P) (z : P) : cos K z ∩ cos L z = cos (K ⊓ L) z := by
  ext w
  simp only [Finset.mem_inter, mem_cos, Subgroup.mem_inf]

theorem cos_mono {K L : Subgroup P} (hKL : K ≤ L) (z : P) : cos K z ⊆ cos L z := by
  intro w hw
  rw [mem_cos] at hw ⊢
  exact hKL hw

theorem card_inf_P_eq_one (C : Subgroup P) (hC : Nat.card C = 2) :
    Nat.card ↥(C ⊓ Psub : Subgroup P) = 1 := by
  have h1 : Nat.card ↥(C ⊓ Psub : Subgroup P) ∣ Nat.card C :=
    Subgroup.card_dvd_of_le (inf_le_left : (C ⊓ Psub : Subgroup P) ≤ C)
  have h2 : Nat.card ↥(C ⊓ Psub : Subgroup P) ∣ Nat.card Psub :=
    Subgroup.card_dvd_of_le (inf_le_right : (C ⊓ Psub : Subgroup P) ≤ Psub)
  rw [hC] at h1
  rw [Psub_card] at h2
  have hd : Nat.card ↥(C ⊓ Psub : Subgroup P) ∣ Nat.gcd 2 5 := Nat.dvd_gcd h1 h2
  rwa [show Nat.gcd 2 5 = 1 from by norm_num, Nat.dvd_one] at hd

noncomputable abbrev a5Equiv : A5 ≃ Fin 60 := CertPP12Inputs.a5Equiv
noncomputable abbrev p5 (p : Fin 60) : P := CertPP12Inputs.p5 p
theorem p5_mem (p : Fin 60) : p5 p ∈ A5 := CertPP12Inputs.p5_mem p
noncomputable abbrev pointOf (C : Finset P) : Finset (Fin 60) := CertPP12Inputs.pointOf C

theorem mem_pointOf_iff {C : Finset P} (hC : ∀ y ∈ C, y ∈ A5) {p : Fin 60} :
    p ∈ pointOf C ↔ p5 p ∈ C := CertPP12Inputs.mem_pointOf_iff hC

theorem pointOf_card {C : Finset P} (hC : ∀ y ∈ C, y ∈ A5) : (pointOf C).card = C.card :=
  CertPP12Inputs.pointOf_card hC

theorem pointOf_inter {A B : Finset P} (hA : ∀ y ∈ A, y ∈ A5) (hB : ∀ y ∈ B, y ∈ A5) :
    pointOf (A ∩ B) = pointOf A ∩ pointOf B := CertPP12Inputs.pointOf_inter hA hB

theorem pointOf_sdiff {A B : Finset P} (hA : ∀ y ∈ A, y ∈ A5) (hB : ∀ y ∈ B, y ∈ A5) :
    pointOf (A \ B) = pointOf A \ pointOf B := CertPP12Inputs.pointOf_sdiff hA hB

theorem disjoint_of_disjoint_pointOf {A B : Finset P} (h : Disjoint (pointOf A) (pointOf B)) : Disjoint A B :=
  CertPP12Inputs.disjoint_of_disjoint_pointOf h

theorem pointOf_mono {A B : Finset P} (h : A ⊆ B) : pointOf A ⊆ pointOf B := by
  intro p hp
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_image.mpr ⟨y, h hy, rfl⟩

noncomputable def trace (K : Subgroup P) (x : P) : Finset P := cos K x ∩ Hset

theorem trace_card_zero_or (K : Subgroup P) (x : P) :
    (trace K x).card = 0 ∨ (trace K x).card = Nat.card ↥(K ⊓ H : Subgroup P) := by
  simpa [trace, cos_H_one] using cos_inter K H x 1

theorem trace_eq_cos_of_mem {K : Subgroup P} {x z : P} (hz : z ∈ trace K x) :
    trace K x = cos (K ⊓ H) z := by
  have h1 : z ∈ cos K x := (Finset.mem_inter.mp hz).1
  have h2 : z ∈ cos H 1 := by rw [cos_H_one]; exact (Finset.mem_inter.mp hz).2
  have hmain : cos K x ∩ cos H 1 = cos (K ⊓ H) z := by
    rw [cos_eq_of_mem h1, cos_eq_of_mem h2, cos_inf]
  rw [cos_H_one] at hmain
  simpa [trace] using hmain

theorem trace_sub (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5) :
    ∀ y ∈ trace K x, y ∈ A5 := by
  intro y hy
  exact cos_sub K x hK hx y (Finset.mem_inter.mp hy).1

theorem trace_subset_Hset (K : Subgroup P) (x : P) : trace K x ⊆ Hset := Finset.inter_subset_right

theorem traceCap_eq_gcd : ∀ m ∈ allSizes, traceCap m = Nat.gcd m 10 := by decide

theorem trace_cap_coset (K : Subgroup P) (x : P) (hK : Nat.card K ∈ allSizes) :
    (trace K x).card ≤ traceCap (Nat.card K) := by
  rcases trace_card_zero_or K x with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [h, traceCap_eq_gcd (Nat.card K) hK]
    have h1 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card K :=
      Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ H : Subgroup P) ≤ K)
    have h2 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card H :=
      Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ H : Subgroup P) ≤ H)
    rw [H_card] at h2
    have hd : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.gcd (Nat.card K) 10 := Nat.dvd_gcd h1 h2
    have hpos : 0 < Nat.gcd (Nat.card K) 10 := by positivity
    exact Nat.le_of_dvd hpos hd

theorem P_mul_compl : ∀ z ∈ Hset, ∀ s ∈ Hset, s ∉ Pset → (z ∈ Pset ↔ z * s ∉ Pset) := by decide

theorem mem_pair {a b y : P} : y ∈ ({a, b} : Finset P) ↔ y = a ∨ y = b := by simp [Finset.mem_insert, Finset.mem_singleton]

theorem exists_pair_of_card_two (C : Subgroup P) (hC : Nat.card C = 2) :
    ∃ s : P, s ≠ 1 ∧ ∀ y : P, y ∈ C ↔ y = 1 ∨ y = s := by
  obtain ⟨p, q, hpq, hpqeq⟩ := Finset.card_eq_two.mp (by rw [card_Kfin]; exact hC : (Kfin C).card = 2)
  have h1mem : (1 : P) ∈ Kfin C := mem_Kfin.mpr C.one_mem
  have h1pq : (1 : P) = p ∨ (1 : P) = q := by
    have h := h1mem
    rw [hpqeq] at h
    simpa [Finset.mem_insert, Finset.mem_singleton] using h
  rcases h1pq with h | h
  · refine ⟨q, fun hq => hpq (by rw [← h, hq]), fun y => ?_⟩
    rw [← mem_Kfin, hpqeq, ← h, mem_pair]
  · refine ⟨p, fun hp => hpq (by rw [hp, h]), fun y => ?_⟩
    rw [← mem_Kfin, hpqeq, Finset.pair_comm, ← h, mem_pair]

theorem trace_two_P_coset (K : Subgroup P) (x : P) (h2 : (trace K x).card = 2) :
    ((trace K x) ∩ Pset).card = 1 := by
  have hC : Nat.card ↥(K ⊓ H : Subgroup P) = 2 := by
    rcases trace_card_zero_or K x with h | h
    · rw [h] at h2; omega
    · exact h.symm.trans h2
  obtain ⟨z, hz⟩ : (trace K x).Nonempty := Finset.card_pos.mp (by omega)
  have htrace : trace K x = cos (K ⊓ H) z := trace_eq_cos_of_mem hz
  have hzH : z ∈ Hset := (Finset.mem_inter.mp hz).2
  obtain ⟨s, hs1, hpair⟩ := exists_pair_of_card_two (K ⊓ H) hC
  have hs_mem : s ∈ (K ⊓ H : Subgroup P) := (hpair s).mpr (Or.inr rfl)
  have hsH : s ∈ Hset := mem_Hset_of_mem_H (Subgroup.mem_inf.mp hs_mem).2
  have hsP : s ∉ Pset := by
    intro hs
    have h1 : Nat.card ↥((K ⊓ H) ⊓ Psub : Subgroup P) = 1 := card_inf_P_eq_one (K ⊓ H) hC
    have hmem : s ∈ ((K ⊓ H) ⊓ Psub : Subgroup P) := ⟨hs_mem, mem_Psub_of_mem_Pset hs⟩
    have hbot : ((K ⊓ H) ⊓ Psub : Subgroup P) = ⊥ := Subgroup.card_eq_one.mp h1
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hs1 hmem
  have hcos : cos (K ⊓ H) z = {z, z * s} := by
    ext w
    rw [mem_cos]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rw [hpair (z⁻¹ * w)]
    constructor
    · rintro (h | h)
      · left; have := congrArg (fun t => z * t) h; simpa using this
      · right; have := congrArg (fun t => z * t) h; simpa using this
    · rintro (h | h)
      · left; rw [h]; group
      · right; rw [h]; group
  have hzP : z ∈ Pset ↔ z * s ∉ Pset := P_mul_compl z hzH s hsH hsP
  rw [htrace, hcos]
  by_cases hz : z ∈ Pset
  · have hzs : z * s ∉ Pset := hzP.mp hz
    have hset : ({z, z * s} : Finset P) ∩ Pset = {z} := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy | hy, hyP⟩
        · exact hy
        · exact absurd (hy ▸ hyP) hzs
      · rintro rfl; exact ⟨Or.inl rfl, hz⟩
    rw [hset, Finset.card_singleton]
  · have hzs : z * s ∈ Pset := by by_contra hc; exact hz (hzP.mpr hc)
    have hset : ({z, z * s} : Finset P) ∩ Pset = {z * s} := by
      ext y
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hy | hy, hyP⟩
        · exact absurd (hy ▸ hyP) hz
        · exact hy
      · rintro rfl; exact ⟨Or.inr rfl, hzs⟩
    rw [hset, Finset.card_singleton]

theorem pow_five_mem_P : ∀ x ∈ Hset, x * x * x * x * x = 1 → x ∈ Pset := by decide

theorem trace_five_coset (K : Subgroup P) (x : P) (h5 : Nat.card K = 5)
    (hge : 2 ≤ (trace K x).card) : trace K x = Pset ∨ trace K x = Hset \ Pset := by
  have hdiv5 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ 5 := by
    have h1 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card K :=
      Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ H : Subgroup P) ≤ K)
    rw [h5] at h1
    exact h1
  have hC : Nat.card ↥(K ⊓ H : Subgroup P) = 5 := by
    rcases trace_card_zero_or K x with h | h
    · rw [h] at hge; omega
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdiv5 with h1 | h5'
      · omega
      · exact h5'
  have hKH : K ≤ H := by
    have heq : K ⊓ H = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hC, h5])
    intro k hk
    exact (Subgroup.mem_inf.mp (by rw [heq]; exact hk)).2
  have hKP : K = Psub := by
    have hsub : ∀ y ∈ K, y ∈ Pset := by
      intro y hy
      have h5y : y * y * y * y * y = 1 := by
        have h0 : (⟨y, hy⟩ : ↥K) ^ 5 = 1 := by
          have h := pow_card_eq_one (G := ↥K) (x := ⟨y, hy⟩)
          rwa [show Fintype.card ↥K = 5 from by rw [← Nat.card_eq_fintype_card]; exact h5] at h
        have h5' : (⟨y, hy⟩ : ↥K) * ⟨y, hy⟩ * ⟨y, hy⟩ * ⟨y, hy⟩ * ⟨y, hy⟩ = 1 := by
          rw [← h0]; simp [pow_succ]
        simpa using congrArg (fun z : ↥K => (z : P)) h5'
      exact pow_five_mem_P y (mem_Hset_of_mem_H (hKH hy)) h5y
    have hfin : Kfin K = Pset := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy; exact hsub y (mem_Kfin.mp hy)
      · rw [card_Kfin, h5, Pset_card]
    refine SetLike.ext fun y => ?_
    rw [← mem_Kfin, hfin]
    exact ⟨mem_Psub_of_mem_Pset, mem_Pset_of_mem_Psub⟩
  have htrace : trace K x = cos Psub x ∩ Hset := by rw [trace, hKP]
  obtain ⟨z, hz⟩ : (trace K x).Nonempty := Finset.card_pos.mp (by omega)
  have hzH : z ∈ Hset := (Finset.mem_inter.mp hz).2
  have hzcos : z ∈ cos Psub x := by
    have h1 : z ∈ cos K x := (Finset.mem_inter.mp hz).1
    rwa [hKP] at h1
  have htracez : trace K x = cos Psub z ∩ Hset := by rw [htrace, cos_eq_of_mem hzcos]
  by_cases hzP : z ∈ Pset
  · left
    have hcosz : cos Psub z = Pset := by
      have h : z⁻¹ * 1 ∈ Psub := by simpa using Psub.inv_mem (mem_Psub_of_mem_Pset hzP)
      rw [cos_eq h, cos_one, Kfin_P_eq_Pset]
    rw [htracez, hcosz, Finset.inter_eq_left.mpr Pset_sub]
  · right
    have hsub1 : cos Psub z ⊆ Hset := fun w hw => cos_subset_Hset (K := Psub) (h := z) Psub_le_H hzH hw
    have hdisj : cos Psub z ∩ Pset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
      have hzw : z⁻¹ * w ∈ Psub := mem_cos.mp hw1
      have hwP : w ∈ Psub := mem_Psub_of_mem_Pset hw2
      have hzP' : z ∈ Psub := by
        have he : z = w * (z⁻¹ * w)⁻¹ := by group
        rw [he]
        exact Psub.mul_mem hwP (Psub.inv_mem hzw)
      exact hzP (mem_Pset_of_mem_Psub hzP')
    have hcardz : (cos Psub z ∩ Hset).card = 5 := by rw [Finset.inter_eq_left.mpr hsub1, card_cos, Psub_card]
    have hcard2 : (Hset \ Pset).card = 5 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr Pset_sub, Hset_card, Pset_card]
    have hsub2 : trace K x ⊆ Hset \ Pset := by
      rw [htracez]
      intro w hw
      rw [Finset.mem_sdiff]
      exact ⟨(Finset.mem_inter.mp hw).2, fun hwP =>
        Finset.notMem_empty w (by rw [← hdisj]; exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hw).1, hwP⟩)⟩
    refine Finset.eq_of_subset_of_card_le hsub2 ?_
    rw [hcard2, htracez, hcardz]

theorem out_six_three_coset (K L : Subgroup P) (x y : P) (hK : Nat.card K = 6)
    (hL : Nat.card L = 3)
    (hout : 2 ≤ (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card) :
    trace L y ⊆ trace K x := by
  have h2 : 1 < (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
  have haK : a ∈ cos K x := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).1
  have haL : a ∈ cos L y := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).1
  have hbK : b ∈ cos K x := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).1).1
  have hbL : b ∈ cos L y := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).2).1
  have hxa : x⁻¹ * a ∈ K := mem_cos.mp haK
  have hxb : x⁻¹ * b ∈ K := mem_cos.mp hbK
  have hya : y⁻¹ * a ∈ L := mem_cos.mp haL
  have hyb : y⁻¹ * b ∈ L := mem_cos.mp hbL
  set u : P := a⁻¹ * b with hu_def
  have huK : u ∈ K := by
    have he : u = (x⁻¹ * a)⁻¹ * (x⁻¹ * b) := by rw [hu_def]; group
    rw [he]; exact K.mul_mem (K.inv_mem hxa) hxb
  have huL : u ∈ L := by
    have he : u = (y⁻¹ * a)⁻¹ * (y⁻¹ * b) := by rw [hu_def]; group
    rw [he]; exact L.mul_mem (L.inv_mem hya) hyb
  have hu1 : u ≠ 1 := by intro h; exact hab (by rw [hu_def] at h; exact inv_mul_eq_one.mp h)
  have huKL : u ∈ (K ⊓ L : Subgroup P) := ⟨huK, huL⟩
  have hcardKL : Nat.card ↥(K ⊓ L : Subgroup P) = 3 := by
    have hd : Nat.card ↥(K ⊓ L : Subgroup P) ∣ 3 := by
      have h1 : Nat.card ↥(K ⊓ L : Subgroup P) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(K ⊓ L : Subgroup P) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_right
      rw [hK] at h1; rw [hL] at h2
      have hg : Nat.card ↥(K ⊓ L : Subgroup P) ∣ Nat.gcd 6 3 := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 6 3 = 3 from by norm_num] at hg
    have hne1 : Nat.card ↥(K ⊓ L : Subgroup P) ≠ 1 := by
      intro h1
      have hbot : (K ⊓ L : Subgroup P) = ⊥ := Subgroup.card_eq_one.mp h1
      rw [hbot, Subgroup.mem_bot] at huKL
      exact hu1 huKL
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  have hLK : L ≤ K := by
    have heq : K ⊓ L = L := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcardKL, hL])
    intro l hl
    exact (Subgroup.mem_inf.mp (by rw [heq]; exact hl)).1
  have hsub : cos L y ⊆ cos K x := by
    rw [cos_eq_of_mem hbL, cos_eq_of_mem hbK]
    exact cos_mono hLK b
  intro p hp
  exact Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩

noncomputable def Inv : Finset P := A5fin.filter (fun x => x * x = 1 ∧ x ≠ 1)
noncomputable def commInv (u : P) : Finset P := Inv.filter (fun y => y * u = u * y)
theorem commInv_card : ∀ u ∈ Inv, (commInv u).card = 3 := by decide
theorem commInv_H_card : ∀ u ∈ Inv, (commInv u ∩ Hset).card = 1 := by decide
theorem centralizer_mem : ∀ x ∈ A5fin, ∀ u ∈ Inv, x * u = u * x → x = 1 ∨ x ∈ commInv u := by decide
theorem third_mul : ∀ u ∈ Inv, u ∉ Hset → ∀ t ∈ commInv u, t ∈ Hset →
    ∀ w ∈ commInv u, w ≠ u → w ≠ t → w = u * t := by decide

theorem out_six_four_coset (K L : Subgroup P) (x y : P) (hKA5 : K ≤ A5) (hLA5 : L ≤ A5)
    (hK : Nat.card K = 6) (hL : Nat.card L = 4)
    (htK : (trace K x).Nonempty) (htL : (trace L y).Nonempty) :
    (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcon
  have haK : a ∈ cos K x := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).1
  have haH : a ∉ Hset := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).2
  have haL : a ∈ cos L y := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).1
  have hbK : b ∈ cos K x := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).1).1
  have hbH : b ∉ Hset := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).1).2
  have hbL : b ∈ cos L y := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).2).1
  have hxa : x⁻¹ * a ∈ K := mem_cos.mp haK
  have hxb : x⁻¹ * b ∈ K := mem_cos.mp hbK
  have hya : y⁻¹ * a ∈ L := mem_cos.mp haL
  have hyb : y⁻¹ * b ∈ L := mem_cos.mp hbL
  set u : P := a⁻¹ * b with hu_def
  have huK : u ∈ K := by
    have he : u = (x⁻¹ * a)⁻¹ * (x⁻¹ * b) := by rw [hu_def]; group
    rw [he]; exact K.mul_mem (K.inv_mem hxa) hxb
  have huL : u ∈ L := by
    have he : u = (y⁻¹ * a)⁻¹ * (y⁻¹ * b) := by rw [hu_def]; group
    rw [he]; exact L.mul_mem (L.inv_mem hya) hyb
  have hu1 : u ≠ 1 := by intro h; exact hab (by rw [hu_def] at h; exact inv_mul_eq_one.mp h)
  have huKL : u ∈ (K ⊓ L : Subgroup P) := ⟨huK, huL⟩
  have hcardKL : Nat.card ↥(K ⊓ L : Subgroup P) = 2 := by
    have hd : Nat.card ↥(K ⊓ L : Subgroup P) ∣ 2 := by
      have h1 : Nat.card ↥(K ⊓ L : Subgroup P) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
      have h2 : Nat.card ↥(K ⊓ L : Subgroup P) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_right
      rw [hK] at h1; rw [hL] at h2
      have hg : Nat.card ↥(K ⊓ L : Subgroup P) ∣ Nat.gcd 6 4 := Nat.dvd_gcd h1 h2
      rwa [show Nat.gcd 6 4 = 2 from by norm_num] at hg
    have hne1 : Nat.card ↥(K ⊓ L : Subgroup P) ≠ 1 := by
      intro h1
      have hbot : (K ⊓ L : Subgroup P) = ⊥ := Subgroup.card_eq_one.mp h1
      rw [hbot, Subgroup.mem_bot] at huKL
      exact hu1 huKL
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h1 | h2
    · exact absurd h1 hne1
    · exact h2
  have hu2 : u * u = 1 := by
    have h0 : (⟨u, huKL⟩ : ↥(K ⊓ L : Subgroup P)) ^ 2 = 1 := by
      have h := pow_card_eq_one (G := ↥(K ⊓ L : Subgroup P)) (x := ⟨u, huKL⟩)
      rwa [show Fintype.card ↥(K ⊓ L : Subgroup P) = 2 from by rw [← Nat.card_eq_fintype_card]; exact hcardKL] at h
    simpa [pow_two] using congrArg (fun z : ↥(K ⊓ L : Subgroup P) => (z : P)) h0
  have huInv : u ∈ Inv := by
    rw [Inv, Finset.mem_filter]
    exact ⟨mem_A5fin.mpr (hKA5 huK), hu2, hu1⟩
  have hpair1 : (1 : P) ≠ u := fun h => hu1 h.symm
  have hKfin_KL : Kfin (K ⊓ L : Subgroup P) = {1, u} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact mem_Kfin.mpr (K ⊓ L).one_mem
      · exact mem_Kfin.mpr huKL
    · rw [Finset.card_pair hpair1, card_Kfin, hcardKL]
  obtain ⟨h, hh⟩ := htK
  obtain ⟨g, hg⟩ := htL
  have hhH : h ∈ Hset := (Finset.mem_inter.mp hh).2
  have hgH : g ∈ Hset := (Finset.mem_inter.mp hg).2
  have hhK : h ∈ cos K x := (Finset.mem_inter.mp hh).1
  have hgL : g ∈ cos L y := (Finset.mem_inter.mp hg).1
  set k : P := h⁻¹ * a with hk_def
  set l : P := g⁻¹ * a with hl_def
  set q : P := h⁻¹ * g with hq_def
  have hkK : k ∈ K := by
    have he : k = (x⁻¹ * h)⁻¹ * (x⁻¹ * a) := by rw [hk_def]; group
    rw [he]; exact K.mul_mem (K.inv_mem (mem_cos.mp hhK)) hxa
  have hlL : l ∈ L := by
    have he : l = (y⁻¹ * g)⁻¹ * (y⁻¹ * a) := by rw [hl_def]; group
    rw [he]; exact L.mul_mem (L.inv_mem (mem_cos.mp hgL)) hya
  have hqH : q ∈ Hset := by
    rw [hq_def]
    exact Hset_mul _ (Hset_inv h hhH) g hgH
  have hk_eq : k = q * l := by rw [hk_def, hl_def, hq_def]; group
  have hk_notH : k ∉ Hset := by
    intro hk
    have he : a = h * k := by rw [hk_def]; group
    exact haH (by rw [he]; exact Hset_mul h hhH k hk)
  have hku_notH : k * u ∉ Hset := by
    intro hku
    have he : b = h * (k * u) := by rw [hk_def, hu_def]; group
    exact hbH (by rw [he]; exact Hset_mul h hhH _ hku)
  have hl_notH : l ∉ Hset := by
    intro hl
    have he : a = g * l := by rw [hl_def]; group
    exact haH (by rw [he]; exact Hset_mul g hgH l hl)
  have hL_inv : ∀ p ∈ L, p * p = 1 := by
    intro p hp
    have h0 : (⟨p, hp⟩ : ↥L) ^ 4 = 1 := by
      have h := pow_card_eq_one (G := ↥L) (x := ⟨p, hp⟩)
      rwa [show Fintype.card ↥L = 4 from by rw [← Nat.card_eq_fintype_card]; exact hL] at h
    have h4 : (⟨p, hp⟩ : ↥L) * ⟨p, hp⟩ * ⟨p, hp⟩ * ⟨p, hp⟩ = 1 := by
      rw [← h0]; simp [pow_succ]
    exact pow_four_A5 p (mem_A5fin.mpr (hLA5 hp)) (by simpa using congrArg (fun z : ↥L => (z : P)) h4)
  have hL_comm : ∀ p ∈ L, ∀ r ∈ L, p * r = r * p := by
    intro p hp r hr
    have hp2 : p * p = 1 := hL_inv p hp
    have hr2 : r * r = 1 := hL_inv r hr
    have hpr : (p * r) * (p * r) = 1 := hL_inv (p * r) (L.mul_mem hp hr)
    calc p * r = (p * r)⁻¹ := (inv_eq_of_mul_eq_one_right hpr).symm
      _ = r⁻¹ * p⁻¹ := mul_inv_rev p r
      _ = r * p := by rw [inv_eq_of_mul_eq_one_right hp2, inv_eq_of_mul_eq_one_right hr2]
  have hul_comm : u * l = l * u := hL_comm u huL l hlL
  have hKfin_L : Kfin L = ({1} : Finset P) ∪ commInv u := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      have hwL : w ∈ L := mem_Kfin.mp hw
      by_cases hw1 : w = 1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_singleton.mpr hw1))
      · refine Finset.mem_union.mpr (Or.inr ?_)
        rw [commInv, Finset.mem_filter, Inv, Finset.mem_filter]
        exact ⟨⟨mem_A5fin.mpr (hLA5 hwL), hL_inv w hwL, hw1⟩, hL_comm w hwL u huL⟩
    · have hdisj : Disjoint ({1} : Finset P) (commInv u) := by
        rw [Finset.disjoint_singleton_left]
        intro h1
        rw [commInv, Finset.mem_filter, Inv, Finset.mem_filter] at h1
        exact h1.1.2.2 rfl
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton, commInv_card u huInv, card_Kfin, hL]
  have ht_mem : ∃ t ∈ commInv u, t ∈ Hset := by
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp (commInv_H_card u huInv)
    have h1 : t ∈ commInv u ∩ Hset := by rw [ht]; exact Finset.mem_singleton.mpr rfl
    exact ⟨t, (Finset.mem_inter.mp h1).1, (Finset.mem_inter.mp h1).2⟩
  by_cases huH : u ∈ Hset
  · have huKH : u ∈ (K ⊓ H : Subgroup P) := ⟨huK, mem_H_of_mem_Hset huH⟩
    have hcardKH : Nat.card ↥(K ⊓ H : Subgroup P) = 2 := by
      have hd : Nat.card ↥(K ⊓ H : Subgroup P) ∣ 2 := by
        have h1 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_left
        have h2 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_right
        rw [hK] at h1; rw [H_card] at h2
        have hg : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.gcd 6 10 := Nat.dvd_gcd h1 h2
        rwa [show Nat.gcd 6 10 = 2 from by norm_num] at hg
      have hne1 : Nat.card ↥(K ⊓ H : Subgroup P) ≠ 1 := by
        intro h1
        have hbot : (K ⊓ H : Subgroup P) = ⊥ := Subgroup.card_eq_one.mp h1
        rw [hbot, Subgroup.mem_bot] at huKH
        exact hu1 huKH
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h1 | h2
      · exact absurd h1 hne1
      · exact h2
    have hKfin_KH : Kfin (K ⊓ H : Subgroup P) = {1, u} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        rw [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_Kfin.mpr (K ⊓ H).one_mem
        · exact mem_Kfin.mpr huKH
      · rw [Finset.card_pair hpair1, card_Kfin, hcardKH]
    have hlul : l * u * l = u := by
      calc l * u * l = u * l * l := by rw [hul_comm]
        _ = u * (l * l) := by rw [mul_assoc]
        _ = u := by rw [hL_inv l hlL, mul_one]
    have hlinv : l⁻¹ = l := inv_eq_of_mul_eq_one_right (hL_inv l hlL)
    have hconj : q * u * q⁻¹ = k * u * k⁻¹ := by
      have hq' : q = k * l⁻¹ := by rw [hk_eq]; group
      rw [hq', show (k * l⁻¹)⁻¹ = l * k⁻¹ from by group]
      rw [show k * l⁻¹ * u * (l * k⁻¹) = k * (l⁻¹ * u * l) * k⁻¹ from by group]
      rw [hlinv, hlul]
    have hquq_mem : q * u * q⁻¹ ∈ (K ⊓ H : Subgroup P) := by
      refine ⟨?_, ?_⟩
      · rw [hconj]; exact K.mul_mem (K.mul_mem hkK huK) (K.inv_mem hkK)
      · exact H.mul_mem (H.mul_mem (mem_H_of_mem_Hset hqH) (mem_H_of_mem_Hset huH))
          (H.inv_mem (mem_H_of_mem_Hset hqH))
    have hquq_cases : q * u * q⁻¹ = 1 ∨ q * u * q⁻¹ = u := by
      have hmem : q * u * q⁻¹ ∈ ({1, u} : Finset P) := by rw [← hKfin_KH]; exact mem_Kfin.mpr hquq_mem
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hcomm : k * u = u * k := by
      rcases hquq_cases with h1 | h1
      · exfalso
        have h2 := congrArg (fun z => q⁻¹ * z * q) h1
        have h3 : u = 1 := by simpa [mul_assoc] using h2
        exact hu1 h3
      · have he : k * u * k⁻¹ = u := by rw [← hconj]; exact h1
        have h2 := congrArg (fun z => z * k) he
        simpa [mul_assoc] using h2
    have hkL : k ∈ L := by
      rcases centralizer_mem k (mem_A5fin.mpr (hKA5 hkK)) u huInv hcomm with h1 | h1
      · rw [← mem_Kfin, hKfin_L, Finset.mem_union]; exact Or.inl (by rw [h1]; simp)
      · rw [← mem_Kfin, hKfin_L, Finset.mem_union]; exact Or.inr h1
    have hk_cases : k = 1 ∨ k = u := by
      have hmem : k ∈ ({1, u} : Finset P) := by rw [← hKfin_KL]; exact mem_Kfin.mpr ⟨hkK, hkL⟩
      simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hk_cases with h1 | h1
    · exact hk_notH (by rw [h1]; exact Hset_one)
    · exact hk_notH (by rw [h1]; exact huH)
  · obtain ⟨t, ht_comm, ht_H⟩ := ht_mem
    have ht_mul : t * u = u * t := by
      have h := ht_comm
      rw [commInv, Finset.mem_filter] at h
      exact h.2
    have hl_cases : l = u ∨ l = u * t := by
      have hl_union : l ∈ ({1} : Finset P) ∪ commInv u := by rw [← hKfin_L]; exact mem_Kfin.mpr hlL
      rcases Finset.mem_union.mp hl_union with h1 | h1
      · rw [Finset.mem_singleton] at h1
        exact absurd (by rw [h1]; exact Hset_one) hl_notH
      · by_cases hlu : l = u
        · exact Or.inl hlu
        · exact Or.inr (third_mul u huInv huH t ht_comm ht_H l h1 hlu
            (fun h => hl_notH (by rw [h]; exact ht_H)))
    have hut : (u * t) * u = t := by rw [mul_assoc, ht_mul, ← mul_assoc, hu2, one_mul]
    rcases hl_cases with h1 | h1
    · have hku : k * u = q := by rw [hk_eq, h1, mul_assoc, hu2, mul_one]
      exact hku_notH (by rw [hku]; exact hqH)
    · have hku : k * u = q * t := by rw [hk_eq, h1, mul_assoc, hut]
      exact hku_notH (by rw [hku]; exact Hset_mul q hqH t ht_H)

structure CosetSystem (ι : Type*) [Fintype ι] [DecidableEq ι] where
  anchor : ι
  K : ι → Subgroup P
  x : ι → P
  sz : ι → ℕ
  sz_eq : ∀ i, sz i = Nat.card (K i)
  sz_mem : ∀ i, sz i ∈ allSizes
  sz_injective : Function.Injective sz
  K_le : ∀ i, K i ≤ A5
  x_mem : ∀ i, x i ∈ A5
  anchor_K : K anchor = H
  anchor_x : x anchor = 1
  cover : ∀ p ∈ A5, (∃ i, p ∈ cos (K i) (x i)) →
    ∃ i j, i ≠ j ∧ p ∈ cos (K i) (x i) ∧ p ∈ cos (K j) (x j)

namespace CosetSystem
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coset_sub (S : CosetSystem ι) (i : ι) : ∀ y ∈ cos (S.K i) (S.x i), y ∈ A5 :=
  cos_sub (S.K i) (S.x i) (S.K_le i) (S.x_mem i)

theorem trace_sub' (S : CosetSystem ι) (i : ι) : ∀ y ∈ trace (S.K i) (S.x i), y ∈ A5 :=
  trace_sub (S.K i) (S.x i) (S.K_le i) (S.x_mem i)

theorem sz_anchor_eq (S : CosetSystem ι) : S.sz S.anchor = 10 := by rw [S.sz_eq, S.anchor_K, H_card]

theorem sz_eq_anchor_of_ten (S : CosetSystem ι) {i : ι} (h : S.sz i = 10) : i = S.anchor :=
  S.sz_injective (h.trans S.sz_anchor_eq.symm)

theorem sz_mem_lower (S : CosetSystem ι) {i : ι} (h : S.sz i ≠ 10) : S.sz i ∈ lowerSizes := by
  have hmem : S.sz i ∈ (insert 10 lowerSizes : Finset ℕ) := S.sz_mem i
  rcases Finset.mem_insert.mp hmem with h' | h'
  · exact absurd h' h
  · exact h'

theorem point_trace (S : CosetSystem ι) (i : ι) :
    pointOf (trace (S.K i) (S.x i)) = pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset := by
  rw [← pointOf_inter (S.coset_sub i) Hset_sub]
  rfl

theorem card_point_trace (S : CosetSystem ι) (i : ι) :
    (pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset).card = (trace (S.K i) (S.x i)).card := by
  rw [← S.point_trace i]
  exact pointOf_card (S.trace_sub' i)

theorem card_point_trace_inter_P (S : CosetSystem ι) (i : ι) :
    ((pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset) ∩ pointOf Pset).card
      = ((trace (S.K i) (S.x i)) ∩ Pset).card := by
  have h1 : pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset = pointOf (trace (S.K i) (S.x i)) :=
    (S.point_trace i).symm
  rw [h1, ← pointOf_inter (S.trace_sub' i) Pset_A5]
  exact pointOf_card fun y hy => S.trace_sub' i y (Finset.mem_inter.mp hy).1

theorem mem_trace_point (S : CosetSystem ι) (i : ι) {p : Fin 60} :
    p ∈ pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset ↔ p5 p ∈ trace (S.K i) (S.x i) := by
  rw [← S.point_trace i, mem_pointOf_iff (S.trace_sub' i)]

theorem out_point_card (S : CosetSystem ι) (i j : ι) :
    (((pointOf (cos (S.K i) (S.x i))) \ pointOf Hset)
        ∩ ((pointOf (cos (S.K j) (S.x j))) \ pointOf Hset)).card
      = (((cos (S.K i) (S.x i)) \ Hset) ∩ ((cos (S.K j) (S.x j)) \ Hset)).card := by
  rw [← pointOf_sdiff (S.coset_sub i) Hset_sub, ← pointOf_sdiff (S.coset_sub j) Hset_sub,
    ← pointOf_inter ?_ ?_]
  · exact pointOf_card fun y hy =>
      cos_sub _ _ (S.K_le i) (S.x_mem i) y (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
  · intro y hy; exact cos_sub _ _ (S.K_le i) (S.x_mem i) y (Finset.mem_sdiff.mp hy).1
  · intro y hy; exact cos_sub _ _ (S.K_le j) (S.x_mem j) y (Finset.mem_sdiff.mp hy).1

noncomputable def toAnchored (S : CosetSystem ι) : CertPP10.Anchored ι where
  anchor := S.anchor
  sz := S.sz
  point := fun i => pointOf (cos (S.K i) (S.x i))
  H := pointOf Hset
  P := pointOf Pset
  sz_anchor := S.sz_anchor_eq
  sz_mem := S.sz_mem
  sz_injective := S.sz_injective
  card_point := by intro i; rw [pointOf_card (S.coset_sub i), card_cos, ← S.sz_eq i]
  point_anchor := by rw [S.anchor_K, S.anchor_x, cos_one, Kfin_H_eq_Hset]
  card_H := by rw [pointOf_card Hset_sub, Hset_card]
  P_sub := by intro p hp; exact pointOf_mono Pset_sub hp
  card_P := by rw [pointOf_card Pset_A5, Pset_card]
  cover := by
    intro p
    by_cases hsome : ∃ i, p5 p ∈ cos (S.K i) (S.x i)
    · left
      obtain ⟨i, hi⟩ := hsome
      obtain ⟨i', j', hij, hi', hj'⟩ := S.cover (p5 p) (p5_mem p) ⟨i, hi⟩
      have hsub : ({i', j'} : Finset ι) ⊆ univ.filter (fun i => p ∈ pointOf (cos (S.K i) (S.x i))) := by
        intro k hk
        rw [Finset.mem_filter]
        rcases Finset.mem_insert.mp hk with hk' | hk'
        · rw [hk']; exact ⟨Finset.mem_univ _, (mem_pointOf_iff (S.coset_sub i')).mpr hi'⟩
        · rw [Finset.mem_singleton] at hk'; rw [hk']; exact ⟨Finset.mem_univ _, (mem_pointOf_iff (S.coset_sub j')).mpr hj'⟩
      have hcard := Finset.card_le_card hsub
      rwa [Finset.card_pair hij] at hcard
    · right
      intro i hpi
      exact hsome ⟨i, (mem_pointOf_iff (S.coset_sub i)).mp hpi⟩
  trace_cap := by
    intro i
    have hsz : Nat.card (S.K i) = S.sz i := (S.sz_eq i).symm
    rw [← hsz]
    rw [show (pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset).card = (trace (S.K i) (S.x i)).card from S.card_point_trace i]
    exact trace_cap_coset (S.K i) (S.x i) (by rw [← S.sz_eq i]; exact S.sz_mem i)
  trace_two_P := by
    intro i h2
    have h2' : (trace (S.K i) (S.x i)).card = 2 := by rw [← S.card_point_trace i]; exact h2
    have h := trace_two_P_coset (S.K i) (S.x i) h2'
    rwa [← S.card_point_trace_inter_P i] at h
  trace_five := by
    intro i h5 hge
    have h5' : Nat.card (S.K i) = 5 := by rw [← S.sz_eq i]; exact h5
    have hge' : 2 ≤ (trace (S.K i) (S.x i)).card := by rw [← S.card_point_trace i]; exact hge
    rcases trace_five_coset (S.K i) (S.x i) h5' hge' with h | h
    · left; rw [← S.point_trace i, h]
    · right; rw [← S.point_trace i, h, pointOf_sdiff Hset_sub Pset_A5]
  out_six_three := by
    intro i j hi6 hi1 hj3 hj1 hout
    have h6' : Nat.card (S.K i) = 6 := by rw [← S.sz_eq i]; exact hi6
    have h3' : Nat.card (S.K j) = 3 := by rw [← S.sz_eq j]; exact hj3
    have hout' : 2 ≤ (((cos (S.K i) (S.x i)) \ Hset) ∩ ((cos (S.K j) (S.x j)) \ Hset)).card := by
      rw [← S.out_point_card i j]; exact hout
    have hsub := out_six_three_coset (S.K i) (S.K j) (S.x i) (S.x j) h6' h3' hout'
    intro p hp
    have hp' : p5 p ∈ trace (S.K j) (S.x j) := (S.mem_trace_point j).mp hp
    exact (S.mem_trace_point i).mpr (hsub hp')
  out_six_four := by
    intro i j hi6 hi1 hj4 hj1
    have h6' : Nat.card (S.K i) = 6 := by rw [← S.sz_eq i]; exact hi6
    have h4' : Nat.card (S.K j) = 4 := by rw [← S.sz_eq j]; exact hj4
    have htK : (trace (S.K i) (S.x i)).Nonempty := by rw [← Finset.card_pos, ← S.card_point_trace i]; omega
    have htL : (trace (S.K j) (S.x j)).Nonempty := by rw [← Finset.card_pos, ← S.card_point_trace j]; omega
    rw [S.out_point_card i j]
    exact out_six_four_coset (S.K i) (S.K j) (S.x i) (S.x j) (S.K_le i) (S.K_le j) h6' h4' htK htL

end CosetSystem

theorem anchor_ten_closed {ι : Type*} [Fintype ι] [DecidableEq ι] (S : CosetSystem ι) : False :=
  CertPP10.Anchored.no_anchored_system S.toAnchored

end CertPP10Inputs
end HSC
