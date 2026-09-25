import StepsUnboundedResults.HSC.CertPP12
import Mathlib

open scoped Classical
open Finset

set_option maxRecDepth 100000

namespace HSC
namespace CertPP12Inputs

abbrev lowerSizes := CertPP12.lowerSizes
abbrev allSizes := CertPP12.allSizes
abbrev traceCap := CertPP12.traceCap
abbrev pairCap := CertPP12.pairCap
abbrev attainableTraces := CertPP12.attainableTraces

abbrev P : Type := Equiv.Perm (Fin 5)
abbrev A5 : Subgroup P := alternatingGroup (Fin 5)

theorem card_A5 : Nat.card A5 = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

def mk (f g : Fin 5 → Fin 5) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) : P :=
  ⟨f, g, h1, h2⟩

def h0 : P := mk ![0, 1, 2, 3, 4] ![0, 1, 2, 3, 4] (by decide) (by decide)
def h1 : P := mk ![0, 2, 3, 1, 4] ![0, 3, 1, 2, 4] (by decide) (by decide)
def h2 : P := mk ![0, 3, 1, 2, 4] ![0, 2, 3, 1, 4] (by decide) (by decide)
def h3 : P := mk ![1, 0, 3, 2, 4] ![1, 0, 3, 2, 4] (by decide) (by decide)
def h4 : P := mk ![1, 2, 0, 3, 4] ![2, 0, 1, 3, 4] (by decide) (by decide)
def h5 : P := mk ![1, 3, 2, 0, 4] ![3, 0, 2, 1, 4] (by decide) (by decide)
def h6 : P := mk ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4] (by decide) (by decide)
def h7 : P := mk ![2, 1, 3, 0, 4] ![3, 1, 0, 2, 4] (by decide) (by decide)
def h8 : P := mk ![2, 3, 0, 1, 4] ![2, 3, 0, 1, 4] (by decide) (by decide)
def h9 : P := mk ![3, 0, 2, 1, 4] ![1, 3, 2, 0, 4] (by decide) (by decide)
def h10 : P := mk ![3, 1, 0, 2, 4] ![2, 1, 3, 0, 4] (by decide) (by decide)
def h11 : P := mk ![3, 2, 1, 0, 4] ![3, 2, 1, 0, 4] (by decide) (by decide)

def Hset : Finset P := {h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11}

theorem Hset_card : Hset.card = 12 := by decide
theorem Hset_one : (1 : P) ∈ Hset := by decide
theorem Hset_mul : ∀ a ∈ Hset, ∀ b ∈ Hset, a * b ∈ Hset := by decide
theorem Hset_inv : ∀ a ∈ Hset, a⁻¹ ∈ Hset := by decide

theorem Hset_even : ∀ a ∈ Hset, a ∈ A5 := by
  intro a ha
  rw [Equiv.Perm.mem_alternatingGroup]
  simp only [Hset, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

def H : Subgroup P where
  carrier := {x : P | x ∈ Hset}
  mul_mem' := by
    intro a b ha hb
    exact Hset_mul a (by simpa using ha) b (by simpa using hb)
  one_mem' := Hset_one
  inv_mem' := by
    intro a ha
    exact Hset_inv a (by simpa using ha)

theorem H_coe : (H : Set P) = ↑Hset := rfl

theorem H_card : Nat.card H = 12 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have e : ↥H ≃ ↥Hset :=
    { toFun := fun x => ⟨x.1, by simpa [H_coe] using x.2⟩
      invFun := fun x => ⟨x.1, by simpa [H_coe] using x.2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Hset_card]

theorem H_le_A5 : H ≤ A5 := by
  intro a ha
  exact Hset_even a (by rw [← Finset.mem_coe, ← H_coe]; exact ha)

noncomputable def Kfin (K : Subgroup P) : Finset P := by
  classical exact Finset.univ.filter (fun y => y ∈ K)

noncomputable def cos (K : Subgroup P) (x : P) : Finset P := by
  classical exact Finset.univ.filter (fun y => x⁻¹ * y ∈ K)

theorem mem_cos {K : Subgroup P} {x y : P} : y ∈ cos K x ↔ x⁻¹ * y ∈ K := by
  classical
  simp [cos]

theorem cos_eq {K : Subgroup P} {x z : P} (h : x⁻¹ * z ∈ K) : cos K x = cos K z := by
  ext y
  rw [mem_cos, mem_cos]
  constructor
  · intro hy
    have hzy : z⁻¹ * y = (z⁻¹ * x) * (x⁻¹ * y) := by group
    rw [hzy]
    exact K.mul_mem (by simpa using K.inv_mem h) hy
  · intro hy
    have hxy : x⁻¹ * y = (x⁻¹ * z) * (z⁻¹ * y) := by group
    rw [hxy]
    exact K.mul_mem h hy

theorem cos_one (K : Subgroup P) : cos K 1 = Kfin K := by
  classical
  ext y; rw [mem_cos, show (1 : P)⁻¹ * y = y from by simp]; simp [Kfin]

theorem card_Kfin (K : Subgroup P) : (Kfin K).card = Nat.card K := by
  classical
  show (Finset.univ.filter (fun y : P => y ∈ K)).card = Nat.card K
  rw [Nat.card_eq_fintype_card, ← Fintype.card_coe (Finset.univ.filter (fun y : P => y ∈ K))]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun y => by simp))

theorem card_cos (K : Subgroup P) (x : P) : (cos K x).card = Nat.card K := by
  classical
  have himg : cos K x = (Kfin K).image (fun k => x * k) := by
    ext y
    constructor
    · intro hy
      rw [mem_cos] at hy
      exact mem_image.mpr ⟨x⁻¹ * y, by simpa [Kfin] using hy, by group⟩
    · intro hy
      rcases mem_image.mp hy with ⟨k, hk, rfl⟩
      rw [mem_cos]
      simpa [Kfin] using hk
  rw [himg, card_image_of_injective _ (fun a b hab => mul_left_cancel hab), card_Kfin]

theorem cos_inter (K L : Subgroup P) (x y : P) :
    ((cos K x) ∩ (cos L y)).card = 0 ∨
      ((cos K x) ∩ (cos L y)).card = Nat.card (K ⊓ L : Subgroup P) := by
  rcases eq_empty_or_nonempty ((cos K x) ∩ (cos L y)) with h | ⟨z, hz⟩
  · exact Or.inl (by rw [h]; simp)
  · right
    obtain ⟨hzx, hzy⟩ := mem_inter.mp hz
    rw [mem_cos] at hzx hzy
    have h3 : cos K z ∩ cos L z = cos (K ⊓ L) z := by
      ext w
      rw [mem_inter, mem_cos, mem_cos, mem_cos]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
    rw [cos_eq hzx, cos_eq hzy, h3, card_cos (K ⊓ L) z]

theorem mul_card_le_of_inf_eq_bot (K L : Subgroup P) (hK : K ≤ A5) (hL : L ≤ A5)
    (h : K ⊓ L = ⊥) : Nat.card K * Nat.card L ≤ 60 := by
  classical
  have hinj : Function.Injective
      (fun p : ↥K × ↥L => (⟨(p.1 : P) * (p.2 : P), A5.mul_mem (hK p.1.2) (hL p.2.2)⟩ : A5)) := by
    rintro ⟨a1, a2⟩ ⟨b1, b2⟩ hab
    have h1 : (a1 : P) * (a2 : P) = (b1 : P) * (b2 : P) := congrArg Subtype.val hab
    have h1' : (b1 : P) * (b2 : P) = (a1 : P) * (a2 : P) := h1.symm
    have h2 : (a1 : P)⁻¹ * (b1 : P) = (a2 : P) * (b2 : P)⁻¹ := by
      calc (a1 : P)⁻¹ * (b1 : P)
          = (a1 : P)⁻¹ * ((b1 : P) * (b2 : P)) * (b2 : P)⁻¹ := by group
        _ = (a1 : P)⁻¹ * ((a1 : P) * (a2 : P)) * (b2 : P)⁻¹ := by rw [h1']
        _ = (a2 : P) * (b2 : P)⁻¹ := by group
    have h3 : (a1 : P)⁻¹ * (b1 : P) ∈ K ⊓ L :=
      ⟨K.mul_mem (K.inv_mem a1.2) b1.2, by rw [h2]; exact L.mul_mem a2.2 (L.inv_mem b2.2)⟩
    rw [h, Subgroup.mem_bot] at h3
    have h4 : (a1 : P) = (b1 : P) := by
      have hh := congrArg (fun t : P => (a1 : P) * t) h3
      simpa using hh.symm
    have h5 : (a2 : P) = (b2 : P) := by
      rw [h4] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
  have h60 := Fintype.card_le_of_injective _ hinj
  have hKL : Fintype.card (↥K × ↥L) = Nat.card K * Nat.card L := by
    rw [Fintype.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hA : Fintype.card ↥A5 = 60 := by
    rw [← Nat.card_eq_fintype_card]; exact card_A5
  rw [hKL, hA] at h60
  exact h60

theorem inf_H_card_dvd (K : Subgroup P) : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card K :=
  Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ H : Subgroup P) ≤ K)

theorem inf_H_card_dvd_twelve (K : Subgroup P) : Nat.card ↥(K ⊓ H : Subgroup P) ∣ 12 := by
  have h := Subgroup.card_dvd_of_le (inf_le_right : K ⊓ H ≤ H)
  rwa [H_card] at h

theorem inf_H_ne_one (K : Subgroup P) (hK : K ≤ A5) {m : ℕ} (hm : Nat.card K = m) (hm2 : 5 < m) :
    Nat.card ↥(K ⊓ H : Subgroup P) ≠ 1 := by
  intro h1
  have hbot : K ⊓ H = ⊥ := Subgroup.card_eq_one.mp h1
  have hb := mul_card_le_of_inf_eq_bot K H hK H_le_A5 hbot
  rw [H_card, hm] at hb
  omega

theorem inf_H_dvd_gcd (K : Subgroup P) {m : ℕ} (hm : Nat.card K = m) :
    Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.gcd m 12 := by
  have h1 : Nat.card ↥(K ⊓ H : Subgroup P) ∣ Nat.card K := inf_H_card_dvd K
  rw [hm] at h1
  exact Nat.dvd_gcd h1 (inf_H_card_dvd_twelve K)

noncomputable def trace (K : Subgroup P) (x : P) : Finset P := (cos K x) ∩ cos H 1

theorem cos_H_one : cos H 1 = Hset := by
  rw [cos_one]
  ext y
  simp [Kfin, H]

theorem trace_eq (K : Subgroup P) (x : P) : trace K x = (cos K x) ∩ Hset := by
  rw [trace, cos_H_one]

theorem trace_card_zero_or (K : Subgroup P) (x : P) :
    (trace K x).card = 0 ∨ (trace K x).card = Nat.card ↥(K ⊓ H : Subgroup P) :=
  cos_inter K H x 1

theorem trace_one (K : Subgroup P) (x : P) (hK : Nat.card K = 1) :
    (trace K x).card ∈ attainableTraces 1 := by
  rcases trace_card_zero_or K x with h | h
  · rw [h]; decide
  · have hd : Nat.card ↥(K ⊓ H : Subgroup P) ∣ 1 := by simpa using inf_H_dvd_gcd K hK
    rw [h, Nat.dvd_one.mp hd]; decide

theorem trace_two (K : Subgroup P) (x : P) (hK : Nat.card K = 2) :
    (trace K x).card ∈ attainableTraces 2 := by
  rcases trace_card_zero_or K x with h | h
  · rw [h]; decide
  · have hd : Nat.card ↥(K ⊓ H : Subgroup P) ∣ 2 := by simpa using inf_H_dvd_gcd K hK
    have hpos : 0 < Nat.card ↥(K ⊓ H : Subgroup P) := Nat.pos_of_dvd_of_pos hd (by norm_num)
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hd with h1 | h2
    · rw [h, h1]; decide
    · rw [h, h2]; decide

theorem trace_three (K : Subgroup P) (x : P) (hK : Nat.card K = 3) :
    (trace K x).card ∈ attainableTraces 3 := by
  rcases trace_card_zero_or K x with h | h
  · rw [h]; decide
  · have hd : Nat.card ↥(K ⊓ H : Subgroup P) ∣ 3 := by simpa using inf_H_dvd_gcd K hK
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h1 | h3
    · rw [h, h1]; decide
    · rw [h, h3]; decide

theorem trace_four (K : Subgroup P) (x : P) (h : (trace K x).card = 4) :
    (trace K x).card ∈ attainableTraces 4 := by
  rw [h]; decide

theorem pairCap_eq_gcd : ∀ m ∈ lowerSizes, ∀ n ∈ lowerSizes, pairCap m n = Nat.gcd m n := by
  decide

theorem pair_cap_coset (K L : Subgroup P) (x y : P) (hm : Nat.card K ∈ lowerSizes)
    (hn : Nat.card L ∈ lowerSizes) :
    (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤
      min (Nat.card K - ((cos K x) ∩ Hset).card)
        (min (Nat.card L - ((cos L y) ∩ Hset).card) (pairCap (Nat.card K) (Nat.card L))) := by
  have hsub : ((cos K x) \ Hset) ∩ ((cos L y) \ Hset) ⊆ (cos K x) ∩ (cos L y) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := mem_inter.mp hw
    exact mem_inter.mpr ⟨(mem_sdiff.mp hw1).1, (mem_sdiff.mp hw2).1⟩
  have hcap : (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤ Nat.card ↥(K ⊓ L : Subgroup P) := by
    refine (card_le_card hsub).trans ?_
    rcases cos_inter K L x y with h | h
    · rw [h]; exact Nat.zero_le _
    · rw [h]
  have hgcd : Nat.card ↥(K ⊓ L : Subgroup P) ≤ Nat.gcd (Nat.card K) (Nat.card L) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ Nat.card_pos)
      (Nat.dvd_gcd (Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ L : Subgroup P) ≤ K))
        (Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ L : Subgroup P) ≤ L)))
  rw [pairCap_eq_gcd (Nat.card K) hm (Nat.card L) hn]
  have h1 : (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤ ((cos K x) \ Hset).card :=
    card_le_card inter_subset_left
  have h2 : ((cos K x) \ Hset).card = Nat.card K - ((cos K x) ∩ Hset).card := by
    rw [card_sdiff, inter_comm, card_cos]
  have h3 : (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤ ((cos L y) \ Hset).card :=
    card_le_card inter_subset_right
  have h4 : ((cos L y) \ Hset).card = Nat.card L - ((cos L y) ∩ Hset).card := by
    rw [card_sdiff, inter_comm, card_cos]
  omega

noncomputable def A5fin : Finset P := univ.filter (fun x => Equiv.Perm.sign x = 1)

theorem mem_A5fin {x : P} : x ∈ A5fin ↔ x ∈ A5 := by
  rw [A5fin, Finset.mem_filter, Equiv.Perm.mem_alternatingGroup]
  simp

theorem card_A5fin : A5fin.card = 60 := by
  classical
  have h1 : A5fin.card = Fintype.card {x : P // Equiv.Perm.sign x = 1} := by
    rw [A5fin]; exact (Fintype.card_subtype (fun x : P => Equiv.Perm.sign x = 1)).symm
  rw [h1]
  have h2 : Fintype.card {x : P // Equiv.Perm.sign x = 1} = Fintype.card ↥A5 :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun x : P => Equiv.Perm.mem_alternatingGroup)).symm
  rw [h2, ← Nat.card_eq_fintype_card]
  exact card_A5

theorem mem_Hset_of_mem {x : P} (h : x ∈ H) : x ∈ Hset := by
  have h' : x ∈ (H : Set P) := h
  rwa [H_coe] at h'

theorem mem_H_of_mem_Hset {x : P} (h : x ∈ Hset) : x ∈ H := by
  have h' : x ∈ (H : Set P) := by rwa [H_coe]
  exact h'

def mulPair (K L : Subgroup P) (p : ↥K × ↥L) : P := (p.1 : P) * (p.2 : P)

noncomputable def mulFiberEquiv (K L : Subgroup P) (p : ↥K × ↥L) :
    {q : ↥K × ↥L // mulPair K L q = mulPair K L p} ≃ ↥(K ⊓ L) where
  toFun q :=
    ⟨(p.1 : P)⁻¹ * ((q.1).1 : P),
      ⟨K.mul_mem (K.inv_mem p.1.2) ((q.1).1).2,
       by
         have h : ((q.1).1 : P) * ((q.1).2 : P) = (p.1 : P) * (p.2 : P) := q.2
         have h2 : (p.1 : P)⁻¹ * ((q.1).1 : P) = (p.2 : P) * (((q.1).2 : P))⁻¹ := by
           calc (p.1 : P)⁻¹ * ((q.1).1 : P)
               = (p.1 : P)⁻¹ * (((q.1).1 : P) * ((q.1).2 : P)) * (((q.1).2 : P))⁻¹ := by group
             _ = (p.1 : P)⁻¹ * ((p.1 : P) * (p.2 : P)) * (((q.1).2 : P))⁻¹ := by rw [h]
             _ = (p.2 : P) * (((q.1).2 : P))⁻¹ := by group
         rw [h2]
         exact L.mul_mem p.2.2 (L.inv_mem ((q.1).2).2)⟩⟩
  invFun t :=
    ⟨(⟨(p.1 : P) * (t : P), K.mul_mem p.1.2 (Subgroup.mem_inf.mp t.2).1⟩,
      ⟨(t : P)⁻¹ * (p.2 : P), L.mul_mem (L.inv_mem (Subgroup.mem_inf.mp t.2).2) p.2.2⟩),
      by
        show (p.1 : P) * (t : P) * ((t : P)⁻¹ * (p.2 : P)) = (p.1 : P) * (p.2 : P)
        group⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      show (p.1 : P) * ((p.1 : P)⁻¹ * ((q.1).1 : P)) = ((q.1).1 : P)
      group
    · apply Subtype.ext
      have h : ((q.1).1 : P) * ((q.1).2 : P) = (p.1 : P) * (p.2 : P) := q.2
      have h3 : ((q.1).2 : P) = ((q.1).1 : P)⁻¹ * ((p.1 : P) * (p.2 : P)) := by
        calc ((q.1).2 : P) = ((q.1).1 : P)⁻¹ * (((q.1).1 : P) * ((q.1).2 : P)) := by group
          _ = ((q.1).1 : P)⁻¹ * ((p.1 : P) * (p.2 : P)) := by rw [h]
      show ((p.1 : P)⁻¹ * ((q.1).1 : P))⁻¹ * (p.2 : P) = ((q.1).2 : P)
      rw [h3]; group
  right_inv t := by
    apply Subtype.ext
    show (p.1 : P)⁻¹ * ((p.1 : P) * (t : P)) = (t : P)
    group

theorem card_mul_fiber (K L : Subgroup P) (p : ↥K × ↥L) :
    (univ.filter (fun q : ↥K × ↥L => mulPair K L q = mulPair K L p)).card
      = Nat.card ↥(K ⊓ L) := by
  classical
  rw [← Fintype.card_subtype (fun q : ↥K × ↥L => mulPair K L q = mulPair K L p),
    Fintype.card_congr (mulFiberEquiv K L p), Nat.card_eq_fintype_card]

theorem card_image_mul_mul_card_inf (K L : Subgroup P) :
    (univ.image (fun p : ↥K × ↥L => mulPair K L p)).card * Nat.card ↥(K ⊓ L)
      = Nat.card K * Nat.card L := by
  classical
  have h := Finset.card_eq_sum_card_image (fun p : ↥K × ↥L => mulPair K L p) univ
  rw [Finset.card_univ, Fintype.card_prod, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at h
  rw [h, Finset.sum_congr rfl (fun b hb => ?_), Finset.sum_const, smul_eq_mul]
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hb
  rw [← hp]
  exact card_mul_fiber K L p

theorem image_mul_eq_of_card {K L : Subgroup P} {S : Finset P}
    (hsub : ∀ k ∈ K, ∀ l ∈ L, k * l ∈ S)
    (hcard : Nat.card K * Nat.card L = S.card * Nat.card ↥(K ⊓ L)) :
    univ.image (fun p : ↥K × ↥L => mulPair K L p) = S := by
  classical
  have hcpos : 0 < Nat.card ↥(K ⊓ L) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hsub' : univ.image (fun p : ↥K × ↥L => mulPair K L p) ⊆ S := by
    intro y hy
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hy
    exact hsub p.1 p.1.2 p.2 p.2.2
  have hcard' := card_image_mul_mul_card_inf K L
  rw [hcard] at hcard'
  have hcard'' : (univ.image (fun p : ↥K × ↥L => mulPair K L p)).card = S.card :=
    Nat.mul_right_cancel hcpos hcard'
  exact Finset.eq_of_subset_of_card_le hsub' (le_of_eq hcard''.symm)

theorem exists_mul_eq_of_mem {K L : Subgroup P} {S : Finset P}
    (hsub : ∀ k ∈ K, ∀ l ∈ L, k * l ∈ S)
    (hcard : Nat.card K * Nat.card L = S.card * Nat.card ↥(K ⊓ L)) {x : P} (hx : x ∈ S) :
    ∃ k ∈ K, ∃ l ∈ L, k * l = x := by
  have h := image_mul_eq_of_card (K := K) (L := L) (S := S) hsub hcard
  rw [← h] at hx
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hx
  exact ⟨p.1, p.1.2, p.2, p.2.2, hp⟩

theorem inf_H_card_eq_one_of_five (K : Subgroup P) (hcard : Nat.card K = 5) :
    Nat.card ↥(K ⊓ H) = 1 := by
  have hd : Nat.card ↥(K ⊓ H) ∣ Nat.gcd 5 12 := inf_H_dvd_gcd K hcard
  rw [show Nat.gcd 5 12 = 1 from by norm_num, Nat.dvd_one] at hd
  exact hd

theorem inf_H_card_eq_two_of_ten (K : Subgroup P) (hK : K ≤ A5) (hcard : Nat.card K = 10) :
    Nat.card ↥(K ⊓ H) = 2 := by
  have hd : Nat.card ↥(K ⊓ H) ∣ Nat.gcd 10 12 := inf_H_dvd_gcd K hcard
  have hne : Nat.card ↥(K ⊓ H) ≠ 1 := inf_H_ne_one K hK hcard (by norm_num)
  rw [show Nat.gcd 10 12 = 2 from by norm_num] at hd
  have hpos : 0 < Nat.card ↥(K ⊓ H) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hle : Nat.card ↥(K ⊓ H) ≤ 2 := Nat.le_of_dvd (by norm_num) hd
  omega

theorem image_mul_eq_A5_of_card (K : Subgroup P) (hK : K ≤ A5)
    (hcard : Nat.card H * Nat.card K = 60 * Nat.card ↥(H ⊓ K)) :
    univ.image (fun p : ↥H × ↥K => (p.1 : P) * (p.2 : P)) = A5fin := by
  classical
  have hcard' : Nat.card H * Nat.card K = A5fin.card * Nat.card ↥(H ⊓ K) := by
    rw [card_A5fin]; exact hcard
  exact image_mul_eq_of_card (fun k hk l hl => mem_A5fin.mpr (A5.mul_mem (H_le_A5 hk) (hK hl))) hcard'

theorem trace_nonempty_of_five (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5)
    (hcard : Nat.card K = 5) : (trace K x).Nonempty := by
  classical
  have hc := inf_H_card_eq_one_of_five K hcard
  have himg := image_mul_eq_A5_of_card K hK (by rw [H_card, hcard, inf_comm, hc])
  have hx' : x ∈ univ.image (fun p : ↥H × ↥K => (p.1 : P) * (p.2 : P)) := by
    rw [himg]; exact mem_A5fin.mpr hx
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hx'
  refine ⟨(p.1 : P), ?_⟩
  rw [trace_eq]
  refine Finset.mem_inter.mpr ⟨?_, mem_Hset_of_mem p.1.2⟩
  rw [mem_cos]
  have hpx : x⁻¹ * (p.1 : P) = ((p.2 : P))⁻¹ := by rw [← hp]; group
  rw [hpx]
  exact K.inv_mem p.2.2

theorem trace_five (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5)
    (hcard : Nat.card K = 5) : (trace K x).card ∈ attainableTraces 5 := by
  have hne := trace_nonempty_of_five K x hK hx hcard
  have hc := inf_H_card_eq_one_of_five K hcard
  rcases trace_card_zero_or K x with h | h
  · exact absurd h (by have := Finset.card_pos.mpr hne; omega)
  · rw [h, hc]; decide

theorem trace_ten (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5)
    (hcard : Nat.card K = 10) : (trace K x).card ∈ attainableTraces 10 := by
  classical
  have hc := inf_H_card_eq_two_of_ten K hK hcard
  have himg := image_mul_eq_A5_of_card K hK (by rw [H_card, hcard, inf_comm, hc])
  have hne : (trace K x).Nonempty := by
    have hx' : x ∈ univ.image (fun p : ↥H × ↥K => (p.1 : P) * (p.2 : P)) := by
      rw [himg]; exact mem_A5fin.mpr hx
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hx'
    refine ⟨(p.1 : P), ?_⟩
    rw [trace_eq]
    refine Finset.mem_inter.mpr ⟨?_, mem_Hset_of_mem p.1.2⟩
    rw [mem_cos]
    have hpx : x⁻¹ * (p.1 : P) = ((p.2 : P))⁻¹ := by rw [← hp]; group
    rw [hpx]
    exact K.inv_mem p.2.2
  rcases trace_card_zero_or K x with h | h
  · exact absurd h (by have := Finset.card_pos.mpr hne; omega)
  · rw [h, hc]; decide

noncomputable def Hinv : Finset P := Hset.filter (fun x => x * x = 1 ∧ x ≠ 1)

theorem mem_Hinv {x : P} : x ∈ Hinv ↔ x ∈ Hset ∧ (x * x = 1 ∧ x ≠ 1) := by simp [Hinv]
theorem Hinv_card : Hinv.card = 3 := by decide
theorem Hinv_sub : ∀ x ∈ Hinv, x ∈ Hset := fun x hx => (mem_Hinv.mp hx).1

theorem no_order_six_subgroup_of_H (N : Subgroup P) (hN : N ≤ H) (hcard : Nat.card N = 6) : False := by
  classical
  set S3 : Finset P := Hset.filter (fun x : P => x * x * x = 1 ∧ x ≠ 1) with hS3
  set Nf : Finset P := univ.filter (fun x : P => x ∈ N) with hNf
  have hS3card : S3.card = 8 := by rw [hS3]; decide
  have hNfcard : Nf.card = 6 := by
    rw [hNf, ← Fintype.card_subtype (fun x : P => x ∈ N), ← Nat.card_eq_fintype_card]
    exact hcard
  have hNf_sub : ∀ x ∈ Nf, x ∈ Hset := by
    intro x hx
    rw [hNf, Finset.mem_filter] at hx
    exact mem_Hset_of_mem (hN hx.2)
  have hNf_mul : ∀ a ∈ Nf, ∀ b ∈ Nf, a * b ∈ Nf := by
    intro a ha b hb
    rw [hNf, Finset.mem_filter] at ha hb ⊢
    exact ⟨Finset.mem_univ _, N.mul_mem ha.2 hb.2⟩
  have hNf_inv : ∀ a ∈ Nf, a⁻¹ ∈ Nf := by
    intro a ha
    rw [hNf, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, N.inv_mem ha.2⟩
  have key : ∀ x ∈ Hset, x * x * x = 1 → x ≠ 1 → x ∈ Nf := by
    intro x hx hx3 hx1
    by_contra hxN
    have hCcard : (Nf.image (fun n => x * n)).card = 6 := by
      rw [Finset.card_image_of_injective _ (fun a b hab => mul_left_cancel hab), hNfcard]
    have hC_sub : ∀ y ∈ Nf.image (fun n => x * n), y ∈ Hset := by
      intro y hy
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
      exact Hset_mul x hx n (hNf_sub n hn)
    have hdisj : Disjoint Nf (Nf.image (fun n => x * n)) := by
      rw [Finset.disjoint_left]
      intro y hy hyC
      obtain ⟨n, hn, hny⟩ := Finset.mem_image.mp hyC
      have huy : u := x = y * n⁻¹ := by rw [← hny]; group
      exact hxN (by rw [huy]; exact hNf_mul y hy n⁻¹ (hNf_inv n hn))
    have hunion : Nf ∪ (Nf.image (fun n => x * n)) = Hset := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · exact hNf_sub y h
        · exact hC_sub y h
      · rw [Finset.card_union_of_disjoint hdisj, hNfcard, hCcard, Hset_card]
    have hx2 : x * x ∈ Hset := Hset_mul x hx x hx
    rw [← hunion] at hx2
    rcases Finset.mem_union.mp hx2 with h | h
    · have hx4 : (x * x) * (x * x) = x := by
        calc (x * x) * (x * x) = x * (x * x * x) := by group
          _ = x := by rw [hx3, mul_one]
      exact hxN (by rw [← hx4]; exact hNf_mul (x * x) h (x * x) h)
    · obtain ⟨n, hn, hn2⟩ := Finset.mem_image.mp h
      have hxn : x = n := (mul_right_cancel hn2).symm
      exact hxN (by rw [hxn]; exact hn)
  have hsub : S3 ⊆ Nf := by
    intro x hx
    rw [hS3, Finset.mem_filter] at hx
    exact key x hx.1 hx.2.1 hx.2.2
  have h86 : (8 : ℕ) ≤ 6 := by
    calc (8 : ℕ) = S3.card := hS3card.symm
      _ ≤ Nf.card := Finset.card_le_card hsub
      _ = 6 := hNfcard
  omega

theorem trace_six (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5)
    (hcard : Nat.card K = 6) : (trace K x).card ∈ attainableTraces 6 := by
  have hd : Nat.card ↥(K ⊓ H) ∣ Nat.gcd 6 12 := inf_H_dvd_gcd K hcard
  have hne1 : Nat.card ↥(K ⊓ H) ≠ 1 := inf_H_ne_one K hK hcard (by norm_num)
  have hne6 : Nat.card ↥(K ⊓ H) ≠ 6 := fun h6 => no_order_six_subgroup_of_H (K ⊓ H) inf_le_right h6
  rw [show Nat.gcd 6 12 = 6 from by norm_num] at hd
  have hmem : Nat.card ↥(K ⊓ H) ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    rw [← show Nat.divisors 6 = ({1, 2, 3, 6} : Finset ℕ) from by decide]
    exact Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  have h23 : Nat.card ↥(K ⊓ H) = 2 ∨ Nat.card ↥(K ⊓ H) = 3 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  rcases trace_card_zero_or K x with h | h
  · rw [h]; decide
  · rcases h23 with h2 | h3
    · rw [h, h2]; decide
    · rw [h, h3]; decide

theorem pow_four_A5 : ∀ x ∈ A5fin, x * x * x * x = 1 → x * x = 1 := by decide

theorem inv_comm_Hinv : ∀ t ∈ Hinv, ∀ u ∈ A5fin, u * u = 1 → u ≠ 1 → u * t = t * u → u ∈ Hinv := by
  decide

theorem inf_H_card_ne_two (K : Subgroup P) (hK : K ≤ A5) (hcard : Nat.card K = 4) :
    Nat.card ↥(K ⊓ H) ≠ 2 := by
  classical
  intro h2
  have htwo : Fintype.card ↥(K ⊓ H) = 2 := by rwa [← Nat.card_eq_fintype_card]
  have h1lt : 1 < (Finset.univ : Finset ↥(K ⊓ H)).card := by rw [Finset.card_univ, htwo]; norm_num
  obtain ⟨a, -, b, -, hab⟩ := Finset.one_lt_card.mp h1lt
  obtain ⟨t, ht1⟩ : ∃ t : ↥(K ⊓ H), t ≠ 1 := by
    by_cases ha : a = 1
    · exact ⟨b, fun hb => hab (by rw [ha, hb])⟩
    · exact ⟨a, ha⟩
  have htK : (t : P) ∈ K := (Subgroup.mem_inf.mp t.2).1
  have htH : (t : P) ∈ H := (Subgroup.mem_inf.mp t.2).2
  have ht1' : (t : P) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have ht2 : (t : P) * (t : P) = 1 := by
    have h0 : (t : ↥(K ⊓ H)) ^ 2 = 1 := by
      have h : (t : ↥(K ⊓ H)) ^ Fintype.card ↥(K ⊓ H) = 1 := pow_card_eq_one
      rwa [htwo] at h
    have h2 : (t : ↥(K ⊓ H)) * t = 1 := by rw [← h0]; simp [pow_succ]
    simpa using congrArg (fun z : ↥(K ⊓ H) => (z : P)) h2
  have htHinv : (t : P) ∈ Hinv := mem_Hinv.mpr ⟨mem_Hset_of_mem htH, ht2, ht1'⟩
  have hcardF : Fintype.card ↥K = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hpow : ∀ u ∈ K, u * u * u * u = 1 := by
    intro u hu
    have h0 : (⟨u, hu⟩ : ↥K) ^ 4 = 1 := by
      have h : (⟨u, hu⟩ : ↥K) ^ Fintype.card ↥K = 1 := pow_card_eq_one
      rwa [hcardF] at h
    have h4 : (⟨u, hu⟩ : ↥K) * ⟨u, hu⟩ * ⟨u, hu⟩ * ⟨u, hu⟩ = 1 := by
      rw [← h0]; simp [pow_succ]
    simpa using congrArg (fun z : ↥K => (z : P)) h4
  have hKH : K ≤ H := by
    intro k hk
    by_cases hk1 : k = 1
    · rw [hk1]; exact H.one_mem
    · have hkA5 : k ∈ A5 := hK hk
      have hk2 : k * k = 1 := pow_four_A5 k (mem_A5fin.mpr hkA5) (hpow k hk)
      have hkt_mem : k * (t : P) ∈ K := K.mul_mem hk htK
      have hktA5 : k * (t : P) ∈ A5 := A5.mul_mem hkA5 (hK htK)
      have hkt2 : k * (t : P) * (k * (t : P)) = 1 := pow_four_A5 _ (mem_A5fin.mpr hktA5) (hpow _ hkt_mem)
      have hcomm : k * (t : P) = (t : P) * k := by
        calc k * (t : P) = (k * (t : P))⁻¹ := (inv_eq_of_mul_eq_one_right hkt2).symm
          _ = (t : P)⁻¹ * k⁻¹ := mul_inv_rev k (t : P)
          _ = (t : P) * k := by rw [inv_eq_of_mul_eq_one_right hk2, inv_eq_of_mul_eq_one_right ht2]
      have hmem : k ∈ Hinv := inv_comm_Hinv (t : P) htHinv k (mem_A5fin.mpr hkA5) hk2 hk1 hcomm
      exact mem_H_of_mem_Hset (Hinv_sub k hmem)
  have hKeq : K ⊓ H = K := inf_eq_left.mpr hKH
  rw [hKeq, hcard] at h2
  norm_num at h2

theorem trace_four_coset (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5)
    (hcard : Nat.card K = 4) : (trace K x).card ∈ attainableTraces 4 := by
  have hd : Nat.card ↥(K ⊓ H) ∣ Nat.gcd 4 12 := inf_H_dvd_gcd K hcard
  have hne2 := inf_H_card_ne_two K hK hcard
  rw [show Nat.gcd 4 12 = 4 from by norm_num] at hd
  have hmem : Nat.card ↥(K ⊓ H) ∈ ({1, 2, 4} : Finset ℕ) := by
    rw [← show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) from by decide]
    exact Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
  have h14 : Nat.card ↥(K ⊓ H) = 1 ∨ Nat.card ↥(K ⊓ H) = 4 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  rcases trace_card_zero_or K x with h | h
  · rw [h]; decide
  · rcases h14 with h1 | h4
    · rw [h, h1]; decide
    · rw [h, h4]; decide

theorem mem_Kfin {K : Subgroup P} {x : P} : x ∈ Kfin K ↔ x ∈ K := by classical simp [Kfin]

theorem cos_subset_Hset {K : Subgroup P} (hKH : K ≤ H) {h w : P} (hh : h ∈ Hset)
    (hw : w ∈ cos K h) : w ∈ Hset := by
  have h1 : h⁻¹ * w ∈ K := mem_cos.mp hw
  have h2 : h⁻¹ * w ∈ Hset := mem_Hset_of_mem (hKH h1)
  have h3 : w = h * (h⁻¹ * w) := by group
  rw [h3]
  exact Hset_mul h hh (h⁻¹ * w) h2

theorem mul_mem_of_index_two (C K : Subgroup P) (hCK : C ≤ K) (hC : Nat.card C = 3)
    (hK : Nat.card K = 6) {u₁ u : P} (hu₁ : u₁ ∈ K) (hu₁C : u₁ ∉ C) (hu : u ∈ K) (huC : u ∉ C) :
    u₁ * u ∈ C := by
  classical
  have hCu_card : ((Kfin C).image (fun c => c * u)).card = 3 := by
    rw [Finset.card_image_of_injective _ (fun a b hab => mul_right_cancel hab), card_Kfin, hC]
  have hdisj : Disjoint (Kfin C) ((Kfin C).image (fun c => c * u)) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨c, hc, hcy⟩ := Finset.mem_image.mp hy'
    have huy : u = c⁻¹ * y := by rw [← hcy]; group
    exact huC (by rw [huy]; exact C.mul_mem (C.inv_mem (mem_Kfin.mp hc)) (mem_Kfin.mp hy))
  have hKsplit : Kfin C ∪ (Kfin C).image (fun c => c * u) = Kfin K := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact mem_Kfin.mpr (hCK (mem_Kfin.mp h))
      · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp h
        exact mem_Kfin.mpr (K.mul_mem (hCK (mem_Kfin.mp hc)) hu)
    · rw [card_Kfin, hK, Finset.card_union_of_disjoint hdisj, card_Kfin, hC, hCu_card]
  have hu2 : u * u ∈ C := by
    by_contra hnot
    have hmem : u * u ∈ Kfin C ∪ (Kfin C).image (fun c => c * u) := by
      rw [hKsplit]; exact mem_Kfin.mpr (K.mul_mem hu hu)
    rcases Finset.mem_union.mp hmem with h | h
    · exact hnot (mem_Kfin.mp h)
    · obtain ⟨c', hc', hc'eq⟩ := Finset.mem_image.mp h
      have huc' : u = c' := (mul_right_cancel hc'eq).symm
      exact huC (by rw [huc']; exact mem_Kfin.mp hc')
  have hu₁mem : u₁ ∈ Kfin C ∪ (Kfin C).image (fun c => c * u) := by
    rw [hKsplit]; exact mem_Kfin.mpr hu₁
  rcases Finset.mem_union.mp hu₁mem with h | h
  · exact absurd (mem_Kfin.mp h) hu₁C
  · obtain ⟨c, hc, hceq⟩ := Finset.mem_image.mp h
    have : u₁ * u = c * (u * u) := by rw [← hceq]; group
    rw [this]
    exact C.mul_mem (mem_Kfin.mp hc) hu2

theorem lemma41_coset (K L : Subgroup P) (x y : P) (hK : K ≤ A5) (hL : L ≤ A5)
    (hx : x ∈ A5) (hy : y ∈ A5) (hcardK : Nat.card K = 3) (hcardL : Nat.card L = 4)
    (htK : (trace K x).card = 3) (htL : (trace L y).card = 4) :
    ((trace K x) ∩ (trace L y)).card = 1 := by
  classical
  have hKH : K ≤ H := by
    have hc : Nat.card ↥(K ⊓ H) = 3 := by
      rcases trace_card_zero_or K x with h | h
      · rw [h] at htK; omega
      · omega
    have heq : K ⊓ H = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hcardK])
    intro k hk
    exact (Subgroup.mem_inf.mp (by rw [heq]; exact hk)).2
  have hLH : L ≤ H := by
    have hc : Nat.card ↥(L ⊓ H) = 4 := by
      rcases trace_card_zero_or L y with h | h
      · rw [h] at htL; omega
      · omega
    have heq : L ⊓ H = L := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc, hcardL])
    intro l hl
    exact (Subgroup.mem_inf.mp (by rw [heq]; exact hl)).2
  have hKL : Nat.card ↥(K ⊓ L) = 1 := by
    have hd : Nat.card ↥(K ⊓ L) ∣ Nat.gcd (Nat.card K) (Nat.card L) :=
      Nat.dvd_gcd (Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ L : Subgroup P) ≤ K))
        (Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ L : Subgroup P) ≤ L))
    rw [hcardK, hcardL, show Nat.gcd 3 4 = 1 from by norm_num, Nat.dvd_one] at hd
    exact hd
  obtain ⟨h, hh⟩ : (trace K x).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨h', hh'⟩ : (trace L y).Nonempty := Finset.card_pos.mp (by omega)
  rw [trace_eq] at hh hh'
  have hhcos : h ∈ cos K x := (Finset.mem_inter.mp hh).1
  have hhH : h ∈ Hset := (Finset.mem_inter.mp hh).2
  have hh'cos : h' ∈ cos L y := (Finset.mem_inter.mp hh').1
  have hh'H : h' ∈ Hset := (Finset.mem_inter.mp hh').2
  have htraceK : trace K x = cos K h := by
    rw [trace_eq, cos_eq (mem_cos.mp hhcos)]
    exact Finset.inter_eq_left.mpr fun w hw => cos_subset_Hset hKH hhH hw
  have htraceL : trace L y = cos L h' := by
    rw [trace_eq, cos_eq (mem_cos.mp hh'cos)]
    exact Finset.inter_eq_left.mpr fun w hw => cos_subset_Hset hLH hh'H hw
  rw [htraceK, htraceL]
  have hne : ((cos K h) ∩ (cos L h')).Nonempty := by
    have hmem : h'⁻¹ * h ∈ Hset := Hset_mul h'⁻¹ (Hset_inv h' hh'H) h hhH
    obtain ⟨l, hl, k, hk, hlk⟩ := exists_mul_eq_of_mem (K := L) (L := K) (S := Hset)
      (fun l hl k hk => Hset_mul l (mem_Hset_of_mem (hLH hl)) k (mem_Hset_of_mem (hKH hk)))
      (by rw [Hset_card, hcardK, hcardL,
        show Nat.card ↥(L ⊓ K) = 1 from by rw [inf_comm]; exact hKL]) hmem
    refine ⟨h * k⁻¹, ?_⟩
    rw [Finset.mem_inter]
    constructor
    · rw [mem_cos]
      have he : h⁻¹ * (h * k⁻¹) = k⁻¹ := by group
      rw [he]
      exact K.inv_mem hk
    · rw [mem_cos]
      have he : h'⁻¹ * (h * k⁻¹) = l := by rw [← mul_assoc, ← hlk]; group
      rw [he]
      exact hl
  rcases cos_inter K L h h' with h0 | hcard
  · rw [Finset.card_eq_zero] at h0
    rw [h0] at hne
    simp at hne
  · rw [hcard, hKL]

theorem lemma42_coset (K L : Subgroup P) (x y : P) (hK : K ≤ A5) (hL : L ≤ A5)
    (hx : x ∈ A5) (hy : y ∈ A5) (hcardK : Nat.card K = 5) (hcardL : Nat.card L = 10)
    (hdisj : Disjoint (trace K x) (trace L y)) :
    (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤ 1 := by
  classical
  have hsub : ((cos K x) \ Hset) ∩ ((cos L y) \ Hset) ⊆ (cos K x) ∩ (cos L y) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hw1).1, (Finset.mem_sdiff.mp hw2).1⟩
  have hdvd : Nat.card ↥(K ⊓ L) ∣ 5 := by
    have hd : Nat.card ↥(K ⊓ L) ∣ Nat.gcd (Nat.card K) (Nat.card L) :=
      Nat.dvd_gcd (Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ L : Subgroup P) ≤ K))
        (Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ L : Subgroup P) ≤ L))
    rwa [hcardK, hcardL, show Nat.gcd 5 10 = 5 from by norm_num] at hd
  rcases cos_inter K L x y with h0 | hKL
  · exact le_trans (Finset.card_le_card hsub) (by rw [h0]; exact Nat.zero_le 1)
  · by_cases hc5 : Nat.card ↥(K ⊓ L) = 5
    · exfalso
      have hKL' : K ≤ L := by
        have heq : K ⊓ L = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc5, hcardK])
        intro k hk
        exact (Subgroup.mem_inf.mp (by rw [heq]; exact hk)).2
      have hne : ((cos K x) ∩ (cos L y)).Nonempty := Finset.card_pos.mp (by rw [hKL, hc5]; norm_num)
      obtain ⟨z, hz⟩ := hne
      have hzx : z ∈ cos K x := (Finset.mem_inter.mp hz).1
      have hzy : z ∈ cos L y := (Finset.mem_inter.mp hz).2
      have hsubLK : cos K x ⊆ cos L y := by
        rw [mem_cos] at hzx hzy
        rw [cos_eq hzx, cos_eq hzy]
        intro w hw
        rw [mem_cos] at hw ⊢
        exact hKL' hw
      have htrace : trace K x ⊆ trace L y := by
        intro w hw
        rw [trace_eq] at hw ⊢
        exact Finset.mem_inter.mpr ⟨hsubLK (Finset.mem_inter.mp hw).1, (Finset.mem_inter.mp hw).2⟩
      obtain ⟨w, hw⟩ := trace_nonempty_of_five K x hK hx hcardK
      exact Finset.disjoint_left.mp hdisj hw (htrace hw)
    · have h1 : Nat.card ↥(K ⊓ L) = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
        · exact h
        · exact absurd h hc5
      exact le_trans (Finset.card_le_card hsub) (le_of_eq (hKL.trans h1))

theorem lemma43_coset (K L : Subgroup P) (x y : P) (hK : K ≤ A5) (hx : x ∈ A5)
    (hL : L ≤ A5) (hy : y ∈ A5) (hcardK : Nat.card K = 6) (hcardL : Nat.card L = 10)
    (htrace : (trace K x).card = 3) :
    (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card ≤ 1 := by
  classical
  have hC : Nat.card ↥(K ⊓ H) = 3 := by
    rcases trace_card_zero_or K x with h | h
    · rw [h] at htrace; omega
    · omega
  have hsub : ((cos K x) \ Hset) ∩ ((cos L y) \ Hset) ⊆ (cos K x) ∩ (cos L y) := by
    intro w hw
    obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hw1).1, (Finset.mem_sdiff.mp hw2).1⟩
  have hdvd : Nat.card ↥(K ⊓ L) ∣ 2 := by
    have hd : Nat.card ↥(K ⊓ L) ∣ Nat.gcd (Nat.card K) (Nat.card L) :=
      Nat.dvd_gcd (Subgroup.card_dvd_of_le (inf_le_left : (K ⊓ L : Subgroup P) ≤ K))
        (Subgroup.card_dvd_of_le (inf_le_right : (K ⊓ L : Subgroup P) ≤ L))
    rwa [hcardK, hcardL, show Nat.gcd 6 10 = 2 from by norm_num] at hd
  rcases cos_inter K L x y with h0 | hKL
  · exact le_trans (Finset.card_le_card hsub) (by rw [h0]; exact Nat.zero_le 1)
  · by_cases hT : Nat.card ↥(K ⊓ L) = 2
    · by_contra hgt
      have h2 : 2 ≤ (((cos K x) \ Hset) ∩ ((cos L y) \ Hset)).card := by omega
      obtain ⟨a, ha, b, hb, hab⟩ :=
        (Finset.one_lt_card (s := ((cos K x) \ Hset) ∩ ((cos L y) \ Hset))).mp (by omega)
      have haK : a ∈ cos K x := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).1
      have haH : a ∉ Hset := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).1).2
      have haL : a ∈ cos L y := (Finset.mem_sdiff.mp (Finset.mem_inter.mp ha).2).1
      have hbK : b ∈ cos K x := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).1).1
      have hbH : b ∉ Hset := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).1).2
      have hbL : b ∈ cos L y := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hb).2).1
      obtain ⟨h, hh⟩ : (trace K x).Nonempty := Finset.card_pos.mp (by omega)
      rw [trace_eq] at hh
      have hhcos : h ∈ cos K x := (Finset.mem_inter.mp hh).1
      have hhH : h ∈ Hset := (Finset.mem_inter.mp hh).2
      have hxa : x⁻¹ * a ∈ K := mem_cos.mp haK
      have hxb : x⁻¹ * b ∈ K := mem_cos.mp hbK
      have hxh : x⁻¹ * h ∈ K := mem_cos.mp hhcos
      have hya : y⁻¹ * a ∈ L := mem_cos.mp haL
      have hyb : y⁻¹ * b ∈ L := mem_cos.mp hbL
      have hua : h⁻¹ * a ∈ K := by
        have he : h⁻¹ * a = (x⁻¹ * h)⁻¹ * (x⁻¹ * a) := by group
        rw [he]; exact K.mul_mem (K.inv_mem hxh) hxa
      have hub : h⁻¹ * b ∈ K := by
        have he : h⁻¹ * b = (x⁻¹ * h)⁻¹ * (x⁻¹ * b) := by group
        rw [he]; exact K.mul_mem (K.inv_mem hxh) hxb
      have huaH : h⁻¹ * a ∉ K ⊓ H := by
        intro hcon
        exact haH (by
          have : a = h * (h⁻¹ * a) := by group
          rw [this]
          exact Hset_mul h hhH (h⁻¹ * a) (mem_Hset_of_mem (Subgroup.mem_inf.mp hcon).2))
      have huKL : a⁻¹ * b ∈ K ⊓ L := by
        refine ⟨?_, ?_⟩
        · have he : a⁻¹ * b = (h⁻¹ * a)⁻¹ * (h⁻¹ * b) := by group
          rw [he]; exact K.mul_mem (K.inv_mem hua) hub
        · have he : a⁻¹ * b = (y⁻¹ * a)⁻¹ * (y⁻¹ * b) := by group
          rw [he]; exact L.mul_mem (L.inv_mem hya) hyb
      have hu1 : a⁻¹ * b ≠ 1 := fun h1 => hab (inv_mul_eq_one.mp h1)
      have huC : a⁻¹ * b ∉ K ⊓ H := by
        intro hcon
        have hbot : (K ⊓ L) ⊓ (K ⊓ H) = ⊥ := by
          apply Subgroup.card_eq_one.mp
          have hd : Nat.card ↥((K ⊓ L) ⊓ (K ⊓ H)) ∣ 2 := by
            rw [← hT]
            exact Subgroup.card_dvd_of_le inf_le_left
          have hd3 : Nat.card ↥((K ⊓ L) ⊓ (K ⊓ H)) ∣ 3 := by
            rw [← hC]
            refine Subgroup.card_dvd_of_le ?_
            intro z hz
            exact (Subgroup.mem_inf.mp hz).2
          have := Nat.dvd_gcd hd hd3
          rwa [show Nat.gcd 2 3 = 1 from by norm_num, Nat.dvd_one] at this
        have hmem : a⁻¹ * b ∈ (K ⊓ L) ⊓ (K ⊓ H) := ⟨huKL, hcon⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact hu1 hmem
      have hcu : (h⁻¹ * a) * (a⁻¹ * b) ∈ K ⊓ H :=
        mul_mem_of_index_two (K ⊓ H) K inf_le_left hC hcardK hua huaH huKL.1 huC
      have : b = h * ((h⁻¹ * a) * (a⁻¹ * b)) := by group
      exact hbH (by rw [this]; exact Hset_mul h hhH _ (mem_Hset_of_mem (Subgroup.mem_inf.mp hcu).2))
    · have h1 : Nat.card ↥(K ⊓ L) = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
        · exact h
        · exact absurd h hT
      exact le_trans (Finset.card_le_card hsub) (le_of_eq (hKL.trans h1))

noncomputable def a5Equiv : A5 ≃ Fin 60 :=
  (Fintype.equivFin A5).trans (finCongr (by rw [← Nat.card_eq_fintype_card]; exact card_A5))
noncomputable def p5 (p : Fin 60) : P := (a5Equiv.symm p : A5)
theorem p5_mem (p : Fin 60) : p5 p ∈ A5 := (a5Equiv.symm p).2
noncomputable def toFin (y : P) : Fin 60 := if h : y ∈ A5 then a5Equiv ⟨y, h⟩ else 0

theorem toFin_p5 (p : Fin 60) : toFin (p5 p) = p := by
  rw [toFin, dif_pos (p5_mem p)]
  exact a5Equiv.apply_symm_apply p

theorem toFin_injOn {y z : P} (hy : y ∈ A5) (hz : z ∈ A5) (h : toFin y = toFin z) : y = z := by
  have hy' : toFin y = a5Equiv ⟨y, hy⟩ := by rw [toFin]; exact dif_pos hy
  have hz' : toFin z = a5Equiv ⟨z, hz⟩ := by rw [toFin]; exact dif_pos hz
  rw [hy', hz'] at h
  exact congrArg Subtype.val (a5Equiv.injective h)

noncomputable def pointOf (C : Finset P) : Finset (Fin 60) := C.image toFin

theorem mem_pointOf {C : Finset P} {p : Fin 60} : p ∈ pointOf C ↔ ∃ y ∈ C, toFin y = p := Finset.mem_image

theorem mem_pointOf_iff {C : Finset P} (hC : ∀ y ∈ C, y ∈ A5) {p : Fin 60} :
    p ∈ pointOf C ↔ p5 p ∈ C := by
  rw [mem_pointOf]
  constructor
  · rintro ⟨y, hy, hyfin⟩
    have h1 : a5Equiv ⟨y, hC y hy⟩ = a5Equiv (a5Equiv.symm p) := by
      rw [toFin, dif_pos (hC y hy)] at hyfin
      rw [hyfin]
      exact (a5Equiv.apply_symm_apply p).symm
    have h2 : (⟨y, hC y hy⟩ : A5) = a5Equiv.symm p := a5Equiv.injective h1
    have h3 : p5 p = (a5Equiv.symm p : A5) := rfl
    rw [h3, ← h2]
    exact hy
  · intro hp
    exact ⟨p5 p, hp, toFin_p5 p⟩

theorem pointOf_card {C : Finset P} (hC : ∀ y ∈ C, y ∈ A5) : (pointOf C).card = C.card := by
  classical
  rw [pointOf]
  exact Finset.card_image_of_injOn (fun y hy z hz h => toFin_injOn (hC y hy) (hC z hz) h)

theorem pointOf_inter {A B : Finset P} (hA : ∀ y ∈ A, y ∈ A5) (hB : ∀ y ∈ B, y ∈ A5) :
    pointOf (A ∩ B) = pointOf A ∩ pointOf B := by
  classical
  rw [pointOf, pointOf, pointOf]
  refine Finset.image_inter_of_injOn A B (fun y hy z hz h => toFin_injOn ?_ ?_ h)
  · rcases hy with h' | h' <;> [exact hA y h'; exact hB y h']
  · rcases hz with h' | h' <;> [exact hA z h'; exact hB z h']

theorem pointOf_sdiff {A B : Finset P} (hA : ∀ y ∈ A, y ∈ A5) (hB : ∀ y ∈ B, y ∈ A5) :
    pointOf (A \ B) = pointOf A \ pointOf B := by
  classical
  ext p
  rw [Finset.mem_sdiff]
  constructor
  · rw [mem_pointOf]
    rintro ⟨y, hy, rfl⟩
    rw [Finset.mem_sdiff] at hy
    refine ⟨mem_pointOf.mpr ⟨y, hy.1, rfl⟩, fun hcon => hy.2 ?_⟩
    obtain ⟨z, hzB, hzy⟩ := mem_pointOf.mp hcon
    have hzy' : z = y := toFin_injOn (hB z hzB) (hA y hy.1) hzy
    rw [← hzy']
    exact hzB
  · rintro ⟨hA', hnot⟩
    obtain ⟨y, hyA, rfl⟩ := mem_pointOf.mp hA'
    refine mem_pointOf.mpr ⟨y, ?_, rfl⟩
    rw [Finset.mem_sdiff]
    exact ⟨hyA, fun hyB => hnot (mem_pointOf.mpr ⟨y, hyB, rfl⟩)⟩

theorem disjoint_of_disjoint_pointOf {A B : Finset P} (h : Disjoint (pointOf A) (pointOf B)) : Disjoint A B := by
  rw [Finset.disjoint_left] at h ⊢
  intro y hyA hyB
  exact h (Finset.mem_image.mpr ⟨y, hyA, rfl⟩) (Finset.mem_image.mpr ⟨y, hyB, rfl⟩)

theorem Hset_sub : ∀ y ∈ Hset, y ∈ A5 := fun y hy => Hset_even y hy

theorem Kfin_H_eq_Hset : Kfin H = Hset := by
  classical
  ext y
  simp only [Kfin, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨mem_Hset_of_mem, mem_H_of_mem_Hset⟩

theorem cos_sub (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5) : ∀ y ∈ cos K x, y ∈ A5 := by
  intro y hy
  rw [mem_cos] at hy
  have h : y = x * (x⁻¹ * y) := by group
  rw [h]
  exact A5.mul_mem hx (hK hy)

theorem trace_sub (K : Subgroup P) (x : P) (hK : K ≤ A5) (hx : x ∈ A5) : ∀ y ∈ trace K x, y ∈ A5 := by
  intro y hy
  rw [trace_eq] at hy
  exact cos_sub K x hK hx y (Finset.mem_inter.mp hy).1

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

theorem sz_anchor_eq (S : CosetSystem ι) : S.sz S.anchor = 12 := by
  rw [S.sz_eq, S.anchor_K, H_card]

theorem sz_eq_anchor_of_twelve (S : CosetSystem ι) {i : ι} (h : S.sz i = 12) : i = S.anchor :=
  S.sz_injective (h.trans S.sz_anchor_eq.symm)

theorem sz_mem_lower (S : CosetSystem ι) {i : ι} (h : S.sz i ≠ 12) : S.sz i ∈ lowerSizes := by
  have hmem : S.sz i ∈ (insert 12 CertPP12.lowerSizes : Finset ℕ) := S.sz_mem i
  rcases Finset.mem_insert.mp hmem with h' | h'
  · exact absurd h' h
  · exact h'

theorem trace_point (S : CosetSystem ι) (i : ι) :
    pointOf (trace (S.K i) (S.x i)) = pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset := by
  rw [← pointOf_inter (S.coset_sub i) Hset_sub, trace_eq]

theorem trace_point_card (S : CosetSystem ι) (i : ι) :
    (pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset).card = ((cos (S.K i) (S.x i)) ∩ Hset).card := by
  rw [← S.trace_point i, ← trace_eq]
  exact pointOf_card (S.trace_sub' i)

theorem trace_card' (S : CosetSystem ι) (i : ι) :
    (pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset).card = (trace (S.K i) (S.x i)).card := by
  rw [S.trace_point_card i, trace_eq]

theorem trace_inter_point_card (S : CosetSystem ι) (i j : ι) :
    ((pointOf (cos (S.K i) (S.x i)) ∩ pointOf Hset) ∩
      (pointOf (cos (S.K j) (S.x j)) ∩ pointOf Hset)).card
      = ((trace (S.K i) (S.x i)) ∩ (trace (S.K j) (S.x j))).card := by
  rw [← S.trace_point i, ← S.trace_point j, ← pointOf_inter (S.trace_sub' i) (S.trace_sub' j)]
  refine pointOf_card fun y hy => ?_
  rw [trace_eq] at hy
  exact cos_sub _ _ (S.K_le i) (S.x_mem i) y (Finset.mem_inter.mp (Finset.mem_inter.mp hy).1).1

theorem out_point_card (S : CosetSystem ι) (i j : ι) :
    (((pointOf (cos (S.K i) (S.x i))) \ pointOf Hset) ∩
      ((pointOf (cos (S.K j) (S.x j))) \ pointOf Hset)).card
      = (((cos (S.K i) (S.x i)) \ Hset) ∩ ((cos (S.K j) (S.x j)) \ Hset)).card := by
  rw [← pointOf_sdiff (S.coset_sub i) Hset_sub, ← pointOf_sdiff (S.coset_sub j) Hset_sub,
    ← pointOf_inter ?_ ?_]
  · refine pointOf_card fun y hy => ?_
    exact cos_sub _ _ (S.K_le i) (S.x_mem i) y (Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1
  · intro y hy
    exact cos_sub _ _ (S.K_le i) (S.x_mem i) y (Finset.mem_sdiff.mp hy).1
  · intro y hy
    exact cos_sub _ _ (S.K_le j) (S.x_mem j) y (Finset.mem_sdiff.mp hy).1

noncomputable def toAnchored (S : CosetSystem ι) : CertPP12.Anchored ι where
  anchor := S.anchor
  sz := S.sz
  point := fun i => pointOf (cos (S.K i) (S.x i))
  H := pointOf Hset
  sz_anchor := S.sz_anchor_eq
  sz_mem := S.sz_mem
  sz_injective := S.sz_injective
  card_point := by
    intro i
    rw [pointOf_card (S.coset_sub i), card_cos, ← S.sz_eq i]
  point_anchor := by
    rw [S.anchor_K, S.anchor_x, cos_one, Kfin_H_eq_Hset]
  card_H := by rw [pointOf_card Hset_sub, Hset_card]
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
        · rw [hk']
          exact ⟨Finset.mem_univ _, (mem_pointOf_iff (S.coset_sub i')).mpr hi'⟩
        · rw [Finset.mem_singleton] at hk'
          rw [hk']
          exact ⟨Finset.mem_univ _, (mem_pointOf_iff (S.coset_sub j')).mpr hj'⟩
      have hcard := Finset.card_le_card hsub
      rwa [Finset.card_pair hij] at hcard
    · right
      intro i hpi
      exact hsome ⟨i, (mem_pointOf_iff (S.coset_sub i)).mp hpi⟩
  trace_table := by
    intro i
    rw [S.trace_card' i]
    have hcases : S.sz i = 12 ∨ S.sz i = 1 ∨ S.sz i = 2 ∨ S.sz i = 3 ∨ S.sz i = 4 ∨
        S.sz i = 5 ∨ S.sz i = 6 ∨ S.sz i = 10 := by
      have hmem : S.sz i ∈ (insert 12 CertPP12.lowerSizes : Finset ℕ) := S.sz_mem i
      rcases Finset.mem_insert.mp hmem with h' | h'
      · exact Or.inl h'
      · have h'' : S.sz i ∈ ({1, 2, 3, 4, 5, 6, 10} : Finset ℕ) := h'
        simp only [Finset.mem_insert, Finset.mem_singleton] at h''
        tauto
    have hK : Nat.card (S.K i) = S.sz i := (S.sz_eq i).symm
    rcases hcases with h | h | h | h | h | h | h | h
    · have hia : i = S.anchor := S.sz_eq_anchor_of_twelve h
      subst hia
      rw [h, S.anchor_K, S.anchor_x, trace_eq, cos_one, Kfin_H_eq_Hset, Finset.inter_self, Hset_card]
      decide
    · rw [h]; exact trace_one (S.K i) (S.x i) (by rw [hK, h])
    · rw [h]; exact trace_two (S.K i) (S.x i) (by rw [hK, h])
    · rw [h]; exact trace_three (S.K i) (S.x i) (by rw [hK, h])
    · rw [h]; exact trace_four_coset (S.K i) (S.x i) (S.K_le i) (S.x_mem i) (by rw [hK, h])
    · rw [h]; exact trace_five (S.K i) (S.x i) (S.K_le i) (S.x_mem i) (by rw [hK, h])
    · rw [h]; exact trace_six (S.K i) (S.x i) (S.K_le i) (S.x_mem i) (by rw [hK, h])
    · rw [h]; exact trace_ten (S.K i) (S.x i) (S.K_le i) (S.x_mem i) (by rw [hK, h])
  pair_cap := by
    intro i j hij
    by_cases hi12 : S.sz i = 12
    · have hia : i = S.anchor := S.sz_eq_anchor_of_twelve hi12
      rw [hia]
      have hpt : pointOf (cos (S.K S.anchor) (S.x S.anchor)) = pointOf Hset := by
        rw [S.anchor_K, S.anchor_x, cos_one, Kfin_H_eq_Hset]
      rw [hpt, Finset.sdiff_self, Finset.empty_inter, Finset.card_empty]
      exact Nat.zero_le _
    · by_cases hj12 : S.sz j = 12
      · have hja : j = S.anchor := S.sz_eq_anchor_of_twelve hj12
        rw [hja]
        have hpt : pointOf (cos (S.K S.anchor) (S.x S.anchor)) = pointOf Hset := by
          rw [S.anchor_K, S.anchor_x, cos_one, Kfin_H_eq_Hset]
        rw [hpt, Finset.sdiff_self, Finset.inter_empty, Finset.card_empty]
        exact Nat.zero_le _
      · rw [S.out_point_card i j, S.trace_point_card i, S.trace_point_card j, S.sz_eq i, S.sz_eq j]
        exact pair_cap_coset (S.K i) (S.K j) (S.x i) (S.x j)
          (by rw [← S.sz_eq i]; exact S.sz_mem_lower hi12)
          (by rw [← S.sz_eq j]; exact S.sz_mem_lower hj12)
  lemma41 := by
    intro i j hi hj hci hcj
    rw [S.trace_inter_point_card i j]
    refine lemma41_coset (S.K i) (S.K j) (S.x i) (S.x j) (S.K_le i) (S.K_le j) (S.x_mem i)
      (S.x_mem j) (by rw [← S.sz_eq i, hi]) (by rw [← S.sz_eq j, hj]) ?_ ?_
    · rw [trace_eq]
      exact (S.trace_point_card i).symm.trans hci
    · rw [trace_eq]
      exact (S.trace_point_card j).symm.trans hcj
  lemma42 := by
    intro i j hi hj hdisj
    rw [S.out_point_card i j]
    exact lemma42_coset (S.K i) (S.K j) (S.x i) (S.x j) (S.K_le i) (S.K_le j) (S.x_mem i)
      (S.x_mem j) (by rw [← S.sz_eq i, hi]) (by rw [← S.sz_eq j, hj])
      (disjoint_of_disjoint_pointOf (by rw [S.trace_point i, S.trace_point j]; exact hdisj))
  lemma43 := by
    intro i j hi hci hj
    rw [S.out_point_card i j]
    exact lemma43_coset (S.K i) (S.K j) (S.x i) (S.x j) (S.K_le i) (S.x_mem i) (S.K_le j)
      (S.x_mem j) (by rw [← S.sz_eq i, hi]) (by rw [← S.sz_eq j, hj])
      (by rw [trace_eq]; exact (S.trace_point_card i).symm.trans hci)

end CosetSystem

theorem anchor_twelve_closed {ι : Type*} [Fintype ι] [DecidableEq ι] (S : CosetSystem ι) : False :=
  CertPP12.Anchored.no_anchored_system S.toAnchored

end CertPP12Inputs
end HSC
