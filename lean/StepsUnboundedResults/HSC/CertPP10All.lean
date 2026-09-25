/-
HSC/CertPP10All.lean

Closing the final conjugacy step for the order-10 anchor of `Cert-PP(A₅)`.
-/
import StepsUnboundedResults.HSC.CertPP10Inputs
import Mathlib

open scoped Classical
open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace HSC
namespace CertPP10All

abbrev P : Type := CertPP10Inputs.P
abbrev A5 : Subgroup P := CertPP10Inputs.A5
abbrev H : Subgroup P := CertPP10Inputs.H
abbrev Psub : Subgroup P := CertPP10Inputs.Psub
noncomputable abbrev A5fin : Finset P := CertPP10Inputs.A5fin
abbrev Hset : Finset P := CertPP10Inputs.Hset
abbrev Pset : Finset P := CertPP10Inputs.Pset
abbrev r1 : P := CertPP10Inputs.r1
abbrev r2 : P := CertPP10Inputs.r2
noncomputable abbrev cos (K : Subgroup P) (x : P) : Finset P := CertPP10Inputs.cos K x

noncomputable def conjHom (g : P) : P →* P where
  toFun k := g * k * g⁻¹
  map_one' := by group
  map_mul' a b := by group

@[simp] theorem conjHom_apply (g k : P) : conjHom g k = g * k * g⁻¹ := rfl

theorem conjHom_injective (g : P) : Function.Injective (conjHom g) := by
  intro a b hab
  have h : g * a * g⁻¹ = g * b * g⁻¹ := hab
  simpa using congrArg (fun t => g⁻¹ * t * g) h

noncomputable abbrev conjSub (g : P) (K : Subgroup P) : Subgroup P := Subgroup.map (conjHom g) K

theorem mem_conj_cos {K : Subgroup P} {x p g : P} :
    p ∈ cos (conjSub g K) (g * x * g⁻¹) ↔ g⁻¹ * p * g ∈ cos K x := by
  rw [CertPP10Inputs.mem_cos, CertPP10Inputs.mem_cos, Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, hk'⟩
    rw [conjHom_apply] at hk'
    have h4 : x⁻¹ * (g⁻¹ * p * g) = k := by
      have h5 : x⁻¹ * (g⁻¹ * p * g) = g⁻¹ * ((g * x * g⁻¹)⁻¹ * p) * g := by group
      rw [h5, ← hk']
      group
    rw [h4]
    exact hk
  · rintro hp
    exact ⟨x⁻¹ * (g⁻¹ * p * g), hp, by rw [conjHom_apply]; group⟩

structure CosetSystemFor (H' : Subgroup P) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  anchor : ι
  K : ι → Subgroup P
  x : ι → P
  sz : ι → ℕ
  sz_eq : ∀ i, sz i = Nat.card (K i)
  sz_mem : ∀ i, sz i ∈ CertPP10.allSizes
  sz_injective : Function.Injective sz
  K_le : ∀ i, K i ≤ A5
  x_mem : ∀ i, x i ∈ A5
  anchor_K : K anchor = H'
  anchor_x : x anchor = 1
  cover : ∀ p ∈ A5, (∃ i, p ∈ cos (K i) (x i)) →
    ∃ i j, i ≠ j ∧ p ∈ cos (K i) (x i) ∧ p ∈ cos (K j) (x j)

namespace CosetSystemFor
variable {H' : Subgroup P} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem anchor_le (S : CosetSystemFor H' ι) : H' ≤ A5 := by
  rw [← S.anchor_K]
  exact S.K_le S.anchor

def toCoset (S : CosetSystemFor H ι) : CertPP10Inputs.CosetSystem ι where
  anchor := S.anchor
  K := S.K
  x := S.x
  sz := S.sz
  sz_eq := S.sz_eq
  sz_mem := S.sz_mem
  sz_injective := S.sz_injective
  K_le := S.K_le
  x_mem := S.x_mem
  anchor_K := S.anchor_K
  anchor_x := S.anchor_x
  cover := S.cover

noncomputable def conj (S : CosetSystemFor H' ι) (g : P) (hg : g ∈ A5) :
    CosetSystemFor (conjSub g H') ι where
  anchor := S.anchor
  K := fun i => conjSub g (S.K i)
  x := fun i => g * S.x i * g⁻¹
  sz := S.sz
  sz_eq := by
    intro i
    rw [S.sz_eq i, Subgroup.card_map_of_injective (conjHom_injective g)]
  sz_mem := S.sz_mem
  sz_injective := S.sz_injective
  K_le := by
    intro i y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [conjHom_apply]
    exact A5.mul_mem (A5.mul_mem hg (S.K_le i hz)) (A5.inv_mem hg)
  x_mem := fun i => A5.mul_mem (A5.mul_mem hg (S.x_mem i)) (A5.inv_mem hg)
  anchor_K := by
    show conjSub g (S.K S.anchor) = conjSub g H'
    rw [S.anchor_K]
  anchor_x := by
    show g * S.x S.anchor * g⁻¹ = 1
    rw [S.anchor_x, mul_one, mul_inv_cancel]
  cover := by
    intro p hp hex
    obtain ⟨i, hi⟩ := hex
    have hmem : g⁻¹ * p * g ∈ A5 := A5.mul_mem (A5.mul_mem (A5.inv_mem hg) hp) hg
    have hi' : g⁻¹ * p * g ∈ cos (S.K i) (S.x i) := mem_conj_cos.mp hi
    obtain ⟨i', j', hij, h1, h2⟩ := S.cover (g⁻¹ * p * g) hmem ⟨i, hi'⟩
    exact ⟨i', j', hij, mem_conj_cos.mpr h1, mem_conj_cos.mpr h2⟩

end CosetSystemFor

theorem pow_five_conj :
    ∀ y ∈ A5fin, y ^ 5 = 1 → y ≠ 1 →
      ∃ g ∈ A5fin, g * y * g⁻¹ = r1 ∨ g * y * g⁻¹ = r2 := by
  decide

theorem not_conj_r2_r1 : ∀ g ∈ A5fin, g * r2 * g⁻¹ ≠ r1 := by decide

theorem normalizer_mem : ∀ x ∈ A5fin, (∀ p ∈ Pset, x * p * x⁻¹ ∈ Pset) ↔ x ∈ Hset := by decide

theorem pow_five_repr_r1 : ∀ p ∈ Pset, ∃ k : Fin 5, r1 ^ (k : ℕ) = p := by decide

theorem pow_five_repr_r2 : ∀ p ∈ Pset, ∃ k : Fin 5, r2 ^ (k : ℕ) = p := by decide

theorem Psub_le_zpowers_r1 : Psub ≤ Subgroup.zpowers r1 := by
  intro p hp
  obtain ⟨k, hk⟩ := pow_five_repr_r1 p (CertPP10Inputs.mem_Pset_of_mem_Psub hp)
  rw [← hk]
  exact Subgroup.npow_mem_zpowers r1 k

theorem Psub_le_zpowers_r2 : Psub ≤ Subgroup.zpowers r2 := by
  intro p hp
  obtain ⟨k, hk⟩ := pow_five_repr_r2 p (CertPP10Inputs.mem_Pset_of_mem_Psub hp)
  rw [← hk]
  exact Subgroup.npow_mem_zpowers r2 k

theorem Psub_le_zpowers_of_mem {w : P} (hw : w = r1 ∨ w = r2) : Psub ≤ Subgroup.zpowers w := by
  rcases hw with rfl | rfl
  · exact Psub_le_zpowers_r1
  · exact Psub_le_zpowers_r2

theorem mem_conjSub_of_conj {H' : Subgroup P} {g y w : P} (hy : y ∈ H')
    (h : g * y * g⁻¹ = w) : w ∈ conjSub g H' :=
  ⟨y, hy, by rw [conjHom_apply]; exact h⟩

theorem eq_H_of_card_ten {M : Subgroup P} (hM : M ≤ A5) (hcard : Nat.card M = 10)
    (hP : Psub ≤ M) : M = H := by
  have hQcard : Nat.card ↥(Psub.subgroupOf M) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, CertPP10Inputs.Psub_card]
  have hindex : (Psub.subgroupOf M).index = 2 := by
    have h := Subgroup.card_mul_index (H := Psub.subgroupOf M)
    rw [hQcard] at h
    omega
  have hnormal : (Psub.subgroupOf M).Normal := Subgroup.normal_of_index_eq_two hindex
  have hconj : ∀ x ∈ M, ∀ p ∈ Psub, x * p * x⁻¹ ∈ Psub := by
    intro x hx p hp
    have hmem : (⟨p, hP hp⟩ : ↥M) ∈ Psub.subgroupOf M := Subgroup.mem_subgroupOf.mpr hp
    have h1 : (⟨x, hx⟩ : ↥M) * ⟨p, hP hp⟩ * (⟨x, hx⟩ : ↥M)⁻¹ ∈ Psub.subgroupOf M :=
      hnormal.conj_mem ⟨p, hP hp⟩ hmem ⟨x, hx⟩
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hle : M ≤ H := by
    intro x hx
    have hxA5 : x ∈ A5fin := CertPP10Inputs.mem_A5fin.mpr (hM hx)
    have hcond : ∀ p ∈ Pset, x * p * x⁻¹ ∈ Pset := fun p hp =>
      CertPP10Inputs.mem_Pset_of_mem_Psub (hconj x hx p (CertPP10Inputs.mem_Psub_of_mem_Pset hp))
    exact CertPP10Inputs.mem_H_of_mem_Hset ((normalizer_mem x hxA5).mp hcond)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, CertPP10Inputs.H_card])

theorem exists_conj_eq_H10 {H' : Subgroup P} (hH' : H' ≤ A5) (hcard : Nat.card H' = 10) :
    ∃ g ∈ A5, conjSub g H' = H := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy5⟩ := exists_prime_orderOf_dvd_card' (G := ↥H') 5 (by rw [hcard]; norm_num)
  have hy5' : (y : P) ^ 5 = 1 := by
    have h : y ^ orderOf y = 1 := pow_orderOf_eq_one y
    rw [hy5] at h
    simpa using congrArg (fun z : ↥H' => (z : P)) h
  have hyne : (y : P) ≠ 1 := by
    intro h
    have hy1 : y = 1 := Subtype.ext h
    rw [hy1, orderOf_one] at hy5
    omega
  have hyA5 : (y : P) ∈ A5fin := CertPP10Inputs.mem_A5fin.mpr (hH' y.2)
  obtain ⟨g, hgA5, hgy⟩ := pow_five_conj (y : P) hyA5 hy5' hyne
  have hgA5' : g ∈ A5 := CertPP10Inputs.mem_A5fin.mp hgA5
  refine ⟨g, hgA5', ?_⟩
  have hMle : conjSub g H' ≤ A5 := by
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨k, hk, rfl⟩ := hz
    rw [conjHom_apply]
    exact A5.mul_mem (A5.mul_mem hgA5' (hH' hk)) (A5.inv_mem hgA5')
  have hMcard : Nat.card ↥(conjSub g H') = 10 := by
    rw [Subgroup.card_map_of_injective (conjHom_injective g), hcard]
  have hPsub_le : Psub ≤ conjSub g H' := by
    rcases hgy with h | h
    · exact le_trans (Psub_le_zpowers_of_mem (Or.inl rfl))
        (Subgroup.zpowers_le.mpr (mem_conjSub_of_conj y.2 h))
    · exact le_trans (Psub_le_zpowers_of_mem (Or.inr rfl))
        (Subgroup.zpowers_le.mpr (mem_conjSub_of_conj y.2 h))
  exact eq_H_of_card_ten hMle hMcard hPsub_le

namespace CosetSystemFor
variable {H' : Subgroup P} {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def toExplicit (S : CosetSystemFor H' ι) (hH' : H' ≤ A5)
    (hcard : Nat.card H' = 10) : CertPP10Inputs.CosetSystem ι :=
  let g := Classical.choose (exists_conj_eq_H10 hH' hcard)
  let hg := Classical.choose_spec (exists_conj_eq_H10 hH' hcard)
  (hg.2 ▸ S.conj g hg.1).toCoset

end CosetSystemFor

theorem anchor_ten_closed_all {ι : Type*} [Fintype ι] [DecidableEq ι] (H' : Subgroup P)
    (hcard : Nat.card H' = 10) (S : CosetSystemFor H' ι) : False :=
  CertPP10Inputs.anchor_ten_closed (S.toExplicit S.anchor_le hcard)

theorem anchor_ten_closed_alt5 {ι : Type*} [Fintype ι] [DecidableEq ι] (H'' : Subgroup A5)
    (hcard : Nat.card H'' = 10) (S : CosetSystemFor (Subgroup.map A5.subtype H'') ι) : False :=
  anchor_ten_closed_all _ (by
    rw [Subgroup.card_map_of_injective A5.subtype_injective]
    exact hcard) S

theorem anchor_ten_closed_H {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : CosetSystemFor H ι) : False :=
  CertPP10Inputs.anchor_ten_closed S.toCoset

end CertPP10All
end HSC
