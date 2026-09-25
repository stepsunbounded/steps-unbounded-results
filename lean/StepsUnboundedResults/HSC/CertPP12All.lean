/-
HSC/CertPP12All.lean

Closing the last external step of the `S = 12` anchor of `Cert-PP(A₅)`.

`HSC/CertPP12Inputs.lean` proves `anchor_twelve_closed` for one explicit order-`12` subgroup.
This module proves the conjugacy reduction and closes the anchor for every order-`12` subgroup.
-/
import StepsUnboundedResults.HSC.CertPP12Inputs
import Mathlib

open scoped Classical
open Finset

set_option maxRecDepth 100000

namespace HSC
namespace CertPP12All

abbrev P : Type := CertPP12Inputs.P
abbrev A5 : Subgroup P := CertPP12Inputs.A5
abbrev H : Subgroup P := CertPP12Inputs.H
noncomputable abbrev A5fin : Finset P := CertPP12Inputs.A5fin
abbrev Hset : Finset P := CertPP12Inputs.Hset

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
    p ∈ CertPP12Inputs.cos (conjSub g K) (g * x * g⁻¹) ↔
      g⁻¹ * p * g ∈ CertPP12Inputs.cos K x := by
  rw [CertPP12Inputs.mem_cos, CertPP12Inputs.mem_cos, Subgroup.mem_map]
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
  sz_mem : ∀ i, sz i ∈ CertPP12.allSizes
  sz_injective : Function.Injective sz
  K_le : ∀ i, K i ≤ A5
  x_mem : ∀ i, x i ∈ A5
  anchor_K : K anchor = H'
  anchor_x : x anchor = 1
  cover : ∀ p ∈ A5, (∃ i, p ∈ CertPP12Inputs.cos (K i) (x i)) →
    ∃ i j, i ≠ j ∧ p ∈ CertPP12Inputs.cos (K i) (x i) ∧ p ∈ CertPP12Inputs.cos (K j) (x j)

namespace CosetSystemFor
variable {H' : Subgroup P} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem anchor_le (S : CosetSystemFor H' ι) : H' ≤ A5 := by
  rw [← S.anchor_K]
  exact S.K_le S.anchor

def toCoset (S : CosetSystemFor H ι) : CertPP12Inputs.CosetSystem ι where
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
    have hi' : g⁻¹ * p * g ∈ CertPP12Inputs.cos (S.K i) (S.x i) := mem_conj_cos.mp hi
    obtain ⟨i', j', hij, h1, h2⟩ := S.cover (g⁻¹ * p * g) hmem ⟨i, hi'⟩
    exact ⟨i', j', hij, mem_conj_cos.mpr h1, mem_conj_cos.mpr h2⟩

end CosetSystemFor

theorem fix_three_eq_one :
    ∀ x ∈ A5fin, 3 ≤ (univ.filter fun i : Fin 5 => x i = i).card → x = 1 := by
  decide

theorem fix_four_mem_Hset : ∀ x ∈ A5fin, x 4 = 4 → x ∈ Hset := by
  decide

theorem exists_smul_eq_four (x : Fin 5) : ∃ g ∈ A5, g • x = 4 := by
  by_cases hx : x = 4
  · exact ⟨1, A5.one_mem, by rw [hx]; simp⟩
  · have h3 : (((univ : Finset (Fin 5)).erase 4).erase x).card = 3 := by
      rw [Finset.card_erase_of_mem (by simp [hx] : x ∈ (univ : Finset (Fin 5)).erase 4),
        Finset.card_erase_of_mem (by simp : (4 : Fin 5) ∈ (univ : Finset (Fin 5))),
        Finset.card_univ, Fintype.card_fin]
    obtain ⟨k, hk⟩ : (((univ : Finset (Fin 5)).erase 4).erase x).Nonempty := by
      rw [← Finset.card_pos, h3]
      norm_num
    have hkx : k ≠ x := (Finset.mem_erase.mp hk).1
    have hk4 : k ≠ 4 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    refine ⟨Equiv.swap 4 k * Equiv.swap k x, ?_, ?_⟩
    · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (Ne.symm hk4),
        Equiv.Perm.sign_swap hkx]
      norm_num
    · show (Equiv.swap 4 k * Equiv.swap k x) x = 4
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right (a := k) (b := x),
        Equiv.swap_apply_right (a := 4) (b := k)]

noncomputable def orbF (H' : Subgroup P) (x : Fin 5) : Finset (Fin 5) :=
  univ.filter fun y => y ∈ MulAction.orbit H' x

theorem mem_orbF {H' : Subgroup P} {x y : Fin 5} : y ∈ orbF H' x ↔ y ∈ MulAction.orbit H' x :=
  Finset.mem_filter.trans ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem orbF_card_eq {H' : Subgroup P} (x : Fin 5) :
    (orbF H' x).card = Fintype.card ↥(MulAction.orbit H' x) :=
  (Fintype.card_subtype fun y : Fin 5 => y ∈ MulAction.orbit H' x).symm

theorem orbF_card_dvd {H' : Subgroup P} (hcard : Nat.card H' = 12) (x : Fin 5) :
    (orbF H' x).card ∣ 12 := by
  have hcard' : Fintype.card ↥H' = 12 := by rwa [Nat.card_eq_fintype_card] at hcard
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H' x
  rw [hcard'] at h
  rw [orbF_card_eq x]
  exact ⟨_, h.symm⟩

theorem orbF_card_le_five {H' : Subgroup P} (x : Fin 5) : (orbF H' x).card ≤ 5 := by
  have h : (orbF H' x).card ≤ (univ : Finset (Fin 5)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa using h

theorem two_le_orbF_card {H' : Subgroup P} (hcon : ∀ x : Fin 5, ∃ h : H', h • x ≠ x) (x : Fin 5) :
    2 ≤ (orbF H' x).card := by
  by_contra hlt
  push Not at hlt
  have h1 : (orbF H' x).card = 1 := by
    have hpos : 0 < (orbF H' x).card :=
      Finset.card_pos.mpr ⟨x, mem_orbF.mpr (MulAction.mem_orbit_self x)⟩
    omega
  have hcardO : Fintype.card ↥(MulAction.orbit H' x) = 1 := by
    rw [← orbF_card_eq x]
    exact h1
  have hfix : x ∈ MulAction.fixedPoints H' (Fin 5) :=
    MulAction.mem_fixedPoints_iff_card_orbit_eq_one.mpr hcardO
  obtain ⟨h, hh⟩ := hcon x
  exact hh (MulAction.mem_fixedPoints.mp hfix h)

theorem orbF_subset_compl {H' : Subgroup P} {x y : Fin 5} (hy : y ∉ MulAction.orbit H' x) :
    orbF H' y ⊆ (orbF H' x)ᶜ := by
  intro z hz
  rw [Finset.mem_compl]
  intro hzx
  have h1 : y ∈ MulAction.orbit H' z := MulAction.mem_orbit_symm.mpr (mem_orbF.mp hz)
  rw [MulAction.orbit_eq_iff.mpr (mem_orbF.mp hzx)] at h1
  exact hy h1

theorem orbF_disjoint {H' : Subgroup P} {x y : Fin 5} (hy : y ∉ MulAction.orbit H' x) :
    Disjoint (orbF H' x) (orbF H' y) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have h1 : y ∈ MulAction.orbit H' z := MulAction.mem_orbit_symm.mpr (mem_orbF.mp hzy)
  rw [MulAction.orbit_eq_iff.mpr (mem_orbF.mp hzx)] at h1
  exact hy h1

theorem exists_orbF_card_three {H' : Subgroup P} (hcard : Nat.card H' = 12)
    (hcon : ∀ x : Fin 5, ∃ h : H', h • x ≠ x) : ∃ x : Fin 5, (orbF H' x).card = 3 := by
  have hmem : (orbF H' (0 : Fin 5)).card ∈ ({2, 3, 4} : Finset ℕ) := by
    have hd := orbF_card_dvd hcard (0 : Fin 5)
    have h2 := two_le_orbF_card hcon (0 : Fin 5)
    have h5 := orbF_card_le_five (H' := H') (0 : Fin 5)
    have h12 : (orbF H' (0 : Fin 5)).card ∈ Nat.divisors 12 :=
      Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    rw [show Nat.divisors 12 = ({1, 2, 3, 4, 6, 12} : Finset ℕ) from by decide] at h12
    simp only [Finset.mem_insert, Finset.mem_singleton] at h12 ⊢
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h
  · obtain ⟨y, hy⟩ : ((orbF H' (0 : Fin 5))ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, h]
      norm_num
    have hy0 : y ∉ MulAction.orbit H' (0 : Fin 5) :=
      fun hh => (Finset.mem_compl.mp hy) (mem_orbF.mpr hh)
    have hy3 : (orbF H' y).card ≤ 3 := by
      have h1 := Finset.card_le_card (orbF_subset_compl hy0)
      rw [Finset.card_compl, Fintype.card_fin, h] at h1
      omega
    have hy2 := two_le_orbF_card hcon y
    have hydvd := orbF_card_dvd hcard y
    have hymem : (orbF H' y).card = 2 ∨ (orbF H' y).card = 3 := by
      have h12 : (orbF H' y).card ∈ Nat.divisors 12 :=
        Nat.mem_divisors.mpr ⟨hydvd, by norm_num⟩
      rw [show Nat.divisors 12 = ({1, 2, 3, 4, 6, 12} : Finset ℕ) from by decide] at h12
      simp only [Finset.mem_insert, Finset.mem_singleton] at h12
      omega
    rcases hymem with h2 | h3
    · exfalso
      have hunion : (orbF H' (0 : Fin 5) ∪ orbF H' y).card = 4 := by
        rw [Finset.card_union_of_disjoint (orbF_disjoint hy0), h, h2]
      obtain ⟨z, hz⟩ : ((orbF H' (0 : Fin 5) ∪ orbF H' y)ᶜ).Nonempty := by
        rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, hunion]
        norm_num
      have hzu : z ∉ orbF H' (0 : Fin 5) ∪ orbF H' y := Finset.mem_compl.mp hz
      have hz0 : z ∉ MulAction.orbit H' (0 : Fin 5) :=
        fun hh => hzu (Finset.mem_union.mpr (Or.inl (mem_orbF.mpr hh)))
      have hzy : z ∉ MulAction.orbit H' y :=
        fun hh => hzu (Finset.mem_union.mpr (Or.inr (mem_orbF.mpr hh)))
      have hsub : orbF H' z ⊆ (orbF H' (0 : Fin 5) ∪ orbF H' y)ᶜ := by
        intro w hw
        rw [Finset.mem_compl]
        intro hwu
        rcases Finset.mem_union.mp hwu with hw0 | hwy
        · exact (Finset.mem_compl.mp (orbF_subset_compl hz0 hw)) hw0
        · exact (Finset.mem_compl.mp (orbF_subset_compl hzy hw)) hwy
      have hle : (orbF H' z).card ≤ 1 := by
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_compl, Fintype.card_fin, hunion] at h1
        omega
      have h2' := two_le_orbF_card hcon z
      omega
    · exact ⟨y, h3⟩
  · exact ⟨0, h⟩
  · exfalso
    obtain ⟨z, hz⟩ : ((orbF H' (0 : Fin 5))ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin, h]
      norm_num
    have hz0 : z ∉ MulAction.orbit H' (0 : Fin 5) :=
      fun hh => (Finset.mem_compl.mp hz) (mem_orbF.mpr hh)
    have hle : (orbF H' z).card ≤ 1 := by
      have h1 := Finset.card_le_card (orbF_subset_compl hz0)
      rw [Finset.card_compl, Fintype.card_fin, h] at h1
      omega
    have h2 := two_le_orbF_card hcon z
    omega

theorem exists_fixed_point {H' : Subgroup P} (hH' : H' ≤ A5) (hcard : Nat.card H' = 12) :
    ∃ x : Fin 5, ∀ h : H', h • x = x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx3⟩ := exists_orbF_card_three hcard hcon
  have hO3 : Fintype.card ↥(MulAction.orbit H' x) = 3 := by
    rw [← orbF_card_eq x]
    exact hx3
  have hcard' : Fintype.card ↥H' = 12 := by rwa [Nat.card_eq_fintype_card] at hcard
  have hnotinj : ¬ Function.Injective (MulAction.toPermHom H' ↥(MulAction.orbit H' x)) := by
    intro hinj
    have hle := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_perm, hO3, hcard'] at hle
    norm_num at hle
  obtain ⟨g₁, g₂, hg₁₂, hne⟩ := Function.not_injective_iff.mp hnotinj
  set z : H' := g₁⁻¹ * g₂ with hz
  have hz1 : z ≠ 1 := by
    intro hcontra
    rw [hz] at hcontra
    exact hne (inv_mul_eq_one.mp hcontra)
  have hzφ : MulAction.toPermHom H' ↥(MulAction.orbit H' x) z = 1 := by
    rw [hz, map_mul, map_inv, hg₁₂, inv_mul_cancel]
  have hfixO : ∀ w : ↥(MulAction.orbit H' x), (z : P) • (w : Fin 5) = (w : Fin 5) := by
    intro w
    have h1 : (MulAction.toPermHom H' ↥(MulAction.orbit H' x) z) w = w := by
      rw [hzφ]
      rfl
    have h2 : ((MulAction.toPermHom H' ↥(MulAction.orbit H' x) z) w : Fin 5)
        = (z : P) • (w : Fin 5) := rfl
    rw [← h2, h1]
  have hfixO' : ∀ w : Fin 5, w ∈ MulAction.orbit H' x → (z : P) w = w := by
    intro w hw
    simpa using hfixO ⟨w, hw⟩
  have hfix3 : 3 ≤ (univ.filter fun i : Fin 5 => (z : P) i = i).card := by
    rw [← hx3]
    refine Finset.card_le_card ?_
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfixO' w (mem_orbF.mp hw)⟩
  have hzA5 : (z : P) ∈ A5fin := CertPP12Inputs.mem_A5fin.mpr (hH' z.2)
  exact hz1 (Subtype.ext (fix_three_eq_one (z : P) hzA5 hfix3))

theorem exists_conj_eq_H {H' : Subgroup P} (hH' : H' ≤ A5) (hcard : Nat.card H' = 12) :
    ∃ g ∈ A5, conjSub g H' = H := by
  obtain ⟨x, hx⟩ := exists_fixed_point hH' hcard
  obtain ⟨g, hgA5, hgx⟩ := exists_smul_eq_four x
  have hgx' : g x = 4 := hgx
  have hx' : ∀ h : H', (h : P) x = x := fun h => hx h
  refine ⟨g, hgA5, ?_⟩
  have hKle : conjSub g H' ≤ H := by
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hkA5 : conjHom g k ∈ A5 := by
      rw [conjHom_apply]
      exact A5.mul_mem (A5.mul_mem hgA5 (hH' hk)) (A5.inv_mem hgA5)
    have hfix4 : conjHom g k 4 = 4 := by
      have hgk : g⁻¹ 4 = x := by
        rw [← hgx']
        simp
      rw [conjHom_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgk, hx' ⟨k, hk⟩, hgx']
    exact CertPP12Inputs.mem_H_of_mem_Hset
      (fix_four_mem_Hset _ (CertPP12Inputs.mem_A5fin.mpr hkA5) hfix4)
  have hcardK : Nat.card ↥(conjSub g H') = 12 := by
    rw [Subgroup.card_map_of_injective (conjHom_injective g), hcard]
  exact Subgroup.eq_of_le_of_card_ge hKle (by rw [hcardK, CertPP12Inputs.H_card])

namespace CosetSystemFor
variable {H' : Subgroup P} {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def toExplicit (S : CosetSystemFor H' ι) (hH' : H' ≤ A5)
    (hcard : Nat.card H' = 12) : CertPP12Inputs.CosetSystem ι :=
  let g := Classical.choose (exists_conj_eq_H hH' hcard)
  let hg := Classical.choose_spec (exists_conj_eq_H hH' hcard)
  (hg.2 ▸ S.conj g hg.1).toCoset

end CosetSystemFor

theorem anchor_twelve_closed_all {ι : Type*} [Fintype ι] [DecidableEq ι] (H' : Subgroup P)
    (hcard : Nat.card H' = 12) (S : CosetSystemFor H' ι) : False :=
  CertPP12Inputs.anchor_twelve_closed (S.toExplicit S.anchor_le hcard)

theorem anchor_twelve_closed_alt5 {ι : Type*} [Fintype ι] [DecidableEq ι] (H'' : Subgroup A5)
    (hcard : Nat.card H'' = 12) (S : CosetSystemFor (Subgroup.map A5.subtype H'') ι) : False :=
  anchor_twelve_closed_all _ (by
    rw [Subgroup.card_map_of_injective A5.subtype_injective]
    exact hcard) S

theorem anchor_twelve_closed_H {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : CosetSystemFor H ι) : False :=
  CertPP12Inputs.anchor_twelve_closed S.toCoset

end CertPP12All
end HSC
