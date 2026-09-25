/-
HSC/Extension.lean

Group-theoretic extension lemmas for the Herzog–Schönheim formalization.
-/
import StepsUnboundedResults.HSC.Defs
import Mathlib.Tactic.Group

open scoped Classical

namespace HSC

theorem relIndex_sup_eq_relIndex_inf {G : Type*} [Group G] (H N : Subgroup G) [N.Normal] :
    H.relIndex (H ⊔ N) = H.relIndex N := by
  let g : ↥N → ↥(H ⊔ N) := fun x => ⟨(x : G), le_sup_right (a := H) (b := N) x.2⟩
  have hg : ∀ a b : ↥N, QuotientGroup.leftRel ((H ⊓ N).subgroupOf N) a b →
      QuotientGroup.leftRel (H.subgroupOf (H ⊔ N)) (g a) (g b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hab
    simp only [Subgroup.mem_subgroupOf, g, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hab.1
  let f : (↥N ⧸ (H ⊓ N).subgroupOf N) → (↥(H ⊔ N) ⧸ H.subgroupOf (H ⊔ N)) :=
    Quotient.map' g hg
  have hf : ∀ a : ↥N, f (Quotient.mk'' a) = Quotient.mk'' (g a) :=
    fun a => Quotient.map'_mk'' g hg a
  have hinj : Function.Injective f := by
    intro x y
    refine Quotient.inductionOn' x ?_
    intro a
    refine Quotient.inductionOn' y ?_
    intro b
    intro hxy
    rw [hf a, hf b] at hxy
    refine Quotient.sound' ?_
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have h : QuotientGroup.leftRel (H.subgroupOf (H ⊔ N)) (g a) (g b) := Quotient.exact' hxy
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h
    simp only [g, Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact ⟨by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h,
      by simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using N.mul_mem (N.inv_mem a.2) b.2⟩
  have hsurj : Function.Surjective f := by
    intro y
    refine Quotient.inductionOn' y ?_
    intro w
    obtain ⟨h, hh, n, hn, hwn⟩ : ∃ h ∈ H, ∃ n ∈ N, h * n = (w : G) := by
      have hw : (w : G) ∈ ((H ⊔ N : Subgroup G) : Set G) := w.2
      rw [Subgroup.mul_normal] at hw
      exact Set.mem_mul.mp hw
    refine ⟨Quotient.mk'' (⟨h * n * h⁻¹, (inferInstance : N.Normal).conj_mem n hn h⟩ : ↥N), ?_⟩
    rw [hf]
    refine Quotient.sound' ?_
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    simp only [g, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hwn]
    have hcalc : (h * n * h⁻¹)⁻¹ * (h * n) = h := by group
    rw [hcalc]
    exact hh
  have hmain : ((H ⊓ N).subgroupOf N).index = (H.subgroupOf (H ⊔ N)).index :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  show (H.subgroupOf (H ⊔ N)).index = (H.subgroupOf N).index
  rw [← hmain, Subgroup.inf_subgroupOf_right]

theorem index_eq_index_map_mul_relIndex {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (H : Subgroup G) :
    H.index = (H.map (QuotientGroup.mk' N)).index * (H ⊓ N).relIndex N := by
  have hker : (QuotientGroup.mk' N).ker ≤ H ⊔ N := by
    rw [QuotientGroup.ker_mk']
    exact le_sup_right
  have hmapN : N.map (QuotientGroup.mk' N) = ⊥ :=
    (Subgroup.map_eq_bot_iff N (f := QuotientGroup.mk' N)).mpr
      (le_of_eq (QuotientGroup.ker_mk' N).symm)
  have hmap : (H ⊔ N).map (QuotientGroup.mk' N) = H.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup, hmapN, sup_bot_eq]
  have hsup : (H ⊔ N).index = (H.map (QuotientGroup.mk' N)).index := by
    rw [← hmap]
    exact (Subgroup.index_map_eq (f := QuotientGroup.mk' N) (H ⊔ N)
      (QuotientGroup.mk'_surjective N) hker).symm
  calc H.index = H.relIndex (H ⊔ N) * (H ⊔ N).index :=
        (Subgroup.relIndex_mul_index le_sup_left).symm
    _ = (H ⊓ N).relIndex N * (H.map (QuotientGroup.mk' N)).index := by
        rw [hsup, relIndex_sup_eq_relIndex_inf H N, Subgroup.inf_relIndex_right]
    _ = (H.map (QuotientGroup.mk' N)).index * (H ⊓ N).relIndex N := Nat.mul_comm _ _

theorem index_mem_mul_indexSet {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    ∀ n ∈ indexSet G, ∃ a ∈ indexSet (G ⧸ N), ∃ b ∈ indexSet N, n = a * b := by
  haveI : Finite (G ⧸ N) :=
    Finite.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  intro n hn
  obtain ⟨-, H, hH⟩ := mem_indexSet.mp hn
  exact ⟨(H.map (QuotientGroup.mk' N)).index, index_mem_indexSet (G ⧸ N) _,
    (H ⊓ N).relIndex N, index_mem_indexSet N ((H ⊓ N).subgroupOf N),
    by rw [← hH, index_eq_index_map_mul_relIndex N H]⟩

theorem indexSet_subset_of_mulEquiv {G S : Type*} [Group G] [Group S] [Finite G] [Finite S]
    (e : G ≃* S) : indexSet G ⊆ indexSet S := by
  intro n hn
  obtain ⟨-, H, hH⟩ := mem_indexSet.mp hn
  have h := index_mem_indexSet S (H.map (e : G →* S))
  rw [Subgroup.index_map_equiv H e] at h
  rwa [hH] at h

end HSC
