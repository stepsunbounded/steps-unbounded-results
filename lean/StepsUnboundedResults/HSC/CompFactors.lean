/-
HSC/CompFactors.lean

Composition-factor structural lemma for the homogeneous-factor layer.
-/
import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Extension
import StepsUnboundedResults.HSC.Assembly
import Mathlib.Tactic

open scoped Classical

namespace HSC

inductive CompFactorsIso (S : Type) [Group S] : (G : Type) → [Group G] → Prop
  | trivial (G : Type) [Group G] [Subsingleton G] : CompFactorsIso S G
  | ext (G : Type) [Group G] (N : Subgroup G) [N.Normal] (hS : Nonempty ((G ⧸ N) ≃* S)) :
      CompFactorsIso S ↥N → CompFactorsIso S G

theorem indexSet_subset_monoidGen_of_compFactors {S : Type} [Group S] [Finite S] {A : Finset ℕ}
    (hS : ∀ n ∈ indexSet S, n ∈ MonoidGen A) :
    ∀ {G : Type} [Group G], CompFactorsIso S G → ∀ (hG : Finite G),
      ∀ n ∈ @indexSet G _ hG, n ∈ MonoidGen A := by
  intro G _ hc
  induction hc with
  | trivial G =>
      intro hG n hn
      haveI : Finite G := hG
      obtain ⟨-, H, rfl⟩ := mem_indexSet.mp hn
      have htop : H = ⊤ := by
        refine top_le_iff.mp ?_
        intro x _
        rw [Subsingleton.elim x 1]
        exact H.one_mem
      rw [htop, Subgroup.index_top]
      exact one_mem_MonoidGen A
  | ext G N hS' hrec ih =>
      intro hG n hn
      haveI : Finite G := hG
      haveI : Finite ↥N := inferInstance
      haveI : Finite (G ⧸ N) := inferInstance
      obtain ⟨a, ha, b, hb, rfl⟩ := index_mem_mul_indexSet N n hn
      obtain ⟨e⟩ := hS'
      exact MonoidGen.mul_mem (hS a (indexSet_subset_of_mulEquiv e ha)) (ih inferInstance b hb)

theorem isHS_of_compFactors {S : Type} [Group S] [Finite S] {A : Finset ℕ}
    (hS : ∀ n ∈ indexSet S, n ∈ MonoidGen A) {c : ℚ} (hMass : MassBound A c) (hc : c < 1)
    {G : Type} [Group G] [Finite G] (hc' : CompFactorsIso S G) : IsHS G :=
  isHS_of_indexSet_subset
    (fun n hn => indexSet_subset_monoidGen_of_compFactors hS hc' inferInstance n hn) hMass hc

theorem compFactorsIso_alt5_self : CompFactorsIso Alt5 Alt5 :=
  CompFactorsIso.ext Alt5 (⊥ : Subgroup Alt5) ⟨QuotientGroup.quotientBot⟩
    (CompFactorsIso.trivial ↥(⊥ : Subgroup Alt5))

end HSC
