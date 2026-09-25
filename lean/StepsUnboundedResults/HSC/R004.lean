/-
HSC/R004.lean

Result **R004** (Steps Unbounded), assembled:

* the lifting theorem itself, `HSC.isHS_of_licosets_quotient`
  (`V ⊴ G` a normal `p`-subgroup, `LI_p(G ⧸ V)` ⟹ `G` is HS), lives in `HSC/LiftingTheorem.lean`;
* `LICosets` transports across group isomorphisms, so the finite input may be checked on `A₅` itself;
* hence: if `LI_p(A₅)` holds, every `p`-extension of `A₅` is HS.
-/
import StepsUnboundedResults.HSC.Lifting
import StepsUnboundedResults.HSC.LiftingTheorem
import Mathlib.Tactic

open scoped Classical

namespace HSC

theorem LICosets.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q') {p : ℕ}
    (h : LICosets p Q) : LICosets p Q' := by
  classical
  intro ι _ c H hcoset hidx
  let c' : ι → Q := fun i => e.symm (c i)
  let H' : ι → Subgroup Q := fun i => (H i).comap (e : Q →* Q')
  have hmem : ∀ (i : ι) (x : Q), x ∈ leftCoset (c' i) (H' i) ↔ e x ∈ leftCoset (c i) (H i) := by
    intro i x
    simp only [c', H', mem_leftCoset, Subgroup.mem_comap, map_mul, map_inv]
    simp
  have hpre : ∀ i, leftCoset (c' i) (H' i) = (e : Q → Q') ⁻¹' leftCoset (c i) (H i) :=
    fun i => Set.ext fun x => hmem i x
  have himg : ∀ i, e '' leftCoset (c' i) (H' i) = leftCoset (c i) (H i) := fun i => by
    rw [hpre i, Set.image_preimage_eq _ e.surjective]
  have hcoset' : ∀ i j, i ≠ j → leftCoset (c' i) (H' i) ≠ leftCoset (c' j) (H' j) := by
    intro i j hij hEq
    exact hcoset i j hij (by rw [← himg i, ← himg j, hEq])
  have hidx' : ∀ i j, i ≠ j → (H' i).index ≠ (H' j).index := by
    intro i j hij
    rw [Subgroup.index_comap_of_surjective (H i) e.surjective,
      Subgroup.index_comap_of_surjective (H j) e.surjective]
    exact hidx i j hij
  have hLI := h ι c' H' hcoset' hidx'
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro g hg
  refine hLI g ?_
  funext x
  have hx := congrFun hg (e x)
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  rw [← hx]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  by_cases hxi : x ∈ leftCoset (c' i) (H' i)
  · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem ((hmem i x).mp hxi)]
  · rw [Set.indicator_of_notMem hxi]
    have hni : e x ∉ leftCoset (c i) (H i) := fun hc => hxi ((hmem i x).mpr hc)
    rw [Set.indicator_of_notMem hni]

theorem isHS_of_normal_pSubgroup_quotient_alt5 {G : Type} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] {p : ℕ} (hp : p.Prime) (hV : IsPGroup p V)
    (e : (G ⧸ V) ≃* Alt5) (hLI : LICosets p Alt5) : IsHS G :=
  isHS_of_licosets_quotient V hp hV ((LICosets.of_mulEquiv e.symm hLI))

theorem isHS_of_normal_pSubgroup_quotient {G : Type} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] {p : ℕ} (hp : p.Prime) (hV : IsPGroup p V)
    (hLI : LICosets p (G ⧸ V)) : IsHS G :=
  isHS_of_licosets_quotient V hp hV hLI

theorem LICosets.alt5_of_mulEquiv {Q : Type*} [Group Q] (e : Q ≃* Alt5) {p : ℕ}
    (h : LICosets p Alt5) : LICosets p Q :=
  LICosets.of_mulEquiv e.symm h

end HSC
