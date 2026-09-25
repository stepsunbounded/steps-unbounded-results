/-
HSC/Headline.lean

The `A₅` headline results, depending on the three independent layers:

* `HSC.A5Index.a5_indexSet_subset`  : `I(A₅) ⊆ {1,5,6,10,12,15,20,30,60}`;
* `HSC.A5Monoid.massBound_a5IndexSet` : `Λ({A₅}) = 5611/5852 < 1`;
* `HSC.Assembly.isHS_of_builtFrom` / `HSC.Products.indexSet_pow_subset`.

Nothing here is conditional: the two inputs above are proofs, not hypotheses.
-/
import StepsUnboundedResults.HSC.Assembly
import StepsUnboundedResults.HSC.Products
import StepsUnboundedResults.HSC.CompFactors
import StepsUnboundedResults.HSC.A5Index
import StepsUnboundedResults.HSC.A5Monoid
import StepsUnboundedResults.HSC.UniformBound
import Mathlib.Tactic

open scoped Classical

universe u

namespace HSC

theorem a5_indexSet_subset_monoidGen :
    ∀ n ∈ indexSet Alt5, n ∈ MonoidGen a5IndexSet :=
  fun n hn => subset_MonoidGen (a5_indexSet_subset n hn)

theorem A5_builtFrom_isHS {G : Type} [Group G] [Finite G] (hb : BuiltFrom Alt5 G) : IsHS G :=
  isHS_of_builtFrom a5_indexSet_subset_monoidGen massBound_a5IndexSet (by norm_num) hb

theorem isHS_Alt5 : IsHS Alt5 :=
  A5_builtFrom_isHS (BuiltFrom.iso Alt5 (MulEquiv.refl Alt5))

theorem isHS_pow_Alt5 (r : ℕ) : IsHS (pow Alt5 r) :=
  isHS_of_indexSet_subset
    (indexSet_pow_subset Alt5 (fun n hn => subset_MonoidGen (a5_indexSet_subset n hn)) r)
    massBound_a5IndexSet (by norm_num)

theorem HS_of_compFactors_Alt5 {G : Type} [Group G] [Finite G] (h : CompFactorsIso Alt5 G) :
    IsHS G :=
  isHS_of_compFactors a5_indexSet_subset_monoidGen massBound_a5IndexSet (by norm_num) h

theorem isHS_of_compFactors_of_euler {S : Type} [Group S] [Finite S]
    (h : (∏ a ∈ (indexSet S).filter (fun a => 1 < a), ((1 : ℚ) - 1 / a)⁻¹) < 2)
    {G : Type} [Group G] [Finite G] (hc : CompFactorsIso S G) : IsHS G :=
  isHS_of_compFactors (A := indexSet S) (fun _ hn => subset_MonoidGen hn)
    (massBound_euler (indexSet S)) (massBound_euler_of_lt_two (indexSet S) h).2 hc

theorem isHS_Alt5_compFactors : IsHS Alt5 :=
  HS_of_compFactors_Alt5 compFactorsIso_alt5_self

end HSC
