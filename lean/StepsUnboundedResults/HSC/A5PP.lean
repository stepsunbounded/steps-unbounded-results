/-
HSC/A5PP.lean

R004 unconditional on the Lean side.

`StepsUnboundedResults.HSC.CertPPAlt5` proves `Cert-PP(A₅) ⟹ PP(A₅)` from the four anchor
refutations given the capacity sieve, and `PP ⟹ LI_p` for every `p`.
`StepsUnboundedResults.HSC.A5Sieve` supplies the sieve.
-/
import StepsUnboundedResults.HSC.A5Sieve
import StepsUnboundedResults.HSC.CertPPAlt5
import StepsUnboundedResults.HSC.R004

open scoped Classical

namespace HSC
namespace A5PP

theorem pp_alt5 : PP Alt5 :=
  CertPPAlt5.pp_alt5_of_max_size (fun {_} _ _ c K i₀ hcoset hinj hmax hnopriv =>
    A5Sieve.max_size_mem c K i₀ hcoset hinj hmax hnopriv)

theorem licosets_alt5 (p : ℕ) : LICosets p Alt5 :=
  CertPPAlt5.licosets_of_pp pp_alt5 p

theorem isHS_alt5 : IsHS Alt5 :=
  isHS_of_PP pp_alt5

theorem isHS_of_pExtension_alt5 {G : Type} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] {p : ℕ} (hp : p.Prime) (hV : IsPGroup p V)
    (e : (G ⧸ V) ≃* Alt5) : IsHS G :=
  isHS_of_normal_pSubgroup_quotient_alt5 V hp hV e (licosets_alt5 p)

end A5PP
end HSC
