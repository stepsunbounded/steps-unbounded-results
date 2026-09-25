import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Lifting
import StepsUnboundedResults.HSC.LiftingTheorem
import StepsUnboundedResults.HSC.R004
import StepsUnboundedResults.HSC.A5PP

/-!
# R004 — lifting a normal `p`-subgroup

If `V ⊴ G` is a normal `p`-subgroup and the quotient `G ⧸ V` has linearly independent
coset indicators over `𝔽_p` (`LI_p`), then `G` is HS (`HSC.isHS_of_licosets_quotient`).

For `A₅`, the finite input is internal to this development: the capacity sieve and the four
anchors establish `PP(A₅)`, hence `LI_p(A₅)` for every prime `p`. Therefore the headline
`HSC.A5PP.isHS_of_pExtension_alt5` is unconditional.

Corresponds to <https://stepsunbounded.com/results/R004/>.
-/
