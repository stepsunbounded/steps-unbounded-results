import StepsUnboundedResults.HSC.Defs
import StepsUnboundedResults.HSC.Criterion
import StepsUnboundedResults.HSC.Lifting
import StepsUnboundedResults.HSC.PrivatePoints
import StepsUnboundedResults.HSC.SolvableReduction
import StepsUnboundedResults.HSC.Trace
import StepsUnboundedResults.HSC.Gap

/-!
# R006 — private points imply Herzog–Schönheim, and the solvable case reduces to `LI_p`

The three propositions and the reduction:

* `HSC.isHS_of_PP` — the private-point property implies HS, with no lifting step;
* `HSC.Hp_of_PP` and `HSC.Hp_of_licosets` — private points imply the all-ones hypothesis
  `H_p`, and linear independence implies it;
* `HSC.Hp_of_isPGroup` — `H_p` holds for every finite `p`-group (the proved case of
  Lemma A);
* `HSC.top_row_capacity`, `HSC.top_row_sieve_iff` — the top row of the capacity sieve is
  the criterion `𝒥(G) < 2`;
* `HSC.isHS_of_isSolvable_of_licosets`, `HSC.isHS_of_forall_licosets` — if every finite
  solvable group satisfies `LI_p`, then every finite solvable group is HS.

The hypothesis itself for arbitrary solvable groups is not a theorem: it is the range the
GAP search verifies (and the case the record's Lemmas A and B would close), so the
solvable corollary remains conditional here exactly as on the page.

Corresponds to <https://stepsunbounded.com/results/R006/>.
-/
