import StepsUnboundedResults.Foundation
import StepsUnboundedResults.R002
import StepsUnboundedResults.R003
import StepsUnboundedResults.R004
import StepsUnboundedResults.R005
import StepsUnboundedResults.R006

/-!
# Axiom audit

This file is run separately by CI. Every theorem that the repository or website describes as
formally verified should appear here. The expected trust footprint is the ordinary Lean/mathlib
classical kernel footprint only; no `sorryAx`, extra explicit axioms, or `native_decide` should
appear in these headlines.
-/

#print axioms StepsUnboundedResults.sanity

-- R002
#print axioms StepsUnboundedResults.R002.primeRealModulus_autocorrelation_fermatQuotient
#print axioms StepsUnboundedResults.R002.primeRealModulus_autocorrelation_eq_iff_isWieferich

-- R003
#print axioms HSC.massBound_a5IndexSet
#print axioms HSC.isHS_pow_Alt5
#print axioms HSC.isHS_pow_Alt5_prod_pow_C5
#print axioms HSC.isHS_quotient_pow_Alt5_prod_pow_C5

-- R004
#print axioms HSC.CertPP10All.anchor_ten_closed_all
#print axioms HSC.CertPP12All.anchor_twelve_closed_all
#print axioms HSC.CertPPAlt5.certPP_raw
#print axioms HSC.A5PP.pp_alt5
#print axioms HSC.A5PP.licosets_alt5
#print axioms HSC.A5PP.isHS_of_pExtension_alt5

-- R005
#print axioms HSC.HS_of_compFactors_Alt5
#print axioms HSC.isHS_of_compFactors_of_euler
#print axioms HSC.isHS_of_compFactors_of_simpleData

-- R006
#print axioms HSC.isHS_of_isSolvable_of_licosets
#print axioms HSC.isHS_of_forall_licosets
#print axioms HSC.descent
