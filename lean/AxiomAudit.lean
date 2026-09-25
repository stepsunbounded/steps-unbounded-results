import StepsUnboundedResults

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
