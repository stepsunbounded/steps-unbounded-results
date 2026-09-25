import StepsUnboundedResults.HSC.R003

namespace HSC

/-- R003 headline: every finite direct power of `A₅` satisfies Herzog–Schönheim. -/
theorem isHS_pow_Alt5 (r : ℕ) : IsHS (pow Alt5 r) :=
  isHS_of_indexSet_subset
    (indexSet_pow_subset Alt5 (fun n hn => subset_MonoidGen (a5_indexSet_subset n hn)) r)
    massBound_a5IndexSet (by norm_num)

end HSC
