import StepsUnboundedResults.HSC.CertPPFour
import StepsUnboundedResults.HSC.CertPPSixTraceA
import StepsUnboundedResults.HSC.CertPPSixTraceB
import StepsUnboundedResults.HSC.CertPPSixArithmetic
import StepsUnboundedResults.HSC.CertPPSixOutside
import StepsUnboundedResults.HSC.CertPPSixAnchor

/-!
Canonical `Cert-PP` facade. The original large implementation is split by theorem dependency
boundaries so the two general anchors (`S = 4` and `S = 6`) remain independently reviewable.
-/
