import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessAD3Assembly

/-!
# Families in the sporadic cases with cyclic outer automorphism group

Feng–Li–Zhang, Corollary 2.13, gives the full blockwise inductive condition
from an equivariant bijection on a block of the universal prime-to-p cover
when the simple group's outer automorphism group is cyclic. A common
Definition 4.1 family additionally requires common coefficient fields and
root embeddings, defect zero normalisation and compatible choices of the
block correspondences. The exported triple cover construction gives a raw
witness from the assumptions below. The full application additionally assumes
compatible extension and intermediate block witnesses for the specified
numerical correspondence. These compatible witnesses are not derived from
the raw construction. The raw construction uses the specified character
carriers, block operations, local Brauer reductions, full automorphism
action and original cover. In the triple cover case, the centre action and
full cover map determine the prime centre and the faithful and trivial
sector alternatives. The raw extension and block conditions follow from ordinary
and modular extension, covering and block laws. The common correspondence
and its normalisation are hypotheses of this construction, proved first in
the separate applications.

The centreless result supplies the ordinary AD(3a–d) family. The application
at three combines it with block preservation, normalisation for defect zero
characters and the full local data to obtain Definition 4.1.

These results retain their hypotheses on the centre and outer automorphism
group of order one or two. The general published criterion for cyclic outer
automorphism groups and its interpretation over a common finite splitting
system remain explicit in the source crosswalk.
-/

namespace ManuscriptIBAW.Sporadic.CyclicOuterFamilies

namespace TripleCover
export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalTripleCoverFamily
  (ofNormalizedEquiv)
end TripleCover

namespace Centerless
export ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessAD3Assembly
  (CenterlessAD3Output centerless_manuscript_ad3_assembly)
end Centerless

end ManuscriptIBAW.Sporadic.CyclicOuterFamilies

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
