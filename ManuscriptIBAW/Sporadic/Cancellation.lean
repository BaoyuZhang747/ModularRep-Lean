import Formalisation.BlockCancellation

/-!
# Lemma 5.3

Finite sets with involutions are decomposed into the distinguished block
orbit and the union of the other block orbits. The proof cancels total
cardinalities and numbers of fixed points. On an exchanged pair of blocks,
it chooses a map on one fibre and defines the other by the involutions. The
resulting bijection preserves each block label.

If the remaining block orbit is a singleton, every bijection of its
underlying sets preserves that label. The theorem for an exchanged pair of
blocks includes preservation of both labels explicitly.
-/

namespace ManuscriptIBAW.Sporadic.Cancellation

export Formalisation.BlockCancellation
  (Intertwines sumPerm sigmaPerm cancel_equivariant_equiv
   cancel_equivariant_equiv_of_parts exchangedPerm
   exchangedBlockOrbitEquiv exchangedBlockOrbitEquiv_intertwines
   exchangedBlockOrbitEquiv_preserves_blocks cancel_exchanged_blocks_preserving)

end ManuscriptIBAW.Sporadic.Cancellation

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
