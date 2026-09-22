import ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction
import ModularRep.PaperProofs.SporadicFi24SelectedOuterC2

/-!
# Adapter from the Fischer quotient binding to the selected-outer kernel source

This downstream-only experimental module connects the structural
`Fi24C2OuterQuotientBinding` to the one-field
`C2OuterInnerKernelSource` expected by the selected-outer semidirect branch.
The target module must be imported because it owns that target declaration;
keeping the adapter here prevents that dependency from flowing upstream into
the quotient-cardinality reduction.

The adapter is K and has no external source fields.  Its only target field is
definitionally the `kernel_eq_inner` field already present in the binding.
Both records are generic structural bindings intended for a separately
verified concrete Fischer instantiation; this adapter does not prove that
`Out(Fi'_24)` is isomorphic to `C2`.
It accepts no additional permutation homomorphism, kernel equality,
carrier-fixation clause, character--weight map, fibre equivalence, raw sector
family, additional output/block-preservation equality, An--Dietrich input,
Spath input, Proposition 5.7 conclusion, BAW, or iBAW conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24C2OuterInnerKernelAdapter

open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24C2OuterActionSourceReduction

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-- Repackage the kernel equality in a structural quotient binding as the
selected-outer branch's kernel source for the operational action constructed
from that binding.  No new field is required. -/
theorem c2OuterInnerKernelSource_ofQuotientBinding
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (B : Fi24C2OuterQuotientBinding S) :
    C2OuterInnerKernelSource iota S
      (c2OuterActionSource_ofQuotientBinding iota S B) where
  kernel_eq_inner := B.kernel_eq_inner

end ModularRep.PaperProofs.SporadicFi24C2OuterInnerKernelAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
