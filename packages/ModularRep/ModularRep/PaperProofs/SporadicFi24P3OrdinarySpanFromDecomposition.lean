import ModularRep.BlockwiseOrdinaryBrauerSpan
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.RegularRestriction
import ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction

/-!
# Fi24 p=3 ordinary span from decomposition

This adapter constructs BrauerRestrictionSpaceBinding and derives its
span_eq_literal field. Its external E1/E3 inputs are global
decomposition/block data, six-character coverage, and literal row
identification; Brauer-character linear independence is an existing kernel
fact. The equality is therefore not an additional source input to this
adapter.

The source records contain no rank, fixed-count, action, equivalence, or
cancellation conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3OrdinarySpanFromDecomposition

open Formalisation
open ModularRep.BlockwiseOrdinaryBrauerSpan
open ModularRep.BlockwiseOrdinaryBrauerSpan.GlobalOrdinaryBrauerDecompositionSource
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3LiteralSpanBindingConstruction

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

/-- The actual ordinary character function restricted to the 3-regular
carrier. -/
abbrev fi24P3OrdinaryRestriction
    (chi : OrdinaryIrreducibleCharacter.Irr K X) :
    PrimeRegularFunction K X 3 :=
  restrictToPrimeRegular 3 chi.1

/-- The actual function underlying a global irreducible Brauer character. -/
abbrev fi24P3BrauerFunction (phi : IBr iota) :
    PrimeRegularFunction K X 3 :=
  phi.1.toFun

/-- E1 decomposition and block data for all actual ordinary and Brauer
irreducible characters. The third field is the universal Brauer-to-ordinary
spanning law supplied by Navarro Corollary (2.16). -/
structure Fi24P3OrdinaryDecompositionSource : Type u where
  ordinaryBlock : OrdinaryIrreducibleCharacter.Irr K X →
    ActualBlock (k := k) (X := X)
  decomposition : GlobalOrdinaryBrauerDecompositionSource
    (K := K)
    (fi24P3OrdinaryRestriction (K := K) (X := X))
    (fi24P3BrauerFunction iota)
    ordinaryBlock
    (brauerBlock iota hinj blocks)

/-- Separate E1/E3 enumeration boundary: the selected six ordinary characters
cover precisely the ordinary characters with the selected literal block. -/
structure Fi24P3SixOrdinaryBlockCoverage
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : Fi24P3OrdinaryDecompositionSource iota hinj blocks) : Type u where
  sixOrdinary : Fin 6 → OrdinaryIrreducibleCharacter.Irr K X
  six_complete : ∀ chi,
    D.ordinaryBlock chi = S.nonprincipalBlock ↔
      ∃ i, sixOrdinary i = chi

/-- Separate E1/E3 literal-table boundary.  It identifies the displayed six
raw prime regular functions with restrictions of the already selected ordinary
characters, without asserting anything about their span. -/
structure Fi24P3LiteralRowIdentification
    {S : Fi24ThreeBlockSource (k := k) (X := X)}
    {D : Fi24P3OrdinaryDecompositionSource iota hinj blocks}
    (C : Fi24P3SixOrdinaryBlockCoverage iota hinj blocks S D) : Type u where
  rows : Fin 6 → PrimeRegularFunction K X 3
  row_eq_restriction : ∀ i,
    rows i =
      fi24P3OrdinaryRestriction (K := K) (X := X) (C.sixOrdinary i)

/-- Construct the existing literal B1 span binding.  The equality is derived,
not received: six-row completeness gives the ordinary block span, global
decomposition plus support gives the Brauer block span, and the last carrier
conversion is definitional. -/
noncomputable def Fi24P3LiteralRowIdentification.toBrauerRestrictionSpaceBinding
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (D : Fi24P3OrdinaryDecompositionSource iota hinj blocks)
    (C : Fi24P3SixOrdinaryBlockCoverage iota hinj blocks S D)
    (T : Fi24P3LiteralRowIdentification iota hinj blocks C) :
    BrauerRestrictionSpaceBinding iota hinj blocks S where
  rows := T.rows
  span_eq_literal := by
    have hrows :
        T.rows = fun i =>
          fi24P3OrdinaryRestriction (K := K) (X := X) (C.sixOrdinary i) := by
      funext i
      exact T.row_eq_restriction i
    rw [hrows]
    have hlinear :
        LinearIndependent K (fi24P3BrauerFunction (K := K) (X := X) iota) := by
      simpa only [fi24P3BrauerFunction] using
        FDRepSimpleClassKZero.irreducibleBrauerCharacters_linearIndependent iota
    calc
      Submodule.span K (Set.range (fun i =>
          fi24P3OrdinaryRestriction (K := K) (X := X) (C.sixOrdinary i))) =
          blockSpan (K := K)
            (fi24P3OrdinaryRestriction (K := K) (X := X))
            D.ordinaryBlock S.nonprincipalBlock :=
        selected_span_eq_blockSpan
          (fi24P3OrdinaryRestriction (K := K) (X := X)) D.ordinaryBlock
          S.nonprincipalBlock C.sixOrdinary C.six_complete
      _ = blockSpan (K := K) (fi24P3BrauerFunction (K := K) (X := X) iota)
          (brauerBlock iota hinj blocks) S.nonprincipalBlock :=
        blockwise_span_eq D.decomposition hlinear S.nonprincipalBlock
      _ = literalB1BrauerSpan iota hinj blocks S := rfl

end ModularRep.PaperProofs.SporadicFi24P3OrdinarySpanFromDecomposition



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
