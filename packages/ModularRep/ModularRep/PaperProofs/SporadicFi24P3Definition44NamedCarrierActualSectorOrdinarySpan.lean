import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import ModularRep.BlockwiseOrdinaryBrauerSpan
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.RegularRestriction
import ModularRep.BrauerCharacterLinearIndependence
import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase

/-!
# Actual central-sector ordinary and Brauer spans

Global ordinary decomposition, specified block support and complete
ordinary-row coverage imply the actual sector span equality. A canonical
Brauer basis identifies its dimension with the actual sector cardinality.
No matrix, numerical rank, action or correspondence source occurs here.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.BlockwiseOrdinaryBrauerSpan
open ModularRep.BlockwiseOrdinaryBrauerSpan.GlobalOrdinaryBrauerDecompositionSource
open SporadicFi24CentralSectorAssemblyLemma56Actual

universe u v
variable {p : ℕ} {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

abbrev actualOrdinaryRestriction (chi : OrdinaryIrreducibleCharacter.Irr K X) :
    PrimeRegularFunction K X p := restrictToPrimeRegular p chi.1

abbrev actualBrauerFunction (phi : IBr iota) : PrimeRegularFunction K X p := phi.1.toFun

/-- Global ordinary decomposition and support on specified primitive blocks. -/
structure ActualOrdinaryDecomposition : Type u where
  ordinaryBlock : OrdinaryIrreducibleCharacter.Irr K X → ActualBlock (k := k) (X := X)
  decomposition : GlobalOrdinaryBrauerDecompositionSource (K := K)
    (actualOrdinaryRestriction (p := p) (K := K) (X := X))
    (actualBrauerFunction iota) ordinaryBlock (brauerBlock iota hinj blocks)

local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

def ActualOrdinaryDecomposition.sectorDecomposition
    (D : ActualOrdinaryDecomposition iota hinj blocks) :
    GlobalOrdinaryBrauerDecompositionSource (K := K)
      (actualOrdinaryRestriction (p := p) (K := K) (X := X))
      (actualBrauerFunction iota) (fun chi => blockSector (D.ordinaryBlock chi))
      (brauerSector iota hinj blocks) where
  columns := D.decomposition.columns
  ordinary_eq_decomposition := D.decomposition.ordinary_eq_decomposition
  column_support := by
    intro chi phi h
    exact congrArg (blockSector (k := k) (X := X)) (D.decomposition.column_support chi phi h)
  brauer_eq_ordinary_combination := D.decomposition.brauer_eq_ordinary_combination

abbrev ActualBrauerSector (nu : CentralSector (k := k) (X := X)) :=
  {phi : IBr iota // brauerSector iota hinj blocks phi = nu}

abbrev actualSectorBrauerFunction (nu : CentralSector (k := k) (X := X)) :
    ActualBrauerSector iota hinj blocks nu → PrimeRegularFunction K X p :=
  fun phi => phi.1.1.toFun

abbrev actualSectorBrauerSpan (nu : CentralSector (k := k) (X := X)) :
    Submodule K (PrimeRegularFunction K X p) :=
  Submodule.span K (Set.range (actualSectorBrauerFunction iota hinj blocks nu))

theorem actualSectorBrauerFunction_linearIndependent (nu : CentralSector (k := k) (X := X)) :
    LinearIndependent K (actualSectorBrauerFunction iota hinj blocks nu) := by
  change LinearIndependent K ((fun phi : IBr iota => phi.1.toFun) ∘
    (fun phi : ActualBrauerSector iota hinj blocks nu => phi.1))
  exact (irreducibleBrauerCharacters_linearIndependent iota).comp
    (fun phi : ActualBrauerSector iota hinj blocks nu => phi.1) Subtype.val_injective

def actualSectorBrauerBasis (nu : CentralSector (k := k) (X := X)) :
    Module.Basis (ActualBrauerSector iota hinj blocks nu) K
      (actualSectorBrauerSpan iota hinj blocks nu) :=
  Module.Basis.span (actualSectorBrauerFunction_linearIndependent iota hinj blocks nu)

@[simp]
theorem coe_actualSectorBrauerBasis_apply
    (nu : CentralSector (k := k) (X := X)) (phi : ActualBrauerSector iota hinj blocks nu) :
    ((actualSectorBrauerBasis iota hinj blocks nu phi :
      actualSectorBrauerSpan iota hinj blocks nu) : PrimeRegularFunction K X p) = phi.1.1.toFun := by
  simp [actualSectorBrauerBasis]

theorem actualSectorBrauer_card_eq_finrank (nu : CentralSector (k := k) (X := X)) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} =
      Module.finrank K (actualSectorBrauerSpan iota hinj blocks nu) :=
  (Module.finrank_eq_nat_card_basis (actualSectorBrauerBasis iota hinj blocks nu)).symm

/-- Complete actual ordinary coverage; repeated rows are permitted. -/
structure ActualSectorOrdinaryRows
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : CentralSector (k := k) (X := X)) (Row : Type v) : Type (max u v) where
  character : Row → OrdinaryIrreducibleCharacter.Irr K X
  complete : ∀ chi, blockSector (D.ordinaryBlock chi) = nu ↔ ∃ r, character r = chi

abbrev actualSectorOrdinaryRestrictionRows
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : CentralSector (k := k) (X := X)) {Row : Type v}
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row) : Row → PrimeRegularFunction K X p :=
  fun r => actualOrdinaryRestriction (p := p) (C.character r)

abbrev actualSectorOrdinarySpan
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : CentralSector (k := k) (X := X)) {Row : Type v}
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row) :
    Submodule K (PrimeRegularFunction K X p) :=
  Submodule.span K (Set.range (actualSectorOrdinaryRestrictionRows iota hinj blocks D nu C))

theorem actualSectorOrdinaryRows_span
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : CentralSector (k := k) (X := X)) {Row : Type v}
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row) :
    actualSectorOrdinarySpan iota hinj blocks D nu C = actualSectorBrauerSpan iota hinj blocks nu := by
  calc
    actualSectorOrdinarySpan iota hinj blocks D nu C =
        blockSpan (K := K) (actualOrdinaryRestriction (p := p) (K := K) (X := X))
          (fun chi => blockSector (D.ordinaryBlock chi)) nu :=
      selected_span_eq_blockSpan (actualOrdinaryRestriction (p := p) (K := K) (X := X))
        (fun chi => blockSector (D.ordinaryBlock chi)) nu C.character C.complete
    _ = blockSpan (K := K) (actualBrauerFunction iota) (brauerSector iota hinj blocks) nu :=
      blockwise_span_eq (ActualOrdinaryDecomposition.sectorDecomposition iota hinj blocks D)
        (irreducibleBrauerCharacters_linearIndependent iota) nu
    _ = actualSectorBrauerSpan iota hinj blocks nu := rfl

theorem actualSector_card_eq_ordinarySpan_finrank
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (nu : CentralSector (k := k) (X := X)) {Row : Type v}
    (C : ActualSectorOrdinaryRows iota hinj blocks D nu Row) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} =
      Module.finrank K (actualSectorOrdinarySpan iota hinj blocks D nu C) := by
  rw [actualSectorOrdinaryRows_span iota hinj blocks D nu C]
  exact actualSectorBrauer_card_eq_finrank iota hinj blocks nu

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
