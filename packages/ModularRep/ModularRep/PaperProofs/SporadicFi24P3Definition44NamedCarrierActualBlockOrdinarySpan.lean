import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
import ModularRep.PaperProofs.FiniteRowRankCertificate

/-! Specified-block spans and complete selected rows from global ordinary allocation. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.BlockwiseOrdinaryBrauerSpan
open ModularRep.BlockwiseOrdinaryBrauerSpan.GlobalOrdinaryBrauerDecompositionSource
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation

universe u v w
variable {p : ℕ} {k K X BlockIndex : Type u} {Row : Type v} {Column : Type w}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

abbrev ActualBrauerBlock (b : ActualBlock (k := k) (X := X)) :=
  {phi : IBr iota // brauerBlock iota hinj blocks phi = b}

abbrev actualBlockBrauerFunction (b : ActualBlock (k := k) (X := X)) :
    ActualBrauerBlock iota hinj blocks b → PrimeRegularFunction K X p :=
  fun phi => phi.1.1.toFun

abbrev actualBlockBrauerSpan (b : ActualBlock (k := k) (X := X)) :
    Submodule K (PrimeRegularFunction K X p) :=
  Submodule.span K (Set.range (actualBlockBrauerFunction iota hinj blocks b))

theorem actualBlockBrauerFunction_linearIndependent
    (b : ActualBlock (k := k) (X := X)) :
    LinearIndependent K (actualBlockBrauerFunction iota hinj blocks b) := by
  change LinearIndependent K ((fun phi : IBr iota => phi.1.toFun) ∘
    (fun phi : ActualBrauerBlock iota hinj blocks b => phi.1))
  exact (irreducibleBrauerCharacters_linearIndependent iota).comp
    (fun phi : ActualBrauerBlock iota hinj blocks b => phi.1) Subtype.val_injective

def actualBlockBrauerBasis (b : ActualBlock (k := k) (X := X)) :
    Module.Basis (ActualBrauerBlock iota hinj blocks b) K
      (actualBlockBrauerSpan iota hinj blocks b) :=
  Module.Basis.span (actualBlockBrauerFunction_linearIndependent iota hinj blocks b)

@[simp]
theorem coe_actualBlockBrauerBasis_apply
    (b : ActualBlock (k := k) (X := X)) (phi : ActualBrauerBlock iota hinj blocks b) :
    ((actualBlockBrauerBasis iota hinj blocks b phi :
      actualBlockBrauerSpan iota hinj blocks b) : PrimeRegularFunction K X p) = phi.1.1.toFun := by
  simp [actualBlockBrauerBasis]

theorem actualBlockBrauer_card_eq_finrank (b : ActualBlock (k := k) (X := X)) :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} =
      Module.finrank K (actualBlockBrauerSpan iota hinj blocks b) :=
  (Module.finrank_eq_nat_card_basis (actualBlockBrauerBasis iota hinj blocks b)).symm

theorem actualBlockOrdinaryRows_span
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (b : ActualBlock (k := k) (X := X))
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi) :
    Submodule.span K (Set.range fun r => actualOrdinaryRestriction (p := p) (selected r)) =
      actualBlockBrauerSpan iota hinj blocks b := by
  calc
    _ = blockSpan (K := K) (actualOrdinaryRestriction (p := p) (K := K) (X := X))
        D.ordinaryBlock b :=
      selected_span_eq_blockSpan (actualOrdinaryRestriction (p := p) (K := K) (X := X))
        D.ordinaryBlock b selected hcomplete
    _ = blockSpan (K := K) (actualBrauerFunction iota) (brauerBlock iota hinj blocks) b :=
      blockwise_span_eq D.decomposition (irreducibleBrauerCharacters_linearIndependent iota) b
    _ = _ := rfl

def actualBlockBrauerEvaluationEquiv
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (b : ActualBlock (k := k) (X := X))
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c) :
    actualBlockBrauerSpan iota hinj blocks b ≃ₗ[K]
      Submodule.span K (Set.range matrix) :=
  (LinearEquiv.ofEq _ _
    (actualBlockOrdinaryRows_span iota hinj blocks D b selected hcomplete).symm).trans
      (classFunctionSpanEvaluationEquiv A
        (fun r => ordinaryRestrictionClassFunction (p := p) (selected r)) matrix hvalues)

@[simp]
theorem actualBlockBrauerEvaluationEquiv_apply
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (b : ActualBlock (k := k) (X := X))
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c)
    (f : actualBlockBrauerSpan iota hinj blocks b) :
    ((actualBlockBrauerEvaluationEquiv iota hinj blocks D b selected hcomplete A matrix hvalues f :
      Submodule.span K (Set.range matrix)) : Column → K) =
        fun c => f.1 (A.representative c) := rfl

theorem actualBlock_card_of_certificate
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (b : ActualBlock (k := k) (X := X))
    (selected : Row → OrdinaryIrreducibleCharacter.Irr K X)
    (hcomplete : ∀ chi, D.ordinaryBlock chi = b ↔ ∃ r, selected r = chi)
    (A : PrimeRegularRepresentativeCover p X Column)
    (matrix : Row → Column → K)
    (hvalues : ∀ r c, (selected r).1 (A.representative c).1 = matrix r c)
    (n : ℕ) (certificate : FiniteRowRankCertificate K matrix n) :
    Nat.card {phi : IBr iota // brauerBlock iota hinj blocks phi = b} = n :=
  (actualBlockBrauer_card_eq_finrank iota hinj blocks b).trans
    ((actualBlockBrauerEvaluationEquiv iota hinj blocks D b selected hcomplete
      A matrix hvalues).finrank_eq.trans certificate.rows_finrank)

local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem blockRows_complete_of_trivial_allocation
    (D : ActualOrdinaryDecomposition iota hinj blocks)
    (C : ActualSectorOrdinaryRows iota hinj blocks D
      (1 : CentralSector (k := k) (X := X)) (Fin 108))
    (trivialRoles : Fin 5 ≃
      {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
    (exportedBlockLabel : Fin 108 → Fin 5)
    (allocation : ∀ r, D.ordinaryBlock (C.character r) =
      (trivialRoles (exportedBlockLabel r)).1)
    (rowPosition : Fin 4 → Fin 108)
    (rowFibre : ∀ r, exportedBlockLabel r = 1 ↔ ∃ i, rowPosition i = r) :
    ∀ chi, D.ordinaryBlock chi = (trivialRoles 1).1 ↔
      ∃ i : Fin 4, C.character (rowPosition i) = chi := by
  intro chi
  constructor
  · intro hchi
    have hsector : blockSector (D.ordinaryBlock chi) = 1 := by
      rw [hchi]
      exact (trivialRoles 1).2
    obtain ⟨r, hr⟩ := (C.complete chi).1 hsector
    have hphysical : (trivialRoles (exportedBlockLabel r)).1 = (trivialRoles 1).1 :=
      (allocation r).symm.trans ((congrArg D.ordinaryBlock hr).trans hchi)
    have hlabel : exportedBlockLabel r = 1 :=
      trivialRoles.injective (Subtype.ext hphysical)
    obtain ⟨i, hi⟩ := (rowFibre r).1 hlabel
    exact ⟨i, (congrArg C.character hi).trans hr⟩
  · rintro ⟨i, rfl⟩
    exact (allocation (rowPosition i)).trans
      (congrArg (fun j : Fin 5 => (trivialRoles j).1)
        ((rowFibre (rowPosition i)).2 ⟨i, rfl⟩))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualBlockOrdinarySpan


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
