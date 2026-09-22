import ModularRep.PaperProofs.TypeBQ3B45CentralDescent
import ModularRep.PaperProofs.TypeBQ3B45PhysicalInputs
import ModularRep.PaperProofs.TypeBQ3B45CriterionAssembly

/-!
The B4/B5 manuscript deduction on the actual triple quotient X and matrix G3.
The literal table row determines the supported singleton, the common central
quotient, its primitive dominated block and complete Brauer deflation. A
selected ordinary defect-zero reduction and scoped standard specified facts
then construct the unique actual weight class and its equivariant matching.
The complete fixed-block criterion is the output, including full actual
Brauer inertia, the same global extension used locally, and every intermediate
block equation. No matching, ClauseIII packet or criterion is an input.

This is a source-conditional endpoint. The specified table dictionary, sectors,
ordinary reduction, scoped Navarro and block-selector facts remain explicit;
compilation does not authenticate their representation theoretic inhabitants.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B45CriterionApplication

open ModularRep CharacterWeight FDRepSimpleClassKZero
open Formalisation.ComputationArithmetic
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBExceptionalQ3Proposition416Actual TypeBQ3PrincipalCriterionDominatedBlock
open TypeBLocalReductionInstantiation TypeBQ3B45CentralDescent
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicCompleteCollapseLemma52Actual (GlobalDefectZeroCharacter)
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable (matrixSource : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
  {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- For either named defect-zero block, construct its actual central descent
and the complete fixed-block criterion from the displayed subordinate facts.
The only ambient catalogue and seed are at the one derived reference character;
all other supported characters are proved equal to it before those are reused. -/
theorem actualTripleCover_B4_B5_criterion :
  letI : Finite X := finite_X matrixSource
  ∀ (root : PrimeRegularRootEmbedding 2 k K X)
    (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys root)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card X)]
    (d : Q3Block → k[X]) (blocks : BlockIdempotentDecomposition d)
    (dictionary : LiteralBrauerOutputMap root)
    (complete : Function.Surjective dictionary.character)
    (compatible : BrauerBlockFibreCompatible root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks dictionary)
    (i : Block45)
    (sectorOne : centralSector matrixSource freeSource (upBlock blocks i) = 1)
    (R : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (primitive : CentralPrimeToPrimitiveImageSource (k := k)
      (q matrixSource freeSource) (q_surjective matrixSource freeSource) root.prime
      (q_kernel_le_center matrixSource freeSource) (q_kernel_primeToTwo matrixSource freeSource)),
    let rootDown := downRoot root matrixSource freeSource
    letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
    let calibrationDown :=
      TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
    ∃ (b : LiteralPrimitiveBlock k G3)
      (reference : BrauerFibre rootDown b)
      (deflation : BrauerFibre root (upBlock blocks i) ≃ BrauerFibre rootDown b),
      algebraMapOf (q matrixSource freeSource) (d i.val) = b.val ∧
      PrimeRegularClassFunction.pullback (q matrixSource freeSource) reference.val.val =
        (dictionary.character (row i)).val ∧
      (∀ phi : BrauerFibre root (upBlock blocks i),
        PrimeRegularClassFunction.pullback (q matrixSource freeSource)
          (deflation phi).val.val = phi.val.val) ∧
      (∀ phi : BrauerFibre root (upBlock blocks i),
        TypeBBSCentralCharacterQuotient.centralKernel root phi.val =
          (q matrixSource freeSource).ker) ∧
      (∀ phi : BrauerFibre root (upBlock blocks i),
        ∃ e : TypeBQ3PrincipalExtensionCentralQuotient.CentralQuotient root
            (upBlock blocks i) phi ≃* G3,
          (∀ x : X, e (QuotientGroup.mk'
            (TypeBBSCentralCharacterQuotient.centralKernel root phi.val) x) =
              q matrixSource freeSource x) ∧
          (TypeBQ3PrincipalExtensionCentralQuotient.quotientBrauer root
            (upBlock blocks i) phi).val =
            PrimeRegularClassFunction.pullback e.toMonoidHom (deflation phi).val.val) ∧
      Nat.card (BrauerFibre rootDown b) = 1 ∧
      (∀ phi : BrauerFibre rootDown b, phi = reference) ∧
      ∀ (ordinary : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3))
        (reduction : IsBrauerReduction rootDown ordinary.val reference.val)
        (regular_unique : ∀ ordinary' : GlobalDefectZeroCharacter (p := 2) (K := K) (X := G3),
          (∀ g : PrimeRegularElement (G := G3) 2,
            ordinary'.val g.val = ordinary.val g.val) → ordinary' = ordinary)
        (ambientAt : R.operations.ambientBlockData.blockIdempotent b = b.val)
        (rawTrivial : ∀ W : CharacterWeight 2 K G3,
          R.operations.rawWeightBlock W = b → W.subgroup = ⊥)
        (physical : TypeBQ3B45PhysicalInputs.ScopedInputs
          Msys rootDown calibrationDown matrixSource R b ordinary)
        (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
        (indexTwo : (G (ZMod 3)).index = 2)
        (ambientBlocks : PhysicalBlocks k (ActualAutAmbient rootDown reference.val))
        (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
        (ambientSeed : PrimeRegularRootEmbedding 2 k K
          (ActualAutAmbient rootDown reference.val))
        (fieldSource : SpathCoefficientField 2 k Nat.prime_two),
        ∃ omega : BrauerFibre rootDown b ≃ R.Fibre b,
          TypeBQ3B2CriterionAssembly.CompleteClauses rootDown R b omega := by
  letI : Finite X := finite_X matrixSource
  intro root Msys calibration ordinaryRoots d blocks dictionary complete compatible
    i sectorOne R primitive
  letI : Fintype (LiteralPrimitiveBlock k X) := TypeBLiteralBlockReindex.literalBlockFintype blocks
  letI : Fintype (LiteralPrimitiveBlock k G3) := R.operations.ambientBlockData.fintypeBlock
  let DB := TypeBLiteralBlockReindex.literalBlocks R.operations.ambientBlockData.blocks
  let rootDown := downRoot root matrixSource freeSource
  letI := TypeBQ3B2RootDescent.downOrdinaryRoots (K := K) matrixSource freeSource
  let calibrationDown :=
    TypeBQ3B2RootDescent.downRoot_residue matrixSource freeSource root Msys calibration
  let b := downBlock root blocks dictionary compatible matrixSource freeSource i sectorOne DB primitive
  let reference := downReference root blocks dictionary compatible matrixSource freeSource
    i sectorOne DB primitive
  let deflation := downDeflation root blocks dictionary compatible matrixSource freeSource
    i sectorOne DB primitive
  have unique (phi : BrauerFibre rootDown b) : phi = reference :=
    downReference_unique root blocks dictionary compatible matrixSource freeSource
      i sectorOne DB primitive complete phi
  refine ⟨b, reference, deflation, rfl, ?_, ?_, ?_, ?_, ?_, unique, ?_⟩
  · exact downReference_pullback root blocks dictionary compatible matrixSource freeSource
      i sectorOne DB primitive
  · exact downDeflation_pullback root blocks dictionary compatible matrixSource freeSource
      i sectorOne DB primitive
  · exact centralKernel_eq_qker root blocks matrixSource freeSource i sectorOne
  · intro phi
    exact ⟨ownQuotientEquiv root blocks matrixSource freeSource i sectorOne phi,
      ownQuotientEquiv_mk root blocks matrixSource freeSource i sectorOne phi,
      ownQuotientBrauer_eq_pullback root blocks dictionary compatible matrixSource freeSource
        i sectorOne DB primitive phi⟩
  · exact downCard root blocks dictionary compatible matrixSource freeSource
      i sectorOne DB primitive complete
  · intro ordinary reduction regular_unique ambientAt rawTrivial physical
      automorphisms indexTwo ambientBlocks principle ambientSeed fieldSource
    have uniqueValues (psi : IBr rootDown) (supported : Supported rootDown b psi) :
        psi = reference.val := congrArg Subtype.val (unique ⟨psi, supported⟩)
    let source := TypeBQ3B45PhysicalInputs.fixedBlockSource physical reference.val
      reduction regular_unique reference.property uniqueValues ambientAt rawTrivial
    refine ⟨TypeBQ3B45DefectZeroMatching.fixedBlockEquiv source,
      TypeBQ3B45CriterionAssembly.of_fixedBlockSource rootDown R b matrixSource
        automorphisms indexTwo reference.val source ?_ principle ?_ fieldSource⟩
    · intro phi
      rw [unique phi]
      exact ambientBlocks
    · intro phi
      rw [unique phi]
      exact ambientSeed

end ModularRep.PaperProofs.TypeBQ3B45CriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
