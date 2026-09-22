import ModularRep.PaperProofs.TypeBGroupEquivLocalBlockOperations
import ModularRep.PaperProofs.TypeBGroupEquivPhysicalGuard
import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre
import ModularRep.PaperProofs.TypeBCentrelessSelectedWeightBlockTransport

/-!
# The complete specified weight fibre on the actual principal reference quotient

All target operations are computed from the original source. The primitive
dictionary and specified guard are proved before restricting the complete
weight-class equivalence. The target block labels are the same literal
labels as the quotient Brauer decomposition.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientWeightFibre

open ModularRep CharacterWeight
open TypeBRankThreePrincipalCountBinding TypeBLocalReductionInstantiation
open TypeBFixedRootDefinitionFamily TypeBCentralKernelBlockSource
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open EvenFieldFLZ318FixedTheoremGate TypeBCliffordCarriers
open TypeBRankThreePrincipalReferenceBinding TypeBRankThreePrincipalQuotientBrauerFibre

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (G F))]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F))

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (hb : IsPrincipal b)

local notation "qGroup" => quotientGroup S SH literal literalH Msys root calibration navarro guard b hb
local notation "eQ" => quotientEquiv S SH literal literalH Msys root calibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb
local notation "rQ" => quotientRoot S SH literal literalH Msys root calibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb

/-- The actual quotient operations are computed from the original specified source. -/
def quotientOperations : LocalBlockInductionOperations
    (p := 2) (k := k) (K := K) (G := qGroup) (Block := LiteralPrimitiveBlock k (G F)) :=
  TypeBGroupEquivLocalBlockOperations.operations S.operations eQ

local notation "operationsQ" => quotientOperations S SH literal literalH Msys root calibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb

/-- Ambient allocation equals the already constructed quotient Brauer allocation. -/
theorem quotientOperations_idempotent (c : LiteralPrimitiveBlock k (G F)) :
    (operationsQ).ambientBlockData.blockIdempotent c =
      quotientIdempotent S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb c := by
  change MonoidAlgebra.domCongr k k eQ
      (S.operations.ambientBlockData.blockIdempotent c) =
    MonoidAlgebra.domCongr k k eQ c.val
  rw [literal]

/-- The quotient source uses the actual pulled-back opposite automorphism action. -/
def quotientSource :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) eQ
    LocalBlockInductionSource
      (p := 2) (k := k) (K := K) (G := qGroup) (Block := LiteralPrimitiveBlock k (G F)) := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) eQ
  exact OddTwoGroupEquivWeightBlocks.transportedSource operationsQ eQ S
    (TypeBGroupEquivLocalBlockOperations.primitiveDictionary S.operations eQ)

local notation "sourceQ" => quotientSource S SH literal literalH Msys root calibration navarro guard b
  parameters N C centreSpin fullCover simple nonabelian hb

@[simp] theorem quotientSource_operations :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) eQ
    (sourceQ).operations = operationsQ := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) eQ
  rfl

/-- No target specified guard is supplied: it follows from the constructed operations. -/
theorem quotientSource_guard :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) eQ
    GuardedBlockCompatibility rQ (sourceQ).operations := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) eQ
  exact TypeBGroupEquivPhysicalGuard.guardedBlockCompatibility
    S.operations operationsQ eQ root rQ
    (quotientRoot_lift S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) guard
    (TypeBGroupEquivLocalBlockOperations.ownNormalizerBlock_backward S.operations eQ)

/-- The exact raw image has its original ambient block label. -/
theorem rawWeightBlock_eq (W : CharacterWeight 2 K (G F)) :
    (operationsQ).rawWeightBlock (W.mapGroupEquiv eQ) =
      S.operations.rawWeightBlock W :=
  OddTwoGroupEquivWeightBlocks.rawWeightBlock_eq S.operations operationsQ eQ
    (TypeBGroupEquivLocalBlockOperations.primitiveDictionary S.operations eQ) W

/-- Both complete conjugacy class fibres are restricted along the actual group map. -/
def fibreEquiv (c : LiteralPrimitiveBlock k (G F)) :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) eQ
    S.Fibre c ≃ (sourceQ).Fibre c := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) eQ
  exact OddTwoGroupEquivWeightBlocks.fibreEquiv operationsQ eQ S
    (TypeBGroupEquivLocalBlockOperations.primitiveDictionary S.operations eQ) c

@[simp] theorem fibreEquiv_val (c : LiteralPrimitiveBlock k (G F)) (w : S.Fibre c) :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) eQ
    (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb c w).val =
      CharacterWeight.conjugacyClassGroupEquiv eQ w.val := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) eQ
  rfl

/-- Its value is also the already accepted literal central-kernel class map. -/
theorem fibreEquiv_weightClassEquiv (c : LiteralPrimitiveBlock k (G F)) (w : S.Fibre c) :
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F)) eQ
    (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb c w).val =
      TypeBCentralKernelSpinFibreIdentification.weightClassEquiv eQ w.val := by
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) eQ
  exact TypeBCentrelessSelectedWeightBlockTransport.conjugacyClassGroupEquiv_eq_weightClassEquiv
    eQ w.val

/-- The full class map intertwines the actual opposite automorphisms. -/
theorem allWeights_op_smul (alpha : (MulAut (G F))ᵐᵒᵖ)
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G F)) :
    CharacterWeight.conjugacyClassGroupEquiv eQ (alpha • w) =
      MulOpposite.op (MulAut.congr eQ alpha.unop) •
        CharacterWeight.conjugacyClassGroupEquiv eQ w :=
  CharacterWeight.conjugacyClassGroupEquiv_op_smul eQ alpha w

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientWeightFibre




/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
