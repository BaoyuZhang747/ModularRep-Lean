import ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
import ModularRep.IBrBlockAutomorphism

/-!
# All-character block transport on the principal reference quotient

The actual quotient action on the original primitive block labels is pulled
back along the reference quotient equivalence. The complete Brauer character
equivalence preserves those labels and intertwines the opposite automorphism
actions. Thus the specified block transport equation holds for every quotient
Brauer character, with the same block action as the quotient weight source.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBlockAutomorphism

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCentralKernelBlockSource
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open EvenFieldFLZ318FixedTheoremGate TypeBCliffordCarriers
open TypeBRankThreePrincipalQuotientBrauerFibre

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

/-- Every quotient Brauer character has the prescribed transported block
label under every actual opposite automorphism of the quotient. -/
theorem quotientBrauerBlock_transport
    (alpha : (MulAut (quotientGroup S SH literal literalH Msys root calibration
      navarro guard b hb))ᵐᵒᵖ)
    (phi : IBr (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    letI := physicalBlockFintype S
    letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
      (Block := LiteralPrimitiveBlock k (G F))
      (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb)
    irreducibleBrauerCharacterBlock
        (quotientRoot S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
          (quotientRoot S SH literal literalH Msys root calibration navarro guard b
            parameters N C centreSpin fullCover simple nonabelian hb))
        (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb) (alpha • phi) =
      alpha • irreducibleBrauerCharacterBlock
        (quotientRoot S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
          (quotientRoot S SH literal literalH Msys root calibration navarro guard b
            parameters N C centreSpin fullCover simple nonabelian hb))
        (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
          parameters N C centreSpin fullCover simple nonabelian hb) phi := by
  letI := physicalBlockFintype S
  let e := quotientEquiv S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb
  letI := OddTwoGroupEquivWeightBlocks.transportedBlockAction
    (Block := LiteralPrimitiveBlock k (G F)) e
  let brauerEquiv := allBrauerEquiv S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb
  let originalBlock := irreducibleBrauerCharacterBlock root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    (physicalDecomposition S literal)
  let blockQ := irreducibleBrauerCharacterBlock
    (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (quotientRoot S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb))
    (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
  let pre : IBr root := brauerEquiv.symm phi
  let a : (MulAut (G F))ᵐᵒᵖ := MulOpposite.op (MulAut.congr e.symm alpha.unop)
  have characterValue : brauerEquiv pre = phi := brauerEquiv.apply_symm_apply phi
  have automorphismValue : MulOpposite.op (MulAut.congr e a.unop) = alpha := by
    change MulOpposite.op (MulAut.congr e (MulAut.congr e.symm alpha.unop)) = alpha
    exact (congrArg MulOpposite.op
      (OddTwoGroupEquivWeightBlocks.congr_symm_congr e alpha.unop)).trans
        (MulOpposite.op_unop alpha)
  have characterAction : brauerEquiv (a • pre) = alpha • phi := by
    have natural := IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul root e pre a
    change brauerEquiv (a • pre) =
      MulOpposite.op (MulAut.congr e a.unop) • brauerEquiv pre at natural
    rw [automorphismValue, characterValue] at natural
    exact natural
  have blockValue (chi : IBr root) : blockQ (brauerEquiv chi) = originalBlock chi :=
    allBrauerEquiv_block S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb chi
  have originalAction : originalBlock (a • pre) = a • originalBlock pre := by
    have physicalAction := primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
      root (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      (physicalDecomposition S literal) a pre
    change originalBlock (a • pre) = a • originalBlock pre at physicalAction
    exact physicalAction
  change blockQ (alpha • phi) = alpha • blockQ phi
  calc
    blockQ (alpha • phi) = blockQ (brauerEquiv (a • pre)) :=
      congrArg blockQ characterAction.symm
    _ = originalBlock (a • pre) := blockValue (a • pre)
    _ = a • originalBlock pre := originalAction
    _ = alpha • blockQ phi := by
      change a • originalBlock pre = a • blockQ phi
      exact congrArg (fun c : LiteralPrimitiveBlock k (G F) => a • c)
        ((blockValue pre).symm.trans (congrArg blockQ characterValue))

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBlockAutomorphism


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
