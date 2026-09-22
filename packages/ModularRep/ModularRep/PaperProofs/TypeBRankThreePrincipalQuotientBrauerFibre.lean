import ModularRep.PaperProofs.TypeBRankThreePrincipalReferenceBinding
import ModularRep.IBrBlockEquivTransport

/-!
# The complete Brauer fibre on the principal reference quotient

The quotient block decomposition is induced by the actual canonical
projection. Its indices remain the original literal primitive blocks.
The complete character equivalence restricts in both directions, and its
forward map is the reference binding's already constructed quotient character.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalFieldNaturality
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily
open TypeBCentralKernelBlockSource
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open EvenFieldFLZCentrelessCentralKernel EvenFieldFLZ318FixedTheoremGate
open TypeBCliffordCarriers TypeBRankThreePrincipalReferenceBinding

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

/-- The enumeration is computed from the explicitly supplied source. -/
def physicalBlockFintype : Fintype (LiteralPrimitiveBlock k (G F)) :=
  S.operations.ambientBlockData.fintypeBlock

/-- Every fibre below uses this one actual principal reference quotient. -/
abbrev quotientGroup (hb : IsPrincipal b) :=
  CentralCharacterQuotient (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb)

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (hb : IsPrincipal b)

/-- The forward equivalence is the same reference quotient projection. -/
def quotientEquiv : (G F) ≃* (quotientGroup S SH literal literalH Msys root calibration navarro guard b hb) :=
  (centerlessCentralCharacterQuotientEquiv
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb)).symm

@[simp] theorem quotientEquiv_projection (g : G F) :
    quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb g =
      centralCharacterQuotientMap (problem S SH literal literalH Msys root calibration navarro guard b) (reference S SH literal literalH Msys root calibration navarro guard b hb) g := by
  apply (centerlessCentralCharacterQuotientEquiv
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb)).injective
  exact (centerlessCentralCharacterQuotientEquiv
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb)).apply_symm_apply g

/-- The root is transported over the same reference quotient for every character. -/
def quotientRoot : PrimeRegularRootEmbedding 2 k K (quotientGroup S SH literal literalH Msys root calibration navarro guard b hb) :=
  root.alongMulEquiv (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)

@[simp] theorem quotientBrauer_iota
    (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).iota = quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb := rfl

theorem quotientRoot_lift :
    (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).lift = root.lift :=
  TypeBRankThreePrincipalReferenceBinding.quotientBrauer_root_lift
    S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (reference S SH literal literalH Msys root calibration navarro guard b hb)

theorem quotientRoot_residue :
    RootResidueCompatible Msys (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :=
  TypeBRankThreePrincipalReferenceBinding.quotientBrauer_residue
    S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb (reference S SH literal literalH Msys root calibration navarro guard b hb)

/-- The indices remain the original primitive blocks; the idempotents are induced. -/
def quotientIdempotent (c : LiteralPrimitiveBlock k (G F)) :
    k[quotientGroup S SH literal literalH Msys root calibration navarro guard b hb] :=
  MonoidAlgebra.domCongr k k (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) c.val

/-- The entire quotient decomposition is derived from the prescribed specified one. -/
def quotientBlocks :
    letI := physicalBlockFintype S
    BlockIdempotentDecomposition (quotientIdempotent S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) := by
  letI := physicalBlockFintype S
  exact (physicalDecomposition S literal).alongMulEquiv (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)

/-- All quotient irreducible Brauer characters are included before restricting blocks. -/
def allBrauerEquiv : IBr root ≃ IBr (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv root (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)

/-- Transport preserves the original index in the induced specified decomposition. -/
theorem allBrauerEquiv_block (phi : IBr root) :
    letI := physicalBlockFintype S
    irreducibleBrauerCharacterBlock (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
      (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (allBrauerEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb phi) =
    irreducibleBrauerCharacterBlock root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      (physicalDecomposition S literal) phi := by
  letI := physicalBlockFintype S
  exact irreducibleBrauerCharacterBlock_alongMulEquiv root
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
    (quotientEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
    (physicalDecomposition S literal) phi

/-- This is the whole block fibre at the original index, on the reference quotient. -/
abbrev QuotientBrauerFibre :=
  letI := physicalBlockFintype S
  IBrBlock (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
    (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) b

/-- The complete original family fibre is equivalent to the complete quotient fibre. -/
def fibreEquiv :
    Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b) ≃ QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb := by
  letI := physicalBlockFintype S
  exact (allBrauerEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).subtypeEquiv (fun phi => by
    change irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
        (physicalDecomposition S literal) phi = b ↔
      irreducibleBrauerCharacterBlock (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
        (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (allBrauerEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb phi) = b
    rw [allBrauerEquiv_block S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb phi])

/-- The forward character is exactly the previously constructed reference descent. -/
@[simp] theorem fibreEquiv_val
    (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).val = (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer := rfl

/-- Forward membership is proved for the actual descended character and block. -/
theorem quotientBrauer_block
    (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    letI := physicalBlockFintype S
    irreducibleBrauerCharacterBlock
      (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).iota
      (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).irreducibleBrauerInjective
      (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer = b := by
  letI := physicalBlockFintype S
  exact (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).property

@[simp] theorem fibreEquiv_apply_symm_apply (phi : QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) :
    fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm phi) = phi :=
  (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).apply_symm_apply phi

@[simp] theorem fibreEquiv_symm_apply_apply
    (psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b)) :
    (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi) = psi :=
  (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm_apply_apply psi

/-- Every member of the entire quotient block has one and only one original character. -/
theorem quotientBrauer_existsUnique
    (phi : IBr (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)) :
    letI := physicalBlockFintype S
    irreducibleBrauerCharacterBlock (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (quotientRoot S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb))
        (quotientBlocks S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) phi = b ↔
      ∃! psi : Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b),
        (TypeBRankThreePrincipalReferenceBinding.quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer = phi := by
  letI := physicalBlockFintype S
  constructor
  · intro membership
    let target : QuotientBrauerFibre S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb := ⟨phi, membership⟩
    refine ⟨(fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).symm target, ?_, ?_⟩
    · exact congrArg Subtype.val ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).apply_symm_apply target)
    · intro psi character
      apply (fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).injective
      apply Subtype.ext
      exact character.trans
        (congrArg Subtype.val ((fibreEquiv S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb).apply_symm_apply target)).symm
  · rintro ⟨psi, character, _⟩
    rw [← character]
    exact quotientBrauer_block S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi

end ModularRep.PaperProofs.TypeBRankThreePrincipalQuotientBrauerFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
