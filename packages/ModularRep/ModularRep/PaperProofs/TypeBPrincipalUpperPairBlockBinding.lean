import ModularRep.PaperProofs.TypeBRankThreePrincipalSOMatchingSplitting
import ModularRep.PaperProofs.TypeBRankThreePrincipalFieldNaturality
import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding

/-!
# Specified blocks of an upper principal pair

The same specified principal fibre supplies both ambient block equalities.
Every representative of the computed SO weight class is covered. The local
ordinary inflation law is retained on the literal normalizer and the given
weight's own ordinary character; it is never replaced by a block label.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalUpperPairBlockBinding

open ModularRep CharacterWeight TypeBCentralKernelBlockSource
open TypeBRankThreePrincipalFieldNaturality TypeBLocalPhysicalBlockBinding
open TypeBCliffordCarriers TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding TypeBGreenPrincipalConstituentSource
open TypeBCliffordOrthogonalAmbientQuotient NavarroCoveringBrauerExtension
open TypeBLocalReductionInstantiation TypeBFixedRootDefinitionFamily

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section PhysicalFibre

variable {k K X : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k]
  [CharZero K] [Group X] [Finite X]
  (S : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := X) (Block := LiteralPrimitiveBlock k X))
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (root : PrimeRegularRootEmbedding 2 k K X)
  (b : LiteralPrimitiveBlock k X)

theorem supportedCharacter_block (Phi : BrauerFibre root b) :
    letI := S.operations.ambientBlockData.fintypeBlock
    TypeBCentralKernelBrauerBlocks.block root (physicalDecomposition S literal) Phi.val = b := by
  letI := S.operations.ambientBlockData.fintypeBlock
  exact (TypeBCentralKernelBrauerBlocks.supported_iff_block root
    (physicalDecomposition S literal) b Phi.val).mp Phi.property

/-- The conclusion holds for any representative of the supplied fibre point. -/
theorem rawWeight_inducedBlock_eq (v : S.Fibre b) (V : CharacterWeight 2 K X)
    (represents : TypeBWeightCoveringSource.rawClass V = v.val) :
    S.operations.induceToAmbient V = b := by
  have hv : S.weightBlock v.val = b := v.property
  rw [← represents] at hv
  change S.operations.rawWeightBlock V = b at hv
  exact hv

theorem upperPair_sameBlock (Phi : BrauerFibre root b) (v : S.Fibre b)
    (V : CharacterWeight 2 K X)
    (represents : TypeBWeightCoveringSource.rawClass V = v.val) :
    letI := S.operations.ambientBlockData.fintypeBlock
    TypeBCentralKernelBrauerBlocks.block root (physicalDecomposition S literal) Phi.val =
      S.operations.induceToAmbient V := by
  letI := S.operations.ambientBlockData.fintypeBlock
  exact (supportedCharacter_block S literal root b Phi).trans
    (rawWeight_inducedBlock_eq S b v V represents).symm

end PhysicalFibre

section OrdinaryLocalBlock

variable {K O k X : Type} [Field K] [CommRing O] [IsDomain O] [Field k]
  [Algebra O K] [CharZero K] [CharP k 2] [IsAlgClosed k] [Group X] [Finite X]
  (Msys : ModularSystem 2 K O k)
  [HasEnoughRootsOfUnity K (Nat.card X)]
  (S : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := X) (Block := LiteralPrimitiveBlock k X))
  (ordinary : ∀ Q : Subgroup X, NormalizerOrdinarySource Msys S.operations Q)
  (membership : OrdinaryInflationMembership Msys S.operations ordinary)

include membership in
/-- The normalizer block in the induction is that of the same inflated
ordinary local character, with the operations-specific source displayed. -/
theorem ownLocalCharacter_normalizerBlock (V : CharacterWeight 2 K X) :
    ordinaryNormalizerBlock Msys S.operations V.subgroup (ordinary V.subgroup)
      (inflatedOrdinary V.subgroup V.localCharacter) =
        S.operations.inflateToNormalizer V.subgroup
          (S.operations.localCharacterBlock V.subgroup V.localCharacter V.defectZero) :=
  membership.membership V.subgroup V.radical V.localCharacter V.defectZero

include membership in
/-- Actual induction from the primitive block of the own inflated ordinary
character, with both specified central character catalogues retained. -/
theorem ownLocalCharacter_blockInducesTo (V : CharacterWeight 2 K X) :
    letI := S.operations.ambientBlockData.fintypeBlock
    letI := (S.operations.inflatedNormalizerBlockData V.subgroup).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set X))
      (S.operations.inflatedNormalizerBlockData V.subgroup).catalogue
      S.operations.ambientBlockData.catalogue
      (ordinaryNormalizerBlock Msys S.operations V.subgroup (ordinary V.subgroup)
        (inflatedOrdinary V.subgroup V.localCharacter))
      (S.operations.induceToAmbient V) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := (S.operations.inflatedNormalizerBlockData V.subgroup).fintypeBlock
  rw [ownLocalCharacter_normalizerBlock Msys S ordinary membership V]
  exact inducedBlock_spec (Subgroup.normalizer (V.subgroup : Set X))
    (S.operations.inflatedNormalizerBlockData V.subgroup).catalogue
    S.operations.ambientBlockData.catalogue _ (S.operations.blockInductionDefined V)

include membership in
theorem upperPair_ordinaryBlockInducesTo
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (root : PrimeRegularRootEmbedding 2 k K X) (b : LiteralPrimitiveBlock k X)
    (Phi : BrauerFibre root b) (v : S.Fibre b) (V : CharacterWeight 2 K X)
    (represents : TypeBWeightCoveringSource.rawClass V = v.val) :
    letI := S.operations.ambientBlockData.fintypeBlock
    letI := (S.operations.inflatedNormalizerBlockData V.subgroup).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set X))
      (S.operations.inflatedNormalizerBlockData V.subgroup).catalogue
      S.operations.ambientBlockData.catalogue
      (ordinaryNormalizerBlock Msys S.operations V.subgroup (ordinary V.subgroup)
        (inflatedOrdinary V.subgroup V.localCharacter))
      (TypeBCentralKernelBrauerBlocks.block root (physicalDecomposition S literal) Phi.val) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  letI := (S.operations.inflatedNormalizerBlockData V.subgroup).fintypeBlock
  rw [upperPair_sameBlock S literal root b Phi v V represents]
  exact ownLocalCharacter_blockInducesTo Msys S ordinary membership V

end OrdinaryLocalBlock

section ActualSOMap

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {r f : ℕ} [CharP F r]
  {S : OmegaWeightSource (k := k) (K := K) F}
  {SH : SOWeightSource (k := k) (K := K) F}
  {root : PrimeRegularRootEmbedding 2 k K (G F)}
  {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
  {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
  {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
  {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
  {literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val}
  {delta : H F} {indexTwo : (G F).index = 2} {outside : delta ∉ G F}
  {parameters : OddFieldParameters F r f} {notThree : Nat.card F ≠ 3}
  {Msys : ModularSystem 2 K O k}
  {rootCalibration : RootResidueCompatible Msys root}
  {rootHCalibration : RootResidueCompatible Msys rootH}
  {guard : GuardedBlockCompatibility root S.operations}
  {guardH : GuardedBlockCompatibility rootH SH.operations}
  [HasEnoughRootsOfUnity K (Nat.card (H F))]
  {dgn : TypeBWeightCoveringSplittingSource.DGNSource (G F) Msys}
  (covering : TypeBRankThreePrincipalCoverSplitting.PublishedWeightCovering
    F S SH root rootH b hb bH hbH literal literalH delta indexTwo outside parameters
    notThree Msys rootCalibration rootHCalibration guard guardH dgn)
  [Fintype (OmegaBrauer F root b)] [DecidableEq (OmegaBrauer F root b)]
  [Fintype (SOBrauer F rootH bH)]
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (counts : PublishedCounts F S root b SH rootH bH parameters notThree hb hbH literal literalH)
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

local notation "soMap" =>
  TypeBRankThreePrincipalSOMatchingSplitting.principalSOEquiv covering counts roots fieldScope
    green principalLift clifford principalRestriction

theorem principalSOEquiv_upperRawWeight_inducedBlock_eq (Phi : SOBrauer F rootH bH)
    (V : CharacterWeight 2 K (H F))
    (represents : TypeBWeightCoveringSource.rawClass V = (soMap Phi).val) :
    SH.operations.induceToAmbient V = bH :=
  rawWeight_inducedBlock_eq SH bH (soMap Phi) V represents

/-- The actual computed upper pair has the same specified block. -/
theorem principalSOEquiv_upperPair_sameBlock (Phi : SOBrauer F rootH bH)
    (V : CharacterWeight 2 K (H F))
    (represents : TypeBWeightCoveringSource.rawClass V = (soMap Phi).val) :
    letI := SH.operations.ambientBlockData.fintypeBlock
    TypeBCentralKernelBrauerBlocks.block rootH (physicalDecomposition SH literalH) Phi.val =
      SH.operations.induceToAmbient V :=
  upperPair_sameBlock SH literalH rootH bH Phi (soMap Phi) V represents

/-- The same SO map satisfies the literal ordinary-to-Brauer block induction. -/
theorem principalSOEquiv_upperPair_ordinaryBlockInducesTo
    (ordinary : ∀ Q : Subgroup (H F), NormalizerOrdinarySource Msys SH.operations Q)
    (membership : OrdinaryInflationMembership Msys SH.operations ordinary)
    (Phi : SOBrauer F rootH bH) (V : CharacterWeight 2 K (H F))
    (represents : TypeBWeightCoveringSource.rawClass V = (soMap Phi).val) :
    letI := SH.operations.ambientBlockData.fintypeBlock
    letI := (SH.operations.inflatedNormalizerBlockData V.subgroup).fintypeBlock
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (H F)))
      (SH.operations.inflatedNormalizerBlockData V.subgroup).catalogue
      SH.operations.ambientBlockData.catalogue
      (ordinaryNormalizerBlock Msys SH.operations V.subgroup (ordinary V.subgroup)
        (inflatedOrdinary V.subgroup V.localCharacter))
      (TypeBCentralKernelBrauerBlocks.block rootH (physicalDecomposition SH literalH) Phi.val) :=
  upperPair_ordinaryBlockInducesTo Msys SH ordinary membership literalH rootH bH
    Phi (soMap Phi) V represents

end ActualSOMap

end ModularRep.PaperProofs.TypeBPrincipalUpperPairBlockBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
