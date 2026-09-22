import ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import ModularRep.GroupAlgebraClassSums

/-!
# The principal weight fibre of the actual central two-quotient

K proves that coefficient restriction commutes with the actual normalizer
projection. The remaining local E1 inputs are Navarro 9.10 on the actual
normalizer Brauer inflation, with compatible roots, and the central character
description of block domination on pp.198--199. They concern actual primitive
idempotents and centers, not a selected ambient block or principal fibre.

Shared local support and actual compatible reductions identify the two
operations' blocks of the selected pair's own character. K then compares
the induced central functions, identifies their primitive ambient blocks by
the catalogue delta laws, and restricts the constructed weight-class map.
The downstairs FM map is computed from the existing upstairs FM map.

No instance of the standard sources is asserted. Full projective
automorphism lifting, full stabilizer triples, and the final iBAW relation
remain separate joins.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroLocalReductionInflationBlockCompatibility
open ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoCentralTwoWeightInflation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) : Fintype Q := Fintype.ofFinite _

section Coefficients

variable {k G H : Type u} [Field k] [Group G] [Fintype G] [Group H] [Fintype H]

/-- The literal algebra map between the two actual normalizers. -/
def normalizerAlgebraMap (f : G →* H) (Q : Subgroup G) :
    k[Subgroup.normalizer (Q : Set G)] →ₐ[k]
      k[Subgroup.normalizer ((Q.map f : Subgroup H) : Set H)] :=
  MonoidAlgebra.mapDomainAlgHom k k (normalizerMap f Q)

/-- Coefficient restriction commutes with projection because the upstairs
normalizer is the entire preimage of the downstairs normalizer. This is a
K identity for all algebra elements, independent of block theory. -/
theorem coeffRestrict_normalizer_projection
    (f : G →* H) (hf : Function.Surjective f) (Q : Subgroup G)
    (hkernel : f.ker ≤ Q) (z : k[G]) :
    normalizerAlgebraMap f Q
        (coeffRestrict (Subgroup.normalizer (Q : Set G)) z) =
      coeffRestrict (Subgroup.normalizer ((Q.map f : Subgroup H) : Set H))
        (MonoidAlgebra.mapDomainAlgHom k k f z) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero =>
    rw [map_zero (coeffRestrict (Subgroup.normalizer (Q : Set G))),
      map_zero (normalizerAlgebraMap (k := k) f Q),
      map_zero (MonoidAlgebra.mapDomainAlgHom k k f),
      map_zero (coeffRestrict (Subgroup.normalizer ((Q.map f : Subgroup H) : Set H)))]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r =>
    have hmem : f g ∈ Subgroup.normalizer ((Q.map f : Subgroup H) : Set H) ↔
        g ∈ Subgroup.normalizer (Q : Set G) := by
      change g ∈ (Subgroup.normalizer ((Q.map f : Subgroup H) : Set H)).comap f ↔ _
      rw [Subgroup.comap_normalizer_eq_of_surjective _ hf,
        Subgroup.comap_map_eq_self hkernel]
    change MonoidAlgebra.mapDomain (normalizerMap f Q)
        (coeffRestrict (Subgroup.normalizer (Q : Set G))
          (MonoidAlgebra.single g r)) =
      coeffRestrict (Subgroup.normalizer ((Q.map f : Subgroup H) : Set H))
        (MonoidAlgebra.mapDomain f (MonoidAlgebra.single g r))
    rw [MonoidAlgebra.mapDomain_single, coeffRestrict_single, coeffRestrict_single]
    by_cases hg : g ∈ Subgroup.normalizer (Q : Set G)
    · rw [dif_pos hg, dif_pos (hmem.mpr hg), MonoidAlgebra.mapDomain_single]
      rfl
    · rw [dif_neg hg, dif_neg (mt hmem.mp hg)]
      exact MonoidAlgebra.mapDomain_zero (normalizerMap f Q)

end Coefficients

section OwnCentralFunctions

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [IsAlgClosed k] [Field K] [CharZero K]
variable [Group G] [Fintype G] [MulAction (MulAut G)ᵐᵒᵖ Block]

def ownNormalizerBlock
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G)
      (Block := Block)) (W : CharacterWeight p K G) :
    InflatedNormalizerBlock (k := k) W.subgroup :=
  O.inflateToNormalizer W.subgroup
    (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

def ownLocalCentralCharacter
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G)
      (Block := Block)) (W : CharacterWeight p K G) :
    GroupAlgebraCenter k (Subgroup.normalizer (W.subgroup : Set G)) →ₐ[k] k :=
  letI := (O.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  (O.inflatedNormalizerBlockData W.subgroup).catalogue.centralCharacter
    (ownNormalizerBlock O W)

def ownInducedCentralFunction
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G)
      (Block := Block)) (W : CharacterWeight p K G) :
    GroupAlgebraCenter k G →ₗ[k] k :=
  inducedCentralFunction (Subgroup.normalizer (W.subgroup : Set G))
    (ownLocalCentralCharacter O W)

theorem rawWeightBlock_evaluation
    (O : LocalBlockInductionOperations (p := p) (k := k) (K := K) (G := G)
      (Block := Block)) (W : CharacterWeight p K G) (z : GroupAlgebraCenter k G) :
    letI := O.ambientBlockData.fintypeBlock
    O.ambientBlockData.catalogue.centralCharacter (O.rawWeightBlock W) z =
      ownInducedCentralFunction O W z := by
  letI := O.ambientBlockData.fintypeBlock
  letI := (O.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  have h := congrArg (fun lambda => lambda z)
    (inducedBlock_centralCharacter (Subgroup.normalizer (W.subgroup : Set G))
      (O.inflatedNormalizerBlockData W.subgroup).catalogue
      O.ambientBlockData.catalogue (ownNormalizerBlock O W) (O.blockInductionDefined W))
  simpa only [LocalBlockInductionOperations.rawWeightBlock,
    LocalBlockInductionOperations.induceToAmbient, ownNormalizerBlock,
    ownInducedCentralFunction, ownLocalCentralCharacter, inducedCentralCharacter_apply] using h

end OwnCentralFunctions

section LiteralProjection

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance spFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable (cover : OddSymplecticFullCoverSource n F)
variable (iotaUp : PrimeRegularRootEmbedding 2 k K (LiteralSp n F))
variable (iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F))
variable (OUp : LocalBlockInductionOperations (p := 2) (k := k) (K := K)
  (G := LiteralSp n F) (Block := Block))
variable (ODown : LocalBlockInductionOperations (p := 2) (k := k) (K := K)
  (G := LiteralPSp n F) (Block := J))

/-- Actual reductions of the same selected local character on both sides,
with the root triangle through both inclusions and the actual projection.
No block condition is included. -/
structure CompatiblePairReductions (W : CharacterWeight 2 K (LiteralSp n F)) where
  upRoot : PrimeRegularRootEmbedding 2 k K
    (Subgroup.normalizer (W.subgroup : Set (LiteralSp n F)))
  downRoot : PrimeRegularRootEmbedding 2 k K
    (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (LiteralPSp n F)))
  upCompatible : RootCompatibleAlong iotaUp upRoot
    (Subgroup.normalizer (W.subgroup : Set (LiteralSp n F))).subtype
  downCompatible : RootCompatibleAlong iotaDown downRoot
    (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (LiteralPSp n F))).subtype
  quotientCompatible : RootCompatibleAlong downRoot upRoot
    (normalizerMap (literalProjection n F) W.subgroup)
  upBrauer : IBr upRoot
  downBrauer : IBr downRoot
  upReduction : NormalizerInflatedReduction W.subgroup W.localCharacter upRoot upBrauer
  downReduction : NormalizerInflatedReduction (spQuotientPair cover W).subgroup
    (spQuotientPair cover W).localCharacter downRoot downBrauer

/-- Exact local E1 source facts for this central-two projection. The first
is Navarro 9.10 on the actual normalizer Brauer inflation. The second is
the central character characterization of domination, Navarro pp.198--199.
It applies to all local primitive blocks and all central algebra elements.
Neither field selects an induced ambient block or a principal fibre. -/
structure NormalizerProjectionSource : Prop where
  brauer_support : ∀ (W : CharacterWeight 2 K (LiteralSp n F))
      (upRoot : PrimeRegularRootEmbedding 2 k K
        (Subgroup.normalizer (W.subgroup : Set (LiteralSp n F))))
      (downRoot : PrimeRegularRootEmbedding 2 k K
        (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (LiteralPSp n F))))
      (phiUp : IBr upRoot) (phiDown : IBr downRoot),
      RootCompatibleAlong downRoot upRoot (normalizerMap (literalProjection n F) W.subgroup) →
      phiUp.1 = pullbackPrimeRegularClassFunction
        (normalizerMap (literalProjection n F) W.subgroup) phiDown.1 →
      normalizerAlgebraMap (literalProjection n F) W.subgroup
        (normalizerBrauerBlock OUp W.subgroup upRoot phiUp).1 =
        (normalizerBrauerBlock ODown (spQuotientPair cover W).subgroup downRoot phiDown).1
  central_character : ∀ (W : CharacterWeight 2 K (LiteralSp n F))
      (bUp : InflatedNormalizerBlock (k := k) W.subgroup)
      (bDown : InflatedNormalizerBlock (k := k) (spQuotientPair cover W).subgroup),
      normalizerAlgebraMap (literalProjection n F) W.subgroup bUp.1 = bDown.1 →
      ∀ (zUp : GroupAlgebraCenter k (Subgroup.normalizer (W.subgroup : Set (LiteralSp n F))))
        (zDown : GroupAlgebraCenter k
          (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (LiteralPSp n F)))),
      normalizerAlgebraMap (literalProjection n F) W.subgroup zUp.1 = zDown.1 →
      letI := (OUp.inflatedNormalizerBlockData W.subgroup).fintypeBlock
      letI := (ODown.inflatedNormalizerBlockData (spQuotientPair cover W).subgroup).fintypeBlock
      (OUp.inflatedNormalizerBlockData W.subgroup).catalogue.centralCharacter bUp zUp =
        (ODown.inflatedNormalizerBlockData (spQuotientPair cover W).subgroup).catalogue.centralCharacter
          bDown zDown

/-- The exact operations are interpreted by the shared source, and genuine
compatible reductions exist for every own pair. No block transport result
or global weight equivalence is a field. -/
structure BlockProjectionInput : Prop where
  upSupport : OddTwoActualLocalBlockSupport.Source iotaUp OUp
  downSupport : OddTwoActualLocalBlockSupport.Source iotaDown ODown
  reductions : ∀ W : CharacterWeight 2 K (LiteralSp n F),
    Nonempty (CompatiblePairReductions cover iotaUp iotaDown W)
  normalizer : NormalizerProjectionSource cover OUp ODown

namespace BlockProjectionInput

variable {cover iotaUp iotaDown OUp ODown}
variable (B : BlockProjectionInput cover iotaUp iotaDown OUp ODown)

include B

theorem ownNormalizerBlock_projection (W : CharacterWeight 2 K (LiteralSp n F)) :
    normalizerAlgebraMap (literalProjection n F) W.subgroup (ownNormalizerBlock OUp W).1 =
      (ownNormalizerBlock ODown (spQuotientPair cover W)).1 := by
  let R := Classical.choice (B.reductions W)
  have h := B.normalizer.brauer_support W R.upRoot R.downRoot R.upBrauer R.downBrauer
    R.quotientCompatible
    (ownLocalReduction_inflation (literalProjection n F) cover.fullCover.1.1
      cover.projection_twoKernel W R.upRoot R.downRoot R.upBrauer R.downBrauer
      R.upReduction R.downReduction)
  rw [B.upSupport.normalizer_block_of_reduction W R.upRoot R.upBrauer
    R.upCompatible R.upReduction,
    B.downSupport.normalizer_block_of_reduction (spQuotientPair cover W)
      R.downRoot R.downBrauer R.downCompatible R.downReduction] at h
  exact h

theorem ownInducedCentralFunction_projection (W : CharacterWeight 2 K (LiteralSp n F))
    (zUp : GroupAlgebraCenter k (LiteralSp n F))
    (zDown : GroupAlgebraCenter k (LiteralPSp n F))
    (hz : quotientAlgebraMap zUp.1 = zDown.1) :
    ownInducedCentralFunction OUp W zUp =
      ownInducedCentralFunction ODown (spQuotientPair cover W) zDown := by
  apply B.normalizer.central_character W (ownNormalizerBlock OUp W)
    (ownNormalizerBlock ODown (spQuotientPair cover W)) (B.ownNormalizerBlock_projection W)
  change normalizerAlgebraMap (literalProjection n F) W.subgroup
      (coeffRestrict (Subgroup.normalizer (W.subgroup : Set (LiteralSp n F))) zUp.1) =
    coeffRestrict
      (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (LiteralPSp n F))) zDown.1
  rw [coeffRestrict_normalizer_projection (literalProjection n F) cover.fullCover.1.1
    W.subgroup (kernel_le_selected (literalProjection n F) cover.projection_twoKernel W)]
  exact congrArg (coeffRestrict
    (Subgroup.normalizer ((spQuotientPair cover W).subgroup : Set (LiteralPSp n F)))) hz

/-- K derives the ambient primitive image by evaluating the induced
central functions at block idempotents and using their delta laws. -/
theorem rawWeightBlock_projection
    (primitiveImage : ∀ b : {b : k[LiteralSp n F] // IsPrimitiveCentralIdempotent b},
      IsPrimitiveCentralIdempotent (quotientAlgebraMap b.1))
    (W : CharacterWeight 2 K (LiteralSp n F)) :
    quotientAlgebraMap (OUp.ambientBlockData.blockIdempotent (OUp.rawWeightBlock W)) =
      ODown.ambientBlockData.blockIdempotent (ODown.rawWeightBlock (spQuotientPair cover W)) := by
  letI := OUp.ambientBlockData.fintypeBlock
  letI := ODown.ambientBlockData.fintypeBlock
  let bUp := OUp.rawWeightBlock W
  obtain ⟨bDown, hbDown⟩ := ODown.ambientBlockData.blocks.primitiveBlockOfIndex_surjective
    ⟨quotientAlgebraMap (OUp.ambientBlockData.blockIdempotent bUp),
      primitiveImage (OUp.ambientBlockData.blocks.primitiveBlockOfIndex bUp)⟩
  have hprojection : quotientAlgebraMap (OUp.ambientBlockData.blockIdempotent bUp) =
      ODown.ambientBlockData.blockIdempotent bDown := (congrArg Subtype.val hbDown).symm
  have heval := B.ownInducedCentralFunction_projection W
    (OUp.ambientBlockData.blocks.blockIdempotentInCenter bUp)
    (ODown.ambientBlockData.blocks.blockIdempotentInCenter bDown) hprojection
  rw [← rawWeightBlock_evaluation OUp W,
    ← rawWeightBlock_evaluation ODown (spQuotientPair cover W),
    OUp.ambientBlockData.catalogue.delta_own] at heval
  by_cases h : ODown.rawWeightBlock (spQuotientPair cover W) = bDown
  · exact hprojection.trans (congrArg ODown.ambientBlockData.blockIdempotent h.symm)
  · rw [ODown.ambientBlockData.catalogue.delta_other _ _ h] at heval
    exact (one_ne_zero heval).elim

theorem weightBlock_projection
    (upSource : LocalBlockInductionSource (p := 2) (k := k) (K := K)
      (G := LiteralSp n F) (Block := Block))
    (downSource : LocalBlockInductionSource (p := 2) (k := k) (K := K)
      (G := LiteralPSp n F) (Block := J))
    (hUp : upSource.operations = OUp) (hDown : downSource.operations = ODown)
    (T : ActualQuotientNaturality (K := K) (literalProjection n F)
      cover.fullCover.1.1 cover.projection_twoKernel)
    (primitiveImage : ∀ b : {b : k[LiteralSp n F] // IsPrimitiveCentralIdempotent b},
      IsPrimitiveCentralIdempotent (quotientAlgebraMap b.1))
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := LiteralSp n F)) :
    quotientAlgebraMap (OUp.ambientBlockData.blockIdempotent (upSource.weightBlock w)) =
      ODown.ambientBlockData.blockIdempotent (downSource.weightBlock (T.conjugacyClassEquiv w)) := by
  refine Quotient.inductionOn w ?_
  intro v
  refine Quotient.inductionOn v ?_
  intro W
  change quotientAlgebraMap (OUp.ambientBlockData.blockIdempotent
      (upSource.operations.rawWeightBlock W)) =
    ODown.ambientBlockData.blockIdempotent
      (downSource.operations.rawWeightBlock (spQuotientPair cover W))
  rw [hUp, hDown]
  exact B.rawWeightBlock_projection primitiveImage W

end BlockProjectionInput

end LiteralProjection

section ExistingPrincipalMap

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance principalSpFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance principalPSpFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block))
variable (cover : OddSymplecticFullCoverSource n F)

/-- Standard coefficient/block data on the literal quotient. Every map
below is computed from the projection and the existing FM map; neither a
Brauer nor weight equivalence, nor a principal-fibre identification, is a
field of this packet. -/
structure PrincipalDescentData where
  iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F)
  downInjective : IrreducibleBrauerCharacterInjectivity iotaDown
  downSource : LocalBlockInductionSource (p := 2) (k := k) (K := K)
    (G := LiteralPSp n F) (Block := J)
  oneDown : IBr iotaDown
  oneDown_value : ∀ g, oneDown.1 g = 1
  brauer : BrauerInflationSources D.iota iotaDown
  primitive :
    letI := D.blockSource.operations.ambientBlockData.fintypeBlock
    letI := downSource.operations.ambientBlockData.fintypeBlock
    Navarro910PrimitiveSource brauer cover
      D.blockSource.operations.ambientBlockData.blocks
      downSource.operations.ambientBlockData.blocks D.injective downInjective
  weightNaturality : ActualQuotientNaturality (K := K) (literalProjection n F)
    cover.fullCover.1.1 cover.projection_twoKernel
  blockProjection : BlockProjectionInput cover D.iota iotaDown
    D.blockSource.operations downSource.operations

namespace PrincipalDescentData

variable {D cover} (E : PrincipalDescentData (J := J) D cover)

def downPrincipalBlock : J :=
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  irreducibleBrauerCharacterBlock E.iotaDown E.downInjective
    E.downSource.operations.ambientBlockData.blocks E.oneDown

abbrev DownPrincipalBrauer :=
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  IBrBlock E.iotaDown E.downInjective
    E.downSource.operations.ambientBlockData.blocks E.downPrincipalBlock

abbrev DownPrincipalWeight := E.downSource.Fibre E.downPrincipalBlock

def brauerEquiv : E.DownPrincipalBrauer ≃ D.PrincipalBrauer := by
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  exact principalBrauerEquivForData D cover E.iotaDown E.downInjective
    E.downSource.operations.ambientBlockData.blocks E.oneDown E.oneDown_value
    E.brauer E.primitive

theorem principalBlock_projection :
    quotientAlgebraMap
        (D.blockSource.operations.ambientBlockData.blockIdempotent D.principalBlock) =
      E.downSource.operations.ambientBlockData.blockIdempotent E.downPrincipalBlock := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  have h := E.primitive.inflated_support E.oneDown
  rw [E.brauer.brauerEquiv_trivial cover E.oneDown D.trivialCharacter
    E.oneDown_value D.trivial_value] at h
  exact h

theorem principalWeight_iff
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := LiteralSp n F)) :
    D.blockSource.weightBlock w = D.principalBlock ↔
      E.downSource.weightBlock (E.weightNaturality.conjugacyClassEquiv w) =
        E.downPrincipalBlock := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  have hprojection := E.blockProjection.weightBlock_projection
    D.blockSource E.downSource rfl rfl E.weightNaturality E.primitive.primitive_image w
  constructor
  · intro h
    apply E.downSource.operations.ambientBlockData.blocks.primitiveBlockOfIndex_injective
    apply Subtype.ext
    change E.downSource.operations.ambientBlockData.blockIdempotent
        (E.downSource.weightBlock (E.weightNaturality.conjugacyClassEquiv w)) =
      E.downSource.operations.ambientBlockData.blockIdempotent E.downPrincipalBlock
    rw [← hprojection, h, E.principalBlock_projection]
  · intro h
    apply D.blockSource.operations.ambientBlockData.blocks.primitiveBlockOfIndex_injective
    apply E.primitive.primitive_injective
    change quotientAlgebraMap
        (D.blockSource.operations.ambientBlockData.blockIdempotent
          (D.blockSource.weightBlock w)) =
      quotientAlgebraMap
        (D.blockSource.operations.ambientBlockData.blockIdempotent D.principalBlock)
    rw [hprojection, h, E.principalBlock_projection]

/-- Restrict the already computed actual conjugacy class equivalence.
The principal membership proofs are derived from primitive algebra images.
-/
def weightEquiv : D.PrincipalWeight ≃ E.DownPrincipalWeight where
  toFun w := ⟨E.weightNaturality.conjugacyClassEquiv w.1,
    (E.principalWeight_iff w.1).mp w.2⟩
  invFun w := ⟨E.weightNaturality.conjugacyClassEquiv.symm w.1, by
    apply (E.principalWeight_iff _).mpr
    rw [Equiv.apply_symm_apply]
    exact w.2⟩
  left_inv w := Subtype.ext (E.weightNaturality.conjugacyClassEquiv.symm_apply_apply w.1)
  right_inv w := Subtype.ext (E.weightNaturality.conjugacyClassEquiv.apply_symm_apply w.1)

@[simp] theorem weightEquiv_class (w : D.PrincipalWeight) :
    (E.weightEquiv w).1 = E.weightNaturality.conjugacyClassEquiv w.1 := rfl

/-- The downstairs principal correspondence is the computed composite of
actual Brauer inflation, the same supplied FM omega, and actual quotienting
of weight classes. A second downstairs FM map is not assumed. -/
def descendedFengMalleOmega (FM : D.FengMalleTheorem62LiteralCertificate) :
    E.DownPrincipalBrauer ≃ E.DownPrincipalWeight :=
  E.brauerEquiv.trans (FM.omega.trans E.weightEquiv)

@[simp] theorem descendedFengMalleOmega_class
    (FM : D.FengMalleTheorem62LiteralCertificate) (phi : E.DownPrincipalBrauer) :
    (E.descendedFengMalleOmega FM phi).1 =
      E.weightNaturality.conjugacyClassEquiv (FM.omega (E.brauerEquiv phi)).1 := rfl

/-- Whenever W represents the existing FM image, the downstairs image is
represented by the actual quotient of that very pair, retaining its own
local character. The representative is not required to be equivariant. -/
theorem descendedFengMalleOmega_quotientPair
    (FM : D.FengMalleTheorem62LiteralCertificate) (phi : E.DownPrincipalBrauer)
    (W : CharacterWeight 2 K (LiteralSp n F))
    (hW : (FM.omega (E.brauerEquiv phi)).1 = Quotient.mk'' (Quotient.mk'' W)) :
    (E.descendedFengMalleOmega FM phi).1 =
      Quotient.mk'' (Quotient.mk'' (spQuotientPair cover W)) := by
  rw [descendedFengMalleOmega_class, hW]
  rfl

end PrincipalDescentData

end ExistingPrincipalMap

end ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
