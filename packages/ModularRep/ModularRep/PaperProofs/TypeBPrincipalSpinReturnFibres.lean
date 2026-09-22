import ModularRep.PaperProofs.TypeBCentralKernelLocalBlockBinding
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily
import ModularRep.PaperProofs.TypeBPrincipalRootLiftBinding
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource

/-!
# Principal specified fibres under the actual central two-surjection

All groups, ordinary characters, primitive blocks and root conventions are
literal. Ordinary roots are required only at the finite ambient orders.
The normalizer inputs contain ordinary catalogue membership and expansion,
not a transported block or a fibre equivalence. The local proof is used only
when either one of the two displayed raw weights is principal.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBPrincipalSpinReturnFibres

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelWeightTransport TypeBCentralKernelWeightBlockTransport
open TypeBCentralKernelLocalReduction TypeBFixedRootDefinitionFamily
open TypeBLocalReductionInstantiation TypeBLocalPhysicalBlockBinding
open TypeBModularGroupRootBinding TypeBCentralKernelBrauerInflation
open TypeBQ3PrincipalWeightInflation TypeBCentralKernelInertia
open TypeBAllRankPrincipalCriterionFixedBlockSource
open IrreducibleBrauerCharacterSurjectiveDescent

local instance finiteFintype (Y : Type) [Finite Y] : Fintype Y := Fintype.ofFinite Y
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K O : Type} [Field k] [Field K] [CommRing O] [IsDomain O]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- Ordinary data on precisely the normalizer of this raw weight. -/
structure NormalizerFacts {H : Type} [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (Msys : ModularSystem 2 K O k)
    (operations : LocalBlockInductionOperations
      (p := 2) (k := k) (K := K) (G := H) (Block := LiteralPrimitiveBlock k H))
    (W : CharacterWeight 2 K H) where
  ordinary : NormalizerOrdinarySource Msys operations W.subgroup
  expansion : letI := normalizerOrdinaryRoots (K := K) W.subgroup
    ScopedDecompositionExpansionSource
      (H := Subgroup.normalizer (W.subgroup : Set H)) Msys
  inflation :
    ordinaryNormalizerBlock Msys operations W.subgroup ordinary
      (inflatedOrdinary W.subgroup W.localCharacter) =
    operations.inflateToNormalizer W.subgroup
      (operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)

section Local

variable {H : Type} [Group H] [Finite H]
  [HasEnoughRootsOfUnity K (Nat.card H)]
  (Msys : ModularSystem 2 K O k)

/-- The scoped ordinary facts imply the specified law at this one weight. -/
theorem normalizerBlock_of_facts
    (root : PrimeRegularRootEmbedding 2 k K H)
    (calibration : RootResidueCompatible Msys root)
    (operations : LocalBlockInductionOperations
      (p := 2) (k := k) (K := K) (G := H) (Block := LiteralPrimitiveBlock k H))
    (W : CharacterWeight 2 K H) (facts : NormalizerFacts Msys operations W)
    (rootN : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer (W.subgroup : Set H))) (phiN : IBr rootN)
    (agreement : NormalizerRootAgreement root W.subgroup rootN)
    (reduction : NormalizerInflatedReduction W.subgroup W.localCharacter rootN phiN) :
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
      operations W.subgroup rootN phiN = ownNormalizerBlock operations W := by
  have heq := normalizerRoot_eq_groupRoot Msys root calibration W.subgroup rootN agreement
  subst rootN
  letI := normalizerOrdinaryRoots (K := K) W.subgroup
  have support := decompositionRow_self_ne_zero Msys facts.expansion
    (inflatedOrdinary W.subgroup W.localCharacter) phiN reduction
  exact (normalizerBrauerBlock_eq_ordinary Msys operations W.subgroup
    facts.ordinary (inflatedOrdinary W.subgroup W.localCharacter) phiN support).trans
      facts.inflation

abbrev localRoot (W : CharacterWeight 2 K H) :=
  normalizerRoot W (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W)

theorem localRoot_residue (W : CharacterWeight 2 K H) :
    RootResidueCompatible Msys (localRoot Msys W) :=
  TypeBCentralKernelPairSplittingBinding.normalizerRoot_residue Msys W

theorem localRoot_agrees (root : PrimeRegularRootEmbedding 2 k K H)
    (calibration : RootResidueCompatible Msys root) (W : CharacterWeight 2 K H) :
    NormalizerRootAgreement root W.subgroup (localRoot Msys W) := by
  rw [eq_groupRoot_of_residue Msys H root calibration,
    eq_groupRoot_of_residue Msys _ (localRoot Msys W) (localRoot_residue Msys W)]
  intro z
  exact groupRoot_agrees_of_dvd Msys H
    (Subgroup.normalizer (W.subgroup : Set H))
    (by
      simpa only [primeRegularExponent] using
        (Nat.ordCompl_dvd_ordCompl_of_dvd
          (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (W.subgroup : Set H))) 2)) z

variable (navarro : ∀ (Y : Type) [Group Y] [Finite Y]
    [HasEnoughRootsOfUnity K (Nat.card Y)]
    (root : PrimeRegularRootEmbedding 2 k K Y)
    (calibration : RootResidueCompatible Msys root),
      ScopedDefectZeroReductionSource Msys root calibration)

def localReduction (W : CharacterWeight 2 K H) : IBr (localRoot Msys W) :=
  inflatedReduction W (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W)
    (TypeBCentralKernelPairSplittingBinding.quotientReduction Msys W navarro)

theorem localReduction_value (W : CharacterWeight 2 K H) :
    NormalizerInflatedReduction W.subgroup W.localCharacter (localRoot Msys W)
      (localReduction Msys navarro W) :=
  inflatedReduction_value W _ _
    (TypeBCentralKernelPairSplittingBinding.quotientReduction_value Msys W navarro)

end Local

section Surjection

variable {H X : Type} [Group H] [Finite H] [Group X] [Finite X]
  (Msys : ModularSystem 2 K O k)
  (q : H →* X) (surjective : Function.Surjective q) (kernelTwo : IsPGroup 2 q.ker)

include q surjective kernelTwo in
/-- The entire root lifts agree because the actual kernel is a two-group. -/
theorem roots_lift_eq
    (root : PrimeRegularRootEmbedding 2 k K H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (calibrationX : RootResidueCompatible Msys rootX) :
    root.lift = rootX.lift :=
  TypeBPrincipalRootLiftBinding.lift_eq_of_residue Msys
    (TypeBCentralKernelTripleRootFamily.exponent_surjection
      q surjective Nat.prime_two kernelTwo) root rootX calibration calibrationX

/-- The canonical first isomorphism is used only for primitive blocks. -/
def primitiveEquiv (central : q.ker ≤ Subgroup.center H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (blocks : NavarroCentralBlockPrinciple 2 k) :
    LiteralPrimitiveBlock k H ≃ LiteralPrimitiveBlock k X :=
  (TypeBCentralKernelBlockSource.blockEquiv q.ker kernelTwo central
    (rootX.alongMulEquiv (QuotientGroup.quotientKerEquivOfSurjective q surjective).symm)
      blocks).trans
    (TypeBCentralKernelSpinFibreIdentification.primitiveBlockEquiv
      (QuotientGroup.quotientKerEquivOfSurjective q surjective))

theorem primitiveEquiv_value (central : q.ker ≤ Subgroup.center H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (blocks : NavarroCentralBlockPrinciple 2 k) (b : LiteralPrimitiveBlock k H) :
    (primitiveEquiv q surjective kernelTwo central rootX blocks b).val =
      algebraMapOf q b.val := by
  exact TypeBCentralKernelLocalBlockBinding.quotient_algebra_factor q surjective b.val

theorem primitiveEquiv_principal (central : q.ker ≤ Subgroup.center H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (blocks : NavarroCentralBlockPrinciple 2 k) (b : LiteralPrimitiveBlock k H)
    (principal : IsPrincipal b) :
    IsPrincipal (primitiveEquiv q surjective kernelTwo central rootX blocks b) :=
  (TypeBCentralKernelSpinFibreIdentification.primitiveBlockEquiv_principal_iff _ _).mpr
    ((TypeBCentralKernelBlockSource.blockEquiv_principal_iff
      q.ker kernelTwo central _ blocks b).mpr principal)

include surjective kernelTwo in
/-- Prime regular surjectivity is derived from the same quotient source. -/
theorem regular_surjective (regular : PrimeRegularQuotientLiftPrinciple.{0} 2) :
    Function.Surjective (PrimeRegularElement.map (p := 2) q) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective q surjective
  intro x
  obtain ⟨y, hy⟩ := regular H q.ker Nat.prime_two kernelTwo
    (PrimeRegularElement.map e.symm.toMonoidHom x)
  apply Exists.intro y
  apply Subtype.ext
  have h := congrArg (fun z : PrimeRegularElement (G := H ⧸ q.ker) 2 => e z.val) hy
  change q y.val = x.val
  change q y.val = e (e.symm x.val) at h
  exact h.trans (e.apply_symm_apply x.val)

theorem root_compatible
    (root : PrimeRegularRootEmbedding 2 k K H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (calibrationX : RootResidueCompatible Msys rootX) (V : FDRep k X) :
    Representation.BrauerRootLiftCompatibleAlong V.ρ rootX root q := by
  rw [eq_groupRoot_of_residue Msys H root calibration,
    eq_groupRoot_of_residue Msys X rootX calibrationX]
  exact groupRoot_compatible_along Msys V.ρ q

def kernelTrivial
    (root : PrimeRegularRootEmbedding 2 k K H)
    (kernel : Navarro232Principle 2 k) (phi : IBr root) :
    KernelTrivialIBrAlong q root := by
  refine ⟨phi, ?_⟩
  obtain ⟨V, hV, hchar⟩ := phi.property
  exact ⟨V, hV, hchar, kernel H q.ker Nat.prime_two kernelTwo V hV⟩

def brauerEquiv
    (root : PrimeRegularRootEmbedding 2 k K H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (calibrationX : RootResidueCompatible Msys rootX)
    (kernel : Navarro232Principle 2 k)
    (regular : PrimeRegularQuotientLiftPrinciple.{0} 2) : IBr rootX ≃ IBr root where
  toFun phi := (inflateToKernelTrivialIBrAlong q surjective root rootX
    (root_compatible Msys q root rootX calibration calibrationX) phi).val
  invFun phi := descendIBrAlong q surjective root rootX
    (kernelTrivial q kernelTwo root kernel phi)
  left_inv phi := by
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro x
    obtain ⟨y, hy⟩ := regular_surjective q surjective kernelTwo regular x
    have h := descendIBrAlong_pullback q surjective root rootX
      (root_compatible Msys q root rootX calibration calibrationX)
      (kernelTrivial q kernelTwo root kernel
        (inflateToKernelTrivialIBrAlong q surjective root rootX
          (root_compatible Msys q root rootX calibration calibrationX) phi).val)
    have hv := congrArg (fun c : PrimeRegularClassFunction K H 2 => c y) h
    change (descendIBrAlong q surjective root rootX
      (kernelTrivial q kernelTwo root kernel
        (inflateToKernelTrivialIBrAlong q surjective root rootX
          (root_compatible Msys q root rootX calibration calibrationX) phi).val)).val
        (PrimeRegularElement.map q y) = phi.val (PrimeRegularElement.map q y) at hv
    rw [hy] at hv
    exact hv
  right_inv phi := by
    apply Subtype.ext
    exact descendIBrAlong_pullback q surjective root rootX
      (root_compatible Msys q root rootX calibration calibrationX)
      (kernelTrivial q kernelTwo root kernel phi)

theorem brauerEquiv_value
    (root : PrimeRegularRootEmbedding 2 k K H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (calibrationX : RootResidueCompatible Msys rootX)
    (kernel : Navarro232Principle 2 k)
    (regular : PrimeRegularQuotientLiftPrinciple.{0} 2) (phi : IBr rootX) :
    (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi).val = PrimeRegularClassFunction.pullback q phi.val := rfl

theorem brauerEquiv_twist
    (root : PrimeRegularRootEmbedding 2 k K H)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (calibration : RootResidueCompatible Msys root)
    (calibrationX : RootResidueCompatible Msys rootX)
    (kernel : Navarro232Principle 2 k)
    (regular : PrimeRegularQuotientLiftPrinciple.{0} 2)
    (alpha : MulAut H) (beta : MulAut X)
    (square : ∀ h, q (alpha h) = beta (q h)) (phi : IBr rootX) :
    brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX kernel regular
      (IrreducibleBrauerCharacter.twist rootX phi beta) =
    IrreducibleBrauerCharacter.twist root
      (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
        kernel regular phi) alpha := by
  apply Subtype.ext
  exact NormalCoreLemma48SourceInstantiation.pullback_twist q alpha beta square phi.val

/-- Centrality of the actual normalizer kernel, without a quotient carrier. -/
theorem normalizer_kernel_central (central : q.ker ≤ Subgroup.center H)
    (W : CharacterWeight 2 K H) :
    (normalizerMap q W.subgroup).ker ≤
      Subgroup.center (Subgroup.normalizer (W.subgroup : Set H)) := by
  intro x hx
  have hq : q (x : H) = 1 := congrArg Subtype.val hx
  have hk : (x : H) ∈ q.ker := hq
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (central hk) (y : H)

end Surjection

section Fibres

variable {H X : Type} [Group H] [Finite H] [Group X] [Finite X]
  [HasEnoughRootsOfUnity K (Nat.card H)] [HasEnoughRootsOfUnity K (Nat.card X)]
  (Msys : ModularSystem 2 K O k)
  (q : H →* X) (surjective : Function.Surjective q) (kernelTwo : IsPGroup 2 q.ker)
  (central : q.ker ≤ Subgroup.center H)
  (root : PrimeRegularRootEmbedding 2 k K H)
  (rootX : PrimeRegularRootEmbedding 2 k K X)
  (calibration : RootResidueCompatible Msys root)
  (calibrationX : RootResidueCompatible Msys rootX)
  (RSpin : CoverWeightSource (k := k) (K := K) H)
  (SX : CoverWeightSource (k := k) (K := K) X)
  (b : LiteralPrimitiveBlock k H) (bX : LiteralPrimitiveBlock k X)
  (principal : IsPrincipal b) (principalX : IsPrincipal bX)
  (literalSpin : ∀ c, RSpin.operations.ambientBlockData.blockIdempotent c = c.val)
  (physicalX : PhysicalWeightCalibration Msys rootX SX bX)
  (blocks : NavarroCentralBlockPrinciple 2 k)

def principalEither (W : CharacterWeight 2 K H) : Prop :=
  RSpin.operations.induceToAmbient W = b ∨
    SX.operations.induceToAmbient (descend q surjective kernelTwo W) = bX

variable
  (spinFacts : ∀ W : CharacterWeight 2 K H,
    principalEither q surjective kernelTwo RSpin SX b bX W →
      NormalizerFacts Msys RSpin.operations W)
  (omegaFacts : ∀ W : CharacterWeight 2 K H, RSpin.operations.induceToAmbient W = b →
    NormalizerFacts Msys SX.operations (descend q surjective kernelTwo W))
  (navarro : ∀ (Y : Type) [Group Y] [Finite Y]
    [HasEnoughRootsOfUnity K (Nat.card Y)]
    (iota : PrimeRegularRootEmbedding 2 k K Y)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

include calibration calibrationX physicalX blocks spinFacts omegaFacts navarro central in
/-- Only the two actual local blocks for this independently guarded pair. -/
theorem normalizer_block_map
    (W : CharacterWeight 2 K H)
    (scope : principalEither q surjective kernelTwo RSpin SX b bX W) :
    algebraMapOf (normalizerMap q W.subgroup) (ownNormalizerBlock RSpin.operations W).val =
      (ownNormalizerBlock SX.operations (descend q surjective kernelTwo W)).val := by
  let WD := descend q surjective kernelTwo W
  let qN := normalizerMap q W.subgroup
  have hqN : Function.Surjective qN :=
    normalizerMap_surjective q surjective W.subgroup (kernel_le_radical q kernelTwo W)
  have hkN : IsPGroup 2 qN.ker := normalizerMap_ker_isPGroup q W.subgroup kernelTwo
  have hcN := normalizer_kernel_central q central W
  let rootU := localRoot Msys W
  let rootD := localRoot Msys WD
  let phiU := localReduction Msys navarro W
  let phiD := localReduction Msys navarro WD
  have reduceU := localReduction_value Msys navarro W
  have reduceD := localReduction_value Msys navarro WD
  have agreeU := localRoot_agrees Msys root calibration W
  have agreeD := localRoot_agrees Msys rootX calibrationX WD
  have hU := normalizerBlock_of_facts Msys root calibration RSpin.operations W
    (spinFacts W scope) rootU phiU agreeU reduceU
  have hD :
      NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        SX.operations WD.subgroup rootD phiD = ownNormalizerBlock SX.operations WD := by
    rcases scope with hSpin | hX
    · exact normalizerBlock_of_facts Msys rootX calibrationX SX.operations WD
        (omegaFacts W hSpin) rootD phiD agreeD reduceD
    · exact physicalX.normalizer_reduction WD hX rootD phiD agreeD reduceD
  have lifts : rootU.lift = rootD.lift :=
    roots_lift_eq Msys qN hqN hkN rootU rootD
      (localRoot_residue Msys W) (localRoot_residue Msys WD)
  have values : phiU.val = PrimeRegularClassFunction.pullback qN phiD.val := by
    ext x
    exact normalizer_reduction_quotient_square W q surjective kernelTwo
      rootU rootD phiU phiD reduceU reduceD x
  letI : Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer (W.subgroup : Set H))) :=
    (RSpin.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W.subgroup.map q) : Set X))) :=
    (SX.operations.inflatedNormalizerBlockData WD.subgroup).fintypeBlock
  letI : Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer (WD.subgroup : Set X))) :=
    (SX.operations.inflatedNormalizerBlockData WD.subgroup).fintypeBlock
  change block rootU (RSpin.operations.inflatedNormalizerBlockData W.subgroup).blocks phiU =
    ownNormalizerBlock RSpin.operations W at hU
  change block rootD (SX.operations.inflatedNormalizerBlockData WD.subgroup).blocks phiD =
    ownNormalizerBlock SX.operations WD at hD
  rw [← hU, ← hD]
  exact TypeBCentralKernelLocalBlockBinding.brauer_block_map qN hqN hkN hcN blocks
    rootU rootD (RSpin.operations.inflatedNormalizerBlockData W.subgroup).blocks
    (SX.operations.inflatedNormalizerBlockData WD.subgroup).blocks phiU phiD lifts values

/-- Literal block decomposition from the already stored allocation. -/
def literalDecomposition {Y : Type} [Group Y] [Finite Y]
    (S : CoverWeightSource (k := k) (K := K) Y)
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val) :
    letI := S.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k Y => c.val) := by
  letI := S.operations.ambientBlockData.fintypeBlock
  have allocation : S.operations.ambientBlockData.blockIdempotent =
      (fun c : LiteralPrimitiveBlock k Y => c.val) := funext literal
  rw [← allocation]
  exact S.operations.ambientBlockData.blocks

include principal principalX physicalX in
theorem principal_image :
    primitiveEquiv q surjective kernelTwo central rootX blocks b = bX := by
  letI := SX.operations.ambientBlockData.fintypeBlock
  exact TypeBCentralKernelPrincipalStability.principal_unique
    (literalDecomposition SX physicalX.literal) _ bX
    (primitiveEquiv_principal q surjective kernelTwo central rootX blocks b principal)
    principalX

include calibration calibrationX literalSpin physicalX spinFacts omegaFacts navarro in
/-- The ordinary-local proof induces the ambient block under direct q. -/
theorem raw_block_map
    (W : CharacterWeight 2 K H)
    (scope : principalEither q surjective kernelTwo RSpin SX b bX W) :
    SX.operations.rawWeightBlock (descend q surjective kernelTwo W) =
      primitiveEquiv q surjective kernelTwo central rootX blocks
        (RSpin.operations.rawWeightBlock W) := by
  let WD := descend q surjective kernelTwo W
  let U := Subgroup.normalizer (W.subgroup : Set H)
  let V := Subgroup.normalizer (WD.subgroup : Set X)
  let qN : U →* V := normalizerMap q W.subgroup
  have hker : q.ker ≤ W.subgroup := kernel_le_radical q kernelTwo W
  have hqN : Function.Surjective qN := normalizerMap_surjective q surjective W.subgroup hker
  have hNmap : U.map q = V :=
    map_normalizer_eq_of_surjective_of_ker_le q surjective W.subgroup hker
  have hpreimage : V.comap q = U := by
    rw [← hNmap]
    exact Subgroup.comap_map_eq_self (hker.trans W.subgroup.le_normalizer)
  have saturated : ∀ h : H, h ∈ U ↔ q h ∈ V := by
    intro h
    change h ∈ U ↔ h ∈ V.comap q
    rw [hpreimage]
  letI := RSpin.operations.ambientBlockData.fintypeBlock
  letI := SX.operations.ambientBlockData.fintypeBlock
  letI := (RSpin.operations.inflatedNormalizerBlockData W.subgroup).fintypeBlock
  letI := (SX.operations.inflatedNormalizerBlockData WD.subgroup).fintypeBlock
  have hup := inducedBlock_spec U
    (RSpin.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    RSpin.operations.ambientBlockData.catalogue (ownNormalizerBlock RSpin.operations W)
    (RSpin.operations.blockInductionDefined W)
  have physical : algebraMapOf q
      (RSpin.operations.ambientBlockData.blockIdempotent (RSpin.operations.rawWeightBlock W)) =
      SX.operations.ambientBlockData.blockIdempotent
        (primitiveEquiv q surjective kernelTwo central rootX blocks
          (RSpin.operations.rawWeightBlock W)) := by
    rw [literalSpin, physicalX.literal, primitiveEquiv_value]
  have localPhysical := normalizer_block_map Msys q surjective kernelTwo central
    root rootX calibration calibrationX RSpin SX b bX physicalX blocks
    spinFacts omegaFacts navarro W scope
  have hdown := blockInducesTo_map U V q surjective qN hqN (fun _ => rfl) saturated
    RSpin.operations.ambientBlockData.catalogue SX.operations.ambientBlockData.catalogue
    (RSpin.operations.inflatedNormalizerBlockData W.subgroup).catalogue
    (SX.operations.inflatedNormalizerBlockData WD.subgroup).catalogue
    (ownNormalizerBlock RSpin.operations W) (ownNormalizerBlock SX.operations WD)
    (RSpin.operations.rawWeightBlock W)
    (primitiveEquiv q surjective kernelTwo central rootX blocks
      (RSpin.operations.rawWeightBlock W))
    localPhysical physical hup (SX.operations.blockInductionDefined WD)
  exact (eq_inducedBlock_of_blockInducesTo V
    (SX.operations.inflatedNormalizerBlockData WD.subgroup).catalogue
    SX.operations.ambientBlockData.catalogue (ownNormalizerBlock SX.operations WD)
    (SX.operations.blockInductionDefined WD) hdown).symm

include central blocks calibration calibrationX principal principalX literalSpin physicalX
  spinFacts omegaFacts navarro in
theorem principal_weight_iff
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H)) :
    RSpin.weightBlock w = b ↔
      SX.weightBlock (conjugacyClassEquiv q surjective kernelTwo w) = bX := by
  refine Quotient.inductionOn w ?_
  intro w
  refine Quotient.inductionOn w ?_
  intro W
  change RSpin.operations.rawWeightBlock W = b ↔
    SX.operations.rawWeightBlock (descend q surjective kernelTwo W) = bX
  have image := principal_image Msys q surjective kernelTwo central rootX SX b bX
    principal principalX physicalX blocks
  constructor
  · intro h
    have mapped := raw_block_map Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX literalSpin physicalX blocks
      spinFacts omegaFacts navarro W (Or.inl h)
    rw [mapped, h, image]
  · intro h
    have mapped := raw_block_map Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX literalSpin physicalX blocks
      spinFacts omegaFacts navarro W (Or.inr h)
    apply (primitiveEquiv q surjective kernelTwo central rootX blocks).injective
    exact mapped.symm.trans (h.trans image.symm)

def principalWeightEquiv :
    CoverWeight RSpin b ≃ CoverWeight SX bX :=
  (conjugacyClassEquiv q surjective kernelTwo).subtypeEquiv
    (principal_weight_iff Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro)

theorem principalWeightEquiv_value (w : CoverWeight RSpin b) :
    (principalWeightEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro w).val = conjugacyClassEquiv q surjective kernelTwo w.val := rfl

variable (kernel : Navarro232Principle 2 k)
  (regular : PrimeRegularQuotientLiftPrinciple.{0} 2)

include central principal principalX literalSpin physicalX blocks in
theorem principal_brauer_iff (phi : IBr rootX) :
    Supported rootX bX phi ↔
      Supported root b (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi) := by
  letI := RSpin.operations.ambientBlockData.fintypeBlock
  letI := SX.operations.ambientBlockData.fintypeBlock
  let DU := literalDecomposition RSpin literalSpin
  let DX := literalDecomposition SX physicalX.literal
  have mapped := TypeBCentralKernelLocalBlockBinding.brauer_block_map q surjective
    kernelTwo central blocks root rootX DU DX (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi) phi
    (roots_lift_eq Msys q surjective kernelTwo root rootX calibration calibrationX)
    (brauerEquiv_value Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi)
  have h :
      primitiveEquiv q surjective kernelTwo central rootX blocks
        (block root DU (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi)) = block rootX DX phi := by
    apply Subtype.ext
    exact (primitiveEquiv_value q surjective kernelTwo central rootX blocks _).trans mapped
  have image := principal_image Msys q surjective kernelTwo central rootX SX b bX
    principal principalX physicalX blocks
  rw [supported_iff_block rootX DX, supported_iff_block root DU]
  constructor
  · intro hp
    apply (primitiveEquiv q surjective kernelTwo central rootX blocks).injective
    exact h.trans (hp.trans image.symm)
  · intro hp
    rw [hp, image] at h
    exact h.symm

/-- The supported Brauer equivalence uses the two literal principal blocks. -/
def principalBrauerEquiv : BrauerFibre rootX bX ≃ BrauerFibre root b :=
  (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular).subtypeEquiv
    (principal_brauer_iff Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular)

theorem principalBrauerEquiv_value (phi : BrauerFibre rootX bX) :
    (principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular phi).val.val = PrimeRegularClassFunction.pullback q phi.val.val := rfl

theorem principalBrauerEquiv_twist
    (alpha : MulAut H) (beta : MulAut X)
    (square : ∀ h, q (alpha h) = beta (q h))
    (phi phi' : BrauerFibre rootX bX)
    (same : phi'.val = IrreducibleBrauerCharacter.twist rootX phi.val beta) :
    (principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular phi').val =
      IrreducibleBrauerCharacter.twist root (principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular phi).val alpha := by
  change brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi'.val = IrreducibleBrauerCharacter.twist root (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular phi.val) alpha
  rw [same]
  exact brauerEquiv_twist Msys q surjective kernelTwo root rootX calibration calibrationX
    kernel regular alpha beta square phi.val

/-- The only matching argument is the already obtained matrix matching. -/
def liftedBijection (omegaX : BrauerFibre rootX bX ≃ CoverWeight SX bX) :
    BrauerFibre root b ≃ CoverWeight RSpin b :=
  (principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm.trans (omegaX.trans (principalWeightEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro).symm)

/-- The descended weight belongs to the very same branch of the matrix map. -/
theorem descended_liftedBijection
    (omegaX : BrauerFibre rootX bX ≃ CoverWeight SX bX) (theta : BrauerFibre root b) :
    conjugacyClassEquiv q surjective kernelTwo (liftedBijection Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro kernel regular omegaX theta).val =
      (omegaX ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta)).val := by
  exact congrArg Subtype.val ((principalWeightEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro).apply_symm_apply _)

theorem descendedBrauer_twist
    (alpha : MulAut H) (beta : MulAut X)
    (square : ∀ h, q (alpha h) = beta (q h))
    (theta theta' : BrauerFibre root b)
    (same : theta'.val = IrreducibleBrauerCharacter.twist root theta.val alpha) :
    ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta').val =
      IrreducibleBrauerCharacter.twist rootX ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta).val beta := by
  apply (brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular).injective
  rw [brauerEquiv_twist Msys q surjective kernelTwo root rootX
    calibration calibrationX kernel regular alpha beta square]
  have ht := congrArg Subtype.val ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).apply_symm_apply theta)
  have ht' := congrArg Subtype.val ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).apply_symm_apply theta')
  change brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta).val = theta.val at ht
  change brauerEquiv Msys q surjective kernelTwo root rootX calibration calibrationX
      kernel regular ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta').val = theta'.val at ht'
  rw [ht, ht', same]

theorem liftedBijection_twist
    (omegaX : BrauerFibre rootX bX ≃ CoverWeight SX bX)
    (alpha : MulAut H) (beta : MulAut X)
    (square : ∀ h, q (alpha h) = beta (q h))
    (equivariantX : ∀ phi phi' : BrauerFibre rootX bX,
      phi'.val = IrreducibleBrauerCharacter.twist rootX phi.val beta →
      (omegaX phi').val = CharacterWeight.rightTwistConjugacyClass beta (omegaX phi).val)
    (theta theta' : BrauerFibre root b)
    (same : theta'.val = IrreducibleBrauerCharacter.twist root theta.val alpha) :
    (liftedBijection Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro kernel regular omegaX theta').val =
      CharacterWeight.rightTwistConjugacyClass alpha (liftedBijection Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro kernel regular omegaX theta).val := by
  apply (conjugacyClassEquiv q surjective kernelTwo).injective
  rw [conjugacyClassEquiv_rightTwist q surjective kernelTwo alpha beta square]
  rw [descended_liftedBijection, descended_liftedBijection]
  exact equivariantX _ _
    (descendedBrauer_twist Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular alpha beta square theta theta' same)

theorem raw_match_descends
    (omegaX : BrauerFibre rootX bX ≃ CoverWeight SX bX)
    (theta : BrauerFibre root b) (Wraw : CharacterWeight 2 K H)
    (same : TypeBWeightCoveringSource.rawClass Wraw = (liftedBijection Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro kernel regular omegaX theta).val) :
    TypeBWeightCoveringSource.rawClass (descend q surjective kernelTwo Wraw) =
      (omegaX ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta)).val := by
  have h := congrArg (conjugacyClassEquiv q surjective kernelTwo) same
  change TypeBWeightCoveringSource.rawClass (descend q surjective kernelTwo Wraw) = _ at h
  exact h.trans (descended_liftedBijection Msys q surjective kernelTwo central root rootX
    calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
    spinFacts omegaFacts navarro kernel regular omegaX theta)

theorem raw_match_supported
    (omegaX : BrauerFibre rootX bX ≃ CoverWeight SX bX)
    (theta : BrauerFibre root b) (Wraw : CharacterWeight 2 K H)
    (same : TypeBWeightCoveringSource.rawClass Wraw = (liftedBijection Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro kernel regular omegaX theta).val) :
    RSpin.operations.induceToAmbient Wraw = b ∧
      SX.operations.induceToAmbient (descend q surjective kernelTwo Wraw) = bX := by
  have up := (liftedBijection Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      spinFacts omegaFacts navarro kernel regular omegaX theta).property
  have down := (omegaX ((principalBrauerEquiv Msys q surjective kernelTwo central root rootX
      calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
      kernel regular).symm theta)).property
  rw [← same] at up
  have sameDown := raw_match_descends Msys q surjective kernelTwo central root rootX
    calibration calibrationX RSpin SX b bX principal principalX literalSpin physicalX blocks
    spinFacts omegaFacts navarro kernel regular omegaX theta Wraw same
  rw [← sameDown] at down
  exact ⟨up, down⟩

end Fibres

end ModularRep.PaperProofs.TypeBPrincipalSpinReturnFibres


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
