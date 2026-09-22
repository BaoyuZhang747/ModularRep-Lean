import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.TypeBCentralKernelQuotientTripleTransport
import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification
import ModularRep.PaperProofs.TypeBPrincipalSpinReturnCarriers
import ModularRep.CentralCharacterCovering

/-!
# Finite-root transport of the same central-quotient pair

The ordinary local character is always the given raw weight's character.
Quotient-image block catalogues are transported from the existing lower
pair, rather than supplied as an additional source family. The only deep
transport inputs are the one-way Butterfly and MRR 3.14 interfaces.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBPrincipalSpinReturnPairs

open ModularRep CharacterWeight
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelButterflyCertificate
open TypeBCentralKernelPairSplittingBinding TypeBLocalReductionInstantiation

local instance finiteGroupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

section CatalogueTransport

variable {k X Y B I : Type} [Field k] [Group X] [Group Y]
  [Fintype B] [Fintype I]
  {allocation : B → k[X]}

/-- Reindex the same complete decomposition, without changing its idempotents. -/
def reindexDecomposition (D : BlockIdempotentDecomposition allocation) (e : I ≃ B) :
    BlockIdempotentDecomposition (fun i => allocation (e i)) where
  complete := {
    idem := fun i => (D.primitive (e i)).idempotent
    ortho := fun i j hij => D.complete.ortho (fun h => hij (e.injective h))
    complete := (e.sum_comp allocation).trans D.complete.complete
    central := fun i => (D.primitive (e i)).central }
  primitive := fun i => D.primitive (e i)

variable [IsAlgClosed k] [Fintype X]

/-- The source central characters, in the same reindexed coordinates. -/
def reindexCatalogue (D : BlockIdempotentDecomposition allocation) (e : I ≃ B)
    (C : BlockCentralCharacterCatalogue D) :
    BlockCentralCharacterCatalogue (reindexDecomposition D e) where
  centralCharacter i := C.centralCharacter (e i)
  delta_own i := C.delta_own (e i)
  delta_other i j hij := C.delta_other (e i) (e j) (fun h => hij (e.injective h))
  exhaustive := by
    intro lambda
    obtain ⟨b, hb⟩ := C.exhaustive lambda
    refine ⟨e.symm b, ?_⟩
    change C.centralCharacter (e (e.symm b)) = lambda
    rw [e.apply_symm_apply]
    exact hb

end CatalogueTransport

section PhysicalTransport

variable {k X Y : Type} [Field k] [IsAlgClosed k]
  [Group X] [Finite X] [Group Y] [Finite Y]

/-- An actual group equivalence transports the whole literal catalogue. -/
def physicalBlocksAlong (e : X ≃* Y) (D : PhysicalBlocks k X) : PhysicalBlocks k Y := by
  letI := D.blockFintype
  let eB := TypeBCentralKernelSpinFibreIdentification.primitiveBlockEquiv (k := k) e
  letI : Fintype (LiteralPrimitiveBlock k Y) := Fintype.ofEquiv _ eB
  let allocation : LiteralPrimitiveBlock k Y → k[Y] :=
    fun b => MonoidAlgebra.domCongr k k e (eB.symm b).val
  let blocks : BlockIdempotentDecomposition allocation :=
    reindexDecomposition (D.decomposition.alongMulEquiv e) eB.symm
  let catalogue : BlockCentralCharacterCatalogue blocks :=
    reindexCatalogue (D.decomposition.alongMulEquiv e) eB.symm
      (D.catalogue.alongMulEquiv e)
  have actual : allocation = fun b : LiteralPrimitiveBlock k Y => b.val := by
    funext b
    exact congrArg Subtype.val (eB.apply_symm_apply b)
  exact {
    blockFintype := inferInstance
    decomposition := actual ▸ blocks
    catalogue := Eq.ndrec
      (motive := fun allocation' =>
        ∀ decomposition : BlockIdempotentDecomposition allocation',
          BlockCentralCharacterCatalogue decomposition)
      (fun _ => catalogue) actual _ }

end PhysicalTransport

section SubgroupTransport

variable {X Y : Type} [Group X] [Group Y]

/-- Restrict one actual equivalence using a proved membership square. -/
def subgroupEquiv (e : X ≃* Y) (S : Subgroup X) (T : Subgroup Y)
    (membership : ∀ x, x ∈ S ↔ e x ∈ T) : S ≃* T where
  toFun x := ⟨e x, (membership x).mp x.property⟩
  invFun y := ⟨e.symm y, (membership (e.symm y)).mpr (by
    simpa only [e.apply_symm_apply] using y.property)⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y
  map_mul' x y := by apply Subtype.ext; exact e.map_mul x y

@[simp] theorem subgroupEquiv_value (e : X ≃* Y) (S : Subgroup X) (T : Subgroup Y)
    (membership : ∀ x, x ∈ S ↔ e x ∈ T) (x : S) :
    (subgroupEquiv e S T membership x).val = e x := rfl

variable (e : X ≃* Y) (N1 U1 : Subgroup X) (N2 U2 : Subgroup Y)
  (base : ∀ x, x ∈ N1 ↔ e x ∈ N2)
  (localMembership : ∀ x, x ∈ U1 ↔ e x ∈ U2)

def baseEquiv : N1 ≃* N2 := subgroupEquiv e N1 N2 base

def localAmbientEquiv : U1 ≃* U2 := subgroupEquiv e U1 U2 localMembership

def localBaseEquiv : localBase N1 U1 ≃* localBase N2 U2 :=
  subgroupEquiv (localAmbientEquiv e U1 U2 localMembership)
    (localBase N1 U1) (localBase N2 U2) (fun x => base x.val)

theorem base_anchor (x : N1) :
    e x.val = (baseEquiv e N1 N2 base x).val := rfl

theorem local_anchor (x : localBase N1 U1) :
    localToBase N2 U2 (localBaseEquiv e N1 U1 N2 U2 base localMembership x) =
      baseEquiv e N1 N2 base (localToBase N1 U1 x) := rfl

include localMembership in
theorem local_image : U1.map e.toMonoidHom = U2 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (localMembership x).mp hx
  · intro hy
    refine ⟨e.symm y, (localMembership (e.symm y)).mpr ?_, e.apply_symm_apply y⟩
    simpa only [e.apply_symm_apply] using hy

end SubgroupTransport

section FamilyTransport

variable {k X Y : Type} [Field k] [IsAlgClosed k]
  [Group X] [Finite X] [Group Y] [Finite Y]
  (e : X ≃* Y) (N1 U1 : Subgroup X) (N2 U2 : Subgroup Y)
  (base : ∀ x, x ∈ N1 ↔ e x ∈ N2)
  (localMembership : ∀ x, x ∈ U1 ↔ e x ∈ U2)

/-- Every intermediate catalogue comes from the corresponding source subgroup. -/
def physicalFamilyAlong (D : PhysicalBlockFamily (k := k) N1 U1) :
    PhysicalBlockFamily (k := k) N2 U2 where
  base := physicalBlocksAlong (baseEquiv e N1 N2 base) D.base
  localData := physicalBlocksAlong (localBaseEquiv e N1 U1 N2 U2 base localMembership) D.localData
  intermediate J hNJ :=
    physicalBlocksAlong (subgroupEquiv e (J.comap e.toMonoidHom) J (fun _ => Iff.rfl))
      (D.intermediate (J.comap e.toMonoidHom) (fun x hx => hNJ ((base x).mp hx)))
  localIntermediateData J hNJ :=
    physicalBlocksAlong
      (subgroupEquiv
        (subgroupEquiv e (J.comap e.toMonoidHom) J (fun _ => Iff.rfl))
        (localIntermediate U1 (J.comap e.toMonoidHom)) (localIntermediate U2 J)
        (fun x => localMembership x.val))
      (D.localIntermediateData (J.comap e.toMonoidHom)
        (fun x hx => hNJ ((base x).mp hx)))

end FamilyTransport

section TripleTransport

variable {p : ℕ} {k K X Y : Type} [Field k] [Field K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X] [Group Y] [Finite Y]
  (e : X ≃* Y) (N1 U1 : Subgroup X) (N2 U2 : Subgroup Y)
  [N1.Normal] [N2.Normal]
  (base : ∀ x, x ∈ N1 ↔ e x ∈ N2)
  (localMembership : ∀ x, x ∈ U1 ↔ e x ∈ U2)
  (D : TripleData (p := p) (k := k) (K := K) N1 U1)

/-- The actual source roots and complete catalogues in target coordinates. -/
def tripleDataAlong : TripleData (p := p) (k := k) (K := K) N2 U2 :=
  withPrescribedRoots N2 U2 (D.ambientRoot.alongMulEquiv e)
    (D.base.iota.alongMulEquiv (baseEquiv e N1 N2 base))
    (D.localData.iota.alongMulEquiv (localBaseEquiv e N1 U1 N2 U2 base localMembership))
    (fun z => (alongMulEquiv_agrees D.ambientRoot D.base.iota
      (baseEquiv e N1 N2 base) D.baseRoots z).trans
        (D.ambientRoot.alongMulEquiv_lift e _).symm)
    (fun z => (alongMulEquiv_agrees D.ambientRoot D.localData.iota
      (localBaseEquiv e N1 U1 N2 U2 base localMembership) D.localRoots z).trans
        (D.ambientRoot.alongMulEquiv_lift e _).symm)
    (physicalFamilyAlong e N1 U1 N2 U2 base localMembership {
      base := D.base.blocks
      localData := D.localData.blocks
      intermediate J hNJ := (D.intermediate J hNJ).blocks
      localIntermediateData J hNJ := (D.localIntermediateData J hNJ).blocks })

def thetaAlong (theta : IBr D.base.iota) :
    IBr (tripleDataAlong e N1 U1 N2 U2 base localMembership D).base.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv D.base.iota
    (baseEquiv e N1 N2 base) theta

def phiAlong (phi : IBr D.localData.iota) :
    IBr (tripleDataAlong e N1 U1 N2 U2 base localMembership D).localData.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv D.localData.iota
    (localBaseEquiv e N1 U1 N2 U2 base localMembership) phi

/-- Transport an existing full witness; every target catalogue is constructed. -/
theorem witnessAlong (theta : IBr D.base.iota) (phi : IBr D.localData.iota)
    (witness : BlockTripleWitness D theta phi)
    (butterfly : ButterflyCertificate p k K) :
    Nonempty (BlockTripleWitness (tripleDataAlong e N1 U1 N2 U2 base localMembership D)
      (thetaAlong e N1 U1 N2 U2 base localMembership D theta)
      (phiAlong e N1 U1 N2 U2 base localMembership D phi)) := by
  apply TypeBCentralKernelQuotientTripleTransport.transfer_with_local_image
    N1 N2 U1 U2 e (baseEquiv e N1 N2 base)
    (base_anchor e N1 N2 base) (local_image e U1 U2 localMembership)
    (localBaseEquiv e N1 U1 N2 U2 base localMembership)
    (local_anchor e N1 U1 N2 U2 base localMembership) D
    (tripleDataAlong e N1 U1 N2 U2 base localMembership D) theta phi witness
    (thetaAlong e N1 U1 N2 U2 base localMembership D theta)
    (phiAlong e N1 U1 N2 U2 base localMembership D phi)
  · intro z _ _
    exact (D.ambientRoot.alongMulEquiv_lift e _).symm
  · exact funext (D.base.iota.alongMulEquiv_lift (baseEquiv e N1 N2 base))
  · exact funext (D.localData.iota.alongMulEquiv_lift
      (localBaseEquiv e N1 U1 N2 U2 base localMembership))
  · rfl
  · rfl
  · exact butterfly

end TripleTransport

section FiniteReduction

variable {p : ℕ} {K O k H X : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group H] [Finite H] [Group X] [Finite X]
  (Msys : ModularSystem p K O k)
  [HasEnoughRootsOfUnity K (Nat.card H)]
  [HasEnoughRootsOfUnity K (Nat.card X)]
  (navarro : ∀ (Y : Type) [Group Y] [Finite Y]
    [HasEnoughRootsOfUnity K (Nat.card Y)]
    (iota : PrimeRegularRootEmbedding p k K Y)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The normalizer character is the inflation of this raw weight's reduction. -/
def normalizerCharacter (W : CharacterWeight p K H) :
    IBr (TypeBCentralKernelLocalReduction.normalizerRoot W (quotientRoot Msys W)) :=
  TypeBCentralKernelLocalReduction.inflatedReduction W (quotientRoot Msys W)
    (quotientReduction Msys W navarro)

theorem normalizerCharacter_value (W : CharacterWeight p K H) :
    NormalizerInflatedReduction W.subgroup W.localCharacter
      (TypeBCentralKernelLocalReduction.normalizerRoot W (quotientRoot Msys W))
      (normalizerCharacter Msys navarro W) :=
  TypeBCentralKernelLocalReduction.inflatedReduction_value W (quotientRoot Msys W)
    (quotientReduction Msys W navarro) (quotientReduction_value Msys W navarro)

/-- Ordinary descent proves the full finite-root normalizer inflation square. -/
theorem normalizerCharacter_quotient (q : H →* X) (surjective : Function.Surjective q)
    (kernel : IsPGroup p q.ker) (W : CharacterWeight p K H)
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set H)) p) :
    (normalizerCharacter Msys navarro W).val x =
      (normalizerCharacter Msys navarro
        (TypeBCentralKernelWeightTransport.descend q surjective kernel W)).val
          (PrimeRegularElement.map
            (ModularRep.normalizerMap q W.subgroup) x) :=
  TypeBCentralKernelLocalReduction.normalizer_reduction_quotient_square W
    q surjective kernel _ _ _ _
    (normalizerCharacter_value Msys navarro W)
    (normalizerCharacter_value Msys navarro
      (TypeBCentralKernelWeightTransport.descend q surjective kernel W)) x

end FiniteReduction

section CanonicalCharacters

open TypeBAllRankPrincipalCriterionSpathSource

variable {K O k H : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K] [Group H] [Finite H]
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K H)
  (calibration : RootResidueCompatible Msys root)
  (theta : IBr root) (W : CharacterWeight 2 K H)
  (hUT : weightInertia W ≤ characterInertia root theta)
  (blocks : PairBlocks root theta W)

abbrev canonicalData :=
  TypeBCentralKernelConjugatePairBinding.tripleData
    (canonicalBase H) (embeddedRoot root) (embeddedCharacter root theta)
    (embeddedWeight W) hUT
    (pairData Msys (canonicalBase H) (embeddedRoot root)
      (embeddedRoot_residue Msys root calibration) (embeddedCharacter root theta)
      (embeddedWeight W) hUT blocks)

abbrev canonicalTheta : IBr (canonicalData Msys root calibration theta W hUT blocks).base.iota :=
  TypeBCentralKernelTripleCharacters.baseBrauer
    (canonicalBase H) (embeddedRoot root) (embeddedCharacter root theta)

def canonicalBaseEquiv : H ≃* TypeBCentralKernelTripleCarriers.inside
    (canonicalBase H) (characterInertia root theta) :=
  (TypeBAllRankPrincipalCriterionSpathSource.baseEquiv H).trans
    (TypeBCentralKernelTripleCharacters.baseEquiv
      (canonicalBase H) (embeddedRoot root) (embeddedCharacter root theta))

theorem canonicalTheta_value (x : PrimeRegularElement
    (G := TypeBCentralKernelTripleCarriers.inside (canonicalBase H)
      (characterInertia root theta)) 2) :
    (canonicalTheta Msys root calibration theta W hUT blocks).val x =
      theta.val (PrimeRegularElement.map
        (canonicalBaseEquiv root theta).symm.toMonoidHom x) := rfl

/-- The normalizer equivalence retains the actual embedded raw subgroup. -/
def embeddedNormalizerEquiv :
    Subgroup.normalizer (W.subgroup : Set H) ≃*
      Subgroup.normalizer ((embeddedWeight W).subgroup : Set (canonicalBase H)) :=
  ((TypeBAllRankPrincipalCriterionSpathSource.baseEquiv H).subgroupMap
    (Subgroup.normalizer (W.subgroup : Set H))).trans
      (MulEquiv.subgroupCongr
        (Subgroup.map_equiv_normalizer_eq W.subgroup
          (TypeBAllRankPrincipalCriterionSpathSource.baseEquiv H)))

def canonicalNormalizerEquiv :
    Subgroup.normalizer (W.subgroup : Set H) ≃*
      localBase
        (TypeBCentralKernelTripleCarriers.inside (canonicalBase H) (characterInertia root theta))
        (TypeBCentralKernelTripleCarriers.inside (weightInertia W) (characterInertia root theta)) :=
  (embeddedNormalizerEquiv W).trans
    (TypeBCentralKernelTripleCharacters.localEquiv
      (canonicalBase H) (embeddedRoot root) (embeddedCharacter root theta)
      (embeddedWeight W) hUT)

@[simp] theorem canonicalBaseEquiv_value (x : H) :
    (canonicalBaseEquiv root theta x).val.val = SemidirectProduct.inl x := rfl

@[simp] theorem canonicalNormalizerEquiv_value
    (x : Subgroup.normalizer (W.subgroup : Set H)) :
    (canonicalNormalizerEquiv root theta W hUT x).val.val.val =
      SemidirectProduct.inl x.val := rfl

theorem canonicalBaseEquiv_symm_value
    (x : TypeBCentralKernelTripleCarriers.inside (canonicalBase H) (characterInertia root theta)) :
    SemidirectProduct.inl ((canonicalBaseEquiv root theta).symm x) = x.val.val :=
  congrArg (fun y => y.val.val) ((canonicalBaseEquiv root theta).apply_symm_apply x)

theorem canonicalNormalizerEquiv_symm_value
    (x : localBase
      (TypeBCentralKernelTripleCarriers.inside (canonicalBase H) (characterInertia root theta))
      (TypeBCentralKernelTripleCarriers.inside (weightInertia W) (characterInertia root theta))) :
    SemidirectProduct.inl ((canonicalNormalizerEquiv root theta W hUT).symm x).val =
      x.val.val.val :=
  congrArg (fun y => y.val.val.val)
    ((canonicalNormalizerEquiv root theta W hUT).apply_symm_apply x)

variable [HasEnoughRootsOfUnity K (Nat.card H)]
  (navarro : ∀ (Y : Type) [Group Y] [Finite Y]
    [HasEnoughRootsOfUnity K (Nat.card Y)]
    (iota : PrimeRegularRootEmbedding 2 k K Y)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

def canonicalPhi : IBr (canonicalData Msys root calibration theta W hUT blocks).localData.iota := by
  letI := embeddedOrdinaryRoots (K := K) (Y := H)
  exact TypeBCentralKernelPairSplittingBinding.localCharacter
    Msys (canonicalBase H) (embeddedRoot root)
    (embeddedRoot_residue Msys root calibration) (embeddedCharacter root theta)
    (embeddedWeight W) hUT navarro blocks

/-- The pair's local Brauer value is the original raw weight's ordinary value. -/
theorem canonicalPhi_value (x : PrimeRegularElement
    (G := localBase
      (TypeBCentralKernelTripleCarriers.inside (canonicalBase H) (characterInertia root theta))
      (TypeBCentralKernelTripleCarriers.inside (weightInertia W) (characterInertia root theta))) 2) :
    (canonicalPhi Msys root calibration theta W hUT blocks navarro).val x =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup
        ((canonicalNormalizerEquiv root theta W hUT).symm x.val)) := by
  letI := embeddedOrdinaryRoots (K := K) (Y := H)
  rw [show (canonicalPhi Msys root calibration theta W hUT blocks navarro).val x =
      (embeddedWeight W).localCharacter
        (TypeBCentralKernelWeightTransport.localMk (embeddedWeight W).subgroup
          ((TypeBCentralKernelTripleCharacters.localEquiv
            (canonicalBase H) (embeddedRoot root) (embeddedCharacter root theta)
            (embeddedWeight W) hUT).symm x.val)) from
    (TypeBCentralKernelPairSplittingBinding.localCharacter_reduction
      Msys (canonicalBase H) (embeddedRoot root)
      (embeddedRoot_residue Msys root calibration) (embeddedCharacter root theta)
      (embeddedWeight W) hUT navarro blocks x).symm]
  apply TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv_localCharacter
    (TypeBAllRankPrincipalCriterionSpathSource.baseEquiv H) W
  have h := congrArg Subtype.val
    ((embeddedNormalizerEquiv W).apply_symm_apply
      ((TypeBCentralKernelTripleCharacters.localEquiv
        (canonicalBase H) (embeddedRoot root) (embeddedCharacter root theta)
        (embeddedWeight W) hUT).symm x.val))
  exact h

end CanonicalCharacters

section SamePair

open TypeBAllRankPrincipalCriterionSpathSource TypeBPrincipalSpinReturnCarriers
open TypeBCentralKernelTripleCarriers TypeBModularGroupRootBinding

variable {K O k X Y : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Group X] [Finite X] [Group Y] [Finite Y]
  (q : X →* Y) (surjective : Function.Surjective q) (kernelTwo : IsPGroup 2 q.ker)
  (rho : MulAut X ≃* MulAut Y)
  (square : ∀ (alpha : MulAut X) (x : X), rho alpha (q x) = q (alpha x))
  (rootX : PrimeRegularRootEmbedding 2 k K X)
  (rootY : PrimeRegularRootEmbedding 2 k K Y)
  (theta : IBr rootX) (thetaBar : IBr rootY)
  (values : theta.val = PrimeRegularClassFunction.pullback q thetaBar.val)
  (regular : Function.Surjective (PrimeRegularElement.map (p := 2) q))

local notation "fA" => ambientMap q rho square
local notation "TI" => characterInertia rootX theta
local notation "TB" => characterInertia rootY thetaBar
local notation "P" => MonoidHom.ker (ambientMap q rho square)
local notation "Z" => inside (MonoidHom.ker (ambientMap q rho square)) (characterInertia rootX theta)
local notation "NX" => inside (canonicalBase X) (characterInertia rootX theta)
local notation "NY" => inside (canonicalBase Y) (characterInertia rootY thetaBar)
local notation "NQ" =>
  Subgroup.map
    (QuotientGroup.mk' (inside (MonoidHom.ker (ambientMap q rho square)) (characterInertia rootX theta)))
    (inside (canonicalBase X) (characterInertia rootX theta))

include kernelTwo in
theorem ambientKernel_isTwoGroup : IsPGroup 2 (ambientMap q rho square).ker := by
  rw [ambientMap_ker]
  exact kernelTwo.map SemidirectProduct.inl

def pairQuotientEquiv : (TI ⧸ Z) ≃* TB :=
  subgroupQuotientEquiv (ambientMap q rho square)
    (ambientMap_surjective q rho square surjective) (ambientMap q rho square).ker rfl
    (characterInertia rootX theta) (characterInertia rootY thetaBar)
    (characterInertia_comap q rho square rootX rootY theta thetaBar values regular)

theorem pairQuotientEquiv_mk_value (t : TI) :
    (pairQuotientEquiv q surjective rho square rootX rootY theta thetaBar values regular
      (QuotientGroup.mk' Z t)).val = fA t.val := rfl

theorem pairBaseMembership (x : TB) :
    x ∈ NY ↔
      (pairQuotientEquiv q surjective rho square rootX rootY theta thetaBar values regular).symm x ∈ NQ := by
  rw [← subgroupQuotient_image fA (ambientMap_surjective q rho square surjective) P rfl
    TI TB (characterInertia_comap q rho square rootX rootY theta thetaBar values regular)
    (canonicalBase X) (canonicalBase Y) (canonicalBase_comap q rho square).symm]
  exact Subgroup.mem_map_equiv

variable (W : CharacterWeight 2 K X)
  (hUTbar : weightInertia (TypeBCentralKernelWeightTransport.descend q surjective kernelTwo W) ≤
    characterInertia rootY thetaBar)

local notation "WB" => TypeBCentralKernelWeightTransport.descend q surjective kernelTwo W
local notation "UX" => inside (weightInertia W) (characterInertia rootX theta)
local notation "UY" => inside
  (weightInertia (TypeBCentralKernelWeightTransport.descend q surjective kernelTwo W))
  (characterInertia rootY thetaBar)
local notation "UQ" =>
  Subgroup.map
    (QuotientGroup.mk' (inside (MonoidHom.ker (ambientMap q rho square)) (characterInertia rootX theta)))
    (inside (weightInertia W) (characterInertia rootX theta))

include rho square values regular hUTbar in
theorem pairInclusion : weightInertia W ≤ characterInertia rootX theta := by
  rw [weightInertia_comap q rho square surjective kernelTwo W,
    characterInertia_comap q rho square rootX rootY theta thetaBar values regular]
  exact Subgroup.comap_mono hUTbar

theorem pairLocalMembership (x : TB) :
    x ∈ UY ↔
      (pairQuotientEquiv q surjective rho square rootX rootY theta thetaBar values regular).symm x ∈ UQ := by
  rw [← subgroupQuotient_image fA (ambientMap_surjective q rho square surjective) P rfl
    TI TB (characterInertia_comap q rho square rootX rootY theta thetaBar values regular)
    (weightInertia W) (weightInertia WB)
    (weightInertia_comap q rho square surjective kernelTwo W)]
  exact Subgroup.mem_map_equiv

local notation "eQ" =>
  MulEquiv.symm (pairQuotientEquiv q surjective rho square rootX rootY theta thetaBar values regular)
local notation "baseQ" => pairBaseMembership q surjective rho square rootX rootY theta thetaBar values regular
local notation "localQ" => pairLocalMembership q surjective kernelTwo rho square rootX rootY theta thetaBar values regular W
local notation "upInclusion" => pairInclusion q surjective kernelTwo rho square rootX rootY theta thetaBar values regular W hUTbar

theorem pairBase_projection (x : NX) :
    ((baseEquiv eQ NY NQ baseQ).symm (quotientSubgroupMap Z NX x)).val.val =
      fA x.val.val := by
  change (pairQuotientEquiv q surjective rho square rootX rootY theta thetaBar values regular
    (QuotientGroup.mk' Z x.val)).val = _
  exact pairQuotientEquiv_mk_value q surjective rho square rootX rootY theta thetaBar values regular x.val

theorem pairLocal_projection (x : localBase NX UX) :
    ((localBaseEquiv eQ NY UY NQ UQ baseQ localQ).symm
      (quotientLocalMap Z NX UX x)).val.val.val = fA x.val.val.val := by
  change (pairQuotientEquiv q surjective rho square rootX rootY theta thetaBar values regular
    (QuotientGroup.mk' Z x.val.val)).val = _
  exact pairQuotientEquiv_mk_value q surjective rho square rootX rootY theta thetaBar values regular x.val.val

variable (Msys : ModularSystem 2 K O k)
  (calibrationX : RootResidueCompatible Msys rootX)
  (calibrationY : RootResidueCompatible Msys rootY)
  [HasEnoughRootsOfUnity K (Nat.card X)] [HasEnoughRootsOfUnity K (Nat.card Y)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding 2 k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (blocksX : PairBlocks rootX theta W)
  (blocksY : PairBlocks rootY thetaBar
    (TypeBCentralKernelWeightTransport.descend q surjective kernelTwo W))

local notation "DX" => canonicalData Msys rootX calibrationX theta W upInclusion blocksX
local notation "DY" => canonicalData Msys rootY calibrationY thetaBar WB hUTbar blocksY
local notation "thetaX" => canonicalTheta Msys rootX calibrationX theta W upInclusion blocksX
local notation "thetaY" => canonicalTheta Msys rootY calibrationY thetaBar WB hUTbar blocksY
local notation "phiX" => canonicalPhi Msys rootX calibrationX theta W upInclusion blocksX navarro
local notation "phiY" => canonicalPhi Msys rootY calibrationY thetaBar WB hUTbar blocksY navarro

/-- Quotient-image data are built from the same lower pair's complete catalogues. -/
def quotientPairData : TripleData (p := 2) (k := k) (K := K) NQ UQ :=
  tripleDataAlong eQ NY UY NQ UQ baseQ localQ DY

def quotientPairTheta : IBr
    (quotientPairData q surjective kernelTwo rho square rootX rootY theta thetaBar
      values regular W hUTbar Msys calibrationY blocksY).base.iota :=
  thetaAlong eQ NY UY NQ UQ baseQ localQ DY thetaY

def quotientPairPhi : IBr
    (quotientPairData q surjective kernelTwo rho square rootX rootY theta thetaBar
      values regular W hUTbar Msys calibrationY blocksY).localData.iota :=
  phiAlong eQ NY UY NQ UQ baseQ localQ DY phiY

local notation "DQ" => quotientPairData q surjective kernelTwo rho square rootX rootY theta thetaBar values regular W hUTbar Msys calibrationY blocksY
local notation "thetaQ" => quotientPairTheta q surjective kernelTwo rho square rootX rootY theta thetaBar values regular W hUTbar Msys calibrationY blocksY
local notation "phiQ" => quotientPairPhi q surjective kernelTwo rho square rootX rootY theta thetaBar values regular W hUTbar Msys calibrationY navarro blocksY

theorem quotientPair_baseInflation (x : PrimeRegularElement (G := NX) 2) :
    (thetaX).val x = (thetaQ).val (PrimeRegularElement.map (quotientSubgroupMap Z NX) x) := by
  let y : NY := (baseEquiv eQ NY NQ baseQ).symm (quotientSubgroupMap Z NX x.val)
  have point : q ((canonicalBaseEquiv rootX theta).symm x.val) =
      (canonicalBaseEquiv rootY thetaBar).symm y := by
    apply SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut Y))
    calc
      _ = fA (SemidirectProduct.inl ((canonicalBaseEquiv rootX theta).symm x.val)) :=
        (ambientMap_inl q rho square _).symm
      _ = fA x.val.val.val := congrArg fA (canonicalBaseEquiv_symm_value rootX theta x.val)
      _ = y.val.val := (pairBase_projection q surjective rho square rootX rootY theta thetaBar values regular x.val).symm
      _ = _ := (canonicalBaseEquiv_symm_value rootY thetaBar y).symm
  change (thetaX).val x = (thetaY).val
    (PrimeRegularElement.map (baseEquiv eQ NY NQ baseQ).symm.toMonoidHom
      (PrimeRegularElement.map (quotientSubgroupMap Z NX) x))
  rw [canonicalTheta_value, canonicalTheta_value, values]
  exact congrArg thetaBar.val (Subtype.ext point)

theorem quotientPair_localInflation (x : PrimeRegularElement (G := localBase NX UX) 2) :
    (phiX).val x = (phiQ).val (PrimeRegularElement.map (quotientLocalMap Z NX UX) x) := by
  let y : localBase NY UY := (localBaseEquiv eQ NY UY NQ UQ baseQ localQ).symm
    (quotientLocalMap Z NX UX x.val)
  have point : q ((canonicalNormalizerEquiv rootX theta W upInclusion).symm x.val).val =
      ((canonicalNormalizerEquiv rootY thetaBar WB hUTbar).symm y).val := by
    apply SemidirectProduct.inl_injective (φ := MonoidHom.id (MulAut Y))
    calc
      _ = fA (SemidirectProduct.inl
          ((canonicalNormalizerEquiv rootX theta W upInclusion).symm x.val).val) :=
        (ambientMap_inl q rho square _).symm
      _ = fA x.val.val.val.val := congrArg fA
        (canonicalNormalizerEquiv_symm_value rootX theta W upInclusion x.val)
      _ = y.val.val.val :=
        (pairLocal_projection q surjective kernelTwo rho square rootX rootY theta thetaBar
          values regular W x.val).symm
      _ = _ := (canonicalNormalizerEquiv_symm_value rootY thetaBar WB hUTbar y).symm
  change (phiX).val x = (phiY).val
    (PrimeRegularElement.map (localBaseEquiv eQ NY UY NQ UQ baseQ localQ).symm.toMonoidHom
      (PrimeRegularElement.map (quotientLocalMap Z NX UX) x))
  rw [canonicalPhi_value, canonicalPhi_value]
  exact (TypeBCentralKernelWeightTransport.descend_localCharacter q surjective kernelTwo W
    ((canonicalNormalizerEquiv rootX theta W upInclusion).symm x.val)
    ((canonicalNormalizerEquiv rootY thetaBar WB hUTbar).symm y) point).symm

theorem quotientPair_ambientRoots
    (z : rootsOfUnity (primeRegularExponent 2 (TI ⧸ Z)) k) :
    (DQ).ambientRoot.lift ((z : kˣ) : k) = (DX).ambientRoot.lift ((z : kˣ) : k) := by
  have exp : primeRegularExponent 2 TI = primeRegularExponent 2 TB :=
    exponent_surjection
      (subgroupProjection fA TI TB
        (characterInertia_comap q rho square rootX rootY theta thetaBar values regular))
      (subgroupProjection_surjective fA (ambientMap_surjective q rho square surjective)
        TI TB (characterInertia_comap q rho square rootX rootY theta thetaBar values regular))
      (by decide : Nat.Prime 2) (by
        rw [subgroupProjection_ker fA P rfl TI TB
          (characterInertia_comap q rho square rootX rootY theta thetaBar values regular)]
        exact (ambientKernel_isTwoGroup q kernelTwo rho square).comap_subtype)
  change ((groupRoot Msys TB).alongMulEquiv eQ).lift ((z : kˣ) : k) =
    (groupRoot Msys TI).lift ((z : kˣ) : k)
  rw [PrimeRegularRootEmbedding.alongMulEquiv_lift]
  exact congrFun (TypeBPrincipalRootLiftBinding.groupRoot_lift_eq_of_exponent_eq Msys exp.symm) _

/-- The lower witness is an internal premise obtained from the same Omega match.
All quotient-image characters, catalogues and inflation equations are constructed. -/
theorem samePair_return
    (butterfly : ButterflyCertificate 2 k K)
    (mrr314 : Lemma314Certificate 2 k K)
    (witness : CanonicalPairWitness Msys rootY calibrationY thetaBar WB hUTbar navarro blocksY) :
    Nonempty (CanonicalPairWitness Msys rootX calibrationX theta W upInclusion navarro blocksX) := by
  have quotientWitness : Nonempty (BlockTripleWitness DQ thetaQ phiQ) :=
    witnessAlong eQ NY UY NQ UQ baseQ localQ DY thetaY phiY witness butterfly
  have kernelBase : Z ≤ NX := by
    apply Subgroup.comap_mono
    rw [← canonicalBase_comap q rho square]
    exact Subgroup.ker_le_comap fA (canonicalBase Y)
  have kernelLocal : Z ≤ UX := by
    apply Subgroup.comap_mono
    rw [weightInertia_comap q rho square surjective kernelTwo W]
    exact Subgroup.ker_le_comap fA (weightInertia WB)
  exact mrr314.inflate TI NX UX Z kernelBase kernelLocal DX DQ thetaX phiX thetaQ phiQ
    (quotientPair_ambientRoots q surjective kernelTwo rho square rootX rootY theta thetaBar
      values regular W hUTbar Msys calibrationX calibrationY blocksX blocksY)
    (quotientPair_baseInflation q surjective kernelTwo rho square rootX rootY theta thetaBar
      values regular W hUTbar Msys calibrationX calibrationY blocksX blocksY)
    (quotientPair_localInflation q surjective kernelTwo rho square rootX rootY theta thetaBar
      values regular W hUTbar Msys calibrationX calibrationY navarro blocksX blocksY)
    quotientWitness

end SamePair

end ModularRep.PaperProofs.TypeBPrincipalSpinReturnPairs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
