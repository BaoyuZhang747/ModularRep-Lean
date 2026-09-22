import ModularRep.PaperProofs.TypeBBSCentralCharacterQuotient
import ModularRep.PaperProofs.TypeBCentralKernelConjugateTripleTransport

/-!
# The complete pair on the computed central quotient

The kernel is computed from the original character and mapped into its
actual inertia. Centrelessness proves that this subgroup is bottom. The
ambient, base and local maps below are restrictions of its projection.
The existing complete pair is transported through these maps by the
accepted one-way Butterfly certificate, including every intermediate
character fibre and specified block clause.

Both specified catalogue families remain explicit on their literal groups.
The target roots are transported from the same modular system and the
local character remains the transported reduction of the original weight's
own ordinary character. This construction supplies no honest extensions.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBBSCentralQuotientPairTransport

open ModularRep
open TypeBCentralKernelInertia TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelButterflyCertificate TypeBLocalReductionInstantiation

variable {p : ℕ} {K O k A : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (G : Subgroup A) [G.Normal]
  (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)

/-- The original base embeds in its actual character inertia. -/
def baseInclusion : G →* (T G root theta) :=
  ((inside G (T G root theta))).subtype.comp (TypeBCentralKernelTripleCharacters.baseEquiv G root theta).toMonoidHom

/-- The centreless proof fixes the group instance, not the subgroup formula. -/
def ambientKernel (centreless : Subgroup.center G = ⊥) : Subgroup (T G root theta) :=
  (TypeBBSCentralCharacterQuotient.centralKernel root theta).map
    (baseInclusion G root theta)

theorem ambientKernel_eq_bot (centreless : Subgroup.center G = ⊥) :
    ambientKernel G root theta centreless = ⊥ := by
  unfold ambientKernel
  rw [TypeBBSCentralCharacterQuotient.centralKernel_eq_bot root theta centreless,
    Subgroup.map_bot]

instance ambientKernel_normal (centreless : Subgroup.center G = ⊥) :
    (ambientKernel G root theta centreless).Normal := by
  rw [ambientKernel_eq_bot G root theta centreless]
  infer_instance

variable (centreless : Subgroup.center G = ⊥)

/-- Its forward homomorphism is exactly the actual quotient projection. -/
def ambientEquiv : (T G root theta) ≃* ((T G root theta) ⧸ (ambientKernel G root theta centreless)) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (ambientKernel G root theta centreless)) ⟨by
    intro x y h
    let e : ((T G root theta) ⧸ (ambientKernel G root theta centreless)) ≃* (T G root theta) :=
      (QuotientGroup.quotientMulEquivOfEq
        (ambientKernel_eq_bot G root theta centreless)).trans QuotientGroup.quotientBot
    exact congrArg e h,
    QuotientGroup.mk'_surjective (ambientKernel G root theta centreless)⟩

@[simp] theorem ambientEquiv_apply (t : (T G root theta)) :
    ambientEquiv G root theta centreless t = (QuotientGroup.mk' (ambientKernel G root theta centreless)) t := rfl

/-- The base in the quotient ambient is its literal projection image. -/
abbrev quotientBase : Subgroup ((T G root theta) ⧸ (ambientKernel G root theta centreless)) := ((inside G (T G root theta))).map (QuotientGroup.mk' (ambientKernel G root theta centreless))

def baseEquiv : (inside G (T G root theta)) ≃* (quotientBase G root theta centreless) :=
  (ambientEquiv G root theta centreless).subgroupMap (inside G (T G root theta))

@[simp] theorem baseEquiv_projection (n : (inside G (T G root theta))) :
    (baseEquiv G root theta centreless n).val = (QuotientGroup.mk' (ambientKernel G root theta centreless)) n.val := rfl

/-- This anchors the base image to the original computed character quotient. -/
def baseQuotientEquiv :
    G ⧸ TypeBBSCentralCharacterQuotient.centralKernel root theta ≃* (quotientBase G root theta centreless) :=
  ((TypeBBSCentralCharacterQuotient.quotientEquiv root theta centreless).trans
    (TypeBCentralKernelTripleCharacters.baseEquiv G root theta)).trans
      (baseEquiv G root theta centreless)

@[simp] theorem baseQuotientEquiv_projection (g : G) :
    (baseQuotientEquiv G root theta centreless
      (QuotientGroup.mk' (TypeBBSCentralCharacterQuotient.centralKernel root theta) g)).val =
        (QuotientGroup.mk' (ambientKernel G root theta centreless)) (baseInclusion G root theta g) := rfl

variable (W : CharacterWeight p K G)
  (hUT : U G W ≤ (T G root theta))

/-- The local ambient uses the image of the same raw-weight inertia. -/
abbrev quotientLocalAmbient : Subgroup ((T G root theta) ⧸ (ambientKernel G root theta centreless)) := ((inside (U G W) (T G root theta))).map (QuotientGroup.mk' (ambientKernel G root theta centreless))

/-- The local intersection map also has the ambient projection as its value. -/
def localEquiv : localBase (inside G (T G root theta)) (inside (U G W) (T G root theta)) ≃* localBase (quotientBase G root theta centreless) (quotientLocalAmbient G root theta centreless W) :=
  (((localBaseEquivIntersection (inside G (T G root theta)) (inside (U G W) (T G root theta))).trans
    ((ambientEquiv G root theta centreless).subgroupMap ((inside G (T G root theta)) ⊓ (inside (U G W) (T G root theta))))).trans
      (MulEquiv.subgroupCongr
        (Subgroup.map_inf (inside G (T G root theta)) (inside (U G W) (T G root theta)) (QuotientGroup.mk' (ambientKernel G root theta centreless)) (ambientEquiv G root theta centreless).injective))).trans
          (localBaseEquivIntersection (quotientBase G root theta centreless) (quotientLocalAmbient G root theta centreless W)).symm

@[simp] theorem localEquiv_projection (x : localBase (inside G (T G root theta)) (inside (U G W) (T G root theta))) :
    (localEquiv G root theta centreless W x).val.val = (QuotientGroup.mk' (ambientKernel G root theta centreless)) x.val.val := rfl

variable (Msys : ModularSystem p K O k)
  (calibration : RootResidueCompatible Msys root)
  (blocks : PhysicalBlockFamily (k := k) (inside G (T G root theta)) (inside (U G W) (T G root theta)))

/-- A typed name for the existing splitting triple, with the same catalogue. -/
def sourceTripleData : TripleData (p := p) (k := k) (K := K) (inside G (T G root theta)) (inside (U G W) (T G root theta)) :=
  TypeBCentralKernelConjugatePairBinding.tripleData (p := p) (k := k) (K := K)
    G root theta W hUT
    (TypeBCentralKernelPairSplittingBinding.pairData
      Msys G root calibration theta W hUT blocks)

theorem sourceTripleData_ambientRoot :
    (sourceTripleData G root theta W hUT Msys calibration blocks).ambientRoot =
      TypeBModularGroupRootBinding.groupRoot Msys (T G root theta) := rfl

theorem sourceTripleData_baseRoot :
    (sourceTripleData G root theta W hUT Msys calibration blocks).base.iota =
      TypeBCentralKernelTripleCharacters.baseRoot G root theta := rfl

theorem sourceTripleData_localRoot :
    (sourceTripleData G root theta W hUT Msys calibration blocks).localData.iota =
      TypeBCentralKernelTripleCharacters.localRoot G root theta W hUT
        (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W) := rfl

variable (quotientBlocks : PhysicalBlockFamily (k := k) (quotientBase G root theta centreless) (quotientLocalAmbient G root theta centreless W))

/-- Every intermediate root is restricted from the transported ambient root. -/
def quotientData : TripleData (p := p) (k := k) (K := K) (quotientBase G root theta centreless) (quotientLocalAmbient G root theta centreless W) := by
  let iotaT : PrimeRegularRootEmbedding p k K (T G root theta) :=
    TypeBModularGroupRootBinding.groupRoot Msys (T G root theta)
  let iotaN : PrimeRegularRootEmbedding p k K (inside G (T G root theta)) :=
    TypeBCentralKernelTripleCharacters.baseRoot G root theta
  let iotaL : PrimeRegularRootEmbedding p k K (localBase (inside G (T G root theta)) (inside (U G W) (T G root theta))) :=
    TypeBCentralKernelTripleCharacters.localRoot G root theta W hUT
      (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W)
  have baseAgree : ∀ z : rootsOfUnity (primeRegularExponent p (inside G (T G root theta))) k,
      iotaN.lift ((z : kˣ) : k) = iotaT.lift ((z : kˣ) : k) :=
    (sourceTripleData G root theta W hUT Msys calibration blocks).baseRoots
  have localAgree : ∀ z : rootsOfUnity (primeRegularExponent p (localBase (inside G (T G root theta)) (inside (U G W) (T G root theta)))) k,
      iotaL.lift ((z : kˣ) : k) = iotaT.lift ((z : kˣ) : k) :=
    (sourceTripleData G root theta W hUT Msys calibration blocks).localRoots
  exact withPrescribedRoots (p := p) (k := k) (K := K) (T := ((T G root theta) ⧸ (ambientKernel G root theta centreless))) (quotientBase G root theta centreless) (quotientLocalAmbient G root theta centreless W)
    (PrimeRegularRootEmbedding.alongMulEquiv (p := p) (k := k) (K := K)
      (G := (T G root theta)) (H := ((T G root theta) ⧸ (ambientKernel G root theta centreless))) iotaT (ambientEquiv G root theta centreless))
    (PrimeRegularRootEmbedding.alongMulEquiv (p := p) (k := k) (K := K)
      (G := (inside G (T G root theta))) (H := (quotientBase G root theta centreless)) iotaN (baseEquiv G root theta centreless))
    (PrimeRegularRootEmbedding.alongMulEquiv (p := p) (k := k) (K := K)
      (G := localBase (inside G (T G root theta)) (inside (U G W) (T G root theta))) (H := localBase (quotientBase G root theta centreless) (quotientLocalAmbient G root theta centreless W))
      iotaL (localEquiv G root theta centreless W))
    (fun z =>
      (alongMulEquiv_agrees iotaT iotaN
        (baseEquiv G root theta centreless) baseAgree z).trans
          (iotaT.alongMulEquiv_lift
            (ambientEquiv G root theta centreless) _).symm)
    (fun z =>
      (alongMulEquiv_agrees iotaT iotaL
        (localEquiv G root theta centreless W) localAgree z).trans
          (iotaT.alongMulEquiv_lift
            (ambientEquiv G root theta centreless) _).symm)
    quotientBlocks

theorem quotientData_ambient_lift : (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).ambientRoot.lift = (sourceTripleData G root theta W hUT Msys calibration blocks).ambientRoot.lift :=
  funext ((sourceTripleData G root theta W hUT Msys calibration blocks).ambientRoot.alongMulEquiv_lift (ambientEquiv G root theta centreless))

theorem quotientData_base_lift : (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).base.iota.lift = (sourceTripleData G root theta W hUT Msys calibration blocks).base.iota.lift :=
  funext ((sourceTripleData G root theta W hUT Msys calibration blocks).base.iota.alongMulEquiv_lift (baseEquiv G root theta centreless))

theorem quotientData_local_lift : (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).localData.iota.lift = (sourceTripleData G root theta W hUT Msys calibration blocks).localData.iota.lift :=
  funext ((sourceTripleData G root theta W hUT Msys calibration blocks).localData.iota.alongMulEquiv_lift (localEquiv G root theta centreless W))

theorem quotientData_ambient_residue : RootResidueCompatible Msys (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).ambientRoot :=
  TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue Msys (sourceTripleData G root theta W hUT Msys calibration blocks).ambientRoot
    (TypeBModularGroupRootBinding.groupRoot_residue Msys (T G root theta))
    (ambientEquiv G root theta centreless)

/-- Both base roots retain the same residue map, on their actual domains. -/
theorem quotientData_base_residue : RootResidueCompatible Msys (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).base.iota := by
  apply TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys (sourceTripleData G root theta W hUT Msys calibration blocks).base.iota _ (baseEquiv G root theta centreless)
  exact TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue Msys root
    calibration (TypeBCentralKernelTripleCharacters.baseEquiv G root theta)

theorem quotientData_local_residue : RootResidueCompatible Msys (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).localData.iota := by
  apply TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys (sourceTripleData G root theta W hUT Msys calibration blocks).localData.iota _ (localEquiv G root theta centreless W)
  exact TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue Msys
    (TypeBCentralKernelLocalReduction.normalizerRoot W
      (TypeBCentralKernelPairSplittingBinding.quotientRoot Msys W))
    (TypeBCentralKernelPairSplittingBinding.normalizerRoot_residue Msys W)
    (TypeBCentralKernelTripleCharacters.localEquiv G root theta W hUT)

/-- Restriction of a calibrated root uses the same residue map. -/
theorem subgroupRoot_residue {X : Type} [Group X] [Finite X]
    (M : ModularSystem p K O k) (iota : PrimeRegularRootEmbedding p k K X)
    (compatible : RootResidueCompatible M iota) (H : Subgroup X) :
    letI : Fintype X := Fintype.ofFinite X
    RootResidueCompatible M (TypeBCentralKernelLocalBlockBinding.subgroupRoot iota H) := by
  letI : Fintype X := Fintype.ofFinite X
  intro z hz
  letI : NeZero (primeRegularExponent p H) := ⟨(primeRegularExponent_pos p H).ne'⟩
  let zbar : rootsOfUnity (primeRegularExponent p H) k :=
    rootsOfUnity.mkOfPowEq (M.residue z) (by rw [← map_pow, hz, map_one])
  have hval : ((zbar : kˣ) : k) = M.residue z := rfl
  rw [← hval, TypeBCentralKernelLocalBlockBinding.subgroupRoot_agrees, hval]
  apply compatible
  obtain ⟨d, hd⟩ := Nat.ordCompl_dvd_ordCompl_of_dvd
    (Subgroup.card_subgroup_dvd_card H) p
  change primeRegularExponent p X = primeRegularExponent p H * d at hd
  rw [hd, pow_mul, hz, one_pow]

theorem quotientData_intermediate_residue (J : Subgroup ((T G root theta) ⧸ (ambientKernel G root theta centreless))) (hNJ : (quotientBase G root theta centreless) ≤ J) :
    RootResidueCompatible Msys ((quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).intermediate J hNJ).iota :=
  subgroupRoot_residue Msys (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).ambientRoot
    (quotientData_ambient_residue G root theta centreless W hUT
      Msys calibration blocks quotientBlocks) J

theorem quotientData_localIntermediate_residue (J : Subgroup ((T G root theta) ⧸ (ambientKernel G root theta centreless))) (hNJ : (quotientBase G root theta centreless) ≤ J) :
    RootResidueCompatible Msys ((quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).localIntermediateData J hNJ).iota := by
  letI : Fintype ((T G root theta) ⧸ (ambientKernel G root theta centreless)) := Fintype.ofFinite ((T G root theta) ⧸ (ambientKernel G root theta centreless))
  exact subgroupRoot_residue Msys
    (TypeBCentralKernelLocalBlockBinding.subgroupRoot (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).ambientRoot J)
    (quotientData_intermediate_residue G root theta centreless W hUT
      Msys calibration blocks quotientBlocks J hNJ) (localIntermediate (quotientLocalAmbient G root theta centreless W) J)

/-- The entire prescribed quotient catalogue family is retained verbatim. -/
theorem quotientData_blocks :
    (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).base.blocks = quotientBlocks.base ∧
    (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).localData.blocks = quotientBlocks.localData ∧
    (∀ (J : Subgroup ((T G root theta) ⧸ (ambientKernel G root theta centreless))) (hNJ : (quotientBase G root theta centreless) ≤ J),
      ((quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).intermediate J hNJ).blocks = quotientBlocks.intermediate J hNJ) ∧
    (∀ (J : Subgroup ((T G root theta) ⧸ (ambientKernel G root theta centreless))) (hNJ : (quotientBase G root theta centreless) ≤ J),
      ((quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).localIntermediateData J hNJ).blocks =
        quotientBlocks.localIntermediateData J hNJ) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The descended base character is constructed from the existing pair. -/
def quotientTheta : IBr (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).base.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (sourceTripleData G root theta W hUT Msys calibration blocks).base.iota
    (baseEquiv G root theta centreless)
    (TypeBCentralKernelConjugatePairBinding.baseCharacter G root theta W hUT
      (TypeBCentralKernelPairSplittingBinding.pairData
        Msys G root calibration theta W hUT blocks))

/-- Inflation is along the restriction of the actual ambient projection. -/
theorem quotientTheta_inflation :
    PrimeRegularClassFunction.pullback
      (quotientSubgroupMap (ambientKernel G root theta centreless) (inside G (T G root theta)))
      (quotientTheta G root theta centreless W hUT Msys calibration blocks quotientBlocks).val =
        (TypeBCentralKernelConjugatePairBinding.baseCharacter G root theta W hUT
          (TypeBCentralKernelPairSplittingBinding.pairData
            Msys G root calibration theta W hUT blocks)).val := by
  ext x
  change (TypeBCentralKernelConjugatePairBinding.baseCharacter G root theta W hUT
    (TypeBCentralKernelPairSplittingBinding.pairData
      Msys G root calibration theta W hUT blocks)).val
        (PrimeRegularElement.map (baseEquiv G root theta centreless).symm.toMonoidHom
          (PrimeRegularElement.map (baseEquiv G root theta centreless).toMonoidHom x)) = _
  congr 1
  apply Subtype.ext
  exact (baseEquiv G root theta centreless).symm_apply_apply x.val

/-- The quotient base uses the original computed quotient's root lift. -/
theorem quotientTheta_quotientRoot_lift :
    (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).base.iota.lift =
      (TypeBBSCentralCharacterQuotient.quotientRoot root theta centreless).lift :=
  (quotientData_base_lift G root theta centreless W hUT
    Msys calibration blocks quotientBlocks).trans
      ((funext (TypeBCentralKernelTripleCharacters.baseRoot_lift G root theta)).trans
        (TypeBBSCentralCharacterQuotient.quotientRoot_lift root theta centreless).symm)

/-- The transported pair character is the existing computed quotient character
under the same canonical base-image equivalence. -/
theorem quotientTheta_quotientCharacter :
    (quotientTheta G root theta centreless W hUT Msys calibration blocks quotientBlocks).val =
      PrimeRegularClassFunction.pullback
        (baseQuotientEquiv G root theta centreless).symm.toMonoidHom
        (TypeBBSCentralCharacterQuotient.quotientCharacter root theta centreless).val := by
  rw [TypeBBSCentralCharacterQuotient.quotientCharacter,
    TypeBBSCentralCharacterQuotient.brauerEquiv,
    TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val]
  ext x
  change theta.val
      (PrimeRegularElement.map
        (TypeBCentralKernelTripleCharacters.baseEquiv G root theta).symm.toMonoidHom
        (PrimeRegularElement.map (baseEquiv G root theta centreless).symm.toMonoidHom x)) =
    theta.val
      (PrimeRegularElement.map
        (TypeBBSCentralCharacterQuotient.quotientEquiv root theta centreless).toMonoidHom
        (PrimeRegularElement.map
          (baseQuotientEquiv G root theta centreless).symm.toMonoidHom x))
  congr 1

variable [HasEnoughRootsOfUnity K (Nat.card G)]
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding p k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)

/-- The local character is the projection transport of the same own reduction. -/
def quotientPhi : IBr (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks).localData.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (sourceTripleData G root theta W hUT Msys calibration blocks).localData.iota
    (localEquiv G root theta centreless W) (TypeBCentralKernelPairSplittingBinding.localCharacter Msys G root calibration theta W hUT navarro blocks)

theorem quotientPhi_inflation :
    PrimeRegularClassFunction.pullback (quotientLocalMap (ambientKernel G root theta centreless) (inside G (T G root theta)) (inside (U G W) (T G root theta)))
      (quotientPhi G root theta centreless W hUT Msys calibration blocks quotientBlocks navarro).val =
        ((TypeBCentralKernelPairSplittingBinding.localCharacter Msys G root calibration theta W hUT navarro blocks)).val := by
  ext x
  change ((TypeBCentralKernelPairSplittingBinding.localCharacter Msys G root calibration theta W hUT navarro blocks)).val
    (PrimeRegularElement.map (localEquiv G root theta centreless W).symm.toMonoidHom
      (PrimeRegularElement.map (localEquiv G root theta centreless W).toMonoidHom x)) = _
  congr 1
  apply Subtype.ext
  exact (localEquiv G root theta centreless W).symm_apply_apply x.val

/-- The source pair is a derived witness. Every intermediate clause is carried
to the literal quotient groups by the same one-way certificate. -/
theorem quotientPairWitness
    (witness : TypeBCentralKernelPairSplittingBinding.PairWitness
      Msys G root calibration theta W hUT navarro blocks)
    (certificate : ButterflyCertificate p k K) :
    Nonempty (BlockTripleWitness (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks)
      (quotientTheta G root theta centreless W hUT Msys calibration blocks quotientBlocks)
      (quotientPhi G root theta centreless W hUT Msys calibration blocks quotientBlocks navarro)) := by
  apply TypeBCentralKernelConjugateTripleTransport.transfer_to_image
    (inside G (T G root theta)) (quotientBase G root theta centreless) (inside (U G W) (T G root theta)) (quotientLocalAmbient G root theta centreless W) (ambientEquiv G root theta centreless)
    (baseEquiv G root theta centreless) (fun _ => rfl) rfl (sourceTripleData G root theta W hUT Msys calibration blocks) (quotientData G root theta centreless W hUT Msys calibration blocks quotientBlocks)
    (TypeBCentralKernelConjugatePairBinding.baseCharacter G root theta W hUT
      (TypeBCentralKernelPairSplittingBinding.pairData
        Msys G root calibration theta W hUT blocks)) (TypeBCentralKernelPairSplittingBinding.localCharacter Msys G root calibration theta W hUT navarro blocks)
    (quotientTheta G root theta centreless W hUT Msys calibration blocks quotientBlocks)
    (quotientPhi G root theta centreless W hUT Msys calibration blocks quotientBlocks navarro)
    witness
  · intro z _ _
    exact (congrFun (quotientData_ambient_lift G root theta centreless W hUT
      Msys calibration blocks quotientBlocks) (z : k)).symm
  · exact quotientData_base_lift G root theta centreless W hUT
      Msys calibration blocks quotientBlocks
  · exact quotientData_local_lift G root theta centreless W hUT
      Msys calibration blocks quotientBlocks
  · rfl
  · intro x y hxy
    change ((TypeBCentralKernelPairSplittingBinding.localCharacter Msys G root calibration theta W hUT navarro blocks)).val
      (PrimeRegularElement.map (localEquiv G root theta centreless W).symm.toMonoidHom y) =
        ((TypeBCentralKernelPairSplittingBinding.localCharacter Msys G root calibration theta W hUT navarro blocks)).val x
    have heq : (localEquiv G root theta centreless W) x.val = y.val := by
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
    have hback := congrArg (localEquiv G root theta centreless W).symm heq
    rw [MulEquiv.symm_apply_apply] at hback
    congr 1
    exact Subtype.ext hback.symm
  · exact certificate

end ModularRep.PaperProofs.TypeBBSCentralQuotientPairTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
