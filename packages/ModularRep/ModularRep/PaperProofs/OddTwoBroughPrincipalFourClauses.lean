import ModularRep.PaperProofs.OddTwoBroughLemma46SourceAndPacket
import ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers

/-!
# The four BS4.6 clauses for the same descended principal FM map

The only new input data are standard common roots on the two ORIGINAL
global inertia groups. Both base roots are computed from the same iota.
No extension, matched covering pair, stabilizer equality or block-triple
relation is supplied by that root packet.

K uses the checked principal field fixedness, SAME descended FM map,
actual full-automorphism equivariance and ambient commutator calculation.
Both local extensions concern the supplied W's own character on actual
inertia/Q. W need only represent the computed FM image; its raw field
stabilizer is not assumed to be its class stabilizer. The all-translates
global extensions keep the original inertia groups and base coordinates.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughPrincipalFourClauses

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
open ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers
open ModularRep.PaperProofs.OddTwoBroughExtensionGroups
open ModularRep.PaperProofs.OddTwoBroughCoveringSource
open ModularRep.PaperProofs.OddTwoBroughLemma46SourceAndPacket
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple (OwnNormalizerReduction)
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

variable {n : ℕ} {F k K Block J BlockT : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]
variable [MulAction (MulAut (PCSp n F))ᵐᵒᵖ BlockT]

local instance principal46Fintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

local instance principal46FieldAutFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

local instance principal46FieldGroupFinite : Finite (FieldGroup (n := n) (F := F)) :=
  Finite.of_equiv (PSp n F × (F ≃+* F)) SemidirectProduct.equivProd.symm

variable {D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block)}
variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)
variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective E.downSource.operations)
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable [projectiveBaseNormal : (pspEmbedding C).range.Normal]

/-- Narrow standard common-root data. The source of each compatibility
is the exact base root computed on the ORIGINAL inertia group. -/
structure GlobalRoots (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))
    (psi : IBr iota) where
  fieldRoot : PrimeRegularRootEmbedding 2 k K ((fieldGeometry (C := C)).global S iota psi)
  fieldCompatible : RootCompatibleAlong fieldRoot
    ((fieldGeometry (C := C)).globalBaseRoot S iota psi)
    ((fieldGeometry (C := C)).globalBase S iota psi).subtype
  conformalRoot : PrimeRegularRootEmbedding 2 k K ((conformalGeometry S).global S iota psi)
  conformalCompatible : RootCompatibleAlong conformalRoot
    ((conformalGeometry S).globalBaseRoot S iota psi)
    ((conformalGeometry S).globalBase S iota psi).subtype

/-- Principal fibre and actual class stabilizers have exactly the same
membership. This is a restriction-of-action fact, not representative
equivariance. -/
theorem principalWeight_stabilizer_eq (w : E.DownPrincipalWeight)
    (W : CharacterWeight 2 K (PSp n F)) (hW : weightClass W = w.1) :
    let _ := ambientWeightAction E downSupport S
    MulAction.stabilizer (Ambient (n := n) (F := F)) w = weightClassStabilizer S W := by
  dsimp only
  letI := ambientWeightAction E downSupport S
  ext g
  change g • w = w ↔ MulOpposite.op (S.fullAut g⁻¹) • weightClass W = weightClass W
  rw [hW]
  have hcoe : (g • w).1 = MulOpposite.op (S.fullAut g⁻¹) • w.1 := by
    change MulOpposite.op ((S.fullAut g)⁻¹) • w.1 = _
    rw [map_inv]
  constructor
  · intro h
    exact hcoe.symm.trans (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (hcoe.trans h)

variable (fixed : FengMalleCorollary43aSource D)
variable (FM : D.FengMalleTheorem62LiteralCertificate)
variable (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))

include downSupport FM lifting in
/-- Equality of actual character and weight-CLASS stabilizers from the
same fully equivariant and injective descended FM correspondence. -/
theorem matched_actual_stabilizers (psi : E.DownPrincipalBrauer)
    (W : CharacterWeight 2 K (PSp n F))
    (hW : weightClass W = (E.descendedFengMalleOmega FM psi).1) :
    OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 = weightClassStabilizer S W := by
  letI := downstreamBrauerAction E downSupport
  letI := downstreamWeightAction E downSupport
  letI := ambientBrauerAction E downSupport S
  letI := ambientWeightAction E downSupport S
  rw [← principal_stabilizer_eq E downSupport S,
    ← principalWeight_stabilizer_eq E downSupport S (E.descendedFengMalleOmega FM psi) W hW]
  ext g
  exact descendedOmega_fixed_iff E downSupport FM lifting (S.fullAut g) psi

include downSupport fixed in
theorem principal_brauer_field_fixed (psi : E.DownPrincipalBrauer) (sigma : F ≃+* F) :
    IrreducibleBrauerCharacter.twist E.iotaDown psi.1 (pspFieldAction sigma)⁻¹ = psi.1 := by
  exact congrArg Subtype.val (downstreamBrauer_field_fixed fixed E downSupport sigma psi)

include downSupport fixed FM in
theorem principal_weight_field_fixed (psi : E.DownPrincipalBrauer)
    (W : CharacterWeight 2 K (PSp n F))
    (hW : weightClass W = (E.descendedFengMalleOmega FM psi).1) (sigma : F ≃+* F) :
    rightTwistConjugacyClass (pspFieldAction sigma)⁻¹ (weightClass W) = weightClass W := by
  rw [hW]
  exact congrArg Subtype.val (downstreamWeight_field_fixed fixed FM E downSupport sigma
    (E.descendedFengMalleOmega FM psi))

/-- Both base objects lie in the SAME actual constant-one block by their
principal fibres. No principal property of a covering pair is assumed. -/
theorem same_principal_base_block (psi : E.DownPrincipalBrauer)
    (W : CharacterWeight 2 K (PSp n F))
    (hW : weightClass W = (E.descendedFengMalleOmega FM psi).1) :
    baseBrauerBlock E.iotaDown E.downSource E.downInjective psi.1 =
      E.downSource.weightBlock (weightClass W) := by
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  have hpsi : baseBrauerBlock E.iotaDown E.downSource E.downInjective psi.1 =
      E.downPrincipalBlock := psi.2
  have hw : E.downSource.weightBlock (weightClass W) = E.downPrincipalBlock := by
    rw [hW]
    exact (E.descendedFengMalleOmega FM psi).2
  exact hpsi.trans hw.symm

variable (iotaT : PrimeRegularRootEmbedding 2 k K (PCSp n F))
variable (OT : LocalBlockInductionSource
  (p := 2) (k := k) (K := K) (G := PCSp n F) (Block := BlockT))
variable (injT : IrreducibleBrauerCharacterInjectivity iotaT)
variable (A : DGNSourceSemantics (K := K) C S)
variable (laws : BroughCoveringLaws C S E.iotaDown iotaT A)
variable (blocks : BlockCoveringLaws C S E.iotaDown iotaT
  E.downSource OT E.downInjective injT A)

include downSupport fixed FM lifting laws blocks in
/-- K combines all four published clauses. Standard extension principles
and common-root data are explicit. No relation or extension conclusion is
an input; the supplied own W is retained throughout. -/
theorem principal_fourClauses
    (brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
    (ordinaryExtension : Representation.CyclicExtensionPrinciple.{u, u, u} K)
    (psi : E.DownPrincipalBrauer) (W : CharacterWeight 2 K (PSp n F))
    (hW : weightClass W = (E.descendedFengMalleOmega FM psi).1)
    (roots : GlobalRoots S E.iotaDown psi.1) :
    FourClauses S E.iotaDown iotaT OT injT A laws.tensorFormula psi.1 W := by
  letI := ambientBrauerAction E downSupport S
  letI := ambientWeightAction E downSupport S
  letI : IsAlgClosed K := laws.ordinarySplitting
  letI : IsCyclic (F ≃+* F) := S.field_cyclic
  letI : IsCyclic (PCSp n F ⧸ (pspEmbedding C).range) := conformalOuter_cyclic S
  have hstab := matched_actual_stabilizers E downSupport S FM lifting psi W hW
  have hfield : ∀ sigma : F ≃+* F,
      (SemidirectProduct.inr sigma : Ambient (n := n) (F := F)) ∈
        OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 := by
    intro sigma
    rw [← principal_stabilizer_eq E downSupport S]
    exact ambientBrauer_field_fixed fixed E downSupport S sigma psi
  have factor : ∀ g : Ambient (n := n) (F := F),
      g ∈ OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 ↔
        (SemidirectProduct.inl g.left : Ambient (n := n) (F := F)) ∈
          OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 ∧
        (SemidirectProduct.inr g.right : Ambient (n := n) (F := F)) ∈
          OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 := by
    intro g
    have h := ambientBrauer_stabilizer_factorization fixed E downSupport S g psi
    dsimp only at h
    rw [principal_stabilizer_eq E downSupport S] at h
    exact h.trans (and_iff_left (hfield g.right)).symm
  refine
    { global_factor := factor
      commutator := fun g t _ => commutator_mem_conformal_stabilizer E downSupport S fixed g t psi
      global_extensions := ?_
      weight_factor := ?_
      local_extensions := ?_
      stabilizers := hstab
      covering := ?_ }
  · intro t
    have hsame : OddTwoBroughActualTriple.globalStabilizer S E.iotaDown
        (IrreducibleBrauerCharacter.twist E.iotaDown psi.1 (S.pcspToAut t)⁻¹) =
        OddTwoBroughActualTriple.globalStabilizer S E.iotaDown psi.1 :=
      actual_global_stabilizer_translate E downSupport S fixed (SemidirectProduct.inl t) psi
    constructor
    · exact (fieldGeometry (C := C)).extensionOnOriginalInertia S E.iotaDown psi.1 _
        brauerExtension (congrArg (fun H => H.comap (fieldGeometry (C := C)).embedding) hsame)
        roots.fieldRoot roots.fieldCompatible
    · exact (conformalGeometry S).extensionOnOriginalInertia S E.iotaDown psi.1 _
        brauerExtension (congrArg (fun H => H.comap (conformalGeometry S).embedding) hsame)
        roots.conformalRoot roots.conformalCompatible
  · intro g
    simpa only [← hstab] using factor g
  · exact ⟨(fieldGeometry (C := C)).exists_ownLocalOrdinary_extension S W ordinaryExtension,
      (conformalGeometry S).exists_ownLocalOrdinary_extension S W ordinaryExtension⟩
  · exact ⟨coveringClauseOfFixed S E.iotaDown iotaT E.downSource OT E.downInjective injT A
      laws blocks psi.1 W (principal_brauer_field_fixed E downSupport fixed psi)
      (principal_weight_field_fixed E downSupport fixed FM psi W hW)
      (same_principal_base_block E FM psi W hW)⟩

include downSupport fixed FM lifting laws blocks in
/-- The exact forward BS4.6 endpoint. The existential conformal element
changes the global character while retaining the ORIGINAL W and R.
There is no final FLZ or orbit predicate in this conclusion. -/
theorem exists_principal_brough_relation
    (semantics : BlockTripleSourceSemantics 2 k K)
    (source : BroughLemma46Source S E.iotaDown iotaT OT injT A laws.tensorFormula cover semantics)
    (brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
    (ordinaryExtension : Representation.CyclicExtensionPrinciple.{u, u, u} K)
    (psi : E.DownPrincipalBrauer) (W : CharacterWeight 2 K (PSp n F))
    (hW : weightClass W = (E.descendedFengMalleOmega FM psi).1)
    (roots : GlobalRoots S E.iotaDown psi.1)
    (R : OwnNormalizerReduction (k := k) W)
    (ownRoots : RootCompatibleAlong E.iotaDown R.root
      (Subgroup.normalizer (W.subgroup : Set (PSp n F))).subtype) :
    ∃ t : PCSp n F, semantics.blockIsomorphic
      (OddTwoBroughActualTriple.arguments S E.iotaDown
        (IrreducibleBrauerCharacter.twist E.iotaDown psi.1 (S.pcspToAut t)⁻¹) W R) :=
  source.lemma46 psi.1 W R laws.ordinarySplitting ownRoots laws.commonRoots
    blocks.coverSupport blocks.coverReductions
    (principal_fourClauses E downSupport S fixed FM lifting iotaT OT injT A laws blocks
      brauerExtension ordinaryExtension psi W hW roots)

end ModularRep.PaperProofs.OddTwoBroughPrincipalFourClauses


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
