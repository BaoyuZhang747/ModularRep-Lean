import ModularRep.PaperProofs.OddTwoBroughGlobalExtensionOnOriginalInertia
import ModularRep.PaperProofs.OddTwoBroughLocalOrdinaryExtension
import ModularRep.PaperProofs.OddTwoBroughCoveringSource
import ModularRep.PaperProofs.OddTwoBroughButterflySource

/-!
# The four literal hypotheses of Brough--Spath Lemma 4.6

BS (2022), Lemma4.6, pp.477--478, is retained as the precise E2 result on
X=PSp, T=PCSp and the actual field group. The four hypotheses below use
actual character and weight-CLASS stabilizers, the OWN local ordinary
character on the two raw-pair inertia quotients, and the definition-shaped
covering predicates and actual induced block from the checked source.

Every conformal translate extends on the ORIGINAL two global groups;
GlobalExtensionOnOriginal fixes their actual base coordinates and roots.
The local inertia groups are never replaced by whole normalizers.

The source conclusion is only some actual conformal translate of the
global character, with the ORIGINAL W and its own compatible normalizer
reduction, in the already computed Brough tuple. The standard full-cover
packet licenses the identity prime-to-two cover of this literal PSp, whose
centre is trivial. No FLZ relation, orbit witness, seed, intermediate
matched-extension block condition, or final Type C conclusion is an input.

The DGN interpretation and BlockTripleSourceSemantics must have their
authenticated standard meanings. Arbitrary predicates are not licensed
instances. Their foundational reconstruction is outside this window.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughLemma46SourceAndPacket

open scoped commutatorElement
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoBroughExtensionGroups
open ModularRep.PaperProofs.OddTwoBroughCoveringSource
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple (OwnNormalizerReduction)
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

variable {n : ℕ} {F k K BlockX BlockT : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (PSp n F))ᵐᵒᵖ BlockX]
variable [MulAction (MulAut (PCSp n F))ᵐᵒᵖ BlockT]

local instance lemma46Fintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

local instance lemma46FieldAutFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

local instance lemma46FieldGroupFinite : Finite (FieldGroup (n := n) (F := F)) :=
  Finite.of_equiv (PSp n F × (F ≃+* F)) SemidirectProduct.equivProd.symm

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable [projectiveBaseNormal : (pspEmbedding C).range.Normal]
variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))

/-- The canonical action on ambient-conjugacy weight CLASSES, distinct
from the action on raw IsoClass used to construct the local inertia. -/
@[instance_reducible]
def actualWeightClassAction : MulAction (Ambient (n := n) (F := F))
    (BaseWeightClass (n := n) (F := F) (K := K)) :=
  rightAutomorphismAction S.fullAut.toMonoidHom

def weightClassStabilizer (W : CharacterWeight 2 K (PSp n F)) :
    Subgroup (Ambient (n := n) (F := F)) :=
  letI := actualWeightClassAction (K := K) S
  MulAction.stabilizer (Ambient (n := n) (F := F)) (weightClass W)

/-- Raw-pair fixation implies fixation of its ambient conjugacy class.
The converse, which would amount to an invariant representative, is not
used or asserted. -/
theorem rawStabilizer_le_weightClassStabilizer (W : CharacterWeight 2 K (PSp n F)) :
    OddTwoBroughActualTriple.rawStabilizer S W ≤ weightClassStabilizer S W := by
  intro g hg
  change (Quotient.mk'' (W.rightTwist (S.fullAut g⁻¹)) :
    CharacterWeight.IsoClass (p := 2) (K := K) (G := PSp n F)) = Quotient.mk'' W at hg
  change (Quotient.mk'' (Quotient.mk'' (W.rightTwist (S.fullAut g⁻¹))) :
    BaseWeightClass (n := n) (F := F) (K := K)) = Quotient.mk'' (Quotient.mk'' W)
  exact congrArg (fun r : CharacterWeight.IsoClass (p := 2) (K := K) (G := PSp n F) =>
    (Quotient.mk'' r : BaseWeightClass (n := n) (F := F) (K := K))) hg

/-- Definition-shaped extension of OWN theta, on the actual inertia/Q,
with equality on every lift from the actual own normalizer. -/
def LocalOrdinaryExtends {G T : Type u} [Group G] [Finite G] [Group T]
    (L : Geometry (C := C) G T) (W : CharacterWeight 2 K (PSp n F)) : Prop :=
  ∃ thetaHat : OrdinaryIrreducibleCharacter.Irr K (L.LocalQuotient S W),
    ∀ x : Subgroup.normalizer (W.subgroup : Set (PSp n F)),
      thetaHat (QuotientGroup.mk' (L.radical S W) (L.normalizerToRaw S W x)) =
        W.localCharacter (QuotientGroup.mk x)

variable (iotaT : PrimeRegularRootEmbedding 2 k K (PCSp n F))
variable (OX : LocalBlockInductionSource
  (p := 2) (k := k) (K := K) (G := PSp n F) (Block := BlockX))
variable (OT : LocalBlockInductionSource
  (p := 2) (k := k) (K := K) (G := PCSp n F) (Block := BlockT))
variable (injX : IrreducibleBrauerCharacterInjectivity iota)
variable (injT : IrreducibleBrauerCharacterInjectivity iotaT)
variable (A : DGNSourceSemantics (K := K) C S)
variable (tensor : BrauerLinearTensorProductFormula iotaT)

/-- Published clause (iv), retaining actual covering objects and the
SAME quotient linear Brauer character for both actions. The local block
is OT.weightBlock of that same covering weight CLASS. -/
structure CoveringClause (psi : IBr iota) (W : CharacterWeight 2 K (PSp n F)) where
  character : IBr iotaT
  weight : CoverWeightClass (n := n) (F := F) (K := K)
  character_covers : CharacterCovers C iota iotaT psi character
  weight_covers : WeightCovers C S A (weightClass W) weight
  common_mu : ∀ sigma : F ≃+* F,
    (SemidirectProduct.inr sigma : Ambient (n := n) (F := F)) ∈
      OddTwoBroughActualTriple.globalStabilizer S iota psi →
    ∃ lambda : QuotientLinBr (k := k) C S,
      IrreducibleBrauerCharacter.twist iotaT character (pcspFieldAction sigma)⁻¹ =
        IrreducibleBrauerCharacter.linearTwist iotaT tensor character (ambientLinear C S lambda) ∧
      LinearWeightRelated C S iotaT lambda
        (rightTwistConjugacyClass (pcspFieldAction sigma)⁻¹ weight) weight
  same_block : coverBrauerBlock iotaT OT injT character = OT.weightBlock weight

/-- The four published clauses, with no relation conclusion. The
factorizations display both actual conformal and field stabilizers.
Clause (i) extends every translate on the original inertia groups. -/
structure FourClauses (psi : IBr iota) (W : CharacterWeight 2 K (PSp n F)) : Prop where
  global_factor : ∀ g : Ambient (n := n) (F := F),
    g ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi ↔
      (SemidirectProduct.inl g.left : Ambient (n := n) (F := F)) ∈
        OddTwoBroughActualTriple.globalStabilizer S iota psi ∧
      (SemidirectProduct.inr g.right : Ambient (n := n) (F := F)) ∈
        OddTwoBroughActualTriple.globalStabilizer S iota psi
  commutator : ∀ (g : Ambient (n := n) (F := F)) (t : PCSp n F),
    g ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi →
      ⁅g, SemidirectProduct.inl t⁆ ∈
        (SemidirectProduct.inl (φ := pcspFieldAction (n := n) (F := F))).range ∧
      ⁅g, SemidirectProduct.inl t⁆ ∈ OddTwoBroughActualTriple.globalStabilizer S iota psi
  global_extensions : ∀ t : PCSp n F,
    Nonempty ((fieldGeometry (C := C)).GlobalExtensionOnOriginal S iota psi
      (IrreducibleBrauerCharacter.twist iota psi (S.pcspToAut t)⁻¹)) ∧
    Nonempty ((conformalGeometry S).GlobalExtensionOnOriginal S iota psi
      (IrreducibleBrauerCharacter.twist iota psi (S.pcspToAut t)⁻¹))
  weight_factor : ∀ g : Ambient (n := n) (F := F),
    g ∈ weightClassStabilizer S W ↔
      (SemidirectProduct.inl g.left : Ambient (n := n) (F := F)) ∈ weightClassStabilizer S W ∧
      (SemidirectProduct.inr g.right : Ambient (n := n) (F := F)) ∈ weightClassStabilizer S W
  local_extensions : LocalOrdinaryExtends S (fieldGeometry (C := C)) W ∧
    LocalOrdinaryExtends S (conformalGeometry S) W
  stabilizers : OddTwoBroughActualTriple.globalStabilizer S iota psi = weightClassStabilizer S W
  covering : Nonempty (CoveringClause S iota iotaT OT injT A tensor psi W)

/-- Clause (iii) places the entire original raw inertia inside the
actual global stabilizer. Thus the computed local intersection is the
published full raw inertia, by the checked fullRawStabilizerEquiv. -/
theorem FourClauses.raw_contained {psi : IBr iota} {W : CharacterWeight 2 K (PSp n F)}
    (clauses : FourClauses S iota iotaT OT injT A tensor psi W) :
    OddTwoBroughActualTriple.rawStabilizer S W ≤
      OddTwoBroughActualTriple.globalStabilizer S iota psi := by
  rw [clauses.stabilizers]
  exact rawStabilizer_le_weightClassStabilizer S W

/-- Exact standard BS4.6, specialized to these literal carriers. The
cover argument supplies the published group scope through the checked
identity prime-to-two cover construction. The support inputs authenticate
the actual OT labels used in clause (iv); they assert no relation.

The source retains every actual psi and W, not just one FM-selected pair.
The output changes only psi by some actual t and preserves W and R.
Transport from the published centre quotient is along Z(X)=1, and from
the full raw inertia to the tuple's local subgroup uses clause (iii).
These are definition-shaped identifications, not additional conclusions
assumed about an arbitrary block-triple predicate. -/
structure BroughLemma46Source
    (cover : OddSymplecticFullCoverSource n F)
    (semantics : BlockTripleSourceSemantics 2 k K) : Prop where
  lemma46 : ∀ (psi : IBr iota) (W : CharacterWeight 2 K (PSp n F))
      (R : OwnNormalizerReduction (k := k) W),
    IsAlgClosed K →
    RootCompatibleAlong iota R.root
      (Subgroup.normalizer (W.subgroup : Set (PSp n F))).subtype →
    RootCompatibleAlong iotaT iota (pspEmbedding C) →
    Source iotaT OT.operations →
    (∀ V : CoverWeight (n := n) (F := F) (K := K),
      Nonempty (OddTwoFengMalleForwardSourceJoin.CompatibleReduction iotaT V)) →
    FourClauses S iota iotaT OT injT A tensor psi W →
      ∃ t : PCSp n F, semantics.blockIsomorphic
        (OddTwoBroughActualTriple.arguments S iota
          (IrreducibleBrauerCharacter.twist iota psi (S.pcspToAut t)⁻¹) W R)

/-- K constructs the covering clause from the checked source laws and
field fixedness of the actual base character and weight CLASS. A common
covering block is deduced, never supplied as an external chosen pairing. -/
def coveringClauseOfFixed
    (laws : BroughCoveringLaws C S iota iotaT A)
    (blocks : BlockCoveringLaws C S iota iotaT OX OT injX injT A)
    (psi : IBr iota) (W : CharacterWeight 2 K (PSp n F))
    (psiFixed : ∀ sigma : F ≃+* F,
      IrreducibleBrauerCharacter.twist iota psi (pspFieldAction sigma)⁻¹ = psi)
    (weightFixed : ∀ sigma : F ≃+* F,
      rightTwistConjugacyClass (pspFieldAction sigma)⁻¹ (weightClass W) = weightClass W)
    (sameBaseBlock : baseBrauerBlock iota OX injX psi = OX.weightBlock (weightClass W)) :
    CoveringClause S iota iotaT OT injT A laws.tensorFormula psi W := by
  choose Phi hPhi using laws.character_exists psi
  choose v hv using laws.weight_class_exists W
  exact
    { character := Phi
      weight := v
      character_covers := hPhi
      weight_covers := hv
      common_mu := by
        intro sigma _
        obtain ⟨lambda, _, hchar, hweight⟩ :=
          laws.common_mu_one sigma hPhi hv (psiFixed sigma) (weightFixed sigma)
        exact ⟨lambda, hchar, hweight⟩
      same_block := blocks.common_block hPhi hv sameBaseBlock }

end ModularRep.PaperProofs.OddTwoBroughLemma46SourceAndPacket


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
