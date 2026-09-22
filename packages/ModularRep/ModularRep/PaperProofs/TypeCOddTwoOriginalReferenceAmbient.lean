import ModularRep.PaperProofs.TypeCOddTwoOriginalQuotientFibres
import ModularRep.PaperProofs.EvenFieldBlockGroupEquivCoordinates

/-!
# The same original ambient group in fixed reference-quotient coordinates

The original Definition41 packet uses the central quotient of its own
Brauer character. A block-wide relative witness uses one reference quotient.
Both quotients are canonically the original centreless group. This module
computes the resulting character-stabilizer and ambient coordinate changes.
The ambient group, its base, centre and centralizer are retained verbatim.

At the original selected own pair the embedded radical and local normalizer
are unchanged. The already derived original Frattini equality therefore
holds in these reference coordinates, including the every-J decomposition.
No complete BlockWitness, root agreement, extension, or source relation is
assumed or constructed here. The chosen reductions, extensions and both Q=1
normalizations remain attached to the same original packet for later joins.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalReferenceAmbient

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open EvenFieldFLZCentrelessCentralKernel OddTwoLiteralSpathTarget
open EvenFieldBlockGroupEquivCoordinates
open TypeCOddTwoOriginalBlockMatching TypeCOddTwoOriginalQuotientFibres

universe u

section CharacterCoordinates

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]
variable (iotaG : PrimeRegularRootEmbedding p k K G)
variable (iotaH : PrimeRegularRootEmbedding p k K H)
variable (e : G ≃* H) (phiG : IBr iotaG) (phiH : IBr iotaH)
variable (values : PrimeRegularClassFunction.equivAlongMulEquiv e phiG.1 = phiH.1)

include values in
/-- Exact character values suffice for stabilizer transport. This asserts
no compatibility of independently chosen roots. -/
theorem fixed_iff (a : (MulAut G)ᵐᵒᵖ) :
    a • phiG = phiG ↔ oppositeAutEquiv e a • phiH = phiH := by
  have ht := PrimeRegularClassFunction.equivAlongMulEquiv_twist e phiG.1 a.unop
  constructor
  · intro ha
    apply Subtype.ext
    change phiH.1.twist (MulAut.congr e a.unop) = phiH.1
    exact (congrArg (fun f : PrimeRegularClassFunction K H p =>
      f.twist (MulAut.congr e a.unop)) values.symm).trans
        (ht.symm.trans ((congrArg (fun phi : IBr iotaG =>
          PrimeRegularClassFunction.equivAlongMulEquiv e phi.1) ha).trans values))
  · intro ha
    apply Subtype.ext
    apply (PrimeRegularClassFunction.equivAlongMulEquiv e).injective
    exact (ht.trans (congrArg (fun f : PrimeRegularClassFunction K H p =>
      f.twist (MulAut.congr e a.unop)) values)).trans
        ((congrArg Subtype.val ha).trans values.symm)

/-- Restrict the computed opposite automorphism equivalence to the actual
two character stabilizers; neither stabilizer is a supplied subgroup. -/
def characterStabilizerEquiv :
    MulAction.stabilizer (MulAut G)ᵐᵒᵖ phiG ≃*
      MulAction.stabilizer (MulAut H)ᵐᵒᵖ phiH where
  toFun a := ⟨oppositeAutEquiv e a.1,
    (fixed_iff iotaG iotaH e phiG phiH values a.1).mp a.2⟩
  invFun a := ⟨(oppositeAutEquiv e).symm a.1, by
    apply (fixed_iff iotaG iotaH e phiG phiH values
      ((oppositeAutEquiv e).symm a.1)).mpr
    exact (congrArg (fun c : (MulAut H)ᵐᵒᵖ => c • phiH)
      ((oppositeAutEquiv e).apply_symm_apply a.1)).trans a.2⟩
  left_inv a := Subtype.ext ((oppositeAutEquiv e).symm_apply_apply a.1)
  right_inv a := Subtype.ext ((oppositeAutEquiv e).apply_symm_apply a.1)
  map_mul' a c := Subtype.ext (map_mul (oppositeAutEquiv e) a.1 c.1)

@[simp] theorem characterStabilizerEquiv_coe
    (a : MulAction.stabilizer (MulAut G)ᵐᵒᵖ phiG) :
    (characterStabilizerEquiv iotaG iotaH e phiG phiH values a).1 =
      oppositeAutEquiv e a.1 := rfl

end CharacterCoordinates

section ReferenceCoordinates

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : Problem n F) (b : P.Block)
variable (reference psi : Definition35Brauer (P.blockProblem b))

/-- The reference packet uses the same fixed quotient root and character
as the computed complete specified fibres. -/
def referenceSource : CentralQuotientBrauerSource (P.blockProblem b) reference psi where
  iota := quotientRoot P b reference
  brauer := descendedBrauer P b reference psi.1
  irreducibleBrauerInjective := quotientInjective P b reference
  centralFaithful := by
    rw [center_centralCharacterQuotient_eq_bot_of_centerless
      (P.blockProblem b) P.center_eq_bot reference]
    exact bot_inf_eq _
  inflation := descendedBrauer_inflation P b reference psi.1

/-- The two quotient characters are identified by their canonical actual
pullbacks. The exact existing own root is retained, not equated to another. -/
theorem reference_brauer_transport :
    PrimeRegularClassFunction.equivAlongMulEquiv (referenceToOwn b reference psi).symm
        (P.quotientSource psi.1).brauer.1 =
      (referenceSource P b reference psi).brauer.1 := by
  apply PrimeRegularClassFunction.ext
  intro z
  change psi.1.1 (PrimeRegularElement.map
    (TypeCOddTwoOriginalOwnPairAmbient.quotientEquiv P psi.1).symm.toMonoidHom
    (PrimeRegularElement.map (referenceToOwn b reference psi).toMonoidHom z)) =
      psi.1.1 (PrimeRegularElement.map
        (referenceQuotientEquiv b reference).symm.toMonoidHom z)
  apply congrArg psi.1.1
  apply Subtype.ext
  exact (TypeCOddTwoOriginalOwnPairAmbient.quotientEquiv P psi.1).symm_apply_apply
    ((referenceQuotientEquiv b reference).symm z.1)

/-- Full actual quotient-character stabilizers, in the required direction. -/
def referenceStabilizerEquiv :
    QuotientBrauerAutomorphismStabilizer
        (P.blockProblem (P.brauerBlock psi.1)) (P.ownBrauer psi.1)
        (P.ownBrauer psi.1) (P.quotientSource psi.1) ≃*
      QuotientBrauerAutomorphismStabilizer (P.blockProblem b) reference psi
        (referenceSource P b reference psi) :=
  characterStabilizerEquiv (P.quotientSource psi.1).iota
    (referenceSource P b reference psi).iota (referenceToOwn b reference psi).symm
    (P.quotientSource psi.1).brauer (referenceSource P b reference psi).brauer
    (reference_brauer_transport P b reference psi)

variable (A : P.Ambient psi.1)

/-- Only the quotient coordinates change. A, base, centre and centralizer
are the original stored data, and the quotient action is computed. -/
def referenceAmbient : SpathAmbientGroup (P.blockProblem b) reference psi
    (referenceSource P b reference psi) where
  A := A.A
  groupA := A.groupA
  fintypeA := A.fintypeA
  base := A.base
  baseNormal := A.baseNormal
  baseEquiv := (referenceToOwn b reference psi).trans A.baseEquiv
  baseCentralizer_eq_center := A.baseCentralizer_eq_center
  centerPrimeTo := A.centerPrimeTo
  conjugation := (MulAut.congr (referenceToOwn b reference psi).symm).toMonoidHom.comp
    A.conjugation
  conjugation_on_base a z := by
    change (A.baseEquiv ((referenceToOwn b reference psi)
      ((referenceToOwn b reference psi).symm
        (A.conjugation a (referenceToOwn b reference psi z)))) : A.A) = _
    exact (congrArg (fun x => (A.baseEquiv x : A.A))
      ((referenceToOwn b reference psi).apply_symm_apply _)).trans
        (A.conjugation_on_base a (referenceToOwn b reference psi z))
  automorphismQuotientEquiv := A.automorphismQuotientEquiv.trans
    (referenceStabilizerEquiv P b reference psi)
  automorphismQuotientEquiv_natural a := by
    change oppositeAutEquiv (referenceToOwn b reference psi).symm
      ((A.automorphismQuotientEquiv (QuotientGroup.mk' (Subgroup.center A.A) a)).1) = _
    exact congrArg (oppositeAutEquiv (referenceToOwn b reference psi).symm)
      (A.automorphismQuotientEquiv_natural a)

@[simp] theorem referenceAmbient_base : (referenceAmbient P b reference psi A).base =
    A.base := rfl

/-- The original X-to-A map is unchanged under the canonical quotient map. -/
theorem referenceAmbient_embedding_square :
    (quotientToAmbient (P.blockProblem b) reference psi
      (referenceSource P b reference psi) (referenceAmbient P b reference psi A)).comp
        (centralCharacterQuotientMap (P.blockProblem b) reference) =
      P.baseEmbedding A := by
  apply MonoidHom.ext
  intro x
  change (A.baseEquiv (referenceToOwn b reference psi
    (centralCharacterQuotientMap (P.blockProblem b) reference x)) : A.A) =
      (A.baseEquiv (centralCharacterQuotientMap
        (P.blockProblem (P.brauerBlock psi.1)) (P.ownBrauer psi.1) x) : A.A)
  exact congrArg (fun z => (A.baseEquiv z : A.A))
    (referenceToOwn_square b reference psi x)

end ReferenceCoordinates

section SelectedMatching

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable {P : Problem n F} (D : Definition41 P) (b : P.Block)
variable (reference psi : Definition35Brauer (P.blockProblem b))

/-- The own selected matched ambient, now on the fixed reference quotient. -/
abbrev selectedReferenceAmbient :=
  referenceAmbient P b reference psi (selectedMatched D b psi).ambient

/-- Equality of the actual embedded subgroup includes the canonical
reference projection and the unchanged own selected pair. -/
theorem selectedReference_radical :
    EvenFieldFLZBAWGoodFamily.ambientRadical (P.blockProblem b) reference psi
      (blockEquiv D b psi) (referenceSource P b reference psi)
      (selectedReferenceAmbient D b reference psi) =
        P.ambientRadical (selectedMatched D b psi).ambient
          (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi) := by
  unfold EvenFieldFLZBAWGoodFamily.ambientRadical quotientRadical
  rw [Subgroup.map_map]
  exact congrArg (fun f => (selectedPair D b psi).subgroup.map f)
    (referenceAmbient_embedding_square P b reference psi (selectedMatched D b psi).ambient)

/-- Hence the full local ambient group is the same actual normalizer. -/
theorem selectedReference_localGroup :
    AmbientLocalGroup (P.blockProblem b) reference psi (blockEquiv D b psi)
      (referenceSource P b reference psi) (selectedReferenceAmbient D b reference psi) =
        P.LocalGroup (selectedMatched D b psi).ambient
          (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi) :=
  congrArg (fun Q : Subgroup (selectedMatched D b psi).ambient.A =>
    Subgroup.normalizer (Q : Set (selectedMatched D b psi).ambient.A))
      (selectedReference_radical D b reference psi)

/-- The Frattini premise is an existing own-pair consequence, not input. -/
theorem selectedReference_frattini :
    (selectedReferenceAmbient D b reference psi).base ⊔
      AmbientLocalGroup (P.blockProblem b) reference psi (blockEquiv D b psi)
        (referenceSource P b reference psi) (selectedReferenceAmbient D b reference psi) =
      ⊤ := by
  rw [selectedReference_localGroup]
  exact selectedMatched_frattini D b psi

/-- Every intermediate J can be compared with the original direct-H
presentation using H=J intersect N_A(Q), with the exact same ambient group. -/
theorem selectedReference_intermediate
    (J : Subgroup (selectedMatched D b psi).ambient.A)
    (hJ : (selectedReferenceAmbient D b reference psi).base ≤ J) :
    J = (selectedReferenceAmbient D b reference psi).base ⊔
      (J ⊓ AmbientLocalGroup (P.blockProblem b) reference psi (blockEquiv D b psi)
        (referenceSource P b reference psi) (selectedReferenceAmbient D b reference psi)) :=
  TypeCIntermediateNormalizerComparison.intermediate_eq_join_inf
    (selectedReferenceAmbient D b reference psi).base
    (AmbientLocalGroup (P.blockProblem b) reference psi (blockEquiv D b psi)
      (referenceSource P b reference psi) (selectedReferenceAmbient D b reference psi))
    J hJ (selectedReference_frattini D b reference psi)

end SelectedMatching

end ModularRep.PaperProofs.TypeCOddTwoOriginalReferenceAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
