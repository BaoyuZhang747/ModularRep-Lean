import ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions
import ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

/-!
# Computed intrinsic-to-family principal carrier transport

The three fibre/action maps and forward relation are the existing computed
FibreActions.forwardTransport. This file binds them to e.symm, identity
coefficients, actual selected whole weight images, and the actual Brauer
and gamma coordinates. The compatible target raw representative need not
be the independently selected family representative.

No seed, corrected map, authentic relation interpretation, selected-pair
equivariance, value compatibility or carrier-transport record is an input.
Authenticating the pulled-back relation remains the separate uniform
FullHG interpretation join before the principal engine is applied.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilySeedTransport

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
open ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoTypeASourceJoin
open ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
open ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
open ModularRep.PaperProofs.OddTwoPrincipalFamilyAutomorphisms
open ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

universe u

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)
variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))
variable (reduction : Reduction family block carrier input OH dictionary)

local instance familySeedTransportSpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

/-- The source principal carrier uses D's actual constant-one character;
rank and oddness are inherited from the routed carrier, not a new source. -/
def intrinsicCarrier : OddSymplecticPrincipalCarrier
    (intrinsicProblem family block carrier input OH dictionary reduction) rank F := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  exact
    { rankAtLeastTwo := carrier.rankAtLeastTwo
      fieldOdd := carrier.fieldOdd
      coefficientTwo := rfl
      symplecticEquiv := MulEquiv.refl _
      principalCharacter := ⟨(data family block carrier input OH dictionary).trivialCharacter, rfl⟩
      principalCharacter_value_one := (data family block carrier input OH dictionary).trivial_value }

/-- Map the intrinsic selection as a WHOLE raw pair by the actual e.symm. -/
def targetPair
    (w : Definition35Weight
      (intrinsicProblem family block carrier input OH dictionary reduction)) :
    CharacterWeight 2 family.K family.H :=
  (selectedCharacterWeight
    (intrinsicProblem family block carrier input OH dictionary reduction).blockSource
    (intrinsicProblem family block carrier input OH dictionary reduction).block w).mapGroupEquiv
      (groupEquiv family block carrier).symm

/-- The class is the precise inverse fibre image, using both inverse laws
and the actual selection specification. No class equation is a source field. -/
theorem targetPair_class
    (w : Definition35Weight
      (intrinsicProblem family block carrier input OH dictionary reduction)) :
    weightClass (targetPair family block carrier input OH dictionary reduction w) =
      ((toIntrinsicWeight family block carrier input OH dictionary reduction).symm w).1 := by
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  letI : MulAction (MulAut (Sp rank F))ᵐᵒᵖ
      (intrinsicProblem family block carrier input OH dictionary reduction).Block :=
    transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  let C := CharacterWeight.conjugacyClassGroupEquiv (p := 2) (K := family.K)
    (groupEquiv family block carrier)
  have selected := selectedCharacterWeight_spec
    (intrinsicProblem family block carrier input OH dictionary reduction).blockSource
    (intrinsicProblem family block carrier input OH dictionary reduction).block w
  have image := toIntrinsicWeight_class family block carrier input OH dictionary reduction
    ((toIntrinsicWeight family block carrier input OH dictionary reduction).symm w)
  have cancel := congrArg Subtype.val
    ((toIntrinsicWeight family block carrier input OH dictionary reduction).apply_symm_apply w)
  have exactImage : C
      ((toIntrinsicWeight family block carrier input OH dictionary reduction).symm w).1 = w.1 :=
    image.symm.trans cancel
  change C.symm (weightClass (selectedCharacterWeight
    (intrinsicProblem family block carrier input OH dictionary reduction).blockSource
    (intrinsicProblem family block carrier input OH dictionary reduction).block w)) = _
  exact (congrArg C.symm selected).trans
    ((congrArg C.symm exactImage.symm).trans (C.symm_apply_apply _))

/-- Every field is computed from the actual whole-pair map. The permitted
target is this compatible representative, not an equivariant selection. -/
def selectedWeights : SelectedWeightTransport
    (intrinsicProblem family block carrier input OH dictionary reduction)
    (family.problem block) (groupEquiv family block carrier).symm
    (RingEquiv.refl family.K)
    (toIntrinsicWeight family block carrier input OH dictionary reduction).symm where
  targetRepresentative := targetPair family block carrier input OH dictionary reduction
  target_class := targetPair_class family block carrier input OH dictionary reduction
  subgroup_map := fun _ => rfl
  normalizerEquiv w := ModularRep.normalizerEquiv (groupEquiv family block carrier).symm
    (selectedCharacterWeight
      (intrinsicProblem family block carrier input OH dictionary reduction).blockSource
      (intrinsicProblem family block carrier input OH dictionary reduction).block w).subgroup
  normalizer_coe := fun _ _ => rfl
  quotientEquiv w := normalizerQuotientEquiv (groupEquiv family block carrier).symm
    (selectedCharacterWeight
      (intrinsicProblem family block carrier input OH dictionary reduction).blockSource
      (intrinsicProblem family block carrier input OH dictionary reduction).block w).subgroup
  quotient_mk := fun _ _ => rfl
  localCharacter_values w x := mapGroupEquiv_localCharacter_image
    (selectedCharacterWeight
      (intrinsicProblem family block carrier input OH dictionary reduction).blockSource
      (intrinsicProblem family block carrier input OH dictionary reduction).block w)
    (groupEquiv family block carrier).symm x

/-- Its family block membership is derived from the actual class and fibre. -/
theorem targetPair_block
    (w : Definition35Weight
      (intrinsicProblem family block carrier input OH dictionary reduction)) :
    family.blockSource.operations.rawWeightBlock
      (targetPair family block carrier input OH dictionary reduction w) = block :=
  (selectedWeights family block carrier input OH dictionary reduction).targetRepresentative_block w

/-- The inverse computed Brauer fibre map has the actual e.symm values. -/
theorem inverseBrauer_values
    (psi : Definition35Brauer
      (intrinsicProblem family block carrier input OH dictionary reduction))
    (x : PrimeRegularElement (G := Sp rank F) 2) :
    ((toIntrinsicBrauer family block carrier input OH dictionary reduction).symm psi).1.1
        (primeRegularElementEquiv (groupEquiv family block carrier).symm (rfl : 2 = 2) x) =
      psi.1.1 x := by
  have image := toIntrinsicBrauer_character family block carrier input OH dictionary reduction
    ((toIntrinsicBrauer family block carrier input OH dictionary reduction).symm psi)
  have cancel := congrArg Subtype.val
    ((toIntrinsicBrauer family block carrier input OH dictionary reduction).apply_symm_apply psi)
  exact congrArg (fun chi : IBr (symplecticRoot family block carrier) => chi.1 x)
    (image.symm.trans cancel)

variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem block))

/-- The actual adapter is supplied independently; in FullHG it is
blockSource.automorphisms pair block, not the family's action record. -/
theorem inverseGamma_coordinates
    (a : (intrinsicProblem family block carrier input OH dictionary reduction).Gamma)
    (x : Sp rank F) :
    (groupEquiv family block carrier).symm
        ((intrinsicProblem family block carrier input OH dictionary reduction).gamma a x) =
      (family.problem block).gamma
        ((gammaEquiv family block carrier input OH dictionary reduction adapter).symm a)
        ((groupEquiv family block carrier).symm x) := by
  let alpha : MulAut (Sp rank F) := a
  apply (groupEquiv family block carrier).injective
  have square := symplecticAutEquiv_symm_coordinates family block carrier adapter alpha
    ((groupEquiv family block carrier).symm x)
  exact ((groupEquiv family block carrier).apply_symm_apply (alpha x)).trans
    ((congrArg alpha ((groupEquiv family block carrier).apply_symm_apply x)).symm.trans square.symm)

variable (source : FLZSourceSemantics (family.problem block) adapter)

/-- The entire carrier-transport packet is a K construction. Its forward
relation field is inherited from the DEFINITION of the same intrinsicSource;
authenticating that source remains the separate FullHG interpretation join. -/
def carrierTransport : PrincipalSeedCarrierTransport
    (intrinsicProblem family block carrier input OH dictionary reduction)
    (intrinsicAutomorphisms family block carrier input OH dictionary reduction)
    (intrinsicSource family block carrier input OH dictionary reduction adapter source)
    (family.problem block) adapter source rank F where
  sourceCarrier := intrinsicCarrier family block carrier input OH dictionary reduction
  transport := forwardTransport family block carrier input OH dictionary reduction adapter source
  groupEquiv := (groupEquiv family block carrier).symm
  coefficientPrime_eq := rfl
  coefficientFieldEquiv := RingEquiv.refl family.K
  selectedWeights := selectedWeights family block carrier input OH dictionary reduction
  brauer_values := inverseBrauer_values family block carrier input OH dictionary reduction
  gamma_compatible := inverseGamma_coordinates family block carrier input OH dictionary reduction adapter

@[simp] theorem carrierTransport_group :
    (carrierTransport family block carrier input OH dictionary reduction adapter source).groupEquiv =
      carrier.symplecticEquiv.symm := rfl

@[simp] theorem carrierTransport_coefficients :
    (carrierTransport family block carrier input OH dictionary reduction adapter source).coefficientFieldEquiv =
      RingEquiv.refl family.K := rfl

@[simp] theorem carrierTransport_forward :
    (carrierTransport family block carrier input OH dictionary reduction adapter source).transport =
      forwardTransport family block carrier input OH dictionary reduction adapter source := rfl

end ModularRep.PaperProofs.OddTwoPrincipalFamilySeedTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
