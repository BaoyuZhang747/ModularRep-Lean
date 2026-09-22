import ModularRep.PaperProofs.OddTwoPrincipalFamilyCharacterData
import ModularRep.PaperProofs.OddTwoPrincipalFamilyAutomorphisms
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport

/-!
# Canonical actions on the computed principal family fibres

The Brauer and weight maps are precisely the computed restrictions of the
actual group-equivalence maps. The acting-group map is the computed full
automorphism equivalence, followed by conjugation through the SAME routed
group equivalence. Their naturality is proved for the canonical Definition
3.5 actions, including the inverse/op convention.

The intrinsic relation below is DEFINED as the pullback of the fixed family
relation. Its forward transport therefore needs no extra relation or action
law. This definition does not authenticate an intrinsic character-triple
interpretation. Identifying it with standard actual triples for EVERY
admissible selected root packet remains a separate join. No seed, witness,
source covariance, selected-pair equality or compatible-root square is
asserted here. The intrinsic selected reduction is an explicit parameter.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
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

universe u

private theorem inverse_naturality
    {A B X Y : Type*} [Group A] [Group B]
    [MulAction A X] [MulAction B Y]
    (e : A ≃* B) (f : X ≃ Y)
    (h : ∀ a x, f (a • x) = e a • f x) (b : B) (y : Y) :
    f.symm (b • y) = e.symm b • f.symm y := by
  apply f.injective
  calc
    f (f.symm (b • y)) = b • y := f.apply_symm_apply _
    _ = e (e.symm b) • f (f.symm y) := by
      rw [e.apply_symm_apply, f.apply_symm_apply]
    _ = f (e.symm b • f.symm y) := (h _ _).symm

variable (family : Definition35Family.{u} 2) (block : family.Block)
variable {rank : ℕ} {F : Type u} [Field F] [Fintype F]
variable (carrier : OddSymplecticPrincipalCarrier (family.problem block) rank F)

local instance familyFibreSpFintype : Fintype (Sp rank F) := Fintype.ofFinite _

variable (input : TypeAInputSemantics family)
variable (OH : LocalBlockInductionOperations
  (p := 2) (k := family.k) (K := family.K) (G := Sp rank F) (Block := family.Block))
variable (dictionary : PrimitiveDictionary family.blockSource.operations OH
  (groupEquiv family block carrier))

/-- A reduction for the actual selected representative of each computed
intrinsic weight. This remains a parameter, not a new existence assertion. -/
abbrev Reduction : Type u :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  ∀ w : (data family block carrier input OH dictionary).PrincipalWeight,
    SelectedLocalReductionSource
      (data family block carrier input OH dictionary).blockSource
      (data family block carrier input OH dictionary).principalBlock w

variable (reduction : Reduction family block carrier input OH dictionary)

/-- The literal problem of the computed character data and supplied table. -/
abbrev intrinsicProblem : Definition35Problem.{u} :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  (data family block carrier input OH dictionary).problem reduction

/-- Its actual full-automorphism stabilizer adapter is already constructed. -/
def intrinsicAutomorphisms :
    Definition35AutomorphismStabilizerAdapter
      (intrinsicProblem family block carrier input OH dictionary reduction) :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  (data family block carrier input OH dictionary).automorphisms reduction

/-- The SAME computed Brauer fibre equivalence, displayed as problem fibres. -/
def toIntrinsicBrauer :
    Definition35Brauer (family.problem block) ≃
      Definition35Brauer (intrinsicProblem family block carrier input OH dictionary reduction) :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  brauerEquiv family block carrier input OH dictionary

/-- The SAME computed own-character weight-class fibre equivalence. -/
def toIntrinsicWeight :
    Definition35Weight (family.problem block) ≃
      Definition35Weight (intrinsicProblem family block carrier input OH dictionary reduction) :=
  letI := transportedBlockAction (Block := family.Block) (groupEquiv family block carrier)
  weightEquiv family block carrier input OH dictionary

@[simp] theorem toIntrinsicBrauer_character
    (psi : Definition35Brauer (family.problem block)) :
    (toIntrinsicBrauer family block carrier input OH dictionary reduction psi).1 =
      IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
        (groupEquiv family block carrier) (psi.1 : IBr family.iota) := rfl

@[simp] theorem toIntrinsicWeight_class
    (w : Definition35Weight (family.problem block)) :
    (toIntrinsicWeight family block carrier input OH dictionary reduction w).1 =
      CharacterWeight.conjugacyClassGroupEquiv (groupEquiv family block carrier) w.1 := rfl

variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem block))

/-- The actual acting-group equivalence; its value uses the family's gamma. -/
def gammaEquiv :
    (family.problem block).Gamma ≃*
      (intrinsicProblem family block carrier input OH dictionary reduction).Gamma :=
  symplecticAutEquiv family block carrier adapter

@[simp] theorem gammaEquiv_apply (a : (family.problem block).Gamma) :
    gammaEquiv family block carrier input OH dictionary reduction adapter a =
      MulAut.congr (groupEquiv family block carrier) ((family.problem block).gamma a) := rfl

/-- The canonical inverse/op homomorphisms agree under these coordinates. -/
theorem inverseOp_coordinates (a : (family.problem block).Gamma) :
    inverseOpHom
        (intrinsicProblem family block carrier input OH dictionary reduction).gamma
        (gammaEquiv family block carrier input OH dictionary reduction adapter a) =
      MulOpposite.op (MulAut.congr (groupEquiv family block carrier)
        (inverseOpHom (family.problem block).gamma a).unop) := by
  change MulOpposite.op
      (gammaEquiv family block carrier input OH dictionary reduction adapter a)⁻¹ =
    MulOpposite.op
      (gammaEquiv family block carrier input OH dictionary reduction adapter a⁻¹)
  exact congrArg MulOpposite.op
    ((gammaEquiv family block carrier input OH dictionary reduction adapter).map_inv a).symm

/-- Naturality on Brauer fibres uses only the canonical problem actions. -/
theorem brauer_naturality :
    letI : MulAction (family.problem block).Gamma
        (Definition35Brauer (family.problem block)) :=
      definition35BrauerAction (family.problem block)
    letI : MulAction
        (intrinsicProblem family block carrier input OH dictionary reduction).Gamma
        (Definition35Brauer
          (intrinsicProblem family block carrier input OH dictionary reduction)) :=
      definition35BrauerAction
        (intrinsicProblem family block carrier input OH dictionary reduction)
    ∀ (a : (family.problem block).Gamma)
        (psi : Definition35Brauer (family.problem block)),
      toIntrinsicBrauer family block carrier input OH dictionary reduction (a • psi) =
        gammaEquiv family block carrier input OH dictionary reduction adapter a •
          toIntrinsicBrauer family block carrier input OH dictionary reduction psi := by
  letI : MulAction (family.problem block).Gamma
      (Definition35Brauer (family.problem block)) :=
    definition35BrauerAction (family.problem block)
  letI : MulAction
      (intrinsicProblem family block carrier input OH dictionary reduction).Gamma
      (Definition35Brauer
        (intrinsicProblem family block carrier input OH dictionary reduction)) :=
    definition35BrauerAction
      (intrinsicProblem family block carrier input OH dictionary reduction)
  intro a psi
  apply Subtype.ext
  have h := IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul family.iota
    (groupEquiv family block carrier) (psi.1 : IBr family.iota)
    (inverseOpHom (family.problem block).gamma a)
  exact h.trans (congrArg
    (fun alpha : (MulAut (Sp rank F))ᵐᵒᵖ =>
      @HSMul.hSMul (MulAut (Sp rank F))ᵐᵒᵖ
        (IBr (family.iota.alongMulEquiv (groupEquiv family block carrier)))
        (IBr (family.iota.alongMulEquiv (groupEquiv family block carrier)))
        inferInstance alpha
        (IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota
          (groupEquiv family block carrier) (psi.1 : IBr family.iota)))
    (inverseOp_coordinates family block carrier input OH dictionary reduction adapter a).symm)

/-- Naturality on weight fibres uses the actual own-character class action. -/
theorem weight_naturality :
    letI : MulAction (family.problem block).Gamma
        (Definition35Weight (family.problem block)) :=
      definition35WeightAction (family.problem block)
    letI : MulAction
        (intrinsicProblem family block carrier input OH dictionary reduction).Gamma
        (Definition35Weight
          (intrinsicProblem family block carrier input OH dictionary reduction)) :=
      definition35WeightAction
        (intrinsicProblem family block carrier input OH dictionary reduction)
    ∀ (a : (family.problem block).Gamma)
        (w : Definition35Weight (family.problem block)),
      toIntrinsicWeight family block carrier input OH dictionary reduction (a • w) =
        gammaEquiv family block carrier input OH dictionary reduction adapter a •
          toIntrinsicWeight family block carrier input OH dictionary reduction w := by
  letI : MulAction (family.problem block).Gamma
      (Definition35Weight (family.problem block)) :=
    definition35WeightAction (family.problem block)
  letI : MulAction
      (intrinsicProblem family block carrier input OH dictionary reduction).Gamma
      (Definition35Weight
        (intrinsicProblem family block carrier input OH dictionary reduction)) :=
    definition35WeightAction
      (intrinsicProblem family block carrier input OH dictionary reduction)
  intro a w
  apply Subtype.ext
  have h := CharacterWeight.conjugacyClassGroupEquiv_op_smul
    (groupEquiv family block carrier) (inverseOpHom (family.problem block).gamma a) w.1
  exact h.trans (congrArg
    (fun alpha : (MulAut (Sp rank F))ᵐᵒᵖ =>
      @HSMul.hSMul (MulAut (Sp rank F))ᵐᵒᵖ
        (CharacterWeight.ConjugacyClass (p := 2) (K := family.K) (G := Sp rank F))
        (CharacterWeight.ConjugacyClass (p := 2) (K := family.K) (G := Sp rank F))
        inferInstance alpha
        (CharacterWeight.conjugacyClassGroupEquiv (groupEquiv family block carrier) w.1))
    (inverseOp_coordinates family block carrier input OH dictionary reduction adapter a).symm)

variable (source : FLZSourceSemantics (family.problem block) adapter)

/-- Literal pullback of the fixed family relation. This asserts neither
relation and does not supply an authentic actual-triple interpretation. -/
def intrinsicSource :
    FLZSourceSemantics
      (intrinsicProblem family block carrier input OH dictionary reduction)
      (intrinsicAutomorphisms family block carrier input OH dictionary reduction) where
  definition35BlockIsomorphic psi w := source.definition35BlockIsomorphic
    ((toIntrinsicBrauer family block carrier input OH dictionary reduction).symm psi)
    ((toIntrinsicWeight family block carrier input OH dictionary reduction).symm w)

@[simp] theorem intrinsicSource_relation
    (psi : Definition35Brauer
      (intrinsicProblem family block carrier input OH dictionary reduction))
    (w : Definition35Weight
      (intrinsicProblem family block carrier input OH dictionary reduction)) :
    (intrinsicSource family block carrier input OH dictionary reduction adapter source).definition35BlockIsomorphic
        psi w ↔
      source.definition35BlockIsomorphic
        ((toIntrinsicBrauer family block carrier input OH dictionary reduction).symm psi)
        ((toIntrinsicWeight family block carrier input OH dictionary reduction).symm w) := Iff.rfl

/-- The intrinsic-to-family transport is computed. Its three maps are the
inverse coordinate maps, naturality follows from the actual actions, and
the relation implication is the definition of the pullback above. -/
def forwardTransport :
    Definition35ForwardTransport
      (intrinsicProblem family block carrier input OH dictionary reduction)
      (intrinsicAutomorphisms family block carrier input OH dictionary reduction)
      (intrinsicSource family block carrier input OH dictionary reduction adapter source)
      (family.problem block) adapter source where
  gammaEquiv := (gammaEquiv family block carrier input OH dictionary reduction adapter).symm
  brauerEquiv := (toIntrinsicBrauer family block carrier input OH dictionary reduction).symm
  weightEquiv := (toIntrinsicWeight family block carrier input OH dictionary reduction).symm
  brauer_naturality := by
    letI : MulAction (family.problem block).Gamma
        (Definition35Brauer (family.problem block)) :=
      definition35BrauerAction (family.problem block)
    letI : MulAction
        (intrinsicProblem family block carrier input OH dictionary reduction).Gamma
        (Definition35Brauer
          (intrinsicProblem family block carrier input OH dictionary reduction)) :=
      definition35BrauerAction
        (intrinsicProblem family block carrier input OH dictionary reduction)
    exact inverse_naturality
      (gammaEquiv family block carrier input OH dictionary reduction adapter)
      (toIntrinsicBrauer family block carrier input OH dictionary reduction)
      (brauer_naturality family block carrier input OH dictionary reduction adapter)
  weight_naturality := by
    letI : MulAction (family.problem block).Gamma
        (Definition35Weight (family.problem block)) :=
      definition35WeightAction (family.problem block)
    letI : MulAction
        (intrinsicProblem family block carrier input OH dictionary reduction).Gamma
        (Definition35Weight
          (intrinsicProblem family block carrier input OH dictionary reduction)) :=
      definition35WeightAction
        (intrinsicProblem family block carrier input OH dictionary reduction)
    exact inverse_naturality
      (gammaEquiv family block carrier input OH dictionary reduction adapter)
      (toIntrinsicWeight family block carrier input OH dictionary reduction)
      (weight_naturality family block carrier input OH dictionary reduction adapter)
  relation_forward := fun _ _ h => h

@[simp] theorem forwardTransport_gamma :
    (forwardTransport family block carrier input OH dictionary reduction adapter source).gammaEquiv =
      (gammaEquiv family block carrier input OH dictionary reduction adapter).symm := rfl

@[simp] theorem forwardTransport_brauer :
    (forwardTransport family block carrier input OH dictionary reduction adapter source).brauerEquiv =
      (toIntrinsicBrauer family block carrier input OH dictionary reduction).symm := rfl

@[simp] theorem forwardTransport_weight :
    (forwardTransport family block carrier input OH dictionary reduction adapter source).weightEquiv =
      (toIntrinsicWeight family block carrier input OH dictionary reduction).symm := rfl

end ModularRep.PaperProofs.OddTwoPrincipalFamilyFibreActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
