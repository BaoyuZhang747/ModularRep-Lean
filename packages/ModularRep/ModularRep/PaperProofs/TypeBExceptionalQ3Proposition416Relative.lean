import ModularRep.ExceptionalQ3OutputCertificate
import Mathlib.Tactic

/-!
# Paper proof: the exceptional triple cover in type B

This file checks six manuscript-specific deductions in Proposition 4.11,
after the cited representation theory and the five GAP calculations have
been supplied as explicit inputs.

* The Feng--Yu--Zhang splitting parameter equation in dimension seven has
  exactly two solutions.  A source-shaped index-two covering interface then
  yields twelve principal weight classes with eight fixed by the covering
  involution.
* The two faithful-sector totals and the two known dihedral-block
  contributions force six weights in each of the remaining faithful blocks.
* The order-eight classification, the positive-height obstruction, the
  quaternion character count, and the computed five ordinary characters
  force the defect group of `B2` to be dihedral.
* The printed outer block involution has no nontrivial stabiliser on any of
  the four faithful blocks.
* From the actual `C2` outer quotient, inner fixation, and the computed action
  of one noninner representative, Lean derives the full printed block action.
  Every faithful block stabiliser then lies in the subgroup of inner
  automorphisms.  Once the standard fact that inner
  automorphisms fix characters and conjugacy classes of weights is supplied,
  Lean proves that every bijection on such a block is equivariant for its
  full stabiliser.  Equal finite cardinalities then supply the bijections to
  which the cited cyclic-outer-group criterion is applied.

No assertion about GAP, CTblLib, AtlasRep, the identification of a computed
group, the completeness of a subgroup enumeration, or the cited block theory
is proved here.  Those inputs are listed in the accompanying contract.
-/

namespace ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative

open Formalisation.ComputationArithmetic
open ModularRep.ManuscriptVerification.ExceptionalQ3OutputCertificate

/-! ## The two Feng--Yu--Zhang splitting parameters -/

/-- The two size parameters that remain from the Feng--Yu--Zhang covering
rule in dimension seven.  The first two coordinates are the sizes of the two
partitions and the third is the length of the staircase defining the
`2`-core. -/
def splittingParameterSizes : List (Nat × Nat × Nat) :=
  [(1, 0, 2), (0, 1, 2)]

/-- In dimension seven the source equation
`4 (|lambda_1| + |lambda_2|) + |kappa| = 7`, with the `2`-core `kappa`
the staircase of length `t`, is equivalent after multiplication by two to
the equation below.  It has precisely the two stated solutions. -/
theorem splitting_parameter_equation
    (a b t : Nat) (h : 8 * (a + b) + t * (t + 1) = 14) :
    (a = 1 ∧ b = 0 ∧ t = 2) ∨ (a = 0 ∧ b = 1 ∧ t = 2) := by
  have htprod : t * (t + 1) ≤ 14 := by omega
  have ht : t ≤ 3 := by nlinarith
  interval_cases t <;> simp_all <;> omega

theorem splittingParameterSizes_exact :
    splittingParameterSizes.length = 2 ∧ splittingParameterSizes.Nodup := by
  decide

theorem mem_splittingParameterSizes_iff (a b t : Nat) :
    (a, b, t) ∈ splittingParameterSizes ↔
      8 * (a + b) + t * (t + 1) = 14 := by
  constructor
  · intro h
    simp only [splittingParameterSizes, List.mem_cons] at h
    rcases h with h | h <;> simp_all
  · intro h
    rcases splitting_parameter_equation a b t h with h | h
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [splittingParameterSizes]
    · rcases h with ⟨rfl, rfl, rfl⟩
      simp [splittingParameterSizes]

/-! ### The principal-weight covering count -/

/-- The finite index type for the two solutions of the splitting equation.
Using indices, rather than a subtype of triples of natural numbers, keeps the
finite carrier explicit.  The preceding membership theorem identifies its
two entries with all solutions of the source equation. -/
abbrev SplittingParameterIndex := Fin splittingParameterSizes.length

theorem splittingParameterIndex_card :
    Fintype.card SplittingParameterIndex = 2 := by
  decide

/-- Source-shaped form of the covering rule used for the principal weights.

`HWeight` is the set of principal `SO_7(3)`-weight classes and `SWeight` is
the set of principal `Omega_7(3)`-weight classes.  The source
parametrisation identifies the classes that split with the finite parameter
set above.  The fibre-size and action fields express the index-two covering
rule.  They do not assume the resulting cardinalities or an equivariant
character--weight bijection.

In the intended instance, `hWeight_card` uses the equality in Feng--Yu--Zhang
Lemma 5.7 together with the computed principal Brauer count ten.  The
parametrisation and covering rule come from the proof of their Proposition
5.11.  Matching these abstract carriers with the actual weight classes is an
E2/U input. -/
structure PrincipalWeightCoveringInput
    (HWeight SWeight : Type*)
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight] where
  splits : HWeight → Prop
  splitsDecidable : DecidablePred splits
  splittingParametrisation :
    {weight : HWeight // splits weight} ≃ SplittingParameterIndex
  cover : SWeight → HWeight
  cover_surjective : Function.Surjective cover
  weightAction : Equiv.Perm SWeight
  weightAction_involutive : Function.Involutive weightAction
  cover_action : ∀ weight, cover (weightAction weight) = cover weight
  fibre_card : ∀ weight,
    Fintype.card {covered : SWeight // cover covered = weight} =
      if splits weight then 2 else 1
  split_weights_are_moved : ∀ weight,
    splits (cover weight) → weightAction weight ≠ weight
  hWeight_card : Fintype.card HWeight = 10

namespace PrincipalWeightCoveringInput

/-- The cited splitting parametrisation and the kernel-checked size equation
force exactly two splitting `SO_7(3)` weight classes.  This conclusion does
not use the two subgroup orders preselected by `o7weights.g`. -/
theorem splitting_weight_card
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    let _ := D.splitsDecidable
    Fintype.card {weight : HWeight // D.splits weight} = 2 := by
  let _ := D.splitsDecidable
  exact (Fintype.card_congr D.splittingParametrisation).trans
    splittingParameterIndex_card

theorem action_fixed_iff_not_split
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight)
    (weight : SWeight) :
    D.weightAction weight = weight ↔ ¬ D.splits (D.cover weight) := by
  let _ := D.splitsDecidable
  constructor
  · intro hfixed hsplit
    exact D.split_weights_are_moved weight hsplit hfixed
  · intro hnonsplit
    have hfibre :
        Fintype.card {covered : SWeight //
          D.cover covered = D.cover weight} = 1 := by
      simpa [hnonsplit] using D.fibre_card (D.cover weight)
    obtain ⟨only, honly⟩ := Fintype.card_eq_one_iff.mp hfibre
    let moved : {covered : SWeight // D.cover covered = D.cover weight} :=
      ⟨D.weightAction weight, D.cover_action weight⟩
    let original : {covered : SWeight // D.cover covered = D.cover weight} :=
      ⟨weight, rfl⟩
    exact congrArg Subtype.val ((honly moved).trans (honly original).symm)

/-- An index-two covering has one extra downstairs class for each splitting
upstairs class.  This is derived from the exact fibre sizes. -/
theorem sWeight_card_eq_hWeight_card_add_splitting_card
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    let _ := D.splitsDecidable
    Fintype.card SWeight = Fintype.card HWeight +
      Fintype.card {weight : HWeight // D.splits weight} := by
  let _ := D.splitsDecidable
  classical
  calc
    Fintype.card SWeight =
        Fintype.card (Σ weight : HWeight,
          {covered : SWeight // D.cover covered = weight}) :=
      Fintype.card_congr (Equiv.sigmaFiberEquiv D.cover).symm
    _ = ∑ weight : HWeight,
        Fintype.card {covered : SWeight // D.cover covered = weight} :=
      Fintype.card_sigma
    _ = ∑ weight : HWeight,
        (1 + if D.splits weight then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro weight _
      rw [D.fibre_card weight]
      by_cases hsplit : D.splits weight <;> simp [hsplit]
    _ = (∑ _weight : HWeight, 1) +
        ∑ weight : HWeight, if D.splits weight then 1 else 0 := by
      rw [Finset.sum_add_distrib]
    _ = Fintype.card HWeight +
        Fintype.card {weight : HWeight // D.splits weight} := by
      simp [Fintype.card_subtype]

def fixedCoverMap
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    Function.fixedPoints D.weightAction →
      {weight : HWeight // ¬ D.splits weight} := fun weight =>
  ⟨D.cover weight.1,
    (D.action_fixed_iff_not_split weight.1).mp weight.2⟩

theorem fixedCoverMap_bijective
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    Function.Bijective D.fixedCoverMap := by
  let _ := D.splitsDecidable
  constructor
  · intro x y hxy
    refine Subtype.ext ?_
    have hcover : D.cover x.1 = D.cover y.1 :=
      congrArg Subtype.val hxy
    have hnonsplit : ¬ D.splits (D.cover x.1) :=
      (D.action_fixed_iff_not_split x.1).mp x.2
    have hfibre :
        Fintype.card {covered : SWeight //
          D.cover covered = D.cover x.1} = 1 := by
      simpa [hnonsplit] using D.fibre_card (D.cover x.1)
    obtain ⟨only, honly⟩ := Fintype.card_eq_one_iff.mp hfibre
    let left : {covered : SWeight // D.cover covered = D.cover x.1} :=
      ⟨x.1, rfl⟩
    let right : {covered : SWeight // D.cover covered = D.cover x.1} :=
      ⟨y.1, hcover.symm⟩
    simpa [left, right] using
      congrArg Subtype.val ((honly left).trans (honly right).symm)
  · intro weight
    obtain ⟨covered, hcovered⟩ := D.cover_surjective weight.1
    have hfixed : D.weightAction covered = covered :=
      (D.action_fixed_iff_not_split covered).mpr
        (by simpa [hcovered] using weight.2)
    refine ⟨⟨covered, hfixed⟩, ?_⟩
    apply Subtype.ext
    exact hcovered

noncomputable def fixedCoverEquiv
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    Function.fixedPoints D.weightAction ≃
      {weight : HWeight // ¬ D.splits weight} :=
  Equiv.ofBijective D.fixedCoverMap D.fixedCoverMap_bijective

/-- The principal weight action has twelve points and eight fixed points.
Unlike the earlier external-signature interface, this theorem derives both
numbers from the ten upstairs classes, the exact splitting parametrisation,
and the index-two covering rule. -/
theorem principalWeight_action_signature
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    (Fintype.card SWeight,
      Fintype.card (Function.fixedPoints D.weightAction)) = (12, 8) := by
  let _ := D.splitsDecidable
  have hsplit := D.splitting_weight_card
  have hs := D.sWeight_card_eq_hWeight_card_add_splitting_card
  dsimp only at hsplit hs
  have hfixed : Fintype.card (Function.fixedPoints D.weightAction) =
      Fintype.card HWeight -
        Fintype.card {weight : HWeight // D.splits weight} := by
    rw [Fintype.card_congr D.fixedCoverEquiv]
    exact Fintype.card_subtype_compl D.splits
  have hsExact : Fintype.card SWeight = 12 := by
    rw [D.hWeight_card, hsplit] at hs
    omega
  have hfixedExact :
      Fintype.card (Function.fixedPoints D.weightAction) = 8 := by
    rw [D.hWeight_card, hsplit] at hfixed
    omega
  exact Prod.ext hsExact hfixedExact

/-- The source-shaped covering data supplies the formerly external principal
weight-action signature. -/
theorem toExternalPrincipalWeightActionInput
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight) :
    ExternalPrincipalWeightActionInput SWeight D.weightAction where
  involutive := D.weightAction_involutive
  card_eq := congrArg Prod.fst D.principalWeight_action_signature
  fixed_card_eq := congrArg Prod.snd D.principalWeight_action_signature

/-- Combining the covering count with the independently supplied alignment
of the two Brauer-label carriers yields the principal `C2`-set equivalence.
The carrier alignment remains U; no character--weight equivariance is an
input to this theorem. -/
theorem exists_principalC2Set_equivalence_of_coveringParametrisation
    {HWeight SWeight : Type*}
    [Fintype HWeight] [DecidableEq HWeight]
    [Fintype SWeight] [DecidableEq SWeight]
    (D : PrincipalWeightCoveringInput HWeight SWeight)
    (alignment : PrincipalRestrictionAlignmentInput) :
    ∃ equivalence : PrincipalBrauerLabel ≃ SWeight,
      ∀ label, equivalence (principalBrauerOuterAction label) =
        D.weightAction (equivalence label) :=
  exists_principalC2Set_equivalence_of_external_weight_input
    D.weightAction D.toExternalPrincipalWeightActionInput alignment

end PrincipalWeightCoveringInput

/-! ## Faithful-sector subtraction and block stabilisers -/

/-- The subtraction used for `B6` and `B7`, stated for arbitrary supplied
weight counts rather than only for the transcript numerals. -/
theorem faithful_sector_counts_forced
    (weightCount : Q3Block → Nat)
    (hOne : weightCount .B6 + weightCount .B8 = 8)
    (hTwo : weightCount .B7 + weightCount .B9 = 8)
    (hEight : weightCount .B8 = 2)
    (hNine : weightCount .B9 = 2) :
    weightCount .B6 = 6 ∧ weightCount .B7 = 6 := by
  omega

/-! ## The defect group of `B2` -/

/-- Source-shaped inputs for the short elimination of the defect group of
`B2`.  `DefectClass` is deliberately arbitrary: the classification of groups
of order eight is supplied by `classified`, rather than being built into an
inductive type whose constructors would silently assume exhaustiveness.

The positive-height obstruction and the quaternion character-count theorem
are representation theoretic inputs.  The value five is the separately
computed number of ordinary irreducible characters. -/
structure BlockTwoDefectInput (DefectClass : Type*) where
  defect : DefectClass
  IsAbelian : DefectClass → Prop
  IsDihedral : DefectClass → Prop
  IsQuaternion : DefectClass → Prop
  classified :
    IsAbelian defect ∨ IsDihedral defect ∨ IsQuaternion defect
  positiveHeight_excludes_abelian : ¬ IsAbelian defect
  ordinaryCharacterCount : Nat
  ordinaryCharacterCount_eq_five : ordinaryCharacterCount = 5
  quaternion_forces_six_characters :
    IsQuaternion defect → ordinaryCharacterCount = 6

namespace BlockTwoDefectInput

/-- The actual manuscript deduction for `B2`: the supplied classification
leaves three possibilities, positive height excludes the abelian case, and
the computed value five contradicts the supplied quaternion value six. -/
theorem defect_is_dihedral {DefectClass : Type*}
    (D : BlockTwoDefectInput DefectClass) :
    D.IsDihedral D.defect := by
  rcases D.classified with hab | hdih | hquat
  · exact (D.positiveHeight_excludes_abelian hab).elim
  · exact hdih
  · have hsix := D.quaternion_forces_six_characters hquat
    have hfive := D.ordinaryCharacterCount_eq_five
    omega

end BlockTwoDefectInput

/-- The nonidentity element of the printed outer quotient exchanges each of
the four faithful blocks and therefore fixes none of them. -/
theorem faithful_blocks_not_fixed_by_outer
    (block : Q3Block)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9) :
    blockOuterAction block ≠ block := by
  rcases hblock with rfl | rfl | rfl | rfl <;> decide

/-! ## The actual block stabilisers -/

/-- The E1/U interface identifying an actual outer quotient with `C2`.

The target `Equiv.Perm (Fin 2)` is the symmetric group on two points, hence
is cyclic of order two.  In the intended application `A` is the actual
automorphism group and `innerSubgroup` is its subgroup of inner
automorphisms.  The source identification of those groups is not proved in
this file. -/
structure C2OuterQuotientInput (A : Type*) [Group A] where
  innerSubgroup : Subgroup A
  outerClass : A →* Equiv.Perm (Fin 2)
  outerClass_surjective : Function.Surjective outerClass
  outerClass_ker : outerClass.ker = innerSubgroup

/-- The E3/U interface identifying the computed block involution with the
actual action of the nontrivial outer class.

The compatibility field says that inner automorphisms fix every block and
that every automorphism in the nontrivial outer class acts by the involution
transcribed in `o7blocks.out`. -/
structure ActualOuterBlockActionInput (A : Type*) [Group A]
    extends C2OuterQuotientInput A where
  blockPermutation : A →* Equiv.Perm Q3Block
  blockPermutation_compatible : ∀ α,
    blockPermutation α =
      if outerClass α = 1 then (1 : Equiv.Perm Q3Block)
      else blockOuterAction

/-- The symmetric group on two points has a unique nonidentity element. -/
theorem finTwo_perm_eq_of_ne_one
    (p q : Equiv.Perm (Fin 2)) (hp : p ≠ 1) (hq : q ≠ 1) : p = q := by
  have hcard : Fintype.card {r : Equiv.Perm (Fin 2) // r ≠ 1} = 1 := by
    decide
  obtain ⟨r, hr⟩ := Fintype.card_eq_one_iff.mp hcard
  exact congrArg Subtype.val ((hr ⟨p, hp⟩).trans (hr ⟨q, hq⟩).symm)

abbrev EncodedQ3Block := Formalisation.ComputationArithmetic.Q3Block

/-- Transport a permutation action through the E3/U identification of the
actual CTblLib set of blocks with the nine encoded block labels. -/
def transportBlockPermutation
    {Block : Type*} (blockLabel : Block ≃ EncodedQ3Block) :
    Equiv.Perm Block →* Equiv.Perm EncodedQ3Block where
  toFun permutation := blockLabel.symm.trans (permutation.trans blockLabel)
  map_one' := by
    ext block
    simp
  map_mul' left right := by
    ext block
    simp

/-- A source-shaped replacement for assuming the complete block-action
formula for every automorphism.

The CTblLib calculation supplies the action of one representative of the
nonidentity outer class on the actual set of blocks.  The routine quotient
`A/Inn = C2` and the fact that inner automorphisms fix blocks are separate E1
inputs.  Lean derives the action of every element of `A`.  The equivalence
`blockLabel` and the computed generator action remain the precise E3/U
carrier-matching boundary. -/
structure OuterGeneratorBlockActionInput
    (A Block : Type*) [Group A] [Fintype Block] [DecidableEq Block]
    extends C2OuterQuotientInput A where
  blockLabel : Block ≃ EncodedQ3Block
  blockPermutation : A →* Equiv.Perm Block
  inner_fixes_blocks : ∀ α,
    α ∈ innerSubgroup → blockPermutation α = 1
  outerGenerator : A
  outerGenerator_nontrivial : outerClass outerGenerator ≠ 1
  computed_outerGenerator_action : ∀ block,
    blockLabel (blockPermutation outerGenerator block) =
      blockOuterAction (blockLabel block)

namespace OuterGeneratorBlockActionInput

def transportedBlockPermutation
    {A Block : Type*} [Group A] [Fintype Block] [DecidableEq Block]
    (D : OuterGeneratorBlockActionInput A Block) :
    A →* Equiv.Perm EncodedQ3Block :=
  (transportBlockPermutation D.blockLabel).comp D.blockPermutation

theorem transported_outerGenerator_action
    {A Block : Type*} [Group A] [Fintype Block] [DecidableEq Block]
    (D : OuterGeneratorBlockActionInput A Block) :
    D.transportedBlockPermutation D.outerGenerator = blockOuterAction := by
  ext block
  simpa [transportedBlockPermutation, transportBlockPermutation] using
    D.computed_outerGenerator_action (D.blockLabel.symm block)

/-- The full nine-block action is a deduction from the one computed outer
generator, not an input quantified over all automorphisms. -/
theorem transportedBlockPermutation_compatible
    {A Block : Type*} [Group A] [Fintype Block] [DecidableEq Block]
    (D : OuterGeneratorBlockActionInput A Block) (α : A) :
    D.transportedBlockPermutation α =
      ite (D.outerClass α = Equiv.refl (Fin 2))
        (Equiv.refl EncodedQ3Block) blockOuterAction := by
  by_cases hclass : D.outerClass α = Equiv.refl (Fin 2)
  · rw [if_pos hclass]
    have hker : α ∈ D.outerClass.ker := hclass
    rw [D.outerClass_ker] at hker
    rw [transportedBlockPermutation, MonoidHom.comp_apply,
      D.inner_fixes_blocks α hker]
    exact map_one (transportBlockPermutation D.blockLabel)
  · rw [if_neg hclass]
    have hclasses : D.outerClass α = D.outerClass D.outerGenerator :=
      finTwo_perm_eq_of_ne_one _ _ hclass D.outerGenerator_nontrivial
    let innerPart : A := α * D.outerGenerator⁻¹
    have hinnerClass : D.outerClass innerPart = 1 := by
      simp only [innerPart, map_mul, map_inv, hclasses]
      exact mul_inv_cancel _
    have hinner : innerPart ∈ D.innerSubgroup := by
      have : innerPart ∈ D.outerClass.ker := hinnerClass
      rwa [D.outerClass_ker] at this
    have halpha : α = innerPart * D.outerGenerator := by
      simp [innerPart]
    rw [halpha, map_mul, transportedBlockPermutation,
      MonoidHom.comp_apply, D.inner_fixes_blocks innerPart hinner]
    simp only [map_one, one_mul]
    exact D.transported_outerGenerator_action

/-- The derived full action instantiates the older downstream interface used
by the faithful-block stabiliser theorem. -/
def toActualOuterBlockActionInput
    {A Block : Type*} [Group A] [Fintype Block] [DecidableEq Block]
    (D : OuterGeneratorBlockActionInput A Block) :
    ActualOuterBlockActionInput A where
  innerSubgroup := D.innerSubgroup
  outerClass := D.outerClass
  outerClass_surjective := D.outerClass_surjective
  outerClass_ker := D.outerClass_ker
  blockPermutation := D.transportedBlockPermutation
  blockPermutation_compatible := D.transportedBlockPermutation_compatible

end OuterGeneratorBlockActionInput

namespace ActualOuterBlockActionInput

/-- The stabiliser of an encoded block under the supplied actual
automorphism action. -/
def blockStabilizer {A : Type*} [Group A]
    (D : ActualOuterBlockActionInput A) (block : Q3Block) : Subgroup A :=
  (MulAction.stabilizer (Equiv.Perm Q3Block) block).comap
    D.blockPermutation

/-- For each faithful block, compatibility of the actual action with the
computed involution forces its full automorphism stabiliser to consist of
inner automorphisms. -/
theorem faithful_blockStabilizer_le_inner
    {A : Type*} [Group A]
    (D : ActualOuterBlockActionInput A)
    (block : Q3Block)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9) :
    D.blockStabilizer block ≤ D.innerSubgroup := by
  intro α hα
  have hfix : D.blockPermutation α block = block := by
    exact hα
  have hclass : D.outerClass α = 1 := by
    by_contra hnontrivial
    have hpermutation : D.blockPermutation α = blockOuterAction := by
      simpa [hnontrivial] using D.blockPermutation_compatible α
    have houterFixes : blockOuterAction block = block := by
      rw [← hpermutation]
      exact hfix
    exact (faithful_blocks_not_fixed_by_outer block hblock) houterFixes
  have hker : α ∈ D.outerClass.ker := by
    exact hclass
  rw [D.outerClass_ker] at hker
  exact hker

/-! ### Actions on the character and weight fibres -/

/-- Source-shaped actions on the Brauer-character and weight sets belonging
to one block.  The two action functions are the restrictions of the actual
automorphism actions to a block stabiliser.  The fields below supply only the
standard fact that inner automorphisms act trivially on characters and on
conjugacy classes of weights; they do not assume equivariance of a chosen
bijection. -/
structure FaithfulBlockFibreActions
    {A : Type*} [Group A]
    (D : ActualOuterBlockActionInput A)
    (block : Q3Block)
    (BrauerLabels WeightLabels : Type*) where
  brauerAction : D.blockStabilizer block → BrauerLabels → BrauerLabels
  weightAction : D.blockStabilizer block → WeightLabels → WeightLabels
  inner_fixes_brauer : ∀ (α : D.blockStabilizer block),
    (α : A) ∈ D.innerSubgroup → ∀ x,
    brauerAction α x = x
  inner_fixes_weight : ∀ (α : D.blockStabilizer block),
    (α : A) ∈ D.innerSubgroup → ∀ y,
    weightAction α y = y

namespace FaithfulBlockFibreActions

/-- Once the actual outer action shows that a faithful block stabiliser is
inner, every bijection between its Brauer-character and weight sets is
automatically equivariant for the full block stabiliser.  Equivariance is a
deduction here, not an input field. -/
theorem arbitrary_equiv_is_blockStabilizer_equivariant
    {A : Type*} [Group A]
    {BrauerLabels WeightLabels : Type*}
    (D : ActualOuterBlockActionInput A)
    (block : Q3Block)
    (F : FaithfulBlockFibreActions D block BrauerLabels WeightLabels)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9)
    (equivalence : BrauerLabels ≃ WeightLabels) :
    ∀ α : D.blockStabilizer block, ∀ x,
      equivalence (F.brauerAction α x) =
        F.weightAction α (equivalence x) := by
  intro α x
  have hinner : (α : A) ∈ D.innerSubgroup :=
    D.faithful_blockStabilizer_le_inner block hblock α.property
  rw [F.inner_fixes_brauer α hinner x,
    F.inner_fixes_weight α hinner (equivalence x)]

/-- Equal cardinalities now give the stabiliser-equivariant bijection used in
the faithful-block part of Proposition 4.11.  The only action inputs are the
actual outer block action and the standard triviality of inner actions on the
two fibres. -/
theorem exists_blockStabilizer_equivariant_equiv_of_card_eq
    {A : Type*} [Group A]
    {BrauerLabels WeightLabels : Type*}
    [Fintype BrauerLabels] [Fintype WeightLabels]
    (D : ActualOuterBlockActionInput A)
    (block : Q3Block)
    (F : FaithfulBlockFibreActions D block BrauerLabels WeightLabels)
    (hblock : block = .B6 ∨ block = .B7 ∨ block = .B8 ∨ block = .B9)
    (hcard : Fintype.card BrauerLabels = Fintype.card WeightLabels) :
    ∃ equivalence : BrauerLabels ≃ WeightLabels,
      ∀ α : D.blockStabilizer block, ∀ x,
        equivalence (F.brauerAction α x) =
          F.weightAction α (equivalence x) := by
  let equivalence : BrauerLabels ≃ WeightLabels :=
    Fintype.equivOfCardEq hcard
  exact ⟨equivalence,
    F.arbitrary_equiv_is_blockStabilizer_equivariant
      D block hblock equivalence⟩

end FaithfulBlockFibreActions

end ActualOuterBlockActionInput

/-! ## Relative construction of the nine blocks -/

universe u v

/-- Exact logical inputs left after the finite deductions above.

The five blocks in the trivial central sector are supplied by the principal,
dihedral, cyclic-defect, and defect-zero arguments in the manuscript.  For a
faithful block the final field records the application of Feng--Li--Zhang
Corollary 2.13 after the outer stabiliser has become inner and a finite
bijection has been constructed. -/
structure Inputs
    (BrauerLabels : Q3Block → Type u)
    (WeightLabels : Q3Block → Type v)
    [∀ block, Fintype (BrauerLabels block)]
    [∀ block, Fintype (WeightLabels block)] where
  BlockGood : Q3Block → Prop
  brauerCount : ∀ block,
    Fintype.card (BrauerLabels block) = q3BrauerCount block
  faithfulOneWeightTotal :
    Fintype.card (WeightLabels .B6) +
      Fintype.card (WeightLabels .B8) = 8
  faithfulTwoWeightTotal :
    Fintype.card (WeightLabels .B7) +
      Fintype.card (WeightLabels .B9) = 8
  blockEightWeightCount : Fintype.card (WeightLabels .B8) = 2
  blockNineWeightCount : Fintype.card (WeightLabels .B9) = 2
  blockOneGood : BlockGood .B1
  blockTwoGood : BlockGood .B2
  blockThreeGood : BlockGood .B3
  blockFourGood : BlockGood .B4
  blockFiveGood : BlockGood .B5
  good_of_bijection_with_inner_stabiliser : ∀ block,
    blockOuterAction block ≠ block →
    Nonempty (BrauerLabels block ≃ WeightLabels block) →
    BlockGood block

namespace Inputs

/-- The nine-block conclusion after the two faithful-sector subtractions and
the four finite bijections have been constructed.  In particular, goodness
of `B6` and `B7` is not an input. -/
theorem proposition_4_16_relative
    {BrauerLabels : Q3Block → Type u}
    {WeightLabels : Q3Block → Type v}
    [∀ block, Fintype (BrauerLabels block)]
    [∀ block, Fintype (WeightLabels block)]
    (D : Inputs BrauerLabels WeightLabels) :
    ∀ block, D.BlockGood block := by
  have hfaithful := faithful_sector_counts_forced
    (fun block => Fintype.card (WeightLabels block))
    D.faithfulOneWeightTotal D.faithfulTwoWeightTotal
    D.blockEightWeightCount D.blockNineWeightCount
  intro block
  cases block with
  | B1 => exact D.blockOneGood
  | B2 => exact D.blockTwoGood
  | B3 => exact D.blockThreeGood
  | B4 => exact D.blockFourGood
  | B5 => exact D.blockFiveGood
  | B6 =>
      apply D.good_of_bijection_with_inner_stabiliser .B6 (by decide)
      refine ⟨Fintype.equivOfCardEq ?_⟩
      calc
        Fintype.card (BrauerLabels .B6) = q3BrauerCount .B6 :=
          D.brauerCount .B6
        _ = 6 := rfl
        _ = Fintype.card (WeightLabels .B6) := hfaithful.1.symm
  | B7 =>
      apply D.good_of_bijection_with_inner_stabiliser .B7 (by decide)
      refine ⟨Fintype.equivOfCardEq ?_⟩
      calc
        Fintype.card (BrauerLabels .B7) = q3BrauerCount .B7 :=
          D.brauerCount .B7
        _ = 6 := rfl
        _ = Fintype.card (WeightLabels .B7) := hfaithful.2.symm
  | B8 =>
      apply D.good_of_bijection_with_inner_stabiliser .B8 (by decide)
      refine ⟨Fintype.equivOfCardEq ?_⟩
      calc
        Fintype.card (BrauerLabels .B8) = q3BrauerCount .B8 :=
          D.brauerCount .B8
        _ = 2 := rfl
        _ = Fintype.card (WeightLabels .B8) :=
          D.blockEightWeightCount.symm
  | B9 =>
      apply D.good_of_bijection_with_inner_stabiliser .B9 (by decide)
      refine ⟨Fintype.equivOfCardEq ?_⟩
      calc
        Fintype.card (BrauerLabels .B9) = q3BrauerCount .B9 :=
          D.brauerCount .B9
        _ = 2 := rfl
        _ = Fintype.card (WeightLabels .B9) :=
          D.blockNineWeightCount.symm

end Inputs

end ModularRep.PaperProofs.TypeBExceptionalQ3Proposition416Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
