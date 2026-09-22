import ModularRep.PaperProofs.EvenFieldP38FamilyGammaEquivariance
import ModularRep.PaperProofs.TypeCBlockStabilizerTupleTransport

/-!
# Pointwise Definition 3.5 transport at the chosen P38 packets

One admissible own-normalizer packet is fixed for every family weight. Its
two root squares refer to the actual ambient root and the exact stored
quotient reduction. The concrete table is computed through the previously
proved equality of WHOLE selected pairs. No independent root equality is
assumed.

The definition dictionary below interprets the two existing predicates at
these chosen packets; it asserts neither predicate. Actual block-stabilizer,
group-equivalence and inner-correction comparisons then prove transport in K.
The final map uses the bijection RETURNED by the existing FLZ 3.18 source.
It is not identified with the separately constructed P38 endgame map.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldP38ChosenDefinition35Transport

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldConcreteTypeC EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldClassifiedP38FamilyPacket EvenFieldP38ChosenFamilyReduction
open EvenFieldProposition39HighRankU0 EvenFieldFLZ318FixedTheoremGate
open EvenFieldFLZDefinition35Transport
open OddTwoActualStabilizerTriple OddTwoActualCentralInflationPacket
open OddTwoActualLocalBlockSupport OddTwoDefinition35OwnReduction
open OddTwoCentralTwoRelationInflation OddTwoStandardBlockTripleTransport
open TypeCSelectedPairGroupEquivCoordinates TypeCChosenPairRootTransport

universe u

local instance chosenSubgroupFintype {G : Type u} [Group G] [Finite G]
    (Q : Subgroup G) : Fintype Q := Fintype.ofFinite Q

local instance chosenFiniteAut (G : Type u) [Group G] [Finite G] : Finite (MulAut G) :=
  Finite.of_injective (fun a : MulAut G => (a : G → G)) DFunLike.coe_injective

/-- ONE chosen own reduction with both exact source-root guards. This is
conventional data, not a relation, extension, or existence theorem. -/
structure ChosenOwnReduction (P : Definition35Problem.{u})
    (w : Definition35Weight P) where
  reduction : OwnNormalizerReduction (k := P.k)
    (selectedCharacterWeight P.blockSource P.block w)
  ambientCompatible : RootCompatibleAlong P.iota
    (ownReductionRoot (selectedCharacterWeight P.blockSource P.block w) reduction)
    (Subgroup.normalizer
      ((selectedCharacterWeight P.blockSource P.block w).subgroup : Set P.H)).subtype
  quotientCompatible : RootCompatibleAlong (P.localReduction w).iota
    (ownReductionRoot (selectedCharacterWeight P.blockSource P.block w) reduction)
    (normalizerProjection (selectedCharacterWeight P.blockSource P.block w).subgroup)

/-- The actual full-raw containment and the authentic standard tuple at
the chosen own character. Neither conjunct is built into the packet. -/
def chosenCondition (P : Definition35Problem.{u})
    (standard : BlockTripleSourceSemantics P.p P.k P.K)
    (packets : ∀ w : Definition35Weight P, ChosenOwnReduction P w)
    (psi : Definition35Brauer P) (w : Definition35Weight P) : Prop :=
  (rawStabilizer P.gamma (selectedCharacterWeight P.blockSource P.block w) ≤
    globalStabilizer P.iota P.gamma psi.1) ∧
  standard.blockIsomorphic (arguments P.iota P.gamma psi.1
    (selectedCharacterWeight P.blockSource P.block w) (packets w).reduction)

/-- E1 definition interpretation at the ONE chosen table. The standard
predicate must mean the published block-triple relation. This field is not
an E2 theorem output, and asserts neither side of its equivalence. -/
structure ChosenDefinition35Interpretation (P : Definition35Problem.{u})
    (adapter : Definition35AutomorphismStabilizerAdapter P)
    (flz : FLZSourceSemantics P adapter)
    (standard : BlockTripleSourceSemantics P.p P.k P.K)
    (packets : ∀ w : Definition35Weight P, ChosenOwnReduction P w) : Prop where
  relation_iff : ∀ (psi : Definition35Brauer P) (w : Definition35Weight P),
    flz.definition35BlockIsomorphic psi w ↔ chosenCondition P standard packets psi w

/-- K specialization of an already available uniform definition dictionary,
such as the exact FullHG.definition35_iff. It introduces no second meaning
assumption where that stronger dictionary is available. -/
def ChosenDefinition35Interpretation.ofUniform (P : Definition35Problem.{u})
    (adapter : Definition35AutomorphismStabilizerAdapter P)
    (flz : FLZSourceSemantics P adapter)
    (standard : BlockTripleSourceSemantics P.p P.k P.K)
    (packets : ∀ w : Definition35Weight P, ChosenOwnReduction P w)
    (meaning : ∀ (psi : Definition35Brauer P) (w : Definition35Weight P)
      (R : OwnNormalizerReduction (k := P.k)
        (selectedCharacterWeight P.blockSource P.block w)),
      RootCompatibleAlong P.iota
          (ownReductionRoot (selectedCharacterWeight P.blockSource P.block w) R)
          (Subgroup.normalizer
            ((selectedCharacterWeight P.blockSource P.block w).subgroup : Set P.H)).subtype →
      RootCompatibleAlong (P.localReduction w).iota
          (ownReductionRoot (selectedCharacterWeight P.blockSource P.block w) R)
          (normalizerProjection (selectedCharacterWeight P.blockSource P.block w).subgroup) →
      (flz.definition35BlockIsomorphic psi w ↔
        (rawStabilizer P.gamma (selectedCharacterWeight P.blockSource P.block w) ≤
          globalStabilizer P.iota P.gamma psi.1) ∧
        standard.blockIsomorphic (arguments P.iota P.gamma psi.1
          (selectedCharacterWeight P.blockSource P.block w) R))) :
    ChosenDefinition35Interpretation P adapter flz standard packets where
  relation_iff psi w := meaning psi w (packets w).reduction
    (packets w).ambientCompatible (packets w).quotientCompatible

section CorrectedContainment

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

/-- The actual whole-pair correction preserves full raw containment while
its inner action disappears only from the global class function. -/
theorem corrected_fullRawContainment_iff
    (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H) (g : H)
    (psi : IBr iota) (W : CharacterWeight p K G) (V : CharacterWeight p K H)
    (hpair : W.mapGroupEquiv (correctedEquiv e g) = V) :
    (rawStabilizer (MonoidHom.id (MulAut G)) W ≤
      globalStabilizer iota (MonoidHom.id (MulAut G)) psi) ↔
    (rawStabilizer (MonoidHom.id (MulAut H)) V ≤
      globalStabilizer (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
        (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi)) := by
  subst V
  have h := OddTwoGroupEquivRawTupleCoordinates.fullRawContainment_iff
    iota (correctedEquiv e g) psi W
  simp only [correctedBrauer_eq] at h
  simpa only [correctedRoot_eq] using h

end CorrectedContainment

section Family

variable {ell r a : ℕ} (family : Definition35Family.{0} ell)
variable (ha : 0 < a) [Fintype (FiniteSymplecticFixed r a)]
variable (e : family.H ≃* FiniteSymplecticFixed r a) (b : family.Block)
variable (source : FamilyInputs family ha e b)
variable (dictionary : PhysicalDictionary family ha e b source)

/-- The concrete problem has the computed quotient table BEFORE FLZ is
applied. All coefficients, specified catalogues and ambient roots are fixed. -/
abbrev concreteProblem := selfCoverProblem
  (FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary))

variable (packets : ∀ w : Definition35Weight (family.problem b),
  ChosenOwnReduction (family.problem b) w)

/-- Compute the concrete own packet through the selected WHOLE-pair map.
Both guards are the existing K preservation laws for the fixed family table. -/
def concretePackets (v : Definition35Weight (concreteProblem family ha e b source dictionary)) :
    ChosenOwnReduction (concreteProblem family ha e b source dictionary) v where
  reduction := chosenOwnReduction family ha e b source dictionary v
    (packets (familyWeight family ha e b source dictionary v)).reduction
  ambientCompatible := chosenOwnReduction_ambientCompatible family ha e b source dictionary v
    (packets (familyWeight family ha e b source dictionary v)).reduction
    (packets (familyWeight family ha e b source dictionary v)).ambientCompatible
  quotientCompatible := chosenOwnReduction_quotientCompatible family ha e b source dictionary v
    (packets (familyWeight family ha e b source dictionary v)).reduction
    (packets (familyWeight family ha e b source dictionary v)).quotientCompatible

variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem b))
variable (ambient : HighRankSelfCoverAmbientU0
  (FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary)))

abbrev concreteAdapter := selfCoverAutomorphisms
  (FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary)) ambient

variable (standard : BlockTripleSourceSemantics ell family.k family.K)
variable (transport : StandardTransportSource standard)

include adapter ambient transport in
/-- Three computed comparisons: family block presentation to full Aut,
the corrected actual group map, and full Aut back to the concrete block
presentation. The standard and the transported own reduction are unchanged. -/
theorem chosenCondition_iff
    (psi : Definition35Brauer (concreteProblem family ha e b source dictionary))
    (v : Definition35Weight (concreteProblem family ha e b source dictionary)) :
    chosenCondition (family.problem b) standard packets
        ((FamilyInputs.brauerFibreEquiv family ha e b source).symm psi)
        ((FamilyInputs.weightFibreEquiv family ha e b source dictionary).symm v) ↔
      chosenCondition (concreteProblem family ha e b source dictionary) standard
        (concretePackets family ha e b source dictionary packets) psi v := by
  let pf : Definition35Brauer (family.problem b) :=
    (FamilyInputs.brauerFibreEquiv family ha e b source).symm psi
  let wf : Definition35Weight (family.problem b) :=
    familyWeight family ha e b source dictionary v
  let WF : CharacterWeight ell family.K family.H :=
    familyPair family ha e b source dictionary v
  let V : CharacterWeight ell family.K (FiniteSymplecticFixed r a) :=
    concretePair family ha e b source v
  let R : OwnNormalizerReduction (k := family.k) WF := (packets wf).reduction
  let g := selectedConjugator family ha e b source dictionary v
  have hpair : WF.mapGroupEquiv (correctedEquiv e g) = V :=
    selectedEquiv_pair family ha e b source dictionary v
  have hpsi : IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota e pf.1 = psi.1 := by
    exact congrArg Subtype.val
      ((FamilyInputs.brauerFibreEquiv family ha e b source).apply_symm_apply psi)
  have hc1 := TypeCBlockStabilizerTupleTransport.selected_fullRawContainment_iff
    (family.problem b) adapter pf wf
  have hc2 := corrected_fullRawContainment_iff family.iota e g pf.1 WF V hpair
  have hc3 := TypeCBlockStabilizerTupleTransport.selected_fullRawContainment_iff
    (concreteProblem family ha e b source dictionary)
    (concreteAdapter family ha e b source dictionary ambient) psi v
  rw [hpsi] at hc2
  have ht1 := TypeCBlockStabilizerTupleTransport.blockIsomorphic_iff
    (family.problem b) adapter pf WF R standard transport
  have ht2 := corrected_blockIsomorphic_iff family.iota e g pf.1 WF V hpair R standard transport
  have ht3 := TypeCBlockStabilizerTupleTransport.blockIsomorphic_iff
    (concreteProblem family ha e b source dictionary)
    (concreteAdapter family ha e b source dictionary ambient) psi V
    (chosenOwnReduction family ha e b source dictionary v R) standard transport
  rw [hpsi] at ht2
  exact and_congr (hc1.trans (hc2.trans hc3.symm))
    (ht1.trans (ht2.trans ht3.symm))

variable (familyFlz : FLZSourceSemantics (family.problem b) adapter)
variable (concreteFlz : FLZSourceSemantics (concreteProblem family ha e b source dictionary)
  (concreteAdapter family ha e b source dictionary ambient))
variable (familyMeaning : ChosenDefinition35Interpretation (family.problem b)
  adapter familyFlz standard packets)
variable (concreteMeaning : ChosenDefinition35Interpretation
  (concreteProblem family ha e b source dictionary)
  (concreteAdapter family ha e b source dictionary ambient) concreteFlz standard
  (concretePackets family ha e b source dictionary packets))

include familyMeaning concreteMeaning transport in
/-- The forward relation is DERIVED from the two exact definition dictionaries
and the actual packet comparisons; it is not a new source field. -/
theorem relation_iff
    (psi : Definition35Brauer (concreteProblem family ha e b source dictionary))
    (v : Definition35Weight (concreteProblem family ha e b source dictionary)) :
    concreteFlz.definition35BlockIsomorphic psi v ↔
      familyFlz.definition35BlockIsomorphic
        ((FamilyInputs.brauerFibreEquiv family ha e b source).symm psi)
        ((FamilyInputs.weightFibreEquiv family ha e b source dictionary).symm v) :=
  (concreteMeaning.relation_iff psi v).trans
    ((chosenCondition_iff family ha e b source dictionary packets adapter ambient
      standard transport psi v).symm.trans (familyMeaning.relation_iff _ _).symm)

/-- Every field of this transport is computed. In particular it consumes
neither an arbitrary fibre equivalence nor a relation-forward certificate. -/
def forwardTransport : Definition35ForwardTransport
    (concreteProblem family ha e b source dictionary)
    (concreteAdapter family ha e b source dictionary ambient) concreteFlz
    (family.problem b) adapter familyFlz where
  gammaEquiv := (EvenFieldP38FamilyGammaEquivariance.gammaEquiv family ha e b
    (alignedInputs family ha e b source dictionary)
    (alignedDictionary family ha e b source dictionary) adapter ambient).symm
  brauerEquiv := (FamilyInputs.brauerFibreEquiv family ha e b source).symm
  weightEquiv := (FamilyInputs.weightFibreEquiv family ha e b source dictionary).symm
  brauer_naturality := by
    intro _ _ g psi
    let Eg := EvenFieldP38FamilyGammaEquivariance.gammaEquiv family ha e b
      (alignedInputs family ha e b source dictionary)
      (alignedDictionary family ha e b source dictionary) adapter ambient
    let Ep : Definition35Brauer (family.problem b) ≃
        Definition35Brauer (concreteProblem family ha e b source dictionary) :=
      FamilyInputs.brauerFibreEquiv family ha e b source
    apply Ep.injective
    have h := EvenFieldP38FamilyGammaEquivariance.brauerFibreEquiv_action family ha e b
      (alignedInputs family ha e b source dictionary)
      (alignedDictionary family ha e b source dictionary) adapter ambient
      (Eg.symm g) (Ep.symm psi)
    change Ep ((definition35BrauerAction (family.problem b)).smul (Eg.symm g) (Ep.symm psi)) =
      (definition35BrauerAction (concreteProblem family ha e b source dictionary)).smul
        (Eg (Eg.symm g)) (Ep (Ep.symm psi)) at h
    have hc := congrArg₂
      (fun (d : (concreteProblem family ha e b source dictionary).Gamma)
        (z : Definition35Brauer (concreteProblem family ha e b source dictionary)) =>
        (definition35BrauerAction (concreteProblem family ha e b source dictionary)).smul d z)
      (Eg.apply_symm_apply g) (Ep.apply_symm_apply psi)
    exact (Ep.apply_symm_apply _).trans (h.trans hc).symm
  weight_naturality := by
    intro _ _ g w
    let Eg := EvenFieldP38FamilyGammaEquivariance.gammaEquiv family ha e b
      (alignedInputs family ha e b source dictionary)
      (alignedDictionary family ha e b source dictionary) adapter ambient
    let Ew : Definition35Weight (family.problem b) ≃
        Definition35Weight (concreteProblem family ha e b source dictionary) :=
      FamilyInputs.weightFibreEquiv family ha e b source dictionary
    apply Ew.injective
    have h := EvenFieldP38FamilyGammaEquivariance.weightFibreEquiv_action family ha e b
      (alignedInputs family ha e b source dictionary)
      (alignedDictionary family ha e b source dictionary) adapter ambient
      (Eg.symm g) (Ew.symm w)
    change Ew ((definition35WeightAction (family.problem b)).smul (Eg.symm g) (Ew.symm w)) =
      (definition35WeightAction (concreteProblem family ha e b source dictionary)).smul
        (Eg (Eg.symm g)) (Ew (Ew.symm w)) at h
    have hc := congrArg₂
      (fun (d : (concreteProblem family ha e b source dictionary).Gamma)
        (z : Definition35Weight (concreteProblem family ha e b source dictionary)) =>
        (definition35WeightAction (concreteProblem family ha e b source dictionary)).smul d z)
      (Eg.apply_symm_apply g) (Ew.apply_symm_apply w)
    exact (Ew.apply_symm_apply _).trans (h.trans hc).symm
  relation_forward psi w :=
    (relation_iff family ha e b source dictionary packets adapter ambient standard transport
      familyFlz concreteFlz familyMeaning concreteMeaning psi w).mp

/-- Consume the existing theorem's returned witness, preserving its actual
map. The chosen tables precede that witness and are independent of its map. -/
def familyBijection
    (B : Definition35IBAWBijection (concreteProblem family ha e b source dictionary)
      (concreteAdapter family ha e b source dictionary ambient) concreteFlz) :
    Definition35IBAWBijection (family.problem b) adapter familyFlz :=
  (forwardTransport family ha e b source dictionary packets adapter ambient standard transport
    familyFlz concreteFlz familyMeaning concreteMeaning).map B

/-- The final equivalence is exactly Epsi, then the RETURNED B.omega, then
the inverse actual weight-fibre equivalence. -/
theorem familyBijection_omega
    (B : Definition35IBAWBijection (concreteProblem family ha e b source dictionary)
      (concreteAdapter family ha e b source dictionary ambient) concreteFlz) :
    (familyBijection family ha e b source dictionary packets adapter ambient standard transport
      familyFlz concreteFlz familyMeaning concreteMeaning B).omega =
      (FamilyInputs.brauerFibreEquiv family ha e b source).trans
        (B.omega.trans (FamilyInputs.weightFibreEquiv family ha e b source dictionary).symm) := rfl

include familyMeaning concreteMeaning transport in
theorem nonempty_familyBijection
    (hB : Nonempty (Definition35IBAWBijection
      (concreteProblem family ha e b source dictionary)
      (concreteAdapter family ha e b source dictionary ambient) concreteFlz)) :
    Nonempty (Definition35IBAWBijection (family.problem b) adapter familyFlz) := by
  obtain ⟨B⟩ := hB
  exact ⟨familyBijection family ha e b source dictionary packets adapter ambient standard transport
    familyFlz concreteFlz familyMeaning concreteMeaning B⟩

/-- The EXISTING Theorem 3.18 source, specialized to the aligned P38 data.
This abbreviation adds no theorem law or equation about its returned map. -/
abbrev alignedTheorem318Source :=
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  let p38 := FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary)
  FLZ318Source p38.iota p38.hinj p38.blocks (fieldAction r a ha)
    p38.blockSource p38.block p38.T p38.localReduction ambient.structural
    p38.endgame concreteFlz

/-- The existing protected explicit package belongs to the SAME aligned
endgame, source operations and operation adapters. -/
abbrev alignedExplicitHypotheses
    (theorem318 : alignedTheorem318Source family ha e b source dictionary ambient concreteFlz) :=
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  let p38 := FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary)
  CompletedExplicitPackage p38.iota p38.hinj p38.blocks (fieldAction r a ha)
    p38.blockSource p38.block p38.T p38.localReduction p38.endgame ambient.structural
    theorem318.operations theorem318.operationAdapters

include familyMeaning concreteMeaning transport in
/-- The actual source/application join: apply the existing E2 theorem to
its complete hypotheses, then transport its returned witness in K. -/
theorem familyBijection_of_theorem318
    (theorem318 : alignedTheorem318Source family ha e b source dictionary ambient concreteFlz)
    (hypotheses : alignedExplicitHypotheses family ha e b source dictionary ambient
      concreteFlz theorem318) :
    Nonempty (Definition35IBAWBijection (family.problem b) adapter familyFlz) := by
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  apply nonempty_familyBijection family ha e b source dictionary packets adapter ambient
    standard transport familyFlz concreteFlz familyMeaning concreteMeaning
  exact theorem318.applyTheorem318 hypotheses ambient.identification

end Family

end ModularRep.PaperProofs.EvenFieldP38ChosenDefinition35Transport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
