import ModularRep.PaperProofs.EvenFieldChosenStrictBlockPlaylist
import ModularRep.PaperProofs.EvenFieldFLZ57SemisimpleApplication
import ModularRep.PaperProofs.EvenFieldStrongRelativeCompleteBlock
import ModularRep.PaperProofs.TypeCKoshitaniSpathFamilySource

/-!
# Strong FLZ output to complete blocks and the normalized family

Fix the existing ambient family, canonical cover, standard modular system,
selected quotient tables and individual specified dictionaries before the
joint FLZ choice. The guarded strict-block hypotheses use the actual chosen
P38 caller. One joint strong output then supplies every relative packet,
its root metadata, its full block-stabilizer adapter and its BAW relation.

The complete blocks below retain that output verbatim. The only specified
supplier returns actual operations and their individual primitive/support
laws, never a matching, graph, block witness or final relation. The final
KS3.3 call consumes the constructed complete blocks and chooses a fresh
normalized family. No preservation of those old packets after KS is claimed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldStrongFLZCompleteApplication

open ModularRep CharacterWeight
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre
open EvenFieldFLZ57CentrelessGate EvenFieldFLZ57ChosenRootMetadata
open EvenFieldStrongRelativeQuotientWeight EvenFieldStrongRelativeQuotientAction
open EvenFieldAssumption53Actual EvenFieldConcreteTypeC EvenFieldFLZFullHG
open EvenFieldFLZ57Proposition39AssemblyU0 EvenFieldProposition39SemisimpleRouting
open TypeBFullBlockCondition TypeBFixedRootDefinitionFamily
open TypeCCoherentFiniteRootConvention OddTwoGroupEquivWeightBlocks

universe u

section PhysicalData

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}
variable (W : RelativeBlockConditionWitness family cover block)
variable (hcenter : Subgroup.center family.H = ⊥)

local instance quotientFintype : Fintype (QuotientCarrier W) := Fintype.ofFinite _

/-- Individual specified data on the actual quotient and computed action.
The support law is separate from the primitive equations. No target block,
graph, reverse map, extension or relation conclusion is a field. -/
structure QuotientPhysicalData where
  source :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    LocalBlockInductionSource (p := ell) (k := family.k) (K := family.K)
    (G := QuotientCarrier W) (Block := W.QuotientBlock)
  targetAmbient :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    ∀ c : W.QuotientBlock,
    source.operations.ambientBlockData.blockIdempotent c = W.quotientBlockIdempotent c
  ownPrimitive :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    ∀ V : CharacterWeight ell family.K family.H,
    MonoidAlgebra.domCongr family.k family.k
        (normalizerEquiv (EvenFieldStrongRelativeQuotientWeight.quotientEquiv W hcenter)
          V.subgroup)
        (ownNormalizerBlock family.blockSource.operations V).1 =
      (ownNormalizerBlock source.operations (V.mapGroupEquiv
        (EvenFieldStrongRelativeQuotientWeight.quotientEquiv W hcenter))).1
  physical :
    letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W hcenter
    OddTwoActualLocalBlockSupport.Source (fixedQuotientRoot W) source.operations

end PhysicalData

/-- Fix the specified interpretation before the joint output is selected.
Only packets whose selected roots belong to C are in the supplier's domain.
This is not an existence theorem for arbitrary abstract block operations. -/
structure PhysicalInputs {ell : ℕ} (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H)
    (hcenter : Subgroup.center family.H = ⊥)
    (C : Convention ell family.k family.K) where
  sourceAmbient : ∀ b : family.Block,
    family.blockSource.operations.ambientBlockData.blockIdempotent b = family.blockIdempotent b
  quotientData : ∀ (b : family.Block)
      (W : RelativeBlockConditionWitness family cover b)
      (metadata : RelativeRootMetadata C W),
    QuotientPhysicalData W hcenter

/-- Restrict the existing authentic specified support law to the actual
finite-root guard required by the KS source. -/
def ambientGuarded {ell : ℕ} (family : Definition35Family.{u} ell)
    (physical : OddTwoActualLocalBlockSupport.Source family.iota family.blockSource.operations) :
    GuardedBlockCompatibility family.iota family.blockSource.operations where
  normalizer_block_of_reduction V iotaN phiN roots reduction :=
    physical.normalizer_block_of_reduction V iotaN phiN
      (fun rho => Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
        rho.ρ family.iota iotaN (Subgroup.normalizer (V.subgroup : Set family.H)).subtype roots)
      reduction

/-- The pre-existing selected quotient tables agree on their entire
finite root domains by actual quotient/subgroup cardinal divisibility. -/
theorem selectedRoots {ell : ℕ} (family : Definition35Family.{u} ell)
    (C : Convention ell family.k family.K) (admissible : FamilyRootAdmissibility family C)
    (b : family.Block) (w : Definition35Weight (family.problem b)) :
    QuotientRootAgreement family.iota (SelectedRadical family.blockSource b w)
      (family.localReduction b w).iota := by
  let Q : Subgroup family.H := selectedRadical (family.problem b) w
  let N := Subgroup.normalizer (Q : Set family.H)
  change ∀ z : rootsOfUnity (primeRegularExponent ell (NormalizerQuotient Q)) family.k,
    (family.localReduction b w).iota.lift (((z : family.kˣ) : family.k)) =
      family.iota.lift (((z : family.kˣ) : family.k))
  intro z
  rw [admissible.selected_eq b w, admissible.ambient_eq]
  exact C.rootAt_lift_of_card_dvd
    ((Q.subgroupOf N).card_quotient_dvd_card.trans (Subgroup.card_subgroup_dvd_card N)) z

section SelectedOutput

variable {ell r a : ℕ}
variable (scope : FLZFullHGUniverse 2 ell) (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
variable (frobenius : AmbientFrobeniusFieldMatch scope model)
variable (blockSource : FullHGBlockSource coverage)
variable (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
variable (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
  blockSource identification)
variable (C : Convention ell (AmbientFamily scope coverage).k (AmbientFamily scope coverage).K)
variable (admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) C)
variable (selected :
  {output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
      identification semantics //
    ChosenRootMetadata scope coverage model frobenius blockSource identification semantics C output})
variable (physical : PhysicalInputs (AmbientFamily scope coverage)
  identification.identityEllPrimeCover identification.centerless C)

/-- A K intermediate consumer of a selected old output. The final caller
below constructs that output from the joint source instead of assuming it. -/
def completeBlockAt (b : (AmbientFamily scope coverage).Block) :
    BlockWitness (AmbientFamily scope coverage) identification.identityEllPrimeCover b := by
  let W := (selected.1.certificate.blockCertificate b).relative
  letI := EvenFieldStrongRelativeQuotientAction.quotientBlockAction W identification.centerless
  let metadata := selected.2.block b
  let data := physical.quotientData b W metadata
  exact EvenFieldStrongRelativeCompleteBlock.completeBlock
    W identification.centerless C admissible metadata data.source
    physical.sourceAmbient data.targetAmbient data.ownPrimitive data.physical

@[simp] theorem completeBlockAt_relative (b : (AmbientFamily scope coverage).Block) :
    (completeBlockAt scope coverage model frobenius blockSource identification semantics
      C admissible selected physical b).relative =
      (selected.1.certificate.blockCertificate b).relative := rfl

@[simp] theorem completeBlockAt_omega (b : (AmbientFamily scope coverage).Block) :
    (completeBlockAt scope coverage model frobenius blockSource identification semantics
      C admissible selected physical b).relative.omega =
      (selected.1.certificate.blockCertificate b).omega := rfl

/-- The full block-stabilizer adapter is the one already fixed by the
original block source and retained by the strong certificate. -/
theorem completeBlockAt_automorphisms (b : (AmbientFamily scope coverage).Block) :
    (completeBlockAt scope coverage model frobenius blockSource identification semantics
      C admissible selected physical b).relative.automorphismStabilizer =
      blockSource.automorphisms scope.ambientPair b :=
  (selected.1.certificate.blockCertificate b).automorphismStabilizer_eq

/-- The same fixed BAW relation holds at the same retained map. This uses
the old output's relation source, not a new implication from Definition3.5. -/
theorem completeBlockAt_baw (b : (AmbientFamily scope coverage).Block)
    (psi : Definition35Brauer ((AmbientFamily scope coverage).problem b)) :
    (semantics.relation b).bawGoodBlockIsomorphic psi
      ((completeBlockAt scope coverage model frobenius blockSource identification semantics
        C admissible selected physical b).relative.omega psi) :=
  selected.1.relationSource.relation_of_certificate b psi

/-- Independently computed COMPLETE blocks on the same family and cover. -/
def allBlocks : ∀ b : (AmbientFamily scope coverage).Block,
    Nonempty (BlockWitness (AmbientFamily scope coverage) identification.identityEllPrimeCover b) :=
  fun b => ⟨completeBlockAt scope coverage model frobenius blockSource identification semantics
    C admissible selected physical b⟩

/-- Apply the separate published normalization theorem only after all
complete blocks have been constructed. Its output packets are fresh choices. -/
def normalizedFamilyOfSelectedOutput
    (splitting : IsAlgClosed (AmbientFamily scope coverage).K)
    (coefficient : SpathCoefficientField ell (AmbientFamily scope coverage).k
      (AmbientFamily scope coverage).ellPrime)
    (ambientPhysical : OddTwoActualLocalBlockSupport.Source (AmbientFamily scope coverage).iota
      (AmbientFamily scope coverage).blockSource.operations)
    (ks : TypeCKoshitaniSpathFamilySource.Source.{0}) :
    FamilyWitness (AmbientFamily scope coverage) identification.identityEllPrimeCover :=
  TypeCKoshitaniSpathFamilySource.familyWitness
    (AmbientFamily scope coverage) identification.identityEllPrimeCover splitting coefficient
    physical.sourceAmbient (ambientGuarded (AmbientFamily scope coverage) ambientPhysical)
    (selectedRoots (AmbientFamily scope coverage) C admissible) ks
    (allBlocks scope coverage model frobenius blockSource identification semantics
      C admissible selected physical)

end SelectedOutput

section Application

variable {ell r a : ℕ} {CSp Fq : Type}
variable [Group CSp] [Finite CSp] [Field Fq] [Finite Fq] [CharP Fq 2]
variable (ha : 0 < a) [Finite (FiniteSymplecticFixed r a)]
variable [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
variable (scope : FLZFullHGUniverse 2 ell) (coverage : FullHGDefinition35Coverage scope)
variable (model : CentrelessTypeCAmbientModel (r := r) (a := a) scope)
variable (frobenius : AmbientFrobeniusFieldMatch scope model)
variable (conformal : ConformalStructuralSource r a ha CSp Fq)
variable (blockSource : FullHGBlockSource coverage)
variable (strictSource : FullHGStrictQuasiIsolationAdapter coverage)
variable (classification : FullHGTypeCClassificationSource scope)
variable (rankAtLeastFour : 4 ≤ r)
variable (identification : CentrelessTypeCSourceIdentification scope coverage model frobenius)
variable (coherent : ∀ pair : FullHG scope, CoherentPairStrictSourceU0 strictSource pair)
variable (labels : ∀ pair : FullHG scope, SemisimpleLabelSource (coherent pair).strictData)
variable (playlist : ∀ pair : FullHG scope,
  EvenFieldChosenStrictBlockPlaylist.SourceInputs blockSource strictSource classification pair
    (coherent pair).strictData (labels pair))
variable (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0}
  ell (AmbientFamily scope coverage).k)
variable (semantics : AmbientFLZBAWGoodSemantics scope coverage model frobenius
  blockSource identification)
variable (C : Convention ell (AmbientFamily scope coverage).k (AmbientFamily scope coverage).K)
variable (admissible : FamilyRootAdmissibility (AmbientFamily scope coverage) C)
variable (physical : PhysicalInputs (AmbientFamily scope coverage)
  identification.identityEllPrimeCover identification.centerless C)
variable (joint : JointFLZ57MatchedPairSource ha scope coverage model frobenius conformal
  blockSource strictSource identification semantics C admissible)

/-- Choose once after constructing both authentic FLZ hypotheses. This
preserves the old field-size exclusion and fixes every output index. -/
def chosenOutput :
    {output : FLZ57MatchedPairOutput scope coverage model frobenius blockSource
        identification semantics //
      ChosenRootMetadata scope coverage model frobenius blockSource identification semantics C output} :=
  joint.choose (EvenFieldFLZ57SemisimpleApplication.explicitHypotheses
    ha scope coverage model frobenius conformal blockSource strictSource classification
    rankAtLeastFour identification coherent labels (fun pair => (playlist pair).toGuarded) principle)

/-- Forward strong-FLZ application followed by the computed quotient
completion. No complete-block or relation-forward input is accepted. -/
def completeBlocks : ∀ b : (AmbientFamily scope coverage).Block,
    Nonempty (BlockWitness (AmbientFamily scope coverage) identification.identityEllPrimeCover b) :=
  allBlocks scope coverage model frobenius blockSource identification semantics C admissible
    (chosenOutput ha scope coverage model frobenius conformal blockSource strictSource
      classification rankAtLeastFour identification coherent labels playlist principle
      semantics C admissible joint) physical

/-- Retain the stronger BAW-good output at the SAME selected certificate,
separately from the normalized family's permitted fresh choices. -/
def bawGoodFamily :
    AmbientFLZBAWGoodFamilyWitness scope coverage model frobenius blockSource identification semantics :=
  (chosenOutput ha scope coverage model frobenius conformal blockSource strictSource
    classification rankAtLeastFour identification coherent labels playlist principle
    semantics C admissible joint).1.toBAWGoodFamilyWitness

/-- The complete fixed-family target: actual guarded P38 callers feed
FLZ5.7, computed complete blocks feed KS3.3. Both source interpretations and
the specified/modular-system dictionaries remain their named external inputs. -/
def familyWitness
    (splitting : IsAlgClosed (AmbientFamily scope coverage).K)
    (coefficient : SpathCoefficientField ell (AmbientFamily scope coverage).k
      (AmbientFamily scope coverage).ellPrime)
    (ambientPhysical : OddTwoActualLocalBlockSupport.Source (AmbientFamily scope coverage).iota
      (AmbientFamily scope coverage).blockSource.operations)
    (ks : TypeCKoshitaniSpathFamilySource.Source.{0}) :
    FamilyWitness (AmbientFamily scope coverage) identification.identityEllPrimeCover :=
  normalizedFamilyOfSelectedOutput scope coverage model frobenius blockSource identification semantics
    C admissible
    (chosenOutput ha scope coverage model frobenius conformal blockSource strictSource
      classification rankAtLeastFour identification coherent labels playlist principle
      semantics C admissible joint)
    physical splitting coefficient ambientPhysical ks

end Application

end ModularRep.PaperProofs.EvenFieldStrongFLZCompleteApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
