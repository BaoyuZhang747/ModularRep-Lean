import ModularRep.PaperProofs.TypeBProposition44SourceInstantiation
import ModularRep.PaperProofs.TypeBSpinAmbientStabilizer
import ModularRep.PaperProofs.TypeBCriterionCarrierBindings
import ModularRep.PaperProofs.TypeBGlobalExtensionBinding
import ModularRep.PaperProofs.TypeBClassInertiaFactorization
import ModularRep.PaperProofs.TypeBSourceStabilizerBindings
import ModularRep.PaperProofs.TypeBSpinCoverSource
import ModularRep.PaperProofs.TypeBBroughSpathCriterionSource

/-!
# Full Type B criterion construction on the literal source carriers

The special Clifford correspondence and the Spin constituent are deductions
from the previously checked moving windows. This module binds their SAME
primitive blocks, roots, field action, and norm kernel to the universal
Brough--Spaeth criterion. The four extension clauses are constructed from
the universal cyclic extension principles. The literal FLZ 7.5 raw product
implies the original criterion's class product by the checked quotient
argument.

All external premises below are the primitive hypotheses of those existing
source endpoints, the named universal criterion, and the narrow structural,
cover, coefficient, and fixed-root local block sources. No full criterion
hypothesis packet, downstairs correspondence, factorizing Brauer constituent,
or family witness is an input. The generic cover excludes (n,q)=(3,3).
Published-source realization grades remain those recorded in the Type B
contracts; applying a certificate does not authenticate it.
-/

noncomputable section

open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBProposition44CriterionAssembly

open ModularRep TypeBCliffordCarriers
open TypeBCriterionHypotheses TypeBCriterionCarrierBindings
open TypeBSpinRestrictionConstituent
open TypeBSourceStabilizerBindings

section LiteralStabilizerBridges

variable {n p f ell : ℕ} {F k K : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
variable (N : NormSource n F) [Finite (SpecialClifford n F)]
variable {parameters : OddFieldParameters F p f}
variable (fs : FieldActionSource n F p f parameters N)


/-- Because the published source holds for every raw weight, identity is
an allowed normalizer conjugator. The class product is proved for that very
same twisted representative. -/
theorem rawClause_of_theorem75
    (source : TypeBWeightStabilizerSource.Theorem75Source (K := K) (ell := ell) fs) :
    RawNormalizerClause (ell := ell) (K := K)
      (SpinSubgroup n F N) fs.action (naturalAction N fs) := by
  intro W
  refine ⟨1, (Subgroup.normalizer _).one_mem, ?_, ?_⟩
  · exact rawFactorization_of_theorem75 N fs source _
  · exact TypeBClassInertiaFactorization.weightClassFactorization_of_rawNormalizerFactorization
      (SpinSubgroup n F N) fs.action (naturalAction N fs) _
      (rawFactorization_of_theorem75 N fs source _)

/-- The source's embedded inertia images are the criterion's intersections
with the two fixed ambient factors. -/
theorem brauerFactorization_of_ambient_product
    (iotaG : PrimeRegularRootEmbedding ell k K (Spin n F N)) (phi : IBr iotaG)
    (h : (TypeBSpinAmbientStabilizer.ambientBrauerInertia fs iotaG phi :
        Set (Ambient fs.action)) =
      (TypeBSpinAmbientStabilizer.specialCliffordInertiaImage fs iotaG phi :
        Set (Ambient fs.action)) *
      (TypeBSpinAmbientStabilizer.fieldInertiaImage fs iotaG phi :
        Set (Ambient fs.action))) :
    BrauerFactorization (SpinSubgroup n F N) fs.action (naturalAction N fs) iotaG phi := by
  simpa only [BrauerFactorization, factorInertia, embeddedM, embeddedE,
    brauerInertia, naturalAction,
    TypeBSpinAmbientStabilizer.ambientBrauerInertia,
    TypeBSpinAmbientStabilizer.specialCliffordInertiaImage,
    TypeBSpinAmbientStabilizer.fieldInertiaImage, Subgroup.map_comap_eq, inf_comm] using h

end LiteralStabilizerBridges

section SourceInstantiation

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero IntegralBasicSetBridge OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBIntegralSeriesCertificate TypeBFLZLabelSource
open TypeBConlonBlockSourceInstantiation TypeBConlonBlockFLZ ConlonBasicSet
open OddConlonOrbitAssembly TypeCWeightTensorFieldAction

variable {p ell f n : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)

local instance : Fintype (SpecialClifford n F) := Fintype.ofFinite _

variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
variable [Finite (TensorCharacters (k := k) (SpinSubgroup n F N))]
variable [Finite (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
  (field_spinSubgroup_map n F fs))]
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable [MulAction (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
  (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable (Msys : ModularSystem ell K O k)
variable (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (unipotent : UnipotentPredicate F K p n)
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : Equation34Source (ell := ell) unipotent)
variable (Core : AdmissibleParameter F p ell n → Type)
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (ordinaryBlock : Irr K (SpecialClifford n F) →
  LiteralPrimitiveBlock k (SpecialClifford n F))
variable (T : Theorem63Source unipotent S Core ordinaryBlock)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.1))
variable (source23 : Theorem23Certificate Msys iota hcompat hinj
  S.rationalSeriesSource blocks T.blockSeries p 1)
variable (seriesTensorStable : TypeCConformalActionAdapter.OrdinarySeriesTensorStable
  (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
    S.rationalSeriesSource.selectedSeries)
variable (seriesFieldStable : TypeCConformalActionAdapter.OrdinarySeriesFieldStable
  (K := K) fs.action S.rationalSeriesSource.selectedSeries)
variable (liftPrimeTo : ∀ c : TensorCharacters (k := k) (SpinSubgroup n F N),
  ell.Coprime (orderOf (TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
    (G0 := SpinSubgroup n F N) (field := fs.action)
    (hinvariant := field_spinSubgroup_map n F fs) D c)))
variable (blockSource : CharacterWeight.LocalBlockInductionSource
  (p := ell) (k := k) (K := K) (G := SpecialClifford n F)
  (Block := LiteralPrimitiveBlock k (SpecialClifford n F)))


variable (productFormula : BrauerLinearTensorProductFormula iota)

variable [Finite S.rationalSeriesSource.Basic]

variable (hOrdBlock : TypeCConformalActionAdapter.OrdinaryBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D ordinaryBlock)

variable (hBrBlock : TypeCConformalActionAdapter.BrauerBlockEquivariant
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) iota productFormula
        (irreducibleBrauerCharacterBlock iota hinj blocks))

variable (forwardSupport :
      let data := integralData Msys iota hcompat hinj unipotent S Core ordinaryBlock T
        blocks source23
      ∀ x : S.rationalSeriesSource.Basic,
        aggregateLinearEquiv S.rationalSeriesSource.ordinaryIndex
          (brauerIndex iota hinj blocks T.blockSeries)
          (data.fibreMaps Msys iota hcompat hinj S.rationalSeriesSource blocks T.blockSeries)
          (MonoidAlgebra.single x 1) ∈ MonoidAlgebra.supported ℤ ℤ
            (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks)
              (ordinaryBlock x.1)))

variable (liftCompatible : OrdinaryLiftReductionCompatible (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D iota)

variable (eq35 : Fˣ ≃* linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))

variable (liftTrivial : ∀ c : TensorCharacters (k := k) (SpinSubgroup n F N),
      TypeCConformalActionAdapter.OrdinaryReductionEquiv.lift
        (G0 := SpinSubgroup n F N) (field := fs.action)
        (hinvariant := field_spinSubgroup_map n F fs) D c ∈
          linearCharactersTrivialOn (k := K) (SpinSubgroup n F N))

variable (tensorLabel : TensorCharacters (k := k) (SpinSubgroup n F N) →
      CharacterPair F K p ell n unipotent → CharacterPair F K p ell n unipotent)

variable (tensor_character :
      let hseries := TypeCConformalActionAdapter.ordinarySeriesStable_of_tensor_and_field
        (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D
        S.rationalSeriesSource.selectedSeries seriesTensorStable seriesFieldStable
      ∀ c l, S.familyCharacter (tensorLabel c l) =
        @SMul.smul (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) S.rationalSeriesSource.Basic
          (ordinarySeriesCarrierAction (SpinSubgroup n F N) fs.action
            (field_spinSubgroup_map n F fs) D S.rationalSeriesSource.selectedSeries
            hseries).toSMul (SemidirectProduct.inl c) (S.familyCharacter l))

variable (tensor_parameter : ∀ c l,
      (tensorLabel c l).1.1 = scalar F n
        (equation35Scalar (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs) D eq35 liftTrivial c)⁻¹ * l.1.1)

variable (brauer_nonempty : ∀ b : LiteralPrimitiveBlock k (SpecialClifford n F),
      Nonempty (BlockFibre (irreducibleBrauerCharacterBlock iota hinj blocks) b))

variable (conlon : ∀ orbit : BlockOrbit
        (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (orbitRepresentative orbit)))

variable (burnside : ∀ orbit : BlockOrbit
        (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (LiteralPrimitiveBlock k (SpecialClifford n F)),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (ActingGroup (k := k) (SpinSubgroup n F N) fs.action
          (field_spinSubgroup_map n F fs)) (orbitRepresentative orbit)))

variable (blockBinding : TypeBProposition44SourceInstantiation.LiteralBlockSourceBinding blockSource)

variable (source72 : TypeBProposition44SourceInstantiation.Theorem72Source parameters N fs D unipotent S ordinaryBlock
      seriesTensorStable seriesFieldStable liftPrimeTo blockSource)

open TypeBSpinStabilizer TypeBSpinConlonBlockSourceInstantiation TypeBSpinStabilizerTransfer

variable (rank_at_least_three : 3 ≤ n)

variable (hEll : Nat.Prime ell)

variable (hOdd : Odd ell)

variable (hNondef : ell ≠ p)

variable (restriction : RestrictionExpansionSource N iota)

variable (spinCompat : StableReductionBrauerCharacterCompatibility Msys (spinRoot N iota))

variable (hinjSpin : IrreducibleBrauerCharacterInjectivity (spinRoot N iota))

variable (spinSource : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))

variable [Finite spinSource.family.Basic]

variable [MulAction (OuterGroup f) spinSource.family.Basic]

variable [MulAction (OuterGroup f) (IBr (spinRoot N iota))]

variable [MulAction (OuterGroup f) (SpinBlock (k := k) (N := N))]

variable [Fintype (SpinBlock (k := k) (N := N))]

variable (spinBlocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))

variable (spinCertificate : Theorem23Certificate Msys (spinRoot N iota) spinCompat hinjSpin spinSource.family
      spinBlocks spinSource.blockSeries p 2)

variable (spinOrdinaryBlock : spinSource.family.Basic → SpinBlock (k := k) (N := N))

variable (spinForwardGenerator : ∀ x : spinSource.family.Basic,
      (spinBasicSetFromTheorem23 Msys (spinRoot N iota) spinCompat hinjSpin spinSource spinBlocks
        spinCertificate hEll hOdd hNondef).linearEquiv (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet (irreducibleBrauerCharacterBlock (spinRoot N iota) hinjSpin spinBlocks)
            (spinOrdinaryBlock x)))

variable (spinOrdinaryBlockEquivariant : ∀ (a : OuterGroup f)
        (x : spinSource.family.Basic), spinOrdinaryBlock (a • x) = a • spinOrdinaryBlock x)

variable (spinBrauerBlockEquivariant : ∀ (a : OuterGroup f) (phi : IBr (spinRoot N iota)),
      irreducibleBrauerCharacterBlock (spinRoot N iota) hinjSpin spinBlocks (a • phi) =
        a • irreducibleBrauerCharacterBlock (spinRoot N iota) hinjSpin spinBlocks phi)

variable (spinActions : EffectiveActionSource fs (spinRoot N iota) hinjSpin
      spinSource.family.selectedSeries
      (spinBasicSetFromTheorem23 Msys (spinRoot N iota) spinCompat hinjSpin spinSource spinBlocks
        spinCertificate hEll hOdd hNondef))

variable (spinOrdinarySeparation : Theorem310Source (N := N) (f := f)
      spinSource.family.selectedSeries spinActions.diagonal)

variable (spinConlon : ∀ b : SpinBlock (k := k) (N := N),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (OuterGroup f) b))

variable (spinBurnside : ∀ b : SpinBlock (k := k) (N := N),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (OuterGroup f) b))

local instance : Fintype (Spin n F N) := Fintype.ofFinite _

variable (spinLocal : TypeBFixedRootDefinitionFamily.PrimitiveLocalSource (spinRoot N iota))

/-- The same two complete primitive block decompositions and specified
weight-block catalogues used by the source-instantiated moving windows. -/
def literalBlocks : BlockData (ell := ell) (k := k) (K := K) (SpinSubgroup n F N) where
  downstairs := spinBlocks
  upstairs := blocks
  weightDownstairs := spinLocal.blockSource
  weightUpstairs := blockSource
  downstairs_idempotent := spinLocal.idempotent
  upstairs_idempotent := blockBinding.ambient_idempotent

/-- The criterion receives precisely the guarded local reductions from the
fixed Spin root. This adapter introduces no additional choice. -/
def literalLocalReduction :
    LocalReductionData (SpinSubgroup n F N) (spinRoot N iota)
      (literalBlocks (N := N) (blocks := blocks) (blockSource := blockSource)
        (blockBinding := blockBinding) (spinBlocks := spinBlocks) (spinLocal := spinLocal)) where
  blockCompatibility := spinLocal.blockCompatibility
  reduction := spinLocal.reduction
  rootAgreement := spinLocal.reduction_roots

variable (coefficient : SpathCoefficientField ell k hEll)
variable (coverSource : TypeBSpinCoverSource.GenericSpinCoverSource
  (p := p) (f := f) (ell := ell) N)
variable (dividesSimpleOrder : ell ∣ Nat.card (TypeBSpinCoverSource.Omega N))
variable (automorphismSource : TypeBAutomorphismSource.StructuralSource fs)
variable (hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell)
variable (rawSource : TypeBWeightStabilizerSource.Theorem75Source (K := K) (ell := ell) fs)
variable (brauerPrinciple : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
variable (ordinaryPrinciple : Representation.CyclicExtensionPrinciple.{0, 0, 0} K)
variable (criterion : TypeBBroughSpathCriterionSource.Theorem45Certificate)

include parameters N fs D Msys iota hcompat hinj
  unipotent S Core ordinaryBlock T blocks source23 seriesTensorStable
  seriesFieldStable liftPrimeTo blockSource productFormula hOrdBlock hBrBlock forwardSupport liftCompatible
  eq35 liftTrivial tensorLabel tensor_character tensor_parameter brauer_nonempty conlon burnside
  blockBinding source72 rank_at_least_three hEll hOdd hNondef restriction spinCompat
  hinjSpin spinSource spinBlocks spinCertificate spinOrdinaryBlock spinForwardGenerator spinOrdinaryBlockEquivariant spinBrauerBlockEquivariant
  spinActions spinOrdinarySeparation spinConlon spinBurnside spinLocal coefficient coverSource dividesSimpleOrder
  automorphismSource hall rawSource brauerPrinciple ordinaryPrinciple criterion

set_option maxHeartbeats 2400000 in
/-- Full literal output, conditional on the independently quantified
published criterion and the exact source-sized inputs of the checked
Type B windows. The family and cover are computed here. No condition on
a downstairs matching is assumed.

The generic Spin cover source fixes the precise generic scope; the
exceptional full cover of Omega_7(3) is not silently identified with Spin.
-/ 
theorem full_block_condition_source_instantiated :
    Nonempty (TypeBFullBlockCondition.FamilyWitness
      (TypeBFixedRootDefinitionFamily.primitiveFamily
        (spinRoot N iota) hinjSpin spinBlocks hEll spinLocal)
      (TypeBSpinCoverSource.genericSpinEllPrimeCover N hEll hOdd coverSource)) := by
  classical
  let blockData := literalBlocks (N := N) (blocks := blocks) (blockSource := blockSource)
    (blockBinding := blockBinding) (spinBlocks := spinBlocks) (spinLocal := spinLocal)
  let localData := literalLocalReduction (N := N) (blocks := blocks)
    (blockSource := blockSource) (blockBinding := blockBinding)
    (spinBlocks := spinBlocks) (spinLocal := spinLocal)
  let radicalKernel := TypeBRadicalLiftKernel.specialCliffordRadicalKernel
    parameters N fs D liftPrimeTo
  letI : MulAction
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
      (IBr iota) :=
    brauerCharacterAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) iota productFormula
  letI : MulAction
      (ActingGroup (k := k) (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
      (CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := SpecialClifford n F)) :=
    TypeBOddPrimesProposition44Actual.weightAction (SpinSubgroup n F N) fs.action
      (field_spinSubgroup_map n F fs) D radicalKernel
  obtain ⟨omega, hOmega, hBlock, _⟩ :=
    TypeBProposition44SourceInstantiation.proposition_4_4_source_instantiated
      (parameters := parameters) (N := N) (fs := fs) (D := D)
      (Msys := Msys) (iota := iota) (hcompat := hcompat) (hinj := hinj)
      (unipotent := unipotent) (S := S) (Core := Core) (ordinaryBlock := ordinaryBlock)
      (T := T) (blocks := blocks) (source23 := source23)
      (seriesTensorStable := seriesTensorStable) (seriesFieldStable := seriesFieldStable)
      (liftPrimeTo := liftPrimeTo) (blockSource := blockSource)
      (productFormula := productFormula) (hOrdBlock := hOrdBlock) (hBrBlock := hBrBlock)
      (forwardSupport := forwardSupport) (liftCompatible := liftCompatible)
      (eq35 := eq35) (liftTrivial := liftTrivial) (tensorLabel := tensorLabel)
      (tensor_character := tensor_character) (tensor_parameter := tensor_parameter)
      (brauer_nonempty := brauer_nonempty) (conlon := conlon) (burnside := burnside)
      (blockBinding := blockBinding) (source72 := source72)
  have constituent :
      ConstituentClause (SpinSubgroup n F N) fs.action (naturalAction N fs)
        iota (spinRoot N iota) := by
    intro Phi
    obtain ⟨phi, hRestriction, hFactor⟩ :=
      TypeBSpinAmbientStabilizer.exists_spin_constituent_with_ambient_factorization
        (fieldSource := fs) (rank_at_least_three := rank_at_least_three)
        (hEll := hEll) (hOdd := hOdd) (hNondef := hNondef)
        (Msys := Msys) (iotaA := iota) (restriction := restriction)
        (hcompat := spinCompat) (hinjSpin := hinjSpin) (source := spinSource)
        (blocks := spinBlocks) (certificate := spinCertificate)
        (ordinaryBlock := spinOrdinaryBlock) (forwardGenerator := spinForwardGenerator)
        (ordinaryBlockEquivariant := spinOrdinaryBlockEquivariant)
        (brauerBlockEquivariant := spinBrauerBlockEquivariant)
        (actions := spinActions) (ordinarySeparation := spinOrdinarySeparation)
        (conlon := spinConlon) (burnside := spinBurnside) (Phi := Phi)
    exact ⟨phi, hRestriction,
      brauerFactorization_of_ambient_product N fs (spinRoot N iota) phi hFactor⟩
  let hypotheses : AllBlocksHypotheses
      (SpinSubgroup n F N) fs.action (naturalAction N fs) iota (spinRoot N iota)
      blockData hinj (field_spinSubgroup_map n F fs) D productFormula radicalKernel :=
    { prime := hEll
      coefficient := coefficient
      cover := TypeBSpinCoverSource.genericSpinEllPrimeCover N hEll hOdd coverSource
      divides_simple_order := dividesSimpleOrder
      structural := TypeBCriterionCarrierBindings.structural N fs automorphismSource
      rootAgreement := spinRoot_agrees N iota
      brauer_injective_downstairs := hinjSpin
      localReduction := localData
      liftCompatible := liftCompatible
      lift_primeTo := liftPrimeTo
      lift_trivial := liftTrivial
      extensions := TypeBGlobalExtensionBinding.extensionClauses
        (SpinSubgroup n F N) fs.action (naturalAction N fs) (spinRoot N iota)
        brauerPrinciple ordinaryPrinciple automorphismSource.quotient_cyclic
      correspondence := { omega := omega, equivariant := hOmega, block := hBlock }
      hall := hallData N hall
      JG := allPairsJG N fs (spinRoot N iota) hOdd spinActions.diagonal
        spinActions.diagonal_surjective spinActions.diagonal_kernel hall
      constituent := constituent
      rawNormalizer := rawClause_of_theorem75 N fs rawSource }
  exact criterion.allBlocks
    (SpinSubgroup n F N) fs.action (naturalAction N fs) iota (spinRoot N iota)
    blockData hinj (field_spinSubgroup_map n F fs) D productFormula radicalKernel hypotheses

end SourceInstantiation

end ModularRep.PaperProofs.TypeBProposition44CriterionAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
