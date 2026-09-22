import ModularRep.PaperProofs.TypeCOddPrimeExtensionClauses
import ModularRep.PaperProofs.TypeCOddPrimeSymplecticCover
import ModularRep.PaperProofs.TypeCOddPrimeInertiaHall
import ModularRep.PaperProofs.TypeCOddPrimeConstituentFactorization
import ModularRep.PaperProofs.TypeCOddPrimeWeightStabilizerTransport
import ModularRep.PaperProofs.TypeCProposition313CriterionCorrespondence
import ModularRep.PaperProofs.TypeBBroughSpathCriterionSource

/-!
# Actual odd-field, odd-prime Type C criterion application

All groups and actions below are the previously constructed matrix Sp range,
CSp, entrywise field action, and natural semidirect action. The input record
contains the exact source premises of the protected constituent, correspondence,
extension, Hall and raw-normalizer arguments. Their conclusions are computed;
none of the criterion's five resulting clauses is a new field.

The final endpoint applies the published universal certificate to its fixed
complete block-family output. Authentication of its literal source-to-output
interpretation, and transport to the independently selected Type C target,
remain separate obligations. This is not an unconditional Type C proposition.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddPrimeCriterionApplication

open ModularRep FDRepSimpleClassKZero
open TypeBCriterionHypotheses TypeCConformalActionAdapter
open TypeCWeightTensorFieldAction
open TypeCOddPrimeConformalCriterionCarriers
open OddTwoConformalProjectiveRealisation (CSp PSp)
open EvenFieldFLZSourceConditions

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]
variable {ell : ℕ} {k K O Index CyclicTarget : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharP k ell] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]


local instance ambientFintype : Fintype (CSp n F) := Fintype.ofFinite _
local instance baseFintype : Fintype (SpSubgroup n F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (CSp n F))]
variable [Fintype (LiteralPrimitiveBlock k (SpSubgroup n F))]
variable [Finite (TensorCharacters (k := k) (SpSubgroup n F))]
variable [MulAction (ActingGroup (k := k) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
  (LiteralPrimitiveBlock k (CSp n F))]
variable [MulAction (Ambient (fieldAction n F)) (LiteralPrimitiveBlock k (SpSubgroup n F))]
variable (iotaM : PrimeRegularRootEmbedding ell k K (CSp n F))
variable (iotaG : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
variable (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
variable (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
variable (blocks : BlockData (ell := ell) (k := k) (K := K) (SpSubgroup n F))
variable (D : OrdinaryReductionEquiv (k := k) (K := K) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
variable (productFormula : BrauerLinearTensorProductFormula iotaM)
variable (radicalKernel : RadicalKernelLiftInput (p := ell) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D)

/-- Source premises on fixed carriers. `standardRadicals` must receive Li's
actual product-basic family in its source interpretation; coverage is only
subgroup conjugacy and the standard formula concerns each weight's own pair.
The fixed nondefining odd-prime scope is retained even where a generic K
argument does not need all of it. -/
structure ApplicationInputs where
  prime : Nat.Prime ell
  odd : Odd ell
  nondefining : ¬ ell ∣ Nat.card F
  coefficient : SpathCoefficientField ell k prime
  structuralSource : StructuralSource n F
  coverSource : TypeCOddPrimeSymplecticCover.CoverSource n F ell
  dividesSimpleOrder : ell ∣ Nat.card (PSp n F)
  localReduction : LocalReductionData (SpSubgroup n F) iotaG blocks
  correspondenceSource : TypeCProposition313CriterionCorrespondence.SourceInputs
    (O := O) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D iotaM hinjM blocks productFormula radicalKernel
  basicSet : TypeCOddPrimeConstituentFactorization.BasicSetSource
    (O := O) (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG blocks.downstairs
  blockInputs : ∀ b : LiteralPrimitiveBlock k (SpSubgroup n F),
    TypeCOddPrimeConstituentFactorization.BlockSourceInputs
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaG hinjG blocks.downstairs basicSet
      (CyclicTarget := CyclicTarget) b
  restriction : TypeCOddPrimeConstituentFactorization.RestrictionExpansionSource
    (SpSubgroup n F) iotaM iotaG
  liftPrimeTo : ∀ lambda : TensorCharacters (k := k) (SpSubgroup n F),
    ell.Coprime (orderOf (OrdinaryReductionEquiv.lift
      (G0 := SpSubgroup n F) (field := fieldAction n F)
      (hinvariant := field_spSubgroup_map n F) D lambda))
  liftTrivial : ∀ lambda : TensorCharacters (k := k) (SpSubgroup n F),
    OrdinaryReductionEquiv.lift
      (G0 := SpSubgroup n F) (field := fieldAction n F)
      (hinvariant := field_spSubgroup_map n F) D lambda ∈
        linearCharactersTrivialOn (k := K) (SpSubgroup n F)
  brauerExtension : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k
  ordinaryExtension : Representation.CyclicExtensionPrinciple.{0, 0, 0} K
  hall : HallData (SpSubgroup n F) ell
  index_dvd_two : ((SpSubgroup n F) ⊔ Subgroup.center (CSp n F)).index ∣ 2
  standardRadicals : Index → Subgroup (SpSubgroup n F)
  radicalCoverage : ∀ Q : Subgroup (SpSubgroup n F), IsRadicalSubgroup ell Q →
    ∃ (i : Index) (g : (SpSubgroup n F)),
      Q.comap (MulAut.conj g⁻¹).toMonoidHom = standardRadicals i
  standardFormula : ∀ (i : Index) (W : CharacterWeight ell K (SpSubgroup n F)),
    W.subgroup = standardRadicals i → RawNormalizerFactorization (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W

variable (inputs : ApplicationInputs n F (O := O) (Index := Index)
  (CyclicTarget := CyclicTarget) iotaM iotaG hinjM hinjG blocks D
  productFormula radicalKernel)

/-- Join the already checked K arguments on the same actual Sp/CSp datum.
The extension principles are generic; no Type B structural fact is used. -/
def hypotheses : AllBlocksHypotheses (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG blocks
    hinjM (field_spSubgroup_map n F) D productFormula radicalKernel := by
  letI := inputs.structuralSource.field_cyclic
  exact {
    prime := inputs.prime
    coefficient := inputs.coefficient
    cover := TypeCOddPrimeSymplecticCover.ellPrimeCover n F
      inputs.prime inputs.odd inputs.coverSource
    divides_simple_order := inputs.dividesSimpleOrder
    structural := structural n F inputs.structuralSource
    rootAgreement := inputs.restriction.roots
    brauer_injective_downstairs := hinjG
    localReduction := inputs.localReduction
    liftCompatible := inputs.correspondenceSource.liftReductionCompatible
    lift_primeTo := inputs.liftPrimeTo
    lift_trivial := inputs.liftTrivial
    extensions := TypeCOddPrimeExtensionClauses.extensionClauses n F iotaG
      inputs.structuralSource inputs.brauerExtension inputs.ordinaryExtension
    correspondence := TypeCProposition313CriterionCorrespondence.globalCorrespondence
      (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D iotaM hinjM blocks productFormula radicalKernel
      inputs.correspondenceSource
    hall := inputs.hall
    JG := TypeCOddPrimeInertiaHall.allPairsJG n F iotaG inputs.odd
      inputs.index_dvd_two inputs.structuralSource.quotient_cyclic inputs.hall
    constituent := TypeCOddPrimeConstituentFactorization.constituentClause_of_lemma312
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG hinjG blocks.downstairs inputs.basicSet
      inputs.blockInputs inputs.restriction
    rawNormalizer := TypeCOddPrimeWeightStabilizerTransport.rawNormalizerClause_of_standard_subgroups
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) inputs.standardRadicals inputs.radicalCoverage inputs.standardFormula }

/-- Invoke the universal fixed-output source at this actual Type C input.
The target family uses the same downstairs blocks, roots and local reductions;
the cover is the same matrix projection to the pre-existing PSp quotient.
The external certificate's source interpretation is still an audit boundary. -/
theorem full_block_condition_source_instantiated
    (criterion : TypeBBroughSpathCriterionSource.Theorem45Certificate) :
    Nonempty (TypeBFullBlockCondition.FamilyWitness
      (downstairsFamily (SpSubgroup n F) iotaG blocks inputs.prime hinjG inputs.localReduction)
      (TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        inputs.prime inputs.odd inputs.coverSource)) :=
  criterion.allBlocks (SpSubgroup n F) (fieldAction n F) (naturalAction n F) iotaM iotaG blocks hinjM (field_spSubgroup_map n F) D
    productFormula radicalKernel
    (hypotheses n F iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel inputs)

end ModularRep.PaperProofs.TypeCOddPrimeCriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
