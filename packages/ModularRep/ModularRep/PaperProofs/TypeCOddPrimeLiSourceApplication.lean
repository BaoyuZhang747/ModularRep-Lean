import ModularRep.PaperProofs.TypeCOddPrimeCriterionApplication

/-!
# Li's existential standard family in the actual Type C criterion

Li Section 2.C and Lemma 5.5 supply a family of actual standard subgroups,
subgroup conjugacy coverage, and the stabilizer formula for each own local
character. The universal source below fixes precisely that output on the
literal Sp/CSp matrices and their natural field action. It does not assert
the global raw/class criterion clause. K chooses the family, indexes it by
its own subgroup elements, and invokes the accepted whole-pair transport.

The other source data contain no standard family or raw-normalizer premise.
The final theorem combines the existing actual criterion application with
the family supplied by Li. No inhabitant of either published certificate is
constructed, and no independently selected final Type C target is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddPrimeLiSourceApplication

open ModularRep FDRepSimpleClassKZero
open TypeBCriterionHypotheses TypeCConformalActionAdapter
open TypeCWeightTensorFieldAction
open TypeCOddPrimeConformalCriterionCarriers
open OddTwoConformalProjectiveRealisation (CSp PSp)
open EvenFieldFLZSourceConditions

section PublishedFamily

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]
variable (ell : ℕ) (K : Type) [Field K] [CharZero K] [IsAlgClosed K]

/-- Exact existential output of the source's standard-subgroup construction.
The representative is an actual subgroup, and the character quantified by
the last field is always the given weight's own local quotient character. -/
structure StandardFamily where
  representatives : Set (Subgroup (SpSubgroup n F))
  conjugacyCoverage : ∀ Q : Subgroup (SpSubgroup n F), IsRadicalSubgroup ell Q →
    ∃ (R : Subgroup (SpSubgroup n F)), R ∈ representatives ∧
      ∃ g : SpSubgroup n F, Q.comap (MulAut.conj g⁻¹).toMonoidHom = R
  formula : ∀ R ∈ representatives, ∀ W : CharacterWeight ell K (SpSubgroup n F),
    W.subgroup = R → RawNormalizerFactorization
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W

/-- Li 2.C/5.5 in one direction, uniformly on the fixed actual groups and
ordinary coefficients. The source chooses the family; no caller-chosen
predicate, global matching, raw/class clause or final target is accepted. -/
structure Li55Certificate : Prop where
  normalForms : ∀ (n : ℕ) (F : Type) [Field F] [Finite F]
      [(SpSubgroup n F).Normal] (ell : ℕ) (K : Type)
      [Field K] [CharZero K] [IsAlgClosed K],
    3 ≤ n → Odd (Nat.card F) → Nat.Prime ell → Odd ell →
      ¬ ell ∣ Nat.card F → Nonempty (StandardFamily n F ell K)

variable (family : StandardFamily n F ell K)

/-- Index the source family by its actual subgroup elements. -/
abbrev StandardFamily.Index := {R : Subgroup (SpSubgroup n F) // R ∈ family.representatives}

def StandardFamily.subgroup : family.Index → Subgroup (SpSubgroup n F) := Subtype.val

/-- Source subgroup coverage now has the exact protected K consumer type. -/
theorem StandardFamily.coverage (Q : Subgroup (SpSubgroup n F))
    (hQ : IsRadicalSubgroup ell Q) :
    ∃ (i : family.Index) (g : SpSubgroup n F),
      Q.comap (MulAut.conj g⁻¹).toMonoidHom = (StandardFamily.subgroup n F ell K family) i := by
  obtain ⟨R, hR, g, hg⟩ := family.conjugacyCoverage Q hQ
  exact ⟨⟨R, hR⟩, g, hg⟩

theorem StandardFamily.standard (i : family.Index)
    (W : CharacterWeight ell K (SpSubgroup n F))
    (hW : W.subgroup = (StandardFamily.subgroup n F ell K family) i) :
    RawNormalizerFactorization
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) W :=
  family.formula i.1 i.2 W hW

/-- The global raw/class clause is derived by the accepted WHOLE-pair
conjugation argument, not a field of the published source. -/
theorem StandardFamily.rawNormalizerClause (family : StandardFamily n F ell K) :
    RawNormalizerClause (ell := ell) (K := K)
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F) :=
  TypeCOddPrimeWeightStabilizerTransport.rawNormalizerClause_of_standard_subgroups
    (SpSubgroup n F) (fieldAction n F) (naturalAction n F)
    (StandardFamily.subgroup n F ell K family) (StandardFamily.coverage n F ell K family) (StandardFamily.standard n F ell K family)

end PublishedFamily

section Application

variable (n : ℕ) (F : Type) [Field F] [Finite F]
variable [(SpSubgroup n F).Normal]
variable {ell : ℕ} {k K O CyclicTarget : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharP k ell] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
variable [Group CyclicTarget] [IsCyclic CyclicTarget]

local instance ambientFintype : Fintype (CSp n F) := Fintype.ofFinite _
local instance baseFintype : Fintype (SpSubgroup n F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (CSp n F))]
variable [Fintype (LiteralPrimitiveBlock k (SpSubgroup n F))]
variable [Finite (TensorCharacters (k := k) (SpSubgroup n F))]
variable [MulAction
  (ActingGroup (k := k) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
  (LiteralPrimitiveBlock k (CSp n F))]
variable [MulAction (Ambient (fieldAction n F)) (LiteralPrimitiveBlock k (SpSubgroup n F))]
variable (iotaM : PrimeRegularRootEmbedding ell k K (CSp n F))
variable (iotaG : PrimeRegularRootEmbedding ell k K (SpSubgroup n F))
variable (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
variable (hinjG : IrreducibleBrauerCharacterInjectivity iotaG)
variable (blocks : BlockData (ell := ell) (k := k) (K := K) (SpSubgroup n F))
variable (D : OrdinaryReductionEquiv (k := k) (K := K)
  (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F))
variable (productFormula : BrauerLinearTensorProductFormula iotaM)
variable (radicalKernel : RadicalKernelLiftInput (p := ell)
  (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F) D)

/-- Precisely the remaining source data of the accepted application.
No radical family, coverage, standard formula or global raw clause is a field. -/
structure OtherInputs where
  prime : Nat.Prime ell
  odd : Odd ell
  nondefining : ¬ ell ∣ Nat.card F
  coefficient : SpathCoefficientField ell k prime
  structuralSource : StructuralSource n F
  coverSource : TypeCOddPrimeSymplecticCover.CoverSource n F ell
  dividesSimpleOrder : ell ∣ Nat.card (PSp n F)
  localReduction : LocalReductionData (SpSubgroup n F) iotaG blocks
  correspondenceSource : TypeCProposition313CriterionCorrespondence.SourceInputs
    (O := O) (SpSubgroup n F) (fieldAction n F) (field_spSubgroup_map n F)
      D iotaM hinjM blocks productFormula radicalKernel
  basicSet : TypeCOddPrimeConstituentFactorization.BasicSetSource
    (O := O) (SpSubgroup n F) (fieldAction n F) (naturalAction n F)
      iotaG hinjG blocks.downstairs
  blockInputs : ∀ b : LiteralPrimitiveBlock k (SpSubgroup n F),
    TypeCOddPrimeConstituentFactorization.BlockSourceInputs
      (SpSubgroup n F) (fieldAction n F) (naturalAction n F)
        iotaG hinjG blocks.downstairs basicSet (CyclicTarget := CyclicTarget) b
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
  index_dvd_two : (SpSubgroup n F ⊔ Subgroup.center (CSp n F)).index ∣ 2

variable (inputs : OtherInputs n F (O := O) (CyclicTarget := CyclicTarget)
  iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel)

/-- Fill only the three removed source slots from the SAME existential family. -/
def applicationInputs (family : StandardFamily n F ell K) :
    TypeCOddPrimeCriterionApplication.ApplicationInputs n F
      (O := O) (Index := family.Index) (CyclicTarget := CyclicTarget)
      iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel where
  prime := inputs.prime
  odd := inputs.odd
  nondefining := inputs.nondefining
  coefficient := inputs.coefficient
  structuralSource := inputs.structuralSource
  coverSource := inputs.coverSource
  dividesSimpleOrder := inputs.dividesSimpleOrder
  localReduction := inputs.localReduction
  correspondenceSource := inputs.correspondenceSource
  basicSet := inputs.basicSet
  blockInputs := inputs.blockInputs
  restriction := inputs.restriction
  liftPrimeTo := inputs.liftPrimeTo
  liftTrivial := inputs.liftTrivial
  brauerExtension := inputs.brauerExtension
  ordinaryExtension := inputs.ordinaryExtension
  hall := inputs.hall
  index_dvd_two := inputs.index_dvd_two
  standardRadicals := (StandardFamily.subgroup n F ell K family)
  radicalCoverage := (StandardFamily.coverage n F ell K family)
  standardFormula := (StandardFamily.standard n F ell K family)

/-- The source's existential choice supplies the standard-family slot before
the actual Type C application is invoked. The full output remains fixed by
the independently stated universal criterion, on the SAME blocks/roots/cover. -/
theorem full_block_condition_source_instantiated
    (li : Li55Certificate)
    (criterion : TypeBBroughSpathCriterionSource.Theorem45Certificate) :
    Nonempty (TypeBFullBlockCondition.FamilyWitness
      (downstairsFamily (SpSubgroup n F) iotaG blocks inputs.prime hinjG inputs.localReduction)
      (TypeCOddPrimeSymplecticCover.ellPrimeCover n F
        inputs.prime inputs.odd inputs.coverSource)) := by
  let family := Classical.choice (li.normalForms n F ell K
    inputs.structuralSource.rank inputs.structuralSource.field_odd
    inputs.prime inputs.odd inputs.nondefining)
  exact TypeCOddPrimeCriterionApplication.full_block_condition_source_instantiated
    n F iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel
    (applicationInputs n F iotaM iotaG hinjM hinjG blocks D productFormula radicalKernel
      inputs family) criterion

end Application

end ModularRep.PaperProofs.TypeCOddPrimeLiSourceApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
