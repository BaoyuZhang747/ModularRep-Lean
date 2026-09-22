import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedP3Application
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTableDerivedLiteralTripleCoverFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4FullCover
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalBabyTwoFullCover
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyOddFullCover
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoFullCover
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterOddFullCover

/-! Applications of the stated structural and numerical sources. These results produce raw extension and block data. They do not assert that the independently chosen roots are compatible. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications

namespace J4

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {p : ℕ} {k K U X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem definition41_from_external_inputs
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    let Cover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian
    SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.RawDefinition41Certificate iota R Cover := by
  exact SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.raw_of_canonical
    (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (SporadicFi24P3Definition44NamedCarrierCanonicalJ4FullCover.exists_definition41_of_full_cover_and_defect_counts
      iota hinj R C cover hcover hkernel hsimple hnonabelian hOuter D T source compatibility fieldSource)

end J4

namespace BabyTwo

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource DefectZeroReductionSource TrivialWeightSource)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalBabyTwoNumerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoFullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {k K U X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

theorem definition41_from_external_inputs
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
    (source : BabyTwoSource iota hinj R)
    (small : SmallDefectNumericalSource iota hinj R)
    (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 2)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime) :
    let Cover := identityTwoPrimeCover_of_fullCover_kernel_card_two
      cover hcover hkernel hsimple hnonabelian
    SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.RawDefinition41Certificate iota R Cover := by
  exact SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.raw_of_canonical
    (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (SporadicFi24P3Definition44NamedCarrierCanonicalBabyTwoFullCover.exists_definition41_of_full_cover_and_baby_two_sources
      iota hinj R source small C cover hcover hkernel hsimple hnonabelian hOuter D T compatibility fieldSource)

end BabyTwo

namespace BabyOdd

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefectCounts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphisms

universe u
variable {p : ℕ} {k K X S : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Group S] [Fintype S]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem definition41_from_external_inputs
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (hpne : p ≠ 2)
    (q : X →* S) (hq : IsUniversalCentralExtension q)
    (hkernel : Nat.card q.ker = 2)
    (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
    (hOuter : Nat.card ((MulAut S)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := S)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (source : CyclicNoncyclicNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (lower : QuotientDataFamily iota hinj R C
      (ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel))
    (fieldSource : SpathCoefficientField p k iota.prime) :
    let Cover := ellPrimeCover_of_fullCover_kernel_two iota.prime hpne q hq hs hna hkernel
    SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.RawDefinition41Certificate iota R Cover := by
  exact SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.raw_of_original
    (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (SporadicFi24P3Definition44NamedCarrierBabyOddFullCover.exists_definition41_of_full_cover_and_baby_odd_sources
      iota hinj R C hpne q hq hkernel hs hna hOuter D T source compatibility lower fieldSource)

end BabyOdd

namespace MonsterTwo

open ModularRep
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (ActualBlock LiteralBlockSource DefectZeroReductionSource TrivialWeightSource)
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBabyTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterTwoSources
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoNumerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {k K U X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

theorem definition41_from_external_inputs
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := 2) (k := k) (K := K) (X := X))
    (source : MonsterTwoSource iota hinj R)
    (small : SmallDefectNumericalSource iota hinj R)
    (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := 2) (X := X))
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField 2 k iota.prime) :
    let Cover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian
    SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.RawDefinition41Certificate iota R Cover := by
  exact SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.raw_of_canonical
    (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (SporadicFi24P3Definition44NamedCarrierCanonicalMonsterTwoFullCover.exists_definition41_of_full_cover_and_monster_two_sources
      iota hinj R source small C cover hcover hkernel hsimple hnonabelian hOuter D T compatibility fieldSource)

end MonsterTwo

namespace MonsterOdd

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierMonsterOddSources
open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZ318FixedTheoremGate
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSelfCover

open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4FullCover
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction

universe u

variable {p : ℕ} {k K U X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group U] [Group X] [Fintype X]

local instance brauerFintype (iota : PrimeRegularRootEmbedding p k K X) : Fintype (IBr iota) :=
  Fintype.ofFinite _

variable [Fintype (WeightClass (p := p) (K := K) (X := X))]

theorem definition41_from_external_inputs
    (iota : PrimeRegularRootEmbedding p k K X)
    (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
    (R : LiteralBlockSource (p := p) (k := k) (K := K) (X := X))
    (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
    (cover : U →* X) (hcover : IsUniversalCentralExtension cover)
    (hkernel : Nat.card cover.ker = 1)
    (hsimple : IsSimpleGroup X) (hnonabelian : ¬ IsMulCommutative X)
    (hOuter : Nat.card ((MulAut X)ᵐᵒᵖ ⧸
      (RepresentationWeight.innerInverseOpHom (G := X)).range) = 1)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (hpOdd : 3 ≤ p)
    (source : MonsterOddNumericalSource iota hinj R)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (fieldSource : SpathCoefficientField p k iota.prime) :
    let Cover := identityEllPrimeCover_of_fullCover_kernel_card_one
      iota.prime cover hcover hkernel hsimple hnonabelian
    SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.RawDefinition41Certificate iota R Cover := by
  exact SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.raw_of_canonical
    (iota := iota) (R := R) (Cover := _) (C := C) (D := D) (T := T)
    (center_eq_bot_of_nonabelian_simple hsimple hnonabelian)
    (SporadicFi24P3Definition44NamedCarrierMonsterOddFullCover.exists_definition41_of_full_cover_and_monster_odd_sources
      iota hinj R C cover hcover hkernel hsimple hnonabelian hOuter D T hpOdd source compatibility fieldSource)

end MonsterOdd

namespace Fi24Three
open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierAcceleratedP3Application
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
universe u
variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction] [MulAction SourceAction SourceBrauer] [MulAction SourceAction SourceWeight]
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

/-- The named universal 3'-cover is an explicit structural binding. The 49
character-theoretic inputs are exactly the accepted prime-three contract. -/
theorem definition41_from_external_inputs
    (iota : PrimeRegularRootEmbedding 3 k K X)
    (R : LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X))
    (Cover : EllPrimeCoverSource 3 X)
    (I : ExternalInputs (SourceAction := SourceAction) (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) iota R) : RawDefinition41Certificate iota R Cover := by
  obtain ⟨Omega, hOmega, hblock, hdata⟩ :=
    SporadicFi24P3Definition44NamedCarrierAcceleratedP3Application.definition41_from_external_inputs iota R I
  exact raw_of_centerless_rows (iota := iota) (R := R) (Cover := Cover)
    (D := _) (T := _) _ Omega hOmega hblock hdata
end Fi24Three

namespace Fi24Two

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorOrdinaryCorrespondence
open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryBlockData
open SporadicFi24P3Definition44NamedCarrierSmallDefectNumericalSource
open SporadicFi24P3Definition44NamedCarrierSmallDefectPhysicalCounts
open SporadicFi24P3Definition44NamedCarrierTrivialSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures
open SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks
open SporadicFi24P3Definition44NamedCarrierActualTwoSectorCounts
open SporadicFi24P3Definition44NamedCarrierActualNumericalEquiv
open SporadicFi24P3Definition44NamedCarrierWeightSectorFinite
open SporadicFi24P3Definition44NamedCarrierAllPairs

open SporadicFi24P3Definition44NamedCarrierActualTwoSectorSmallDefectCorrespondence
open SporadicFi24P3Definition44NamedCarrierActualSectorOrdinarySpan
open SporadicFi24P3Definition44NamedCarrierActualSectorCoordinateEvaluation
open SporadicFi24P3Definition44NamedCarrierSameIotaCyclotomicRoot
open SporadicFi24P3Definition44NamedCarrierTrivialColumnPermutation
open SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation
open SporadicFi24P3Definition44NamedCarrierKleinFourIntegerData
open SporadicFi24P3Definition44NamedCarrierKleinFourActualCounts
open SporadicFi24P3Definition44NamedCarrierTrivialLiteralActualCounts

open SporadicFi24P3Definition44NamedCarrierKleinFourLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialBlockData
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialActualCounts

universe u v w
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
local instance quotientFintype : Fintype (X ⧸ Subgroup.center X) := Fintype.ofFinite _
open EvenFieldFLZ318FixedTheoremGate
variable {S : Type u} [Group S] [Fintype S]
variable (q : X →* S) (hq : IsUniversalCentralExtension q)
variable (hs : IsSimpleGroup S) (hna : ¬ IsMulCommutative S)
variable (hkernel : Nat.card q.ker = 3)
variable (hOuterS : Nat.card (SporadicFi24P3Definition44NamedCarrierActualOuterQuotient.LiteralOuterQuotient S) = 2)
open SporadicFi24P3Definition44NamedCarrierRemainingTrivialLiteralCorrespondence
open SporadicFi24P3Definition44NamedCarrierFaithfulLiteralActualCount
open SporadicFi24P3Definition44NamedCarrierFaithfulSmallActualCount

open ModularRep.NavarroBrauerRestrictionCovering ModularRep.NavarroCoveringBrauerExtension
open EvenFieldFLZ318FixedTheoremGate EvenFieldFLZSourceConditions
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open SporadicFi24QOneNormalisationActual (DefectZeroOrdinaryBlockSource)
open SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
open SporadicFi24P3Definition44NamedCarrierOriginalIdentityFamily (QuotientDataFamily)
open SporadicFi24P3Definition44NamedCarrierOriginalPrimeCenterFamily
  (TrivialAmbientDataFamily TrivialAmbientRootFamily)
open SporadicFi24P3Definition44NamedCarrierActualOuterQuotient
open SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open SporadicFi24P3Definition44NamedCarrierCanonicalEquivQOne
open SporadicFi24P3Definition44NamedCarrierAllLiteralBrauerCorrespondence

open SporadicFi24P3Definition44NamedCarrierAllLiteralTripleCoverFamily
open SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryTableConstructor
open SporadicFi24P3Definition44NamedCarrierOrdinaryDefectZeroBlock


open SporadicFi24P3Definition44NamedCarrierTableDerivedLiteralTripleCoverFamily

include hOuterS in
theorem definition41_from_external_inputs :
    letI := centerCardInverseFromCover (k := k) q hq hs hna hkernel
    ∀ (iota : PrimeRegularRootEmbedding 2 k K X)
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      {BIndex : Type u} [Fintype BIndex] {e : BIndex → k[X]} (blocks : BlockIdempotentDecomposition e)
      (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
      (Rbar : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X ⧸ Subgroup.center X))
      (tau : MulAut X)
      {RowT : Fin 34 → Type v} {RowF : Fin 34 → Type w}
      [∀ i, Finite (RowT i)] [∀ i, Finite (RowF i)]
      {BlockD : Type u} [MulAction (MulAut (X ⧸ Subgroup.center X))ᵐᵒᵖ BlockD]
      (T : TrivialOrdinaryTableData iota tau RowT BlockD)
      (_F : FaithfulOrdinaryTableData iota RowF)
      (_compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
      (_decomposition : ∀ a : MulAut X, ∃ x : X,
  a = MulAut.conj x ∨ a = MulAut.conj x * tau)
      (_hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
      (trivialRoles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
      (faithfulRoles : ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
  Fin 2 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = nu})
      (_Lrows :
  SporadicFi24P3Definition44NamedCarrierTwoLocalOrdinaryRowData.TwoLocalOrdinaryRowData
    (iota := iota) (R := R) (Rbar := Rbar) (hprimeTo := T.primeToCenter)
    (roles := trivialRoles) (Sglobal := T.primitiveGlobal))
      (_small : SmallDefectNumericalSource iota hinj R)
      (_hDefectTrivial : ∀ j : Fin 4, ∃ H : Subgroup X,
  actualHasDefect R (trivialRoles j.succ).1 H ∧ Nat.card H =
    (if j = 0 then 4 else if j = 1 then 8 else 1))
      (_hDefectFaithful : ∀ (nu : CentralSector (k := k) (X := X)) (hnu : nu ≠ 1),
  ∃ H : Subgroup X, actualHasDefect R (faithfulRoles nu hnu 1).1 H ∧ Nat.card H = 8)
      (D : ActualOrdinaryDecomposition iota hinj blocks)
      (C : ActualSectorOrdinaryRows iota hinj blocks D
  (1 : CentralSector (k := k) (X := X)) (Fin 108))
      (A : PrimeRegularRepresentativeCover 2 X (Fin 91))
      (roots : SameIotaConductorRoot iota 10015005)
      (_hvalues : ∀ r c, (C.character r).1 (A.representative c).1 =
  SporadicFi24P3Definition44NamedCarrierTrivialFullColumnEvaluation.rawEvaluatedRows (iota.lift roots.source_root) r c)
      (_allocation : ∀ r : Fin 108, D.ordinaryBlock (C.character r) =
  (trivialRoles (printedBlockLabel r)).1)
      (_fusion : ∀ c : Fin 91, ∃ x : X, tau (A.representative c).1 =
  x * (A.representative (fullPerm c)).1 * x⁻¹)
      (CF : ∀ nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1},
  ActualSectorOrdinaryRows iota hinj blocks D nu.1 (Fin 74))
      (rootsF : {nu : CentralSector (k := k) (X := X) // nu ≠ 1} →
  SameIotaConductorRoot iota 770385)
      (_valuesF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r c,
  ((CF nu).character r).1 (A.representative c).1 =
    SporadicFi24P3Definition44NamedCarrierFaithfulFullColumnEvaluation.rawEvaluatedRows
      (iota.lift (rootsF nu).source_root) r c)
      (_allocationF : ∀ (nu : {nu : CentralSector (k := k) (X := X) // nu ≠ 1}) r,
  D.ordinaryBlock ((CF nu).character r) =
    (faithfulRoles nu.1 nu.2
      (SporadicFi24P3Definition44NamedCarrierFaithfulSmallPolynomialData.faithfulPrintedBlockLabel r)).1)
      (Ccanonical : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
      (_Dzero : DefectZeroReductionSource iota)
      (_Tzero : TrivialWeightSource (p := 2) (X := X))
      (_hsingletonZero :
  ∀ d : GlobalDefectZeroCharacter (p := 2) (K := K) (X := X),
    Subsingleton {phi : IBr iota // brauerBlock iota hinj blocks phi = D.ordinaryBlock d.1})
      (_lower : QuotientDataFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel))
      (_ambientData : TrivialAmbientDataFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) hq)
      (_seed : TrivialAmbientRootFamily iota hinj R Ccanonical
  (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) hq)
      (_extensionPrinciple : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
      (_fieldSource : SpathCoefficientField 2 k iota.prime)
      (_S9295 : Navarro9295BrauerRestrictionCoveringPrinciple 2 k K)
      (_S9495 : Navarro9495BrauerCoveringPrinciple 2 k K)
      (_S820 : Navarro820CyclicBrauerTwistPrinciple 2 k K),
    SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.RawDefinition41Certificate
      iota R (ellPrimeCover_of_fullCover_kernel_three iota.prime (by decide) q hq hs hna hkernel) := by
  let := centerCardInverseFromCover (k := k) q hq hs hna hkernel
  intro iota hinj BIndex instBIndex e blocks R Rbar tau RowT RowF
    instRowsT instRowsF BlockD instBlockD T F compatibility decomposition hinverts
    trivialRoles faithfulRoles Lrows small hDefectTrivial hDefectFaithful D C A
    roots hvalues allocation fusion CF rootsF valuesF allocationF Ccanonical
    Dzero Tzero hsingletonZero lower ambientData seed extensionPrinciple fieldSource
    S9295 S9495 S820
  have h := SporadicFi24P3Definition44NamedCarrierTableDerivedLiteralTripleCoverFamily.exists_definition41_of_tables_and_literal_values
    (q := q) (hq := hq) (hs := hs) (hna := hna) (hkernel := hkernel) (hOuterS := hOuterS)
    iota hinj blocks R Rbar tau T F compatibility decomposition hinverts
    trivialRoles faithfulRoles Lrows small hDefectTrivial hDefectFaithful D C A
    roots hvalues allocation fusion CF rootsF valuesF allocationF Ccanonical
    Dzero Tzero hsingletonZero lower ambientData seed extensionPrinciple fieldSource
    S9295 S9495 S820
  exact SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate.raw_of_original
    (iota := iota) (R := R) (Cover := _) (C := Ccanonical) (D := Dzero) (T := Tzero) h

end Fi24Two

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedCaseApplications


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
