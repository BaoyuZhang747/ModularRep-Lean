import ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin
import ModularRep.PaperProofs.TypeCCoherentFiniteRootConvention
import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent

/-!
# The literal original target chosen under one finite-root convention

The target root and every selected own quotient root are computed from C
before TargetData.toProblem is formed. The only local character input is
Navarro 3.18 at each actual ordinary defect-zero quotient character and
that fixed root. Its normalizer Brauer character is computed by actual
representation inflation, with both root compatibilities proved from C.

The existing specified block and group inputs remain explicit. No matching,
extension, induction, relation, original witness or complete block witness
is an input or output. In particular, the old bare Feng--Malle existential
is not upgraded to coherent metadata. A future published joint choice must
retain the convention for its own chosen matched packets separately.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoCoherentTargetData

open ModularRep CharacterWeight FDRepSimpleClassKZero
open IrreducibleBrauerCharacterSurjectiveDescent
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions
open OddTwoFinalBlockOrbitCentralCoverDescentWindow
open OddTwoFengMalleForwardSourceJoin
open TypeCCoherentFiniteRootConvention
open SporadicCompleteCollapseLemma52ConcreteLocal (IsBrauerReduction)

universe u

local instance coherentTargetSubgroupFintype
    {G : Type u} [Group G] [Finite G] (Q : Subgroup G) :
    Fintype Q := Fintype.ofFinite _

section OwnReduction

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (C : Convention p k K) (W : CharacterWeight p K G)

/-- Navarro 3.18 on this OWN quotient character under the prescribed
standard scalar convention. No root is independently chosen in the record. -/
structure CanonicalQuotientReduction where
  brauer : IBr (C.rootAt (NormalizerQuotient W.subgroup))
  reduction : IsBrauerReduction
    (C.rootAt (NormalizerQuotient W.subgroup)) W.localCharacter brauer

/-- The actual quotient map of this radical inside its normalizer. -/
def ownProjection :
    Subgroup.normalizer (W.subgroup : Set G) →* NormalizerQuotient W.subgroup :=
  QuotientGroup.mk' (W.subgroup.subgroupOf
    (Subgroup.normalizer (W.subgroup : Set G)))

theorem ownProjection_surjective : Function.Surjective (ownProjection W) :=
  QuotientGroup.mk'_surjective _

variable (R : CanonicalQuotientReduction C W)

/-- Representation inflation along the literal quotient map. Its kernel
need not be prime to p; surjectivity and the computed compatible roots suffice. -/
def normalizerBrauer :
    IBr (C.rootAt (Subgroup.normalizer (W.subgroup : Set G))) :=
  (inflateToKernelTrivialIBrAlong (ownProjection W) (ownProjection_surjective W)
    (C.rootAt (Subgroup.normalizer (W.subgroup : Set G)))
    (C.rootAt (NormalizerQuotient W.subgroup))
    (C.rootAt_compatible (ownProjection W)) R.brauer).1

theorem normalizerBrauer_values
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set G)) p) :
    (normalizerBrauer C W R).1 x =
      R.brauer.1 (PrimeRegularElement.map (ownProjection W) x) := rfl

/-- The SAME own ordinary quotient reduction gives its inflated reduction. -/
theorem normalizerBrauer_reduction :
    NormalizerInflatedReduction W.subgroup W.localCharacter
      (C.rootAt (Subgroup.normalizer (W.subgroup : Set G)))
      (normalizerBrauer C W R) := by
  intro x
  exact R.reduction (PrimeRegularElement.map (ownProjection W) x)

/-- The old compatible-reduction interface is filled by this computed
normalizer character and the SAME coherent ambient root. -/
def normalizerReduction : CompatibleReduction (C.rootAt G) W where
  root := C.rootAt (Subgroup.normalizer (W.subgroup : Set G))
  rootCompatible := C.rootAt_compatible
    (Subgroup.normalizer (W.subgroup : Set G)).subtype
  brauer := normalizerBrauer C W R
  reduction := normalizerBrauer_reduction C W R

@[simp] theorem normalizerReduction_root :
    (normalizerReduction C W R).root =
      C.rootAt (Subgroup.normalizer (W.subgroup : Set G)) := rfl

end OwnReduction

section Target

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : LiteralFengMalleProblem n F) (C : Convention 2 P.k P.K)

/-- Standard target group/specified inputs at the computed convention.
The quotient-reduction input is Navarro 3.18 on each raw own character,
independent of any global map or selected matched packet. -/
structure CanonicalTargetData where
  coverSource : OddTwoUniversalPrimeToTwoSelfCover.OddSymplecticFullCoverSource n F
  blockSource : LocalBlockInductionSource
    (p := 2) (k := P.k) (K := P.K) (G := LiteralPSp n F)
    (Block := LiteralPrimitiveBlock P.k (LiteralPSp n F))
  catalogue_idempotent : ∀ b : LiteralPrimitiveBlock P.k (LiteralPSp n F),
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  support_transport : OperationsBrauerSupport (C.rootAt (LiteralPSp n F))
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
      (C.rootAt (LiteralPSp n F))) blockSource.operations
  support : OddTwoActualLocalBlockSupport.Source
    (C.rootAt (LiteralPSp n F)) blockSource.operations
  quotient_reductions : ∀ W : CharacterWeight 2 P.K (LiteralPSp n F),
    Nonempty (CanonicalQuotientReduction C W)
  oneRadical : RadicalSubgroup (p := 2) (G := LiteralPSp n F)
  oneRadical_eq_bot : oneRadical.1 = ⊥

namespace CanonicalTargetData

variable {P C} (S : CanonicalTargetData P C)

/-- A fixed choice on all raw own characters before any matching is chosen. -/
def quotientReduction (W : CharacterWeight 2 P.K (LiteralPSp n F)) :
    CanonicalQuotientReduction C W := Classical.choice (S.quotient_reductions W)

/-- The selected table evaluates the SAME raw-character choice. Its root
is computed from C, rather than inferred equal to an old independent table. -/
def selectedQuotientReduction (b : LiteralPrimitiveBlock P.k (LiteralPSp n F))
    (w : LiteralWeightFibre S.blockSource b) :
    SelectedLocalReductionSource S.blockSource b w where
  iota := C.rootAt (NormalizerQuotient (SelectedRadical S.blockSource b w))
  brauer := (S.quotientReduction (selectedCharacterWeight S.blockSource b w)).brauer
  reduction := (S.quotientReduction (selectedCharacterWeight S.blockSource b w)).reduction

@[simp] theorem selectedQuotientReduction_root
    (b : LiteralPrimitiveBlock P.k (LiteralPSp n F))
    (w : LiteralWeightFibre S.blockSource b) :
    (S.selectedQuotientReduction b w).iota =
      C.rootAt (NormalizerQuotient (SelectedRadical S.blockSource b w)) := rfl

/-- Full finite-domain agreement follows from actual quotient/subgroup
cardinality divisibility, before a Definition41 witness is requested. -/
theorem selectedQuotientReduction_roots
    (b : LiteralPrimitiveBlock P.k (LiteralPSp n F))
    (w : LiteralWeightFibre S.blockSource b)
    (z : rootsOfUnity (primeRegularExponent 2
      (NormalizerQuotient (SelectedRadical S.blockSource b w))) P.k) :
    (S.selectedQuotientReduction b w).iota.lift (((z : P.kˣ) : P.k)) =
      (C.rootAt (LiteralPSp n F)).lift (((z : P.kˣ) : P.k)) := by
  let Q := SelectedRadical S.blockSource b w
  let N := Subgroup.normalizer (Q : Set (LiteralPSp n F))
  have hd : Nat.card (NormalizerQuotient Q) ∣ Nat.card (LiteralPSp n F) :=
    (Q.subgroupOf N).card_quotient_dvd_card.trans
      (Subgroup.card_subgroup_dvd_card N)
  exact C.rootAt_lift_of_card_dvd hd z

variable (admissible : P.iota = C.rootAt (LiteralSp n F))

/-- Build the existing target data AFTER choosing the ambient convention
and exact quotient table. No original-condition conclusion is a field. -/
def targetData : TargetData P where
  coverSource := S.coverSource
  iota := C.rootAt (LiteralPSp n F)
  projectionRootCompatible := by
    rw [admissible]
    exact C.rootAt_compatible (literalProjection n F)
  injective := irreducibleBrauerCharacterInjectivity_of_rootEmbedding
    (C.rootAt (LiteralPSp n F))
  blockSource := S.blockSource
  catalogue_idempotent := S.catalogue_idempotent
  support_transport := S.support_transport
  selectedQuotientReduction := S.selectedQuotientReduction
  oneRadical := S.oneRadical
  oneRadical_eq_bot := S.oneRadical_eq_bot
  support := S.support
  reductions W := ⟨normalizerReduction C W (S.quotientReduction W)⟩

@[simp] theorem targetData_root :
    (S.targetData admissible).iota = C.rootAt (LiteralPSp n F) := rfl

@[simp] theorem targetData_selectedReduction
    (b : LiteralPrimitiveBlock P.k (LiteralPSp n F))
    (w : LiteralWeightFibre S.blockSource b) :
    (S.targetData admissible).selectedQuotientReduction b w =
      S.selectedQuotientReduction b w := rfl

@[simp] theorem targetData_problem_localReduction
    (b : LiteralPrimitiveBlock P.k (LiteralPSp n F))
    (w : LiteralWeightFibre S.blockSource b) :
    (S.targetData admissible).toProblem.localReduction b w =
      S.selectedQuotientReduction b w := rfl

/-- Direct canonical local reduction, retaining its computed root. This
is not asserted equal to the old arbitrary choice from T.reductions. -/
def canonicalLocalReduction
    (Q : RadicalSubgroup (p := 2) (G := LiteralPSp n F))
    (theta : LocalDefectZeroCharacter (K := P.K) Q) :
    (S.targetData admissible).toProblem.LocalReduction Q theta := by
  let W : CharacterWeight 2 P.K (LiteralPSp n F) :=
    characterWeightAt Nat.prime_two Q theta
  let R := normalizerReduction C W (S.quotientReduction W)
  exact
    { root := R.root
      rootCompatible := R.rootCompatible
      brauer := R.brauer
      reduction := R.reduction
      block_support := S.support.normalizer_block_of_reduction
        W R.root R.brauer R.rootCompatible R.reduction }

@[simp] theorem canonicalLocalReduction_root
    (Q : RadicalSubgroup (p := 2) (G := LiteralPSp n F))
    (theta : LocalDefectZeroCharacter (K := P.K) Q) :
    (S.canonicalLocalReduction admissible Q theta).root =
      C.rootAt (Subgroup.normalizer (Q.1 : Set (LiteralPSp n F))) := rfl

end CanonicalTargetData
end Target

end ModularRep.PaperProofs.TypeCOddTwoCoherentTargetData


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
