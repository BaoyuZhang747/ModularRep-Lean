import ModularRep.PaperProofs.OddTwoWeightGroupEquiv
import ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
import ModularRep.IrreducibleBrauerCharacterEquiv

/-!
# Own-character reductions through an actual group equivalence

An arbitrary existing own-normalizer reduction is transported through the
canonical normalizer equivalence. Its target root and irreducible Brauer
character are computed, and its own ordinary-character identity is proved.
The horizontal root compatibility is K because the target root is this
transport. Ambient and quotient compatibility travel through the actual
inclusion and quotient squares. No independent root is identified with it.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoActualCentralInflationPacket
open ModularRep.PaperProofs.OddTwoDefinition35OwnReduction

universe u

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance groupEquivReductionSubgroupFintype {A : Type u}
    [Group A] [Finite A] (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

variable (W : CharacterWeight p K G) (e : G ≃* H)
variable (R : OwnNormalizerReduction (k := k) W)

/-- The target root is the SAME source convention transported by the actual
normalizer map, for every source root packet. -/
def mappedNormalizerRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)) :=
  (ownReductionRoot W R).alongMulEquiv (normalizerEquiv e W.subgroup)

/-- Actual representation pullback computes the target irreducible Brauer
character without an independent reduction-existence source. -/
def mappedNormalizerBrauer : IBr (mappedNormalizerRoot W e R) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv (ownReductionRoot W R)
    (normalizerEquiv e W.subgroup) (ownReductionBrauer W R)

theorem mappedNormalizerBrauer_values
    (x : PrimeRegularElement (G := Subgroup.normalizer
      ((W.mapGroupEquiv e).subgroup : Set H)) p) :
    (mappedNormalizerBrauer W e R).1 x =
      (ownReductionBrauer W R).1
        (PrimeRegularElement.map (normalizerEquiv e W.subgroup).symm.toMonoidHom x) := rfl

/-- Transported ordinary values and the original own reduction determine
the target reduction, on the OWN local character of the mapped pair. -/
theorem mappedNormalizerBrauer_ownReduction :
    NormalizerInflatedReduction (W.mapGroupEquiv e).subgroup
      (W.mapGroupEquiv e).localCharacter (mappedNormalizerRoot W e R)
      (mappedNormalizerBrauer W e R) := by
  intro x
  change (W.mapGroupEquiv e).localCharacter (QuotientGroup.mk x.1) =
    (ownReductionBrauer W R).1
      (PrimeRegularElement.map (normalizerEquiv e W.subgroup).symm.toMonoidHom x)
  have h := mapGroupEquiv_normalizer_values W e
    ((normalizerEquiv e W.subgroup).symm x.1)
  have cancellation := congrArg
    (fun z : Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H) =>
      (W.mapGroupEquiv e).localCharacter (QuotientGroup.mk z))
    ((normalizerEquiv e W.subgroup).apply_symm_apply x.1)
  exact cancellation.symm.trans (h.trans (ownReductionValues W R
    (PrimeRegularElement.map (normalizerEquiv e W.subgroup).symm.toMonoidHom x)))

/-- The complete target own reduction is computed from R. -/
def mapOwnReduction : OwnNormalizerReduction (k := k) (W.mapGroupEquiv e) where
  root := mappedNormalizerRoot W e R
  brauer := mappedNormalizerBrauer W e R
  own_reduction := mappedNormalizerBrauer_ownReduction W e R

@[simp] theorem mapOwnReduction_root :
    ownReductionRoot (W.mapGroupEquiv e) (mapOwnReduction W e R) =
      (ownReductionRoot W R).alongMulEquiv (normalizerEquiv e W.subgroup) := rfl

/-- This is the exact horizontal square consumed by the actual tuple
transport. It compares a root with ITS transported root, never two
independently chosen conventions. -/
theorem mapOwnReduction_horizontal :
    RootCompatibleAlong
      (ownReductionRoot (W.mapGroupEquiv e) (mapOwnReduction W e R))
      (ownReductionRoot W R) (normalizerEquiv e W.subgroup).toMonoidHom := by
  intro V x a
  exact ((ownReductionRoot W R).alongMulEquiv_lift
    (normalizerEquiv e W.subgroup) a.1).symm

/-- Arbitrary admissible ambient compatibility transports through the
literal inclusion square, with target ambient root iota.alongMulEquiv e. -/
theorem mapOwnReduction_ambientCompatible
    (iota : PrimeRegularRootEmbedding p k K G)
    (compatible : RootCompatibleAlong iota (ownReductionRoot W R)
      (Subgroup.normalizer (W.subgroup : Set G)).subtype) :
    RootCompatibleAlong (iota.alongMulEquiv e)
      (ownReductionRoot (W.mapGroupEquiv e) (mapOwnReduction W e R))
      (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype := by
  exact rootCompatibleAlong_transport (ownReductionRoot W R) iota
    (Subgroup.normalizer (W.subgroup : Set G)).subtype
    (normalizerEquiv e W.subgroup) e
    (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype
    (fun _ => rfl) compatible

section Quotient

variable (rootQ : PrimeRegularRootEmbedding p k K (NormalizerQuotient W.subgroup))
variable (phiQ : IBr rootQ)

/-- Actual quotient-root transport, without any selection claim. -/
def mappedQuotientRoot : PrimeRegularRootEmbedding p k K
    (NormalizerQuotient (W.mapGroupEquiv e).subgroup) :=
  rootQ.alongMulEquiv (normalizerQuotientEquiv e W.subgroup)

/-- The exact quotient Brauer character, transported as an actual IBr. -/
def mappedQuotientBrauer : IBr (mappedQuotientRoot W e rootQ) :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv rootQ
    (normalizerQuotientEquiv e W.subgroup) phiQ

theorem mappedQuotientBrauer_values
    (x : PrimeRegularElement (G := NormalizerQuotient (W.mapGroupEquiv e).subgroup) p) :
    (mappedQuotientBrauer W e rootQ phiQ).1 x =
      phiQ.1 (PrimeRegularElement.map
        (normalizerQuotientEquiv e W.subgroup).symm.toMonoidHom x) := rfl

/-- Every actual source quotient reduction transports to the OWN quotient
character of the actual image pair. No selected reduction is substituted. -/
theorem mappedQuotientBrauer_reduction
    (reduction : ∀ x : PrimeRegularElement (G := NormalizerQuotient W.subgroup) p,
      W.localCharacter x.1 = phiQ.1 x)
    (x : PrimeRegularElement (G := NormalizerQuotient (W.mapGroupEquiv e).subgroup) p) :
    (W.mapGroupEquiv e).localCharacter x.1 =
      (mappedQuotientBrauer W e rootQ phiQ).1 x := by
  exact reduction (PrimeRegularElement.map
    (normalizerQuotientEquiv e W.subgroup).symm.toMonoidHom x)

/-- The quotient and normalizer transports preserve the actual quotient
projection square and any originally admissible quotient-root condition. -/
theorem mapOwnReduction_quotientCompatible
    (compatible : RootCompatibleAlong rootQ (ownReductionRoot W R)
      (normalizerProjection W.subgroup)) :
    RootCompatibleAlong (mappedQuotientRoot W e rootQ)
      (ownReductionRoot (W.mapGroupEquiv e) (mapOwnReduction W e R))
      (normalizerProjection (W.mapGroupEquiv e).subgroup) := by
  exact rootCompatibleAlong_transport (ownReductionRoot W R) rootQ
    (normalizerProjection W.subgroup)
    (normalizerEquiv e W.subgroup) (normalizerQuotientEquiv e W.subgroup)
    (normalizerProjection (W.mapGroupEquiv e).subgroup)
    (fun _ => rfl) compatible

end Quotient

end ModularRep.PaperProofs.OddTwoGroupEquivOwnReduction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
