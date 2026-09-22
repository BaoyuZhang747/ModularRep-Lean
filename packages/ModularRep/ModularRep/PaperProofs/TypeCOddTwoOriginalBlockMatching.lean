import ModularRep.PaperProofs.TypeCOddTwoOriginalOwnPairAmbient
import ModularRep.PaperProofs.EvenFieldFLZCentrelessLocalPackets
import ModularRep.PaperProofs.OddTwoWeightGroupEquiv

/-!
# Original odd-two matching on its specified block fibres and own quotient pair

The family uses the original problem's exact catalogue, root, operations,
block stabilizers and selected reductions. Its block equivalences are
restrictions of the SAME original global map. For each image we use the
subgroup of its existing selected weight as the original radical Q.
Fixed-radical character uniqueness then proves equality of the entire pair;
there is no representative-matching input or new representative choice.

At an arbitrary reference character in this same block the accepted
centreless construction transports the exact selected quotient reduction.
The resulting raw quotient pair is proved equal to the actual group-image
pair. A canonical quotient coordinate also compares the reference and own
presentations. No complete BlockWitness or FamilyWitness is consumed.

This K carrier stage does not reconcile the distinct stored normalizer-root
conventions or transport chosen extensions, intermediate blocks or the two
Q=1 clauses to a complete target. Those stay attached to the unchanged
original witness; no universal choice of extra packets is required here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalBlockMatching

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZCentrelessCentralKernel
open EvenFieldFLZCentrelessLocalPackets OddTwoLiteralSpathTarget
open OddTwoSelectedWeightAutomorphismCoordinates

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

/-- The same complete specified data combined for all blocks. The finite
catalogue is exactly the one already stored in the original operations. -/
def family (P : Problem n F) : Definition35Family 2 where
  ellPrime := Nat.prime_two
  k := P.k
  K := P.K
  H := X n F
  Block := P.Block
  fintypeBlock := P.blockSource.operations.ambientBlockData.fintypeBlock
  blockIdempotent := P.blockSource.operations.ambientBlockData.blockIdempotent
  iota := P.iota
  irreducibleBrauerInjective := P.injective
  blocks := P.blockSource.operations.ambientBlockData.blocks
  blockSource := P.blockSource
  brauerBlock_transport := P.support_transport
  automorphisms b := {
    Gamma := (P.blockProblem b).Gamma
    groupGamma := (P.blockProblem b).groupGamma
    finiteGamma := (P.blockProblem b).finiteGamma
    gamma := (P.blockProblem b).gamma
    gammaBlock_fixed := (P.blockProblem b).gammaBlock_fixed }
  localReduction := P.localReduction

/-- This family changes no block problem, including its selected reduction. -/
theorem family_problem (P : Problem n F) (b : P.Block) :
    (family P).problem b = P.blockProblem b := rfl

/-- The displayed family catalogue is the actual specified primitive. -/
theorem family_primitive (P : Problem n F) (b : P.Block) :
    (family P).blockIdempotent b = b.1 := P.catalogue_idempotent b

/-- The fixed cover is the original identity prime-to-two cover. -/
abbrev familyCover (P : Problem n F) : EllPrimeCoverSource 2 (family P).H := P.cover

/-- No new full-stabilizer assumption is needed for this literal family. -/
def stabilizerAdapter (P : Problem n F) (b : P.Block) :
    Definition35AutomorphismStabilizerAdapter ((family P).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := by
    change a.1 = MulOpposite.op ((a.1.unop⁻¹)⁻¹)
    simp only [inv_inv, MulOpposite.op_unop]

section Matching

variable {P : Problem n F} (D : Definition41 P)

/-- The actual specified-block restriction of the existing global bijection. -/
def blockEquiv (b : P.Block) :
    Definition35Brauer (P.blockProblem b) ≃ Definition35Weight (P.blockProblem b) where
  toFun psi := ⟨D.map.equiv psi.1, (D.map.block_preserving psi.1).trans psi.2⟩
  invFun w := ⟨D.map.equiv.symm w.1, by
    have h := D.map.block_preserving (D.map.equiv.symm w.1)
    exact h.symm.trans ((congrArg P.blockSource.weightBlock
      (D.map.equiv.apply_symm_apply w.1)).trans w.2)⟩
  left_inv psi := Subtype.ext (D.map.equiv.symm_apply_apply psi.1)
  right_inv w := Subtype.ext (D.map.equiv.apply_symm_apply w.1)

@[simp] theorem blockEquiv_val (b : P.Block)
    (psi : Definition35Brauer (P.blockProblem b)) :
    (blockEquiv D b psi).1 = D.map.equiv psi.1 := rfl

/-- Recombination of these computed block maps is the SAME global map. -/
theorem blockEquiv_ownBlock (psi : IBr P.iota) :
    (blockEquiv D (P.brauerBlock psi) (P.ownBrauer psi)).1 = D.map.equiv psi := rfl

/-- All-block naturality uses the existing family transports and original
equivariance. Neither an independent block map nor a new action is supplied. -/
theorem blockEquiv_naturality (b : P.Block)
    (psi : Definition35Brauer ((family P).problem b))
    (a : (MulAut (X n F))ᵐᵒᵖ) :
    blockEquiv D (a • b) ((family P).transportBrauer a psi) =
      (family P).transportWeight a (blockEquiv D b psi) := by
  apply Subtype.ext
  exact D.map.equivariant a psi.1

variable (b : P.Block) (psi : Definition35Brauer (P.blockProblem b))

/-- This is the already selected image weight, not a fresh choice. -/
def selectedPair : CharacterWeight 2 P.K (X n F) :=
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  selectedCharacterWeight P.blockSource b (blockEquiv D b psi)

def selectedRadical : RadicalSubgroup (p := 2) (G := X n F) :=
  ⟨(selectedPair D b psi).subgroup, (selectedPair D b psi).radical⟩

theorem selectedPair_class : weightClass (selectedPair D b psi) = D.map.equiv psi.1 := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact selectedCharacterWeight_spec P.blockSource b (blockEquiv D b psi)

/-- The original character belongs to the original map's part at precisely
the subgroup of this selected image weight. -/
def selectedPart : D.map.Part (selectedRadical D b psi) :=
  ⟨psi.1, (congrArg radicalClass (selectedPair_class D b psi)).symm⟩

private theorem characterWeightAt_self (W : CharacterWeight 2 P.K (X n F)) :
    characterWeightAt Nat.prime_two ⟨W.subgroup, W.radical⟩
      ⟨W.localCharacter, W.defectZero⟩ = W := by
  cases W
  rfl

/-- Injectivity on a fixed radical identifies the actual own character.
No singleton defect-zero hypothesis or representative equality is assumed. -/
theorem selectedLocalCharacter_eq :
    D.map.localMap (selectedRadical D b psi) (selectedPart D b psi) =
      (⟨(selectedPair D b psi).localCharacter, (selectedPair D b psi).defectZero⟩ :
        LocalDefectZeroCharacter (K := P.K) (selectedRadical D b psi)) := by
  apply (localDefectZeroEquivWeightRadicalFibre
    (K := P.K) Nat.prime_two (selectedRadical D b psi)).injective
  apply Subtype.ext
  rw [localDefectZeroEquivWeightRadicalFibre_apply_val,
    localDefectZeroEquivWeightRadicalFibre_apply_val]
  have h := IntrinsicGlobalToRepresentativeMaps.localMap_class P.iota D.map.equiv
    Nat.prime_two (selectedRadical D b psi) (selectedPart D b psi)
  have hs := characterWeightAt_self (P := P) (selectedPair D b psi)
  exact h.trans ((selectedPair_class D b psi).symm.trans
    (congrArg weightClass hs).symm)

/-- Equality of the ENTIRE original own pair and existing selected pair. -/
theorem originalOwnPair_eq_selected :
    TypeCOddTwoOriginalOwnPairAmbient.ownPair D
      (selectedRadical D b psi) (selectedPart D b psi) = selectedPair D b psi := by
  exact (congrArg (characterWeightAt Nat.prime_two (selectedRadical D b psi))
    (selectedLocalCharacter_eq D b psi)).trans
      (characterWeightAt_self (P := P) (selectedPair D b psi))

/-- The existing original matching is now indexed by the selected subgroup.
Its local reduction and extensions are retained as the same stored fields. -/
abbrev selectedMatched := D.matched (selectedRadical D b psi) (selectedPart D b psi)

theorem selectedMatched_frattini :
    (selectedMatched D b psi).ambient.base ⊔
      P.LocalGroup (selectedMatched D b psi).ambient (selectedRadical D b psi) = ⊤ :=
  TypeCOddTwoOriginalOwnPairAmbient.matched_frattini D
    (selectedRadical D b psi) (selectedPart D b psi)

end Matching

section ReferenceQuotient

variable {P : Problem n F} (D : Definition41 P) (b : P.Block)
variable (reference psi : Definition35Brauer (P.blockProblem b))

/-- Arbitrary block reference, with its actual canonical quotient map. -/
abbrev referenceQuotientEquiv :=
  centerlessCentralCharacterQuotientMapEquiv (P.blockProblem b) P.center_eq_bot reference

/-- The OWN original selected quotient reduction is transported by the
accepted centreless construction; no independent reduction is supplied. -/
def quotientPacket : QuotientWeightBrauerSource (P.blockProblem b) reference
    (blockEquiv D b psi) :=
  centerlessQuotientWeightBrauerSource (P.blockProblem b) P.center_eq_bot
    reference (blockEquiv D b psi)

/-- Exact selected root binding on the normalizer quotient. This is a
computed transport, not an assertion about unrelated root records. -/
theorem quotientPacket_root :
    (quotientPacket D b reference psi).iota =
      (P.localReduction b (blockEquiv D b psi)).iota.alongMulEquiv
        (centerlessQuotientNormalizerEquiv (P.blockProblem b) P.center_eq_bot
          reference (blockEquiv D b psi)) := rfl

/-- The packet's own ordinary character descends through the canonical map. -/
theorem quotientPacket_ordinary (x : NormalizerQuotient (selectedPair D b psi).subgroup) :
    (quotientPacket D b reference psi).ordinary
      (quotientNormalizerMap (P.blockProblem b) reference (blockEquiv D b psi) x) =
        (selectedPair D b psi).localCharacter x :=
  (quotientPacket D b reference psi).ordinaryDescends x

/-- The reverse reduction equation refers to the EXACT stored input
selected reduction; it is not replaced by the original matched ambient root. -/
theorem quotientPacket_brauer :
    PrimeRegularClassFunction.pullback
      (quotientNormalizerMap (P.blockProblem b) reference (blockEquiv D b psi))
        (quotientPacket D b reference psi).brauer.1 =
      (P.localReduction b (blockEquiv D b psi)).brauer.1 :=
  (quotientPacket D b reference psi).brauerDescends

/-- The raw quotient weight consists of this same packet's own character. -/
def quotientPair : CharacterWeight 2 P.K
    (CentralCharacterQuotient (P.blockProblem b) reference) where
  prime := Nat.prime_two
  subgroup := quotientRadical (P.blockProblem b) reference (blockEquiv D b psi)
  radical := (quotientPacket D b reference psi).radical
  localCharacter := (quotientPacket D b reference psi).ordinary
  defectZero := (quotientPacket D b reference psi).defectZero

/-- Canonical normalizer coordinates prove this is the actual group-image
pair. Equality includes the local character, not merely the radical. -/
theorem quotientPair_eq_map :
    quotientPair D b reference psi =
      (selectedPair D b psi).mapGroupEquiv (referenceQuotientEquiv b reference) := by
  symm
  apply mapGroupEquiv_eq_of_normalizer_coordinates
    (selectedPair D b psi) (referenceQuotientEquiv b reference)
    (quotientPair D b reference psi) rfl
    (normalizerEquiv (referenceQuotientEquiv b reference) (selectedPair D b psi).subgroup)
  · intro x
    rfl
  · intro x
    exact quotientPacket_ordinary D b reference psi (QuotientGroup.mk x)

/-- The quotient class is the canonical image of the SAME original global
image. This proves injectivity without a new quotient matching assumption. -/
theorem quotientPair_class :
    letI := Fintype.ofFinite (CentralCharacterQuotient (P.blockProblem b) reference)
    weightClass (quotientPair D b reference psi) =
      conjugacyClassGroupEquiv (referenceQuotientEquiv b reference) (D.map.equiv psi.1) := by
  letI := Fintype.ofFinite (CentralCharacterQuotient (P.blockProblem b) reference)
  have h := congrArg (conjugacyClassGroupEquiv (referenceQuotientEquiv b reference))
    (selectedPair_class D b psi)
  change weightClass ((selectedPair D b psi).mapGroupEquiv
    (referenceQuotientEquiv b reference)) = _ at h
  exact (congrArg weightClass (quotientPair_eq_map D b reference psi)).trans h

theorem quotientPair_class_injective :
    letI := Fintype.ofFinite (CentralCharacterQuotient (P.blockProblem b) reference)
    Function.Injective (fun chi : Definition35Brauer (P.blockProblem b) =>
      weightClass (quotientPair D b reference chi)) := by
  letI := Fintype.ofFinite (CentralCharacterQuotient (P.blockProblem b) reference)
  intro chi eta h
  have hh := (quotientPair_class D b reference chi).symm.trans
    (h.trans (quotientPair_class D b reference eta))
  apply Subtype.ext
  exact D.map.equiv.injective
    ((conjugacyClassGroupEquiv (referenceQuotientEquiv b reference)).injective hh)

/-- The reference quotient to the OWN quotient used by the original
matched ambient group, with no quotient or root identification premise. -/
def referenceToOwn : CentralCharacterQuotient (P.blockProblem b) reference ≃*
    CentralCharacterQuotient (P.blockProblem (P.brauerBlock psi.1)) (P.ownBrauer psi.1) :=
  (referenceQuotientEquiv b reference).symm.trans
    (TypeCOddTwoOriginalOwnPairAmbient.quotientEquiv P psi.1)

theorem referenceToOwn_square (x : X n F) :
    referenceToOwn b reference psi
      (centralCharacterQuotientMap (P.blockProblem b) reference x) =
        centralCharacterQuotientMap (P.blockProblem (P.brauerBlock psi.1))
          (P.ownBrauer psi.1) x := by
  change TypeCOddTwoOriginalOwnPairAmbient.quotientEquiv P psi.1
    ((referenceQuotientEquiv b reference).symm (referenceQuotientEquiv b reference x)) = _
  exact (congrArg (TypeCOddTwoOriginalOwnPairAmbient.quotientEquiv P psi.1)
    ((referenceQuotientEquiv b reference).symm_apply_apply x)).trans
      (TypeCOddTwoOriginalOwnPairAmbient.quotientEquiv_apply P psi.1 x)

end ReferenceQuotient

end ModularRep.PaperProofs.TypeCOddTwoOriginalBlockMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
