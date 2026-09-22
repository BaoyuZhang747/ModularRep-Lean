import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation
import ModularRep.PaperProofs.TypeBQ3PrincipalWeightInflation
import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import Mathlib.Logic.Equiv.Sum

/-!
# Radical parts and ordinary local characters of the same principal matching

The radical projection partitions one specified principal Brauer fibre. The
existing representative weight-fibre equivalence decodes its same matching
into ordinary defect-zero characters with the actual induced-block guard.
Automorphism covariance follows from the matching and its exact class graph.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalRadicalDecoding

open ModularRep CharacterWeight
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation

variable {k K Y : Type} [Field k] [Field K] [CharZero K]
  [Group Y] [Finite Y] [CharP k 2] [IsAlgClosed k]

local instance groupFintype : Fintype Y := Fintype.ofFinite Y

variable {rootX : PrimeRegularRootEmbedding 2 k K Y}
  {SX : CoverWeightSource (k := k) (K := K) Y}
  {bX : LiteralPrimitiveBlock k Y}
  (omega : BrauerFibre rootX bX ≃ CoverWeight SX bX)

/-- The part is the literal radical conjugacy class of the same weight. -/
def part (phi : BrauerFibre rootX bX) :
    RadicalConjugacyClass (p := 2) (G := Y) :=
  radicalClass (omega phi).val

def partitionEquiv : BrauerFibre rootX bX ≃
    Σ c : RadicalConjugacyClass (p := 2) (G := Y),
      {phi : BrauerFibre rootX bX // part omega phi = c} :=
  (Equiv.sigmaFiberEquiv (part omega)).symm

theorem partitionEquiv_part (phi : BrauerFibre rootX bX) :
    (partitionEquiv omega phi).1 = part omega phi := rfl

theorem partitionEquiv_character (phi : BrauerFibre rootX bX) :
    (partitionEquiv omega phi).2.val = phi := rfl

abbrev BrauerAtRadical (Q : RadicalSubgroup (p := 2) (G := Y)) :=
  {phi : BrauerFibre rootX bX // part omega phi =
    (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := Y))}

theorem exists_radical (phi : BrauerFibre rootX bX) :
    ∃ Q : RadicalSubgroup (p := 2) (G := Y),
      part omega phi = (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := Y)) := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (part omega phi)
  exact ⟨Q, hQ.symm⟩

def brauerEquivWeightBlockRadicalFibre
    (Q : RadicalSubgroup (p := 2) (G := Y)) :
    BrauerAtRadical omega Q ≃ WeightBlockRadicalFibre SX Q bX where
  toFun phi := ⟨(omega phi.val).val, by exact (omega phi.val).property, phi.property⟩
  invFun w := by
    let weight : CoverWeight SX bX := ⟨w.val, by exact w.property.1⟩
    refine ⟨omega.symm weight, ?_⟩
    exact (congrArg (fun z : CoverWeight SX bX => radicalClass z.val)
      (omega.apply_symm_apply weight)).trans w.property.2
  left_inv phi := Subtype.ext (omega.symm_apply_apply phi.val)
  right_inv w := by
    apply Subtype.ext
    let weight : CoverWeight SX bX := ⟨w.val, by exact w.property.1⟩
    change (omega (omega.symm weight)).val = w.val
    exact congrArg (fun z : CoverWeight SX bX => z.val) (omega.apply_symm_apply weight)

/-- The target consists of actual local ordinary characters in this block. -/
def localMap (Q : RadicalSubgroup (p := 2) (G := Y)) :
    BrauerAtRadical omega Q ≃ RepresentativeDZ Nat.prime_two SX Q bX :=
  (brauerEquivWeightBlockRadicalFibre omega Q).trans
    (representativeDZEquivWeightBlockRadicalFibre Nat.prime_two SX Q bX).symm

theorem localMap_class (Q : RadicalSubgroup (p := 2) (G := Y))
    (phi : BrauerAtRadical omega Q) :
    (Quotient.mk'' (Quotient.mk''
      (characterWeightAt Nat.prime_two Q (localMap omega Q phi).val)) :
        CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y)) =
      (omega phi.val).val := by
  have h := congrArg Subtype.val
    ((representativeDZEquivWeightBlockRadicalFibre Nat.prime_two SX Q bX).apply_symm_apply
      (brauerEquivWeightBlockRadicalFibre omega Q phi))
  change (localDefectZeroEquivWeightRadicalFibre Nat.prime_two Q
    (localMap omega Q phi).val).val = (omega phi.val).val at h
  rw [localDefectZeroEquivWeightRadicalFibre_apply_val] at h
  exact h

theorem localMap_blockInducesTo (Q : RadicalSubgroup (p := 2) (G := Y))
    (phi : BrauerAtRadical omega Q) :
    let theta := (localMap omega Q phi).val
    let O := SX.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (Q.1 : Set Y))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2)) bX := by
  let W := characterWeightAt Nat.prime_two Q (localMap omega Q phi).val
  let O := SX.operations
  let localData := O.inflatedNormalizerBlockData Q.1
  letI := O.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  have hinduced : O.induceToAmbient W = bX := (localMap omega Q phi).property
  change BlockInducesTo (Subgroup.normalizer (Q.1 : Set Y))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 W.localCharacter W.defectZero)) bX
  rw [← hinduced]
  exact inducedBlock_spec (Subgroup.normalizer (Q.1 : Set Y))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 W.localCharacter W.defectZero))
    (O.blockInductionDefined W)

def localCharacterTwist (Q : RadicalSubgroup (p := 2) (G := Y))
    (alpha : (MulAut Y)ᵐᵒᵖ) (theta : LocalDefectZeroCharacter (K := K) Q) :
    LocalDefectZeroCharacter (K := K) (Q.rightTwist alpha.unop) :=
  ⟨((characterWeightAt Nat.prime_two Q theta).rightTwist alpha.unop).localCharacter,
    ((characterWeightAt Nat.prime_two Q theta).rightTwist alpha.unop).defectZero⟩

variable (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
  (hbX : IsPrincipal bX)
  (equivariant : letI := SX.operations.ambientBlockData.fintypeBlock
    ∀ (alpha : (MulAut Y)ᵐᵒᵖ) (phi : BrauerFibre rootX bX),
    omega (TypeBQ3PrincipalBrauerInflation.principalStep rootX
      (coverDecomposition SX literalX) bX hbX alpha phi) =
    coverWeightStep SX literalX bX hbX alpha (omega phi))

include equivariant in
theorem part_equivariant (alpha : (MulAut Y)ᵐᵒᵖ) (phi : BrauerFibre rootX bX) :
    letI := SX.operations.ambientBlockData.fintypeBlock
    part omega (TypeBQ3PrincipalBrauerInflation.principalStep rootX
      (coverDecomposition SX literalX) bX hbX alpha phi) = alpha • part omega phi := by
  letI := SX.operations.ambientBlockData.fintypeBlock
  unfold part
  rw [equivariant]
  exact radicalClass_equivariant alpha (omega phi).val

include equivariant in
def brauerTransport (alpha : (MulAut Y)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := Y)) (phi : BrauerAtRadical omega Q) :
    BrauerAtRadical omega (Q.rightTwist alpha.unop) := by
  letI := SX.operations.ambientBlockData.fintypeBlock
  refine ⟨TypeBQ3PrincipalBrauerInflation.principalStep rootX
    (coverDecomposition SX literalX) bX hbX alpha phi.val, ?_⟩
  rw [part_equivariant omega literalX hbX equivariant, phi.property]
  rfl

include equivariant in
theorem localMap_covariance (alpha : (MulAut Y)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := Y)) (phi : BrauerAtRadical omega Q) :
    (localMap omega (Q.rightTwist alpha.unop)
      (brauerTransport omega literalX hbX equivariant alpha Q phi)).val =
    localCharacterTwist Q alpha (localMap omega Q phi).val := by
  apply (localDefectZeroEquivWeightRadicalFibre Nat.prime_two
    (Q.rightTwist alpha.unop)).injective
  apply Subtype.ext
  rw [localDefectZeroEquivWeightRadicalFibre_apply_val,
    localDefectZeroEquivWeightRadicalFibre_apply_val]
  change (Quotient.mk'' (Quotient.mk''
      (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
        (localMap omega (Q.rightTwist alpha.unop)
          (brauerTransport omega literalX hbX equivariant alpha Q phi)).val)) :
        CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y)) =
    alpha • (Quotient.mk'' (Quotient.mk''
      (characterWeightAt Nat.prime_two Q (localMap omega Q phi).val)) :
        CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y))
  rw [localMap_class, localMap_class]
  exact congrArg Subtype.val (equivariant alpha phi.val)

include equivariant in
theorem localMap_raw_transport (alpha : (MulAut Y)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := Y)) (phi : BrauerAtRadical omega Q) :
    CharacterWeight.Isomorphic
      ((characterWeightAt Nat.prime_two Q (localMap omega Q phi).val).rightTwist alpha.unop)
      (characterWeightAt Nat.prime_two (Q.rightTwist alpha.unop)
        (localMap omega (Q.rightTwist alpha.unop)
          (brauerTransport omega literalX hbX equivariant alpha Q phi)).val) := by
  rw [localMap_covariance omega literalX hbX equivariant]
  exact ⟨rfl, rfl⟩

end ModularRep.PaperProofs.TypeBQ3PrincipalRadicalDecoding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
