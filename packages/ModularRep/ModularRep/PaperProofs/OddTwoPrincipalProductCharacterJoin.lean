import ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
import ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport

/-!
# The own principal character on the complete independent product

The actual An/FM induced-character enumeration is transported through the
block-monomial normalizer quotient from the same product geometry. Its
inverse picks the transported local character of the original weight.
K then proves equality of the whole raw pair, the intrinsic class and the
principal FM fibre. Compatible reduction of that own character gives the
actual normalizer block-induction endpoint through the shared support law.

No local-character comparison, candidate principal membership, induced
block equality or whole-weight bijection is a source field. The genuine
subgroup match, full normalizer realization and local wreath theorem are
explicit inputs. Complete FYZ six-case coverage and its exhaustive
case-(4) adapter are still needed to supply that match for every weight;
this file does not label that remaining source join as discharged.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin

open ModularRep.CharacterWeight
open ModularRep.NavarroLocalReductionInflationBlockCompatibility
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.OddTwoPrincipalProductNormalizer
open ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F K : Type u} [Field F] [Fintype F] [Field K] [CharZero K]

local instance spFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

/-- Actual ordinary-character transport under the prescribed quotient
equivalence. Both directions are pullbacks on character functions. -/
def defectZeroEquiv {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) : DZ K G ≃ DZ K H where
  toFun chi := ⟨OrdinaryIrreducibleCharacter.mapEquiv chi.1 e, chi.2.mapEquiv e⟩
  invFun chi := ⟨OrdinaryIrreducibleCharacter.mapEquiv chi.1 e.symm,
    chi.2.mapEquiv e.symm⟩
  left_inv chi := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    change chi.1 (e.symm (e x)) = chi.1 x
    rw [MulEquiv.symm_apply_apply]
  right_inv chi := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    change chi.1 (e (e.symm x)) = chi.1 x
    rw [MulEquiv.apply_symm_apply]

variable (P : ProductShape n F) (A : P.Geometry)
variable (N : AnProductNormalizerSource P A)
variable (E : ∀ i, BasicModel.LocalEnumeration (K := K) (P.basic i))

local instance basicQuotientFintype (i : Fin P.count) :
    Fintype (BasicQuotient P i) := Fintype.ofFinite _

abbrev Assignments := CoreAssignments (fun i => (P.basic i).colours) P.copies

variable (formula : CoreFormulaData (multiplicity := P.copies)
  (BasicQuotient P) (fun i => (E i).enumeration))
variable (source : AnFMCoreCharacterSource (BasicQuotient P)
  (fun i => (E i).enumeration) formula)

/-- The full local enumeration uses the actual induced-character formula
and the same block-monomial quotient equivalence. -/
def localEnumeration : Assignments P ≃
    LocalDefectZeroCharacters (K := K) A.subgroup :=
  source.enumeration.trans (defectZeroEquiv N.quotientEquiv)

@[simp] theorem localEnumeration_value (h : Assignments P)
    (q : NormalizerQuotient A.subgroup) :
    (localEnumeration P A N E formula source h).1 q =
      formula.characterFunction h (N.quotientEquiv.symm q) := rfl

/-- On each actual normalizer lift the character is the displayed An/FM
induced function at the corresponding basic quotient elements. -/
theorem localEnumeration_on_lift (h : Assignments P) (z : NormalizerWreaths P) :
    (localEnumeration P A N E formula source h).1
        (QuotientGroup.mk' (A.subgroup.subgroupOf
          (Subgroup.normalizer (A.subgroup : Set (Sp n F)))) (N.normalizerLift z)) =
      formula.characterFunction h (quotientWreathMap P z) := by
  rw [localEnumeration_value, N.inverse_quotient_lift]

section Principal

variable {k Block : Type u} [Field k] [CharP k 2] [IsAlgClosed k]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (w : D.PrincipalWeight) (g : Sp n F)
variable (hR : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
  (MulAut.conj g⁻¹)).subgroup = A.subgroup)

/-- The heights are computed from the selected weight's OWN transported
character by the inverse of the complete actual enumeration. -/
def selectedHeights : Assignments P :=
  matchingIndex (selectedCharacterWeight D.blockSource D.principalBlock w)
    (MulAut.conj g⁻¹) hR (localEnumeration P A N E formula source)

def selectedPair : CharacterWeight 2 K (Sp n F) :=
  selectedEnumeratedPair D w A.subgroup g hR (localEnumeration P A N E formula source)

theorem selectedPair_eq_twist :
    selectedPair P A N E formula source D w g hR =
      (selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
        (MulAut.conj g⁻¹) :=
  selectedEnumeratedPair_eq_twist D w A.subgroup g hR
    (localEnumeration P A N E formula source)

/-- This exposes the source induction formula for the same pair whose
principal class is proved below. A different local colour cannot be used.
-/
theorem selectedPair_character_on_lift (z : NormalizerWreaths P) :
    (selectedPair P A N E formula source D w g hR).localCharacter
        (QuotientGroup.mk' (A.subgroup.subgroupOf
          (Subgroup.normalizer (A.subgroup : Set (Sp n F)))) (N.normalizerLift z)) =
      formula.characterFunction (selectedHeights P A N E formula source D w g hR)
        (quotientWreathMap P z) :=
  localEnumeration_on_lift P A N E formula source
    (selectedHeights P A N E formula source D w g hR) z

def principalWeight : D.FengMallePrincipalWeight :=
  OddTwoPrincipalLocalEnumerationJoin.principalWeight D w A.subgroup g hR
    (localEnumeration P A N E formula source)

theorem principalWeight_eq :
    principalWeight P A N E formula source D w g hR = D.intrinsicWeightEquiv w :=
  OddTwoPrincipalLocalEnumerationJoin.principalWeight_eq D w A.subgroup g hR
    (localEnumeration P A N E formula source)

include hR in
/-- The complete independent-product bridge. The only matching premise is
the genuine subgroup equality; the selected heights, own character and
same principal FM weight are constructed and compared in K. -/
theorem exists_principalProductPair :
    ∃ h : Assignments P,
      (localEnumeration P A N E formula source h) =
        transportedLocal (selectedCharacterWeight D.blockSource D.principalBlock w)
          (MulAut.conj g⁻¹) hR ∧
      principalWeight P A N E formula source D w g hR = D.intrinsicWeightEquiv w := by
  exact ⟨selectedHeights P A N E formula source D w g hR,
    enumeration_matchingIndex _ _ hR (localEnumeration P A N E formula source),
    principalWeight_eq P A N E formula source D w g hR⟩

open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport

variable (support : Source D.iota D.blockSource.operations)

include support in
/-- Actual block induction from a compatible normalizer reduction of this
same induced ordinary character, using the shared block support source. -/
theorem selectedPair_actualBlockInducesTo
    (iotaN : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer
        ((selectedPair P A N E formula source D w g hR).subgroup : Set (Sp n F))))
    (phiN : IBr iotaN)
    (hroots : RootCompatibleAlong D.iota iotaN
      (Subgroup.normalizer
        ((selectedPair P A N E formula source D w g hR).subgroup : Set (Sp n F))).subtype)
    (hReduction : NormalizerInflatedReduction
      (selectedPair P A N E formula source D w g hR).subgroup
      (selectedPair P A N E formula source D w g hR).localCharacter iotaN phiN) :
    let V := selectedPair P A N E formula source D w g hR
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData V.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (normalizerBrauerBlock O V.subgroup iotaN phiN) D.principalBlock :=
  enumeratedPair_actualBlockInducesTo D support w A.subgroup g hR
    (localEnumeration P A N E formula source) iotaN phiN hroots hReduction

end Principal

end ModularRep.PaperProofs.OddTwoPrincipalProductCharacterJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
