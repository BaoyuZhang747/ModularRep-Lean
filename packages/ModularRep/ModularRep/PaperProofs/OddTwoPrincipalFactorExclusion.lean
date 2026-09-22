import ModularRep.PaperProofs.OddTwoFYZSourceAdapter
import ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

/-!
# The corrected FYZ factor in the intrinsic principal fibre

The reflection calculation is already checked in `OddTwoFYZSourceAdapter`.
Here its ambient model is identified with the actual matrix symplectic group
and its subgroup with the subgroup of the same selected intrinsic weight.
The necessary Sylow-centre clause of FYZ Lemma 2.3 is stated on that weight.
Consequently no such weight admits the corrected equation-(3.35) realization.

K: transport of the constructed reflection and the resulting exclusion.
E1/U: the coordinate equivalence and subgroup identification supplied by
the source decomposition. E2: Lemma 2.3 on the fixed principal block fibre.
This does not assert that every case-(4) occurrence has been realized, nor
classify the two surviving families or identify their local characters.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoAmbientRealisation
open ModularRep.PaperProofs.OddTwoCorrectedFactorAdapter
open ModularRep.PaperProofs.OddTwoFYZSourceAdapter
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoProposition33Relative
open ModularRep.PaperProofs.OddTwoWreathReflection
open ModularRep.PaperProofs.OddTwoSourceWreathAction
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {rank : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance spFintype : Fintype (Sp rank F) := Fintype.ofFinite _

local instance wreathPointsFintype (cs : List ℕ) :
    Fintype (SourceWreathPoints cs) := Fintype.ofFinite _

local instance wreathPointsDecidableEq (cs : List ℕ) :
    DecidableEq (SourceWreathPoints cs) := Classical.decEq _

/-- Derive the characteristic restriction from the cardinality of the
actual field, rather than a detached parameter called its order. -/
theorem two_ne_zero_of_odd_card (fieldOdd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  apply Ring.two_ne_zero
  intro hchar
  have heven := FiniteField.even_card_of_char_two hchar
  have hodd : Fintype.card F % 2 = 1 :=
    Nat.odd_iff.mp (by simpa only [Nat.card_eq_fintype_card] using fieldOdd)
  omega

/-- Equation (3.35) and the orthogonal product decomposition, bound to an
actual raw weight pair. The remaining dimension, wreath list, multiplicity,
and coordinate map may vary with the occurrence.

The coordinate equivalence has the literal matrix group as target; its
subgroup equation concerns `W.subgroup`, not a second set of weights.
Authenticating the source decomposition supplies these data. No reflection,
Sylow failure, principal exclusion or local-character conclusion is a field.
-/
structure CorrectedFactorRealisation
    (W : CharacterWeight 2 K (Sp rank F)) where
  multiplicityOffset : ℕ
  wreathList : List ℕ
  diagonalCoefficients : Fin (multiplicityOffset + 2) → F
  remainingDimension : ℕ
  remainingGram : Matrix (Fin remainingDimension) (Fin remainingDimension) F
  decomposition : FYZEquation335Decomposition multiplicityOffset wreathList
    diagonalCoefficients remainingGram
  coordinates : FormIsometryGroup
    (correctedFullGram multiplicityOffset wreathList diagonalCoefficients
      remainingGram) ≃* Sp rank F
  subgroup_eq : W.subgroup = decomposition.subgroup.map coordinates.toMonoidHom

/-- The existing equation-(3.35) reflection, transported to the actual
symplectic group by the same coordinate identification as the subgroup. -/
def CorrectedFactorRealisation.reflection
    {W : CharacterWeight 2 K (Sp rank F)} (C : CorrectedFactorRealisation W) :
    Sp rank F :=
  C.coordinates ((MulAut.conj C.decomposition.classificationConjugator)
    (canonicalCorrectedFullReflection C.multiplicityOffset C.wreathList
      C.diagonalCoefficients C.remainingGram))

theorem CorrectedFactorRealisation.reflection_spec
    {W : CharacterWeight 2 K (Sp rank F)} (C : CorrectedFactorRealisation W)
    (fieldOdd : Odd (Nat.card F)) :
    C.reflection ^ 2 = 1 ∧
      C.reflection ∈ Subgroup.centralizer (W.subgroup : Set (Sp rank F)) ∧
      C.reflection ∉ W.subgroup := by
  have hmodel := FYZCorrectedSourceModel.reflection_involution_centralises_outside
    (two_ne_zero_of_odd_card fieldOdd) C.decomposition.toCorrectedSourceModel
  have hmapped := map_involution_centralises_outside_of_injective
    C.coordinates.toMonoidHom C.coordinates.injective C.decomposition.subgroup
    hmodel.1 hmodel.2.1 hmodel.2.2
  simpa only [CorrectedFactorRealisation.reflection,
    FYZEquation335Decomposition.toCorrectedSourceModel, ← C.subgroup_eq,
    MulEquiv.coe_toMonoidHom] using hmapped

variable [MulAction (MulAut (Sp rank F))ᵐᵒᵖ Block]

variable (D : PrincipalCharacterData (n := rank) (F := F) (k := k) (K := K)
  (Block := Block))

/-- The necessary direction of FYZ Lemma 2.3, p. 6, on the selected actual
weight in the intrinsic principal block fibre. Its proof/source instance is
external E2. The literal centre embedding is retained from the source.
There is no independently chosen predicate meaning "principal weight". -/
structure FYZLemma23IntrinsicCertificate : Prop where
  centre_is_sylow : ∀ w : D.PrincipalWeight,
    let R := (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup
    ∃ P : Sylow 2 (Subgroup.centralizer (R : Set (Sp rank F))),
      (P : Subgroup (Subgroup.centralizer (R : Set (Sp rank F)))) =
        sourceCentreInCentralizer R

/-- An actual principal weight cannot contain the corrected factor with the
specified decomposition: the reflection lies outside its centre, whereas
Lemma 2.3 makes that same centre Sylow in its actual centralizer. -/
theorem intrinsicPrincipal_correctedFactor_isEmpty
    (fieldOdd : Odd (Nat.card F)) (Lemma23 : FYZLemma23IntrinsicCertificate D)
    (w : D.PrincipalWeight) :
    IsEmpty (CorrectedFactorRealisation
      (selectedCharacterWeight D.blockSource D.principalBlock w)) := by
  constructor
  intro C
  let R := (selectedCharacterWeight D.blockSource D.principalBlock w).subgroup
  have ht := C.reflection_spec fieldOdd
  let t : Subgroup.centralizer (R : Set (Sp rank F)) := ⟨C.reflection, ht.2.1⟩
  obtain ⟨P, hP⟩ := Lemma23.centre_is_sylow w
  have hcentre : (P : Subgroup (Subgroup.centralizer (R : Set (Sp rank F)))) =
      centreInCentralizer R :=
    hP.trans (sourceCentreInCentralizer_eq_centreInCentralizer R)
  have hcentral : t ∈ Subgroup.centralizer
      (P : Set (Subgroup.centralizer (R : Set (Sp rank F)))) := by
    change t ∈ Subgroup.centralizer
      ((P : Subgroup (Subgroup.centralizer (R : Set (Sp rank F)))).carrier)
    rw [hcentre, Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact ht.2.1 z.1 (show z.1 ∈ R from hz)
  have houtside : t ∉ (P : Subgroup
      (Subgroup.centralizer (R : Set (Sp rank F)))) := by
    rw [hcentre]
    exact ht.2.2
  have hsq : t ^ 2 = 1 := Subtype.ext ht.1
  exact false_of_centralising_involution_outside_sylow
    P hsq hcentral houtside

end ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
