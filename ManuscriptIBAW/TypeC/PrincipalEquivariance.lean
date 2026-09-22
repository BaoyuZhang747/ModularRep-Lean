import ManuscriptIBAW.Library.EquivariantBijections
import ManuscriptIBAW.TypeC.PrincipalParameterActions
import ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness

/-!
# The principal equivariant bijection from the principal parameters

The published numerical character counts are compared with the weight
parameters. Inner automorphisms fix both character and weight classes. Field
invariance and the diagonal fixed counts then give an equivariant bijection
by the elementary classification of an involution's orbits.

The source record about automorphisms contains only group structure. The
character and local wreath calculations are separate hypotheses with their
own source statements. No bijection between Brauer characters and weights is
assumed.
-/

noncomputable section

namespace ManuscriptIBAW.TypeC

open ModularRep ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoFYZPrincipalFullCarrierJoin
open ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation (spFieldAut)
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness

universe u

variable {n : ℕ} {F k K Block Index : Type u}
    [Field F] [Fintype F] [Field k] [CharP k 2] [IsAlgClosed k]
    [Field K] [CharZero K]
    [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance symplecticFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

/-- The inner and entrywise field automorphisms. -/
def principalTrivialGenerators : Set (MulAut (Sp n F)) :=
  Set.range (MulAut.conj : Sp n F → MulAut (Sp n F)) ∪
    Set.range (spFieldAut (n := n) (F := F))

/-- The diagonal automorphism uses the inverse because the specified left action
on characters represents right transport by the inverse automorphism. -/
def principalDiagonal (O : LiteralDiagonalFieldRealisation n F) : MulAut (Sp n F) :=
  O.outer.diagonal.unop⁻¹

/-- The structure of the automorphism group of the symplectic group over a field
of odd order. The chosen diagonal automorphism comes from the specified
nonsquare similitude in `O`. These assumptions concern groups alone. -/
structure PrincipalAutomorphismSource (O : LiteralDiagonalFieldRealisation n F) : Prop where
  rank_ge_two : 2 ≤ n
  odd_field : Odd (Nat.card F)
  generated : Subgroup.closure
    (principalTrivialGenerators (n := n) (F := F) ∪ {principalDiagonal O}) = ⊤
  diagonal_square_inner : ∃ g : Sp n F,
    principalDiagonal O * principalDiagonal O = MulAut.conj g

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

local instance brauerAction : MulAction (MulAut (Sp n F)) D.PrincipalBrauer :=
  upstreamBrauerAction D
local instance weightAction : MulAction (MulAut (Sp n F)) D.PrincipalWeight :=
  upstreamWeightAction D

theorem principal_brauer_inner_fixed (g : Sp n F) (chi : D.PrincipalBrauer) :
    MulAut.conj g • chi = chi := by
  apply Subtype.ext
  change MulOpposite.op ((MulAut.conj g)⁻¹) • chi.1 = chi.1
  rw [← map_inv]
  exact inner_fixes_ibr D.iota g chi.1

theorem principal_weight_inner_fixed (g : Sp n F) (w : D.PrincipalWeight) :
    MulAut.conj g • w = w := by
  apply Subtype.ext
  change MulOpposite.op ((MulAut.conj g)⁻¹) • w.1 = w.1
  rw [← map_inv]
  exact inner_fixes_weightClass g w.1

theorem principal_brauer_diagonal_involutive
    (O : LiteralDiagonalFieldRealisation n F) (structureSource : PrincipalAutomorphismSource O) :
    Function.Involutive (fun chi : D.PrincipalBrauer => principalDiagonal O • chi) := by
  intro chi
  dsimp only
  obtain ⟨g, hg⟩ := structureSource.diagonal_square_inner
  rw [← mul_smul, hg, principal_brauer_inner_fixed]

variable (fieldOdd : Odd (Nat.card F))
    (core : DefectZeroCoreSource (n := n) (F := F) (K := K))
    (criterion : FYZPrincipalCriterion D)
    (atlas : Index → PrincipalProductData (n := n) (F := F) (K := K))
    (classification : PrincipalProductClassification atlas)
    (lemma23 : FYZLemma23IntrinsicCertificate D)
    (factors : PrincipalFactorSelection D)
    (coordinates : FMProductCoordinates atlas)
    (multiplicities : coordinates.MultiplicityClassification)

include criterion classification lemma23 factors in
/-- The principal correspondence is equivariant under automorphisms by the
parameter construction, the local action formulas and the published
numerical counts. -/
theorem principal_equivariant_bijection
    (O : LiteralDiagonalFieldRealisation n F)
    (structureSource : PrincipalAutomorphismSource O)
    (brauerFields : FengMalleCorollary43aSource D)
    (weightFields : ∀ sigma : F ≃+* F,
      FMParameterActionSource fieldOdd core atlas coordinates multiplicities
        (spFieldAut (n := n) sigma) id)
    (diagonalAction : FMParameterActionSource fieldOdd core atlas coordinates multiplicities
      (principalDiagonal O) (fmParameterDiagonal n))
    (counts : FMPrincipalCountSource D (principalDiagonal O)) :
    ∃ e : D.PrincipalBrauer ≃ D.PrincipalWeight,
      ∀ (a : MulAut (Sp n F)) (chi : D.PrincipalBrauer), e (a • chi) = a • e chi := by
  let _ : Finite D.PrincipalWeight := principalWeight_finite D fieldOdd core criterion atlas
    classification lemma23 factors coordinates multiplicities
  let _ : Fintype D.PrincipalWeight := Fintype.ofFinite _
  let _ : Fintype D.PrincipalBrauer := Fintype.ofFinite _
  apply equivariant_bijection_of_involution_counts principalTrivialGenerators
    (principalDiagonal O) structureSource.generated
  · intro a ha chi
    rcases ha with ⟨g, rfl⟩ | ⟨sigma, rfl⟩
    · exact principal_brauer_inner_fixed D g chi
    · exact brauerFields.field_fixed sigma chi
  · intro a ha w
    rcases ha with ⟨g, rfl⟩ | ⟨sigma, rfl⟩
    · exact principal_weight_inner_fixed D g w
    · exact principalWeight_fixed_of_trivial_parameter_action D fieldOdd core criterion atlas
        classification lemma23 factors coordinates multiplicities (weightFields sigma) w
  · exact principal_brauer_diagonal_involutive D O structureSource
  · exact principalWeight_action_involutive D fieldOdd core criterion atlas classification
      lemma23 factors coordinates multiplicities diagonalAction (fmParameterDiagonal_involutive n)
  · simpa only [Nat.card_eq_fintype_card] using principal_total_counts D fieldOdd core criterion
      atlas classification lemma23 factors coordinates multiplicities (principalDiagonal O) counts
  · exact principal_diagonal_fixed_counts D fieldOdd core criterion atlas classification
      lemma23 factors coordinates multiplicities (principalDiagonal O) counts diagonalAction

/-- Express the constructed correspondence in the form required by central
descent. Feng–Malle's final principal bijection is not an additional
assumption. -/
def principalCorrespondence
    (O : LiteralDiagonalFieldRealisation n F)
    (structureSource : PrincipalAutomorphismSource O)
    (brauerFields : FengMalleCorollary43aSource D)
    (weightFields : ∀ sigma : F ≃+* F,
      FMParameterActionSource fieldOdd core atlas coordinates multiplicities
        (spFieldAut (n := n) sigma) id)
    (diagonalAction : FMParameterActionSource fieldOdd core atlas coordinates multiplicities
      (principalDiagonal O) (fmParameterDiagonal n))
    (counts : FMPrincipalCountSource D (principalDiagonal O)) :
    D.FengMalleTheorem62LiteralCertificate where
  rank_ge_two := structureSource.rank_ge_two
  odd_field := fieldOdd
  omega := Classical.choose (principal_equivariant_bijection D fieldOdd core criterion atlas
    classification lemma23 factors coordinates multiplicities O structureSource brauerFields
    weightFields diagonalAction counts)
  equivariant := Classical.choose_spec (principal_equivariant_bijection D fieldOdd core criterion atlas
    classification lemma23 factors coordinates multiplicities O structureSource brauerFields
    weightFields diagonalAction counts)

end ManuscriptIBAW.TypeC

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
