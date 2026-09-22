import ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

/-!
# Own characters through actual automorphism coordinates

An equality V = W transported by beta determines the normalizer and
normalizer-quotient equivalences. Their underlying maps are beta, and
the transported ordinary character is the OWN character of V.

Two own reduction equations then give the Brauer value pullback identity.
This is a function-value conclusion only: compatibility of independently
chosen roots is separate and is neither assumed nor inferred here.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple
open ModularRep.PaperProofs.OddTwoSelectedWeightAutomorphismCoordinates

universe u

section OrdinaryValues

variable {p : ℕ} {K H : Type u}
variable [Field K] [CharZero K] [Group H] [Fintype H]
variable (W V : CharacterWeight p K H) (beta : MulAut H)
variable (hpair : W.rightTwist beta⁻¹ = V)

/-- The normalizer restriction of the SAME actual beta, computed from the
whole raw-pair equality. No independent normalizer equivalence is supplied. -/
def ownNormalizerEquiv :
    Subgroup.normalizer (W.subgroup : Set H) ≃*
      Subgroup.normalizer (V.subgroup : Set H) := by
  subst V
  exact (rightNormalizerEquiv beta⁻¹ W.subgroup).symm

@[simp] theorem ownNormalizerEquiv_coe
    (x : Subgroup.normalizer (W.subgroup : Set H)) :
    (ownNormalizerEquiv W V beta hpair x : H) = beta x := by
  subst V
  rfl

/-- The induced OWN local quotient map, using the very quotient transport
in CharacterWeight.rightTwist. -/
def ownNormalizerQuotientEquiv :
    NormalizerQuotient W.subgroup ≃* NormalizerQuotient V.subgroup := by
  subst V
  exact (rightNormalizerQuotientEquiv beta⁻¹ W.subgroup).symm

/-- The two computed normalizer maps commute on actual quotient generators. -/
theorem ownNormalizerQuotientEquiv_mk
    (x : Subgroup.normalizer (W.subgroup : Set H)) :
    ownNormalizerQuotientEquiv W V beta hpair (QuotientGroup.mk x) =
      QuotientGroup.mk (ownNormalizerEquiv W V beta hpair x) := by
  subst V
  change (rightNormalizerQuotientEquiv beta⁻¹ W.subgroup).symm
      (QuotientGroup.mk x) =
    QuotientGroup.mk ((rightNormalizerEquiv beta⁻¹ W.subgroup).symm x)
  apply (rightNormalizerQuotientEquiv beta⁻¹ W.subgroup).injective
  rw [MulEquiv.apply_symm_apply, rightNormalizerQuotientEquiv_mk,
    MulEquiv.apply_symm_apply]

/-- The target local character is the transported OWN source character. -/
theorem ownOrdinary_character_values (x : NormalizerQuotient W.subgroup) :
    V.localCharacter (ownNormalizerQuotientEquiv W V beta hpair x) =
      W.localCharacter x := by
  subst V
  change W.localCharacter
      (rightNormalizerQuotientEquiv beta⁻¹ W.subgroup
        ((rightNormalizerQuotientEquiv beta⁻¹ W.subgroup).symm x)) =
    W.localCharacter x
  rw [MulEquiv.apply_symm_apply]

/-- The same ordinary value equation on lifts from the ACTUAL normalizer. -/
theorem ownOrdinary_normalizer_values
    (x : Subgroup.normalizer (W.subgroup : Set H)) :
    V.localCharacter (QuotientGroup.mk (ownNormalizerEquiv W V beta hpair x)) =
      W.localCharacter (QuotientGroup.mk x) := by
  rw [← ownNormalizerQuotientEquiv_mk]
  exact ownOrdinary_character_values W V beta hpair (QuotientGroup.mk x)

end OrdinaryValues

section ReductionValues

variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable (W V : CharacterWeight p K H) (beta : MulAut H)
variable (hpair : W.rightTwist beta⁻¹ = V)
variable (R : OwnNormalizerReduction (k := k) W)
variable (R' : OwnNormalizerReduction (k := k) V)

/-- The two literal own reductions give a function-value pullback identity.
This does NOT assert compatibility of their independently chosen roots. -/
theorem ownBrauer_character_values
    (x : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set H)) p) :
    R.brauer.1 x = R'.brauer.1
      (PrimeRegularElement.map (ownNormalizerEquiv W V beta hpair).toMonoidHom x) := by
  calc
    R.brauer.1 x = W.localCharacter (QuotientGroup.mk x.1) :=
      (R.own_reduction x).symm
    _ = V.localCharacter
        (QuotientGroup.mk (ownNormalizerEquiv W V beta hpair x.1)) :=
      (ownOrdinary_normalizer_values W V beta hpair x.1).symm
    _ = R'.brauer.1
        (PrimeRegularElement.map (ownNormalizerEquiv W V beta hpair).toMonoidHom x) :=
      R'.own_reduction
        (PrimeRegularElement.map (ownNormalizerEquiv W V beta hpair).toMonoidHom x)

end ReductionValues

section GlobalValues

variable {p : ℕ} {k K H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable (iota : PrimeRegularRootEmbedding p k K H)

/-- On the actual base map beta=conj(g)*a, the translated global character
pulls back to the original character. Inner invariance is used on functions. -/
theorem globalBrauer_coordinate_values (g : H) (a : MulAut H) (psi : IBr iota)
    (x : PrimeRegularElement (G := H) p) :
    (MulOpposite.op a⁻¹ • psi).1
        (PrimeRegularElement.map (coordinateAutomorphism g a).toMonoidHom x) =
      psi.1 x := by
  change psi.1 (PrimeRegularElement.map a.symm.toMonoidHom
    (PrimeRegularElement.map (coordinateAutomorphism g a).toMonoidHom x)) = psi.1 x
  have hx : PrimeRegularElement.map a.symm.toMonoidHom
      (PrimeRegularElement.map (coordinateAutomorphism g a).toMonoidHom x) =
      ⟨a.symm g * x.1 * (a.symm g)⁻¹, x.2.conj (a.symm g)⟩ := by
    apply Subtype.ext
    simp [coordinateAutomorphism, MulAut.conj_apply]
  rw [hx]
  exact psi.1.map_conj (a.symm g) x

end GlobalValues

end ModularRep.PaperProofs.OddTwoOwnCharacterAutomorphismTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
