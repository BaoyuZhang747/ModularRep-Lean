import ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness

/-!
# Local defect-zero uniqueness under the actual automorphism transport

The normalizer-quotient equivalence used by `CharacterWeight.rightTwist`
transports the entire set of ordinary defect-zero characters bijectively.
Consequently one source uniqueness statement also gives uniqueness at its
automorphism companion. The right-action convention sends R to
`R.comap alpha.toMonoidHom`, exactly as in the existing raw weight action.

The equivalence and its inverse are constructed from the actual quotient
maps and function-valued ordinary-character transport. No independent
character equivalence or uniqueness assertion at the target is an input.
Authenticating the original An uniqueness statement and its source subgroup
remains E2/E1; this module only transports that statement and does not assert
uniqueness in the three-character exceptional case.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoLocalUniquenessTransport

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness

universe u

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

/-- The local character transport is precisely the one in the existing raw
weight twist. Its inverse is transport back along the same quotient map. -/
def localDefectZeroRightTwistEquiv (R : Subgroup G) (alpha : MulAut G) :
    LocalDefectZeroCharacters (K := K) R ≃
      LocalDefectZeroCharacters (K := K) (R.comap alpha.toMonoidHom) where
  toFun chi :=
    ⟨OrdinaryIrreducibleCharacter.mapEquiv chi.1
        (rightNormalizerQuotientEquiv alpha R).symm,
      chi.2.mapEquiv (rightNormalizerQuotientEquiv alpha R).symm⟩
  invFun chi :=
    ⟨OrdinaryIrreducibleCharacter.mapEquiv chi.1
        (rightNormalizerQuotientEquiv alpha R),
      chi.2.mapEquiv (rightNormalizerQuotientEquiv alpha R)⟩
  left_inv chi := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    change chi.1 ((rightNormalizerQuotientEquiv alpha R)
      ((rightNormalizerQuotientEquiv alpha R).symm x)) = chi.1 x
    rw [MulEquiv.apply_symm_apply]
  right_inv chi := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    change chi.1 ((rightNormalizerQuotientEquiv alpha R).symm
      ((rightNormalizerQuotientEquiv alpha R) x)) = chi.1 x
    rw [MulEquiv.symm_apply_apply]

/-- Uniqueness at R implies uniqueness at its actual right automorphism
image; the latter is derived using the inverse local character transport. -/
theorem localDefectZero_subsingleton_comap
    (R : Subgroup G) (alpha : MulAut G)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) R)) :
    Subsingleton
      (LocalDefectZeroCharacters (K := K) (R.comap alpha.toMonoidHom)) := by
  letI := unique
  constructor
  intro chi psi
  apply (localDefectZeroRightTwistEquiv (K := K) R alpha).symm.injective
  exact Subsingleton.elim _ _

/-- The local equivalence maps the selected raw pair's character to exactly
the selected character of its existing `rightTwist`, with no new choice. -/
theorem localDefectZeroRightTwistEquiv_selected
    (V : CharacterWeight 2 K G) (alpha : MulAut G) :
    localDefectZeroRightTwistEquiv (K := K) V.subgroup alpha
        ⟨V.localCharacter, V.defectZero⟩ =
      ⟨(V.rightTwist alpha).localCharacter, (V.rightTwist alpha).defectZero⟩ := rfl

/-- The exact raw-pair specialization needed for an automorphism companion
of an authenticated quaternion/basic model. -/
theorem localDefectZero_subsingleton_rightTwist
    (V : CharacterWeight 2 K G) (alpha : MulAut G)
    (unique : Subsingleton (LocalDefectZeroCharacters (K := K) V.subgroup)) :
    Subsingleton (LocalDefectZeroCharacters (K := K) (V.rightTwist alpha).subgroup) :=
  localDefectZero_subsingleton_comap V.subgroup alpha unique

end ModularRep.PaperProofs.OddTwoLocalUniquenessTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
