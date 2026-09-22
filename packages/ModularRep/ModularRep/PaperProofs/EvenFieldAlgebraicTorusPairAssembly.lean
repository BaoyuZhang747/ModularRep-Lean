import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

/-!
# Construction of separately fixed algebraic-torus pairs

This file supplies the component-construction step needed in the generic-weight
half of manuscript Lemma 3.6.  It does not assume that a whole local pair is
fixed.  Instead, it assumes separately that the algebraic-torus label is
fixed by `tau` and that its irreducible finite-normaliser character is fixed
under the induced automorphism of that normaliser.  Lean then derives
fixedness of the dependent pair in the manuscript's right-action convention.
-/

namespace ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair

universe u

variable {k H A : Type u}
    [Field k] [Group H] [MulAction (MulAut H) A]

/-- If `tau` fixes an algebraic-torus label, it induces an automorphism of
the finite normaliser of that label.  On underlying elements of `H`, this is
the restriction of `tau`. -/
def inducedFiniteNormalizerAut (tau : MulAut H) (T : A)
    (label_fixed : tau • T = T) :
    MulAut (finiteNormalizer (H := H) (A := A) T) :=
  (finiteNormalizerEquiv (H := H) (A := A) tau T).trans
    (finiteNormalizerCongr (H := H) (A := A) label_fixed)

@[simp]
theorem inducedFiniteNormalizerAut_coe (tau : MulAut H) (T : A)
    (label_fixed : tau • T = T)
    (x : finiteNormalizer (H := H) (A := A) T) :
    ((inducedFiniteNormalizerAut tau T label_fixed x :
      finiteNormalizer (H := H) (A := A) T) : H) = tau x := by
  change
    (((finiteNormalizerCongr (H := H) (A := A) label_fixed)
      (finiteNormalizerEquiv (H := H) (A := A) tau T x) :
        finiteNormalizer (H := H) (A := A) T) : H) = tau x
  calc
    (((finiteNormalizerCongr (H := H) (A := A) label_fixed)
        (finiteNormalizerEquiv (H := H) (A := A) tau T x) :
          finiteNormalizer (H := H) (A := A) T) : H) =
        ((finiteNormalizerEquiv (H := H) (A := A) tau T x :
          finiteNormalizer (H := H) (A := A) (tau • T)) : H) :=
      finiteNormalizerCongr_coe label_fixed _
    _ = tau x := finiteNormalizerEquiv_coe tau T x

/-- Fixation by `tau` also gives the label equality needed for right
transport, which acts covariantly by `tau⁻¹`. -/
theorem inverse_label_fixed (tau : MulAut H) (T : A)
    (label_fixed : tau • T = T) :
    tau.symm • T = T := by
  calc
    tau.symm • T = tau.symm • (tau • T) :=
      congrArg (fun U : A ↦ tau.symm • U) label_fixed.symm
    _ = T := inv_smul_smul tau T

/-- Character invariance under the induced action of `tau` implies the
inverse-action formula required by right transport. -/
theorem localCharacter_fixed_under_inverse
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    (character_fixed :
      twist k (finiteNormalizer (H := H) (A := A) P.1) P.2
          (inducedFiniteNormalizerAut tau P.1 label_fixed) = P.2)
    (x : finiteNormalizer (H := H) (A := A) P.1) :
    P.2 (transportedNormalizerElement tau.symm P P
      (inverse_label_fixed tau P.1 label_fixed).symm x) = P.2 x := by
  let y : finiteNormalizer (H := H) (A := A) P.1 :=
    transportedNormalizerElement tau.symm P P
      (inverse_label_fixed tau P.1 label_fixed).symm x
  have hcharacter := congrArg
    (fun chi : Irr k (finiteNormalizer (H := H) (A := A) P.1) ↦ chi y)
    character_fixed
  change P.2 (inducedFiniteNormalizerAut tau P.1 label_fixed y) = P.2 y at hcharacter
  have hyx : inducedFiniteNormalizerAut tau P.1 label_fixed y = x := by
    apply Subtype.ext
    rw [inducedFiniteNormalizerAut_coe,
      transportedNormalizerElement_coe]
    exact tau.apply_symm_apply x
  calc
    P.2 y = P.2 (inducedFiniteNormalizerAut tau P.1 label_fixed y) :=
      hcharacter.symm
    _ = P.2 x := congrArg P.2 hyx

/-- Separate fixation of the algebraic-torus label and its finite-normaliser
character combines to fixation of the dependent pair under the manuscript's
right action. -/
theorem rightTransportPair_eq_of_label_character_fixed
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    (character_fixed :
      twist k (finiteNormalizer (H := H) (A := A) P.1) P.2
          (inducedFiniteNormalizerAut tau P.1 label_fixed) = P.2) :
    rightTransportPair P tau = P := by
  have hsemantic : IsTransportedBy tau.symm P P :=
    { label_eq := (inverse_label_fixed tau P.1 label_fixed).symm
      character_eq := localCharacter_fixed_under_inverse tau P label_fixed
        character_fixed }
  change transportPair tau.symm P = P
  exact (transportPair_isTransported tau.symm P).right_unique hsemantic

end ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
