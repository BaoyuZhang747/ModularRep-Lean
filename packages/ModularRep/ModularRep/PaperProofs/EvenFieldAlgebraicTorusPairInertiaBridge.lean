import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairCharacterBridge

/-!
# Inertia and relative-quotient inputs for an algebraic-torus pair

This module defines the inertia subgroup of an actual irreducible character
of the base subgroup.  It then derives invariance of that inertia subgroup
from invariance of the base character, and restricts a universal
relative-normaliser difference relation to the inertia subgroup.

Thus the final character bridge no longer needs independently supplied
inertia stability or an inertia-level quotient-triviality relation.
-/

namespace ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CharacterInductionEquivariance
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairAssembly
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairCharacterBridge
open ModularRep.PaperProofs.EvenFieldGallagherFormula
open ModularRep.PaperProofs.EvenFieldLocalCharacterFormula

universe u

variable {k N : Type u} [Field k] [CharZero k] [Group N]

/-- The inertia subgroup of an actual irreducible character of a normal base
subgroup. -/
def characterInertia (B : Subgroup N) [B.Normal]
    (lambda : Irr k B) : Subgroup N where
  carrier := {n : N |
    twist k B lambda (MulAut.conjNormal n) = lambda}
  one_mem' := by
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    simp only [twist_apply]
    apply congrArg lambda
    apply Subtype.ext
    simp
  mul_mem' := by
    intro x y hx hy
    apply OrdinaryIrreducibleCharacter.ext
    intro b
    simp only [twist_apply]
    calc
      lambda (MulAut.conjNormal (x * y) b) =
          lambda (MulAut.conjNormal x (MulAut.conjNormal y b)) := by
        apply congrArg lambda
        apply Subtype.ext
        simp [mul_assoc]
      _ = lambda (MulAut.conjNormal y b) := by
        exact congrArg
          (fun chi : Irr k B ↦ chi (MulAut.conjNormal y b)) hx
      _ = lambda b := by
        exact congrArg (fun chi : Irr k B ↦ chi b) hy
  inv_mem' := by
    intro x hx
    apply OrdinaryIrreducibleCharacter.ext
    intro b
    simp only [twist_apply]
    have hpoint := congrArg
      (fun chi : Irr k B ↦ chi (MulAut.conjNormal x⁻¹ b)) hx
    calc
      lambda (MulAut.conjNormal x⁻¹ b) =
          lambda (MulAut.conjNormal x
            (MulAut.conjNormal x⁻¹ b)) := hpoint.symm
      _ = lambda b := by
        apply congrArg lambda
        apply Subtype.ext
        simp

/-- Every element of the base subgroup fixes its irreducible character by
inner conjugation, so the base lies in its inertia subgroup. -/
theorem base_le_characterInertia (B : Subgroup N) [B.Normal]
    (lambda : Irr k B) : B ≤ characterInertia B lambda := by
  intro n hn
  apply OrdinaryIrreducibleCharacter.ext
  intro b
  simp only [twist_apply]
  rcases lambda.property with ⟨R⟩
  let nB : B := ⟨n, hn⟩
  have harg : MulAut.conjNormal n b = nB * b * nB⁻¹ := by
    apply Subtype.ext
    rfl
  rw [harg]
  rw [← congrFun R.character_eq, ← congrFun R.character_eq]
  simpa [nB, mul_assoc] using
    R.representation.char_mul_comm (nB⁻¹) (nB * b)

/-- The base subgroup, viewed inside its inertia subgroup. -/
def baseInInertia (B : Subgroup N) [B.Normal]
    (lambda : Irr k B) : Subgroup (characterInertia B lambda) :=
  B.comap (characterInertia B lambda).subtype

instance baseInInertia_normal (B : Subgroup N) [B.Normal]
    (lambda : Irr k B) : (baseInInertia B lambda).Normal := by
  unfold baseInInertia
  exact (inferInstance : B.Normal).comap
    (characterInertia B lambda).subtype

/-- A universal relative difference relation already implies stability of
the base subgroup. -/
theorem subgroup_stable_of_difference
    (B : Subgroup N) (alpha : MulAut N)
    (difference_mem : ∀ x : N, x⁻¹ * alpha x ∈ B) :
    ∀ x : N, x ∈ B ↔ alpha x ∈ B := by
  intro x
  constructor
  · intro hx
    have hmul := B.mul_mem hx (difference_mem x)
    simpa [mul_assoc] using hmul
  · intro hx
    have hmul := B.mul_mem hx (B.inv_mem (difference_mem x))
    simpa [mul_assoc] using hmul

/-- Fixation of a character by an automorphism also gives fixation by the
inverse automorphism. -/
theorem twist_symm_eq_self_of_twist_eq_self
    (lambda : Irr k N) (alpha : MulAut N)
    (hfixed : twist k N lambda alpha = lambda) :
    twist k N lambda alpha.symm = lambda := by
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  simp only [twist_apply]
  have hpoint := congrArg
    (fun chi : Irr k N ↦ chi (alpha.symm x)) hfixed
  simpa using hpoint.symm

/-- Restriction of an automorphism to a stable normal subgroup commutes with
ambient conjugation. -/
theorem restrictAut_conjNormal_apply
    (B : Subgroup N) [B.Normal]
    (alpha : MulAut N)
    (base_stable : ∀ x : N, x ∈ B ↔ alpha x ∈ B)
    (n : N) (b : B) :
    restrictAut B alpha base_stable (MulAut.conjNormal n b) =
      MulAut.conjNormal (alpha n)
        (restrictAut B alpha base_stable b) := by
  apply Subtype.ext
  simp [mul_assoc]

/-- If `alpha` fixes the base character, it carries every inertia element to
an inertia element. -/
theorem map_mem_characterInertia
    (B : Subgroup N) [B.Normal]
    (lambda : Irr k B)
    (alpha : MulAut N)
    (base_stable : ∀ x : N, x ∈ B ↔ alpha x ∈ B)
    (lambda_fixed :
      twist k B lambda (restrictAut B alpha base_stable) = lambda)
    (n : N) (hn : n ∈ characterInertia B lambda) :
    alpha n ∈ characterInertia B lambda := by
  apply OrdinaryIrreducibleCharacter.ext
  intro b
  simp only [twist_apply]
  let alphaB := restrictAut B alpha base_stable
  let b₀ : B := alphaB.symm b
  have hb : alphaB b₀ = b := alphaB.apply_symm_apply b
  have hconj : MulAut.conjNormal (alpha n) b =
      alphaB (MulAut.conjNormal n b₀) := by
    rw [← hb]
    exact (restrictAut_conjNormal_apply B alpha base_stable n b₀).symm
  have hlambda (x : B) : lambda (alphaB x) = lambda x := by
    exact congrArg (fun chi : Irr k B ↦ chi x) lambda_fixed
  have hnpoint (x : B) : lambda (MulAut.conjNormal n x) = lambda x := by
    exact congrArg (fun chi : Irr k B ↦ chi x) hn
  calc
    lambda (MulAut.conjNormal (alpha n) b) =
        lambda (alphaB (MulAut.conjNormal n b₀)) :=
      congrArg lambda hconj
    _ = lambda (MulAut.conjNormal n b₀) :=
      hlambda (MulAut.conjNormal n b₀)
    _ = lambda b₀ := hnpoint b₀
    _ = lambda (alphaB b₀) := (hlambda b₀).symm
    _ = lambda b := congrArg lambda hb

/-- The inertia subgroup of a base character fixed by `alpha` is stable under
`alpha`. -/
theorem characterInertia_stable
    (B : Subgroup N) [B.Normal]
    (lambda : Irr k B)
    (alpha : MulAut N)
    (base_stable : ∀ x : N, x ∈ B ↔ alpha x ∈ B)
    (lambda_fixed :
      twist k B lambda (restrictAut B alpha base_stable) = lambda) :
    ∀ n : N,
      n ∈ characterInertia B lambda ↔
        alpha n ∈ characterInertia B lambda := by
  intro n
  constructor
  · exact map_mem_characterInertia B lambda alpha base_stable lambda_fixed n
  · intro hn
    have base_stable_symm : ∀ x : N,
        x ∈ B ↔ alpha.symm x ∈ B := by
      intro x
      simpa using (base_stable (alpha.symm x)).symm
    have restrict_symm :
        restrictAut B alpha.symm base_stable_symm =
          (restrictAut B alpha base_stable).symm := by
      ext x
      rfl
    have lambda_fixed_symm :
        twist k B lambda
          (restrictAut B alpha.symm base_stable_symm) = lambda := by
      rw [restrict_symm]
      exact twist_symm_eq_self_of_twist_eq_self lambda
        (restrictAut B alpha base_stable) lambda_fixed
    have hmap := map_mem_characterInertia B lambda alpha.symm
      base_stable_symm lambda_fixed_symm (alpha n) hn
    simpa using hmap

/-- The inertia subgroup is stable once the universal relative difference
relation and fixation of the actual base character are known. -/
theorem characterInertia_stable_of_difference
    (B : Subgroup N) [B.Normal]
    (lambda : Irr k B)
    (alpha : MulAut N)
    (difference_mem : ∀ x : N, x⁻¹ * alpha x ∈ B)
    (lambda_fixed :
      twist k B lambda
        (restrictAut B alpha
          (subgroup_stable_of_difference B alpha difference_mem)) = lambda) :
    ∀ n : N,
      n ∈ characterInertia B lambda ↔
        alpha n ∈ characterInertia B lambda :=
  characterInertia_stable B lambda alpha
    (subgroup_stable_of_difference B alpha difference_mem) lambda_fixed

/-- Restricting the universal relative difference relation to the inertia
subgroup gives exactly the quotient-triviality input used by Gallagher's
formula. -/
theorem characterInertia_difference_mem
    (B : Subgroup N) [B.Normal]
    (lambda : Irr k B)
    (alpha : MulAut N)
    (difference_mem : ∀ x : N, x⁻¹ * alpha x ∈ B)
    (lambda_fixed :
      twist k B lambda
        (restrictAut B alpha
          (subgroup_stable_of_difference B alpha difference_mem)) = lambda) :
    ∀ x : characterInertia B lambda,
      x⁻¹ * restrictAut (characterInertia B lambda) alpha
        (characterInertia_stable_of_difference B lambda alpha
          difference_mem lambda_fixed) x ∈ baseInInertia B lambda := by
  intro x
  change ((x : N)⁻¹ * alpha (x : N)) ∈ B
  exact difference_mem x

variable {H A K V : Type u}
    [Group H] [MulAction (MulAut H) A]
    [Group K] [AddCommGroup V] [Module k V]

/-- The character conclusion for an algebraic-torus pair with the inertia
subgroup defined from an actual base character.

Neither stability of the inertia subgroup nor the relative difference
relation on that subgroup is an input.  Both are derived from the universal
relative difference relation on the finite normaliser and invariance of the
base character. -/
theorem pairCharacter_fixed_of_inertia_extension_gallagher_clifford
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (B : Subgroup (finiteNormalizer (H := H) (A := A) P.1)) [B.Normal]
    (lambda : Irr k B)
    (difference_mem : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x⁻¹ * inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ B)
    (lambda_fixed :
      twist k B lambda
        (restrictAut B
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          (subgroup_stable_of_difference B
            (inducedFiniteNormalizerAut tau P.1 label_fixed)
            difference_mem)) = lambda)
    (rho : Representation k K V)
    (inclusion : characterInertia B lambda →* K)
    (z : K)
    (intertwines : ∀ x : characterInertia B lambda,
      inclusion (restrictAut (characterInertia B lambda)
        (inducedFiniteNormalizerAut tau P.1 label_fixed)
        (characterInertia_stable_of_difference B lambda
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          difference_mem lambda_fixed) x) =
          z * inclusion x * z⁻¹)
    (kappa : Irr k (characterInertia B lambda))
    (gallagher : HasGallagherFactorisation (baseInInertia B lambda)
      (rho.pullback inclusion).character kappa)
    (clifford : HasCliffordInduction (characterInertia B lambda) kappa P.2) :
    twist k (finiteNormalizer (H := H) (A := A) P.1) P.2
        (inducedFiniteNormalizerAut tau P.1 label_fixed) = P.2 := by
  exact pairCharacter_fixed_of_extension_gallagher_clifford tau P label_fixed
    (characterInertia B lambda)
    (characterInertia_stable_of_difference B lambda
      (inducedFiniteNormalizerAut tau P.1 label_fixed)
      difference_mem lambda_fixed)
    (baseInInertia B lambda)
    (characterInertia_difference_mem B lambda
      (inducedFiniteNormalizerAut tau P.1 label_fixed)
      difference_mem lambda_fixed)
    rho inclusion z intertwines kappa gallagher clifford

/-- Separate fixation of the algebraic-torus label and the source-shaped
inertia, extension, Gallagher, and Clifford inputs fix the dependent pair in
the manuscript's right-action convention. -/
theorem rightTransportPair_eq_of_inertia_extension_gallagher_clifford
    (tau : MulAut H) (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (B : Subgroup (finiteNormalizer (H := H) (A := A) P.1)) [B.Normal]
    (lambda : Irr k B)
    (difference_mem : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x⁻¹ * inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ B)
    (lambda_fixed :
      twist k B lambda
        (restrictAut B
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          (subgroup_stable_of_difference B
            (inducedFiniteNormalizerAut tau P.1 label_fixed)
            difference_mem)) = lambda)
    (rho : Representation k K V)
    (inclusion : characterInertia B lambda →* K)
    (z : K)
    (intertwines : ∀ x : characterInertia B lambda,
      inclusion (restrictAut (characterInertia B lambda)
        (inducedFiniteNormalizerAut tau P.1 label_fixed)
        (characterInertia_stable_of_difference B lambda
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          difference_mem lambda_fixed) x) =
          z * inclusion x * z⁻¹)
    (kappa : Irr k (characterInertia B lambda))
    (gallagher : HasGallagherFactorisation (baseInInertia B lambda)
      (rho.pullback inclusion).character kappa)
    (clifford : HasCliffordInduction (characterInertia B lambda) kappa P.2) :
    rightTransportPair P tau = P := by
  apply rightTransportPair_eq_of_label_character_fixed tau P label_fixed
  exact pairCharacter_fixed_of_inertia_extension_gallagher_clifford
    tau P label_fixed B lambda difference_mem lambda_fixed rho inclusion z
    intertwines kappa gallagher clifford

/-- The final orbit endpoint with inertia stability and the inertia-level
relative difference relation derived rather than assumed. -/
theorem validConjugacyClass_fixed_of_inertia_extension_gallagher_clifford
    (fieldAut tau : MulAut H) (h : H)
    (htau : tau = MulAut.conj h * fieldAut)
    (P : LocalPair k H A)
    (label_fixed : tau • P.1 = P.1)
    [Fintype (finiteNormalizer (H := H) (A := A) P.1)]
    (W : InnerStablePredicate k H A)
    (hP : W.predicate P)
    (B : Subgroup (finiteNormalizer (H := H) (A := A) P.1)) [B.Normal]
    (lambda : Irr k B)
    (difference_mem : ∀ x : finiteNormalizer (H := H) (A := A) P.1,
      x⁻¹ * inducedFiniteNormalizerAut tau P.1 label_fixed x ∈ B)
    (lambda_fixed :
      twist k B lambda
        (restrictAut B
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          (subgroup_stable_of_difference B
            (inducedFiniteNormalizerAut tau P.1 label_fixed)
            difference_mem)) = lambda)
    (rho : Representation k K V)
    (inclusion : characterInertia B lambda →* K)
    (z : K)
    (intertwines : ∀ x : characterInertia B lambda,
      inclusion (restrictAut (characterInertia B lambda)
        (inducedFiniteNormalizerAut tau P.1 label_fixed)
        (characterInertia_stable_of_difference B lambda
          (inducedFiniteNormalizerAut tau P.1 label_fixed)
          difference_mem lambda_fixed) x) =
          z * inclusion x * z⁻¹)
    (kappa : Irr k (characterInertia B lambda))
    (gallagher : HasGallagherFactorisation (baseInInertia B lambda)
      (rho.pullback inclusion).character kappa)
    (clifford : HasCliffordInduction (characterInertia B lambda) kappa P.2) :
    ∃ hField : W.predicate (rightTransportPair P fieldAut),
      validConjugacyClass W ⟨rightTransportPair P fieldAut, hField⟩ =
        validConjugacyClass W ⟨P, hP⟩ := by
  apply validConjugacyClass_fixed_of_innerTwist_right W fieldAut tau h htau
    P hP
  exact rightTransportPair_eq_of_inertia_extension_gallagher_clifford
    tau P label_fixed B lambda difference_mem lambda_fixed rho inclusion z
    intertwines kappa gallagher clifford

end ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
