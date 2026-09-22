import ModularRep.PaperProofs.TypeBFLZLabelSource
import ModularRep.PaperProofs.EvenFieldDependentGenericPair

/-!
# Literal CSp conjugation of FLZ centralizer characters

The actual CSp element, its two order guards, and the actual centralizer
character are transported by conjugation. Ordinary characters use the
checked covariant `transportIrr`: the value at y is the old character at
g⁻¹ y g. A one-way stability condition on this exact transported character
restricts the constructed action to the unipotent full/selected pairs.

The final adapter derives that condition from a fibrewise Psi labelling and
its literal character-value square. It does not define the combinatorial
Psi family or authenticate arbitrary names as the published unipotent
model. Core transport, orbit classifications, blocks and Conlon consumers
remain separate. No ordinary algebraic closure or target source is used.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy

open ModularRep OrdinaryIrreducibleCharacter
open TypeBConformalDualCarriers TypeBFLZLabelSource
open EvenFieldDependentGenericPair (transportIrr transportIrr_apply transportIrr_trans)

universe u

variable {F K : Type u} [Field F] [Field K] [CharZero K]
variable {p ell n : ℕ}

/-- Conjugation of the actual defining-prime regular parameter. -/
def semisimpleConj (g : CSp F n) (s : SemisimpleParameter F p n) :
    SemisimpleParameter F p n :=
  ⟨MulAut.conj g s.val, by
    rw [(MulAut.conj g).orderOf_eq]
    exact s.property⟩

@[simp]
theorem semisimpleConj_val (g : CSp F n) (s : SemisimpleParameter F p n) :
    (semisimpleConj g s).val = g * s.val * g⁻¹ := rfl

@[simp]
theorem semisimpleConj_one (s : SemisimpleParameter F p n) :
    semisimpleConj 1 s = s := by
  apply Subtype.ext
  simp

theorem semisimpleConj_mul (g h : CSp F n) (s : SemisimpleParameter F p n) :
    semisimpleConj (g * h) s = semisimpleConj g (semisimpleConj h s) := by
  apply Subtype.ext
  simp [mul_assoc]

/-- The same conjugation preserves the additional modular-prime guard. -/
def admissibleConj (g : CSp F n) (s : AdmissibleParameter F p ell n) :
    AdmissibleParameter F p ell n :=
  ⟨MulAut.conj g s.val, by
    rw [(MulAut.conj g).orderOf_eq]
    exact s.property⟩

@[simp]
theorem admissibleConj_val (g : CSp F n) (s : AdmissibleParameter F p ell n) :
    (admissibleConj g s).val = g * s.val * g⁻¹ := rfl

@[simp]
theorem admissibleConj_one (s : AdmissibleParameter F p ell n) :
    admissibleConj 1 s = s := by
  apply Subtype.ext
  simp

theorem admissibleConj_mul (g h : CSp F n) (s : AdmissibleParameter F p ell n) :
    admissibleConj (g * h) s = admissibleConj g (admissibleConj h s) := by
  apply Subtype.ext
  simp [mul_assoc]

@[simp]
theorem admissibleToSemisimple_conj (g : CSp F n)
    (s : AdmissibleParameter F p ell n) :
    admissibleToSemisimple F p ell n (admissibleConj g s) =
      semisimpleConj g (admissibleToSemisimple F p ell n s) := rfl

/-- The centralizer equivalence is actual conjugation, with actual inverse
conjugation. Membership is proved by transporting the commutation equation. -/
def centralizerConj (g : CSp F n) (s : SemisimpleParameter F p n) :
    parameterCentralizer F p n s ≃*
      parameterCentralizer F p n (semisimpleConj g s) where
  toFun x := ⟨MulAut.conj g x.val, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change MulAut.conj g x.val * MulAut.conj g s.val =
      MulAut.conj g s.val * MulAut.conj g x.val
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj g)
      (Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
  invFun y := ⟨(MulAut.conj g).symm y.val, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj g).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_centralizer_singleton_iff.mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (MulAut.conj g).symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    exact (MulAut.conj g).apply_symm_apply y.val
  map_mul' x y := by
    apply Subtype.ext
    exact (MulAut.conj g).map_mul x.val y.val

@[simp]
theorem centralizerConj_val (g : CSp F n) (s : SemisimpleParameter F p n)
    (x : parameterCentralizer F p n s) :
    (centralizerConj g s x).val = g * x.val * g⁻¹ := rfl

@[simp]
theorem centralizerConj_symm_val (g : CSp F n) (s : SemisimpleParameter F p n)
    (y : parameterCentralizer F p n (semisimpleConj g s)) :
    ((centralizerConj g s).symm y).val = g⁻¹ * y.val * g := rfl

/-- Reconciliation of equal parameter carriers changes no group element. -/
def centralizerCast {s t : SemisimpleParameter F p n} (h : s = t) :
    parameterCentralizer F p n s ≃* parameterCentralizer F p n t :=
  MulEquiv.subgroupCongr (congrArg (parameterCentralizer F p n) h)

@[simp]
theorem centralizerCast_val {s t : SemisimpleParameter F p n} (h : s = t)
    (x : parameterCentralizer F p n s) :
    (centralizerCast h x).val = x.val := rfl

/-- Identity coherence with its displayed, literal parameter cast. -/
theorem centralizerConj_one (s : SemisimpleParameter F p n) :
    (centralizerConj 1 s).trans (centralizerCast (semisimpleConj_one s)) =
      MulEquiv.refl (parameterCentralizer F p n s) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp

/-- Composition coherence with its displayed, literal parameter cast. -/
theorem centralizerConj_mul (g h : CSp F n) (s : SemisimpleParameter F p n) :
    (centralizerConj h s).trans (centralizerConj g (semisimpleConj h s)) =
      (centralizerConj (g * h) s).trans
        (centralizerCast (semisimpleConj_mul g h s)) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  simp [mul_assoc]

/-- Actual covariant ordinary-character transport along the centralizer
equivalence; the existing irreducible pullback construction is reused. -/
def centralizerCharacterConj (g : CSp F n) (s : SemisimpleParameter F p n)
    (chi : Irr K (parameterCentralizer F p n s)) :
    Irr K (parameterCentralizer F p n (semisimpleConj g s)) :=
  transportIrr (centralizerConj g s) chi

@[simp]
theorem centralizerCharacterConj_apply (g : CSp F n)
    (s : SemisimpleParameter F p n) (chi : Irr K (parameterCentralizer F p n s))
    (y : parameterCentralizer F p n (semisimpleConj g s)) :
    centralizerCharacterConj g s chi y = chi ((centralizerConj g s).symm y) := rfl

/-- Cast-free pointwise anchor for the transported actual character. -/
@[simp]
theorem centralizerCharacterConj_anchor (g : CSp F n)
    (s : SemisimpleParameter F p n) (chi : Irr K (parameterCentralizer F p n s))
    (x : parameterCentralizer F p n s) :
    centralizerCharacterConj g s chi (centralizerConj g s x) = chi x := by
  rw [centralizerCharacterConj_apply, MulEquiv.symm_apply_apply]

/-- The ordinary transport has the same multiplication coherence as the
actual centralizer maps, with no independently supplied character equation. -/
theorem centralizerCharacterConj_mul (g h : CSp F n)
    (s : SemisimpleParameter F p n) (chi : Irr K (parameterCentralizer F p n s)) :
    centralizerCharacterConj g (semisimpleConj h s) (centralizerCharacterConj h s chi) =
      transportIrr (centralizerCast (semisimpleConj_mul g h s))
        (centralizerCharacterConj (g * h) s chi) := by
  unfold centralizerCharacterConj
  rw [transportIrr_trans, transportIrr_trans, centralizerConj_mul]

section UnipotentPairs

variable (unipotent : UnipotentPredicate F K p n)

/-- The narrow one-way predicate condition uses exactly the constructed
character transport. It is a conditional model input, not a pair action. -/
def UnipotentStable : Prop :=
  ∀ (g : CSp F n) (s : SemisimpleParameter F p n)
    (chi : Irr K (parameterCentralizer F p n s)),
    unipotent s chi → unipotent (semisimpleConj g s) (centralizerCharacterConj g s chi)

variable (stable : UnipotentStable unipotent)

/-- The two actual dependent coordinates of the full pair action. -/
def fullPairConj (g : CSp F n) (P : FullCharacterPair F K p n unipotent) :
    FullCharacterPair F K p n unipotent :=
  ⟨semisimpleConj g P.1,
    centralizerCharacterConj g P.1 P.2.val, stable g P.1 P.2.val P.2.property⟩

@[simp]
theorem fullPairConj_parameter (g : CSp F n) (P : FullCharacterPair F K p n unipotent) :
    (fullPairConj unipotent stable g P).1 = semisimpleConj g P.1 := rfl

@[simp]
theorem fullPairConj_character (g : CSp F n) (P : FullCharacterPair F K p n unipotent)
    (x : parameterCentralizer F p n P.1) :
    (fullPairConj unipotent stable g P).2.val (centralizerConj g P.1 x) = P.2.val x :=
  centralizerCharacterConj_anchor g P.1 P.2.val x

/-- Extensionality on literal centralizer elements avoids hiding dependent
carrier casts inside the pair action laws. -/
theorem fullPair_ext {P Q : FullCharacterPair F K p n unipotent}
    (parameters : P.1 = Q.1)
    (values : ∀ (x : parameterCentralizer F p n P.1)
      (y : parameterCentralizer F p n Q.1), x.val = y.val → P.2.val x = Q.2.val y) :
    P = Q := by
  rcases P with ⟨s, chi⟩
  rcases Q with ⟨t, psi⟩
  change s = t at parameters
  subst t
  have characters : chi = psi := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro x
    exact values x x rfl
  exact congrArg (fun z : {chi : Irr K (parameterCentralizer F p n s) // unipotent s chi} =>
    (⟨s, z⟩ : FullCharacterPair F K p n unipotent)) characters

@[simp]
theorem fullPairConj_one (P : FullCharacterPair F K p n unipotent) :
    fullPairConj unipotent stable 1 P = P := by
  apply fullPair_ext unipotent (semisimpleConj_one P.1)
  intro x y hxy
  dsimp only [fullPairConj] at x y hxy ⊢
  change P.2.val ((centralizerConj 1 P.1).symm x) = P.2.val y
  apply congrArg P.2.val
  apply Subtype.ext
  simpa only [centralizerConj_symm_val, inv_one, one_mul, mul_one] using hxy

theorem fullPairConj_mul (g h : CSp F n) (P : FullCharacterPair F K p n unipotent) :
    fullPairConj unipotent stable (g * h) P =
      fullPairConj unipotent stable g (fullPairConj unipotent stable h P) := by
  apply fullPair_ext unipotent (semisimpleConj_mul g h P.1)
  intro x y hxy
  dsimp only [fullPairConj] at x y hxy ⊢
  change P.2.val ((centralizerConj (g * h) P.1).symm x) =
    P.2.val ((centralizerConj h P.1).symm
      ((centralizerConj g (semisimpleConj h P.1)).symm y))
  apply congrArg P.2.val
  apply Subtype.ext
  simp only [centralizerConj_symm_val]
  rw [hxy]
  simp [mul_assoc]

/-- The full dependent character-pair action is constructed, not sourced. -/
@[instance_reducible]
def fullPairAction : MulAction (CSp F n) (FullCharacterPair F K p n unipotent) where
  smul := fullPairConj unipotent stable
  one_smul := fullPairConj_one unipotent stable
  mul_smul := fullPairConj_mul unipotent stable

theorem fullPairAction_parameter (g : CSp F n) (P : FullCharacterPair F K p n unipotent) :
    let _ := fullPairAction unipotent stable
    (g • P).1.val = g * P.1.val * g⁻¹ := rfl

theorem fullPairAction_character (g : CSp F n) (P : FullCharacterPair F K p n unipotent)
    (x : parameterCentralizer F p n P.1) :
    let _ := fullPairAction unipotent stable
    (g • P).2.val (centralizerConj g P.1 x) = P.2.val x :=
  fullPairConj_character unipotent stable g P x

/-- The selected dependent action preserves BOTH order guards. -/
def selectedPairConj (g : CSp F n) (P : CharacterPair F K p ell n unipotent) :
    CharacterPair F K p ell n unipotent :=
  ⟨admissibleConj g P.1,
    centralizerCharacterConj g (admissibleToSemisimple F p ell n P.1) P.2.val,
    stable g (admissibleToSemisimple F p ell n P.1) P.2.val P.2.property⟩

/-- Forgetting the modular-prime order guard changes neither transported
centralizer character nor defining-prime parameter. -/
@[simp]
theorem selectedPairConj_toFull (g : CSp F n)
    (P : CharacterPair F K p ell n unipotent) :
    characterPairToFull F K p ell n unipotent (selectedPairConj unipotent stable g P) =
      fullPairConj unipotent stable g (characterPairToFull F K p ell n unipotent P) := rfl

theorem characterPairToFull_injective :
    Function.Injective (characterPairToFull F K p ell n unipotent) := by
  rintro ⟨s, chi⟩ ⟨t, psi⟩ equality
  have parameters : s = t := by
    apply Subtype.ext
    exact congrArg (fun P : FullCharacterPair F K p n unipotent => P.1.val) equality
  subst t
  change (⟨admissibleToSemisimple F p ell n s, chi⟩ : FullCharacterPair F K p n unipotent) =
    ⟨admissibleToSemisimple F p ell n s, psi⟩ at equality
  have characters : chi = psi := eq_of_heq (Sigma.mk.inj_iff.mp equality).2
  exact congrArg (fun z : {chi : Irr K (parameterCentralizer F p n
      (admissibleToSemisimple F p ell n s)) //
        unipotent (admissibleToSemisimple F p ell n s) chi} =>
    (⟨s, z⟩ : CharacterPair F K p ell n unipotent)) characters

@[simp]
theorem selectedPairConj_one (P : CharacterPair F K p ell n unipotent) :
    selectedPairConj unipotent stable 1 P = P := by
  apply characterPairToFull_injective unipotent
  rw [selectedPairConj_toFull, fullPairConj_one]

theorem selectedPairConj_mul (g h : CSp F n) (P : CharacterPair F K p ell n unipotent) :
    selectedPairConj unipotent stable (g * h) P =
      selectedPairConj unipotent stable g (selectedPairConj unipotent stable h P) := by
  apply characterPairToFull_injective unipotent
  rw [selectedPairConj_toFull, selectedPairConj_toFull,
    selectedPairConj_toFull, fullPairConj_mul]

/-- The selected action is restricted from the same full ordinary pair
action by its literal injective forgetful map. -/
@[instance_reducible]
def selectedPairAction : MulAction (CSp F n) (CharacterPair F K p ell n unipotent) where
  smul := selectedPairConj unipotent stable
  one_smul := selectedPairConj_one unipotent stable
  mul_smul := selectedPairConj_mul unipotent stable

theorem selectedPairAction_parameter (g : CSp F n)
    (P : CharacterPair F K p ell n unipotent) :
    let _ : MulAction (CSp F n) (CharacterPair F K p ell n unipotent) :=
      selectedPairAction (ell := ell) unipotent stable
    (g • P).1.val = g * P.1.val * g⁻¹ := rfl

theorem selectedPairAction_character (g : CSp F n)
    (P : CharacterPair F K p ell n unipotent)
    (x : parameterCentralizer F p n (admissibleToSemisimple F p ell n P.1)) :
    let _ : MulAction (CSp F n) (CharacterPair F K p ell n unipotent) :=
      selectedPairAction (ell := ell) unipotent stable
    (g • P).2.val (centralizerConj g (admissibleToSemisimple F p ell n P.1) x) =
      P.2.val x :=
  centralizerCharacterConj_anchor g _ P.2.val x

theorem characterPairToFull_equivariant (g : CSp F n)
    (P : CharacterPair F K p ell n unipotent) :
    let _ := fullPairAction unipotent stable
    let _ : MulAction (CSp F n) (CharacterPair F K p ell n unipotent) :=
      selectedPairAction (ell := ell) unipotent stable
    characterPairToFull F K p ell n unipotent (g • P) =
      g • characterPairToFull F K p ell n unipotent P := rfl

end UnipotentPairs

section PsiBridge

variable (unipotent : UnipotentPredicate F K p n)
  (Psi : SemisimpleParameter F p n → Type u)
  (psiConj : ∀ (g : CSp F n) (s : SemisimpleParameter F p n),
    Psi s ≃ Psi (semisimpleConj g s))
  (unipotentLabel : ∀ s, Psi s ≃ {chi : Irr K (parameterCentralizer F p n s) //
    unipotent s chi})

/-- The exact local source-model square required when unchanged
combinatorial Psi labels are identified with actual centralizer characters.
No group action, pair classification or target correspondence is asserted. -/
def PsiCharacterSquare : Prop :=
  ∀ (g : CSp F n) (s : SemisimpleParameter F p n) (mu : Psi s)
    (x : parameterCentralizer F p n s),
    (unipotentLabel (semisimpleConj g s) (psiConj g s mu)).val (centralizerConj g s x) =
      (unipotentLabel s mu).val x

/-- Surjectivity of the actual fibrewise unipotent labelling and its
pointwise square supply exactly the one-way stability used above. Actual
Psi definitions, coefficient scope and source realization remain explicit. -/
theorem unipotentStable_of_psiCharacterSquare
    (square : PsiCharacterSquare unipotent Psi psiConj unipotentLabel) :
    UnipotentStable unipotent := by
  intro g s chi hchi
  let mu := (unipotentLabel s).symm ⟨chi, hchi⟩
  have hmu : (unipotentLabel s mu).val = chi :=
    congrArg Subtype.val ((unipotentLabel s).apply_symm_apply ⟨chi, hchi⟩)
  have equality : (unipotentLabel (semisimpleConj g s) (psiConj g s mu)).val =
      centralizerCharacterConj g s chi := by
    apply OrdinaryIrreducibleCharacter.ext
    intro y
    obtain ⟨x, rfl⟩ := (centralizerConj g s).surjective y
    rw [square, centralizerCharacterConj_anchor, hmu]
  exact equality ▸ (unipotentLabel (semisimpleConj g s) (psiConj g s mu)).property

end PsiBridge

end ModularRep.PaperProofs.TypeBFLZCentralizerConjugacy


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
