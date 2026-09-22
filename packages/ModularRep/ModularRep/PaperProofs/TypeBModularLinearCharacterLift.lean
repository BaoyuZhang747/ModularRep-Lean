import ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The actual prime-to-ell ordinary lift of modular quotient characters

Every modular linear character value is killed by the prime-to-ell part
of the finite group order. Applying the prescribed root equivalence to
these values constructs an ordinary linear character on the whole group.
Its image is the selected ordinary tensor subgroup. Injectivity, triviality
on the given subgroup and compatibility with inverse field pullback are
proved from this same pointwise construction.

No ordinary/modular character correspondence, field-equivariance or
regular-value compatibility is a source input. The ordinary subgroup is
the actual lift range, proved equal to all ordinary quotient characters
whose order is prime to ell. The root embedding may in particular be the
checked modular-system construction.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBModularLinearCharacterLift

open ModularRep
open TypeCConformalActionAdapter

universe u

variable {ell : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k ell] [Group G] [Finite G]
  (iota : PrimeRegularRootEmbedding ell k K G)

include iota in
/-- Modular linear character values have no ell-primary torsion, even
when the original group element is not prime regular. -/
theorem value_pow (lambda : G →* kˣ) (g : G) :
    (lambda g : k) ^ primeRegularExponent ell G = 1 := by
  letI : Fact ell.Prime := ⟨iota.prime⟩
  have hcard : (lambda g : k) ^ Nat.card G = 1 := by
    have h := congrArg (fun x : kˣ => (x : k))
      (congrArg lambda (pow_card_eq_one' (x := g)))
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using h
  apply (ExpChar.pow_prime_pow_mul_eq_one_iff ell ((Nat.card G).factorization ell)
    (primeRegularExponent ell G) (lambda g : k)).mp
  have hfactor := Nat.ordProj_mul_ordCompl_eq_self (Nat.card G) ell
  change ell ^ (Nat.card G).factorization ell * primeRegularExponent ell G =
    Nat.card G at hfactor
  rw [hfactor]
  exact hcard

/-- The character itself takes values in the full relevant root group. -/
def characterRoot (lambda : G →* kˣ) :
    G →* rootsOfUnity (primeRegularExponent ell G) k where
  toFun g := ⟨lambda g, by
    apply (mem_rootsOfUnity (primeRegularExponent ell G) (lambda g)).mpr
    apply Units.ext
    exact value_pow iota lambda g⟩
  map_one' := Subtype.ext (map_one lambda)
  map_mul' g h := Subtype.ext (map_mul lambda g h)

@[simp]
theorem characterRoot_val (lambda : G →* kˣ) (g : G) :
    (characterRoot iota lambda g).val = lambda g := rfl

/-- Pointwise root lifting defines an ordinary character on ALL elements. -/
def liftCharacter (lambda : G →* kˣ) : G →* Kˣ :=
  (rootsOfUnity (primeRegularExponent ell G) K).subtype.comp
    (iota.toMulEquiv.toMonoidHom.comp (characterRoot iota lambda))

@[simp]
theorem liftCharacter_apply (lambda : G →* kˣ) (g : G) :
    liftCharacter iota lambda g = (iota.toMulEquiv (characterRoot iota lambda g)).val :=
  rfl

theorem liftCharacter_injective : Function.Injective (liftCharacter iota) := by
  intro lambda mu h
  apply MonoidHom.ext
  intro g
  have hv := DFunLike.congr_fun h g
  have hr : iota.toMulEquiv (characterRoot iota lambda g) =
      iota.toMulEquiv (characterRoot iota mu g) := Subtype.ext hv
  exact congrArg Subtype.val (iota.toMulEquiv.injective hr)

/-- The lift preserves the pointwise character group operation. -/
def liftHom : (G →* kˣ) →* (G →* Kˣ) where
  toFun := liftCharacter iota
  map_one' := by
    apply MonoidHom.ext
    intro g
    have hroot : characterRoot iota (1 : G →* kˣ) g = 1 := Subtype.ext rfl
    rw [liftCharacter_apply, hroot, map_one]
    rfl
  map_mul' lambda mu := by
    apply MonoidHom.ext
    intro g
    have hroot : characterRoot iota (lambda * mu) g =
        characterRoot iota lambda g * characterRoot iota mu g := Subtype.ext rfl
    change (iota.toMulEquiv (characterRoot iota (lambda * mu) g)).val =
      (iota.toMulEquiv (characterRoot iota lambda g)).val *
        (iota.toMulEquiv (characterRoot iota mu g)).val
    rw [hroot, map_mul]
    rfl

@[simp]
theorem liftHom_apply (lambda : G →* kˣ) : liftHom iota lambda = liftCharacter iota lambda :=
  rfl

/-- The ordinary character, not just each chosen value, has bounded order. -/
theorem liftCharacter_pow (lambda : G →* kˣ) :
    liftCharacter iota lambda ^ primeRegularExponent ell G = 1 := by
  apply MonoidHom.ext
  intro g
  change (liftCharacter iota lambda g) ^ primeRegularExponent ell G = 1
  exact (mem_rootsOfUnity (primeRegularExponent ell G)
    (iota.toMulEquiv (characterRoot iota lambda g)).val).mp
      (iota.toMulEquiv (characterRoot iota lambda g)).property

include iota in
theorem exponent_coprime : (primeRegularExponent ell G).Coprime ell :=
  (Nat.coprime_ordCompl iota.prime (Nat.card_pos (α := G)).ne').symm

theorem liftCharacter_order_coprime (lambda : G →* kˣ) :
    (orderOf (liftCharacter iota lambda)).Coprime ell :=
  Nat.Coprime.of_dvd_left (orderOf_dvd_of_pow_eq_one (liftCharacter_pow iota lambda))
    (exponent_coprime iota)

/-- Root lifting commutes with actual group pullback without moving coefficients. -/
theorem liftCharacter_precomp (lambda : G →* kˣ) (alpha : G →* G) :
    liftCharacter iota (lambda.comp alpha) = (liftCharacter iota lambda).comp alpha := by
  apply MonoidHom.ext
  intro g
  rfl

theorem liftCharacter_eq_one (lambda : G →* kˣ) (g : G) (h : lambda g = 1) :
    liftCharacter iota lambda g = 1 := by
  have hroot : characterRoot iota lambda g = 1 := Subtype.ext h
  rw [liftCharacter_apply, hroot, map_one]
  rfl

/-- Every ordinary linear character is killed by the actual group order. -/
theorem character_pow_card (lambda : G →* Kˣ) : lambda ^ Nat.card G = 1 := by
  apply MonoidHom.ext
  intro g
  change lambda g ^ Nat.card G = 1
  rw [← map_pow, pow_card_eq_one', map_one]

include iota in
/-- An ell-prime ordinary character is killed by precisely the exponent
used by the root convention. -/
theorem primeTo_character_pow (lambda : G →* Kˣ)
    (h : ell.Coprime (orderOf lambda)) :
    lambda ^ primeRegularExponent ell G = 1 := by
  apply (orderOf_dvd_iff_pow_eq_one (x := lambda)).mp
  exact Nat.dvd_ordCompl_of_dvd_not_dvd
    (orderOf_dvd_of_pow_eq_one (character_pow_card lambda))
    (iota.prime.coprime_iff_not_dvd.mp h)

/-- The literal root-valued form of an ordinary ell-prime character. -/
def ordinaryCharacterRoot (lambda : G →* Kˣ)
    (h : ell.Coprime (orderOf lambda)) :
    G →* rootsOfUnity (primeRegularExponent ell G) K where
  toFun g := ⟨lambda g, by
    apply (mem_rootsOfUnity (primeRegularExponent ell G) (lambda g)).mpr
    exact DFunLike.congr_fun (primeTo_character_pow iota lambda h) g⟩
  map_one' := Subtype.ext (map_one lambda)
  map_mul' g t := Subtype.ext (map_mul lambda g t)

/-- Inverse pointwise root transport descends every ell-prime character. -/
def descendCharacter (lambda : G →* Kˣ) (h : ell.Coprime (orderOf lambda)) : G →* kˣ :=
  (rootsOfUnity (primeRegularExponent ell G) k).subtype.comp
    (iota.toMulEquiv.symm.toMonoidHom.comp (ordinaryCharacterRoot iota lambda h))

theorem lift_descendCharacter (lambda : G →* Kˣ) (h : ell.Coprime (orderOf lambda)) :
    liftCharacter iota (descendCharacter iota lambda h) = lambda := by
  apply MonoidHom.ext
  intro g
  have hroot : characterRoot iota (descendCharacter iota lambda h) g =
      iota.toMulEquiv.symm (ordinaryCharacterRoot iota lambda h g) := Subtype.ext rfl
  rw [liftCharacter_apply, hroot, MulEquiv.apply_symm_apply]
  rfl

section CharacterInterface

variable [CharZero K] [IsAlgClosed k]

/-- On regular elements the whole-group lift is exactly the existing
linear Brauer lift, so no reduction-compatibility input is needed. -/
theorem liftCharacter_regularCompatible (lambda : G →* kˣ) :
    LinearCharacterReductionCompatible iota (liftCharacter iota lambda) lambda := by
  ext g
  change iota.liftRoot (characterRoot iota lambda g.val) =
    iota.liftRoot (iota.linearCharacterRoot lambda g)
  apply congrArg iota.liftRoot
  apply Subtype.ext
  apply Units.ext
  rfl

variable (G0 : Subgroup G) [G0.Normal]

/-- Restrict the same lift to the actual modular quotient-character subgroup. -/
def quotientLift : TensorCharacters (k := k) G0 →* (G →* Kˣ) :=
  (liftHom iota).comp (linearCharactersTrivialOn (k := k) G0).subtype

@[simp]
theorem quotientLift_apply (c : TensorCharacters (k := k) G0) :
    quotientLift iota G0 c = liftCharacter iota c.val := rfl

theorem quotientLift_injective : Function.Injective (quotientLift iota G0) := by
  intro c d h
  apply Subtype.ext
  exact liftCharacter_injective iota h

theorem quotientLift_trivial (c : TensorCharacters (k := k) G0) :
    quotientLift iota G0 c ∈ linearCharactersTrivialOn (k := K) G0 := by
  intro g hg
  exact liftCharacter_eq_one iota c.val g (c.property hg)

theorem descendCharacter_trivial (lambda : G →* Kˣ)
    (h : ell.Coprime (orderOf lambda))
    (htrivial : lambda ∈ linearCharactersTrivialOn (k := K) G0) :
    descendCharacter iota lambda h ∈ linearCharactersTrivialOn (k := k) G0 := by
  intro g hg
  change (iota.toMulEquiv.symm (ordinaryCharacterRoot iota lambda h g)).val = 1
  have hroot : ordinaryCharacterRoot iota lambda h g = 1 := Subtype.ext (htrivial hg)
  rw [hroot, map_one]
  rfl

/-- Every ordinary ell-prime quotient character belongs to the constructed range. -/
theorem mem_quotientLift_range_of_primeTo (lambda : G →* Kˣ)
    (htrivial : lambda ∈ linearCharactersTrivialOn (k := K) G0)
    (h : ell.Coprime (orderOf lambda)) : lambda ∈ (quotientLift iota G0).range := by
  refine ⟨⟨descendCharacter iota lambda h,
    descendCharacter_trivial iota G0 lambda h htrivial⟩, ?_⟩
  exact lift_descendCharacter iota lambda h

/-- The range is exactly ALL ordinary ell-prime quotient characters. -/
theorem mem_quotientLift_range_iff (lambda : G →* Kˣ) :
    lambda ∈ (quotientLift iota G0).range ↔
      lambda ∈ linearCharactersTrivialOn (k := K) G0 ∧
        ell.Coprime (orderOf lambda) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨quotientLift_trivial iota G0 c, (liftCharacter_order_coprime iota c.val).symm⟩
  · rintro ⟨htrivial, h⟩
    exact mem_quotientLift_range_of_primeTo iota G0 lambda htrivial h

/-- The selected ordinary subgroup is the literal injective lift range. -/
def quotientLiftRangeEquiv :
    TensorCharacters (k := k) G0 ≃* (quotientLift iota G0).range :=
  MonoidHom.ofInjective (quotientLift_injective iota G0)

@[simp]
theorem quotientLiftRangeEquiv_apply (c : TensorCharacters (k := k) G0) :
    (quotientLiftRangeEquiv iota G0 c).val = quotientLift iota G0 c := rfl

theorem quotientLiftRangeEquiv_symm_apply (lambda : (quotientLift iota G0).range) :
    quotientLift iota G0 ((quotientLiftRangeEquiv iota G0).symm lambda) = lambda.val :=
  MonoidHom.apply_ofInjective_symm (quotientLift_injective iota G0) lambda

theorem ordinaryRange_order_coprime (lambda : (quotientLift iota G0).range) :
    (orderOf lambda.val).Coprime ell := by
  rw [← quotientLiftRangeEquiv_symm_apply iota G0 lambda]
  exact liftCharacter_order_coprime iota _

variable {E : Type u} [Group E]
  (field : E →* MulAut G)
  (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)

/-- The inverse group pullback is exactly the existing field convention. -/
theorem quotientLift_field (e : E) (c : TensorCharacters (k := k) G0) :
    quotientLift iota G0
        (LinearCharactersTrivialOn.fieldAction (k := k) field
          (FieldInvariantSubgroup.isFieldStable G0 field hinvariant) e c) =
      (quotientLift iota G0 c).comp (field e⁻¹).toMonoidHom :=
  liftCharacter_precomp iota c.val (field e⁻¹).toMonoidHom

/-- All fields of the former ordinary-reduction source packet are constructed. -/
def ordinaryReductionEquiv :
    OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant where
  ordinaryTensorCharacters := (quotientLift iota G0).range
  ordinaryToBrauer := (quotientLiftRangeEquiv iota G0).symm
  field_stable e lambda := by
    refine ⟨LinearCharactersTrivialOn.fieldAction (k := k) field
      (FieldInvariantSubgroup.isFieldStable G0 field hinvariant) e
      ((quotientLiftRangeEquiv iota G0).symm lambda), ?_⟩
    rw [quotientLift_field iota G0 field hinvariant, quotientLiftRangeEquiv_symm_apply]
  field_equivariant e lambda := by
    apply (quotientLiftRangeEquiv iota G0).injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    change lambda.val.comp (field e⁻¹).toMonoidHom =
      quotientLift iota G0 (LinearCharactersTrivialOn.fieldAction (k := k) field
        (FieldInvariantSubgroup.isFieldStable G0 field hinvariant) e
        ((quotientLiftRangeEquiv iota G0).symm lambda))
    rw [quotientLift_field iota G0 field hinvariant, quotientLiftRangeEquiv_symm_apply]

@[simp]
theorem ordinaryReductionEquiv_range :
    (ordinaryReductionEquiv iota G0 field hinvariant).ordinaryTensorCharacters =
      (quotientLift iota G0).range := rfl

/-- The old consumer's selected subgroup has the manuscript's full ell-prime carrier. -/
theorem ordinaryReductionEquiv_range_iff (lambda : G →* Kˣ) :
    lambda ∈ (ordinaryReductionEquiv iota G0 field hinvariant).ordinaryTensorCharacters ↔
      lambda ∈ linearCharactersTrivialOn (k := K) G0 ∧
        ell.Coprime (orderOf lambda) :=
  mem_quotientLift_range_iff iota G0 lambda

/-- The old consumer's named lift is the SAME pointwise root lift. -/
theorem ordinaryReductionEquiv_lift :
    OrdinaryReductionEquiv.lift (G0 := G0) (field := field) (hinvariant := hinvariant)
        (ordinaryReductionEquiv iota G0 field hinvariant) = quotientLift iota G0 := by
  ext c g
  rfl

theorem liftCompatible :
    TypeBSpecialCliffordActionAdapter.OrdinaryLiftReductionCompatible G0 field hinvariant
      (ordinaryReductionEquiv iota G0 field hinvariant) iota := by
  intro c
  change LinearCharacterReductionCompatible iota
    ((OrdinaryReductionEquiv.lift (G0 := G0) (field := field) (hinvariant := hinvariant)
      (ordinaryReductionEquiv iota G0 field hinvariant)) c) c.val
  rw [ordinaryReductionEquiv_lift]
  exact liftCharacter_regularCompatible iota c.val

theorem liftTrivial (c : TensorCharacters (k := k) G0) :
    OrdinaryReductionEquiv.lift (G0 := G0) (field := field) (hinvariant := hinvariant)
        (ordinaryReductionEquiv iota G0 field hinvariant) c ∈
      linearCharactersTrivialOn (k := K) G0 := by
  rw [ordinaryReductionEquiv_lift]
  exact quotientLift_trivial iota G0 c

end CharacterInterface

end ModularRep.PaperProofs.TypeBModularLinearCharacterLift


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
