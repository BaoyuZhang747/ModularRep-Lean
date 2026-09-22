import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.WeightCharacterBridge
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# The literal weight-normalizer input in Type B Proposition 4.3

Feng--Li--Zhang, Proposition 7.5, pp. 573--574, is an E2 source: for
each weight `(R, phi)` of Spin it gives the product factorization of the
normalizer inertia inside the special Clifford group extended by prime
Frobenius. This file states that one-way source on the actual carriers.
It does not prove the published factorization or assume any iBAW target.

The subgroup is the subgroup of a raw `CharacterWeight`; its local
character is an ordinary irreducible character of the actual normalizer
quotient. `CharacterWeight.Isomorphic` here means equality of that
subgroup and equality of the canonically transported local character.
It is not an unspecified conjugacy relation or an action on free labels.
The ambient normalizer is retained explicitly in the inertia set.

The group, norm and Frobenius sources inherit their E1/U authentication
boundary. Transport of the published complex-character statement to the
selected algebraically closed characteristic-zero coefficient field is
the usual E1 character-field identification and remains explicit.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBWeightStabilizerSource

open ModularRep TypeBCliffordCarriers

variable {n p f ell : ℕ} {F K : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field K] [CharZero K]
variable {N : NormSource n F}
variable {parameters : OddFieldParameters F p f}
variable (S : FieldActionSource n F p f parameters N)
variable [Finite (Spin n F N)]

/-- The actual source ambient group `D_0(V) semidirect <F_p>`. -/
abbrev Ambient := SpecialClifford n F ⋊[S.action] FieldGroup f

/-- The actual subgroup `Spin(V) semidirect <F_p>`, before embedding. -/
abbrev SpinField := Spin n F N ⋊[spinFieldAction n F S] FieldGroup f

/-- Inclusion of the source's `G D` into its `Gtilde D`. -/
def spinFieldEmbedding : SpinField S →* Ambient S :=
  SemidirectProduct.map (SpinSubgroup n F N).subtype
    (MonoidHom.id (FieldGroup f)) (by
      intro e
      apply MonoidHom.ext
      intro g
      exact spinFieldAction_coe n F S e g)

@[simp]
theorem spinFieldEmbedding_left (a : SpinField S) :
    (spinFieldEmbedding S a).left = a.left.1 := rfl

@[simp]
theorem spinFieldEmbedding_right (a : SpinField S) :
    (spinFieldEmbedding S a).right = a.right := rfl

theorem spinFieldEmbedding_injective : Function.Injective (spinFieldEmbedding S) := by
  intro a b hab
  apply SemidirectProduct.ext
  · apply Subtype.ext
    exact congrArg SemidirectProduct.left hab
  · exact congrArg (fun x : Ambient S => x.right) hab

/-- Inclusion of the literal Spin group into the same ambient group. -/
def spinEmbedding : Spin n F N →* Ambient S :=
  SemidirectProduct.inl.comp (SpinSubgroup n F N).subtype

/-- The automorphism induced on Spin by an actual ambient element.
Multiplication of `MulAut` means composition, so the displayed expression
is `x |-> a.left * F_a.right(x) * a.left^-1`. -/
def ambientSpinAutomorphism (a : Ambient S) : MulAut (Spin n F N) :=
  MulAut.conjNormal (H := SpinSubgroup n F N) a.left *
    spinFieldAction n F S a.right

@[simp]
theorem ambientSpinAutomorphism_coe (a : Ambient S) (x : Spin n F N) :
    (ambientSpinAutomorphism S a x).1 =
      a.left * S.action a.right x.1 * a.left⁻¹ := rfl

@[simp]
theorem ambientSpinAutomorphism_inl (m : SpecialClifford n F) :
    ambientSpinAutomorphism S (SemidirectProduct.inl m) =
      MulAut.conjNormal (H := SpinSubgroup n F N) m := by
  simp [ambientSpinAutomorphism]

@[simp]
theorem ambientSpinAutomorphism_inr (e : FieldGroup f) :
    ambientSpinAutomorphism S (SemidirectProduct.inr e) =
      spinFieldAction n F S e := by
  simp [ambientSpinAutomorphism]

/-- `R` is embedded through its actual Spin and Clifford inclusions. -/
def embeddedRadical (W : CharacterWeight ell K (Spin n F N)) :
    Subgroup (Ambient S) :=
  W.subgroup.map (spinEmbedding S)

/-- The source ordinary character on `N_G(R)` is the inflation of the
literal quotient character stored in the raw weight. -/
def inflatedLocalCharacter (W : CharacterWeight ell K (Spin n F N))
    (x : Subgroup.normalizer (W.subgroup : Set (Spin n F N))) : K :=
  W.localCharacter
    (QuotientGroup.mk'
      (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set (Spin n F N)))) x)

/-- The actual normalizer inertia. Inverse right twist is the usual
left conjugation action; all subgroup and character maps are computed.
The second conjunct expands to literal subgroup equality and the local
normalizer-quotient character equality, as recorded below. -/
def normalizerInertia (W : CharacterWeight ell K (Spin n F N)) :
    Set (Ambient S) :=
  {a | a ∈ Subgroup.normalizer (embeddedRadical S W : Set (Ambient S)) ∧
    CharacterWeight.Isomorphic
      (W.rightTwist (ambientSpinAutomorphism S a)⁻¹) W}

/-- There is no unspecified local-character action in `normalizerInertia`.
This is its complete subgroup-and-quotient-character formula. -/
theorem mem_normalizerInertia_iff
    (W : CharacterWeight ell K (Spin n F N)) (a : Ambient S) :
    a ∈ normalizerInertia S W ↔
      a ∈ Subgroup.normalizer (embeddedRadical S W : Set (Ambient S)) ∧
      ∃ hR : W.subgroup.comap ((ambientSpinAutomorphism S a)⁻¹).toMonoidHom =
          W.subgroup,
        CharacterWeight.castLocalCharacter hR
          (OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
            (rightNormalizerQuotientEquiv
              (ambientSpinAutomorphism S a)⁻¹ W.subgroup).symm) =
          W.localCharacter := Iff.rfl

/-- The first factor of the published product, embedded into `Gtilde D`. -/
def specialCliffordInertia (W : CharacterWeight ell K (Spin n F N)) :
    Set (Ambient S) :=
  normalizerInertia S W ∩
    (SemidirectProduct.inl : SpecialClifford n F →* Ambient S).range

/-- The second factor, using the actual embedded `G D`. -/
def spinFieldInertia (W : CharacterWeight ell K (Spin n F N)) :
    Set (Ambient S) :=
  normalizerInertia S W ∩ (spinFieldEmbedding S).range

/-- Exact E2 boundary for FLZ Proposition 7.5, pp. 573--574.
The odd field hypotheses occur in `S`'s fixed `parameters`; all remaining
numerical hypotheses are actual fields, so they cannot disappear through
unused section-variable elaboration. The factorization is the published
input, not a theorem established by this file. -/
structure Theorem75Source : Prop where
  rank : 3 ≤ n
  ellPrime : Nat.Prime ell
  ellOdd : Odd ell
  nondefining : ell ≠ p
  splitting : IsAlgClosed K
  factorization : ∀ W : CharacterWeight ell K (Spin n F N),
    normalizerInertia S W = specialCliffordInertia S W * spinFieldInertia S W

/-- Read the source product equality as actual ambient factors. This
elementary extraction is the only deduction from the E2 certificate. -/
theorem exists_normalizer_inertia_factors
    (source : Theorem75Source (K := K) (ell := ell) S)
    (W : CharacterWeight ell K (Spin n F N))
    (a : Ambient S) (ha : a ∈ normalizerInertia S W) :
    ∃ m : SpecialClifford n F, ∃ ge : SpinField S,
      SemidirectProduct.inl m ∈ normalizerInertia S W ∧
      spinFieldEmbedding S ge ∈ normalizerInertia S W ∧
      (SemidirectProduct.inl m : Ambient S) * spinFieldEmbedding S ge = a := by
  rw [source.factorization W] at ha
  rcases Set.mem_mul.mp ha with ⟨x, hx, y, hy, hxy⟩
  rcases hx.2 with ⟨m, hm⟩
  rcases hy.2 with ⟨ge, hge⟩
  refine ⟨m, ge, ?_, ?_, ?_⟩
  · simpa only [hm] using hx.1
  · simpa only [hge] using hy.1
  · simpa only [hm, hge] using hxy

end ModularRep.PaperProofs.TypeBWeightStabilizerSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
