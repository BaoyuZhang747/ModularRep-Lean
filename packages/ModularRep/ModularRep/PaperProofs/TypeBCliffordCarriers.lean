import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Literal Clifford carriers for the Type B moving window

The quadratic space is the split odd-dimensional space of Feng--Li--Zhang,
J. Algebra 604 (2022), Section 2.5, equation (2.5), pp. 539--540.  Its
special Clifford group is defined by the displayed normalizer definition in
that section, and its Spin subgroup is the kernel of the displayed norm.

We do not identify this normalizer with Mathlib's `spinGroup`: the latter
uses a generated Lipschitz group, and its documentation explicitly leaves
the converse normalizer identification as a TODO.

The E1 source boundary consists of finiteness of this particular Clifford
algebra, existence of its scalar-valued norm with the literal reversal
formula, and prime Frobenius on this algebra and its two subgroups.  These
are standard structural statements, not character, block, or weight inputs.
The finite-field cardinality and characteristic parameters remain explicit.
There are no arbitrary group carriers or target predicates in this file.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBCliffordCarriers

universe u

/-- Coordinates for the ordered basis `epsilon_0, epsilon_i, eta_i`.
The order is immaterial to the defining quadratic form. -/
abbrev Coordinate (n : ℕ) := Option (Fin n ⊕ Fin n)

/-- The literal vector space of dimension `2*n+1`. -/
abbrev Vector (n : ℕ) (F : Type u) := Coordinate n → F

variable (n : ℕ) (F : Type u) [Field F]

/-- FLZ equation (2.5): `x_0^2 + sum_i x_i*y_i`. -/
def splitForm : QuadraticForm F (Vector n F) :=
  QuadraticMap.proj none none +
    ∑ i : Fin n,
      QuadraticMap.proj (some (Sum.inl i)) (some (Sum.inr i))

@[simp]
theorem splitForm_apply (v : Vector n F) :
    splitForm n F v = v none * v none +
      ∑ i : Fin n, v (some (Sum.inl i)) * v (some (Sum.inr i)) := by
  simp [splitForm, QuadraticMap.proj_apply]

/-- The Clifford algebra of the specified form, not a supplied carrier. -/
abbrev Clifford := CliffordAlgebra (splitForm n F)

/-- Its actual canonical vector image. -/
def vectorImage : Set (Clifford n F) :=
  Set.range (CliffordAlgebra.ι (splitForm n F))

/-- Units of the actual even subalgebra, viewed inside the full unit group. -/
def evenUnits : Subgroup (Clifford n F)ˣ :=
  (Units.map (CliffordAlgebra.even (splitForm n F)).val.toMonoidHom).range

/-- The exact setwise normalizer `g*V*g^-1 = V`.  Taking a stabilizer makes
both directions of preservation part of the definition. -/
def vectorNormalizer : Subgroup (Clifford n F)ˣ :=
  (MulAction.stabilizer (ConjAct (Clifford n F)ˣ) (vectorImage n F)).comap
    ConjAct.toConjAct.toMonoidHom

/-- FLZ Section 2.5's special Clifford group `D_0(V)`. -/
def specialCliffordSubgroup : Subgroup (Clifford n F)ˣ :=
  evenUnits n F ⊓ vectorNormalizer n F

/-- The finite special Clifford carrier after the explicit E1 finiteness
input below is installed. -/
abbrev SpecialClifford := specialCliffordSubgroup n F

/-- The inclusion in the Clifford unit group. -/
def toCliffordUnit : SpecialClifford n F →* (Clifford n F)ˣ :=
  (specialCliffordSubgroup n F).subtype

/-- The underlying Clifford-algebra element of a group element. -/
def toClifford : SpecialClifford n F →* Clifford n F :=
  (Units.coeHom (Clifford n F)).comp (toCliffordUnit n F)

theorem toClifford_injective : Function.Injective (toClifford n F) :=
  Units.val_injective.comp Subtype.val_injective

/-- Membership records the source's even-unit and setwise-normalizer clauses. -/
theorem specialClifford_membership (g : SpecialClifford n F) :
    g.1 ∈ evenUnits n F ∧
      ConjAct.toConjAct g.1 • vectorImage n F = vectorImage n F := by
  exact ⟨g.2.1, g.2.2⟩

/-- Parameters for the source finite field `F_(p^f)`.  The endpoint must keep
`CharP F p` together with this record; a name alone is not a field binding. -/
structure OddFieldParameters (p f : ℕ) [Finite F] [CharP F p] : Prop where
  prime : Nat.Prime p
  odd : Odd p
  exponent_pos : 0 < f
  cardinality : Nat.card F = p ^ f

/-- E1: the finite-dimensional Clifford algebra over this finite field is
finite.  Canonical source: the explicit `2^(2*n+1)` monomial basis in FLZ
Section 2.5, p. 539 (Chevalley, *The Algebraic Theory of Spinors*, II.1).
No arbitrary finite group is substituted for the algebra. -/
structure FiniteCliffordSource [Finite F] : Prop where
  finite_algebra : Finite (Clifford n F)

theorem specialClifford_finite [Finite F]
    (S : FiniteCliffordSource n F) : Finite (SpecialClifford n F) := by
  let : Finite (Clifford n F) := S.finite_algebra
  infer_instance

/-- E1: the source norm on this exact normalizer.  Its defining value is
`g * reverse(g)`, as in FLZ Section 2.5, p. 540.  In particular, this input
does not merely assert that some subgroup happens to be called Spin. -/
structure NormSource where
  norm : SpecialClifford n F →* Fˣ
  value : ∀ g : SpecialClifford n F,
    algebraMap F (Clifford n F) (norm g : F) =
      toClifford n F g * CliffordAlgebra.reverse (toClifford n F g)

/-- FLZ's literal `Spin(V) = ker N`, as a normal subgroup of `D_0(V)`. -/
def SpinSubgroup (N : NormSource n F) : Subgroup (SpecialClifford n F) :=
  N.norm.ker

/-- The Spin carrier attached to the same quadratic form and norm. -/
abbrev Spin (N : NormSource n F) := SpinSubgroup n F N

instance spinSubgroup_normal (N : NormSource n F) :
    (SpinSubgroup n F N).Normal :=
  inferInstanceAs N.norm.ker.Normal

@[simp]
theorem mem_spinSubgroup_iff (N : NormSource n F) (g : SpecialClifford n F) :
    g ∈ SpinSubgroup n F N ↔ N.norm g = 1 :=
  Iff.rfl

theorem spin_reverse_product (N : NormSource n F) (g : Spin n F N) :
    toClifford n F g.1 * CliffordAlgebra.reverse (toClifford n F g.1) = 1 := by
  rw [← N.value g.1]
  rw [show N.norm g.1 = 1 from g.2]
  simp

/-- The literal cyclic field group, with addition in `ZMod f` written
multiplicatively.  For positive `f` it is finite and cyclic. -/
abbrev FieldGroup (f : ℕ) := Multiplicative (ZMod f)

/-- The distinguished prime Frobenius generator. -/
def fieldGenerator (f : ℕ) : FieldGroup f :=
  Multiplicative.ofAdd (1 : ZMod f)

/-- E1: Frobenius on the exact Clifford algebra and its special Clifford
group.  FLZ Section 3.1, p. 541, with the standard `p`-Frobenius of
Section 3.5, p. 546.  The ring automorphism is fixed on scalars and on every vector;
the group action is bound to that same automorphism at the cyclic generator.
The norm naturality is the source formula `N(F_p(g))=F_p(N(g))` and its
powers.  It implies Spin invariance below rather than assuming it. -/
structure FieldActionSource (p f : ℕ) [Finite F] [CharP F p]
    (parameters : OddFieldParameters F p f) (N : NormSource n F) where
  algebraFrobenius : Clifford n F ≃+* Clifford n F
  on_scalar : ∀ a : F,
    algebraFrobenius (algebraMap F (Clifford n F) a) =
      algebraMap F (Clifford n F) (a ^ p)
  on_vector : ∀ v : Vector n F,
    algebraFrobenius (CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n F) (fun i => v i ^ p)
  action : FieldGroup f →* MulAut (SpecialClifford n F)
  action_generator : ∀ g : SpecialClifford n F,
    toClifford n F (action (fieldGenerator f) g) =
      algebraFrobenius (toClifford n F g)
  scalarAction : FieldGroup f →* MulAut Fˣ
  scalar_generator : ∀ z : Fˣ,
    (scalarAction (fieldGenerator f) z : F) = (z : F) ^ p
  norm_natural : ∀ (e : FieldGroup f) (g : SpecialClifford n F),
    N.norm (action e g) = scalarAction e (N.norm g)

theorem field_preserves_spin {p f : ℕ} [Finite F] [CharP F p]
    {parameters : OddFieldParameters F p f} {N : NormSource n F}
    (S : FieldActionSource n F p f parameters N)
    (e : FieldGroup f) (g : SpecialClifford n F)
    (hg : g ∈ SpinSubgroup n F N) :
    S.action e g ∈ SpinSubgroup n F N := by
  change N.norm (S.action e g) = 1
  rw [S.norm_natural, show N.norm g = 1 from hg, map_one]

/-- The setwise equality needed by the existing tensor-and-field adapter. -/
theorem field_spinSubgroup_map {p f : ℕ} [Finite F] [CharP F p]
    {parameters : OddFieldParameters F p f} {N : NormSource n F}
    (S : FieldActionSource n F p f parameters N) (e : FieldGroup f) :
    (SpinSubgroup n F N).map (S.action e).toMonoidHom =
      SpinSubgroup n F N := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact field_preserves_spin n F S e g hg
  · intro g hg
    refine ⟨S.action e⁻¹ g, field_preserves_spin n F S e⁻¹ g hg, ?_⟩
    change S.action e (S.action e⁻¹ g) = g
    rw [map_inv]
    exact (S.action e).apply_symm_apply g

/-- Restriction of the literal field automorphism to the norm-one carrier. -/
def spinFieldAutomorphism {p f : ℕ} [Finite F] [CharP F p]
    {parameters : OddFieldParameters F p f} {N : NormSource n F}
    (S : FieldActionSource n F p f parameters N) (e : FieldGroup f) :
    MulAut (Spin n F N) where
  toFun g := ⟨S.action e g.1, field_preserves_spin n F S e g.1 g.2⟩
  invFun g := ⟨S.action e⁻¹ g.1, field_preserves_spin n F S e⁻¹ g.1 g.2⟩
  left_inv g := by
    apply Subtype.ext
    change S.action e⁻¹ (S.action e g.1) = g.1
    rw [map_inv]
    exact (S.action e).symm_apply_apply g.1
  right_inv g := by
    apply Subtype.ext
    change S.action e (S.action e⁻¹ g.1) = g.1
    rw [map_inv]
    exact (S.action e).apply_symm_apply g.1
  map_mul' g h := by
    apply Subtype.ext
    exact (S.action e).map_mul g.1 h.1

/-- The actual field-group homomorphism on the Spin kernel. -/
def spinFieldAction {p f : ℕ} [Finite F] [CharP F p]
    {parameters : OddFieldParameters F p f} {N : NormSource n F}
    (S : FieldActionSource n F p f parameters N) :
    FieldGroup f →* MulAut (Spin n F N) where
  toFun := spinFieldAutomorphism n F S
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change S.action 1 g.1 = g.1
    rw [map_one]
    rfl
  map_mul' e d := by
    apply MulEquiv.ext
    intro g
    apply Subtype.ext
    change S.action (e * d) g.1 = S.action e (S.action d g.1)
    rw [map_mul]
    rfl

@[simp]
theorem spinFieldAction_coe {p f : ℕ} [Finite F] [CharP F p]
    {parameters : OddFieldParameters F p f} {N : NormSource n F}
    (S : FieldActionSource n F p f parameters N)
    (e : FieldGroup f) (g : Spin n F N) :
    (spinFieldAction n F S e g).1 = S.action e g.1 :=
  rfl

end ModularRep.PaperProofs.TypeBCliffordCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
