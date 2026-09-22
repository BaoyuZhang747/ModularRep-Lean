import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic

/-!
# Paper proof: rational unipotent classes and field automorphisms in type B

This file checks the manuscript-specific finite group deduction in Lemma 4.7.
The standard parametrisation of rational classes by twisted conjugacy classes,
and the fact that the field action on the component group is inner, remain
source inputs.  Lean checks the untwisting map, the induced field-action
calculation, the conversion from Taylor's left character action to the
manuscript's right action, and the resulting GGGR fixation.

No algebraic-group fixed-point theorem, type classification, GGGR
construction, BAW statement, or iBAW statement is encoded here.
-/

namespace ModularRep.PaperProofs.TypeBRationalFieldLemma411Relative

universe uA uE uR uC

section TwistedConjugacy

variable {A : Type uA} [Group A]

/-- If the component-group action is `Int(c)`, its `f`th iterate is
conjugation by `c^f`. -/
theorem innerAutomorphism_pow_apply (c g : A) (f : ℕ) :
    ((MulAut.conj c) ^ f) g = c ^ f * g * (c ^ f)⁻¹ := by
  rw [← map_pow]
  exact MulAut.conj_apply (c ^ f) g

/-- The `Int(c)^f`-twisted conjugacy relation in the convention used by
Malle--Testerman and by the manuscript:

`y = Int(c)^f(g) * x * g⁻¹`.

Writing the iterate explicitly keeps the multiplication orientation visible.
-/
def InnerTwistedConj (c : A) (f : ℕ) (x y : A) : Prop :=
  ∃ g : A, y = (c ^ f * g * (c ^ f)⁻¹) * x * g⁻¹

theorem innerTwistedConj_refl (c : A) (f : ℕ) (x : A) :
    InnerTwistedConj c f x x := by
  refine ⟨1, ?_⟩
  simp

theorem innerTwistedConj_symm (c : A) (f : ℕ) {x y : A} :
    InnerTwistedConj c f x y → InnerTwistedConj c f y x := by
  rintro ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  group

theorem innerTwistedConj_trans (c : A) (f : ℕ) {x y z : A} :
    InnerTwistedConj c f x y → InnerTwistedConj c f y z →
      InnerTwistedConj c f x z := by
  rintro ⟨g, rfl⟩ ⟨h, rfl⟩
  refine ⟨h * g, ?_⟩
  group

/-- The setoid of `Int(c)^f`-twisted conjugacy classes. -/
def innerTwistedConjSetoid (c : A) (f : ℕ) : Setoid A where
  r := InnerTwistedConj c f
  iseqv := ⟨innerTwistedConj_refl c f,
    innerTwistedConj_symm c f, innerTwistedConj_trans c f⟩

/-- The parameter set for the rational classes in the source-shaped form used
by Lemma 4.7. -/
def InnerTwistedClasses (c : A) (f : ℕ) : Type uA :=
  Quotient (innerTwistedConjSetoid c f)

/-- The class of a concrete component-group parameter. -/
def twistedClassMk (c : A) (f : ℕ) (x : A) : InnerTwistedClasses c f :=
  Quotient.mk (innerTwistedConjSetoid c f) x

/-- Multiplication by `c⁻f` untwists `Int(c)^f`-conjugacy. -/
def untwist (c : A) (f : ℕ) (x : A) : A :=
  (c ^ f)⁻¹ * x

/-- The pointwise calculation underlying the manuscript's untwisting map. -/
theorem innerTwistedConj_iff_isConj_untwist (c : A) (f : ℕ) (x y : A) :
    InnerTwistedConj c f x y ↔ IsConj (untwist c f x) (untwist c f y) := by
  constructor
  · rintro ⟨g, rfl⟩
    rw [isConj_iff]
    refine ⟨g, ?_⟩
    simp only [untwist]
    group
  · intro h
    rw [isConj_iff] at h
    rcases h with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    simp only [untwist] at hg
    calc
      y = c ^ f * ((c ^ f)⁻¹ * y) := by group
      _ = c ^ f * (g * ((c ^ f)⁻¹ * x) * g⁻¹) := by rw [hg]
      _ = (c ^ f * g * (c ^ f)⁻¹) * x * g⁻¹ := by group

/-- The untwisting map on classes. -/
def untwistClassMap (c : A) (f : ℕ) :
    InnerTwistedClasses c f → ConjClasses A :=
  Quotient.lift
    (fun x ↦ ConjClasses.mk (untwist c f x))
    (fun _ _ h ↦ ConjClasses.mk_eq_mk_iff_isConj.mpr
      ((innerTwistedConj_iff_isConj_untwist c f _ _).mp h))

theorem untwistClassMap_mk (c : A) (f : ℕ) (x : A) :
    untwistClassMap c f (twistedClassMk c f x) =
      ConjClasses.mk (untwist c f x) := by
  rfl

theorem untwistClassMap_injective (c : A) (f : ℕ) :
    Function.Injective (untwistClassMap c f) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ x =>
      induction r using Quotient.inductionOn with
      | _ y =>
          apply Quotient.sound
          exact (innerTwistedConj_iff_isConj_untwist c f x y).mpr
            (ConjClasses.mk_eq_mk_iff_isConj.mp hqr)

theorem untwistClassMap_surjective (c : A) (f : ℕ) :
    Function.Surjective (untwistClassMap c f) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ x =>
      refine ⟨twistedClassMk c f (c ^ f * x), ?_⟩
      rw [untwistClassMap_mk]
      change ConjClasses.mk (untwist c f (c ^ f * x)) = ConjClasses.mk x
      congr 1
      simp only [untwist]
      group

/-- The class-level bijection `[x]_{Int(c)^f} ↦ [c⁻f x]`. -/
noncomputable def untwistClassEquiv (c : A) (f : ℕ) :
    InnerTwistedClasses c f ≃ ConjClasses A :=
  Equiv.ofBijective (untwistClassMap c f)
    ⟨untwistClassMap_injective c f, untwistClassMap_surjective c f⟩

/-- The action of the `e`th field power on a component-group parameter. -/
def innerFieldPower (c : A) (e : ℕ) (x : A) : A :=
  c ^ e * x * (c ^ e)⁻¹

/-- Inner field powers preserve `Int(c)^f`-twisted conjugacy. -/
theorem innerFieldPower_preserves_twistedConj (c : A) (f e : ℕ) {x y : A}
    (hxy : InnerTwistedConj c f x y) :
    InnerTwistedConj c f (innerFieldPower c e x) (innerFieldPower c e y) := by
  rcases hxy with ⟨g, rfl⟩
  refine ⟨c ^ e * g * (c ^ e)⁻¹, ?_⟩
  simp only [innerFieldPower]
  group

/-- The field action induced on the twisted parameter set. -/
def fieldClassMap (c : A) (f e : ℕ) :
    InnerTwistedClasses c f → InnerTwistedClasses c f :=
  Quotient.map (innerFieldPower c e)
    (fun _ _ h ↦ innerFieldPower_preserves_twistedConj c f e h)

theorem fieldClassMap_mk (c : A) (f e : ℕ) (x : A) :
    fieldClassMap c f e (twistedClassMk c f x) =
      twistedClassMk c f (innerFieldPower c e x) := by
  rfl

/-- After untwisting, the `e`th field image is conjugate by `c^e` to the
original parameter.  This is the calculation in the manuscript proof. -/
theorem untwist_innerFieldPower_isConj (c : A) (f e : ℕ) (x : A) :
    IsConj (untwist c f x) (untwist c f (innerFieldPower c e x)) := by
  rw [isConj_iff]
  refine ⟨c ^ e, ?_⟩
  simp only [untwist, innerFieldPower]
  group

theorem untwistClassMap_fieldClassMap (c : A) (f e : ℕ)
    (q : InnerTwistedClasses c f) :
    untwistClassMap c f (fieldClassMap c f e q) = untwistClassMap c f q := by
  induction q using Quotient.inductionOn with
  | _ x =>
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr
        (untwist_innerFieldPower_isConj c f e x).symm

/-- Every inner field power acts trivially on the twisted parameter set. -/
theorem fieldClassMap_eq_self (c : A) (f e : ℕ)
    (q : InnerTwistedClasses c f) :
    fieldClassMap c f e q = q := by
  apply untwistClassMap_injective c f
  exact untwistClassMap_fieldClassMap c f e q

end TwistedConjugacy

section RationalClasses

variable {A : Type uA} [Group A]
variable {E : Type uE} [Group E]
variable {RationalClass : Type uR} [MulAction E RationalClass]

/-- The exact adapter from the standard fixed-point parametrisation to the
finite twisted-conjugacy calculation.  `fieldExponent sigma` records the fact
that the field automorphism `sigma` is induced by a power of `F₀`.

The existence and naturality of `parameter` are source-backed fixed-point
inputs.  The fixedness conclusion is not a field of this structure. -/
structure RationalClassParametrisation (c : A) (f : ℕ) where
  fieldExponent : E → ℕ
  parameter : RationalClass ≃ InnerTwistedClasses c f
  parameter_smul : ∀ sigma r,
    parameter (sigma • r) = fieldClassMap c f (fieldExponent sigma) (parameter r)

namespace RationalClassParametrisation

/-- The manuscript-specific consequence: every field automorphism fixes every
rational class once its component-group action is inner. -/
theorem smul_eq_self
    {c : A} {f : ℕ}
    (D : RationalClassParametrisation
      (E := E) (RationalClass := RationalClass) c f)
    (sigma : E) (r : RationalClass) :
    sigma • r = r := by
  apply D.parameter.injective
  rw [D.parameter_smul]
  exact fieldClassMap_eq_self c f (D.fieldExponent sigma) (D.parameter r)

end RationalClassParametrisation

end RationalClasses

section ClassFunctionOrientation

variable {G : Type*} [Group G] {Value : Type*}

/-- Taylor's left transport of a class function: `sigma chi = chi o sigma⁻¹`. -/
def taylorLeftTransport (sigma : MulAut G) (chi : G → Value) : G → Value :=
  fun x ↦ chi (sigma.symm x)

/-- The manuscript's right transport of a class function:
`chi^sigma = chi o sigma`. -/
def manuscriptRightTransport (sigma : MulAut G) (chi : G → Value) : G → Value :=
  fun x ↦ chi (sigma x)

/-- The two published conventions agree after inverting the automorphism. -/
theorem manuscriptRightTransport_eq_taylorLeftTransport_inv
    (sigma : MulAut G) (chi : G → Value) :
    manuscriptRightTransport sigma chi = taylorLeftTransport sigma⁻¹ chi := by
  rfl

end ClassFunctionOrientation

section GGGRTransfer

variable {E : Type uE} [Group E]
variable {RationalClass : Type uR} [MulAction E RationalClass]
variable {Character : Type uC} [MulAction E Character]

/-- Taylor uses the left action `sigma • chi = chi ∘ sigma⁻¹`.  Therefore
the manuscript's right action by `sigma` is Taylor's left action by
`sigma⁻¹`. -/
def manuscriptRightAction (sigma : E) (chi : Character) : Character :=
  sigma⁻¹ • chi

/-- Conversion of Taylor's GGGR equivariance to the manuscript's right-action
orientation. -/
theorem manuscriptRightAction_gamma
    (gamma : RationalClass → Character)
    (taylorEquivariant : ∀ (sigma : E) (r : RationalClass),
      sigma • gamma r = gamma (sigma • r))
    (sigma : E) (r : RationalClass) :
    manuscriptRightAction sigma (gamma r) = gamma (sigma⁻¹ • r) := by
  exact taylorEquivariant sigma⁻¹ r

/-- Transfer from pointwise fixation of rational classes to pointwise fixation
of the corresponding GGGRs under the manuscript's right action. -/
theorem manuscriptRightAction_gamma_eq_self
    (gamma : RationalClass → Character)
    (taylorEquivariant : ∀ (sigma : E) (r : RationalClass),
      sigma • gamma r = gamma (sigma • r))
    (rationalClassFixed : ∀ (sigma : E) (r : RationalClass), sigma • r = r)
    (sigma : E) (r : RationalClass) :
    manuscriptRightAction sigma (gamma r) = gamma r := by
  rw [manuscriptRightAction_gamma gamma taylorEquivariant]
  exact congrArg gamma (rationalClassFixed sigma⁻¹ r)

/-- Source-shaped endpoint for Lemma 4.7.  The rational-class fixedness is
derived from the twisted-conjugacy parametrisation, and Taylor's GGGR
equivariance is then transported through the explicitly checked right-action
conversion. -/
theorem lemma_4_11_relative
    {A : Type uA} [Group A]
    {c : A} {f : ℕ}
    (D : RationalClassParametrisation
      (E := E) (RationalClass := RationalClass) c f)
    (gamma : RationalClass → Character)
    (taylorEquivariant : ∀ (sigma : E) (r : RationalClass),
      sigma • gamma r = gamma (sigma • r)) :
    (∀ (sigma : E) (r : RationalClass), sigma • r = r) ∧
      (∀ (sigma : E) (r : RationalClass),
        manuscriptRightAction sigma (gamma r) = gamma r) := by
  have hfixed : ∀ (sigma : E) (r : RationalClass), sigma • r = r :=
    D.smul_eq_self
  exact ⟨hfixed,
    manuscriptRightAction_gamma_eq_self gamma taylorEquivariant hfixed⟩

end GGGRTransfer

end ModularRep.PaperProofs.TypeBRationalFieldLemma411Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
