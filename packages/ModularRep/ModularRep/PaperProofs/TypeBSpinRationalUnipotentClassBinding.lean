import ModularRep.PaperProofs.TypeBSpinGGGRPrincipalSeriesBinding
import ModularRep.PaperProofs.TypeBIndexedRationalFieldHandoff

/-!
# Actual rational unipotent class carriers for finite Spin

The carrier consists of actual Spin conjugacy classes containing an element
annihilated by a power of the defining prime. On algebraic finite points these
are the unipotent classes; the algebraic/Clifford realization remains an E1/U
identification. The field action is constructed from the same actual Spin
automorphisms, never supplied as an arbitrary action or as class fixation.

A geometric label still requires its literal algebraic interpretation.
Its field stability only restricts the action to each geometric fibre.
The later Malle--Testerman source must act on these exact fibres.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinRationalUnipotentClassBinding

open ModularRep TypeBCliffordCarriers

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} [Finite (Spin n F N)]

/-- Literal defining-prime element classes in the actual finite Spin group. -/
def UnipotentClass : Type :=
  {c : ConjClasses (Spin n F N) //
    ∃ g : Spin n F N, ConjClasses.mk g = c ∧ ∃ a : ℕ, g ^ (r ^ a) = 1}

instance unipotentClass_finite : Finite (UnipotentClass (r := r) (N := N)) := by
  letI : Finite (ConjClasses (Spin n F N)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold UnipotentClass
  infer_instance

/-- The actual class of an element whose order divides a defining-prime power. -/
def unipotentClassMk (g : Spin n F N) (a : ℕ) (power : g ^ (r ^ a) = 1) :
    UnipotentClass (r := r) (N := N) :=
  ⟨ConjClasses.mk g, g, rfl, a, power⟩

variable (parameters : OddFieldParameters F r f)
  (S : FieldActionSource n F r f parameters N)

/-- Pushforward of actual conjugacy classes by the positive field actor. -/
def conjugacyClassFieldAction : MulAction (FieldGroup f) (ConjClasses (Spin n F N)) where
  smul e c := ConjClasses.map (spinFieldAction n F S e).toMonoidHom c
  one_smul c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (spinFieldAction n F S 1 g) = ConjClasses.mk g
    rw [map_one]
    rfl
  mul_smul e d c := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    change ConjClasses.mk (spinFieldAction n F S (e * d) g) =
      ConjClasses.mk (spinFieldAction n F S e (spinFieldAction n F S d g))
    rw [map_mul]
    rfl

/-- Defining-prime power equations are preserved by actual field automorphisms. -/
def unipotentClassFieldAction :
    MulAction (FieldGroup f) (UnipotentClass (r := r) (N := N)) := by
  letI := conjugacyClassFieldAction parameters S
  exact
    { smul := fun e c => ⟨e • c.val, by
        obtain ⟨g, hg, a, ha⟩ := c.property
        refine ⟨spinFieldAction n F S e g, ?_, a, ?_⟩
        · change ConjClasses.mk (spinFieldAction n F S e g) =
            ConjClasses.map (spinFieldAction n F S e).toMonoidHom c.val
          rw [← hg]
          rfl
        · rw [← map_pow, ha, map_one]⟩
      one_smul := fun c => Subtype.ext (one_smul (FieldGroup f) c.val)
      mul_smul := fun e d c => Subtype.ext (mul_smul e d c.val) }

@[simp] theorem unipotentClassFieldAction_val
    (e : FieldGroup f) (c : UnipotentClass (r := r) (N := N)) :
    letI := unipotentClassFieldAction parameters S
    (e • c).val = ConjClasses.map (spinFieldAction n F S e).toMonoidHom c.val := rfl

variable {GeometricClass : Type}
  (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)

/-- A fibre of actual rational classes belonging to one geometric class. -/
abbrev RationalFibre (C : GeometricClass) :=
  {c : UnipotentClass (r := r) (N := N) // geometricClass c = C}

/-- This is stability of the geometric label only, not fixation of any
rational Spin class. Its algebraic label interpretation is an E1/U input. -/
def GeometricFieldStable : Prop :=
  letI := unipotentClassFieldAction parameters S
  ∀ (e : FieldGroup f) (c : UnipotentClass (r := r) (N := N)),
    geometricClass (e • c) = geometricClass c

variable (geometricStable : GeometricFieldStable parameters S geometricClass)

/-- The rational-fibre action is restricted from the SAME actual class action. -/
def rationalFibreFieldAction (C : GeometricClass) :
    MulAction (FieldGroup f) (RationalFibre geometricClass C) := by
  letI := unipotentClassFieldAction parameters S
  exact
    { smul := fun e c => ⟨e • c.val, (geometricStable e c.val).trans c.property⟩
      one_smul := fun c => Subtype.ext (one_smul (FieldGroup f) c.val)
      mul_smul := fun e d c => Subtype.ext (mul_smul e d c.val) }

@[simp] theorem rationalFibreFieldAction_val
    (C : GeometricClass) (e : FieldGroup f) (c : RationalFibre geometricClass C) :
    letI := unipotentClassFieldAction parameters S
    letI := rationalFibreFieldAction parameters S geometricClass geometricStable C
    (e • c).val = e • c.val := rfl

/-- Counting indices via an actual exhaustive enumeration of the rational
unipotent class carrier. An abstract number is not itself such an enumeration. -/
theorem card_eq_of_classIndex {m : ℕ}
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)) :
    m = Nat.card (UnipotentClass (r := r) (N := N)) := by
  simpa using Nat.card_congr classIndex


section IndexedGGGR

open TypeBSpinGGGRPrincipalSeriesBinding
open TypeBRationalFieldLemma411Relative
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBGGGRRankProposition412SourceInstantiation
open TypeBIndexedRationalFieldHandoff
open TypeBLemma411Proposition412LiteralHandoff

variable {K : Type} [Field K] [CharZero K]

/-- Per-geometric-class source data on the actual rational fibres.
Malle--Testerman and Taylor must be realized on these exact carriers, with
the same positive field action. No field-fixedness or basis is a field. -/
structure RationalGGGRSource
    (parameters : OddFieldParameters F r f)
    (rank : 3 ≤ n) (S : FieldActionSource n F r f parameters N)
    (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
    (geometricStable : GeometricFieldStable parameters S geometricClass)
    (ComponentGroup : GeometricClass → Type)
    [∀ C, Group (ComponentGroup C)] (inner : ∀ C, ComponentGroup C) where
  parameter :
    letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
      fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
    ∀ C, RationalClassParametrisation
      (E := FieldGroup f) (RationalClass := RationalFibre geometricClass C) (inner C) f
  gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K
  taylorEquivariant :
    letI := unipotentClassFieldAction parameters S
    letI := taylorFunctionFieldAction (K := K) (spinRightFieldHom parameters S)
    ∀ (e : FieldGroup f) (c : UnipotentClass (r := r) (N := N)),
      e • gamma c = gamma (e • c)

variable (rank : 3 ≤ n) (ComponentGroup : GeometricClass → Type)
  [∀ C, Group (ComponentGroup C)] (inner : ∀ C, ComponentGroup C)
  (source : RationalGGGRSource (K := K) parameters rank S geometricClass geometricStable
    ComponentGroup inner)

/-- Construct the former indexed handoff using an exhaustive enumeration
of the actual Spin rational classes and the SAME literal GGGR functions. -/
def indexedSource {m : ℕ}
    {projectiveSpace : Submodule K (Spin n F N → K)}
    [FiniteDimensional K projectiveSpace]
    (D : GGGRBasisSource m projectiveSpace)
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
    (gggr_eq : ∀ j, D.gggr j = source.gamma (classIndex j)) :
    letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
      fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
    IndexedLiteralLemma411Source ComponentGroup (RationalFibre geometricClass)
      (spinRightFieldHom parameters S) D inner f := by
  letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
    fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
  exact
    { parameter := source.parameter
      gamma := fun _ c => source.gamma c.val
      taylorEquivariant := fun _ e c => source.taylorEquivariant e c.val
      geometricClassOfIndex := fun j => geometricClass (classIndex j)
      rationalClassOfIndex := fun j => ⟨classIndex j, rfl⟩
      gggr_eq_gamma := gggr_eq }

/-- Actual full-GGGR fixation from the constructed indexed source.
The positive automorphism on the function argument is displayed literally. -/
theorem gggr_fixed {m : ℕ}
    {projectiveSpace : Submodule K (Spin n F N → K)}
    [FiniteDimensional K projectiveSpace]
    (D : GGGRBasisSource m projectiveSpace)
    (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
    (gggr_eq : ∀ j, D.gggr j = source.gamma (classIndex j))
    (e : FieldGroup f) (j : Fin m) :
    functionTwistLinearEquiv (K := K) (spinFieldAction n F S e) (D.gggr j) =
      D.gggr j := by
  letI : ∀ C, MulAction (FieldGroup f) (RationalFibre geometricClass C) :=
    fun C => rationalFibreFieldAction parameters S geometricClass geometricStable C
  simpa only [spinRightFieldHom_unop] using
    (indexedSource parameters S geometricClass geometricStable rank ComponentGroup inner
      source D classIndex gggr_eq).gggr_fixed e j

end IndexedGGGR


end ModularRep.PaperProofs.TypeBSpinRationalUnipotentClassBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
