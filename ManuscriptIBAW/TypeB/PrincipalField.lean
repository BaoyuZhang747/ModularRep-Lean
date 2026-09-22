import ModularRep.PaperProofs.TypeBCurrentPrincipalResults

/-!
# The trivial component action in Lemma 4.7

Taylor's rational basepoint and the Malle–Testerman parametrisation use
ordinary conjugacy classes of the component group. We assume an equivariant
parametrisation and trivial action on the component group. These assumptions
imply fixedness of rational classes, without a separate fixedness hypothesis.
Commutativity is not required, so extraspecial component groups are allowed.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.PrincipalField

open ModularRep ModularRep.PaperProofs
open TypeBRationalFieldLemma411Relative TypeBCliffordCarriers
open TypeBSpinRationalUnipotentClassBinding TypeBCurrentPrincipalResults
open TypeBLemma411Proposition412LiteralHandoff
open TypeBSpinGGGRPrincipalSeriesBinding

/-- External assumptions for the rational class parametrisation, using
Taylor 2013 Section 2 and Malle–Testerman 21.11. The parametrisation is
assumed equivariant, and `frobenius_trivial` specifies trivial component action.
Together these fields imply fixedness of rational classes. Fixedness is not
a separate field. The algebraic interpretation of the component group remains
an explicit structural assumption. -/
structure OrdinaryParameterSource {A E R : Type} [Group A] [Group E]
    [MulAction E R] where
  frobenius : MulAut A
  frobenius_trivial : frobenius = 1
  exponent : E → ℕ
  parameter : R ≃ ConjClasses A
  naturality : ∀ e x a, parameter x = ConjClasses.mk a →
    parameter (e • x) = ConjClasses.mk ((frobenius ^ exponent e) a)

/-- Convert the source on ordinary conjugacy classes to the form using twisted
conjugacy classes. Both parameter sets describe the same classes. -/
def OrdinaryParameterSource.toInner {A E R : Type} [Group A] [Group E]
    [MulAction E R] (D : OrdinaryParameterSource (A := A) (E := E) (R := R))
    (f : ℕ) : RationalClassParametrisation (E := E) (RationalClass := R) (1 : A) f where
  fieldExponent := D.exponent
  parameter := D.parameter.trans (untwistClassEquiv (1 : A) f).symm
  parameter_smul e x := by
    rw [fieldClassMap_eq_self]
    apply (untwistClassEquiv (1 : A) f).injective
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    obtain ⟨a, ha⟩ := ConjClasses.mk_surjective (D.parameter x)
    have h := D.naturality e x a ha.symm
    simp only [D.frobenius_trivial, one_pow, MulAut.one_apply] at h
    exact h.trans ha

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (OrdinaryIrreducibleCharacter.Irr K (Spin n F N))]
  {parameters : OddFieldParameters F r f} {rank : 3 ≤ n}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]

/-- The field sources concern the same specified GGGR functions as the rank
argument. Taylor 2018 Proposition 11.10 uses left pullback. The theorem
proves its conversion to the right action in the manuscript. -/
structure Sources (D : GGGRContext parameters rank Msys iota b)
    (S : FieldActionSource n F r f parameters N) where
  geometricStable : GeometricFieldStable parameters S D.geometricClass
  parameter :
    letI : ∀ C, MulAction (FieldGroup f) (RationalFibre D.geometricClass C) :=
      fun C => rationalFibreFieldAction parameters S D.geometricClass geometricStable C
    ∀ C, OrdinaryParameterSource (A := D.ComponentGroup C)
      (E := FieldGroup f) (R := RationalFibre D.geometricClass C)
  taylorEquivariant :
    letI := unipotentClassFieldAction parameters S
    letI := taylorFunctionFieldAction (K := K) (spinRightFieldHom parameters S)
    ∀ (e : FieldGroup f) (c : UnipotentClass (r := r) (N := N)),
      e • D.gamma c = D.gamma (e • c)

def Sources.toLegacy {D : GGGRContext parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Sources D S) :
    FieldSources D S where
  geometricStable := source.geometricStable
  inner := fun _ => 1
  rational := {
    parameter := by
      letI : ∀ C, MulAction (FieldGroup f) (RationalFibre D.geometricClass C) :=
        fun C => rationalFibreFieldAction parameters S D.geometricClass source.geometricStable C
      exact fun C => (source.parameter C).toInner f
    gamma := D.gamma
    taylorEquivariant := source.taylorEquivariant }
  gamma_eq := rfl

omit [Finite (SpecialClifford n F)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
theorem rationalClass_fixed {D : GGGRContext parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Sources D S)
    (e : FieldGroup f) (c : UnipotentClass (r := r) (N := N)) :
    letI := unipotentClassFieldAction parameters S
    e • c = c :=
  TypeBCurrentPrincipalResults.rationalClass_fixed source.toLegacy.rational e c

omit [Finite (SpecialClifford n F)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
theorem gggr_fixed {D : GGGRContext parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Sources D S)
    (e : FieldGroup f) (c : UnipotentClass (r := r) (N := N)) :
    TypeBPrincipalSelectorCorollary413SourceInstantiation.functionTwistLinearEquiv
      (K := K) (spinFieldAction n F S e) (D.gamma c) = D.gamma c :=
  TypeBCurrentPrincipalResults.gggr_fixed source.toLegacy.rational e c

end ManuscriptIBAW.TypeB.PrincipalField

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
