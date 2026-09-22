import ModularRep.PaperProofs.TypeBCliffordCarriers
import ModularRep.PaperProofs.TypeBConformalDualCarriers
import ModularRep.PaperProofs.TypeBCentralKernelBlockSource
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.CyclicOuterBrauerExtension

/-!
# Selected Spin GGGR characters lie in the specified principal block

The label carrier is the actual projective conformal symplectic group.
The source clauses are global: Bonnafe's adjoint type-C order-four bound,
Cabanes--Enguehard's principal two-series inclusion and preservation of
rational series by normalized Alvis--Curtis duality. Their algebraic
rational-point, Lusztig-series and coefficient realization remains explicit
U at an application; predicate or map names do not establish those identities.

The selected-principal conclusion is derived from the before-duality label.
No rational surjectivity from Sp(F) to PCSp(F), selected-principal source,
basis, fixedness, character-weight correspondence or target predicate is used.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinGGGRPrincipalSeriesBinding

open ModularRep TypeBCliffordCarriers
open TypeBCentralKernelBlockSource
open OrdinaryIrreducibleCharacter

variable {n r f : ℕ} {F k K : Type}
  [Field F] [Finite F] [CharP F r]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]

/-- An actual two-element, stated by a power equation on the literal
projective conformal carrier. -/
def IsTwoElement (s : TypeBConformalDualCarriers.PCSp F n) : Prop :=
  ∃ a : ℕ, s ^ (2 ^ a) = 1

/-- Source data on the literal finite Spin and dual PCSp carriers.
The ordinary selector must be the one bound to specified decomposition
numbers by the application. The predicates and normalized dual map must
be identified with their algebraic sources; no such identification follows
from constructing this record alone. -/
structure PrincipalSeriesCertificate
    (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
    (blockOf : Irr K (Spin n F N) → LiteralPrimitiveBlock k (Spin n F N))
    (principalBlock : LiteralPrimitiveBlock k (Spin n F N))
    (principal : IsPrincipal principalBlock)
    (rationalSeries : TypeBConformalDualCarriers.PCSp F n →
      Irr K (Spin n F N) → Prop)
    (quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop)
    (normalizedDual : Irr K (Spin n F N) → Irr K (Spin n F N)) : Prop where
  /-- Bonnafe (2005), Theorem 5.1/Table 2, p.2335: adjoint type-C
  quasi-isolated semisimple orders are among 1, 2 and 4. The actual
  rational-point identification is retained; no rational Sp lift is used. -/
  quasiIsolated_fourth_power : ∀ s, quasiIsolated s → s ^ 4 = 1
  /-- Cabanes--Enguehard, Theorem21.14, p.341, specialized to the odd-field
  connected reductive type-B source and its SAME specified principal block.
  Only the one-way two-series membership conclusion is retained. -/
  two_series_principal : ∀ s chi,
    IsTwoElement s → rationalSeries s chi → blockOf chi = principalBlock
  /-- Cabanes--Enguehard, Proposition9.8(iv): normalized duality preserves
  the same rational Lusztig series. -/
  normalizedDual_series : ∀ s chi,
    rationalSeries s chi → rationalSeries s (normalizedDual chi)

variable (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
  (blockOf : Irr K (Spin n F N) → LiteralPrimitiveBlock k (Spin n F N))
  (principalBlock : LiteralPrimitiveBlock k (Spin n F N))
  (principal : IsPrincipal principalBlock)
  (rationalSeries : TypeBConformalDualCarriers.PCSp F n →
    Irr K (Spin n F N) → Prop)
  (quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop)
  (normalizedDual : Irr K (Spin n F N) → Irr K (Spin n F N))
  (source : PrincipalSeriesCertificate parameters rank blockOf principalBlock
    principal rationalSeries quasiIsolated normalizedDual)

include source in
/-- The adjoint order-four certificate supplies an actual two-element;
it does not assert that all relevant elements have order at most two. -/
theorem twoElement_of_quasiIsolated
    (s : TypeBConformalDualCarriers.PCSp F n) (hs : quasiIsolated s) :
    IsTwoElement s := by
  refine ⟨2, ?_⟩
  simpa using source.quasiIsolated_fourth_power s hs

include source in
/-- The manuscript's principal-membership deduction, including the
same rational-series passage through normalized duality. -/
theorem selectedDual_principal
    (s : TypeBConformalDualCarriers.PCSp F n)
    (rho : Irr K (Spin n F N))
    (hs : quasiIsolated s) (hrho : rationalSeries s rho) :
    blockOf (normalizedDual rho) = principalBlock := by
  exact source.two_series_principal s (normalizedDual rho)
    (twoElement_of_quasiIsolated parameters rank blockOf principalBlock principal
      rationalSeries quasiIsolated normalizedDual source s hs)
    (source.normalizedDual_series s rho hrho)

include source in
/-- Apply the derived membership to every before-duality selected character
at its own actual dual label. No selected-principal clause is a source. -/
theorem selectedFamily_principal {I : Type}
    (label : I → TypeBConformalDualCarriers.PCSp F n)
    (rho : I → Irr K (Spin n F N))
    (label_quasiIsolated : ∀ i, quasiIsolated (label i))
    (rho_series : ∀ i, rationalSeries (label i) (rho i)) :
    ∀ i, blockOf (normalizedDual (rho i)) = principalBlock := by
  intro i
  exact selectedDual_principal parameters rank blockOf principalBlock principal
    rationalSeries quasiIsolated normalizedDual source (label i) (rho i)
    (label_quasiIsolated i) (rho_series i)

/-- The positive field automorphism is encoded in an opposite homomorphism.
Commutativity of the actual cyclic field group permits the second inversion.
Taylor's left action then pulls back by the inverse actual automorphism. -/
def spinRightFieldHom
    (S : FieldActionSource n F r f parameters N) :
    FieldGroup f →* (MulAut (Spin n F N))ᵐᵒᵖ :=
  (CyclicOuterLemma37Concrete.inverseOpHom (spinFieldAction n F S)).comp invMonoidHom

@[simp] theorem spinRightFieldHom_unop
    (S : FieldActionSource n F r f parameters N) (e : FieldGroup f) :
    (spinRightFieldHom parameters S e).unop = spinFieldAction n F S e := by
  simp [spinRightFieldHom, CyclicOuterLemma37Concrete.inverseOpHom]

end ModularRep.PaperProofs.TypeBSpinGGGRPrincipalSeriesBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
