import ModularRep.PaperProofs.TypeBConformalDualFieldAction
import ModularRep.PaperProofs.TypeBRegularLeviRationalCarriers
import ModularRep.PaperProofs.TypeBRankThreeNonprincipalLeviEnvelope
import ModularRep.PrimeRegular

/-!
The adjoint geometric carrier is the actual projective conformal symplectic
group over the algebraically closed defining field. Rational points retain
the coordinate base-change and scalar-quotient squares. Geometric Levi and
identity-component interpretations are standard source data on subgroups
of this same carrier. The least stable envelope and its properness are
deductions from dimension, intersection and the noncontainment condition.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalGeometry

open TypeBConformalDualCarriers TypeBConformalDualFieldAction
open TypeBRegularLeviRationalCarriers

/-- The specified defining-field Frobenius, with its literal power values. -/
structure FrobeniusSource (p f : ℕ) (A : Type) [Field A] where
  automorphism : RingAut A
  power_value : ∀ a : A, automorphism a = a ^ (p ^ f)

/-- Frobenius on the actual adjoint point group is coordinate transport. -/
def Phi {p f : ℕ} {A : Type} [Field A]
    (frobenius : FrobeniusSource p f A) : MulAut (PCSp A 3) :=
  pcspAutomorphism A 3 frobenius.automorphism

/-- The fixed coordinate extension in the two symplectic coordinate blocks. -/
def vectorBaseChange (F A : Type) [Field F] [Field A] [Algebra F A]
    (v : SymplecticSpace F 3) : SymplecticSpace A 3 :=
  ((fun i => algebraMap F A (v.1 i)), (fun i => algebraMap F A (v.2 i)))

/-- Rational-point identification with the natural matrix and scalar square. -/
structure RationalPointSource (F A : Type) [Field F] [Field A]
    [IsAlgClosed A] [Algebra F A] (p f : ℕ)
    (frobenius : FrobeniusSource p f A) where
  baseChange : CSp F 3 →* CSp A 3
  multiplier_value : ∀ g : CSp F 3,
    multiplier A 3 (baseChange g) =
      Units.map (algebraMap F A).toMonoidHom (multiplier F 3 g)
  coordinate_value : ∀ (g : CSp F 3) (v : SymplecticSpace F 3),
    linearPart A 3 (baseChange g) (vectorBaseChange F A v) =
      vectorBaseChange F A (linearPart F 3 g v)
  rationalEquiv : PCSp F 3 ≃* fixedPoints (Phi frobenius).toMonoidHom
  quotient_square : ∀ g : CSp F 3,
    (rationalEquiv (QuotientGroup.mk' (scalarSubgroup F 3) g)).val =
      QuotientGroup.mk' (scalarSubgroup A 3) (baseChange g)

namespace RationalPointSource

variable {F A : Type} [Field F] [Field A] [IsAlgClosed A] [Algebra F A]
  {p f : ℕ} {frobenius : FrobeniusSource p f A}
  (points : RationalPointSource F A p f frobenius)

/-- The rational embedding is the given fixed-point identification's subtype. -/
def rationalEmbedding : PCSp F 3 →* PCSp A 3 :=
  (fixedPoints (Phi frobenius).toMonoidHom).subtype.comp
    points.rationalEquiv.toMonoidHom

theorem rationalEmbedding_injective : Function.Injective points.rationalEmbedding :=
  Subtype.val_injective.comp points.rationalEquiv.injective

@[simp] theorem rationalEmbedding_fixed (s : PCSp F 3) :
    Phi frobenius (points.rationalEmbedding s) = points.rationalEmbedding s :=
  (points.rationalEquiv s).property

@[simp] theorem rationalEmbedding_mk (g : CSp F 3) :
    points.rationalEmbedding (QuotientGroup.mk' (scalarSubgroup F 3) g) =
      QuotientGroup.mk' (scalarSubgroup A 3) (points.baseChange g) :=
  points.quotient_square g

/-- The image is precisely the fixed subgroup, not a different finite group. -/
theorem rationalEmbedding_range :
    points.rationalEmbedding.range = fixedPoints (Phi frobenius).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    exact points.rationalEmbedding_fixed s
  · intro x hx
    obtain ⟨s, hs⟩ := points.rationalEquiv.surjective ⟨x, hx⟩
    exact ⟨s, congrArg Subtype.val hs⟩

end RationalPointSource

/-- Full centralizers are taken in the algebraic adjoint point carrier. -/
def fullCentralizer {A : Type} [Field A] (s : PCSp A 3) :
    Subgroup (PCSp A 3) := Subgroup.centralizer {s}

/-- The rational centralizer is the literal intersection with fixed points. -/
def finiteCentralizer {p f : ℕ} {A : Type} [Field A]
    (frobenius : FrobeniusSource p f A) (s : PCSp A 3) : Subgroup (PCSp A 3) :=
  fullCentralizer s ⊓ fixedPoints (Phi frobenius).toMonoidHom

theorem finiteCentralizer_le_full {p f : ℕ} {A : Type} [Field A]
    (frobenius : FrobeniusSource p f A) (s : PCSp A 3) :
    finiteCentralizer frobenius s ≤ fullCentralizer s := inf_le_left

/-- Every member of the rational centralizer is fixed individually. -/
theorem finiteCentralizer_frobenius {p f : ℕ} {A : Type} [Field A]
    (frobenius : FrobeniusSource p f A) (s : PCSp A 3) :
    (finiteCentralizer frobenius s).map (Phi frobenius).toMonoidHom =
      finiteCentralizer frobenius s := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have fixed : Phi frobenius x = x := hx.2
    change Phi frobenius x ∈ finiteCentralizer frobenius s
    rw [fixed]
    exact hx
  · intro x hx
    exact ⟨x, hx, hx.2⟩

/-- Standard geometric statements on this exact algebraic point carrier. -/
structure GeometrySource (F A : Type) [Field F] [Field A]
    [IsAlgClosed A] [Algebra F A] (p f : ℕ)
    (frobenius : FrobeniusSource p f A)
    (points : RationalPointSource F A p f frobenius) where
  connectedCentralizer : PCSp A 3 → Subgroup (PCSp A 3)
  connected_le : ∀ s, connectedCentralizer s ≤ fullCentralizer s
  connected_frobenius : ∀ s,
    (connectedCentralizer s).map (Phi frobenius).toMonoidHom =
      connectedCentralizer (Phi frobenius s)
  IsLevi : Subgroup (PCSp A 3) → Prop
  dimension : Subgroup (PCSp A 3) → ℕ
  top_isLevi : IsLevi ⊤
  dimension_strict : ∀ {L M : Subgroup (PCSp A 3)},
    IsLevi L → IsLevi M → L < M → dimension L < dimension M
  intersection_isLevi : ∀ (s : PCSp F 3), ModularRep.IsPrimeRegular p s →
    ∀ L M : Subgroup (PCSp A 3),
      IsLevi L → connectedCentralizer (points.rationalEmbedding s) ≤ L →
      IsLevi M → connectedCentralizer (points.rationalEmbedding s) ≤ M →
        IsLevi (L ⊓ M)
  frobenius_isLevi : ∀ L : Subgroup (PCSp A 3),
    IsLevi (L.map (Phi frobenius).toMonoidHom) ↔ IsLevi L

namespace GeometrySource

variable {F A : Type} [Field F] [Field A] [IsAlgClosed A] [Algebra F A]
  {p f : ℕ} {frobenius : FrobeniusSource p f A}
  {points : RationalPointSource F A p f frobenius}
  (geometry : GeometrySource F A p f frobenius points)

/-- The subgroup generated by the two actual centralizer factors. -/
def H (s : PCSp A 3) : Subgroup (PCSp A 3) :=
  geometry.connectedCentralizer s ⊔ finiteCentralizer frobenius s

theorem connected_le_H (s : PCSp A 3) :
    geometry.connectedCentralizer s ≤ geometry.H s := le_sup_left

theorem H_le_full (s : PCSp A 3) : geometry.H s ≤ fullCentralizer s :=
  sup_le (geometry.connected_le s) (finiteCentralizer_le_full frobenius s)

/-- Subgroup containment is exactly containment of the manuscript product. -/
theorem centralizerProduct_subset_iff (s : PCSp A 3) (L : Subgroup (PCSp A 3)) :
    (geometry.connectedCentralizer s : Set (PCSp A 3)) *
        (finiteCentralizer frobenius s : Set (PCSp A 3)) ⊆ L ↔
      geometry.H s ≤ L := by
  constructor
  · intro h
    apply sup_le
    · intro x hx
      exact h ⟨x, hx, 1, (finiteCentralizer frobenius s).one_mem, mul_one x⟩
    · intro x hx
      exact h ⟨1, (geometry.connectedCentralizer s).one_mem, x, hx, one_mul x⟩
  · intro h
    have left : geometry.connectedCentralizer s ≤ L :=
      (geometry.connected_le_H s).trans h
    have right : finiteCentralizer frobenius s ≤ L :=
      (show finiteCentralizer frobenius s ≤ geometry.H s from le_sup_right).trans h
    exact Subgroup.mul_subset left right

theorem rational_H_frobenius (s : PCSp F 3) :
    (geometry.H (points.rationalEmbedding s)).map (Phi frobenius).toMonoidHom =
      geometry.H (points.rationalEmbedding s) := by
  unfold H
  rw [Subgroup.map_sup, geometry.connected_frobenius,
    points.rationalEmbedding_fixed, finiteCentralizer_frobenius]

/-- Quasi-isolation uses actual algebraic Levi subgroups and full centralizers. -/
def QuasiIsolated (s : PCSp A 3) : Prop :=
  ∀ L : Subgroup (PCSp A 3), geometry.IsLevi L → L ≠ ⊤ →
    ¬ fullCentralizer s ≤ L

/-- Strict quasi-isolation uses the same proper algebraic Levi family. -/
def StrictlyQuasiIsolated (s : PCSp A 3) : Prop :=
  ∀ L : Subgroup (PCSp A 3), geometry.IsLevi L → L ≠ ⊤ →
    ¬ geometry.H s ≤ L

theorem quasiIsolated_of_strictlyQuasiIsolated (s : PCSp A 3)
    (strict : geometry.StrictlyQuasiIsolated s) : geometry.QuasiIsolated s := by
  intro L hL proper contains
  exact strict L hL proper ((geometry.H_le_full s).trans contains)

theorem not_strictlyQuasiIsolated_of_not_quasiIsolated (s : PCSp A 3)
    (notQuasi : ¬ geometry.QuasiIsolated s) : ¬ geometry.StrictlyQuasiIsolated s :=
  fun strict => notQuasi (geometry.quasiIsolated_of_strictlyQuasiIsolated s strict)

/-- Defining-prime regularity supplies the common-torus intersection input. -/
theorem existsUnique_rational_leviEnvelope (s : PCSp F 3)
    (regular : ModularRep.IsPrimeRegular p s) :
    ∃! L : Subgroup (PCSp A 3),
      geometry.IsLevi L ∧ geometry.H (points.rationalEmbedding s) ≤ L ∧
      (∀ M : Subgroup (PCSp A 3), geometry.IsLevi M →
        geometry.H (points.rationalEmbedding s) ≤ M → L ≤ M) ∧
      L.map (Phi frobenius).toMonoidHom = L ∧
      ((∃ M : Subgroup (PCSp A 3), geometry.IsLevi M ∧
        geometry.H (points.rationalEmbedding s) ≤ M ∧ M ≠ ⊤) → L ≠ ⊤) := by
  apply TypeBRankThreeNonprincipalLeviEnvelope.existsUnique_frobeniusStable_leviEnvelope
    geometry.IsLevi geometry.dimension geometry.top_isLevi geometry.dimension_strict
    (geometry.H (points.rationalEmbedding s))
    (fun L M hL hHL hM hHM => geometry.intersection_isLevi s regular L M hL
      ((geometry.connected_le_H _).trans hHL) hM ((geometry.connected_le_H _).trans hHM))
    (Phi frobenius) geometry.frobenius_isLevi
    (geometry.rational_H_frobenius s)

/-- The same least rational envelope is proper once non-strictness is derived. -/
theorem exists_proper_rational_levi (s : PCSp F 3)
    (regular : ModularRep.IsPrimeRegular p s)
    (notStrict : ¬ geometry.StrictlyQuasiIsolated (points.rationalEmbedding s)) :
    ∃ L : Subgroup (PCSp A 3),
      geometry.IsLevi L ∧ geometry.H (points.rationalEmbedding s) ≤ L ∧
      L ≠ ⊤ ∧ L.map (Phi frobenius).toMonoidHom = L ∧
      ∀ M : Subgroup (PCSp A 3), geometry.IsLevi M →
        geometry.H (points.rationalEmbedding s) ≤ M → L ≤ M := by
  classical
  have proper : ∃ M : Subgroup (PCSp A 3), geometry.IsLevi M ∧
      geometry.H (points.rationalEmbedding s) ≤ M ∧ M ≠ ⊤ := by
    by_contra h
    apply notStrict
    intro M hM hne hH
    exact h ⟨M, hM, hH, hne⟩
  obtain ⟨L, hL, _⟩ := geometry.existsUnique_rational_leviEnvelope s regular
  exact ⟨L, hL.1, hL.2.1, hL.2.2.2.2 proper, hL.2.2.2.1, hL.2.2.1⟩

end GeometrySource

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalGeometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
