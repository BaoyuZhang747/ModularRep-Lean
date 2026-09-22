import ModularRep.PaperProofs.TypeBRankThreeNonprincipalGeometry
import ModularRep.PaperProofs.TypeBRankThreeNonprincipalDualLift

/-!
# Bonnafe's algebraic lift certificate on the actual rank-three carriers

The defining-field extension is the same coordinate base change used to
identify rational PCSp points. Its injectivity and its restriction to the
symplectic norm-one multiplier subgroup are proved below. The projective
square and orders are preserved by these constructed maps.

Bonnafe (2005), Proposition 5.3(a), is supplied only on the algebraically
closed symplectic point group, with defining-prime-regularity (the explicit
semisimple finite-order scope) and quasi-isolation of its actual projective
image. It is not an unguarded statement about arbitrary odd-order elements.
The finite-lift conclusion is derived on the same specified point maps.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalBonnafeBinding

open TypeBConformalDualCarriers TypeBCliffordCarriers
open TypeBRankThreeNonprincipalGeometry TypeBRankThreeNonprincipalDualLift

variable {F A : Type} [Field F] [Field A] [IsAlgClosed A] [Algebra F A]
  {p f : ℕ} {frobenius : FrobeniusSource p f A}
  (points : RationalPointSource F A p f frobenius)

/-- Coordinate and multiplier values determine the finite conformal element. -/
theorem baseChange_injective : Function.Injective points.baseChange := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply LinearEquiv.ext
    intro v
    have coordinates :
        vectorBaseChange F A (linearPart F 3 x v) =
          vectorBaseChange F A (linearPart F 3 y v) :=
      (points.coordinate_value x v).symm.trans
        ((congrArg (fun g : CSp A 3 =>
            linearPart A 3 g (vectorBaseChange F A v)) h).trans
          (points.coordinate_value y v))
    apply Prod.ext
    · funext i
      apply (algebraMap F A).injective
      exact congrArg (fun w : SymplecticSpace A 3 => w.1 i) coordinates
    · funext i
      apply (algebraMap F A).injective
      exact congrArg (fun w : SymplecticSpace A 3 => w.2 i) coordinates
  · have multipliers := congrArg (multiplier A 3) h
    rw [points.multiplier_value, points.multiplier_value] at multipliers
    apply Units.ext
    apply (algebraMap F A).injective
    exact congrArg (fun z : Aˣ => (z : A)) multipliers

/-- Restrict that same conformal base change to the actual multiplier kernel. -/
def symplecticBaseChange : Sp F →* Sp A :=
  (points.baseChange.comp (multiplier F 3).ker.subtype).codRestrict
    (multiplier A 3).ker (by
      intro x
      change multiplier A 3 (points.baseChange x.val) = 1
      rw [points.multiplier_value]
      change Units.map (algebraMap F A).toMonoidHom (multiplier F 3 x.val) = 1
      rw [x.property, map_one])

theorem symplecticBaseChange_injective :
    Function.Injective (symplecticBaseChange points) := by
  intro x y h
  apply Subtype.ext
  exact baseChange_injective points (congrArg Subtype.val h)

/-- The finite and algebraic dual projections commute on the same lift. -/
theorem symplecticBaseChange_projective (x : Sp F) :
    symplecticProjection A (symplecticBaseChange points x) =
      points.rationalEmbedding (symplecticProjection F x) :=
  (points.rationalEmbedding_mk x.val).symm

theorem symplecticBaseChange_orderOf (x : Sp F) :
    orderOf (symplecticBaseChange points x) = orderOf x :=
  orderOf_injective (symplecticBaseChange points)
    (symplecticBaseChange_injective points) x

/-- Exact one-way algebraic type-C3 lift bound. All named carriers and
defining-characteristic hypotheses are retained in this certificate. -/
structure AlgebraicBonnafeCertificate
    (p f : ℕ) (F A : Type) [Field F] [Finite F] [CharP F p]
    [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
    (parameters : OddFieldParameters F p f)
    (frobenius : FrobeniusSource p f A)
    (points : RationalPointSource F A p f frobenius)
    (geometry : GeometrySource F A p f frobenius points) : Prop where
  order_four : ∀ x : Sp A, p.Coprime (orderOf x) →
    geometry.QuasiIsolated (symplecticProjection A x) → orderOf x ∣ 4

variable [Finite F] [CharP F p] [CharP A p]
  (parameters : OddFieldParameters F p f)
  (geometry : GeometrySource F A p f frobenius points)

/-- Pull the published bound back through the injective actual base change. -/
theorem finiteLift_order_four
    (source : AlgebraicBonnafeCertificate p f F A parameters frobenius points geometry)
    (x : Sp F) (regular : p.Coprime (orderOf x))
    (quasi : geometry.QuasiIsolated
      (points.rationalEmbedding (symplecticProjection F x))) :
    orderOf x ∣ 4 := by
  have algebraicRegular : p.Coprime (orderOf (symplecticBaseChange points x)) := by
    simpa only [symplecticBaseChange_orderOf] using regular
  have algebraicQuasi : geometry.QuasiIsolated
      (symplecticProjection A (symplecticBaseChange points x)) := by
    simpa only [symplecticBaseChange_projective] using quasi
  simpa only [symplecticBaseChange_orderOf] using
    source.order_four (symplecticBaseChange points x) algebraicRegular algebraicQuasi

/-- The old all-lifts interface is restricted to defining-prime regular
parameters and to the proved projective symplectic image. -/
theorem bonnafe_projection_interface
    (source : AlgebraicBonnafeCertificate p f F A parameters frobenius points geometry)
    (htwo : (2 : F) ≠ 0) :
    (centralDoubleCover F htwo).BonnafeOrderFourProjectionInterface
      (fun s : PSp F => p.Coprime (orderOf (s : PCSp F 3)) ∧
        geometry.QuasiIsolated (points.rationalEmbedding (s : PCSp F 3))) := by
  intro s x hs hx
  have projection : symplecticProjection F x = (s : PCSp F 3) :=
    congrArg Subtype.val hx
  have regular : p.Coprime (orderOf x) :=
    coprime_orderOf_of_projective_order F p x parameters.odd.coprime_two_right
      (by simpa only [projection] using hs.1)
  exact finiteLift_order_four points parameters geometry source x regular
    (by simpa only [projection] using hs.2)

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalBonnafeBinding



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
