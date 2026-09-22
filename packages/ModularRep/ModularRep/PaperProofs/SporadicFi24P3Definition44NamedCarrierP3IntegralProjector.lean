import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntegralCoefficients

/-! The selected inverse values define an integral group algebra element.
Its image is the ordinary projector, and its residue has the literal
coefficients at the actual representatives, independently of class choices. -/

noncomputable section
open scoped BigOperators MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntegralProjector
open ModularRep
open SporadicFi24P3Definition44NamedCarrierP3OrdinaryProjector
open SporadicFi24P3Definition44NamedCarrierP3IntegralCoefficients
open SporadicFi24P3Definition44NamedCarrierP3IdempotentData

variable {G : Type*} [Group G]

def chosenClass (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹) (g : G) : Fin 108 :=
  Classical.choose (cover g)

theorem character_inverse_chosenClass
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (rho : Representation K G V) (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (hvalues : ∀ c, rho.character ((rep c)⁻¹) = (inverseCharacterValues c : K)) (g : G) :
    rho.character g⁻¹ = (inverseCharacterValues (chosenClass rep cover g) : K) := by
  obtain ⟨a, ha⟩ := Classical.choose_spec (cover g)
  change g = a * rep (chosenClass rep cover g) * a⁻¹ at ha
  have hi : g⁻¹ = a * (rep (chosenClass rep cover g))⁻¹ * a⁻¹ := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg (fun x : G => x⁻¹) ha
  calc
    rho.character g⁻¹ = rho.character (a * (rep (chosenClass rep cover g))⁻¹ * a⁻¹) :=
      congrArg rho.character hi
    _ = rho.character ((rep (chosenClass rep cover g))⁻¹) := rho.char_conj _ _
    _ = _ := hvalues _

variable [Fintype G]

def integralProjector (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹) : CoefficientRing[G] :=
  ∑ g : G, MonoidAlgebra.single g
    ((inverseCharacterValues (chosenClass rep cover g) : CoefficientRing) * inverseDenominator)

@[simp]
theorem integralProjector_coeff (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹) (g : G) :
    (integralProjector rep cover).coeff g =
      (inverseCharacterValues (chosenClass rep cover g) : CoefficientRing) *
        inverseDenominator := by
  classical
  simp [integralProjector, MonoidAlgebra.coeff_sum, Finsupp.single_apply]

theorem integralProjector_map_eq
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
    (rho : Representation K G V) (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (hvalues : ∀ c, rho.character ((rep c)⁻¹) = (inverseCharacterValues c : K))
    (hdim : Module.finrank K V = 178514751987)
    (horder : Nat.card G = 1255205709190661721292800) (j : CoefficientRing →+* K) :
    MonoidAlgebra.mapRingHom G j (integralProjector rep cover) = ordinaryProjector rho := by
  have hscale : ((Module.finrank K V : K) / (Nat.card G : K)) =
      (7031383654400 : K)⁻¹ := by
    rw [hdim, horder]
    norm_num
  ext g
  rw [MonoidAlgebra.coeff_mapRingHom, integralProjector_coeff,
    map_mul, map_intCast, map_inverseDenominator, ordinaryProjector_coeff, hscale,
    character_inverse_chosenClass rho rep cover hvalues g]
  exact mul_comm _ _

theorem integralProjector_map_coeff_at_rep
    {K V F : Type*} [Field K] [CharZero K] [Field F]
    [AddCommGroup V] [Module K V]
    (rho : Representation K G V) (rep : Fin 108 → G)
    (cover : ∀ x : G, ∃ c a, x = a * rep c * a⁻¹)
    (hvalues : ∀ c, rho.character ((rep c)⁻¹) = (inverseCharacterValues c : K))
    (f : CoefficientRing →+* F) (c : Fin 108) :
    (MonoidAlgebra.mapRingHom G f (integralProjector rep cover)).coeff (rep c) =
      (inverseCharacterValues c : F) / (7031383654400 : F) := by
  have hc : inverseCharacterValues (chosenClass rep cover (rep c)) = inverseCharacterValues c :=
    (Int.cast_injective (α := K))
      ((character_inverse_chosenClass rho rep cover hvalues (rep c)).symm.trans (hvalues c))
  rw [MonoidAlgebra.coeff_mapRingHom, integralProjector_coeff,
    map_mul, map_intCast, map_inverseDenominator, hc, div_eq_mul_inv]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntegralProjector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
