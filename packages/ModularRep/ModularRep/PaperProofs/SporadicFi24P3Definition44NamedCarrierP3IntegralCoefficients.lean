import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IdempotentData
import ModularRep.GroupAlgebraCentralFunctions
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.CharP.Basic

/-! A fixed rational coefficient ring in which the selected denominator is
invertible. Its characteristic-zero and characteristic-three maps, and the
coefficientwise transport of centres, are constructed rather than assumed. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntegralCoefficients
open ModularRep
open SporadicFi24P3Definition44NamedCarrierP3IdempotentData

abbrev denominator : ℤ := 7031383654400
abbrev CoefficientRing := Localization.Away denominator

def toOrdinary {K : Type*} [Field K] [CharZero K] : CoefficientRing →+* K :=
  Localization.awayLift (Int.castRingHom K) denominator
    (isUnit_iff_ne_zero.mpr (by norm_num [denominator]))

def toResidue {k : Type*} [Field k] [CharP k 3] : CoefficientRing →+* k :=
  Localization.awayLift (Int.castRingHom k) denominator
    (isUnit_iff_ne_zero.mpr (by
      simp only [denominator, Int.coe_castRingHom, Int.cast_ofNat]
      intro h
      exact coefficient_denominator_prime_to_three
        ((CharP.cast_eq_zero_iff k 3 7031383654400).mp h)))

def inverseDenominator : CoefficientRing :=
  IsLocalization.Away.invSelf (S := CoefficientRing) denominator

theorem toOrdinary_injective {K : Type*} [Field K] [CharZero K] :
    Function.Injective (toOrdinary (K := K)) := by
  refine (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers denominator) (toOrdinary (K := K))).2 ?_
  intro a b
  constructor
  · exact fun h => congrArg (toOrdinary (K := K)) h
  · intro h
    have hab : (a : K) = (b : K) := by
      simpa [toOrdinary, Localization.awayLift] using h
    exact congrArg (algebraMap ℤ CoefficientRing) (Int.cast_injective hab)

theorem map_inverseDenominator {F : Type*} [Field F]
    (f : CoefficientRing →+* F) :
    f inverseDenominator = (7031383654400 : F)⁻¹ := by
  have h := congrArg f
    (IsLocalization.Away.mul_invSelf (S := CoefficientRing) denominator)
  have hc : f ((algebraMap ℤ CoefficientRing) denominator) = (denominator : F) :=
    eq_intCast (f.comp (algebraMap ℤ CoefficientRing)) denominator
  have hm : (7031383654400 : F) * f inverseDenominator = 1 := by
    simpa only [map_mul, map_one, hc, inverseDenominator, denominator, Int.cast_ofNat] using h
  exact eq_inv_of_mul_eq_one_right hm

theorem map_integralCoefficient {F : Type*} [Field F]
    (f : CoefficientRing →+* F) (n : ℤ) :
    f ((n : CoefficientRing) * inverseDenominator) =
      (n : F) / (7031383654400 : F) := by
  rw [map_mul, map_intCast, map_inverseDenominator, div_eq_mul_inv]

theorem coeffMap_mem_center
    {A B G : Type*} [CommSemiring A] [CommSemiring B] [Group G]
    (f : A →+* B) {z : A[G]} (hz : z ∈ GroupAlgebraCenter A G) :
    MonoidAlgebra.mapRingHom G f z ∈ GroupAlgebraCenter B G := by
  rw [Subalgebra.mem_center_iff]
  intro y
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [add_mul, mul_add, ha, hb]
  | single g r =>
      ext x
      have hcoeff : z.coeff (g⁻¹ * x) = z.coeff (x * g⁻¹) := by
        have h := congrArg (fun w : A[G] => w.coeff x)
          (Subalgebra.mem_center_iff.mp hz (MonoidAlgebra.single g 1))
        simpa only [MonoidAlgebra.coeff_single_mul_apply,
          MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one] using h
      simp only [MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply, MonoidAlgebra.coeff_mapRingHom]
      rw [hcoeff, mul_comm]

def centerMap {A B G : Type*} [CommSemiring A] [CommSemiring B] [Group G]
    (f : A →+* B) : GroupAlgebraCenter A G →+* GroupAlgebraCenter B G where
  toFun z := ⟨MonoidAlgebra.mapRingHom G f z.val, coeffMap_mem_center f z.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a.val b.val)

theorem coeffMap_injective
    {A B G : Type*} [CommSemiring A] [CommSemiring B] [Group G]
    (f : A →+* B) (hf : Function.Injective f) :
    Function.Injective (MonoidAlgebra.mapRingHom G f) := by
  intro a b hab
  ext x
  apply hf
  have h := congrArg (fun z : B[G] => z.coeff x) hab
  simpa only [MonoidAlgebra.coeff_mapRingHom] using h

theorem mem_center_of_coeffMap_mem_center
    {A B G : Type*} [CommSemiring A] [CommSemiring B] [Group G]
    (f : A →+* B) (hf : Function.Injective f) (z : A[G])
    (hz : MonoidAlgebra.mapRingHom G f z ∈ GroupAlgebraCenter B G) :
    z ∈ GroupAlgebraCenter A G := by
  rw [Subalgebra.mem_center_iff]
  intro y
  apply coeffMap_injective f hf
  simp only [map_mul]
  exact Subalgebra.mem_center_iff.mp hz _

theorem idempotent_of_coeffMap_idempotent
    {A B G : Type*} [CommSemiring A] [CommSemiring B] [Group G]
    (f : A →+* B) (hf : Function.Injective f) (z : A[G])
    (hz : IsIdempotentElem (MonoidAlgebra.mapRingHom G f z)) :
    IsIdempotentElem z := by
  apply coeffMap_injective f hf
  simpa only [map_mul] using hz.eq

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntegralCoefficients


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
