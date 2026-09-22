import ModularRep.ModularSystem
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integral representatives of prescribed ordinary roots
A DVR is integrally closed in its actual fraction field. The equation
zeta^m = 1 therefore constructs a unique integral representative of any
prescribed root of positive order. No integral-lifting certificate is used.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBIntegralCyclotomicRoot

open ModularRep

universe uK uO uk
variable {ell m : ℕ} {K : Type uK} {O : Type uO} {k : Type uk}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  (Msys : ModularSystem ell K O k)

include Msys in
theorem exists_integral_root {zeta : K} (hm : 0 < m)
    (hzeta : zeta ^ m = 1) : ∃ z : O, algebraMap O K z = zeta := by
  letI := Msys.isDiscreteValuationRing
  letI := Msys.isFractionRing
  apply IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hm
  rw [hzeta]
  exact isIntegral_one

/-- The integral representative is chosen over the actual algebra map. -/
def integralRoot {zeta : K} (hm : 0 < m) (hzeta : zeta ^ m = 1) : O :=
  (exists_integral_root Msys hm hzeta).choose

theorem algebraMap_integralRoot {zeta : K} (hm : 0 < m)
    (hzeta : zeta ^ m = 1) :
    algebraMap O K (integralRoot Msys hm hzeta) = zeta :=
  (exists_integral_root Msys hm hzeta).choose_spec

theorem integralRoot_unique {zeta : K} (hm : 0 < m)
    (hzeta : zeta ^ m = 1) {z : O} (hz : algebraMap O K z = zeta) :
    z = integralRoot Msys hm hzeta := by
  letI := Msys.isFractionRing
  apply IsFractionRing.injective O K
  exact hz.trans (algebraMap_integralRoot Msys hm hzeta).symm

theorem integralRoot_primitive {zeta : K} (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m) :
    IsPrimitiveRoot (integralRoot Msys hm hzeta.pow_eq_one) m := by
  letI := Msys.isFractionRing
  apply IsPrimitiveRoot.of_map_of_injective (f := algebraMap O K)
    (hf := IsFractionRing.injective O K)
  rwa [algebraMap_integralRoot]

end ModularRep.PaperProofs.TypeBIntegralCyclotomicRoot


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
