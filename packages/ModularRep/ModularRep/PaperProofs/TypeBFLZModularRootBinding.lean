import ModularRep.PaperProofs.TypeBFLZCyclotomicModel
import ModularRep.PaperProofs.TypeBIntegralCyclotomicRoot
import ModularRep.PaperProofs.TypeBModularRootReduction
import ModularRep.PaperProofs.TypeBPrimitiveRootEquivalence
import ModularRep.PaperProofs.TypeBSpinRestrictionConstituent

/-!
# The modular root convention from the same ordinary cyclotomic choice
The special Clifford prime regular exponent divides the common conductor.
The corresponding power of Choice.root has a unique integral representative
in the actual modular system. Its actual residue defines the modular
generator. Equal powers determine the full root equivalence; Spin receives
its literal restriction. No independent root, prime ideal, lifting map or
root-correspondence certificate is an input.
This does not prove stable-lattice character reduction or authenticate a
separately supplied published character table.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZModularRootBinding

open ModularRep TypeBCliffordCarriers TypeBFLZCyclotomicModel

variable {F K O k : Type} {n ell : ℕ}
  [Field F] [Finite F] [Finite (Clifford n F)]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]

abbrev exponent (F : Type) [Field F] (n ell : ℕ) [Finite (Clifford n F)] : ℕ :=
  primeRegularExponent ell (SpecialClifford n F)

theorem exponent_pos : 0 < exponent F n ell :=
  primeRegularExponent_pos ell (SpecialClifford n F)

instance exponent_neZero : NeZero (exponent F n ell) :=
  ⟨(exponent_pos (F := F) (n := n) (ell := ell)).ne'⟩

theorem exponent_dvd_conductor : exponent F n ell ∣ conductor F n :=
  (Nat.ordCompl_dvd (Nat.card (SpecialClifford n F)) ell).trans
    (ordinary_order_dvd F n)

variable (Msys : ModularSystem ell K O k)
  (choice : Choice (F := F) (n := n) K)

include Msys in
theorem exponent_coprime : (exponent F n ell).Coprime ell :=
  (Nat.coprime_ordCompl Msys.prime
    (Nat.card_pos (α := SpecialClifford n F)).ne').symm

def ordinaryRoot : K := choice.root ^ (conductor F n / exponent F n ell)

theorem ordinaryRoot_primitive :
    IsPrimitiveRoot (ordinaryRoot (ell := ell) choice) (exponent F n ell) :=
  choice.primitive.pow (conductor_pos F n)
    (Nat.div_mul_cancel (exponent_dvd_conductor (F := F) (n := n) (ell := ell))).symm

/-- Its value is the image of the same power of the common number-field generator. -/
theorem ordinaryRoot_embedding :
    ordinaryRoot (ell := ell) choice =
      choice.embedding (generator (F := F) (n := n) ^
        (conductor F n / exponent F n ell)) := by
  rw [map_pow, Choice.embedding_generator]
  rfl

def integralRoot : O :=
  TypeBIntegralCyclotomicRoot.integralRoot Msys exponent_pos
    (ordinaryRoot_primitive (ell := ell) choice).pow_eq_one

theorem algebraMap_integralRoot :
    algebraMap O K (integralRoot Msys choice) = ordinaryRoot (ell := ell) choice :=
  TypeBIntegralCyclotomicRoot.algebraMap_integralRoot Msys exponent_pos
    (ordinaryRoot_primitive (ell := ell) choice).pow_eq_one

theorem integralRoot_primitive :
    IsPrimitiveRoot (integralRoot Msys choice) (exponent F n ell) :=
  TypeBIntegralCyclotomicRoot.integralRoot_primitive Msys exponent_pos
    (ordinaryRoot_primitive (ell := ell) choice)

def residueRoot : k := Msys.residue (integralRoot Msys choice)

theorem residueRoot_primitive :
    IsPrimitiveRoot (residueRoot Msys choice) (exponent F n ell) :=
  TypeBModularRootReduction.isPrimitiveRoot_residue Msys
    (exponent_coprime (F := F) (n := n) Msys) (integralRoot_primitive Msys choice)

def rootEquiv : rootsOfUnity (exponent F n ell) k ≃*
    rootsOfUnity (exponent F n ell) K :=
  TypeBPrimitiveRootEquivalence.equiv
    (residueRoot_primitive Msys choice) (ordinaryRoot_primitive (ell := ell) choice)

/-- The complete special Clifford root convention has now been constructed. -/
def cliffordRoot : PrimeRegularRootEmbedding ell k K (SpecialClifford n F) where
  prime := Msys.prime
  toMulEquiv := rootEquiv Msys choice

theorem cliffordRoot_lift_power (j : ℕ) :
    (cliffordRoot Msys choice).lift ((residueRoot Msys choice) ^ j) =
      ordinaryRoot (ell := ell) choice ^ j := by
  let z := (residueRoot_primitive Msys choice).toRootsOfUnity ^ j
  have hz : ((z : kˣ) : k) = residueRoot Msys choice ^ j := by
    rw [rootsOfUnity.coe_pow]
    rfl
  rw [← hz, PrimeRegularRootEmbedding.lift_coe]
  exact TypeBPrimitiveRootEquivalence.equiv_pow_value
    (residueRoot_primitive Msys choice) (ordinaryRoot_primitive (ell := ell) choice) j

/-- On every integral root in the required range, the lift inverts the
actual residue map followed by the actual fraction-field embedding. -/
theorem cliffordRoot_residue (z : O) (hz : z ^ exponent F n ell = 1) :
    (cliffordRoot Msys choice).lift (Msys.residue z) = algebraMap O K z := by
  obtain ⟨j, _, hj⟩ := (integralRoot_primitive Msys choice).eq_pow_of_pow_eq_one hz
  rw [← hj, map_pow, map_pow, algebraMap_integralRoot]
  exact cliffordRoot_lift_power Msys choice j

variable (N : NormSource n F)

/-- The Spin convention is precisely the existing restriction construction. -/
def spinRoot : PrimeRegularRootEmbedding ell k K (Spin n F N) :=
  TypeBSpinRestrictionConstituent.spinRoot N (cliffordRoot Msys choice)

theorem spinRoot_agrees
    (z : rootsOfUnity (primeRegularExponent ell (Spin n F N)) k) :
    (spinRoot Msys choice N).lift ((z : kˣ) : k) =
      (cliffordRoot Msys choice).lift ((z : kˣ) : k) :=
  by
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion
    (TypeBSpinRestrictionConstituent.spin_exponent_dvd (ell := ell) N) z
  calc
    (spinRoot Msys choice N).lift ((z : kˣ) : k) =
        (spinRoot Msys choice N).liftRoot z :=
      (spinRoot Msys choice N).lift_coe z
    _ = (cliffordRoot Msys choice).liftRoot included := rfl
    _ = (cliffordRoot Msys choice).lift ((included : kˣ) : k) :=
      ((cliffordRoot Msys choice).lift_coe included).symm
    _ = (cliffordRoot Msys choice).lift ((z : kˣ) : k) := rfl

theorem spinRoot_residue (z : O)
    (hz : z ^ primeRegularExponent ell (Spin n F N) = 1) :
    (spinRoot Msys choice N).lift (Msys.residue z) = algebraMap O K z := by
  letI : NeZero (primeRegularExponent ell (Spin n F N)) :=
    ⟨(primeRegularExponent_pos ell (Spin n F N)).ne'⟩
  let zbar : rootsOfUnity (primeRegularExponent ell (Spin n F N)) k :=
    rootsOfUnity.mkOfPowEq (Msys.residue z) (by rw [← map_pow, hz, map_one])
  have hval : ((zbar : kˣ) : k) = Msys.residue z := rfl
  rw [← hval, spinRoot_agrees, hval]
  apply cliffordRoot_residue
  obtain ⟨d, hd⟩ := TypeBSpinRestrictionConstituent.spin_exponent_dvd (ell := ell) N
  change z ^ primeRegularExponent ell (SpecialClifford n F) = 1
  rw [hd, pow_mul, hz, one_pow]

end ModularRep.PaperProofs.TypeBFLZModularRootBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
