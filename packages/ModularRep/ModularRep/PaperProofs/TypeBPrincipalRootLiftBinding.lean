import ModularRep.PaperProofs.TypeBModularGroupRootBinding
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.PaperProofs.TypeBPrincipalSpinMatrixFieldTransport

/-!
# Whole root lifts for the actual principal Spin and orthogonal carriers

The field-level lift is zero outside its finite root domain. Equal residue
conventions therefore give equal whole functions here through equality of
the prime-to-two parts of the actual group orders. The central quotient,
the constructed matrix equivalence and the index-two inclusion supply those
equalities. No ordinary character field closure is required.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalRootLiftBinding

open ModularRep TypeBModularGroupRootBinding
open TypeBLocalReductionInstantiation
open TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding

section General

variable {ell : ℕ} {K O k G H : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [Group G] [Finite G] [Group H] [Finite H]
  (Msys : ModularSystem ell K O k)

/-- The individual residue calibration gives the prescribed whole embedding. -/
theorem root_eq_groupRoot (iota : PrimeRegularRootEmbedding ell k K G)
    (compatible : RootResidueCompatible Msys iota) :
    iota = groupRoot Msys G :=
  eq_groupRoot_of_residue Msys G iota compatible

/-- Equal finite root domains transport the same modular-system convention. -/
theorem groupRoot_transport
    (h : primeRegularExponent ell G = primeRegularExponent ell H) :
    PrimeRegularRootEmbeddingPQuotient.transport (groupRoot Msys G) h =
      groupRoot Msys H := by
  apply eq_groupRoot_of_residue Msys H
  intro z hz
  rw [PrimeRegularRootEmbeddingPQuotient.transport_lift]
  apply groupRoot_residue Msys G z
  simpa only [h] using hz

/-- This equality includes the zero extension outside the required roots. -/
theorem groupRoot_lift_eq_of_exponent_eq
    (h : primeRegularExponent ell G = primeRegularExponent ell H) :
    (groupRoot Msys G).lift = (groupRoot Msys H).lift := by
  funext z
  calc
    (groupRoot Msys G).lift z =
        (PrimeRegularRootEmbeddingPQuotient.transport (groupRoot Msys G) h).lift z :=
      (PrimeRegularRootEmbeddingPQuotient.transport_lift (groupRoot Msys G) h z).symm
    _ = (groupRoot Msys H).lift z :=
      congrArg (fun root : PrimeRegularRootEmbedding ell k K H => root.lift z)
        (groupRoot_transport Msys h)

/-- Individually calibrated roots inherit the derived whole-function equality. -/
theorem lift_eq_of_residue
    (h : primeRegularExponent ell G = primeRegularExponent ell H)
    (iota : PrimeRegularRootEmbedding ell k K G)
    (j : PrimeRegularRootEmbedding ell k K H)
    (compatible : RootResidueCompatible Msys iota)
    (compatibleH : RootResidueCompatible Msys j) :
    iota.lift = j.lift := by
  rw [root_eq_groupRoot Msys iota compatible,
    root_eq_groupRoot Msys j compatibleH]
  exact groupRoot_lift_eq_of_exponent_eq Msys h

end General

section MatrixIndex

variable {n : ℕ} {F : Type} [Field F] [Finite F]

/-- Index two leaves the prime-to-two part of the actual matrix order unchanged. -/
theorem omega_so_exponent
    (indexTwo : (TypeBOrthogonalOmegaCarriers.omegaSubgroup n F).index = 2) :
    primeRegularExponent 2 (TypeBOrthogonalOmegaCarriers.Omega n F) =
      primeRegularExponent 2 (TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F) := by
  have card := (TypeBOrthogonalOmegaCarriers.omegaSubgroup n F).card_mul_index
  rw [indexTwo] at card
  have two : ordCompl[2] 2 = 1 := by
    simpa only [pow_one] using (Nat.ordCompl_self_pow (k := 1) Nat.prime_two)
  change ordCompl[2] (Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)) =
    ordCompl[2] (Nat.card (TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F))
  rw [← card, Nat.ordCompl_mul, two, mul_one]

variable {K O k : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  (Msys : ModularSystem 2 K O k)

/-- Actual SO and its index-two Omega subgroup use the same entire lift. -/
theorem omega_so_groupRoot_lifts
    (indexTwo : (TypeBOrthogonalOmegaCarriers.omegaSubgroup n F).index = 2) :
    (groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F)).lift =
      (groupRoot Msys (TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F)).lift :=
  groupRoot_lift_eq_of_exponent_eq Msys (omega_so_exponent indexTwo)

/-- The prescribed matrix conventions agree through their individual residue equations. -/
theorem omega_so_lifts_of_residue
    (indexTwo : (TypeBOrthogonalOmegaCarriers.omegaSubgroup n F).index = 2)
    (root : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega n F))
    (rootH : PrimeRegularRootEmbedding 2 k K
      (TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F))
    (compatible : RootResidueCompatible Msys root)
    (compatibleH : RootResidueCompatible Msys rootH) :
    root.lift = rootH.lift :=
  lift_eq_of_residue Msys (omega_so_exponent indexTwo)
    root rootH compatible compatibleH

end MatrixIndex

section Spin

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {N : NormSource n F} [Finite (Spin n F N)]
  (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
  (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)

include parameters rank centre in
/-- The actual centre quotient has the same prime-to-two order part as Spin. -/
theorem spin_quotient_exponent :
    primeRegularExponent 2 (Spin n F N) =
      primeRegularExponent 2 (TypeBSpinCoverSource.Omega N) :=
  (PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq Nat.prime_two
    (Subgroup.center (Spin n F N))
    (TypeBPrincipalSpinMatrixFieldTransport.centre_isTwoGroup parameters rank centre)).symm

variable (C : Source n F r f parameters rank N)

include parameters rank centre C in
/-- The literal matrix equivalence identifies the two Omega order parts. -/
theorem matrix_quotient_exponent :
    primeRegularExponent 2 (TypeBOrthogonalOmegaCarriers.Omega n F) =
      primeRegularExponent 2 (TypeBSpinCoverSource.Omega N) := by
  change ordCompl[2] (Nat.card (TypeBOrthogonalOmegaCarriers.Omega n F)) =
    ordCompl[2] (Nat.card (TypeBSpinCoverSource.Omega N))
  exact congrArg (fun m : ℕ => ordCompl[2] m)
    (Nat.card_congr (matrixOmegaEquiv n F N parameters rank C centre).symm.toEquiv)

variable {K O k : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  (Msys : ModularSystem 2 K O k)

include parameters rank centre in
/-- Canonical Spin and quotient roots have identical field-level lifts. -/
theorem spin_groupRoot_lifts :
    (groupRoot Msys (Spin n F N)).lift =
      (groupRoot Msys (TypeBSpinCoverSource.Omega N)).lift :=
  groupRoot_lift_eq_of_exponent_eq Msys (spin_quotient_exponent parameters rank centre)

include parameters rank centre C in
/-- Canonical matrix and quotient roots have identical field-level lifts. -/
theorem matrix_groupRoot_lifts :
    (groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F)).lift =
      (groupRoot Msys (TypeBSpinCoverSource.Omega N)).lift :=
  groupRoot_lift_eq_of_exponent_eq Msys
    (matrix_quotient_exponent parameters rank centre C)

include parameters rank centre in
/-- Discharge the Spin lift premise of the principal GGGR transport. -/
theorem spinLifts_of_residue
    (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (oldRoot : PrimeRegularRootEmbedding 2 k K (TypeBSpinCoverSource.Omega N))
    (spinCompatible : RootResidueCompatible Msys iota)
    (oldCompatible : RootResidueCompatible Msys oldRoot) :
    iota.lift = oldRoot.lift :=
  lift_eq_of_residue Msys (spin_quotient_exponent parameters rank centre)
    iota oldRoot spinCompatible oldCompatible

include parameters rank centre C in
/-- Discharge the matrix lift premise of the same principal GGGR transport. -/
theorem matrixLifts_of_residue
    (matrixRoot : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega n F))
    (oldRoot : PrimeRegularRootEmbedding 2 k K (TypeBSpinCoverSource.Omega N))
    (matrixCompatible : RootResidueCompatible Msys matrixRoot)
    (oldCompatible : RootResidueCompatible Msys oldRoot) :
    matrixRoot.lift = oldRoot.lift :=
  lift_eq_of_residue Msys (matrix_quotient_exponent parameters rank centre C)
    matrixRoot oldRoot matrixCompatible oldCompatible

end Spin

end ModularRep.PaperProofs.TypeBPrincipalRootLiftBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
