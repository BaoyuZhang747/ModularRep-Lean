import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation

/-!
# The same modular-system roots on the fixed quotient G3

The quotient root is the restriction already used by actual Brauer descent.
Its residue calibration and sufficient ordinary roots follow from the given
upstairs data and the surjectivity of the same projection.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3B2RootDescent

open ModularRep TypeBQ3TripleCoverCarrier
open TypeBLocalReductionInstantiation
open SporadicFi24P3Definition44NamedCarrierSurjectiveRoot

variable (source : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
variable [Finite X]

include source freeSource in
/-- Divisibility concerns the actual target of the retained projection. -/
theorem down_order_dvd : Nat.card G3 ∣ Nat.card X :=
  Subgroup.card_dvd_of_surjective (q source freeSource) (q_surjective source freeSource)

/-- Upstairs ordinary roots supply the exact downstairs finite-root guard. -/
def downOrdinaryRoots {K : Type} [Field K]
    [HasEnoughRootsOfUnity K (Nat.card X)] :
    HasEnoughRootsOfUnity K (Nat.card G3) :=
  HasEnoughRootsOfUnity.of_dvd K (down_order_dvd source freeSource)

variable {K O k : Type} [Field K] [CommRing O] [IsDomain O] [Field k]
  [Algebra O K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (rootX : PrimeRegularRootEmbedding 2 k K X)

/-- Restricting the root convention retains its values on every target root. -/
theorem downRoot_agrees
    (z : rootsOfUnity (primeRegularExponent 2 G3) k) :
    (TypeBQ3PrincipalBrauerInflation.downRoot
      (q source freeSource) (q_surjective source freeSource) rootX).lift ((z : kˣ) : k) =
        rootX.lift ((z : kˣ) : k) := by
  let rootDown := TypeBQ3PrincipalBrauerInflation.downRoot
    (q source freeSource) (q_surjective source freeSource) rootX
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion
    (surjectiveExponent_dvd (p := 2) (q source freeSource) (q_surjective source freeSource)) z
  calc
    rootDown.lift ((z : kˣ) : k) = rootDown.liftRoot z := rootDown.lift_coe z
    _ = rootX.liftRoot included := rfl
    _ = rootX.lift ((included : kˣ) : k) := (rootX.lift_coe included).symm
    _ = rootX.lift ((z : kˣ) : k) := rfl

/-- The actual residue map of the same modular system remains calibrated. -/
theorem downRoot_residue (Msys : ModularSystem 2 K O k)
    (calibration : RootResidueCompatible Msys rootX) :
    RootResidueCompatible Msys
      (TypeBQ3PrincipalBrauerInflation.downRoot
        (q source freeSource) (q_surjective source freeSource) rootX) := by
  intro z hz
  letI : NeZero (primeRegularExponent 2 G3) :=
    ⟨(primeRegularExponent_pos 2 G3).ne'⟩
  let zbar : rootsOfUnity (primeRegularExponent 2 G3) k :=
    rootsOfUnity.mkOfPowEq (Msys.residue z) (by rw [← map_pow, hz, map_one])
  have hval : ((zbar : kˣ) : k) = Msys.residue z := rfl
  rw [← hval, downRoot_agrees, hval]
  apply calibration
  obtain ⟨d, hd⟩ :=
    surjectiveExponent_dvd (p := 2) (q source freeSource) (q_surjective source freeSource)
  rw [hd, pow_mul, hz, one_pow]

end ModularRep.PaperProofs.TypeBQ3B2RootDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
