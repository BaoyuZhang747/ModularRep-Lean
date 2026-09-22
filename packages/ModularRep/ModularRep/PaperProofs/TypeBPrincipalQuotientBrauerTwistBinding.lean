import ModularRep.PaperProofs.TypeBPrincipalCommonTrivialTwist
import ModularRep.PaperProofs.TypeBModularGroupRootBinding
import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent

/-!
# The literal quotient Brauer character of the common trivial twist

The actual quotient uses the root convention constructed from the same
modular system. Its trivial representation on the residue field is
one-dimensional and irreducible. Inflation uses the existing surjective
pullback constructor and the calibrated ambient root. Its character is
exactly the lifted linear character already used by the common twist.
The ordinary character remains the existing selected quotient lift.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalQuotientBrauerTwistBinding

open ModularRep
open TypeBModularGroupRootBinding TypeBModularLinearCharacterLift
open IrreducibleBrauerCharacterSurjectiveDescent

variable {k H : Type} [Field k] [CharP k 2] [Group H] [Finite H]
  (G : Subgroup H) [G.Normal]

/-- The actual trivial linear character of the actual quotient. -/
def quotientLinearCharacter : H ⧸ G →* kˣ := 1

/-- The existing quotient identification inflates that same character. -/
def quotientLambda : linearCharactersTrivialOn (k := k) G :=
  (LinearCharactersTrivialOn.quotientMulEquiv (k := k) G).symm
    (quotientLinearCharacter (k := k) G)

@[simp]
theorem quotientLambda_eq_one : quotientLambda (k := k) G = 1 :=
  map_one (LinearCharactersTrivialOn.quotientMulEquiv (k := k) G).symm

/-- Inflation at an actual group element is the quotient-map formula. -/
theorem quotientLambda_apply (h : H) :
    (quotientLambda (k := k) G).val h =
      quotientLinearCharacter (k := k) G (QuotientGroup.mk' G h) := rfl

/-- The affording representation has the residue field as its vector space. -/
def quotientRepresentation : Representation k (H ⧸ G) k :=
  Representation.trivial k (H ⧸ G) k

theorem quotientRepresentation_apply (x : H ⧸ G) (v : k) :
    quotientRepresentation (k := k) G x v =
      (quotientLinearCharacter (k := k) G x : k) • v := by
  simp [quotientRepresentation, quotientLinearCharacter, Representation.trivial]

theorem quotientRepresentation_finrank :
    Module.finrank k (FDRep.of (quotientRepresentation (k := k) G)) = 1 :=
  Module.finrank_self k

/-- A subrepresentation is a subspace of the one-dimensional residue field. -/
theorem quotientRepresentation_irreducible :
    Representation.IsIrreducible (quotientRepresentation (k := k) G) := by
  letI : Nontrivial (Subrepresentation (quotientRepresentation (k := k) G)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule k k) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  letI : IsSimpleOrder (Submodule k k) :=
    is_simple_module_of_finrank_eq_one (Module.finrank_self k)
  refine IsSimpleOrder.mk ?_
  intro W
  rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.ext h)
  · exact Or.inr (Subrepresentation.ext h)

variable {K O : Type} [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharZero K] [IsAlgClosed k] (Msys : ModularSystem 2 K O k)

/-- The actual quotient convention comes from the prescribed residue map. -/
def quotientRoot : PrimeRegularRootEmbedding 2 k K (H ⧸ G) :=
  groupRoot Msys (H ⧸ G)

theorem quotientRoot_residue (z : O)
    (hz : z ^ primeRegularExponent 2 (H ⧸ G) = 1) :
    (quotientRoot G Msys).lift (Msys.residue z) = algebraMap O K z :=
  groupRoot_residue Msys (H ⧸ G) z hz

/-- The quotient character is an actual irreducible Brauer character. -/
def quotientBrauer : IBr (quotientRoot G Msys) :=
  ⟨Representation.brauerCharacterOfRootEmbedding
      (quotientRepresentation (k := k) G) (quotientRoot G Msys),
    ⟨FDRep.of (quotientRepresentation (k := k) G),
      quotientRepresentation_irreducible G, rfl⟩⟩

theorem quotientBrauer_affords :
    (quotientBrauer G Msys).val =
      Representation.brauerCharacterOfRootEmbedding
        (quotientRepresentation (k := k) G) (quotientRoot G Msys) := rfl

@[simp]
theorem quotientBrauer_apply (x : PrimeRegularElement (G := H ⧸ G) 2) :
    (quotientBrauer G Msys).val x = 1 := by
  change (Multiset.map (quotientRoot G Msys).lift
    ((1 : k →ₗ[k] k).charpoly.roots)).sum = 1
  rw [LinearMap.charpoly_one, Module.finrank_self, pow_one]
  rw [show (1 : Polynomial k) = Polynomial.C 1 by simp]
  rw [Polynomial.roots_X_sub_C]
  simp only [Multiset.map_singleton, Multiset.sum_singleton]
  simpa [PrimeRegularRootEmbedding.liftRoot] using
    (quotientRoot G Msys).lift_coe
      (1 : rootsOfUnity (primeRegularExponent 2 (H ⧸ G)) k)

theorem quotientBrauer_degree_one :
    (quotientBrauer G Msys).val ⟨1, isPrimeRegular_one⟩ = 1 :=
  quotientBrauer_apply G Msys ⟨1, isPrimeRegular_one⟩

/-- The literal quotient character equals its lifted modular linear character. -/
theorem quotientBrauer_linearCharacter :
    (quotientBrauer G Msys).val =
      (quotientRoot G Msys).liftedLinearCharacter
        (quotientLinearCharacter (k := k) G) := by
  rw [quotientLinearCharacter, PrimeRegularRootEmbedding.liftedLinearCharacter_one]
  ext x
  exact quotientBrauer_apply G Msys x

variable (iota : PrimeRegularRootEmbedding 2 k K H)
  (calibration : ∀ z : O, z ^ primeRegularExponent 2 H = 1 →
    iota.lift (Msys.residue z) = algebraMap O K z)

include calibration in
/-- Compatibility uses only roots occurring after the actual quotient map. -/
theorem quotientRoot_compatible (V : FDRep k (H ⧸ G)) :
    Representation.BrauerRootLiftCompatibleAlong V.ρ
      (quotientRoot G Msys) iota (QuotientGroup.mk' G) := by
  rw [eq_groupRoot_of_residue Msys H iota calibration]
  exact groupRoot_compatible_along Msys V.ρ (QuotientGroup.mk' G)

/-- Use the checked inflation constructor, retaining its kernel witness. -/
def inflatedBrauer : IBr iota :=
  (inflateToKernelTrivialIBrAlong (QuotientGroup.mk' G)
    (QuotientGroup.mk'_surjective G) iota (quotientRoot G Msys)
    (quotientRoot_compatible G Msys iota calibration) (quotientBrauer G Msys)).val

theorem inflatedBrauer_val :
    (inflatedBrauer G Msys iota calibration).val =
      PrimeRegularClassFunction.pullback (QuotientGroup.mk' G)
        (quotientBrauer G Msys).val := rfl

@[simp]
theorem inflatedBrauer_apply (h : PrimeRegularElement (G := H) 2) :
    (inflatedBrauer G Msys iota calibration).val h = 1 :=
  quotientBrauer_apply G Msys (PrimeRegularElement.map (QuotientGroup.mk' G) h)

/-- Inflation agrees with the same modular character used by tensoring. -/
theorem inflatedBrauer_linearCharacter :
    (inflatedBrauer G Msys iota calibration).val =
      iota.liftedLinearCharacter (quotientLambda (k := k) G).val := by
  rw [quotientLambda_eq_one]
  change (inflatedBrauer G Msys iota calibration).val =
    iota.liftedLinearCharacter (1 : H →* kˣ)
  rw [PrimeRegularRootEmbedding.liftedLinearCharacter_one]
  ext h
  exact inflatedBrauer_apply G Msys iota calibration h

/-- The selected ordinary lift is the existing whole-group lift of one. -/
theorem selectedOrdinaryLift_eq_one :
    quotientLift iota G (quotientLambda (k := k) G) = (1 : H →* Kˣ) := by
  rw [quotientLambda_eq_one]
  exact TypeBPrincipalCommonTrivialTwist.selectedOrdinaryLift_one G iota

/-- The selected lift's value agrees with the actual inflated Brauer value. -/
theorem selectedOrdinaryLift_regular_value (h : PrimeRegularElement (G := H) 2) :
    (quotientLift iota G (quotientLambda (k := k) G) h.val : K) =
      (inflatedBrauer G Msys iota calibration).val h := by
  rw [selectedOrdinaryLift_eq_one, inflatedBrauer_apply]
  rfl

/-- Pointwise multiplication by the literal inflated quotient character is
the previously constructed tensor operation. -/
theorem brauer_twist_inflated
    (productFormula : BrauerLinearTensorProductFormula iota) (Phi : IBr iota) :
    (IrreducibleBrauerCharacter.linearTwist iota productFormula Phi
      (quotientLambda (k := k) G).val).val =
      PrimeRegularClassFunction.pointwiseMul
        (inflatedBrauer G Msys iota calibration).val Phi.val := by
  rw [IrreducibleBrauerCharacter.linearTwist_val,
    inflatedBrauer_linearCharacter]

theorem brauer_twist_eq_self
    (productFormula : BrauerLinearTensorProductFormula iota) (Phi : IBr iota) :
    IrreducibleBrauerCharacter.linearTwist iota productFormula Phi
      (quotientLambda (k := k) G).val = Phi := by
  rw [quotientLambda_eq_one]
  exact IrreducibleBrauerCharacter.linearTwist_one iota productFormula Phi

variable (indexTwo : G.index = 2)

include indexTwo in
/-- At index two, every old quotient-twist parameter is this exact one. -/
theorem lambda_eq_quotientLambda (lambda : linearCharactersTrivialOn (k := k) G) :
    lambda = quotientLambda (k := k) G :=
  (TypeBPrincipalCommonTrivialTwist.linearCharacter_eq_one G indexTwo lambda).trans
    (quotientLambda_eq_one G).symm

include indexTwo in
/-- The old selected ordinary lift is unchanged for every quotient parameter. -/
theorem selectedOrdinaryLift_eq_quotientLambda
    (lambda : linearCharactersTrivialOn (k := k) G) :
    quotientLift iota G lambda = quotientLift iota G (quotientLambda (k := k) G) :=
  congrArg (quotientLift iota G) (lambda_eq_quotientLambda G indexTwo lambda)

/-- The original ordinary weight-class tensor operation uses the same lift. -/
theorem weightClass_twist_eq_self
    (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := H)) :
    TypeCWeightTensorFieldAction.CharacterWeight.linearTwistConjugacyClass
      (TypeBPrincipalCommonTrivialTwist.radicalLift G indexTwo iota
        (quotientLambda (k := k) G)) v = v :=
  TypeBPrincipalCommonTrivialTwist.weightClass_twist_eq_self
    G indexTwo iota (quotientLambda (k := k) G) v

end ModularRep.PaperProofs.TypeBPrincipalQuotientBrauerTwistBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
