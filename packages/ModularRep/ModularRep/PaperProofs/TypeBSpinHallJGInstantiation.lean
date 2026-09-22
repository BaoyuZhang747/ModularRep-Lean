import ModularRep.PaperProofs.TypeBCriterionCarrierBindings
import ModularRep.PaperProofs.TypeBSpinDiagonalNormSource
import ModularRep.PaperProofs.TypeBFLZModularRootBinding

/-!
# The all-pairs Hall/J equality on the actual Spin carriers

The quotient by Spin is identified by the defining Clifford norm with
the actual field unit group. It has order q - 1 in positive rank. This
is distinct from the quotient by Spin joined with the special Clifford
centre, whose order two is supplied by the constructed norm-square map.

Only a Hall subgroup of the literal first quotient, with prime-to-ell
order and ell-power index, can remain a routine E1 choice. The helper
below constructs the existing Hall source with cyclicity deduced from
the norm. Its preimage is the actual quotient-map preimage.

The final equality reuses the checked all-pairs inertia argument with
the actual conjugation/Frobenius action, the norm-derived diagonal, and
the Spin root restricted from the same modular-system/cyclotomic choice.
There is no matching, supplied J_G equality, DGN interpretation, arbitrary
diagonal, ordinary algebraic closure or full criterion input.

Source locators: FLZ Section 3.1, p. 541 for SC/Spin, Remark 2.2, p. 537
for the odd-prime J_G argument; Brough--Spaeth Hypothesis 2.13 and Lemmas
2.14--2.15 for the inertia-times-Hall definition. The narrowly sourced
centre certificate is the same matched E1 input of the norm-square module.
-/

noncomputable section
set_option autoImplicit false

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBSpinHallJGInstantiation

open ModularRep TypeBCliffordCarriers TypeBCriterionHypotheses
open TypeBCriterionCarrierBindings TypeBCliffordCentreSource

section NormQuotient

variable {n : ℕ} {F : Type} [Field F] (N : NormSource n F)

/-- The actual norm quotient in positive rank is the field unit group. -/
def normQuotientEquiv (rank : 1 ≤ n) :
    (SpecialClifford n F ⧸ SpinSubgroup n F N) ≃* Fˣ :=
  QuotientGroup.quotientKerEquivOfSurjective N.norm
    (TypeBCliffordNormSurjectivity.norm_surjective n F rank N)

/-- The quotient equivalence sends the actual class of g to its defining norm. -/
theorem normQuotientEquiv_mk (rank : 1 ≤ n) (g : SpecialClifford n F) :
    normQuotientEquiv N rank (QuotientGroup.mk' (SpinSubgroup n F N) g) =
      N.norm g := rfl

/-- Cyclicity needs only the injective norm kernel lift into finite-field units. -/
theorem normQuotient_cyclic [Finite F] :
    IsCyclic (SpecialClifford n F ⧸ SpinSubgroup n F N) :=
  isCyclic_of_injective (QuotientGroup.kerLift N.norm)
    (QuotientGroup.kerLift_injective N.norm)

/-- SC/Spin has order q - 1, rather than the order-two diagonal quotient. -/
theorem normQuotient_card [Finite F] (rank : 1 ≤ n) :
    Nat.card (SpecialClifford n F ⧸ SpinSubgroup n F N) = Nat.card F - 1 :=
  (Nat.card_congr (normQuotientEquiv N rank).toEquiv).trans (Nat.card_units F)

/-- Package only actual Hall-subgroup data; quotient cyclicity is a deduction. -/
def hallSource [Finite F] {ell : ℕ} (prime : Nat.Prime ell)
    (H : Subgroup (SpecialClifford n F ⧸ SpinSubgroup n F N))
    (order_primeTo : ell.Coprime (Nat.card H)) (exponent : ℕ)
    (index_eq : H.index = ell ^ exponent) :
    TypeBInertiaHallSource.HallPrimeToQuotientSource N ell where
  prime := prime
  quotient_cyclic := normQuotient_cyclic N
  hall := H
  order_primeTo := order_primeTo
  exponent := exponent
  index_eq := index_eq

/-- The helper preserves the exact Hall preimage, including its quotient map. -/
theorem hallSource_preimage [Finite F] {ell : ℕ} (prime : Nat.Prime ell)
    (H : Subgroup (SpecialClifford n F ⧸ SpinSubgroup n F N))
    (order_primeTo : ell.Coprime (Nat.card H)) (exponent : ℕ)
    (index_eq : H.index = ell ^ exponent) :
    (hallSource N prime H order_primeTo exponent index_eq).preimage =
      H.comap (QuotientGroup.mk' (SpinSubgroup n F N)) := rfl

end NormQuotient

section ActualHallJG

variable {n p f ell : ℕ} {F K O k : Type}
variable [Field F] [Finite F] [CharP F p] [NeZero f] [Finite (Clifford n F)]
variable [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (scope : TypeBFLZLabelSource.Applicability p ell n)
variable (N : NormSource n F) (fs : FieldActionSource n F p f parameters N)
variable (centre : CentreSource n F parameters (Nat.le_trans (by decide : 1 ≤ 3) scope.rank))
variable (Msys : ModularSystem ell K O k)
variable (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
variable (hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell)

/-- The criterion and source Hall packets have literally the same preimage. -/
theorem hallData_preimage : (hallData N hall).preimage = hall.preimage := rfl

/-- Restriction of the actual ambient action is the same inverse Spin conjugation. -/
theorem naturalAction_comp_inl :
    (CyclicOuterLemma37Concrete.inverseOpHom (naturalAction N fs).hom).comp
        SemidirectProduct.inl = TypeBInertiaHallSource.spinConjugation N := by
  apply MonoidHom.ext
  intro m
  change MulOpposite.op (TypeBAutomorphismSource.ambientAutomorphism fs
      ((SemidirectProduct.inl m)⁻¹)) =
    MulOpposite.op (MulAut.conjNormal (H := SpinSubgroup n F N) m⁻¹)
  rw [← map_inv]
  exact congrArg MulOpposite.op
    (TypeBAutomorphismSource.ambientAutomorphism_inl fs m⁻¹)

/-- The criterion's lower Brauer inertia is the literal Spin conjugation inertia. -/
theorem brauerMInertia_eq_literal
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N)) (phi : IBr iota) :
    brauerMInertia (SpinSubgroup n F N) fs.action (naturalAction N fs) iota phi =
      TypeBInertiaHallSource.brauerInertia N iota phi := by
  change (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ phi).comap
      ((CyclicOuterLemma37Concrete.inverseOpHom (naturalAction N fs).hom).comp
        SemidirectProduct.inl) = _
  rw [naturalAction_comp_inl]
  rfl

/-- The criterion's lower weight-class inertia uses the same literal action. -/
theorem weightMInertia_eq_literal
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    weightMInertia (SpinSubgroup n F N) fs.action (naturalAction N fs) W =
      TypeBInertiaHallSource.weightInertia N W := by
  change (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ W).comap
      ((CyclicOuterLemma37Concrete.inverseOpHom (naturalAction N fs).hom).comp
        SemidirectProduct.inl) = _
  rw [naturalAction_comp_inl]
  rfl

include centre in
/-- Every actual lower Brauer inertia and every actual lower weight-class
inertia have the same product with the actual Hall preimage. The diagonal
and root conventions are constructed here, and no pairing is selected. -/
theorem allPairsJG_modular_instantiated :
    AllPairsJG (SpinSubgroup n F N) fs.action (naturalAction N fs)
      (TypeBFLZModularRootBinding.spinRoot Msys choice N) (hallData N hall) := by
  let diagonal := TypeBSpinDiagonalNormSource.diagonalSource n F N parameters
    (Nat.le_trans (by decide : 1 ≤ 3) scope.rank) centre
  intro phi W
  rw [brauerMInertia_eq_literal, weightMInertia_eq_literal]
  exact (TypeBInertiaHallSource.brauerInertia_mul_hallPreimage_eq_univ
    N (TypeBFLZModularRootBinding.spinRoot Msys choice N) scope.modular_odd
    diagonal.diagonal diagonal.surjective diagonal.kernel hall phi).trans
      (TypeBInertiaHallSource.weightInertia_mul_hallPreimage_eq_univ
        N scope.modular_odd diagonal.diagonal diagonal.surjective diagonal.kernel hall W).symm

end ActualHallJG

end ModularRep.PaperProofs.TypeBSpinHallJGInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
