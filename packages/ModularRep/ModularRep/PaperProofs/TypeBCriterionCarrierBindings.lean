import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.TypeBAutomorphismSource
import ModularRep.PaperProofs.TypeBInertiaHallSource

/-!
# The criterion's structural and J_G clauses on actual Spin carriers

The generic criterion domain is bound to the already constructed Clifford
norm kernel, Frobenius semidirect product, natural automorphism map, and
literal inertia subgroups. The J_G equality is a deduction from the checked
odd-prime Hall-index argument, for every actual constituent and covered
weight. There is no supplied J_G function or equality of matching targets.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBCriterionCarrierBindings

open ModularRep TypeBCliffordCarriers
open TypeBCriterionHypotheses

variable {n p f ell : ℕ} {F k K : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [IsAlgClosed K] [NeZero f]
variable (N : NormSource n F) [Finite (SpecialClifford n F)]
variable {parameters : OddFieldParameters F p f}
variable (S : FieldActionSource n F p f parameters N)

/-- The criterion uses the already checked natural conjugation/Frobenius
homomorphism; its complete pointwise formula is retained. -/
def naturalAction : NaturalAction (SpinSubgroup n F N) S.action where
  hom := TypeBAutomorphismSource.ambientAutomorphism S
  value := TypeBAutomorphismSource.ambientAutomorphism_coe S

/-- The source structural data give the literal generic criterion clause.
The derived-group and centralizer identities are deductions, and the
acting group's commutativity follows from its actual cyclic carrier. -/
theorem structural (source : TypeBAutomorphismSource.StructuralSource S) :
    Structural (SpinSubgroup n F N) S.action (naturalAction N S) where
  derived := TypeBAutomorphismSource.derived_eq_spin N source.spin_perfect
  acting_abelian := inferInstance
  quotient_cyclic := source.quotient_cyclic
  centralizer := TypeBAutomorphismSource.centralizer_eq_embeddedCenter S source
  natural_kernel := source.kernel
  natural_surjective := source.surjective
  outer_abelian := source.outer_abelian

/-- The Hall source is passed through with the same quotient subgroup. -/
def hallData (hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell) :
    HallData (SpinSubgroup n F N) ell where
  hall := hall.hall
  order_primeTo := hall.order_primeTo
  exponent := hall.exponent
  index := hall.index_eq

theorem naturalAction_on_specialClifford :
    (CyclicOuterLemma37Concrete.inverseOpHom (naturalAction N S).hom).comp
        SemidirectProduct.inl = TypeBInertiaHallSource.spinConjugation N := by
  apply MonoidHom.ext
  intro m
  change MulOpposite.op (TypeBAutomorphismSource.ambientAutomorphism S
      ((SemidirectProduct.inl m)⁻¹)) =
    MulOpposite.op (MulAut.conjNormal (H := SpinSubgroup n F N) m⁻¹)
  rw [← map_inv]
  exact congrArg MulOpposite.op
    (TypeBAutomorphismSource.ambientAutomorphism_inl S m⁻¹)

variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

theorem brauerMInertia_eq (phi : IBr iota) :
    brauerMInertia (SpinSubgroup n F N) S.action (naturalAction N S) iota phi =
      TypeBInertiaHallSource.brauerInertia N iota phi := by
  change (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ phi).comap
      ((CyclicOuterLemma37Concrete.inverseOpHom (naturalAction N S).hom).comp
        SemidirectProduct.inl) = _
  rw [naturalAction_on_specialClifford]
  rfl

theorem weightMInertia_eq
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    weightMInertia (SpinSubgroup n F N) S.action (naturalAction N S) W =
      TypeBInertiaHallSource.weightInertia N W := by
  change (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ W).comap
      ((CyclicOuterLemma37Concrete.inverseOpHom (naturalAction N S).hom).comp
        SemidirectProduct.inl) = _
  rw [naturalAction_on_specialClifford]
  rfl

/-- The stronger, choice-independent form used at the published criterion
boundary. No DGN interpretation is needed: it applies to every possible
downstairs constituent and covered weight class. -/
theorem allPairsJG
    (hOdd : Odd ell)
    (diagonal : SpecialClifford n F →* TypeBSpinStabilizer.DiagonalGroup)
    (surjective : Function.Surjective diagonal)
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))
    (hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell) :
    AllPairsJG (SpinSubgroup n F N) S.action (naturalAction N S)
      iota (hallData N hall) := by
  intro phi W
  rw [brauerMInertia_eq, weightMInertia_eq]
  exact (TypeBInertiaHallSource.brauerInertia_mul_hallPreimage_eq_univ
    N iota hOdd diagonal surjective kernel hall phi).trans
      (TypeBInertiaHallSource.weightInertia_mul_hallPreimage_eq_univ
        N hOdd diagonal surjective kernel hall W).symm

/-- Both sides of the published J_G compatibility clause equal the
whole special Clifford group. The criterion's actual constituent and
covered-weight predicates remain visible in its type; the stronger index
deduction makes the equality independent of those choices. -/
theorem JG_compatible
    (iotaM : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (hOdd : Odd ell)
    (diagonal : SpecialClifford n F →* TypeBSpinStabilizer.DiagonalGroup)
    (surjective : Function.Surjective diagonal)
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))
    (hall : TypeBInertiaHallSource.HallPrimeToQuotientSource N ell)
    (dgn : TypeBWeightCoveringSource.DGNSource
      (ell := ell) (k := k) (K := K) (SpinSubgroup n F N))
    (omega : IBr iotaM ≃ CharacterWeight.ConjugacyClass
      (p := ell) (K := K) (G := SpecialClifford n F)) :
    JGCompatible (SpinSubgroup n F N) S.action (naturalAction N S)
      iotaM iota (hallData N hall) dgn omega := by
  intro Phi phi W _hphi _hW
  rw [brauerMInertia_eq, weightMInertia_eq]
  exact (TypeBInertiaHallSource.brauerInertia_mul_hallPreimage_eq_univ
    N iota hOdd diagonal surjective kernel hall phi).trans
      (TypeBInertiaHallSource.weightInertia_mul_hallPreimage_eq_univ
        N hOdd diagonal surjective kernel hall W).symm

end ModularRep.PaperProofs.TypeBCriterionCarrierBindings


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
