import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionStructure
import ModularRep.PaperProofs.TypeBMatrixOmegaFullAutomorphismBinding

/-!
# Derived structural fields on the actual matrix carriers

The natural matrix action is exactly the action exported by Carriers.
The full Spin cover and its literal automorphism square transport the
existing Spin kernel and surjectivity clauses to that action. The same
Clifford centre source identifies its centralizer and embedded SO centre.
The index-two quotient and the cyclic field group then imply that the
full outer automorphism group of matrix Omega is abelian.

The output structure contains only the structural fields used by the
one-block criterion. Its constructor derives those fields from the same
rank, field, norm, projection, centre and full-cover data. It is not a
new source predicate or a completed criterion, matching or triple packet.
The broader Spin StructuralSource is not required: its unused perfectness,
quotient-cyclicity and outer-commutativity fields are not added here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionMatrixStructure

open ModularRep TypeBCliffordCarriers
open TypeBAllRankPrincipalCriterionCarriers TypeBCriterionHypotheses
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open EvenFieldFLZ318FixedTheoremGate EvenFieldFLZSourceConditions

attribute [local instance] TypeBAllRankPrincipalCriterionCarriers.omegaFintype

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters (rank3 rank) N)
  (S : FieldActionSource n F r f parameters N)

/-- The existing positive field degree makes the actual field group finite. -/
def fieldGroupFinite : Finite (FieldGroup f) := by
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  infer_instance

/-- This is the actual cyclic group, before imposing any criterion clause. -/
theorem fieldGroup_cyclic : IsCyclic (FieldGroup f) := inferInstance

/-- Its commutativity is a deduction on the fixed field actor. -/
theorem acting_abelian : IsMulCommutative (FieldGroup f) := by
  letI : IsCyclic (FieldGroup f) := fieldGroup_cyclic
  infer_instance

/-- The field factor of the same natural action is the prescribed Omega action. -/
theorem matrixNaturalAction_inr (e : FieldGroup f) :
    (matrixNaturalAction parameters rank N C S).hom (SemidirectProduct.inr e) =
      omegaAction parameters rank N C S e :=
  TypeBCliffordOrthogonalAmbientActionBinding.omegaAmbientAction_inr S (rank3 rank) C e

/-- Counting the actual semidirect carrier retains its complete field factor. -/
theorem ambient_card :
    Nat.card (Ambient (fieldAction parameters rank N C S)) =
      Nat.card (H n F) * Nat.card (FieldGroup f) :=
  SemidirectProduct.card

/-- The SO order divides the order of the same ordinary-extension ambient. -/
theorem so_order_dvd_ambient :
    Nat.card (H n F) ∣ Nat.card (Ambient (fieldAction parameters rank N C S)) :=
  ⟨Nat.card (FieldGroup f), ambient_card parameters rank N C S⟩

/-- The single ambient-root guard supplies SO roots by the actual order divisor. -/
def ordinaryRoots_of_ambientRoots {K : Type} [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (Ambient (fieldAction parameters rank N C S)))] :
    HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
  HasEnoughRootsOfUnity.of_dvd K (so_order_dvd_ambient parameters rank N C S)

/-- Index two makes the trivial quotient subgroup the canonical two-prime Hall subgroup. -/
def canonicalHall : HallData (G n F) 2 where
  hall := ⊥
  order_primeTo := by simp
  exponent := 1
  index := by
    rw [Subgroup.index_bot, pow_one]
    exact (G n F).index_eq_card.symm.trans (omega_index_two parameters rank N C)

/-- Its preimage is the original Omega subgroup of SO. -/
theorem canonicalHall_preimage : (canonicalHall parameters rank N C).preimage = G n F := by
  ext h
  change QuotientGroup.mk' (G n F) h = 1 ↔ h ∈ G n F
  exact QuotientGroup.eq_one_iff h

variable
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
  (fullCover : IsUniversalCentralExtension (spinProjection parameters rank N C))
  (centreClifford : TypeBCliffordCentreSource.CentreSource n F parameters
    ((by decide : 1 ≤ 3).trans (rank3 rank)))
  (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism S).ker =
    TypeBAutomorphismSource.embeddedCenter S)
  (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S))

include centreSpin fullCover naturalSurjective in
/-- Surjectivity is transported through the actual full-cover automorphism square. -/
theorem natural_surjective :
    Function.Surjective (matrixNaturalAction parameters rank N C S).hom :=
  TypeBMatrixOmegaFullAutomorphismBinding.omegaAmbientAction_surjective
    S (rank3 rank) C centreSpin fullCover naturalSurjective

include centreSpin fullCover centreClifford naturalKernel in
/-- Both sides are the literal subgroups of the SO/field semidirect product. -/
theorem natural_kernel :
    (matrixNaturalAction parameters rank N C S).hom.ker =
      embeddedCenter (fieldAction parameters rank N C S) :=
  (TypeBMatrixOmegaFullAutomorphismBinding.omegaAmbientAction_ker_eq_bot
    S (rank3 rank) C centreSpin fullCover centreClifford naturalKernel).trans
      (TypeBMatrixOmegaFullAutomorphismBinding.embeddedSOCenter_eq_bot
        S (rank3 rank) C centreSpin fullCover centreClifford naturalKernel).symm

include centreSpin fullCover centreClifford naturalKernel in
/-- The centralizer uses the original subgroup inclusion, not an abstract copy. -/
theorem centralizer :
    Subgroup.centralizer
        (embeddedG (G n F) (fieldAction parameters rank N C S) :
          Set (Ambient (fieldAction parameters rank N C S))) =
      embeddedCenter (fieldAction parameters rank N C S) :=
  TypeBMatrixOmegaFullAutomorphismBinding.centralizer_eq_embeddedSOCenter
    S (rank3 rank) C centreSpin fullCover centreClifford naturalKernel

include centreSpin fullCover naturalSurjective in
/-- The full outer group is abelian by derived index two and the actual field action. -/
theorem outer_abelian : IsMulCommutative (OuterAutomorphism (G n F)) := by
  letI : IsMulCommutative (FieldGroup f) := acting_abelian
  exact TypeBAllRankPrincipalCriterionStructure.outer_abelian
    (G n F) (fieldAction parameters rank N C S)
    (matrixNaturalAction parameters rank N C S)
    (omega_index_two parameters rank N C)
    (natural_surjective parameters rank N C S centreSpin fullCover naturalSurjective)

section PhysicalBlock

variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (root : PrimeRegularRootEmbedding 2 k K (X n F))
  (b : LiteralPrimitiveBlock k (X n F))

/-- Only the ten structural conclusions required by FixedBlockHypotheses.
This is constructed below; no inhabitant of this structure is an input. -/
structure StructuralData where
  cover : EllPrimeCoverSource 2 (G n F)
  divides_simple_order : 2 ∣ Nat.card cover.S
  centralFaithful : ∀ phi : BrauerFibre root b,
    Subgroup.center (G n F) ⊓
      (EvenFieldFLZBAWGoodFamily.chosenIBrRepresentation root phi.val).ρ.ker = ⊥
  block_invariant : ∀ alpha : (MulAut (G n F))ᵐᵒᵖ, alpha • b = b
  derived : commutator (H n F) = G n F
  acting_abelian : IsMulCommutative (FieldGroup f)
  centralizer : Subgroup.centralizer
      (embeddedG (G n F) (fieldAction parameters rank N C S) :
        Set (Ambient (fieldAction parameters rank N C S))) =
    embeddedCenter (fieldAction parameters rank N C S)
  natural_kernel : (matrixNaturalAction parameters rank N C S).hom.ker =
    embeddedCenter (fieldAction parameters rank N C S)
  natural_surjective : Function.Surjective (matrixNaturalAction parameters rank N C S).hom
  outer_abelian : IsMulCommutative (OuterAutomorphism (G n F))

/-- Combine the structural fields without assuming any matrix-side field.
The principal-block decomposition is the same specified decomposition used
in the character transport; the centreless character claim holds for all
characters and is restricted here only to the required principal fibre. -/
def structuralData
    (simple : IsSimpleGroup (X n F)) (nonabelian : ¬ IsMulCommutative (X n F))
    [Fintype (LiteralPrimitiveBlock k (X n F))]
    (matrixBlocks : BlockIdempotentDecomposition
      (fun c : LiteralPrimitiveBlock k (X n F) => c.val))
    (principal : IsPrincipal b) :
    StructuralData parameters rank N C S root b where
  cover := identityCover parameters rank N C centreSpin fullCover simple nonabelian
  divides_simple_order := two_dvd_card parameters rank N C
  centralFaithful := fun phi =>
    TypeBAllRankPrincipalCriterionCarriers.centralFaithful simple nonabelian root phi.val
  block_invariant :=
    TypeBCentralKernelPrincipalStability.principal_op_smul_eq matrixBlocks b principal
  derived := omega_derived n F
  acting_abelian := acting_abelian
  centralizer := centralizer parameters rank N C S centreSpin fullCover centreClifford naturalKernel
  natural_kernel := natural_kernel parameters rank N C S centreSpin fullCover centreClifford naturalKernel
  natural_surjective := natural_surjective parameters rank N C S centreSpin fullCover naturalSurjective
  outer_abelian := outer_abelian parameters rank N C S centreSpin fullCover naturalSurjective

end PhysicalBlock

section CalibratedRoots

variable {K O k : Type} [Field K] [CharZero K] [CommRing O] [IsDomain O]
  [Field k] [Algebra O K] [CharP k 2] [IsAlgClosed k]
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (X n F))
  (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
  (compatible : TypeBLocalReductionInstantiation.RootResidueCompatible Msys root)
  (compatibleH : TypeBLocalReductionInstantiation.RootResidueCompatible Msys rootH)

include parameters rank N C compatible compatibleH in
/-- The exact root-agreement field follows from the same individual calibrations. -/
theorem roots_agree : RootAgreement (G n F) rootH root := by
  intro zeta
  exact congrFun (TypeBAllRankPrincipalCriterionCarriers.omega_so_root_lifts
    parameters rank N C Msys root rootH compatible compatibleH) (((zeta : kˣ) : k))

end CalibratedRoots

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionMatrixStructure


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
