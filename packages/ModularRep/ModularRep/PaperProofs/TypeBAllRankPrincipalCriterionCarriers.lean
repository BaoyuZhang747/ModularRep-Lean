import ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover
import ModularRep.PaperProofs.TypeBMatrixOmegaBSStructure
import ModularRep.PaperProofs.TypeBMatrixOmegaEvenOrder
import ModularRep.PaperProofs.TypeBPrincipalRootLiftBinding
import ModularRep.PaperProofs.TypeBBSCentralCharacterQuotient
import ModularRep.PaperProofs.TypeBCliffordOrthogonalAmbientActionBinding
import ModularRep.PaperProofs.TypeBCriterionHypotheses

/-!
# Actual carriers for the all-rank principal criterion

SO and Omega are the existing split matrix carriers. Omega is literally
the commutator subgroup of SO, and Spin is the same norm kernel used by
the accepted selector. No rank-three specified source is instantiated.

The identity prime-to-two cover uses the full universal property of the
constructed Spin projection, its proved two-kernel, and the retained
simple/nonabelian hypotheses. Those structural facts remain E1/U on the
specified field and norm. Centrelessness and character central
faithfulness are deductions, not additional source fields.

The last theorem transports an internally obtained Spin fixation result.
Its prescribed roots are calibrated to the same modular system; the old
Spin-centre quotient root is constructed from that system. Upper SO
character transport and weight-class/raw-representative distinctions are
handled by the separate upper and selector constructions.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers

open ModularRep TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding

/-- The literal special orthogonal matrix group. -/
abbrev H (n : ℕ) (F : Type) [Field F] :=
  TypeBOrthogonalOmegaCarriers.SpecialOrthogonal n F

/-- The actual normal subgroup of SO, rather than an abstract copy. -/
abbrev G (n : ℕ) (F : Type) [Field F] : Subgroup (H n F) :=
  TypeBOrthogonalOmegaCarriers.omegaSubgroup n F

/-- The carrier of that same subgroup is the existing matrix Omega. -/
abbrev X (n : ℕ) (F : Type) [Field F] :=
  TypeBOrthogonalOmegaCarriers.Omega n F

/-- The inherited generic structural interfaces require only rank three. -/
def rank3 {n : ℕ} (rank : 4 ≤ n) : 3 ≤ n :=
  (show 3 ≤ 4 by decide).trans rank

theorem excludes_rank_three {n : ℕ} (rank : 4 ≤ n) : n ≠ 3 := by
  intro h
  subst n
  exact (by decide : ¬ 4 ≤ 3) rank

theorem omega_derived (n : ℕ) (F : Type) [Field F] :
    commutator (H n F) = G n F := rfl

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  (parameters : OddFieldParameters F r f) (rank : 4 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters (rank3 rank) N)

include parameters rank N C in
/-- The index-two statement is derived from the same projection and norm. -/
theorem omega_index_two : (G n F).index = 2 :=
  TypeBMatrixOmegaBSStructure.omega_index_two N parameters (rank3 rank) C

include parameters rank N C in
/-- An actual projected Clifford involution proves that Omega has even order. -/
theorem two_dvd_card : 2 ∣ Nat.card (X n F) :=
  TypeBMatrixOmegaEvenOrder.two_dvd_card n F N parameters (rank3 rank) C

/-- The exact Spin projection supplies the full-cover source argument. -/
abbrev spinProjection : Spin n F N →* X n F :=
  TypeBCliffordOrthogonalSourceBinding.spinProjection n F parameters (rank3 rank) N C

theorem spinProjection_surjective :
    Function.Surjective (spinProjection parameters rank N C) :=
  TypeBCliffordOrthogonalSourceBinding.spinProjection_surjective
    n F parameters (rank3 rank) N C

local instance omegaFintype : Fintype (X n F) :=
  Fintype.ofFinite (X n F)

/-- The cover quotient is the identity on this matrix Omega carrier. -/
def identityCover
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (fullCover : EvenFieldFLZ318FixedTheoremGate.IsUniversalCentralExtension
      (spinProjection parameters rank N C))
    (simple : IsSimpleGroup (X n F))
    (nonabelian : ¬ IsMulCommutative (X n F)) :
    EvenFieldFLZSourceConditions.EllPrimeCoverSource 2 (X n F) :=
  TypeBMatrixOmegaPrimeToTwoCover.identityEllPrimeCover
    n F parameters (rank3 rank) N C centre fullCover simple nonabelian

@[simp] theorem identityCover_simpleGroup
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (fullCover : EvenFieldFLZ318FixedTheoremGate.IsUniversalCentralExtension
      (spinProjection parameters rank N C))
    (simple : IsSimpleGroup (X n F))
    (nonabelian : ¬ IsMulCommutative (X n F)) :
    (identityCover parameters rank N C centre fullCover simple nonabelian).S = X n F := rfl

@[simp] theorem identityCover_quotient
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (fullCover : EvenFieldFLZ318FixedTheoremGate.IsUniversalCentralExtension
      (spinProjection parameters rank N C))
    (simple : IsSimpleGroup (X n F))
    (nonabelian : ¬ IsMulCommutative (X n F)) :
    (identityCover parameters rank N C centre fullCover simple nonabelian).quotient =
      MonoidHom.id (X n F) := rfl

/-- No extra ambient-centralizer source is needed for this consequence. -/
theorem centerless (simple : IsSimpleGroup (X n F))
    (nonabelian : ¬ IsMulCommutative (X n F)) :
    Subgroup.center (X n F) = ⊥ :=
  OddTwoUniversalPrimeToTwoSelfCover.center_eq_bot_of_nonabelian_simple simple nonabelian

variable (S : FieldActionSource n F r f parameters N)

/-- The SO action is transported from the same Clifford field source. -/
abbrev fieldAction : FieldGroup f →* MulAut (H n F) :=
  TypeBCliffordOrthogonalAmbientQuotient.soFieldAction
    n F parameters (rank3 rank) N C S

/-- Its characteristic-subgroup restriction is the actual Omega action. -/
abbrev omegaAction : FieldGroup f →* MulAut (X n F) :=
  TypeBCliffordOrthogonalFullFieldBinding.omegaFieldAction S (rank3 rank) C

@[simp] theorem omegaAction_val (e : FieldGroup f) (x : X n F) :
    (omegaAction parameters rank N C S e x).val =
      fieldAction parameters rank N C S e x.val := rfl

theorem spinProjection_field (e : FieldGroup f) (g : Spin n F N) :
    spinProjection parameters rank N C (spinFieldAction n F S e g) =
      omegaAction parameters rank N C S e (spinProjection parameters rank N C g) :=
  TypeBCliffordOrthogonalFullFieldBinding.spinProjection_field S (rank3 rank) C e g

theorem fieldAction_eq_prime_pow (e : FieldGroup f) :
    fieldAction parameters rank N C S e =
      TypeBOrthogonalFieldAutomorphism.primeFrobeniusSpecialOrthogonal
        n F r parameters.prime ^ e.toAdd.val :=
  TypeBCliffordOrthogonalFullFieldBinding.soFieldAction_eq_prime_pow S (rank3 rank) C e

theorem omegaAction_eq_prime_pow (e : FieldGroup f) :
    omegaAction parameters rank N C S e =
      TypeBOrthogonalFieldAutomorphism.primeFrobeniusOmega
        n F r parameters.prime ^ e.toAdd.val :=
  TypeBCliffordOrthogonalFullFieldBinding.omegaFieldAction_eq_prime_pow S (rank3 rank) C e

/-- The criterion action is the literal SO/field semidirect action on Omega. -/
def matrixNaturalAction : TypeBCriterionHypotheses.NaturalAction (G n F)
    (fieldAction parameters rank N C S) where
  hom := TypeBCliffordOrthogonalAmbientActionBinding.omegaAmbientAction S (rank3 rank) C
  value := fun _ _ => rfl

/-- Its SO factor is exactly conjugation on the original subgroup. -/
theorem matrixNaturalAction_inl (h : H n F) :
    (matrixNaturalAction parameters rank N C S).hom (SemidirectProduct.inl h) =
      TypeBCentralKernelCarriers.originalAction (G n F) h := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change h * fieldAction parameters rank N C S 1 x.val * h⁻¹ = h * x.val * h⁻¹
  rw [map_one]
  rfl

/-- The inverse/opposite convention agrees with the existing SO inertia action. -/
theorem matrixNaturalAction_on_SO :
    (CyclicOuterLemma37Concrete.inverseOpHom
      (matrixNaturalAction parameters rank N C S).hom).comp SemidirectProduct.inl =
      TypeBCentralKernelInertia.conjugationOp (G n F) := by
  apply MonoidHom.ext
  intro h
  change MulOpposite.op
      ((matrixNaturalAction parameters rank N C S).hom
        ((SemidirectProduct.inl h)⁻¹)) =
    MulOpposite.op (TypeBCentralKernelCarriers.originalAction (G n F) h⁻¹)
  rw [← map_inv]
  exact congrArg MulOpposite.op
    (matrixNaturalAction_inl parameters rank N C S h⁻¹)

section RootsAndCharacters

variable {K O k : Type} [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]

/-- The actual character-central kernel is trivial for every character. -/
theorem centralFaithful (simple : IsSimpleGroup (X n F))
    (nonabelian : ¬ IsMulCommutative (X n F))
    (rootX : PrimeRegularRootEmbedding 2 k K (X n F)) (phi : IBr rootX) :
    TypeBBSCentralCharacterQuotient.centralKernel rootX phi = ⊥ :=
  TypeBBSCentralCharacterQuotient.centralKernel_eq_bot rootX phi
    (centerless simple nonabelian)

include parameters rank N C in
/-- The same modular-system residue calibration joins prescribed SO/Omega roots. -/
theorem omega_so_root_lifts (Msys : ModularSystem 2 K O k)
    (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
    (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
    (compatibleX : RootResidueCompatible Msys rootX)
    (compatibleH : RootResidueCompatible Msys rootH) :
    rootX.lift = rootH.lift :=
  TypeBPrincipalRootLiftBinding.omega_so_lifts_of_residue Msys
    (omega_index_two parameters rank N C) rootX rootH compatibleX compatibleH

variable [Finite (Spin n F N)]

/-- Calibrated transport only: the application supplies Spin fixation by
invoking the accepted all-rank selector on these very Spin data. No old
quotient root, whole lift equality or field-fixedness source is introduced. -/
theorem matrix_field_fixed_of_spin_fixed
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
    (Msys : ModularSystem 2 K O k)
    (rootSpin : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
    (compatibleSpin : RootResidueCompatible Msys rootSpin)
    (compatibleX : RootResidueCompatible Msys rootX)
    (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
    (regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{0} 2)
    (centralBlocks : NavarroCentralBlockPrinciple 2 k)
    [Fintype (LiteralPrimitiveBlock k (X n F))]
    (matrixBlocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (X n F) => b.val))
    (spinBlock : LiteralPrimitiveBlock k (Spin n F N)) (spinPrincipal : IsPrincipal spinBlock)
    (matrixBlock : LiteralPrimitiveBlock k (X n F)) (matrixPrincipal : IsPrincipal matrixBlock)
    (spinFixed : ∀ (e : FieldGroup f) (theta : IBr rootSpin),
      Supported rootSpin spinBlock theta →
        IrreducibleBrauerCharacter.twist rootSpin theta (spinFieldAction n F S e) = theta) :
    ∀ (e : FieldGroup f) (phi : IBr rootX),
      Supported rootX matrixBlock phi →
        IrreducibleBrauerCharacter.twist rootX phi (omegaAction parameters rank N C S e) = phi := by
  let oldRoot := groupRoot Msys (TypeBSpinCoverSource.Omega N)
  have oldCompatible : RootResidueCompatible Msys oldRoot :=
    groupRoot_residue Msys (TypeBSpinCoverSource.Omega N)
  have spinLifts : rootSpin.lift = oldRoot.lift :=
    TypeBPrincipalRootLiftBinding.spinLifts_of_residue
      parameters (rank3 rank) centre Msys rootSpin oldRoot compatibleSpin oldCompatible
  have matrixLifts : rootX.lift = oldRoot.lift :=
    TypeBPrincipalRootLiftBinding.matrixLifts_of_residue
      parameters (rank3 rank) centre C Msys rootX oldRoot compatibleX oldCompatible
  exact TypeBPrincipalSpinMatrixFieldTransport.matrix_fixed_of_spin_fixed
    parameters (rank3 rank) C centre oldRoot rootX matrixLifts
    kernel regular centralBlocks S matrixBlocks rootSpin spinLifts
    spinBlock spinPrincipal matrixBlock matrixPrincipal spinFixed

end RootsAndCharacters

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
