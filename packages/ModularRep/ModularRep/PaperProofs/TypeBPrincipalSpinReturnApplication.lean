import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionApplication
import ModularRep.PaperProofs.TypeBPrincipalSpinReturnCarriers
import ModularRep.PaperProofs.TypeBPrincipalSpinReturnFibres
import ModularRep.PaperProofs.TypeBPrincipalSpinReturnPairs

/-!
# The actual principal Spin return from the same matrix-Omega deduction

The accepted Omega manuscript theorem is invoked once on its original
explicit inputs. Central Brauer inflation and specified weight descent then
construct one principal Spin correspondence. Its full automorphism action
and every raw pair witness belong to that same correspondence.

The additional local facts concern only ordinary catalogue membership and
decomposition at the required actual normalizers. The known matrix-principal
branch reuses the predecessor's calibration. Finite ordinary roots and the
same modular system are retained. Published one-way Butterfly and MRR 3.14
inputs remain conditional; no matching, block-transport or pair witness is
a new external premise.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBPrincipalSpinReturnApplication

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinGGGRRationalSpanBinding TypeBAllRankGGGRFibres
open TypeBAllRankGGGREntries TypeBAllRankGGGR.BasisPhysical
open TypeBAllRankPrincipalCriterionCarriers TypeBCentralKernelInertia
open TypeBLocalReductionInstantiation TypeBCriterionHypotheses
open TypeBAllRankPrincipalCriterionFixedBlockSource
open TypeBQ3PrincipalWeightInflation
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension
open EvenFieldFLZSourceConditions
open TypeBAllRankPrincipalCriterionSpathSource
open TypeBPrincipalSpinReturnFibres
open scoped MonoidAlgebra Pointwise

attribute [local instance]
  TypeBAllRankPrincipalCriterionUpperCorrespondence.physicalSubgroupFintype

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} (finiteClifford : FiniteCliffordSource n F)

variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]

/-- The principal central-two return used in the current localized-return proof, at rank at least four. -/
theorem manuscript_deduction :
    letI : Finite (SpecialClifford n F) := specialClifford_finite n F finiteClifford
    letI : Finite (Spin n F N) := TypeBAllRankGGGRCarriers.spin_finite N finiteClifford
    letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
      TypeBAllRankGGGRCarriers.spin_roots_of_upper N
    ∀ (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)),
    letI : Finite (Irr K (Spin n F N)) := ordinary_finite orthogonality
    ∀ {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
      (S : FieldActionSource n F r f parameters N)
      {GeometricClass : Type}
      {geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass}
      {upperGeometricClass : UpperUnipotentClass (n := n) (F := F) (r := r) → GeometricClass}
      {geometric_square : ∀ c, upperGeometricClass (upperClassMap c) = geometricClass c}
      {ComponentGroup : GeometricClass → Type} [∀ C, Group (ComponentGroup C)]
      (geometricStable : GeometricFieldStable parameters S geometricClass)
      (inner : ∀ C, ComponentGroup C)
      (rational : RationalGGGRSource (K := K) parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank) S
        geometricClass geometricStable ComponentGroup inner)
      {upperDual : Irr K (SpecialClifford n F) → Irr K (SpecialClifford n F)}
      {lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)}
      {rationalSeries : TypeBConformalDualCarriers.PCSp F n → Irr K (Spin n F N) → Prop}
      {quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop}
      {unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop}
      {Msys : ModularSystem 2 K O k}
      {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
      {hcompat : StableReductionBrauerCharacterCompatibility Msys iota}
      {b : LiteralPrimitiveBlock k (Spin n F N)} {principal : IsPrincipal b}
      [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
      {blocks : BlockIdempotentDecomposition
        (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val)}
      {ordinary : OrdinaryBlockSource Msys iota blocks}
      (columns : DecompositionColumnIndependenceSource Msys iota)
      (series : PrincipalSeriesCertificate parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank)
        ordinary.ordinaryBlock b principal rationalSeries quasiIsolated lowerDual)
      {m : ℕ} (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
      {closure : GeometricClass → GeometricClass → Prop}
      (ordering : GeometricOrdering geometricClass classIndex closure)
      (waveFront : WaveFrontClosureCertificate parameters rank geometricClass rational.gamma
        lowerDual unipotentSupport closure)
      (count : PrincipalRationalClassCount parameters rank iota b principal)
      (induction : GGGRInductionSource parameters
        (Nat.le_trans (show 3 ≤ 4 by decide) rank) rational.gamma)
      (expansion : OddInductionExpansionCertificate Msys iota hcompat)
      (reciprocity : FrobeniusReciprocitySource (N := N) (K := K))
      (sources : ∀ C, Nonempty (RationalFibre geometricClass C) →
        TypeBAllRankGGGRSelection.LocalSources (geometricClass := geometricClass)
          (upperGeometricClass := upperGeometricClass) (geometric_square := geometric_square)
          (ComponentGroup := ComponentGroup) (gamma := rational.gamma) (upperDual := upperDual)
          (lowerDual := lowerDual) (rationalSeries := rationalSeries)
          (quasiIsolated := quasiIsolated) (unipotentSupport := unipotentSupport)
          (parameters := parameters) (rank := rank) C),
    letI : Finite (FieldGroup f) :=
      TypeBAllRankPrincipalCriterionMatrixStructure.fieldGroupFinite parameters
    ∀ (C : TypeBCliffordOrthogonalSourceBinding.Source
        n F r f parameters (rank3 rank) N)
      (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n r f F N)
      (fullCover : EvenFieldFLZ318FixedTheoremGate.IsUniversalCentralExtension
        (spinProjection parameters rank N C))
      (centreClifford : TypeBCliffordCentreSource.CentreSource n F parameters
        ((by decide : 1 ≤ 3).trans (rank3 rank)))
      (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism S).ker =
        TypeBAutomorphismSource.embeddedCenter S)
      (naturalSurjective : Function.Surjective (TypeBAutomorphismSource.ambientAutomorphism S))
      (simple : IsSimpleGroup (X n F)) (nonabelian : ¬ IsMulCommutative (X n F))
      [HasEnoughRootsOfUnity K
        (Nat.card (Ambient (fieldAction parameters rank N C S)))],
    letI : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
      TypeBAllRankPrincipalCriterionMatrixStructure.ordinaryRoots_of_ambientRoots
        parameters rank N C S
    letI : HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
      HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G n F))
    ∀ (rootX : PrimeRegularRootEmbedding 2 k K (X n F))
      (rootH : PrimeRegularRootEmbedding 2 k K (H n F))
      (compatibleSpin : RootResidueCompatible Msys iota)
      (compatibleX : RootResidueCompatible Msys rootX)
      (compatibleH : RootResidueCompatible Msys rootH)
      (coefficient : SpathCoefficientField 2 k Msys.prime)
      (SX : CoverWeightSource (k := k) (K := K) (X n F))
      (SH : CoverWeightSource (k := k) (K := K) (H n F))
      (bX : LiteralPrimitiveBlock k (X n F)) (principalX : IsPrincipal bX)
      (bH : LiteralPrimitiveBlock k (H n F)) (principalH : IsPrincipal bH)
      (physicalX : PhysicalWeightCalibration Msys rootX SX bX)
      (physicalH : PhysicalWeightCalibration Msys rootH SH bH),
    let roots := TypeBAllRankPrincipalCriterionMatrixStructure.roots_agree
      parameters rank N C Msys rootX rootH compatibleX compatibleH
    let idx := omega_index_two parameters rank N C
    ∀ (green : Green811Source (G n F) rootH rootX roots coefficient
        (quotient_isTwoGroup (G n F) idx))
      (principalLift : PrincipalLiftSource (G n F) rootH rootX roots coefficient
        (quotient_isTwoGroup (G n F) idx))
      (clifford : Clifford85_87Source (G n F) rootH rootX roots coefficient)
      (principalRestriction : PrincipalRestrictionSource (G n F) rootH rootX roots coefficient)
      (dgn : TypeBWeightCoveringSplittingSource.DGNSource (G n F) Msys)
      (covering : TypeBAllRankPrincipalCriterionUpperCorrespondence.PublishedPrincipalCovering
        (G n F) SX bX SH bH Msys dgn)
      (soBrauerCount : Nat.card (BrauerFibre rootH bH) =
        TypeBAllRankPrincipalCriterionUpperCorrespondence.U n)
      (soWeightCount : Nat.card (SH.Fibre bH) =
        TypeBAllRankPrincipalCriterionUpperCorrespondence.U n)
      (weightDoubleCount : Nat.card {v : SH.Fibre bH //
        Nat.card {w : SX.Fibre bX // TypeBWeightCoveringSplittingSource.CoversClass
          (G n F) dgn v.val w.val} = 2} =
        TypeBAllRankPrincipalCriterionUpperCorrespondence.D n)
      (rationalClassCard : Nat.card (UnipotentClass (r := r) (N := N)) =
        TypeBAllRankPrincipalCriterionUpperCorrespondence.U n +
          TypeBAllRankPrincipalCriterionUpperCorrespondence.D n)
      (weightField : TypeBAllRankPrincipalCriterionWeightFieldSource.FYZCorollary363Source
        F parameters rank N C S Msys coefficient rootX rootH compatibleX compatibleH
        SX SH bX principalX bH principalH physicalX physicalH)
      (kernel : TypeBCentralKernelBrauerInflation.Navarro232Principle 2 k)
      (regular : TypeBCentralKernelBrauerInflation.PrimeRegularQuotientLiftPrinciple.{0} 2)
      (centralBlocks : NavarroCentralBlockPrinciple 2 k)
      (brauerCyclic : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
      (ordinaryCyclic : ∀ (Y : Type) [Group Y] [Finite Y]
        [HasEnoughRootsOfUnity K (Nat.card Y)],
          TypeBLocalOrdinaryExtensionSplitting.ScopedCyclicExtensionSource K Y)
      (bs : Theorem45FixedBlockCertificate),
    ∀ (navarro : ∀ (Y : Type) [Group Y] [Finite Y]
        [HasEnoughRootsOfUnity K (Nat.card Y)]
        (root : PrimeRegularRootEmbedding 2 k K Y)
        (compatible : RootResidueCompatible Msys root),
          ScopedDefectZeroReductionSource Msys root compatible)
      (spath : ForwardTheorem44 k K)
      (pairBlocks : ∀ (phi : BrauerFibre rootX bX) (W : CharacterWeight 2 K (X n F)),
        SX.operations.induceToAmbient W = bX → PairBlocks rootX phi.val W)
      (pairJoins : ∀ (phi : BrauerFibre rootX bX) (W : CharacterWeight 2 K (X n F)),
        SX.operations.induceToAmbient W = bX →
          ActualPairJoins parameters rank N C centreSpin Msys fullCover
            rootX compatibleX navarro phi.val W),
    ∀ (RSpin : CoverWeightSource (k := k) (K := K) (Spin n F N))
      (literalSpin : ∀ c, RSpin.operations.ambientBlockData.blockIdempotent c = c.val)
      (spinFacts : ∀ W : CharacterWeight 2 K (Spin n F N),
        principalEither
          (TypeBPrincipalSpinReturnCarriers.q parameters rank N C)
          (TypeBPrincipalSpinReturnCarriers.q_surjective parameters rank N C)
          (TypeBPrincipalSpinReturnCarriers.q_kernel_isTwoGroup parameters rank N C centreSpin)
          RSpin SX b bX W → NormalizerFacts Msys RSpin.operations W)
      (omegaFacts : ∀ W : CharacterWeight 2 K (Spin n F N),
        RSpin.operations.induceToAmbient W = b →
        NormalizerFacts Msys SX.operations
          (TypeBCentralKernelWeightTransport.descend
            (TypeBPrincipalSpinReturnCarriers.q parameters rank N C)
            (TypeBPrincipalSpinReturnCarriers.q_surjective parameters rank N C)
            (TypeBPrincipalSpinReturnCarriers.q_kernel_isTwoGroup parameters rank N C centreSpin) W))
      (butterfly : TypeBCentralKernelButterflyCertificate.ButterflyCertificate 2 k K)
      (mrr314 : TypeBCentralKernelTripleCertificate.Lemma314Certificate 2 k K)
      (pairBlocksSpin : ∀ (theta : BrauerFibre iota b) (W : CharacterWeight 2 K (Spin n F N)),
        RSpin.operations.induceToAmbient W = b → PairBlocks iota theta.val W),
    ∃ omegaSpin : BrauerFibre iota b ≃ CoverWeight RSpin b,
      (∀ (alpha : (MulAut (Spin n F N))ᵐᵒᵖ) (theta theta' : BrauerFibre iota b),
        theta'.val = alpha • theta.val →
          (omegaSpin theta').val = alpha • (omegaSpin theta).val) ∧
      ∀ (theta : BrauerFibre iota b) (W : CharacterWeight 2 K (Spin n F N)),
        TypeBWeightCoveringSource.rawClass W = (omegaSpin theta).val →
        ∃ supported : RSpin.operations.induceToAmbient W = b,
          ∃ hUT : weightInertia W ≤ characterInertia iota theta.val,
            Nonempty (CanonicalPairWitness Msys iota compatibleSpin theta.val W
              hUT navarro (pairBlocksSpin theta W supported)) := by
  classical
  letI : Finite (SpecialClifford n F) := specialClifford_finite n F finiteClifford
  letI : Finite (Spin n F N) := TypeBAllRankGGGRCarriers.spin_finite N finiteClifford
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    TypeBAllRankGGGRCarriers.spin_roots_of_upper N
  intro orthogonality
  letI : Finite (Irr K (Spin n F N)) := ordinary_finite orthogonality
  intro parameters rank S GeometricClass geometricClass upperGeometricClass geometric_square
    ComponentGroup componentInstances geometricStable inner rational
    upperDual lowerDual rationalSeries quasiIsolated unipotentSupport
    Msys iota hcompat b principal blockInstances blocks ordinary columns series
    m classIndex closure ordering waveFront count induction expansion reciprocity sources
  letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
  letI : Finite (FieldGroup f) :=
    TypeBAllRankPrincipalCriterionMatrixStructure.fieldGroupFinite parameters
  intro C centreSpin fullCover centreClifford naturalKernel naturalSurjective simple nonabelian
    ambientRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (H n F)) :=
    TypeBAllRankPrincipalCriterionMatrixStructure.ordinaryRoots_of_ambientRoots
      parameters rank N C S
  letI : HasEnoughRootsOfUnity K (Nat.card (X n F)) :=
    HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G n F))
  intro rootX rootH compatibleSpin compatibleX compatibleH coefficient SX SH
    bX principalX bH principalH physicalX physicalH
  intro roots idx
  intro green principalLift clifford principalRestriction dgn covering
    soBrauerCount soWeightCount weightDoubleCount rationalClassCard weightField
    kernel regular centralBlocks brauerCyclic ordinaryCyclic bs
  intro navarro spath pairBlocks pairJoins
  intro RSpin literalSpin spinFacts omegaFacts butterfly mrr314 pairBlocksSpin
  obtain ⟨omegaX, clausesX, pairsX⟩ :=
    TypeBAllRankPrincipalCriterionApplication.manuscript_deduction
    (N := N) finiteClifford orthogonality (parameters := parameters) (rank := rank) S
    (geometricClass := geometricClass) (upperGeometricClass := upperGeometricClass)
    (geometric_square := geometric_square) (ComponentGroup := ComponentGroup)
    geometricStable inner rational (upperDual := upperDual) (lowerDual := lowerDual)
    (rationalSeries := rationalSeries) (quasiIsolated := quasiIsolated)
    (unipotentSupport := unipotentSupport) (Msys := Msys) (iota := iota)
    (hcompat := hcompat) (b := b) (principal := principal) (blocks := blocks)
    (ordinary := ordinary) columns series classIndex ordering waveFront count
    induction expansion reciprocity sources
    C centreSpin fullCover centreClifford naturalKernel naturalSurjective simple nonabelian
    rootX rootH compatibleSpin compatibleX compatibleH coefficient SX SH
    bX principalX bH principalH physicalX physicalH
    green principalLift clifford principalRestriction dgn covering
    soBrauerCount soWeightCount weightDoubleCount rationalClassCard weightField
    kernel regular centralBlocks brauerCyclic ordinaryCyclic bs
    navarro spath pairBlocks pairJoins

  let q := TypeBPrincipalSpinReturnCarriers.q parameters rank N C
  have surjective : Function.Surjective q :=
    TypeBPrincipalSpinReturnCarriers.q_surjective parameters rank N C
  have kernelTwo : IsPGroup 2 q.ker :=
    TypeBPrincipalSpinReturnCarriers.q_kernel_isTwoGroup parameters rank N C centreSpin
  have central : q.ker ≤ Subgroup.center (Spin n F N) :=
    (TypeBPrincipalSpinReturnCarriers.q_ker parameters rank N C centreSpin).le
  let rho := TypeBPrincipalSpinReturnCarriers.rho parameters rank N C centreSpin fullCover
  have square : ∀ (alpha : MulAut (Spin n F N)) (x : Spin n F N),
      rho alpha (q x) = q (alpha x) :=
    TypeBPrincipalSpinReturnCarriers.rho_q parameters rank N C centreSpin fullCover
  let brauer := principalBrauerEquiv Msys q surjective kernelTwo central iota rootX
    compatibleSpin compatibleX RSpin SX b bX principal principalX literalSpin physicalX
    centralBlocks kernel regular
  let omegaSpin := liftedBijection Msys q surjective kernelTwo central iota rootX
    compatibleSpin compatibleX RSpin SX b bX principal principalX literalSpin physicalX
    centralBlocks spinFacts omegaFacts navarro kernel regular omegaX
  refine ⟨omegaSpin, ?_, ?_⟩
  · intro alpha theta theta' same
    exact liftedBijection_twist Msys q surjective kernelTwo central iota rootX
      compatibleSpin compatibleX RSpin SX b bX principal principalX literalSpin physicalX
      centralBlocks spinFacts omegaFacts navarro kernel regular omegaX
      alpha.unop (rho alpha.unop) (fun x => (square alpha.unop x).symm)
      (fun phi phi' h => clausesX.1 (MulOpposite.op (rho alpha.unop)) phi phi' h)
      theta theta' same
  · intro theta W same
    have support := (raw_match_supported Msys q surjective kernelTwo central iota rootX
      compatibleSpin compatibleX RSpin SX b bX principal principalX literalSpin physicalX
      centralBlocks spinFacts omegaFacts navarro kernel regular omegaX theta W same).1
    let thetaBar := brauer.symm theta
    let Wbar := TypeBCentralKernelWeightTransport.descend q surjective kernelTwo W
    have sameDown : TypeBWeightCoveringSource.rawClass Wbar = (omegaX thetaBar).val :=
      raw_match_descends Msys q surjective kernelTwo central iota rootX
        compatibleSpin compatibleX RSpin SX b bX principal principalX literalSpin physicalX
        centralBlocks spinFacts omegaFacts navarro kernel regular omegaX theta W same
    obtain ⟨supportedBar, hUTbar, ⟨witness⟩⟩ := pairsX thetaBar Wbar sameDown
    have values : theta.val.val = PrimeRegularClassFunction.pullback q thetaBar.val.val := by
      have value := principalBrauerEquiv_value Msys q surjective kernelTwo central iota rootX
        compatibleSpin compatibleX RSpin SX b bX principal principalX literalSpin physicalX
        centralBlocks kernel regular thetaBar
      exact (congrArg (fun psi : BrauerFibre iota b => psi.val.val)
        (brauer.apply_symm_apply theta)).symm.trans value
    have regularMap : Function.Surjective (PrimeRegularElement.map (p := 2) q) :=
      TypeBPrincipalSpinReturnFibres.regular_surjective q surjective kernelTwo regular
    have hUT := TypeBPrincipalSpinReturnPairs.pairInclusion q surjective kernelTwo
      rho square iota rootX theta.val thetaBar.val values regularMap W hUTbar
    refine ⟨support, hUT, ?_⟩
    exact TypeBPrincipalSpinReturnPairs.samePair_return q surjective kernelTwo
      rho square iota rootX theta.val thetaBar.val values regularMap W hUTbar Msys
      compatibleSpin compatibleX navarro (pairBlocksSpin theta W support)
      (pairBlocks thetaBar Wbar supportedBar) butterfly mrr314 witness

end ModularRep.PaperProofs.TypeBPrincipalSpinReturnApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
