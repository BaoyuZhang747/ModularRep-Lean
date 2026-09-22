import ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorApplication
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionBrauerTransport
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionAssembly
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSpathSource
import ModularRep.PaperProofs.TypeBRankThreePrincipalBSOnePairApplication

/-!
# The all-rank principal criterion from the original GGGR inputs

The actual matrix Omega principal block is reached by invoking the accepted
Spin selector internally on its original raw GGGR, geometric and rational
inputs. The same accepted rational-class/Brauer count is reused; only the
independent rational Spin class formula U+D is new. All upper matching,
field/linear covariance, matched inertias, selectors and structural fields
are constructed before applying the one-block BS source.

This file retains the same modular system and prescribed principal roots,
specified block operations, norm, projection and field actor. No completed
field fixation, upper/downstairs matching or criterion is an external input.
The remaining published/source and specified interpretations are conditional
E1/E2/U inputs, not inhabitants authenticated by this code alone.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionApplication

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
open scoped MonoidAlgebra Pointwise

attribute [local instance]
  TypeBAllRankPrincipalCriterionUpperCorrespondence.physicalSubgroupFintype

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} (finiteClifford : FiniteCliffordSource n F)

variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]

/-- The same normalized output is constructed from the original raw GGGR telescope. -/
theorem exists_normalized_from_GGGR :
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
    Nonempty (NormalizedBlockWitness Msys rootX SX bX) := by
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
  letI := SX.operations.ambientBlockData.fintypeBlock
  let matrixBlocks := TypeBRankThreePrincipalFieldNaturality.physicalDecomposition
    SX physicalX.literal
  have spinFixed : ∀ (e : FieldGroup f) (phi : IBr iota), Supported iota b phi →
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F S e) = phi :=
    TypeBAllRankPrincipalSelectorApplication.principalBrauer_fixed
      (N := N) finiteClifford orthogonality (parameters := parameters) (rank := rank) S
      (geometricClass := geometricClass) (upperGeometricClass := upperGeometricClass)
      (geometric_square := geometric_square) (ComponentGroup := ComponentGroup)
      geometricStable inner rational (upperDual := upperDual) (lowerDual := lowerDual)
      (rationalSeries := rationalSeries) (quasiIsolated := quasiIsolated)
      (unipotentSupport := unipotentSupport) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (b := b) (principal := principal) (blocks := blocks)
      (ordinary := ordinary) columns series classIndex ordering waveFront count
      induction expansion reciprocity sources
  have omegaFixed : ∀ (e : FieldGroup f) (phi : BrauerFibre rootX bX),
      IrreducibleBrauerCharacter.twist rootX phi.val
        (omegaAction parameters rank N C S e) = phi.val := by
    intro e phi
    exact TypeBAllRankPrincipalCriterionBrauerTransport.omega_field_fixed_of_spin_fixed
      parameters rank N C centreSpin Msys iota rootX compatibleSpin compatibleX
      kernel regular centralBlocks matrixBlocks b principal bX principalX S spinFixed
      e phi.val phi.property
  have omegaCount : Nat.card (BrauerFibre rootX bX) =
      TypeBAllRankPrincipalCriterionUpperCorrespondence.U n +
        TypeBAllRankPrincipalCriterionUpperCorrespondence.D n :=
    TypeBAllRankPrincipalCriterionBrauerTransport.omega_principal_card
      parameters rank N C centreSpin Msys iota rootX compatibleSpin compatibleX
      kernel regular centralBlocks matrixBlocks b principal bX principalX count rationalClassCard
  exact TypeBAllRankPrincipalCriterionAssembly.exists_normalizedBlockWitness
    parameters rank N C S centreSpin fullCover centreClifford naturalKernel naturalSurjective
    simple nonabelian Msys rootX rootH compatibleX compatibleH coefficient SX SH
    bX principalX bH principalH physicalX physicalH green principalLift clifford
    principalRestriction dgn covering soBrauerCount soWeightCount weightDoubleCount
    weightField brauerCyclic ordinaryCyclic bs omegaCount omegaFixed

/-- The actual manuscript conclusion at n >= 4: one principal-block matching
satisfies all independent fixed-block clauses and the precise forward Spath
witness on every SAME raw match. The full Spin cover, ordinary normalizer
quotient and character-central quotient are those computed by SpathSource.
Only the remaining specified block/stabilizer interpretation is supplied. -/
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
    ∃ omega : BrauerFibre rootX bX ≃ CoverWeight SX bX,
      TypeBQ3AssemblyCriterionData.CompleteClauses rootX SX bX omega ∧
      ∀ (phi : BrauerFibre rootX bX) (W : CharacterWeight 2 K (X n F)),
        TypeBWeightCoveringSource.rawClass W = (omega phi).val →
        ∃ supported : SX.operations.induceToAmbient W = bX,
          ∃ hUT : weightInertia W ≤ characterInertia rootX phi.val,
            Nonempty (CanonicalPairWitness Msys rootX compatibleX phi.val W
              hUT navarro (pairBlocks phi W supported)) := by
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
  obtain ⟨D⟩ := exists_normalized_from_GGGR
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
  refine ⟨D.omega, TypeBAllRankPrincipalCriterionFixedBlockSource.completeClauses D, ?_⟩
  intro phi W same
  have supported : SX.operations.induceToAmbient W = bX := by
    change SX.weightBlock (TypeBWeightCoveringSource.rawClass W) = bX
    rw [same]
    exact (D.omega phi).property
  let sourceBlocks := TypeBRankThreePrincipalBSOnePairApplication.ambientPhysicalBlocks
    SX physicalX.literal
  refine ⟨supported, same_match_hUT Msys rootX D sourceBlocks principalX phi W same, ?_⟩
  exact actual_pairWitness_of_normalized_match
    parameters rank N C centreSpin Msys fullCover simple nonabelian rootX compatibleX
    navarro spath coefficient D kernel sourceBlocks principalX phi W same
    (pairBlocks phi W supported) (pairJoins phi W supported)

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
