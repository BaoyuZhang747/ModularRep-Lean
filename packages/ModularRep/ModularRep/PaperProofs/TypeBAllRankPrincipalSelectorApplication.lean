import ModularRep.PaperProofs.TypeBAllRankGGGRApplication
import ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorFieldNaturality
import ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorFixedProjective
import ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorSemidirect

/-!
# The actual all-rank principal-selector deduction

The accepted all-rank GGGR theorem is invoked on the same norm kernel,
modular system, principal block, projector and exhaustive class index.
Its rational basis is constructed inside this proof. The GGGR family is
literally rational.gamma, so there is no second family or equality input.
The published source and specified-realization conditions remain explicit.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorApplication

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinRationalUnipotentClassBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinGGGRRationalSpanBinding TypeBAllRankGGGRFibres
open TypeBAllRankGGGREntries TypeBAllRankGGGR.BasisPhysical
open scoped MonoidAlgebra Pointwise

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} (finiteClifford : FiniteCliffordSource n F)

variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]

/-- The first manuscript paragraph on the literal principal Brauer carrier.
The input telescope contains the original source facts, not a GGGR basis,
projective-space fixation or a selected Brauer character. -/
theorem principalBrauer_fixed :
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
    ∀ (e : FieldGroup f) (phi : IBr iota), Supported iota b phi →
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F S e) = phi := by
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
  obtain ⟨_, _, _, _, _, _, B, basis_apply⟩ :=
    TypeBAllRankGGGRApplication.manuscript_deduction
      (N := N) finiteClifford orthogonality
      (parameters := parameters) (rank := rank)
      (geometricClass := geometricClass) (upperGeometricClass := upperGeometricClass)
      (geometric_square := geometric_square) (ComponentGroup := ComponentGroup)
      (gamma := rational.gamma) (upperDual := upperDual) (lowerDual := lowerDual)
      (rationalSeries := rationalSeries) (quasiIsolated := quasiIsolated)
      (unipotentSupport := unipotentSupport)
      (Msys := Msys) (iota := iota) (hcompat := hcompat)
      (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
      columns series classIndex ordering waveFront count induction expansion reciprocity sources
  intro e phi supported
  exact TypeBAllRankPrincipalSelectorFixedProjective.principalBrauer_fixed_of_projectedGGGRBasis
    orthogonality hcompat columns blocks ordinary principal classIndex rational.gamma
    B basis_apply (spinFieldAction n F S e)
    (fun j => TypeBAllRankPrincipalSelectorFieldNaturality.indexed_projectedGGGR_fixed
      (rank := rank) rational Msys iota hcompat b principal blocks ordinary classIndex e j)
    phi supported

/-- The genuine two-paragraph manuscript deduction on the actual carriers:
every principal Brauer character is field fixed, its Clifford-by-field
stabilizer is its actual Clifford inertia times the full field factor,
and it has an extension to the whole Spin-by-field group. -/
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
    ∀ (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
      (phi : IBr iota), Supported iota b phi →
      (∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota phi
        (spinFieldAction n F S e) = phi) ∧
      (TypeBAllRankPrincipalSelectorSemidirect.cliffordStabilizer S iota phi :
        Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) =
        (((TypeBInertiaHallSource.brauerInertia N iota phi).map
          (SemidirectProduct.inl (φ := S.action))) :
            Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) *
        ((SemidirectProduct.inr (φ := S.action)).range :
          Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) ∧
      ∃ V : FDRep k (Spin n F N), Representation.IsIrreducible V.ρ ∧
        phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
        ∃ rho : Representation k (Spin n F N ⋊[spinFieldAction n F S] FieldGroup f) V.V,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (Representation.pullback rho
              (SemidirectProduct.inl (φ := spinFieldAction n F S))) V.ρ) := by
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
    principle phi supported
  have fixed : ∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota phi
      (spinFieldAction n F S e) = phi := by
    intro e
    exact principalBrauer_fixed (N := N) finiteClifford orthogonality
      (parameters := parameters) (rank := rank) S
      (geometricClass := geometricClass) (upperGeometricClass := upperGeometricClass)
      (geometric_square := geometric_square) (ComponentGroup := ComponentGroup)
      geometricStable inner rational
      (upperDual := upperDual) (lowerDual := lowerDual)
      (rationalSeries := rationalSeries) (quasiIsolated := quasiIsolated)
      (unipotentSupport := unipotentSupport)
      (Msys := Msys) (iota := iota) (hcompat := hcompat)
      (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
      columns series classIndex ordering waveFront count induction expansion reciprocity sources
      e phi supported
  refine ⟨fixed, ?_, ?_⟩
  · exact TypeBAllRankPrincipalSelectorSemidirect.cliffordStabilizer_eq_brauerInertia_product
      S iota phi (fun e => fixed e⁻¹)
  · letI : NeZero f := ⟨Nat.ne_of_gt parameters.exponent_pos⟩
    exact TypeBAllRankPrincipalSelectorSemidirect.extends_to_spinField
      S iota phi (fun e => fixed e⁻¹) principle

end ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
