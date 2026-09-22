import ModularRep.PaperProofs.TypeBLeviReturnPowerSelection
import ModularRep.PaperProofs.TypeBSpinPrincipalGGGRFieldApplication
import ModularRep.PaperProofs.TypeBAllRankPrincipalSelectorApplication

/-!
# Principal Spin selectors on the full actual field image

Each endpoint calls the original specified GGGR-to-Brauer-fixation theorem
with its complete source telescope and the same supported principal base.
The standard actor is the full image of the literal finite field action.
No fixedness theorem or completed selector is supplied as an input.

These are subordinate specified source applications. The original component's
principal support and its classical model/positive-return square are separate
joins. Their conditional scope is not discharged by the wrappers below.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBLeviReturnPrincipalSelectorBinding

open ModularRep TypeBCliffordCarriers TypeBLeviReturnPowerSelection

/-- The complete actual field-action image on the same norm-one Spin carrier. -/
abbrev standardFieldImage {n p f : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F p]
    {parameters : OddFieldParameters F p f} {N : NormSource n F}
    (fs : FieldActionSource n F p f parameters N) : Subgroup (MulAut (Spin n F N)) :=
  (spinFieldAction n F fs).range

section RankThree

open OrdinaryIrreducibleCharacter TypeBCentralKernelBlockSource
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBSpinPrincipalGGGRBasisBinding TypeBSpinPrincipalDecompositionBinding
open TypeBSpinPrincipalProjectiveBinding TypeBSpinGGGRProjectivityBinding
open TypeBPrincipalSelectorCorollary413SourceInstantiation
open TypeBGGGRRankProposition412Corollary413Bridge TypeBIndexedRationalFieldHandoff
open scoped MonoidAlgebra

variable {r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource 3 F} [Finite (Spin 3 F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F r f)
  (S : FieldActionSource 3 F r f parameters N)
  {GeometricClass : Type}
  (geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass)
  (geometricStable : GeometricFieldStable parameters S geometricClass)
  (ComponentGroup : GeometricClass → Type) [∀ C, Group (ComponentGroup C)]
  (inner : ∀ C, ComponentGroup C)
  (gamma : UnipotentClass (r := r) (N := N) → Spin 3 F N → K)
  (rational : RationalGGGRSource (K := K) parameters (show 3 ≤ 3 from le_rfl) S
    geometricClass geometricStable ComponentGroup inner)
  (gamma_eq : rational.gamma = gamma)
  (rationalSeries : TypeBConformalDualCarriers.PCSp F 3 → Irr K (Spin 3 F N) → Prop)
  (quasiIsolated : TypeBConformalDualCarriers.PCSp F 3 → Prop)
  (normalizedDual : Irr K (Spin 3 F N) → Irr K (Spin 3 F N))
  (unipotentSupport : Irr K (Spin 3 F N) → GeometricClass → Prop)
  (raw : RankThreeChanebSource parameters geometricClass ComponentGroup gamma
    rationalSeries quasiIsolated normalizedDual unipotentSupport)
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
  (b : LiteralPrimitiveBlock k (Spin 3 F N)) (principal : IsPrincipal b)
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  (ordinary : OrdinaryBlockSource Msys iota blocks)
  (columns : DecompositionColumnIndependenceSource Msys iota)
  (series : PrincipalSeriesCertificate parameters (show 3 ≤ 3 from le_rfl)
    ordinary.ordinaryBlock b principal rationalSeries quasiIsolated normalizedDual)
  {m : ℕ} (classIndex : Fin m ≃ UnipotentClass (r := r) (N := N))
  (closure : GeometricClass → GeometricClass → Prop)
  (ordering : GeometricOrdering geometricClass classIndex closure)
  (waveFront : WaveFrontClosureCertificate parameters geometricClass gamma
    normalizedDual unipotentSupport closure)
  (count : PrincipalRationalClassCount parameters iota b principal)
  (induction : GGGRInductionSource parameters (show 3 ≤ 3 from le_rfl) gamma)
  (expansion : letI : Finite (Irr K (Spin 3 F N)) := ordinary_finite orthogonality
    OddInductionExpansionCertificate Msys iota hcompat)

include raw orthogonality hcompat principal ordinary columns series ordering
  waveFront count induction expansion rational gamma_eq in
/-- The actual rank-three principal source yields a selector at this same
supported character, for the full field image and any displayed diagonal. -/
theorem principal_selectorAt_rankThree {Q : Type} [Group Q]
    (diagonal : Q →* MulAut (Spin 3 F N))
    (psi : IBr iota) (supported : Supported iota b psi) :
    StandardSelectorAt iota diagonal (standardFieldImage S) psi := by
  apply standardSelectorAt_of_fixed
  intro p
  obtain ⟨a, ha⟩ := p.property
  have hfixed := TypeBSpinPrincipalGGGRFieldApplication.principalBrauer_fixed
    (N := N) (parameters := parameters) (geometricClass := geometricClass)
    (ComponentGroup := ComponentGroup) (gamma := gamma) (rationalSeries := rationalSeries)
    (quasiIsolated := quasiIsolated) (normalizedDual := normalizedDual)
    (unipotentSupport := unipotentSupport) (raw := raw)
    (orthogonality := orthogonality) (Msys := Msys) (iota := iota) (hcompat := hcompat)
    (b := b) (principal := principal) (blocks := blocks) (ordinary := ordinary)
    (columns := columns) (series := series) (classIndex := classIndex)
    (closure := closure) (ordering := ordering) (waveFront := waveFront) (count := count)
    (induction := induction) (expansion := expansion)
    (S := S) (geometricStable := geometricStable) (inner := inner)
    (rational := rational) (gamma_eq := gamma_eq) a psi supported
  simpa only [ha] using hfixed

end RankThree

section RankAtLeastFour

open OrdinaryIrreducibleCharacter TypeBCentralKernelBlockSource
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRPrincipalSeriesBinding
open TypeBSpinGGGRProjectivityBinding TypeBSpinGGGRRationalSpanBinding
open TypeBAllRankGGGRFibres TypeBAllRankGGGREntries TypeBAllRankGGGR.BasisPhysical
open scoped MonoidAlgebra Pointwise

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} (finiteClifford : FiniteCliffordSource n F)

variable [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]

/-- The rank-at-least-four specified source gives the same fixed-base selector.
The ordinary roots on the upper Clifford group and all original local sources
are retained; the Spin finite/root instances are derived as in the provider. -/
theorem principal_selectorAt_rankAtLeastFour :
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
    ∀ {Q : Type} [Group Q] (diagonal : Q →* MulAut (Spin n F N))
      (psi : IBr iota), Supported iota b psi →
      StandardSelectorAt iota diagonal (standardFieldImage S) psi := by
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
    Q groupQ diagonal psi supported
  apply standardSelectorAt_of_fixed
  intro p
  obtain ⟨a, ha⟩ := p.property
  have hfixed := TypeBAllRankPrincipalSelectorApplication.principalBrauer_fixed
    (N := N) finiteClifford orthogonality
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
    a psi supported
  simpa only [ha] using hfixed

end RankAtLeastFour

end ModularRep.PaperProofs.TypeBLeviReturnPrincipalSelectorBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
