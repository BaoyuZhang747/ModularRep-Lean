import ModularRep.PaperProofs.TypeBSpinBroueMichelCarriers
import ModularRep.PaperProofs.TypeBBroueMichelBlockIndex

/-!
# Bind Spin's integral-series packet through the full specified block union

The block assignment is constructed from the literal PCSp Broue--Michel
union and the same specified ordinary selector. The individual source map
lands in Brauer characters occurring in reductions of that FULL ordinary
union. Reindexing to the constructed block fibre preserves every actual
Brauer character and the exact stable-reduction equation.

The family remains the prescribed external full rational Lusztig family.
Its authentic source meaning and finite-point/coefficient interpretation
must be matched separately. The ordinary partition and Broue--Michel
block-closure statements concern only ordinary series; no basic set or
blockwise bijection is smuggled into their certificate.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinBroueMichelSourceBinding

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open DecompositionBasicSetBridge
open ExactGrothendieckGroup TypeBCliffordCarriers TypeBRationalSeriesSource
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinBroueMichelCarriers
open TypeBBroueMichelBlockIndex TypeBOrdinaryBlockSplitting
open TypeBIntegralSeriesSplitting TypeBOrdinaryLabelSplitting

variable {n p ell : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p] [Field K] [CommRing O] [IsDomain O]
  [Field k] [Algebra O K] [CharZero K] [CharP k ell] [IsAlgClosed k]
  {N : NormSource n F} [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))
  (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
  (Msys : ModularSystem ell K O k)
  (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  [Fintype (SpinBlock (k := k) (N := N))]
  (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
  (ordinary : OrdinaryBlockSource Msys iota hinj blocks)

/-- The literal ordinary partition and Broue--Michel block-closure boundary.
Coverage/disjointness use the rational-series partition and the commuting
ell/ell-prime decomposition; blockClosed is FLZ Section 2.4.2 p.537.
Every character is an actual ordinary Spin character and every block is
the fixed specified selector. No block index is a source field. -/
structure BlockUnionCertificate
    [finiteDefiningField : Finite F] [definingCharacteristic : CharP F p] : Prop where
  coverage : ∀ chi, ∃ s, indexedOrdinaryUnion S hp he hne s chi
  disjoint : ∀ s t chi, indexedOrdinaryUnion S hp he hne s chi →
    indexedOrdinaryUnion S hp he hne t chi → s = t
  blockClosed : ∀ s chi psi,
    ordinary.physical.ordinaryBlock chi = ordinary.physical.ordinaryBlock psi →
      indexedOrdinaryUnion S hp he hne s chi → indexedOrdinaryUnion S hp he hne s psi

variable (C : BlockUnionCertificate S hp he hne Msys iota hinj blocks ordinary)

/-- Both old source fields are derived from the SAME full rational family
and its full specified Broue--Michel union. -/
def rationalSource : SpinRationalSeriesSource (p := p) (ell := ell)
    (K := K) (k := k) (N := N) where
  family := selectedFamily S
  blockSeries := physicalBlockIndex Msys iota hinj blocks ordinary
    (indexedOrdinaryUnion S hp he hne) C.coverage C.blockClosed

@[simp] theorem rationalSource_family :
    (rationalSource S hp he hne Msys iota hinj blocks ordinary C).family =
      selectedFamily S := rfl

theorem ordinaryUnion_iff_blockSeries (s : RationalIndex p ell n F)
    (chi : Irr K (Spin n F N)) :
    indexedOrdinaryUnion S hp he hne s chi ↔
      (rationalSource S hp he hne Msys iota hinj blocks ordinary C).blockSeries
        (ordinary.physical.ordinaryBlock chi) = s :=
  ordinaryUnion_iff_index Msys iota hinj blocks ordinary
    (indexedOrdinaryUnion S hp he hne) C.coverage C.blockClosed C.disjoint s chi

variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

/-- The literal individual FLZ integral conclusion, before replacing the
specified Brauer union with any index fibre. Its generator equation is the
actual stable decomposition of the fixed ordinary simple representation. -/
structure LiteralIntegralSeriesData where
  perSeries : ∀ s : RationalIndex p ell n F,
    MonoidAlgebra ℤ {chi : Irr K (Spin n F N) //
      chi ∈ (selectedFamily S).rationalSeries s} ≃ₗ[ℤ]
        MonoidAlgebra ℤ (BrauerUnion Msys iota (indexedOrdinaryUnion S hp he hne) s)
  sourceGenerator : ∀ (s : RationalIndex p ell n F)
    (chi : {chi : Irr K (Spin n F N) // chi ∈ (selectedFamily S).rationalSeries s}),
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
      (brauerUnionInclusion Msys iota (indexedOrdinaryUnion S hp he hne) s
        (perSeries s (MonoidAlgebra.single chi 1))) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (ordinaryLabel chi.val))

/-- Exact one-way Theorem2.3 on individual literal unions, with ordinary
splitting and the algebraic-centre numerical guard kept explicit.
The source meaning of S and the centre coinvariant order two remain part
of the source application, not consequences of the finite diagonal map. -/
structure LiteralTheorem23Certificate
    [finiteDefiningField : Finite F]
    [definingCharacteristic : CharP F p]
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] where
  applies : Theorem23Hypotheses p ell 2 →
    Nonempty (LiteralIntegralSeriesData S hp he hne Msys iota hinj hcompat)

variable (existsAbove : ∀ phi : IBr iota, ∃ chi : Irr K (Spin n F N),
  decompositionNumber Msys iota chi phi ≠ 0)

/-- The old per-series packet is constructed by the value-preserving
Brauer-union reindexing; no source generator equation changes. -/
def integralSeriesData
    (T : LiteralIntegralSeriesData S hp he hne Msys iota hinj hcompat) :
    IntegralSeriesData Msys iota hcompat hinj
      (rationalSource S hp he hne Msys iota hinj blocks ordinary C).family blocks
      (rationalSource S hp he hne Msys iota hinj blocks ordinary C).blockSeries where
  perSeries s := (T.perSeries s).trans (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
    (brauerUnionEquivFibre Msys iota hinj blocks ordinary
      (indexedOrdinaryUnion S hp he hne) C.coverage C.blockClosed C.disjoint existsAbove s))
  sourceGenerator s chi := by
    change labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
      (TypeBRationalSeriesBasicSet.seriesInclusion
        (brauerIndex iota hinj blocks
          (physicalBlockIndex Msys iota hinj blocks ordinary
            (indexedOrdinaryUnion S hp he hne) C.coverage C.blockClosed)) s
        (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
          (brauerUnionEquivFibre Msys iota hinj blocks ordinary
            (indexedOrdinaryUnion S hp he hne) C.coverage C.blockClosed C.disjoint
              existsAbove s) (T.perSeries s (MonoidAlgebra.single chi 1)))) = _
    exact (congrArg (labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm)
      (brauerUnionInclusion_reindex Msys iota hinj blocks ordinary
        (indexedOrdinaryUnion S hp he hne) C.coverage C.blockClosed C.disjoint
        existsAbove s (T.perSeries s (MonoidAlgebra.single chi 1)))).trans
          (T.sourceGenerator s chi)

/-- The old certificate now follows from the literal per-union theorem,
using the SAME block construction for every value of its hypothesis. -/
def theorem23Certificate
    (T : LiteralTheorem23Certificate S hp he hne Msys iota hinj hcompat) :
    Theorem23Certificate Msys iota hcompat hinj
      (rationalSource S hp he hne Msys iota hinj blocks ordinary C).family blocks
      (rationalSource S hp he hne Msys iota hinj blocks ordinary C).blockSeries p 2 where
  applies h := by
    obtain ⟨data⟩ := T.applies h
    exact ⟨integralSeriesData S hp he hne Msys iota hinj blocks ordinary C hcompat
      existsAbove data⟩

end ModularRep.PaperProofs.TypeBSpinBroueMichelSourceBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
