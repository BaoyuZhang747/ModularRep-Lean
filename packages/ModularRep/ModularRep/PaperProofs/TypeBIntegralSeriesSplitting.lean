import ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting
import ModularRep.PaperProofs.TypeBIntegralSeriesCertificate
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Type B integral rational-series aggregation over a splitting fraction field

The rational-series family, actual ordinary characters, stable decomposition,
primitive modular blocks, and Brauer block partition are the same literal
carriers as in the earlier Type B source contract. The ordinary labels use
the checked characteristic-zero supplement and require no algebraic closure
of the fraction field of the modular system.

The only published basic-set certificate is one-way FLZ Theorem 2.3 on each
individual rational series, with its exact generator reduction equation.
The global integral basic set is constructed with the existing partition
equivalence. No global/blockwise basic set or set bijection is an input.

Actual algebraic finite-point, rational-series, centre-coinvariant, block,
and coefficient/root source identifications remain explicit obligations.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBIntegralSeriesSplitting

open ModularRep OrdinaryIrreducibleCharacter
open DecompositionBasicSetBridge ExactGrothendieckGroup FDRepSimpleClassKZero
open TypeBRationalSeriesBasicSet TypeBRationalSeriesSource
open TypeBOrdinaryLabelSplitting OddConformalProposition311Relative
open scoped MonoidAlgebra

universe u

/-- Reuse the exact odd, nondefining, prime-to-centre-coinvariant hypotheses
from the frozen FLZ Theorem 2.3 contract. -/
abbrev Theorem23Hypotheses := TypeBIntegralSeriesCertificate.Theorem23Hypotheses

section Aggregation

variable {ell : ℕ} {K O k G I : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Group G] [Finite G] [Fintype I]

/-- The per-series generator equations imply the exact global stable
decomposition equation on the same ordinary labels. The free integral-module
partition and its summand formula are reused unchanged. -/
theorem aggregate_restricts_decomposition
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (series : Irr K G → Prop)
    (ordinaryIndex : OrdinarySeriesCarrier series → I)
    (brauerIndex : IBr iota → I)
    (perSeries : ∀ s : I,
      MonoidAlgebra ℤ (SeriesFibre ordinaryIndex s) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s))
    (sourceGenerator : ∀ (s : I) (x : SeriesFibre ordinaryIndex s),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (seriesInclusion brauerIndex s
            (perSeries s (MonoidAlgebra.single x 1))) =
        decompositionMapOfStableReduction Msys iota hcompat
          (simpleClassToFDRepKZeroGenerator
            (ordinarySeriesLabel series x.val))) :
    ∀ v : MonoidAlgebra ℤ (OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (aggregateLinearEquiv ordinaryIndex brauerIndex perSeries v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero (ordinarySeriesLabel series) v) := by
  let lhs : MonoidAlgebra ℤ (OrdinarySeriesCarrier series) →ₗ[ℤ]
      FDRepKZero k G :=
    (labelledSimpleClassKZero
      (simpleModuleClassEquivIBr iota hinj).symm).toIntLinearMap.comp
        (aggregateLinearEquiv ordinaryIndex brauerIndex perSeries).toLinearMap
  let rhs : MonoidAlgebra ℤ (OrdinarySeriesCarrier series) →ₗ[ℤ]
      FDRepKZero k G :=
    (decompositionMapOfStableReduction Msys iota hcompat).toIntLinearMap.comp
      (labelledSimpleClassKZero (ordinarySeriesLabel series)).toIntLinearMap
  have equality : lhs = rhs := by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    change labelledSimpleClassKZero
        (simpleModuleClassEquivIBr iota hinj).symm
        (aggregateLinearEquiv ordinaryIndex brauerIndex perSeries
          (MonoidAlgebra.single x 1)) = _
    rw [← seriesInclusion_single ordinaryIndex (ordinaryIndex x) ⟨x, rfl⟩,
      aggregateLinearEquiv_seriesInclusion]
    simpa [rhs] using sourceGenerator (ordinaryIndex x) ⟨x, rfl⟩
  intro v
  exact DFunLike.congr_fun equality v

/-- Construct the global integral basic set from the individual series
maps and their literal generator reductions. The ordinary label is fixed. -/
def aggregateOrdinarySeriesBasicSet
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (series : Irr K G → Prop)
    (ordinaryIndex : OrdinarySeriesCarrier series → I)
    (brauerIndex : IBr iota → I)
    (perSeries : ∀ s : I,
      MonoidAlgebra ℤ (SeriesFibre ordinaryIndex s) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s))
    (sourceGenerator : ∀ (s : I) (x : SeriesFibre ordinaryIndex s),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (seriesInclusion brauerIndex s
            (perSeries s (MonoidAlgebra.single x 1))) =
        decompositionMapOfStableReduction Msys iota hcompat
          (simpleClassToFDRepKZeroGenerator
            (ordinarySeriesLabel series x.val))) :
    RestrictedIntegralBasicSetOnIBr iota hinj (OrdinarySeriesCarrier series)
      (decompositionMapOfStableReduction Msys iota hcompat) where
  ordinaryLabel := ordinarySeriesLabel series
  ordinaryLabel_injective := ordinarySeriesLabel_injective series
  linearEquiv := aggregateLinearEquiv ordinaryIndex brauerIndex perSeries
  restricts_decomposition := aggregate_restricts_decomposition Msys iota hcompat hinj
    series ordinaryIndex brauerIndex perSeries sourceGenerator

end Aggregation

section FixedCarriers

variable {ell : ℕ} {K O k G I : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k ell] [IsAlgClosed k]
variable [Group G] [Finite G] [Fintype I]
variable [Fintype (LiteralPrimitiveBlock k G)]
variable (Msys : ModularSystem ell K O k)
variable (iota : PrimeRegularRootEmbedding ell k K G)
variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (S : RationalSeriesSource K G I)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k G => b.val))
variable (blockSeries : LiteralPrimitiveBlock k G → I)

/-- The Brauer index factors through the actual primitive block selector;
there is no independently supplied partition of Brauer characters. -/
def brauerIndex : IBr iota → I :=
  fun phi => blockSeries (irreducibleBrauerCharacterBlock iota hinj blocks phi)

/-- The literal per-series conclusion of FLZ Theorem 2.3, including its
stable decomposition equation on the checked actual ordinary simple label. -/
structure IntegralSeriesData where
  perSeries : ∀ s : I,
    MonoidAlgebra ℤ {chi : Irr K G // chi ∈ S.rationalSeries s} ≃ₗ[ℤ]
      MonoidAlgebra ℤ (SeriesFibre (brauerIndex iota hinj blocks blockSeries) s)
  sourceGenerator : ∀ (s : I) (chi : {chi : Irr K G // chi ∈ S.rationalSeries s}),
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (seriesInclusion (brauerIndex iota hinj blocks blockSeries) s
          (perSeries s (MonoidAlgebra.single chi 1))) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (ordinaryLabel chi.val))

/-- One-way FLZ Theorem 2.3 certificate on these exact carriers. The
ordinary splitting guard is explicit at the source constructor and is
compatible with the SAME characteristic-zero DVR fraction field. The
algebraic group, rational series, and centre coinvariant interpretation
must still be identified by the application. -/
structure Theorem23Certificate (p centreOrder : ℕ)
    [ordinaryCharacteristic : CharZero K]
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card G)] where
  applies : Theorem23Hypotheses p ell centreOrder →
    Nonempty (IntegralSeriesData Msys iota hcompat hinj S blocks blockSeries)

namespace Theorem23Certificate

variable [HasEnoughRootsOfUnity K (Nat.card G)]

/-- Select the one source packet after its exact numerical hypotheses have
been supplied. Later constructions refer to this same selected packet. -/
def data {p centreOrder : ℕ}
    (C : Theorem23Certificate Msys iota hcompat hinj S blocks blockSeries p centreOrder)
    (h : Theorem23Hypotheses p ell centreOrder) :
    IntegralSeriesData Msys iota hcompat hinj S blocks blockSeries :=
  Classical.choice (C.applies h)

end Theorem23Certificate

namespace IntegralSeriesData

variable (T : IntegralSeriesData Msys iota hcompat hinj S blocks blockSeries)

/-- Reuse the canonical literal-membership/index-fibre equivalence; only
the integral coordinates are reindexed. -/
def fibreMaps (s : I) :
    MonoidAlgebra ℤ (SeriesFibre S.ordinaryIndex s) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (SeriesFibre (brauerIndex iota hinj blocks blockSeries) s) :=
  S.perSeriesFromFamily iota (brauerIndex iota hinj blocks blockSeries) T.perSeries s

/-- The new fibre generator is the same literal source generator after
canonical reindexing, not an extra global reduction hypothesis. -/
theorem fibreGenerator (s : I) (x : SeriesFibre S.ordinaryIndex s) :
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (seriesInclusion (brauerIndex iota hinj blocks blockSeries) s
          (T.fibreMaps Msys iota hcompat hinj S blocks blockSeries s
            (MonoidAlgebra.single x 1))) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator
          (ordinarySeriesLabel S.selectedSeries x.val)) := by
  simpa [fibreMaps, RationalSeriesSource.perSeriesFromFamily,
    ordinarySeriesLabel] using T.sourceGenerator s (S.ordinaryFibreEquiv s x)

/-- The actual global basic set is constructed from the selected family
of per-series maps. Its ordinary carrier is the same selected union. -/
def globalBasicSet :
    RestrictedIntegralBasicSetOnIBr iota hinj S.Basic
      (decompositionMapOfStableReduction Msys iota hcompat) :=
  aggregateOrdinarySeriesBasicSet Msys iota hcompat hinj S.selectedSeries
    S.ordinaryIndex (brauerIndex iota hinj blocks blockSeries)
    (T.fibreMaps Msys iota hcompat hinj S blocks blockSeries)
    (T.fibreGenerator Msys iota hcompat hinj S blocks blockSeries)

/-- The derived basic set retains the exact ordinary simple label. -/
@[simp]
theorem globalBasicSet_ordinaryLabel (x : S.Basic) :
    (T.globalBasicSet Msys iota hcompat hinj S blocks blockSeries).ordinaryLabel x =
      ordinaryLabel x.val :=
  rfl

end IntegralSeriesData

namespace Theorem23Certificate

variable [HasEnoughRootsOfUnity K (Nat.card G)]

/-- The source theorem and its hypotheses produce the derived global
basic set; the global equivalence is not a field of the source record. -/
def basicSet {p centreOrder : ℕ}
    (C : Theorem23Certificate Msys iota hcompat hinj S blocks blockSeries p centreOrder)
    (h : Theorem23Hypotheses p ell centreOrder) :
    RestrictedIntegralBasicSetOnIBr iota hinj S.Basic
      (decompositionMapOfStableReduction Msys iota hcompat) :=
  (C.data Msys iota hcompat hinj S blocks blockSeries h).globalBasicSet
    Msys iota hcompat hinj S blocks blockSeries

end Theorem23Certificate

end FixedCarriers

end ModularRep.PaperProofs.TypeBIntegralSeriesSplitting

/- Audit-only arities for the root's focused check, including the explicit
ordinary source guards. These commands add no axioms. -/
#check @ModularRep.PaperProofs.TypeBIntegralSeriesSplitting.Theorem23Certificate.mk
#check @ModularRep.PaperProofs.TypeBIntegralSeriesSplitting.IntegralSeriesData.globalBasicSet
#check @ModularRep.PaperProofs.TypeBIntegralSeriesSplitting.Theorem23Certificate.basicSet


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
