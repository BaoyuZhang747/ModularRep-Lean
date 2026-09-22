import ModularRep.PaperProofs.TypeBRationalSeriesSource
import ModularRep.PrimitiveBlockAutomorphism

/-!
# The Type B specialisation of the FLZ Theorem 2.3 input

This is a one-way external certificate for the individual rational-series
integral basic sets in Feng--Li--Zhang (2022), Theorem 2.3, p. 537. It is
indexed by one rational-series family, one actual group, one modular
system, and the literal primitive modular blocks. Its Brauer partition is
the composite of the actual block assignment and the supplied
Broue--Michel block index.

Oddness is the good-prime specialisation for type B in the manuscript's
rank range. The application must bind the defining prime and the stated
centre component-group coinvariant order to its algebraic Spin or special Clifford
model. In particular, an arbitrary natural number is not evidence about
the algebraic centre. The rational-series family and the block index have
their external, canonically sourced meanings; these meanings are not
proved by the existence of this record.

The certificate supplies only individual integral maps and their exact
decomposition identities. The global integral basic set is then derived
by the checked finite-series aggregation. No equivariant set bijection,
blockwise lattice equivalence, BAW or iBAW predicate occurs as an input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBIntegralSeriesCertificate

open ModularRep
open DecompositionBasicSetBridge ExactGrothendieckGroup FDRepSimpleClassKZero
open OrdinaryIrreducibleCharacter TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet TypeBRationalSeriesSource

universe u

/-- The numerical hypotheses used to specialise FLZ Theorem 2.3 to the
Type B rank range. The source application separately fixes that range and
identifies `centreOrder` with the order of `(Z(G)/Z(G)^0)_F`, the largest
quotient on which Frobenius acts trivially, exactly as stated in FLZ
Theorem 2.3. This is a coinvariant group, not a fixed-point subgroup. -/
structure Theorem23Hypotheses (p ell centreOrder : ℕ) : Prop where
  ell_prime : Nat.Prime ell
  nondefining : ell ≠ p
  ell_odd : Odd ell
  centre_primeTo : ¬ ell ∣ centreOrder

section FixedCarriers

variable {ell : ℕ} {K O k G I : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable [Group G] [Finite G] [Fintype I]
variable [Fintype (LiteralPrimitiveBlock k G)]
variable (Msys : ModularSystem ell K O k)
variable (iota : PrimeRegularRootEmbedding ell k K G)
variable (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (S : RationalSeriesSource K G I)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k G => b.1))
variable (blockSeries : LiteralPrimitiveBlock k G → I)

/-- The Brauer series index is forced to pass through the actual primitive
modular block of the character. It is not a separate partition input. -/
def brauerIndex : IBr iota → I :=
  fun phi => blockSeries (irreducibleBrauerCharacterBlock iota hinj blocks phi)

/-- The exact per-series conclusion of the external basic-set theorem,
on literal ordinary-series membership and actual Brauer block fibres. -/
structure IntegralSeriesData where
  perSeries : ∀ s : I,
    MonoidAlgebra ℤ {chi : Irr K G // chi ∈ S.rationalSeries s} ≃ₗ[ℤ]
      MonoidAlgebra ℤ (SeriesFibre (brauerIndex iota hinj blocks blockSeries) s)
  sourceGenerator : ∀ (s : I) (chi : {chi : Irr K G // chi ∈ S.rationalSeries s}),
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (seriesInclusion (brauerIndex iota hinj blocks blockSeries) s
          (perSeries s (MonoidAlgebra.single chi 1))) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator (simpleModuleClassLabel chi.1))

/-- FLZ Theorem 2.3 used only forward, with its Type B hypotheses and its
fixed source conclusion. There is no caller-selected target predicate. -/
structure Theorem23Certificate (p centreOrder : ℕ) where
  applies : Theorem23Hypotheses p ell centreOrder →
    Nonempty (IntegralSeriesData Msys iota hcompat hinj S blocks blockSeries)

namespace Theorem23Certificate

/-- Select the single source packet used by the application, only after
the stated theorem hypotheses have been supplied. Subsequent action data
can refer to this same selected packet. -/
def data {p centreOrder : ℕ}
    (C : Theorem23Certificate Msys iota hcompat hinj S blocks blockSeries p centreOrder)
    (h : Theorem23Hypotheses p ell centreOrder) :
    IntegralSeriesData Msys iota hcompat hinj S blocks blockSeries :=
  Classical.choice (C.applies h)

end Theorem23Certificate

namespace IntegralSeriesData

variable (T : IntegralSeriesData Msys iota hcompat hinj S blocks blockSeries)

/-- The individual source maps transported to the canonical index fibres
of the selected rational-series union. -/
def fibreMaps (s : I) :
    MonoidAlgebra ℤ (SeriesFibre S.ordinaryIndex s) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (SeriesFibre (brauerIndex iota hinj blocks blockSeries) s) :=
  S.perSeriesFromFamily iota (brauerIndex iota hinj blocks blockSeries) T.perSeries s

/-- The transported generator identity is derived from the literal source
generator; it is not an extra global decomposition premise. -/
theorem fibreGenerator (s : I) (x : SeriesFibre S.ordinaryIndex s) :
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
        (seriesInclusion (brauerIndex iota hinj blocks blockSeries) s
          (T.fibreMaps Msys iota hcompat hinj S blocks blockSeries s
            (MonoidAlgebra.single x 1))) =
      decompositionMapOfStableReduction Msys iota hcompat
        (simpleClassToFDRepKZeroGenerator
          (ordinarySeriesLabel (K := K) S.selectedSeries x.1)) := by
  simpa [fibreMaps, RationalSeriesSource.perSeriesFromFamily,
    ordinarySeriesLabel] using T.sourceGenerator s (S.ordinaryFibreEquiv s x)

/-- The full basic set is a checked consequence of the per-series
certificate. Its ordinary carrier remains the literal selected union. -/
def globalBasicSet :=
  aggregateOrdinarySeriesBasicSet Msys iota hcompat hinj S.selectedSeries
    S.ordinaryIndex (brauerIndex iota hinj blocks blockSeries)
    (T.fibreMaps Msys iota hcompat hinj S blocks blockSeries)
    (T.fibreGenerator Msys iota hcompat hinj S blocks blockSeries)

end IntegralSeriesData

end FixedCarriers

end ModularRep.PaperProofs.TypeBIntegralSeriesCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
