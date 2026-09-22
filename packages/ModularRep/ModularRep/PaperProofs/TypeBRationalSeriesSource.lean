import ModularRep.PaperProofs.TypeBRationalSeriesBasicSet

/-!
# A single rational-series family for the Type B source application

The external family is the rational Lusztig series on the fixed actual
set of ordinary characters. Its source identity remains an explicit
literature boundary. The global ordinary carrier and its index map are
defined from that one family; they cannot be chosen independently.

The application defines the Brauer index through its actual primitive block
and the Broue--Michel block partition. This file transports the individual
source lattice maps from literal rational-series membership subtypes to the
fibres consumed by the checked aggregation. No global basic set or set
bijection is supplied.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRationalSeriesSource

open ModularRep
open OrdinaryIrreducibleCharacter
open TypeBSpecialCliffordActionAdapter
open TypeBRationalSeriesBasicSet

universe u

/-- The externally defined rational Lusztig series, all on the same actual
set of ordinary characters. Disjointness is the standard uniqueness of the
semisimple rational-series label. The literal source meaning of this family
must be recorded by its application. -/
structure RationalSeriesSource (K G I : Type u) [Field K] [Group G] where
  rationalSeries : I → Set (Irr K G)
  disjoint : ∀ {s t : I} {chi : Irr K G},
    chi ∈ rationalSeries s → chi ∈ rationalSeries t → s = t

namespace RationalSeriesSource

variable {K G I : Type u} [Field K] [Group G]
variable (S : RationalSeriesSource K G I)

/-- The union of exactly the indexed rational series. -/
def selectedSeries (chi : Irr K G) : Prop :=
  ∃ s : I, chi ∈ S.rationalSeries s

abbrev Basic := OrdinarySeriesCarrier S.selectedSeries

/-- The unique rational-series index of an element of the selected union. -/
def ordinaryIndex (x : S.Basic) : I := Classical.choose x.2

theorem ordinaryIndex_mem (x : S.Basic) :
    x.1 ∈ S.rationalSeries (S.ordinaryIndex x) := Classical.choose_spec x.2

theorem ordinaryIndex_eq_iff (x : S.Basic) (s : I) :
    S.ordinaryIndex x = s ↔ x.1 ∈ S.rationalSeries s := by
  constructor
  · intro h
    simpa [h] using S.ordinaryIndex_mem x
  · intro h
    exact S.disjoint (S.ordinaryIndex_mem x) h

/-- The canonical index fibre is the literal membership subtype supplied by
the rational-series source. -/
def ordinaryFibreEquiv (s : I) :
    SeriesFibre S.ordinaryIndex s ≃ {chi : Irr K G // chi ∈ S.rationalSeries s} where
  toFun x := ⟨x.1.1, (S.ordinaryIndex_eq_iff x.1 s).mp x.2⟩
  invFun chi :=
    ⟨⟨chi.1, ⟨s, chi.2⟩⟩, (S.ordinaryIndex_eq_iff ⟨chi.1, ⟨s, chi.2⟩⟩ s).mpr chi.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv chi := by
    apply Subtype.ext
    rfl

@[simp]
theorem ordinaryFibreEquiv_val (s : I) (x : SeriesFibre S.ordinaryIndex s) :
    (S.ordinaryFibreEquiv s x).1 = x.1.1 := rfl

section Brauer

variable {p : ℕ} {k : Type u} [Field k]
variable [Finite G] [CharZero K] [IsAlgClosed K] [CharP k p] [IsAlgClosed k]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (brauerIndex : IBr iota → I)

/-- Reindex the individual source maps on literal rational-series members.
The Brauer index is supplied by the application's actual block partition. -/
def perSeriesFromFamily
    (perSeries : ∀ s : I,
      MonoidAlgebra ℤ {chi : Irr K G // chi ∈ S.rationalSeries s} ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s))
    (s : I) :
    MonoidAlgebra ℤ (SeriesFibre S.ordinaryIndex s) ≃ₗ[ℤ]
      MonoidAlgebra ℤ (SeriesFibre brauerIndex s) :=
  (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ (S.ordinaryFibreEquiv s)).trans
    (perSeries s)

/-- Reindexing preserves exactly the source's ordinary generator. This is
the join used to pass its generator reduction identity to aggregation. -/
@[simp]
theorem perSeriesFromFamily_single
    (perSeries : ∀ s : I,
      MonoidAlgebra ℤ {chi : Irr K G // chi ∈ S.rationalSeries s} ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s))
    (s : I) (x : SeriesFibre S.ordinaryIndex s) :
    S.perSeriesFromFamily iota brauerIndex perSeries s (MonoidAlgebra.single x 1) =
      perSeries s (MonoidAlgebra.single (S.ordinaryFibreEquiv s x) 1) := by
  simp [perSeriesFromFamily]

end Brauer

end RationalSeriesSource

end ModularRep.PaperProofs.TypeBRationalSeriesSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
