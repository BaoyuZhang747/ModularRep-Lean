import ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.Pi

/-!
# Aggregating the rational-series basic sets in Type B

Theorem 2.3 of Feng--Li--Zhang, *The inductive blockwise Alperin weight
condition for type B and odd primes* (2022), p. 537, supplies an integral
basic set for each rational semisimple `ell'`-series and its Broue--Michel
union, subject to its good-prime, nondefining-prime, and centre hypotheses.

This file checks the direct-sum deduction from those individual inputs. The
ordinary carrier is a specified subtype of actual function-valued `Irr`;
the modular carrier is actual function-valued `IBr`. Their maps to the same
finite index type record the disjoint and exhaustive series partitions.
Every source application must identify those maps with the rational-series
and Broue--Michel partitions and discharge the literal theorem hypotheses.
An arbitrary partition has no claim to that source identification.

The inputs are individual integral lattice equivalences and their exact
decomposition identities on ordinary generators. Neither a global basic-set
equivalence nor any ordinary/Brauer set bijection is assumed. No action or
block stability is asserted here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRationalSeriesBasicSet

open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.TypeBSpecialCliffordActionAdapter

universe u

section Partition

variable {X Y I : Type u} [Fintype I]

/-- The literal fibre of a series-index map. -/
abbrev SeriesFibre (index : X → I) (s : I) := {x : X // index x = s}

/-- The finite direct-sum decomposition of a free integral module by its
series-index map. This is constructed from the fibres, not supplied. -/
def partitionLinearEquiv (index : X → I) :
    MonoidAlgebra ℤ X ≃ₗ[ℤ]
      (s : I) → MonoidAlgebra ℤ (SeriesFibre index s) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).trans <|
    (Finsupp.domLCongr (Equiv.sigmaFiberEquiv index).symm).trans <|
      (Finsupp.sigmaFinsuppLEquivPiFinsupp ℤ).trans <|
        LinearEquiv.piCongrRight fun _ =>
          (MonoidAlgebra.coeffLinearEquiv ℤ).symm

@[simp]
theorem partitionLinearEquiv_coeff (index : X → I)
    (v : MonoidAlgebra ℤ X) (s : I) (x : SeriesFibre index s) :
    (partitionLinearEquiv index v s).coeff x = v.coeff x.1 := by
  simp [partitionLinearEquiv, Finsupp.domLCongr_apply,
    Finsupp.equivMapDomain_apply]

/-- Insert one series summand in the whole free module. -/
def seriesInclusion (index : X → I) (s : I) :
    MonoidAlgebra ℤ (SeriesFibre index s) →ₗ[ℤ] MonoidAlgebra ℤ X := by
  classical
  exact (partitionLinearEquiv index).symm.toLinearMap.comp
    (LinearMap.single ℤ (fun t => MonoidAlgebra ℤ (SeriesFibre index t)) s)

theorem partitionLinearEquiv_single [DecidableEq I] (index : X → I) (s : I)
    (x : SeriesFibre index s) :
    partitionLinearEquiv index (MonoidAlgebra.single x.1 1) =
      Pi.single s (MonoidAlgebra.single x (1 : ℤ)) := by
  classical
  funext t
  apply MonoidAlgebra.coeff_injective
  ext y
  rw [partitionLinearEquiv_coeff]
  by_cases h : t = s
  · subst t
    simp only [Pi.single_eq_same, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, Subtype.ext_iff]
  · have hy : y.1 ≠ x.1 := by
      intro hyx
      exact h (y.2.symm.trans ((congrArg index hyx).trans x.2))
    simp [Pi.single_eq_of_ne h, MonoidAlgebra.coeff_single,
      Finsupp.single_apply, hy, Ne.symm hy]

@[simp]
theorem seriesInclusion_single (index : X → I) (s : I)
    (x : SeriesFibre index s) :
    seriesInclusion index s (MonoidAlgebra.single x 1) =
      MonoidAlgebra.single x.1 1 := by
  classical
  apply (partitionLinearEquiv index).injective
  simp only [seriesInclusion, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.single_apply, partitionLinearEquiv_single]

/-- Combine the individual rational-series lattice equivalences. -/
def aggregateLinearEquiv (ordinaryIndex : X → I) (brauerIndex : Y → I)
    (perSeries : ∀ s : I,
      MonoidAlgebra ℤ (SeriesFibre ordinaryIndex s) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s)) :
    MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y :=
  (partitionLinearEquiv ordinaryIndex).trans <|
    (LinearEquiv.piCongrRight perSeries).trans
      (partitionLinearEquiv brauerIndex).symm

/-- The resulting map agrees with its stated input on each series. -/
theorem aggregateLinearEquiv_seriesInclusion
    (ordinaryIndex : X → I) (brauerIndex : Y → I)
    (perSeries : ∀ s : I,
      MonoidAlgebra ℤ (SeriesFibre ordinaryIndex s) ≃ₗ[ℤ]
        MonoidAlgebra ℤ (SeriesFibre brauerIndex s))
    (s : I) (v : MonoidAlgebra ℤ (SeriesFibre ordinaryIndex s)) :
    aggregateLinearEquiv ordinaryIndex brauerIndex perSeries
        (seriesInclusion ordinaryIndex s v) =
      seriesInclusion brauerIndex s (perSeries s v) := by
  classical
  apply (partitionLinearEquiv brauerIndex).injective
  simp only [aggregateLinearEquiv, seriesInclusion,
    LinearEquiv.trans_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
    LinearMap.single_apply]
  funext t
  by_cases h : t = s
  · subst t
    simp
  · simp [LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne h]

end Partition

section BlockSupport

open ModularRep.BlockFibreRestriction

variable {X Y I : Type u} [Fintype I]

@[simp]
theorem partitionLinearEquiv_symm_coeff (index : X → I)
    (v : (s : I) → MonoidAlgebra ℤ (SeriesFibre index s)) (x : X) :
    ((partitionLinearEquiv index).symm v).coeff x =
      (v (index x)).coeff ⟨x, rfl⟩ := by
  have h := partitionLinearEquiv_coeff index
    ((partitionLinearEquiv index).symm v) (index x) ⟨x, rfl⟩
  simpa using h.symm

/-- The ordinary coordinate projection onto one block summand. -/
def blockProjector (index : X → I) (s : I) :
    MonoidAlgebra ℤ X →ₗ[ℤ] MonoidAlgebra ℤ X :=
  (seriesInclusion index s).comp
    ((LinearMap.proj s).comp (partitionLinearEquiv index).toLinearMap)

theorem blockProjector_coeff [DecidableEq I] (index : X → I) (s : I)
    (v : MonoidAlgebra ℤ X) (x : X) :
    (blockProjector index s v).coeff x =
      if index x = s then v.coeff x else 0 := by
  classical
  simp only [blockProjector, seriesInclusion, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearMap.proj_apply, LinearMap.single_apply,
    partitionLinearEquiv_symm_coeff]
  by_cases h : index x = s
  · subst s
    simp
  · simp [Pi.single_eq_of_ne h, h]

theorem blockProjector_eq_self_of_supported (index : X → I) (s : I)
    (v : MonoidAlgebra ℤ X)
    (hv : v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet index s)) :
    blockProjector index s v = v := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [blockProjector_coeff]
  by_cases h : index x = s
  · simp [h]
  · have hz := (MonoidAlgebra.mem_supported'.mp hv) x h
    simp [h, hz]

theorem blockProjector_eq_zero_of_supported_other (index : X → I)
    (s t : I) (hst : s ≠ t) (v : MonoidAlgebra ℤ X)
    (hv : v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet index t)) :
    blockProjector index s v = 0 := by
  classical
  apply MonoidAlgebra.coeff_injective
  ext x
  rw [blockProjector_coeff]
  by_cases h : index x = s
  · have hxt : index x ≠ t := fun hxt => hst (h.symm.trans hxt)
    have hz := (MonoidAlgebra.mem_supported'.mp hv) x hxt
    simp [h, hz]
  · simp [h]

theorem single_mem_blockSupported (index : X → I) (x : X) :
    MonoidAlgebra.single x (1 : ℤ) ∈
      MonoidAlgebra.supported ℤ ℤ (blockFibreSet index (index x)) := by
  classical
  rw [MonoidAlgebra.mem_supported']
  intro y hy
  have hxy : x ≠ y := by
    intro hxy
    exact hy (by simpa [blockFibreSet, hxy])
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, hxy]

/-- Forward block support on ordinary generators already forces support
for the inverse integral matrix. The inverse-support clause is therefore a
deduction from block diagonality, not an additional literature input. -/
theorem blockDiagonalLinearEquiv_of_generator_support
    (ordinaryBlock : X → I) (brauerBlock : Y → I)
    (d : MonoidAlgebra ℤ X ≃ₗ[ℤ] MonoidAlgebra ℤ Y)
    (forwardGenerator : ∀ x : X,
      d (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet brauerBlock (ordinaryBlock x))) :
    BlockDiagonalLinearEquiv ordinaryBlock brauerBlock d := by
  classical
  have forward : ∀ (s : I) (v : MonoidAlgebra ℤ X),
      v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet ordinaryBlock s) →
        d v ∈ MonoidAlgebra.supported ℤ ℤ (blockFibreSet brauerBlock s) := by
    intro s v hv
    have hle : MonoidAlgebra.supported ℤ ℤ (blockFibreSet ordinaryBlock s) ≤
        (MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet brauerBlock s)).comap d.toLinearMap := by
      rw [MonoidAlgebra.supported_eq_span_single]
      apply Submodule.span_le.mpr
      rintro _ ⟨x, hx, rfl⟩
      change d (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ (blockFibreSet brauerBlock s)
      have hx' : ordinaryBlock x = s := hx
      simpa [hx'] using forwardGenerator x
    exact hle hv
  have commutes : ∀ (s : I) (v : MonoidAlgebra ℤ X),
      d (blockProjector ordinaryBlock s v) = blockProjector brauerBlock s (d v) := by
    intro s
    have hm : d.toLinearMap.comp (blockProjector ordinaryBlock s) =
        (blockProjector brauerBlock s).comp d.toLinearMap := by
      apply MonoidAlgebra.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      change d (blockProjector ordinaryBlock s (MonoidAlgebra.single x 1)) =
        blockProjector brauerBlock s (d (MonoidAlgebra.single x 1))
      by_cases h : s = ordinaryBlock x
      · subst s
        rw [blockProjector_eq_self_of_supported _ _ _
          (single_mem_blockSupported ordinaryBlock x),
          blockProjector_eq_self_of_supported _ _ _ (forwardGenerator x)]
      · rw [blockProjector_eq_zero_of_supported_other ordinaryBlock s
          (ordinaryBlock x) h _ (single_mem_blockSupported ordinaryBlock x),
          blockProjector_eq_zero_of_supported_other brauerBlock s
          (ordinaryBlock x) h _ (forwardGenerator x), map_zero]
    intro v
    exact DFunLike.congr_fun hm v
  refine ⟨forward, ?_⟩
  intro s v hv
  have hp : blockProjector ordinaryBlock s (d.symm v) = d.symm v := by
    apply d.injective
    rw [commutes, d.apply_symm_apply,
      blockProjector_eq_self_of_supported _ _ _ hv]
  rw [MonoidAlgebra.mem_supported']
  intro x hx
  have he := congrArg (fun w : MonoidAlgebra ℤ X => w.coeff x) hp
  rw [blockProjector_coeff] at he
  have hx' : ordinaryBlock x ≠ s := hx
  simpa [hx'] using he.symm

end BlockSupport

section ActualCharacters

variable {p : ℕ} {K O k G I : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k p] [IsAlgClosed k]
variable [Group G] [Finite G] [Fintype I]

/-- Generator-level compatibility from each rational-series basic-set input
implies the exact decomposition identity for the combined global map. -/
theorem aggregate_restricts_decomposition
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
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
            (ordinarySeriesLabel (K := K) series x.1))) :
    ∀ v : MonoidAlgebra ℤ (OrdinarySeriesCarrier series),
      labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (aggregateLinearEquiv ordinaryIndex brauerIndex perSeries v) =
        decompositionMapOfStableReduction Msys iota hcompat
          (labelledSimpleClassKZero (ordinarySeriesLabel (K := K) series) v) := by
  let lhs : MonoidAlgebra ℤ (OrdinarySeriesCarrier series) →ₗ[ℤ]
      FDRepKZero k G :=
    (labelledSimpleClassKZero
      (simpleModuleClassEquivIBr iota hinj).symm).toIntLinearMap.comp
        (aggregateLinearEquiv ordinaryIndex brauerIndex perSeries).toLinearMap
  let rhs : MonoidAlgebra ℤ (OrdinarySeriesCarrier series) →ₗ[ℤ]
      FDRepKZero k G :=
    (decompositionMapOfStableReduction Msys iota hcompat).toIntLinearMap.comp
      (labelledSimpleClassKZero
        (ordinarySeriesLabel (K := K) series)).toIntLinearMap
  have heq : lhs = rhs := by
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
  exact DFunLike.congr_fun heq v

/-- The global integral basic set required by Lemma 4.2, constructed from
the individual series certificates and their generator identities. -/
def aggregateOrdinarySeriesBasicSet
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
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
            (ordinarySeriesLabel (K := K) series x.1))) :=
  ordinarySeriesBasicSet Msys iota hcompat hinj series
    (aggregateLinearEquiv ordinaryIndex brauerIndex perSeries)
    (aggregate_restricts_decomposition Msys iota hcompat hinj series
      ordinaryIndex brauerIndex perSeries sourceGenerator)

end ActualCharacters

end ModularRep.PaperProofs.TypeBRationalSeriesBasicSet


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
