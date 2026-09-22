import ModularRep.PaperProofs.TypeBSpinPrincipalProjectionPIM
import ModularRep.PaperProofs.TypeBSpinRationalUnipotentClassBinding
import Mathlib.GroupTheory.PGroup

/-!
# Projectivity of the actual principal Spin GGGR components

The inducing subgroup and ordinary character are literal. The global standard
input concerns induction from every odd-order subgroup, with no chosen block
or GGGR indices: its values are a nonnegative integral combination of the
same specified PIM functions. The principal-component membership is deduced.

Taylor (2016), Definition5.14 and Lemma5.13(ii), use U(lambda,1.5) and its
linear extension. Unscaled induction from U(lambda,2) is not that formula.
Finite cyclotomic value choices and the algebraic finite-point realization
remain explicit source obligations; no projectivity or basis target is a
field of the GGGR source.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinGGGRProjectivityBinding

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinPrincipalProjectionPIM TypeBSpinRationalUnipotentClassBinding
open TypeBCentralKernelBlockSource
open scoped BigOperators MonoidAlgebra

variable {n r f : ℕ} {F K O k : Type} [Field F] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- Literal ordinary induction on the actual Spin carrier. -/
def inducedFunction (R : Subgroup (Spin n F N)) (chi : Irr K R) : Spin n F N → K := by
  classical
  exact fun g => (Nat.card R : K)⁻¹ *
    ∑ t : Spin n F N, if h : t⁻¹ * g * t ∈ R then chi ⟨t⁻¹ * g * t, h⟩ else 0

section Modular

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)

/-- Standard E1 certificate on every actual odd subgroup and actual ordinary
irreducible character. Induction preserves projectivity after Maschke;
Navarro's same-system PIM formula gives these exact nonnegative coefficients.
This certificate mentions neither a principal block nor a GGGR family. -/
structure OddInductionExpansionCertificate
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))] : Prop where
  expansion : ∀ (R : Subgroup (Spin n F N)) (chi : Irr K R),
    Odd (Nat.card R) →
      ∃ c : IBr iota →₀ ℕ,
        inducedFunction R chi =
          Finsupp.linearCombination ℕ (projectiveIndecomposable Msys iota) c

variable (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
  (b : LiteralPrimitiveBlock k (Spin n F N))
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
  (ordinary : OrdinaryBlockSource Msys iota blocks)

include orthogonality in
/-- The same explicit projection sends every natural PIM combination into
the specified block projective span. This is a finite-sum deduction. -/
theorem projected_combination_mem (c : IBr iota →₀ ℕ) :
    principalProjection Msys iota b blocks ordinary
        (Finsupp.linearCombination ℕ (projectiveIndecomposable Msys iota) c) ∈
      physicalProjectiveSpace Msys iota b := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_nsmul]
  apply Submodule.sum_mem
  intro phi hphi
  exact nsmul_mem
    (principalProjection_projectiveIndecomposable_mem orthogonality Msys iota
      b blocks ordinary phi) (c phi)

include orthogonality in
/-- Principal projection of an actual odd-subgroup induction belongs to
the SAME specified projective span. No projected membership is supplied. -/
theorem projected_induction_mem
    (source : OddInductionExpansionCertificate Msys iota hcompat)
    (R : Subgroup (Spin n F N)) (chi : Irr K R) (odd : Odd (Nat.card R)) :
    principalProjection Msys iota b blocks ordinary (inducedFunction R chi) ∈
      physicalProjectiveSpace Msys iota b := by
  obtain ⟨c, hc⟩ := source.expansion R chi odd
  rw [hc]
  exact projected_combination_mem Msys iota orthogonality b blocks ordinary c

omit [Fintype (LiteralPrimitiveBlock k (Spin n F N))] in
include orthogonality in
/-- Nonnegative scalar products follow from the SAME natural PIM expansion
and actual decomposition multiplicities; no GGGR multiplicity source is needed. -/
theorem scalarProduct_induction_nonnegative
    (source : OddInductionExpansionCertificate Msys iota hcompat)
    (R : Subgroup (Spin n F N)) (psi : Irr K R) (odd : Odd (Nat.card R))
    (chi : Irr K (Spin n F N)) :
    ∃ a : ℕ, scalarProductRight chi.val (inducedFunction R psi) = (a : K) := by
  classical
  obtain ⟨c, hc⟩ := source.expansion R psi odd
  refine ⟨c.sum (fun phi m => m * decompositionNumber Msys iota chi phi), ?_⟩
  rw [hc]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_nsmul]
  simp only [Nat.cast_sum, Nat.cast_mul, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro phi hphi
  rw [show scalarProductRight chi.val (projectiveIndecomposable Msys iota phi) =
      (decompositionNumber Msys iota chi phi : K) from
    congrFun (projectiveIndecomposable_coordinates orthogonality Msys iota phi) chi]

end Modular

variable [Finite F] [CharP F r]

/-- Taylor's literal induction presentation on the actual rational Spin
classes. The local character is the linear extension on U(lambda,1.5).
Its source character values must be transported using the SAME finite roots. -/
structure GGGRInductionSource
    (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
    (gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K) where
  subgroup : UnipotentClass (r := r) (N := N) → Subgroup (Spin n F N)
  definingPrimeGroup : ∀ c, IsPGroup r (subgroup c)
  localCharacter : ∀ c, Irr K (subgroup c)
  linearCharacter : ∀ c, localCharacter c 1 = 1
  gamma_induced : ∀ c, gamma c = inducedFunction (subgroup c) (localCharacter c)

variable (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
  (gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K)
  (induction : GGGRInductionSource parameters rank gamma)

/-- Oddness is derived from the literal defining-prime group and odd field
parameters, not added as a redundant GGGR source field. -/
theorem inducing_order_odd (c : UnipotentClass (r := r) (N := N)) :
    Odd (Nat.card (induction.subgroup c)) := by
  letI : Fact r.Prime := ⟨parameters.prime⟩
  obtain ⟨a, ha⟩ := (induction.definingPrimeGroup c).exists_card_eq
  rw [ha]
  exact parameters.odd.pow

variable [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]

include induction in
/-- The manuscript's principal GGGR projectivity step on the actual
Spin, modular-system, root, block, gamma and induction carriers. -/
theorem principalGGGR_mem_projective
    (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
    (Msys : ModularSystem 2 K O k)
    (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (b : LiteralPrimitiveBlock k (Spin n F N))
    [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
    (blocks : BlockIdempotentDecomposition
      (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
    (ordinary : OrdinaryBlockSource Msys iota blocks)
    (expansion : OddInductionExpansionCertificate Msys iota hcompat)
    (c : UnipotentClass (r := r) (N := N)) :
    principalProjection Msys iota b blocks ordinary (gamma c) ∈
      physicalProjectiveSpace Msys iota b := by
  rw [induction.gamma_induced c]
  exact projected_induction_mem Msys iota hcompat orthogonality b blocks ordinary expansion
    (induction.subgroup c) (induction.localCharacter c)
    (inducing_order_odd parameters rank gamma induction c)

include induction in
/-- Each actual GGGR scalar product has a derived natural multiplicity,
on the same ordinary/root/induction data used by the projectivity proof. -/
theorem gggr_scalarProduct_nonnegative
    (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
    (Msys : ModularSystem 2 K O k)
    (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (expansion : OddInductionExpansionCertificate Msys iota hcompat)
    (chi : Irr K (Spin n F N))
    (c : UnipotentClass (r := r) (N := N)) :
    ∃ a : ℕ, scalarProductRight chi.val (gamma c) = (a : K) := by
  rw [induction.gamma_induced c]
  exact scalarProduct_induction_nonnegative Msys iota hcompat orthogonality expansion
    (induction.subgroup c) (induction.localCharacter c)
    (inducing_order_odd parameters rank gamma induction c) chi

end ModularRep.PaperProofs.TypeBSpinGGGRProjectivityBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
