import ModularRep.PaperProofs.TypeBSpinPrincipalProjectiveBinding

/-!
# Specified block projection of every literal Spin PIM

The PIM, ordinary Fourier projector, decomposition coefficients and specified
block selector are exactly those in the frozen projective/decomposition
bindings. No projector membership or projectivity source is introduced.
The result works for each specified primitive block; the principal GGGR
application uses its already chosen principal block.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinPrincipalProjectionPIM

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinPrincipalProjectiveBinding TypeBSpinPrincipalDecompositionBinding
open TypeBCentralKernelBlockSource
open scoped BigOperators MonoidAlgebra

variable {n : ℕ} {F K O k : Type} [Field F] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable (orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K))
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (b : LiteralPrimitiveBlock k (Spin n F N))
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val))
  (source : OrdinaryBlockSource Msys iota blocks)

include orthogonality in
/-- A PIM indexed outside the chosen specified block has zero Fourier
projection into that block, by the same actual decomposition support. -/
theorem projection_zero_of_unsupported (phi : IBr iota)
    (unsupported : ¬ Supported iota b phi) :
    principalProjection Msys iota b blocks source
      (projectiveIndecomposable Msys iota phi) = 0 := by
  classical
  rw [principalProjection_apply]
  apply Finset.sum_eq_zero
  intro chi hchi
  by_cases selected : source.ordinaryBlock chi = b
  · have coefficient_zero : decompositionNumber Msys iota chi phi = 0 := by
      apply decompositionNumber_zero_of_other_block Msys iota blocks source chi phi
      intro supported
      exact unsupported (selected ▸ supported)
    have coefficient_value :
        scalarProductRight chi.val (projectiveIndecomposable Msys iota phi) =
          (decompositionNumber Msys iota chi phi : K) :=
      congrFun (projectiveIndecomposable_coordinates orthogonality Msys iota phi) chi
    simp only [if_pos selected, coefficient_value, coefficient_zero, Nat.cast_zero, zero_smul]
  · simp only [if_neg selected, zero_smul]

include orthogonality in
/-- The specified projection of every PIM belongs to the chosen specified
PIM span, including PIMs whose Brauer labels lie in other blocks. -/
theorem principalProjection_projectiveIndecomposable_mem (phi : IBr iota) :
    principalProjection Msys iota b blocks source
      (projectiveIndecomposable Msys iota phi) ∈ physicalProjectiveSpace Msys iota b := by
  classical
  by_cases supported : Supported iota b phi
  · rw [principalProjection_projectiveIndecomposable orthogonality Msys iota b blocks source
      ⟨phi, supported⟩]
    exact projectiveIndecomposable_mem Msys iota b ⟨phi, supported⟩
  · rw [projection_zero_of_unsupported orthogonality Msys iota b blocks source phi supported]
    exact Submodule.zero_mem _

end ModularRep.PaperProofs.TypeBSpinPrincipalProjectionPIM


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
