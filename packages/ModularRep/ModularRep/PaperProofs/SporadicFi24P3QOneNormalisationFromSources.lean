import ModularRep.PaperProofs.SporadicFi24P3AnDietrichBlockwiseAutomorphismEquiv
import ModularRep.PaperProofs.SporadicFi24ThreeBlockQOneNormalisationActual

/-!
# The normalisation at the trivial radical subgroup for `Fi'_{24}` at three

The source-facing Fischer correspondence constructed in the preceding window
is fully automorphism equivariant and preserves blocks.  This file derives its
normalisation at `Q = 1` from the independent defect-zero sources already used
for the defect-zero block.

The external inputs identify the An--Dietrich carriers and action, the three
literal blocks, the two known block fibres, and the canonical defect-zero
reduction and trivial-subgroup weight.  No value of the combined
correspondence, normalisation statement, character-triple condition,
compatible extension, BAW, or iBAW conclusion is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3QOneNormalisationFromSources

open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24QOneNormalisationActual
open SporadicFi24ThreeBlockCancellationActual
open SporadicFi24KnownFibreBridgeActual
open SporadicFi24ThreeBlockAutomorphismPromotionActual
open SporadicFi24ThreeBlockQOneNormalisationActual
open SporadicFi24P3AnDietrichSourceCertificate
open SporadicFi24P3AnDietrichBlockwiseAutomorphismEquiv

universe u

variable {SourceAction SourceBrauer SourceWeight : Type u}
variable [Group SourceAction]
variable [MulAction SourceAction SourceBrauer]
variable [MulAction SourceAction SourceWeight]

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-- The source-facing blockwise correspondence satisfies the normalisation at
the trivial radical subgroup.  Defect-zero uniqueness, rather than a chosen
value of the An--Dietrich bijection, forces the final equality. -/
theorem exists_blockPreservingAutEquivariantEquiv_with_qOne_from_sources
    (AD : AnDietrichFi24P3SourceCertificate
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight))
    (Bridge : AnDietrichFi24P3LiteralCarrierBridge
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)
    (hCenter : Subgroup.center X = ⊥)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z0 : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F0 : Fi24DefectZeroBlockIdentification iota hinj blocks D S)
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S)
    (OuterSource : C2OuterActionSource iota S) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ d : GlobalDefectZeroCharacter (p := 3) (K := K) (X := X),
        Omega (D.reduce (iota := iota) d) = T.atOne d) := by
  have hcenter : ∀ z : Subgroup.center X, z = 1 := by
    intro z
    apply Subtype.ext
    have hz : z.1 ∈ (⊥ : Subgroup X) := by
      rw [← hCenter]
      exact z.2
    exact Subgroup.mem_bot.mp hz
  obtain ⟨Omega, hOmega, hblock⟩ :=
    exists_blockPreservingAutEquivariantEquiv_from_anDietrich
      iota hinj blocks E1 AD Bridge hcenter D T C B Z0 S F0 NC OuterSource
  refine ⟨Omega, hOmega, hblock, ?_⟩
  intro d
  exact threeBlock_literal_qOne_normalisation
    (R := R) iota hinj blocks Omega hblock D T C B d

end ModularRep.PaperProofs.SporadicFi24P3QOneNormalisationFromSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
