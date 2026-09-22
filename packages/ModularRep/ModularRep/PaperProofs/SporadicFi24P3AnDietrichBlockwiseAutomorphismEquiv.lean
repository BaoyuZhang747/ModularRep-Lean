import ModularRep.PaperProofs.SporadicFi24P3AnDietrichSourceCertificate
import ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual

/-!
# The blockwise automorphism-equivariant Fischer correspondence at three

This file composes exactly three existing layers:

1. the An--Dietrich source certificate and explicit literal-carrier bridge
   produce the equivariant principal block-fibre equivalence by cancellation;
2. the principal map is combined with the two independently constructed
   known block-fibre equivalences;
3. the selected-outer equivariance of that construction is promoted through the
   explicit `C2OuterActionSource` to all literal automorphisms.

The conclusion is a block-preserving equivalence of the two complete literal
carriers, equivariant under every element of `(MulAut X)ᵐᵒᵖ`.  Character
triples, `Q = 1` normalisation, extension clauses, BAW, and iBAW do not occur
in either the hypotheses or the conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3AnDietrichBlockwiseAutomorphismEquiv

open Formalisation
open Formalisation.BlockCancellation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24QOneNormalisationActual
open SporadicFi24ThreeBlockCancellationActual
open SporadicFi24KnownFibreBridgeActual
open SporadicFi24ThreeBlockAutomorphismPromotionActual
open SporadicFi24P3AnDietrichSourceCertificate
open SporadicFi24P3AnDietrichSourceCertificate.AnDietrichFi24P3SourceCertificate

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

/-- The source-facing endpoint after three-block construction and full
automorphism promotion.  The An--Dietrich input is only a global equivariant
bijection on its own carriers; block preservation is derived after principal
fibre cancellation and construction. -/
theorem exists_blockPreservingAutEquivariantEquiv_from_anDietrich
    (AD : AnDietrichFi24P3SourceCertificate
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight))
    (Bridge : AnDietrichFi24P3LiteralCarrierBridge
      (SourceAction := SourceAction)
      (SourceBrauer := SourceBrauer)
      (SourceWeight := SourceWeight) (k := k) (K := K) (X := X) iota)
    (hcenter : ∀ z : Subgroup.center X, z = 1)
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
          brauerBlock iota hinj blocks phi) := by
  obtain ⟨principal, hprincipal⟩ :=
    exists_principalFibreEquiv_from_anDietrich
      iota AD Bridge hinj blocks E1 hcenter D T C B Z0 S F0 NC
  let Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S :=
    fi24ThreeKnownEquivalences
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (E1 := E1)
      D T C B Z0 S F0 NC
  let Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X) :=
    assembledThreeBlockEquiv iota hinj blocks E1 S principal Known
  have houter :
      Intertwines Omega
        (totalBrauerPerm iota S) (totalWeightPerm (K := K) S) := by
    simpa only [Omega] using
      assembledThreeBlockEquiv_intertwines
        iota hinj blocks E1 S principal Known hprincipal
  refine ⟨Omega, ?_, ?_⟩
  · exact fullAutomorphism_equivariant
      iota S OuterSource Omega houter
  · simpa only [Omega] using
      assembledThreeBlockEquiv_preserves_block
        iota hinj blocks E1 S principal Known

end ModularRep.PaperProofs.SporadicFi24P3AnDietrichBlockwiseAutomorphismEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
