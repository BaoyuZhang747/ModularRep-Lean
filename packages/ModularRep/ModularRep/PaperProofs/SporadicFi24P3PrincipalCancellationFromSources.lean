import ModularRep.PaperProofs.SporadicFi24KnownFibreBridgeActual
import ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

/-!
# The principal three-block cancellation for the Fischer group

This file gives the source-facing form of the cancellation used for
`Fi'_{24}` at the prime three. The literature supplies an equivariant
correspondence on the whole centreless carrier, but no block preservation.
The nonprincipal equivalence is constructed from its cardinality and fixed
point counts, and the defect-zero equivalence is constructed from the
normalised defect-zero sources. Finite `C₂`-set cancellation then produces
the principal-block equivalence.

No principal-block correspondence, principal signature, block-preserving
global correspondence, extension condition, or iBAW conclusion is an input.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3PrincipalCancellationFromSources

open Formalisation
open Formalisation.BlockCancellation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24QOneNormalisationActual
open SporadicFi24ThreeBlockCancellationActual
open SporadicFi24KnownFibreBridgeActual

universe u

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

/-- The source-facing form of the principal-block cancellation. The two known
fibre equivalences are constructed inside the proof rather than supplied as a
correspondence-shaped hypothesis. -/
theorem exists_principalFibreEquiv_from_sources
    (hcenter : ∀ z : Subgroup.center X, z = 1)
    (rawEquiv : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (rawEquivariant : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      rawEquiv (a • phi) = a • rawEquiv phi)
    (D : DefectZeroReductionSource iota)
    (T : TrivialWeightSource 3 X)
    (C : TrivialWeightBlockCompatibility iota hinj blocks R D T)
    (B : DefectZeroOrdinaryBlockSource iota hinj blocks D)
    (Z0 : DefectZeroWeightSubgroupSource iota hinj blocks (R := R) D)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (F0 : Fi24DefectZeroBlockIdentification iota hinj blocks D S)
    (NC : Fi24NonprincipalCensusSource iota hinj blocks E1 S) :
    ∃ principal :
        BrauerFibre iota hinj blocks S.principalBlock ≃
          WeightFibre (R := R) S.principalBlock,
      Intertwines principal
        (principalBrauerPerm iota hinj blocks E1 S)
        (principalWeightPerm (R := R) S) :=
  exists_principalFibreEquiv_of_equivariantEquiv
    iota hinj blocks E1 hcenter rawEquiv rawEquivariant S
    (fi24ThreeKnownEquivalences
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) (E1 := E1)
      D T C B Z0 S F0 NC)

end ModularRep.PaperProofs.SporadicFi24P3PrincipalCancellationFromSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
