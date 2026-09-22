import Formalisation.EquivariantActions
import ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual

/-!
# Character triple retention for the Fischer three block equivalence

The preceding cancellation and promotion modules construct a fully
automorphism equivariant, block preserving equivalence on the three literal
blocks used for `Fi'_{24}` at the coefficient prime three.  This module
extracts two formal consequences of that construction: matched characters and
weights have the same central sector and the same automorphism stabiliser.

The implication from those two equalities to the modular character triple
condition is an `E2/U` source input.  Its intended use is the centreless group
`Fi'_{24}`, for which every central character sector is faithful.  Lean applies
that implication to the constructed equivalence, but it does not prove the
cited character triple theorem itself.  Compatible extensions, intermediate
block equalities, BAW, and iBAW are neither inputs nor conclusions of this
module.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual

open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24ThreeBlockAutomorphismPromotionActual

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

/-- The external character triple implication used after sector transport.
It contains no equivalence, block map, or inductive conclusion. -/
structure CharacterTripleRetentionSource
    (hCenter : Subgroup.center X = ⊥)
    (ModularCharacterTriple :
      IBr iota → WeightClass (p := 3) (K := K) (X := X) → Prop) : Prop where
  characterTriple_of_sector_and_stabilizer_eq :
    ∀ (phi : IBr iota)
      (w : WeightClass (p := 3) (K := K) (X := X)),
      weightSector (R := R) w = brauerSector iota hinj blocks phi →
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi =
        MulAction.stabilizer (MulAut X)ᵐᵒᵖ w →
      ModularCharacterTriple phi w

/-- Literal block preservation implies equality of the corresponding central
sectors. -/
theorem same_sector_of_block_preserving
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hblock : ∀ phi,
      R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi)
    (phi : IBr iota) :
    weightSector (R := R) (Omega phi) =
      brauerSector iota hinj blocks phi := by
  unfold weightSector brauerSector
  rw [hblock phi]

omit [Invertible (Fintype.card (Subgroup.center X) : k)] in
/-- A fully equivariant equivalence identifies the automorphism stabilisers of
each matched character and weight. -/
theorem matched_stabilizers
    (Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      Omega (alpha • phi) = alpha • Omega phi)
    (phi : IBr iota) :
    MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi =
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ (Omega phi) :=
  Formalisation.stabilizer_eq_of_injective_equivariant
    Omega.injective hOmega phi

/-- The three block equivalence retains the modular character triple condition
after the exact external implication has been supplied.  The sector and
stabiliser equalities are kernel deductions. -/
theorem exists_threeBlockAutEquivariantEquiv_retaining_characterTriples
    (ModularCharacterTriple :
      IBr iota → WeightClass (p := 3) (K := K) (X := X) → Prop)
    (hCenter : Subgroup.center X = ⊥)
    (TripleSource : CharacterTripleRetentionSource
      (R := R) iota hinj blocks hCenter ModularCharacterTriple)
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (OuterSource : C2OuterActionSource iota S) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      (∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
        Omega (alpha • phi) = alpha • Omega phi) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) = brauerBlock iota hinj blocks phi) ∧
      (∀ phi,
        weightSector (R := R) (Omega phi) =
          brauerSector iota hinj blocks phi) ∧
      (∀ phi,
        MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi =
          MulAction.stabilizer (MulAut X)ᵐᵒᵖ (Omega phi)) ∧
      (∀ phi, ModularCharacterTriple phi (Omega phi)) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.nonprincipalBlock,
        Omega phi.1 = (Known.nonprincipal phi).1) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.defectZeroBlock,
        Omega phi.1 = (Known.defectZero phi).1) := by
  obtain ⟨Omega, hOmega, hblock, hnonprincipal, hdefectZero⟩ :=
    exists_threeBlockAutEquivariantEquiv
      (R := R) iota hinj blocks E1 F S Known OuterSource
  have hsector : ∀ phi,
      weightSector (R := R) (Omega phi) =
        brauerSector iota hinj blocks phi :=
    same_sector_of_block_preserving iota hinj blocks Omega hblock
  have hstabilizer : ∀ phi,
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ phi =
        MulAction.stabilizer (MulAut X)ᵐᵒᵖ (Omega phi) :=
    matched_stabilizers iota Omega hOmega
  refine ⟨Omega, hOmega, hblock, hsector, hstabilizer, ?_,
    hnonprincipal, hdefectZero⟩
  intro phi
  exact TripleSource.characterTriple_of_sector_and_stabilizer_eq
    phi (Omega phi) (hsector phi) (hstabilizer phi)

end ModularRep.PaperProofs.SporadicFi24ThreeBlockCharacterTripleRetentionActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
