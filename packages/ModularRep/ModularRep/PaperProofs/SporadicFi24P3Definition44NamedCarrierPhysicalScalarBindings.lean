import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalCentralSector

/-! The actual specified Brauer and raw-weight sectors give the scalar laws
on the retained chosen global and canonical local representations. The
local binding uses the original reduction and lower block compatibility;
no scalar equality for a matched pair is supplied as an input. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

open ModularRep ModularRep.FDRepSimpleClassKZero
open EvenFieldFLZBAWGoodFamily
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierLocalCentralSector
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)

theorem brauerSector_scalar (phi : IBr iota) (z : Subgroup.center G) :
    (chosenIBrRepresentation iota phi).ρ z.1 =
      (brauerSector iota hinj blocks phi z : k) • 1 := by
  let W := chosenIBrRepresentation iota phi
  let : Representation.IsIrreducible W.ρ := (Classical.choose_spec phi.2).1
  have hs : brauerSector iota hinj blocks phi =
      Representation.centralCharacter W.ρ (Subgroup.center G) le_rfl := by
    exact Representation.primitiveCentralIdempotentSector_eq_centralCharacter W.ρ
      (Subgroup.center G) le_rfl
      (blocks.primitive (irreducibleBrauerCharacterBlock iota hinj blocks phi))
      (block_smul_of_affording iota hinj blocks phi W
        inferInstance (chosenIBrRepresentation_character iota phi))
  rw [hs]
  exact Representation.centralCharacter_spec W.ρ (Subgroup.center G) le_rfl z

def scalarBrauer (phi : IBr iota) :
    ScalarBrauerSector iota (brauerSector iota hinj blocks phi) :=
  ⟨phi, brauerSector_scalar iota hinj blocks phi⟩

theorem scalarBrauer_val (phi : IBr iota) :
    (scalarBrauer iota hinj blocks phi).1 = phi := rfl

variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))

theorem rawWeightSector_scalar
    (V : CharacterWeight p K G) (source : CanonicalRawReduction iota V)
    (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)
    (nu : Subgroup.center G →* kˣ)
    (hsector : weightSector (R := R)
      (Quotient.mk'' (Quotient.mk'' V) : CharacterWeight.ConjugacyClass) = nu)
    (z : Subgroup.center G) :
    (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
      (Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z) =
        (nu z : k) • 1 := by
  let N := Subgroup.normalizer (V.subgroup : Set G)
  let rho := (chosenIBrRepresentation source.normalizerRoot source.localBrauer).ρ
  let : Representation.IsIrreducible rho := (Classical.choose_spec source.localBrauer.2).1
  let zN : N := Subgroup.inclusion (Subgroup.center_le_normalizer (V.subgroup : Set G)) z
  let zZN : (Subgroup.center G).subgroupOf N := ⟨zN, z.2⟩
  have hs := rawWeightBlock_local_centralCharacter iota R V source compatibility
  have hv := DFunLike.congr_fun hs zZN
  have hraw : blockSector (k := k) (X := G) (R.1.operations.rawWeightBlock V) = nu := hsector
  change Representation.centralCharacter rho ((Subgroup.center G).subgroupOf N)
    (subgroupOf_le_center N (Subgroup.center G) le_rfl) zZN =
      blockSector (k := k) (X := G) (R.1.operations.rawWeightBlock V) z at hv
  rw [hraw] at hv
  have hscalar := Representation.centralCharacter_spec rho ((Subgroup.center G).subgroupOf N)
    (subgroupOf_le_center N (Subgroup.center G) le_rfl) zZN
  rw [hv] at hscalar
  exact hscalar

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
