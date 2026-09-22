import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

/-! Restrict the same faithful-family equivalence to the original scalar
sector, or to all original Brauer characters when the centre is trivial.
Equivariance and the original raw match are consequences of these maps. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps

open ModularRep ModularRep.FDRepSimpleClassKZero
open EvenFieldFLZBAWGoodFamily
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierCentralTwoEquivariantMatch
open SporadicFi24P3Definition44NamedCarrierPhysicalScalarBindings

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
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)

local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1

theorem scalarBrauer_sector_eq (nu : Subgroup.center G →* kˣ)
    (chi : ScalarBrauerSector iota nu) :
    brauerSector iota hinj blocks chi.1 = nu := by
  let rho := (chosenIBrRepresentation iota chi.1).ρ
  let : Representation.IsIrreducible rho := (Classical.choose_spec chi.1.2).1
  exact (Representation.existsUnique_centralCharacter rho (Subgroup.center G) le_rfl).unique
    (brauerSector_scalar iota hinj blocks chi.1) chi.2

theorem faithfulIBr_val_injective : Function.Injective (fun x : FB => x.val) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  cases h
  rfl

def scalarLift (nu : Subgroup.center G →* kˣ) (hnu : Function.Injective nu)
    (chi : ScalarBrauerSector iota nu) : FB :=
  ⟨chi.1, by rw [scalarBrauer_sector_eq iota hinj blocks nu chi]; exact hnu⟩

def scalarOmega (nu : Subgroup.center G →* kˣ) (hnu : Function.Injective nu)
    (e : FB ≃ FW) (chi : ScalarBrauerSector iota nu) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  (e (scalarLift iota hinj blocks R E1 nu hnu chi)).val

theorem scalarOmega_equivariant
    (nu : Subgroup.center G →* kˣ) (hnu : Function.Injective nu)
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (a : A) (chi chi' : ScalarBrauerSector iota nu) (hchi : chi'.1 = a • chi.1) :
    scalarOmega iota hinj blocks R E1 nu hnu e chi' =
      a • scalarOmega iota hinj blocks R E1 nu hnu e chi := by
  have ht : scalarLift iota hinj blocks R E1 nu hnu chi' =
      a • scalarLift iota hinj blocks R E1 nu hnu chi :=
    faithfulIBr_val_injective iota hinj blocks R E1 hchi
  change (e (scalarLift iota hinj blocks R E1 nu hnu chi')).val =
    (a • e (scalarLift iota hinj blocks R E1 nu hnu chi)).val
  rw [ht, he]

theorem scalarOmega_at_original (e : FB ≃ FW) (phi : FB) :
    scalarOmega iota hinj blocks R E1 (brauerSector iota hinj blocks phi.val)
      phi.faithful e (scalarBrauer iota hinj blocks phi.val) = (e phi).val := by
  have hback : scalarLift iota hinj blocks R E1 (brauerSector iota hinj blocks phi.val)
      phi.faithful (scalarBrauer iota hinj blocks phi.val) = phi :=
    faithfulIBr_val_injective iota hinj blocks R E1 rfl
  change (e (scalarLift iota hinj blocks R E1 _ _ _)).val = _
  rw [hback]

def centerlessLift (hcenter : Subgroup.center G = ⊥) (chi : IBr iota) : FB :=
  ⟨chi, by
    have : Subsingleton (Subgroup.center G) := by rw [hcenter]; infer_instance
    exact fun _ _ _ => Subsingleton.elim _ _⟩

def centerlessOmega (hcenter : Subgroup.center G = ⊥) (e : FB ≃ FW)
    (chi : IBr iota) : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  (e (centerlessLift iota hinj blocks R E1 hcenter chi)).val

theorem centerlessOmega_equivariant (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (he : ∀ (a : A) (x : FB), e (a • x) = a • e x)
    (a : A) (chi : IBr iota) :
    centerlessOmega iota hinj blocks R E1 hcenter e (a • chi) =
      a • centerlessOmega iota hinj blocks R E1 hcenter e chi := by
  have ht : centerlessLift iota hinj blocks R E1 hcenter (a • chi) =
      a • centerlessLift iota hinj blocks R E1 hcenter chi :=
    faithfulIBr_val_injective iota hinj blocks R E1 rfl
  change (e (centerlessLift iota hinj blocks R E1 hcenter (a • chi))).val =
    (a • e (centerlessLift iota hinj blocks R E1 hcenter chi)).val
  rw [ht, he]

theorem centerlessOmega_at_original (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (phi : FB) :
    centerlessOmega iota hinj blocks R E1 hcenter e phi.val = (e phi).val := by
  have hback : centerlessLift iota hinj blocks R E1 hcenter phi.val = phi :=
    faithfulIBr_val_injective iota hinj blocks R E1 rfl
  change (e (centerlessLift iota hinj blocks R E1 hcenter phi.val)).val = _
  rw [hback]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
