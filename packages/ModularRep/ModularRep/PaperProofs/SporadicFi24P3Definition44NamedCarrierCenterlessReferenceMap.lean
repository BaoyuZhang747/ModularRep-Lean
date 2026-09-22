import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction

/-! A centreless reference fibre is the entire specified carrier. Restrict
the same constructed correspondence; all reference laws follow from it. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap

open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierSameFamilyBlockInduction
open SporadicFi24P3Definition44NamedCarrierAllPairs

universe u
variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1
local notation "hpX" => brauerProjection_equivariant iota hinj blocks R E1
local notation "hpY" => weightProjection_equivariant iota hinj blocks R E1

omit [Fintype G] [IsAlgClosed k] [Invertible (Fintype.card (Subgroup.center G) : k)] in
theorem centerlessSector_unique (hcenter : Subgroup.center G = ⊥)
    (nu mu : S) : nu = mu := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro z
  have hz : z = 1 := by
    apply Subtype.ext
    exact Subgroup.mem_bot.mp (hcenter ▸ z.property)
  simp only [hz, map_one]

def centerlessReferenceSector (hcenter : Subgroup.center G = ⊥) : S := by
  have : Subsingleton (Subgroup.center G) := by rw [hcenter]; infer_instance
  exact ⟨1, fun _ _ _ => Subsingleton.elim _ _⟩

def centerlessReferenceBrauerEquiv (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) : Fibre pX nu0 ≃ IBr iota where
  toFun x := x.val.val
  invFun phi := ⟨centerlessLift iota hinj blocks R E1 hcenter phi,
    centerlessSector_unique hcenter _ _⟩
  left_inv x := by
    apply Subtype.ext
    exact faithfulIBr_val_injective iota hinj blocks R E1 rfl
  right_inv phi := rfl

def centerlessReferenceWeightEquiv (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) : Fibre pY nu0 ≃ WeightClass (p := p) (K := K) (X := G) where
  toFun x := x.val.val
  invFun w := ⟨⟨w, by
    have : Subsingleton (Subgroup.center G) := by rw [hcenter]; infer_instance
    exact fun _ _ _ => Subsingleton.elim _ _⟩,
    centerlessSector_unique hcenter _ _⟩
  left_inv x := by
    apply Subtype.ext
    cases x with
    | mk w hw => cases w; rfl
  right_inv w := rfl

def centerlessReferenceEquiv (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := G)) :
    Fibre pX nu0 ≃ Fibre pY nu0 :=
  (centerlessReferenceBrauerEquiv iota hinj blocks R E1 hcenter nu0).trans
    (Omega.trans (centerlessReferenceWeightEquiv iota hinj blocks R E1 hcenter nu0).symm)

theorem centerlessReferenceEquiv_apply (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := G))
    (x : Fibre pX nu0) :
    (centerlessReferenceEquiv iota hinj blocks R E1 hcenter nu0 Omega x).val.val =
      Omega x.val.val := rfl

theorem centerlessReferenceEquiv_block (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := G))
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi) :
    BaseBlockPreserving iota hinj R blocks E1 nu0
      (centerlessReferenceEquiv iota hinj blocks R E1 hcenter nu0 Omega) :=
  fun x => hblock x.val.val

theorem centerlessReferenceEquiv_equivariant (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := G))
    (hOmega : ∀ (a : A) (phi : IBr iota), Omega (a • phi) = a • Omega phi) :
    ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      centerlessReferenceEquiv iota hinj blocks R E1 hcenter nu0 Omega
          (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha
          (centerlessReferenceEquiv iota hinj blocks R E1 hcenter nu0 Omega x) := by
  intro a ha x
  apply (centerlessReferenceWeightEquiv iota hinj blocks R E1 hcenter nu0).injective
  change Omega (a • x.val.val) = a • Omega x.val.val
  exact hOmega a x.val.val

theorem centerlessTransportedEquiv_val (hcenter : Subgroup.center G = ⊥)
    (nu0 : S) (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := G))
    (hOmega : ∀ (a : A) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (t : S → A) (ht : ∀ nu, t nu • nu0 = nu)
    (phi : FaithfulIBr iota hinj blocks R E1) :
    (transportedEquivalence iota hinj blocks R E1 nu0 t ht
      (centerlessReferenceEquiv iota hinj blocks R E1 hcenter nu0 Omega) phi).val =
        Omega phi.val := by
  change t (pX phi) • Omega ((t (pX phi))⁻¹ • phi.val) = Omega phi.val
  rw [hOmega]
  exact smul_inv_smul _ _

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
