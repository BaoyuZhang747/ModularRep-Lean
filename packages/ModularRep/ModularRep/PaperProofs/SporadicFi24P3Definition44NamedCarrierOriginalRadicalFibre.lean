import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps

/-! The actual Brauer partition and the identification of its local ordinary
maps with a retained centreless family. No second family is constructed. -/

noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalRadicalFibre

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierSmallCenterFamilyMaps
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCenterlessReferenceMap
open SporadicFi24P3Definition44NamedCarrierFaithfulOrdinaryMaps (BrauerAtSectorRadical)
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))

def originalPart (q : RadicalConjugacyClass (p := p) (G := G)) : Set (IBr iota) :=
  {phi | radicalClass (Omega phi) = q}

theorem originalPart_cover : (⋃ q, originalPart iota Omega q) = Set.univ := by
  ext phi
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨radicalClass (Omega phi), rfl⟩

theorem originalPart_disjoint : Pairwise (fun q r =>
    Disjoint (originalPart iota Omega q) (originalPart iota Omega r)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro phi hq hr
  exact hqr (hq.symm.trans hr)

theorem originalPart_covariance
    (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (a : (MulAut G)ᵐᵒᵖ) (q : RadicalConjugacyClass (p := p) (G := G)) :
    (fun phi : IBr iota => a • phi) '' originalPart iota Omega q =
      originalPart iota Omega (a • q) := by
  ext phi
  constructor
  · rintro ⟨psi, hpsi, rfl⟩
    change radicalClass (Omega psi) = q at hpsi
    change radicalClass (Omega (a • psi)) = a • q
    rw [hOmega, radicalClass_equivariant, hpsi]
  · intro hphi
    refine ⟨a⁻¹ • phi, ?_, smul_inv_smul a phi⟩
    change radicalClass (Omega (a⁻¹ • phi)) = q
    rw [hOmega, radicalClass_equivariant]
    change radicalClass (Omega phi) = a • q at hphi
    rw [hphi, inv_smul_smul]

variable {Block : Type u} [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1

/-- Both directions preserve the actual Brauer character. -/
def originalRadicalEquiv (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (hlink : ∀ phi : FB, (e phi).val = Omega phi.val)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G)) :
    BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃
      SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.BrauerAtRadical iota Omega Q where
  toFun phi := ⟨phi.val.val,
    (congrArg radicalClass (hlink phi.val)).symm.trans phi.property.2⟩
  invFun psi := ⟨centerlessLift iota hinj blocks R E1 hcenter psi.val,
    centerlessSector_unique hcenter _ _,
    (congrArg radicalClass
      (hlink (centerlessLift iota hinj blocks R E1 hcenter psi.val))).trans psi.property⟩
  left_inv phi := by
    apply Subtype.ext
    exact faithfulIBr_val_injective iota hinj blocks R E1 rfl
  right_inv psi := Subtype.ext rfl

/-- Uniqueness in the actual representative fibre identifies the retained
ordinary value, not just its global conjugacy class. -/
theorem original_localMap_eq_retained (hcenter : Subgroup.center G = ⊥)
    (e : FB ≃ FW) (hlink : ∀ phi : FB, (e phi).val = Omega phi.val)
    (L : ∀ (nu : S) (Q : RadicalSubgroup (p := p) (G := G)),
      BrauerAtSectorRadical iota hinj blocks R E1 e nu Q ≃ RootSectorLocal iota nu.val Q)
    (hclass : ∀ nu Q phi, classAt iota.prime Q (L nu Q phi).val = (e phi.val).val)
    (nu : S) (Q : RadicalSubgroup (p := p) (G := G))
    (phi : BrauerAtSectorRadical iota hinj blocks R E1 e nu Q) :
    SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap iota Omega iota.prime Q
      (originalRadicalEquiv iota Omega hinj blocks R E1 hcenter e hlink nu Q phi) =
      (L nu Q phi).val := by
  apply classAt_injective iota.prime Q
  exact (SporadicFi24P3Definition44NamedCarrierRepresentativeMaps.localMap_class
    iota Omega iota.prime Q
    (originalRadicalEquiv iota Omega hinj blocks R E1 hcenter e hlink nu Q phi)).trans
      ((hlink phi.val).symm.trans (hclass nu Q phi).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalRadicalFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
