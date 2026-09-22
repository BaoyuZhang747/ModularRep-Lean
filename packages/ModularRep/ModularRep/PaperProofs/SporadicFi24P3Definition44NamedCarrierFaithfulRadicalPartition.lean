import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily

/-! The actual faithful-sector fibres of the retained correspondence.
All radical conjugacy classes remain indexed, including empty fibres.
These are the disjoint-union assertions of Spath 4.1(i); equality of two
empty parts does not determine their labels. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulRadicalPartition

open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily

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
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "RC" => RadicalClass (p := p) (X := G)
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1

def label (e : FB ≃ FW) (phi : FB) : S × RC :=
  (pX phi, radicalPart iota hinj blocks R E1 e phi)

def part (e : FB ≃ FW) (j : S × RC) : Set FB :=
  {phi | label iota hinj blocks R E1 e phi = j}

theorem mem_part_iff (e : FB ≃ FW) (nu : S) (q : RC) (phi : FB) :
    phi ∈ part iota hinj blocks R E1 e (nu, q) ↔
      pX phi = nu ∧ radicalPart iota hinj blocks R E1 e phi = q := by
  simp only [part, label, Set.mem_ofPred_eq, Prod.mk.injEq]

theorem part_cover (e : FB ≃ FW) :
    (⋃ j, part iota hinj blocks R E1 e j) = Set.univ := by
  ext phi
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨label iota hinj blocks R E1 e phi, rfl⟩

theorem part_sector_union (e : FB ≃ FW) (nu : S) :
    (⋃ q, part iota hinj blocks R E1 e (nu, q)) = {phi | pX phi = nu} := by
  ext phi
  simp only [Set.mem_iUnion, mem_part_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hnu, _⟩
    exact hnu
  · intro hnu
    exact ⟨radicalPart iota hinj blocks R E1 e phi, hnu, rfl⟩

theorem part_pairwise_disjoint (e : FB ≃ FW) :
    Pairwise (fun i j => Disjoint
      (part iota hinj blocks R E1 e i) (part iota hinj blocks R E1 e j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro phi hi hj
  exact hij (hi.symm.trans hj)

theorem part_eq_iff (e : FB ≃ FW) (i j : S × RC) :
    part iota hinj blocks R E1 e i = part iota hinj blocks R E1 e j ↔
      i = j ∨ (part iota hinj blocks R E1 e i = ∅ ∧
        part iota hinj blocks R E1 e j = ∅) := by
  constructor
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · have hi : part iota hinj blocks R E1 e i = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro phi hphi
        have hj : phi ∈ part iota hinj blocks R E1 e j := h ▸ hphi
        exact hij (hphi.symm.trans hj)
      exact Or.inr ⟨hi, h.symm.trans hi⟩
  · rintro (hij | ⟨hi, hj⟩)
    · rw [hij]
    · exact hi.trans hj.symm

def supportedIndices (e : FB ≃ FW) : Set (S × RC) :=
  {j | (part iota hinj blocks R E1 e j).Nonempty}

theorem supported_part_injective (e : FB ≃ FW) :
    Function.Injective (fun j : supportedIndices iota hinj blocks R E1 e =>
      part iota hinj blocks R E1 e j.val) := by
  intro i j h
  apply Subtype.ext
  obtain ⟨phi, hphi⟩ := i.property
  have hj : phi ∈ part iota hinj blocks R E1 e j.val := by
    change part iota hinj blocks R E1 e i.val = part iota hinj blocks R E1 e j.val at h
    rw [← h]
    exact hphi
  exact hphi.symm.trans hj

theorem supported_part_cover (e : FB ≃ FW) :
    (⋃ j : supportedIndices iota hinj blocks R E1 e,
      part iota hinj blocks R E1 e j.val) = Set.univ := by
  ext phi
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨⟨label iota hinj blocks R E1 e phi, phi, rfl⟩, rfl⟩

theorem label_equivariant (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e) (a : A) (phi : FB) :
    label iota hinj blocks R E1 e (a • phi) =
      a • label iota hinj blocks R E1 e phi := by
  apply Prod.ext
  · exact brauerProjection_equivariant iota hinj blocks R E1 a phi
  · exact hFamily.2.2.2.2.1 a phi

theorem part_covariance (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e) (a : A) (j : S × RC) :
    (fun phi : FB => a • phi) '' part iota hinj blocks R E1 e j =
      part iota hinj blocks R E1 e (a • j) := by
  ext phi
  constructor
  · rintro ⟨psi, hpsi, rfl⟩
    change label iota hinj blocks R E1 e (a • psi) = a • j
    rw [label_equivariant iota hinj blocks R E1 e hFamily]
    exact congrArg (fun x : S × RC => a • x) hpsi
  · intro hphi
    refine ⟨a⁻¹ • phi, ?_, smul_inv_smul a phi⟩
    change label iota hinj blocks R E1 e (a⁻¹ • phi) = j
    rw [label_equivariant iota hinj blocks R E1 e hFamily]
    change label iota hinj blocks R E1 e phi = a • j at hphi
    rw [hphi, inv_smul_smul]

theorem supported_iff_twist (e : FB ≃ FW)
    (hFamily : FamilyProperties iota hinj blocks R E1 e) (a : A) (j : S × RC) :
    (part iota hinj blocks R E1 e (a • j)).Nonempty ↔
      (part iota hinj blocks R E1 e j).Nonempty := by
  rw [← part_covariance iota hinj blocks R E1 e hFamily]
  exact Set.image_nonempty

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulRadicalPartition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
