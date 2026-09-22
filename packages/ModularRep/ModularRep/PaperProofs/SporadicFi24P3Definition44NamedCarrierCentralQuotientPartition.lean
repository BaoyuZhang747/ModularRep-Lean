import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

/-! The actual all-radical partition of the transported correspondence.
Its quotient parts and moving-radical action are derived, retaining empty parts. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientPartition

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientSectorAction
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightAssembly
open SporadicFi24P3Definition44NamedCarrierCentralQuotientWeightTransport
open SporadicFi24P3Definition44NamedCarrierCentralQuotientRadicalLabels
open SporadicFi24P3Definition44NamedCarrierCentralQuotientOrdinaryMaps
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)

local notation "BF" => trivialBrauerFibre iota R Z hcentral
local notation "RC" => RadicalConjugacyClass (p := p) (G := X)

def part (eU : BF ≃ SectorWeights R Z) (c : RC) : Set BF :=
  {phi | radicalClass (eU phi).val = c}

def quotientPart (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (c : RadicalConjugacyClass (p := p) (G := X ⧸ Z)) : Set (IBr (quotientRoot iota Z)) :=
  {psi | radicalClass (eD psi) = c}

omit [Z.Normal] in
theorem part_cover (eU : BF ≃ SectorWeights R Z) :
    (⋃ c, part iota R Z hcentral eU c) = Set.univ := by
  ext phi
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨radicalClass (eU phi).val, rfl⟩

omit [Z.Normal] in
theorem part_pairwise_disjoint (eU : BF ≃ SectorWeights R Z) :
    Pairwise (fun c d => Disjoint (part iota R Z hcentral eU c) (part iota R Z hcentral eU d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro phi hc hd
  exact hcd (hc.symm.trans hd)

omit [Z.Normal] in
theorem part_eq_iff (eU : BF ≃ SectorWeights R Z) (c d : RC) :
    part iota R Z hcentral eU c = part iota R Z hcentral eU d ↔
      c = d ∨ (part iota R Z hcentral eU c = ∅ ∧ part iota R Z hcentral eU d = ∅) := by
  constructor
  · intro h
    by_cases hcd : c = d
    · exact Or.inl hcd
    · have hc : part iota R Z hcentral eU c = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro phi hphi
        have hd : phi ∈ part iota R Z hcentral eU d := h ▸ hphi
        exact hcd (hphi.symm.trans hd)
      exact Or.inr ⟨hc, h.symm.trans hc⟩
  · rintro (hcd | ⟨hc, hd⟩)
    · rw [hcd]
    · exact hc.trans hd.symm

omit [Z.Normal] in
theorem part_support_iff (eU : BF ≃ SectorWeights R Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    (part iota R Z hcentral eU (Quotient.mk'' Q)).Nonempty ↔
      Nonempty (localOrdinaryRows iota R Z Q) := by
  constructor
  · rintro ⟨phi, hphi⟩
    exact ⟨localOrdinaryEquiv iota R Z hcentral eU Q ⟨phi, hphi⟩⟩
  · rintro ⟨theta⟩
    let phi := (localOrdinaryEquiv iota R Z hcentral eU Q).symm theta
    exact ⟨phi.val, phi.property⟩

variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ (Q : RadicalSubgroup (p := p) (G := X))
    (theta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ (Q : RadicalSubgroup (p := p) (G := X ⧸ Z))
    (eta : LocalDefectZeroCharacter (K := K) Q),
  CanonicalRawReduction (quotientRoot iota Z) (characterWeightAt iota.prime Q eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : ∀ Q : RadicalSubgroup (p := p) (G := X),
  CentralPrimeToPrimitiveImageSource (k := k)
    (normalizerMap (QuotientGroup.mk' Z) Q.1)
    (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
    (fixedNormalizer_kernel_central Z Q.1 hcentral)
    (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))


local notation "EU" => transportedUp iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
local notation "ER" => quotientRadicalEquiv iota Z hcentral hprimeTo

theorem transportedUp_radicalLabel (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z)) (phi : BF) :
    ER (radicalClass (EU eD phi).val) =
      radicalClass (eD ((canonicalBrauerEquiv iota R Z hcentral).symm phi)) :=
  (sectorToQuotient_radicalClass iota R Z hcentral hprimeTo OD CU CD compatU compatD
    Sglobal Slocal (EU eD phi)).symm.trans
      (congrArg radicalClass (transportedUp_square iota R Z hcentral hprimeTo OD CU CD
        compatU compatD Sglobal Slocal eD phi))

theorem part_quotient_iff (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z)) (c : RC) (phi : BF) :
    phi ∈ part iota R Z hcentral (EU eD) c ↔
      (canonicalBrauerEquiv iota R Z hcentral).symm phi ∈ quotientPart iota Z eD (ER c) := by
  have hlabel := transportedUp_radicalLabel iota R Z hcentral hprimeTo OD CU CD
    compatU compatD Sglobal Slocal eD phi
  constructor
  · intro h
    exact hlabel.symm.trans (congrArg (ER) h)
  · intro h
    exact (ER).injective (hlabel.trans h)

theorem part_covariance_preimage (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (hD : ∀ psi : IBr (quotientRoot iota Z),
      eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) = MulOpposite.op beta • eD psi)
    (c : RC) :
    (brauerSectorTwist iota R Z hcentral alpha beta square) ⁻¹'
      part iota R Z hcentral (EU eD) (MulOpposite.op alpha • c) =
        part iota R Z hcentral (EU eD) c := by
  ext phi
  change radicalClass (EU eD (brauerSectorTwist iota R Z hcentral alpha beta square phi)).val =
      MulOpposite.op alpha • c ↔ radicalClass (EU eD phi).val = c
  rw [transportedUp_covariance iota R Z hcentral hprimeTo OD CU CD compatU compatD Sglobal Slocal
    eD alpha beta square hD phi]
  change radicalClass (MulOpposite.op alpha • (EU eD phi).val) = MulOpposite.op alpha • c ↔ _
  rw [radicalClass_equivariant]
  exact (MulAction.injective (MulOpposite.op alpha)).eq_iff

theorem part_covariance (eD : IBr (quotientRoot iota Z) ≃
    ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (square : ∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x))
    (hD : ∀ psi : IBr (quotientRoot iota Z),
      eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) = MulOpposite.op beta • eD psi)
    (c : RC) :
    (brauerSectorTwist iota R Z hcentral alpha beta square) '' part iota R Z hcentral (EU eD) c =
      part iota R Z hcentral (EU eD) (MulOpposite.op alpha • c) := by
  let TB := brauerSectorTwist iota R Z hcentral alpha beta square
  have heq := part_covariance_preimage iota R Z hcentral hprimeTo OD CU CD compatU compatD
    Sglobal Slocal eD alpha beta square hD c
  have hiff (phi : BF) : TB phi ∈ part iota R Z hcentral (EU eD) (MulOpposite.op alpha • c) ↔
      phi ∈ part iota R Z hcentral (EU eD) c := by
    change phi ∈ TB ⁻¹' part iota R Z hcentral (EU eD) (MulOpposite.op alpha • c) ↔ _
    rw [heq]
  ext phi
  constructor
  · rintro ⟨psi, hpsi, rfl⟩
    exact (hiff psi).mpr hpsi
  · intro hphi
    refine ⟨TB.symm phi, (hiff (TB.symm phi)).mp ?_, TB.apply_symm_apply phi⟩
    simpa only [TB.apply_symm_apply] using hphi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientPartition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
