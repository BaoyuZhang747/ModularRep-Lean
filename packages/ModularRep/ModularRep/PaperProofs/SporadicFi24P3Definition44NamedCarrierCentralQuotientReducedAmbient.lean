import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre

/-! The reduced ambient realizes the original character stabilizer.
Prime-to-p quotient transport also reflects the trivial radical. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAmbient

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZ318FixedTheoremGate
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToPSubgroups
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre

universe u

theorem pSubgroup_map_eq_bot_iff {p : ℕ} (hp : p.Prime)
    {G H : Type u} [Group G] [Group H] (f : G →* H)
    (hk : ¬ p ∣ Nat.card f.ker) (Q : Subgroup G) (hQ : IsPGroup p Q) :
    Q.map f = ⊥ ↔ Q = ⊥ := by
  constructor
  · intro h
    apply bot_unique
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply injOn_pSubgroup_of_primeTo_ker hp f hk Q hQ hx Q.one_mem
    have hfx : f x ∈ Q.map f := ⟨x, hx, rfl⟩
    rw [h] at hfx
    exact (Subgroup.mem_bot.mp hfx).trans (map_one f).symm
  · rintro rfl
    simp

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] :
    Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X)

omit [CharP k p] [IsAlgClosed k] [CharZero K] in
theorem fixedRadicalImage_eq_bot_iff (hprimeTo : ¬ p ∣ Nat.card Z)
    (Q : RadicalSubgroup (p := p) (G := X)) :
    (fixedRadicalImage iota Z hcentral hprimeTo Q).val = ⊥ ↔ Q.val = ⊥ := by
  change Q.val.map (QuotientGroup.mk' Z) = ⊥ ↔ Q.val = ⊥
  exact pSubgroup_map_eq_bot_iff iota.prime (QuotientGroup.mk' Z)
    (by simpa only [QuotientGroup.ker_mk'] using hprimeTo) Q.val Q.property.isPGroup

variable [Invertible (Fintype.card Z : k)]
variable (hfull : Z = Subgroup.center X)
variable (hq : IsUniversalCentralExtension (QuotientGroup.mk' Z))
variable (phi : trivialBrauerFibre iota R Z hcentral)

local notation "rD" => quotientRoot iota Z
local notation "psiD" => Equiv.symm (canonicalBrauerEquiv iota R Z hcentral) phi
local notation "A" => ActualAutAmbient rD psiD
local notation "B" => actualBase rD psiD
local notation "C" => Subgroup.centralizer (B : Set A)

def reducedCentralizerQuotientEquiv : A ⧸ C ≃* ActualAutAmbient iota phi.val :=
  ((QuotientGroup.quotientMulEquivOfEq
      (actualBase_centralizer_eq_bot rD psiD (quotientCenter_eq_bot Z hfull hq))).trans
    QuotientGroup.quotientBot).trans
      (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi).symm

theorem reducedCentralizerQuotientEquiv_mk (a : A) :
    reducedCentralizerQuotientEquiv iota R Z hcentral hfull hq phi
      (QuotientGroup.mk' C a) =
        (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi).symm a := by
  change (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi).symm
    (QuotientGroup.quotientBot
      (QuotientGroup.quotientMulEquivOfEq
        (actualBase_centralizer_eq_bot rD psiD (quotientCenter_eq_bot Z hfull hq))
        (QuotientGroup.mk a))) = _
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem reducedCentralizerQuotientEquiv_action (a : A) :
    fullCenterAutEquiv Z hfull hq
      (actualConjugation iota phi.val
        (reducedCentralizerQuotientEquiv iota R Z hcentral hfull hq phi
          (QuotientGroup.mk' C a))) = actualConjugation rD psiD a := by
  rw [reducedCentralizerQuotientEquiv_mk]
  have h := fullCenterBrauerStabilizerEquiv_action iota R Z hcentral hfull hq phi
    ((fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi).symm a)
  simpa only [MulEquiv.apply_symm_apply] using h.symm

include hfull hq in
theorem reduced_centralizer_eq_center : C = Subgroup.center A := by
  rw [actualBase_centralizer_eq_bot rD psiD (quotientCenter_eq_bot Z hfull hq),
    actualAmbient_center_eq_bot rD psiD (quotientCenter_eq_bot Z hfull hq)]

include hfull hq in
theorem reduced_center_primeTo : ¬ p ∣ Nat.card (Subgroup.center A) := by
  rw [actualAmbient_center_eq_bot rD psiD (quotientCenter_eq_bot Z hfull hq), Subgroup.card_bot]
  exact iota.prime.not_dvd_one

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAmbient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
