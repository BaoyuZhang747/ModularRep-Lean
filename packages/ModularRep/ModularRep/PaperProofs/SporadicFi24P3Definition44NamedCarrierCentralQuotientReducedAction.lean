import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

/-! Actual full-cover automorphisms and the retained Brauer stabilizers.
Universality supplies lifting; centrality alone is not used for that claim. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZ318FixedTheoremGate
open SporadicFi24P3Definition44NamedCarrierFullCoverGroupFacts
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFullCoverAutomorphismEquiv
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralQuotientBrauerCorrespondence
open SporadicFi24P3Definition44NamedCarrierCentralQuotientCorrespondenceAction

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite _
local instance quotientFintype (H : Subgroup X) [H.Normal] : Fintype (X ⧸ H) := Fintype.ofFinite _
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal] [Invertible (Fintype.card Z : k)]
variable (hcentral : Z ≤ Subgroup.center X) (hfull : Z = Subgroup.center X)
variable (hq : IsUniversalCentralExtension (QuotientGroup.mk' Z))

def fullCenterAutEquiv : MulAut X ≃* MulAut (X ⧸ Z) :=
  fullCoverAutEquiv (QuotientGroup.mk' Z) hq ((QuotientGroup.ker_mk' Z).trans hfull)

include hfull hq in
omit [Fintype X] in
theorem quotientCenter_eq_bot : Subgroup.center (X ⧸ Z) = ⊥ := by
  let _ : Group.IsPerfect X := ⟨perfect_of_universalCentralExtension (QuotientGroup.mk' Z) hq⟩
  subst Z
  exact Group.IsPerfect.center_quotient_center_eq_bot X

local notation "E" => fullCenterAutEquiv Z hfull hq
local notation "EB" => canonicalBrauerEquiv iota R Z hcentral
local notation "BF" => trivialBrauerFibre iota R Z hcentral

omit [Fintype X] in
theorem fullCenterAutEquiv_square (alpha : MulAut X) (x : X) :
    E alpha (QuotientGroup.mk' Z x) = QuotientGroup.mk' Z (alpha x) :=
  fullCoverAutEquiv_apply_q (QuotientGroup.mk' Z) hq
    ((QuotientGroup.ker_mk' Z).trans hfull) alpha x

omit [Fintype X] in
theorem fullCenterAutEquiv_lift_square (beta : MulAut (X ⧸ Z)) (x : X) :
    QuotientGroup.mk' Z ((E).symm beta x) = beta (QuotientGroup.mk' Z x) :=
  fullCoverAutEquiv_symm_apply_q (QuotientGroup.mk' Z) hq
    ((QuotientGroup.ker_mk' Z).trans hfull) beta x

theorem fullCenterBrauer_fixed_iff (phi : BF) (alpha : MulAut X) :
    MulOpposite.op alpha • phi.val = phi.val ↔
      MulOpposite.op (E alpha) • (EB).symm phi = (EB).symm phi := by
  let square (x : X) : QuotientGroup.mk' Z (alpha x) = E alpha (QuotientGroup.mk' Z x) :=
    (fullCenterAutEquiv_square Z hfull hq alpha x).symm
  let TB := brauerSectorTwist iota R Z hcentral alpha (E alpha) square
  have hc := canonicalBrauerEquiv_symm_covariance iota R Z hcentral alpha (E alpha) square phi
  change (EB).symm (TB phi) = MulOpposite.op (E alpha) • (EB).symm phi at hc
  constructor
  · intro h
    have ht : TB phi = phi := Subtype.ext h
    exact hc.symm.trans (congrArg (EB).symm ht)
  · intro h
    have ht : TB phi = phi := (EB).symm.injective (hc.trans h)
    exact congrArg (fun x : BF => x.val) ht

def fullCenterBrauerStabilizerEquiv (phi : BF) :
    ActualAutAmbient iota phi.val ≃*
      ActualAutAmbient (quotientRoot iota Z) ((EB).symm phi) where
  toFun a := ⟨MulOpposite.op (E a.1.unop),
    (fullCenterBrauer_fixed_iff iota R Z hcentral hfull hq phi a.1.unop).mp a.2⟩
  invFun b := ⟨MulOpposite.op ((E).symm b.1.unop), by
    apply (fullCenterBrauer_fixed_iff iota R Z hcentral hfull hq phi ((E).symm b.1.unop)).mpr
    have hb : MulOpposite.op b.1.unop • (EB).symm phi = (EB).symm phi := b.2
    simpa only [(E).apply_symm_apply] using hb⟩
  left_inv a := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact (E).symm_apply_apply a.1.unop
  right_inv b := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact (E).apply_symm_apply b.1.unop
  map_mul' a b := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    exact (E).map_mul b.1.unop a.1.unop

theorem fullCenterBrauerStabilizerEquiv_action (phi : BF) (a : ActualAutAmbient iota phi.val) :
    actualConjugation (quotientRoot iota Z) ((EB).symm phi)
      (fullCenterBrauerStabilizerEquiv iota R Z hcentral hfull hq phi a) =
      E (actualConjugation iota phi.val a) := by
  change (E a.val.unop)⁻¹ = E (a.val.unop⁻¹)
  exact ((E).map_inv _).symm

include hfull hq in
omit [Invertible (Fintype.card Z : k)] in
theorem fullDownEquivariance
    (eD : IBr (quotientRoot iota Z) ≃ ConjugacyClass (p := p) (K := K) (G := X ⧸ Z))
    (hD : ∀ (alpha : MulAut X) (beta : MulAut (X ⧸ Z)),
      (∀ x, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) →
      ∀ psi : IBr (quotientRoot iota Z),
        eD (IrreducibleBrauerCharacter.twist (quotientRoot iota Z) psi beta) =
          MulOpposite.op beta • eD psi) :
    ∀ (a : (MulAut (X ⧸ Z))ᵐᵒᵖ) (psi : IBr (quotientRoot iota Z)),
      eD (a • psi) = a • eD psi := by
  intro a psi
  exact hD ((E).symm a.unop) a.unop (fullCenterAutEquiv_lift_square Z hfull hq a.unop) psi

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientReducedAction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
