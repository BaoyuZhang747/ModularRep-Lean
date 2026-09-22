import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import Mathlib.Data.Fintype.Card

/-! # The actual outer action pairs the two nontrivial central sectors -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInverseSectorTransport

open ModularRep
open SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

theorem eq_or_eq_inv_of_card_three
    {A : Type*} [Group A] (hcard : Nat.card A = 3)
    {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) : b = a ∨ b = a⁻¹ := by
  classical
  let _ : Finite A := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let _ : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 3 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have haInv : a ≠ a⁻¹ := by
    intro h
    have htwo : a ^ 2 = 1 := by
      rw [pow_two]
      calc
        a * a = a⁻¹ * a := congrArg (fun t : A => t * a) h
        _ = 1 := inv_mul_cancel a
    have hthree : a ^ 3 = 1 := by
      simpa only [hcard] using (pow_card_eq_one' (x := a))
    apply ha
    calc
      a = a ^ 2 * a := by rw [htwo, one_mul]
      _ = a ^ 3 := (pow_succ a 2).symm
      _ = 1 := hthree
  have hsize : ({1, a, a⁻¹} : Finset A).card = 3 := by
    simp [ha, ha.symm, haInv]
  have hall : ({1, a, a⁻¹} : Finset A) = Finset.univ :=
    Finset.eq_univ_of_card _ (hsize.trans hcardF.symm)
  have hmem : b ∈ ({1, a, a⁻¹} : Finset A) := by
    rw [hall]
    exact Finset.mem_univ b
  simpa only [Finset.mem_insert, Finset.mem_singleton, hb, false_or] using hmem

theorem centralSector_op_eq_inv
    {k X : Type u} [Field k] [Group X]
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (nu : CentralSector (k := k) (X := X)) :
    MulOpposite.op tau • nu = nu⁻¹ := by
  apply MonoidHom.ext
  intro z
  change nu (Representation.centerAutomorphism tau z) = (nu z)⁻¹
  have hz : Representation.centerAutomorphism tau z = z⁻¹ := by
    apply Subtype.ext
    exact hinverts z
  rw [hz, map_inv]

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharZero K] [IsAlgClosed k]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem centralSector_card_three (hcardCenter : Nat.card (Subgroup.center X) = 3) :
    Nat.card (CentralSector (k := k) (X := X)) = 3 := by
  let _ : CommGroup (Subgroup.center X) := centralSubgroupCommGroup (Subgroup.center X) le_rfl
  let _ : HasEnoughRootsOfUnity k (Monoid.exponent (Subgroup.center X)) :=
    hasEnoughRootsOfUnity_of_isAlgClosed_card_invertible
  exact (CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Subgroup.center X) k).trans hcardCenter

theorem nontrivialCentralSector_eq_or_eq_inv
    (hcardCenter : Nat.card (Subgroup.center X) = 3)
    (nu0 nu : CentralSector (k := k) (X := X)) (hnu0 : nu0 ≠ 1) (hnu : nu ≠ 1) :
    nu = nu0 ∨ nu = nu0⁻¹ :=
  eq_or_eq_inv_of_card_three (centralSector_card_three (k := k) hcardCenter) hnu0 hnu

variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))

theorem weightSector_op_eq_inv
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (w : WeightClass (p := p) (K := K) (X := X)) :
    weightSector (R := R) (MulOpposite.op tau • w) = (weightSector (R := R) w)⁻¹ := by
  unfold weightSector
  rw [R.1.weightBlock_transport, blockSector_transport, centralSector_op_eq_inv tau hinverts]

def weightSectorInvEquiv
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (nu : CentralSector (k := k) (X := X)) :
    {w : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) w = nu} ≃
    {w : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) w = nu⁻¹} := by
  let E : Equiv.Perm (WeightClass (p := p) (K := K) (X := X)) :=
    MulAction.toPerm (MulOpposite.op tau)
  refine E.subtypeEquiv ?_
  intro w
  change weightSector (R := R) w = nu ↔
    weightSector (R := R) (MulOpposite.op tau • w) = nu⁻¹
  rw [weightSector_op_eq_inv R tau hinverts]
  constructor
  · intro h
    exact congrArg (fun mu : CentralSector (k := k) (X := X) => mu⁻¹) h
  · intro h
    apply MonoidHom.ext
    intro z
    have hz := congrArg (fun mu : CentralSector (k := k) (X := X) => mu z) h
    change ((weightSector (R := R) w) z)⁻¹ = (nu z)⁻¹ at hz
    exact inv_injective hz

theorem weightSector_inv_card
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (nu : CentralSector (k := k) (X := X)) :
    Nat.card {w : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) w = nu⁻¹} =
    Nat.card {w : WeightClass (p := p) (K := K) (X := X) // weightSector (R := R) w = nu} :=
  Nat.card_congr (weightSectorInvEquiv R tau hinverts nu).symm

theorem weightSector_card_of_one_nontrivial
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (hcardCenter : Nat.card (Subgroup.center X) = 3)
    (nu0 : CentralSector (k := k) (X := X)) (hnu0 : nu0 ≠ 1) (n : ℕ)
    (hcount : Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
      weightSector (R := R) w = nu0} = n) :
    ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {w : WeightClass (p := p) (K := K) (X := X) //
        weightSector (R := R) w = nu} = n := by
  intro nu hnu
  rcases nontrivialCentralSector_eq_or_eq_inv hcardCenter nu0 nu hnu0 hnu with h | h
  · simpa only [h] using hcount
  · rw [h, weightSector_inv_card R tau hinverts]
    exact hcount

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInverseSectorTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
