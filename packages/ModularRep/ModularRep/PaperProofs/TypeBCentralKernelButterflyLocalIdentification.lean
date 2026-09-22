import ModularRep.PaperProofs.TypeBCentralKernelButterflyCertificate

/-!
# Constructing the Butterfly local-base identification

The second local ambient is the prescribed preimage of the first local
group's actual conjugation image. Containment of the first base centralizer
in the first local group forces membership of corresponding base elements
to agree. Restricting the same base equivalence therefore constructs the
local identification. No local equivalence or new triple is sourced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelButterflyLocalIdentification

open ModularRep TypeBCentralKernelTripleCertificate
open TypeBCentralKernelButterflyCertificate

universe u

variable {T1 T2 : Type u} [Group T1] [Group T2]
variable (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
variable (e : N1 ≃* N2) (H1 : Subgroup T1)

/-- Corresponding base elements induce the same inner automorphism on N1. -/
theorem base_action_eq (n : N1) :
    firstAction N1 (n : T1) = secondAction N1 N2 e (e n : T2) := by
  apply MulEquiv.ext
  intro x
  apply e.injective
  have first : firstAction N1 (n : T1) x = n * x * n⁻¹ := by
    apply Subtype.ext
    rfl
  rw [first, secondAction_value]
  apply Subtype.ext
  change (e (n * x * n⁻¹) : T2) =
    (e n : T2) * (e x : T2) * (e n : T2)⁻¹
  simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

/-- The kernel of actual conjugation centralizes the actual normal base. -/
theorem centralizes_of_action_one (t : T1) (h : firstAction N1 t = 1) :
    t ∈ Subgroup.centralizer (N1 : Set T1) := by
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have point := congrArg (fun a : MulAut N1 => (a ⟨n, hn⟩ : T1)) h
  change t * n * t⁻¹ = n at point
  have cancelled := congrArg (fun x : T1 => x * t) point
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using cancelled.symm

/-- Equality of the two actual inner actions reflects local membership
because the residual first ambient element lies in its base centralizer. -/
theorem base_mem_iff (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (n : N1) :
    (n : T1) ∈ H1 ↔ (e n : T2) ∈ secondLocalAmbient N1 N2 e H1 := by
  rw [mem_secondLocalAmbient]
  constructor
  · intro hn
    exact ⟨n.val, hn, base_action_eq N1 N2 e n⟩
  · rintro ⟨h, hh, same⟩
    have actions : firstAction N1 h = firstAction N1 (n : T1) :=
      same.trans (base_action_eq N1 N2 e n).symm
    have residual : firstAction N1 (h⁻¹ * (n : T1)) = 1 := by
      rw [map_mul, map_inv, actions, inv_mul_cancel]
    have hc := centralizer_le (centralizes_of_action_one N1 (h⁻¹ * (n : T1)) residual)
    have product := H1.mul_mem hh hc
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using product

/-- Restriction of e to the two literal local-base carriers. Both directions
use the proven membership equivalence; there is no independent local map. -/
def localEquiv (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1) :
    localBase N1 H1 ≃* localBase N2 (secondLocalAmbient N1 N2 e H1) where
  toFun x :=
    ⟨⟨(e (localToBase N1 H1 x)).val,
      (base_mem_iff N1 N2 e H1 centralizer_le (localToBase N1 H1 x)).mp x.val.property⟩,
      (e (localToBase N1 H1 x)).property⟩
  invFun y :=
    ⟨⟨(e.symm (localToBase N2 (secondLocalAmbient N1 N2 e H1) y)).val, by
      apply (base_mem_iff N1 N2 e H1 centralizer_le
        (e.symm (localToBase N2 (secondLocalAmbient N1 N2 e H1) y))).mpr
      rw [e.apply_symm_apply]
      exact y.val.property⟩,
      (e.symm (localToBase N2 (secondLocalAmbient N1 N2 e H1) y)).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (e.symm (e (localToBase N1 H1 x)) : T1) = x.val.val
    rw [e.symm_apply_apply]
    rfl
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change (e (e.symm (localToBase N2 (secondLocalAmbient N1 N2 e H1) y)) : T2) = y.val.val
    rw [e.apply_symm_apply]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    change (e (localToBase N1 H1 (x * y)) : T2) =
      (e (localToBase N1 H1 x) : T2) * (e (localToBase N1 H1 y) : T2)
    simp only [map_mul, Subgroup.coe_mul]

theorem localEquiv_base_value
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1)
    (x : localBase N1 H1) :
    localToBase N2 (secondLocalAmbient N1 N2 e H1)
      (localEquiv N1 N2 e H1 centralizer_le x) = e (localToBase N1 H1 x) := rfl

/-- Construct the exact carrier guard requested by the Butterfly interface. -/
def localIdentification
    (centralizer_le : Subgroup.centralizer (N1 : Set T1) ≤ H1) :
    LocalIdentification N1 N2 e H1 (secondLocalAmbient N1 N2 e H1) where
  equiv := localEquiv N1 N2 e H1 centralizer_le
  base_value := localEquiv_base_value N1 N2 e H1 centralizer_le

section ExistingTriple

variable [Finite T1] {p : ℕ} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable {D : TripleData (p := p) (k := k) (K := K) N1 H1}
variable {theta : IBr D.base.iota} {phi : IBr D.localData.iota}

/-- An existing source-side literal block triple supplies the only guard.
No assertion about the new block triple is used to construct this map. -/
def localIdentification_of_witness (witness : BlockTripleWitness D theta phi) :
    LocalIdentification N1 N2 e H1 (secondLocalAmbient N1 N2 e H1) :=
  localIdentification N1 N2 e H1 witness.centralizer_le

end ExistingTriple

end ModularRep.PaperProofs.TypeBCentralKernelButterflyLocalIdentification


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
