import ModularRep.IrreducibleBrauerCharacterEquiv
import ModularRep.PaperProofs.OddTwoActualStabilizerTriple

/-!
# Actual holomorph coordinates along a group equivalence

A fixed group equivalence e determines the automorphism equivalence
MulAut.congr e and the full holomorph equivalence. The character and root
are the existing alongMulEquiv transports. Their actual opposite-group
equivariance then determines the global stabilizer image and the exact
normal base-kernel image.

All declarations are K. No stabilizer equality, character-value or root
square, raw-weight map, block relation or FLZ interpretation is a premise.
The raw/local tuple side is a separate consumer of the same ambient e.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates

open Formalisation
open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple

universe u

section Groups

variable {G H : Type u} [Group G] [Group H]
variable (e : G ≃* H)

/-- The actual full holomorph with the identity automorphism action. -/
abbrev Holomorph (G : Type u) [Group G] :=
  G ⋊[MonoidHom.id (MulAut G)] MulAut G

/-- The induced automorphism is evaluated on the original e-coordinate. -/
theorem automorphismEquiv_apply (a : MulAut G) (x : G) :
    MulAut.congr e a (e x) = e (a x) := by
  change e (a (e.symm (e x))) = e (a x)
  rw [MulEquiv.symm_apply_apply]

/-- Inner automorphisms transport through the actual same e. -/
theorem automorphismEquiv_inner (x : G) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  obtain ⟨z, rfl⟩ := e.surjective y
  rw [automorphismEquiv_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

/-- The full holomorph map is the literal pair (e, MulAut.congr e). -/
def holomorphEquiv : Holomorph G ≃* Holomorph H :=
  SemidirectProduct.congr e (MulAut.congr e) (fun a => by
    ext x
    exact (automorphismEquiv_apply e a x).symm)

@[simp] theorem holomorphEquiv_left (d : Holomorph G) :
    (holomorphEquiv e d).left = e d.left := rfl

@[simp] theorem holomorphEquiv_right (d : Holomorph G) :
    (holomorphEquiv e d).right = MulAut.congr e d.right := rfl

@[simp] theorem holomorphEquiv_inl (x : G) :
    holomorphEquiv e (SemidirectProduct.inl x) = SemidirectProduct.inl (e x) := by
  apply SemidirectProduct.ext
  · rfl
  · exact map_one (MulAut.congr e)

@[simp] theorem holomorphEquiv_inr (a : MulAut G) :
    holomorphEquiv e (SemidirectProduct.inr a) =
      SemidirectProduct.inr (MulAut.congr e a) := by
  apply SemidirectProduct.ext
  · exact map_one e
  · rfl

/-- The base square for the actual natural conjugation action. -/
theorem holomorph_action_square (d : Holomorph G) (x : G) :
    e (semidirectToMulAut (MonoidHom.id (MulAut G)) d x) =
      semidirectToMulAut (MonoidHom.id (MulAut H)) (holomorphEquiv e d) (e x) := by
  change e (d.left * d.right x * d.left⁻¹) =
    e d.left * (MulAut.congr e d.right) (e x) * (e d.left)⁻¹
  rw [automorphismEquiv_apply]
  simp only [map_mul, map_inv]

/-- Both natural automorphism maps commute with the computed equivalence. -/
theorem holomorph_automorphism_square (d : Holomorph G) :
    semidirectToMulAut (MonoidHom.id (MulAut H)) (holomorphEquiv e d) =
      MulAut.congr e (semidirectToMulAut (MonoidHom.id (MulAut G)) d) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [automorphismEquiv_apply]
  exact (holomorph_action_square e d x).symm

end Groups

section BrauerStabilizers

variable {p : ℕ} {k K G H : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group H] [Fintype H]

local instance finiteHolomorphAut (J : Type u) [Group J] [Finite J] : Finite (MulAut J) :=
  Finite.of_injective (fun a : MulAut J => (a : J → J)) DFunLike.coe_injective

variable (iota : PrimeRegularRootEmbedding p k K G) (e : G ≃* H)

/-- The actual full holomorph action on IBr is its right-coordinate
inverse/op action, since the left inner action fixes every character. -/
theorem brauer_smul_right (d : Holomorph G) (psi : IBr iota) :
    letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
    d • psi = MulOpposite.op d.right⁻¹ • psi := by
  letI : MulAction G (IBr iota) :=
    rightAutomorphismAction (MulAut.conj : G →* MulAut G)
  letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
  change d.left • (MulOpposite.op d.right⁻¹ • psi) = MulOpposite.op d.right⁻¹ • psi
  exact inner_fixes_ibr iota d.left (MulOpposite.op d.right⁻¹ • psi)

/-- Actual character equivariance follows from the existing root-preserving
IBr equivalence; no character equality or action match is a premise. -/
theorem brauer_equivariant (d : Holomorph G) (psi : IBr iota) :
    letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
    letI := actualBrauerAction (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
    IrreducibleBrauerCharacter.equivAlongMulEquiv iota e (d • psi) =
      holomorphEquiv e d • IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi := by
  letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
  letI := actualBrauerAction (iota.alongMulEquiv e) (MonoidHom.id (MulAut H))
  rw [brauer_smul_right, brauer_smul_right]
  simpa only [MulOpposite.unop_op, map_inv, holomorphEquiv_right] using
    IrreducibleBrauerCharacter.equivAlongMulEquiv_op_smul iota e psi
      (MulOpposite.op d.right⁻¹)

variable (psi : IBr iota)

local notation "iotaH" => iota.alongMulEquiv e
local notation "psiH" => IrreducibleBrauerCharacter.equivAlongMulEquiv iota e psi

/-- Exact membership equivalence for the two actual character stabilizers. -/
theorem global_membership_iff (d : Holomorph G) :
    holomorphEquiv e d ∈ globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH ↔
      d ∈ globalStabilizer iota (MonoidHom.id (MulAut G)) psi := by
  letI := actualBrauerAction iota (MonoidHom.id (MulAut G))
  letI := actualBrauerAction iotaH (MonoidHom.id (MulAut H))
  change holomorphEquiv e d • psiH = psiH ↔ d • psi = psi
  rw [← brauer_equivariant iota e d psi]
  exact (IrreducibleBrauerCharacter.equivAlongMulEquiv iota e).injective.eq_iff

/-- The whole global stabilizer image is derived, not supplied as data. -/
theorem globalStabilizer_image :
    (globalStabilizer iota (MonoidHom.id (MulAut G)) psi).map
        (holomorphEquiv e).toMonoidHom =
      globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (global_membership_iff iota e psi d).mpr hd
  · intro hy
    obtain ⟨d, rfl⟩ := (holomorphEquiv e).surjective y
    exact ⟨d, (global_membership_iff iota e psi d).mp hy, rfl⟩

/-- Restriction of the computed whole map to the actual global groups. -/
def globalEquiv :
    globalStabilizer iota (MonoidHom.id (MulAut G)) psi ≃*
      globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH :=
  ((holomorphEquiv e).subgroupMap
    (globalStabilizer iota (MonoidHom.id (MulAut G)) psi)).trans
      (MulEquiv.subgroupCongr (globalStabilizer_image iota e psi))

@[simp] theorem globalEquiv_ambient
    (d : globalStabilizer iota (MonoidHom.id (MulAut G)) psi) :
    (globalEquiv iota e psi d : Holomorph H) = holomorphEquiv e (d : Holomorph G) := rfl

/-- The right-projection kernels are the exact normal bases of the tuples. -/
theorem globalEquiv_mem_base_iff
    (d : globalStabilizer iota (MonoidHom.id (MulAut G)) psi) :
    globalEquiv iota e psi d ∈ baseSubgroup iotaH (MonoidHom.id (MulAut H)) psiH ↔
      d ∈ baseSubgroup iota (MonoidHom.id (MulAut G)) psi := by
  change MulAut.congr e d.1.right = 1 ↔ d.1.right = 1
  constructor
  · intro hd
    apply (MulAut.congr e).injective
    exact hd.trans (map_one (MulAut.congr e)).symm
  · intro hd
    rw [hd, map_one]

/-- Exact base image inside the two actual global stabilizers. -/
theorem globalEquiv_map_base :
    (baseSubgroup iota (MonoidHom.id (MulAut G)) psi).map
        (globalEquiv iota e psi).toMonoidHom =
      baseSubgroup iotaH (MonoidHom.id (MulAut H)) psiH := by
  ext y
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (globalEquiv_mem_base_iff iota e psi d).mpr hd
  · intro hy
    obtain ⟨d, rfl⟩ := (globalEquiv iota e psi).surjective y
    exact ⟨d, (globalEquiv_mem_base_iff iota e psi d).mp hy, rfl⟩

/-- Canonical restriction to the actual normal base. -/
def baseKernelEquiv :
    baseSubgroup iota (MonoidHom.id (MulAut G)) psi ≃*
      baseSubgroup iotaH (MonoidHom.id (MulAut H)) psiH :=
  ((globalEquiv iota e psi).subgroupMap
    (baseSubgroup iota (MonoidHom.id (MulAut G)) psi)).trans
      (MulEquiv.subgroupCongr (globalEquiv_map_base iota e psi))

@[simp] theorem baseKernelEquiv_ambient
    (x : baseSubgroup iota (MonoidHom.id (MulAut G)) psi) :
    (baseKernelEquiv iota e psi x :
      globalStabilizer iotaH (MonoidHom.id (MulAut H)) psiH) =
      globalEquiv iota e psi (x : globalStabilizer iota (MonoidHom.id (MulAut G)) psi) := rfl

/-- The canonical base restriction is e in the original base coordinates. -/
theorem baseKernelEquiv_base_square (x : G) :
    baseKernelEquiv iota e psi
        (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi x) =
      OddTwoActualStabilizerTriple.baseEquiv iotaH (MonoidHom.id (MulAut H)) psiH (e x) := by
  apply Subtype.ext
  apply Subtype.ext
  change holomorphEquiv e
      (OddTwoActualStabilizerTriple.baseEquiv iota (MonoidHom.id (MulAut G)) psi x).1.1 =
    (OddTwoActualStabilizerTriple.baseEquiv iotaH (MonoidHom.id (MulAut H)) psiH (e x)).1.1
  rw [OddTwoActualStabilizerTriple.baseEquiv_ambient,
    OddTwoActualStabilizerTriple.baseEquiv_ambient, holomorphEquiv_inl]

end BrauerStabilizers

end ModularRep.PaperProofs.OddTwoGroupEquivHolomorphCoordinates


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
