import ModularRep.PrimitiveBlockAutomorphism
import Mathlib.GroupTheory.OrderOfElement

/-! # An invariant block has trivial sector under inversion of a centre of order three -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedBlockSector

open ModularRep

variable {k X : Type*} [Field k] [Group X]
variable [Fintype (Subgroup.center X)] [IsAlgClosed k]
variable [Invertible (Fintype.card (Subgroup.center X) : k)]

theorem centralCharacterSector_eq_one_of_fixed
    (tau : MulAut X) (hcard : Nat.card (Subgroup.center X) = 3)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (b : LiteralPrimitiveBlock k X) (hfixed : MulOpposite.op tau • b = b) :
    b.2.centralCharacterSector (Subgroup.center X) le_rfl = 1 := by
  let nu : Subgroup.center X →* kˣ := b.2.centralCharacterSector (Subgroup.center X) le_rfl
  have hnu : nu = nu.comp (Subgroup.centerCongr tau).toMonoidHom := by
    have h := LiteralPrimitiveBlock.rightMulAction_smul_centralCharacterSector (MulOpposite.op tau) b
    rw [hfixed] at h
    exact h
  change nu = 1
  apply MonoidHom.ext
  intro z
  change nu z = 1
  have hzi : Subgroup.centerCongr tau z = z⁻¹ := by
    apply Subtype.ext
    change tau (z : X) = (z : X)⁻¹
    exact hinverts z
  have hinv : nu z = (nu z)⁻¹ := by
    have h := DFunLike.congr_fun hnu z
    change nu z = nu (Subgroup.centerCongr tau z) at h
    rw [hzi, map_inv] at h
    exact h
  have htwo : (nu z) ^ 2 = 1 := by
    rw [pow_two]
    calc
      nu z * nu z = (nu z)⁻¹ * nu z := congrArg (fun a : kˣ => a * nu z) hinv
      _ = 1 := inv_mul_cancel (nu z)
  have hzthree : z ^ 3 = 1 := by
    simpa only [hcard] using (pow_card_eq_one' (x := z))
  have hthree : (nu z) ^ 3 = 1 := by rw [← map_pow, hzthree, map_one]
  calc
    nu z = (nu z) ^ 2 * nu z := by rw [htwo, one_mul]
    _ = (nu z) ^ 3 := (pow_succ (nu z) 2).symm
    _ = 1 := hthree

theorem trivial_sector_of_fixed
    (tau : MulAut X) (hcard : Nat.card (Subgroup.center X) = 3)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (b : LiteralPrimitiveBlock k X) (hfixed : MulOpposite.op tau • b = b) :
    IsCentralCharacterSector (Subgroup.center X) b.1 1 := by
  have h := b.2.centralCharacterSector_isSector (Subgroup.center X) le_rfl
  rw [centralCharacterSector_eq_one_of_fixed tau hcard hinverts b hfixed] at h
  exact h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFixedBlockSector


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
