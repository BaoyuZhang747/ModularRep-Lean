import ModularRep.PrimitiveBlockAutomorphism
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport

/-!
# The specified quotient block of an arbitrary trivial-sector primitive

Averaging supplies nonvanishing before a block or character is chosen
downstairs. The actual group algebra image determines the quotient block.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap

open ModularRep
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralQuotientAveraging
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport

universe u

variable {p : ℕ} {k G : Type u}
variable [Field k] [CharP k p] [IsAlgClosed k] [Group G] [Finite G]
variable (Z : Subgroup G) [Z.Normal] [Fintype Z] [Invertible (Fintype.card Z : k)]
variable (hp : p.Prime) (hZ : Z ≤ Subgroup.center G) (hprimeTo : ¬ p ∣ Nat.card Z)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) hp
  (by simpa only [QuotientGroup.ker_mk'] using hZ)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))

def quotientPrimitive
    (b : LiteralPrimitiveBlock k G)
    (hb : IsCentralCharacterSector Z b.1 (1 : Z →* kˣ)) :
    LiteralPrimitiveBlock k (G ⧸ Z) :=
  ⟨algebraMapOf (QuotientGroup.mk' Z) b.1,
    Sglobal.primitive_image_of_ne_zero b.1 b.2
      (quotient_image_ne_zero_of_trivial_sector Z b.2 hb)⟩

@[simp]
theorem quotientPrimitive_val
    (b : LiteralPrimitiveBlock k G)
    (hb : IsCentralCharacterSector Z b.1 (1 : Z →* kˣ)) :
    (quotientPrimitive Z hp hZ hprimeTo Sglobal b hb).1 =
      algebraMapOf (QuotientGroup.mk' Z) b.1 := rfl

variable {J : Type u} [Fintype J] {eQ : J → k[G ⧸ Z]}
variable (DQ : BlockIdempotentDecomposition eQ)

def quotientBlockIndex
    (b : LiteralPrimitiveBlock k G)
    (hb : IsCentralCharacterSector Z b.1 (1 : Z →* kˣ)) : J :=
  DQ.primitiveBlockEquiv.symm (quotientPrimitive Z hp hZ hprimeTo Sglobal b hb)

theorem quotientBlockIndex_value
    (b : LiteralPrimitiveBlock k G)
    (hb : IsCentralCharacterSector Z b.1 (1 : Z →* kˣ)) :
    eQ (quotientBlockIndex Z hp hZ hprimeTo Sglobal DQ b hb) =
      algebraMapOf (QuotientGroup.mk' Z) b.1 := by
  exact congrArg Subtype.val
    (DQ.primitiveBlockEquiv.apply_symm_apply (quotientPrimitive Z hp hZ hprimeTo Sglobal b hb))

theorem quotientBlockIndex_eq_iff
    (b : LiteralPrimitiveBlock k G)
    (hb : IsCentralCharacterSector Z b.1 (1 : Z →* kˣ)) (j : J) :
    quotientBlockIndex Z hp hZ hprimeTo Sglobal DQ b hb = j ↔
      eQ j = algebraMapOf (QuotientGroup.mk' Z) b.1 := by
  constructor
  · intro h
    rw [← h]
    exact quotientBlockIndex_value Z hp hZ hprimeTo Sglobal DQ b hb
  · intro h
    apply DQ.primitiveBlockOfIndex_injective
    apply Subtype.ext
    exact (quotientBlockIndex_value Z hp hZ hprimeTo Sglobal DQ b hb).trans h.symm

variable {I : Type u} [Fintype I] {eG : I → k[G]}
variable (DG : BlockIdempotentDecomposition eG)

theorem quotientBlockIndex_eq_iff_index_eq
    (i j : I)
    (hi : IsCentralCharacterSector Z (eG i) (1 : Z →* kˣ))
    (hj : IsCentralCharacterSector Z (eG j) (1 : Z →* kˣ)) :
    quotientBlockIndex Z hp hZ hprimeTo Sglobal DQ ⟨eG i, DG.primitive i⟩ hi =
      quotientBlockIndex Z hp hZ hprimeTo Sglobal DQ ⟨eG j, DG.primitive j⟩ hj ↔ i = j := by
  constructor
  · intro hij
    have himage : algebraMapOf (QuotientGroup.mk' Z) (eG i) =
        algebraMapOf (QuotientGroup.mk' Z) (eG j) :=
      (quotientBlockIndex_value Z hp hZ hprimeTo Sglobal DQ
        ⟨eG i, DG.primitive i⟩ hi).symm.trans
        ((congrArg eQ hij).trans (quotientBlockIndex_value Z hp hZ hprimeTo Sglobal DQ
          ⟨eG j, DG.primitive j⟩ hj))
    exact blockIndex_eq_of_map_eq_of_ne_zero DG
      (algebraMapOf (k := k) (QuotientGroup.mk' Z)).toRingHom i j himage
      (quotient_image_ne_zero_of_trivial_sector Z (DG.primitive i) hi)
  · rintro rfl
    rfl

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
