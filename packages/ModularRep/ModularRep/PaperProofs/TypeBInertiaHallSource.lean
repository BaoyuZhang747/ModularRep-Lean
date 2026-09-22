import ModularRep.PaperProofs.TypeBCliffordIndexCompatibility
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete

/-!
# Actual downstairs inertias and the Hall preimage in Type B

The two inertia groups here are literal stabilizers of a Spin Brauer
character and a Spin character-weight CONJUGACY CLASS under special
Clifford conjugation. Their actions are the canonical inverse pullbacks.
Inner Spin conjugation and central special Clifford conjugation fix these
carriers, so both inertias contain `Spin sup center` by checked deductions.

The Hall input is a subgroup of the literal quotient special Clifford/Spin,
with prime-to-ell order and ell-power index. Its preimage is defined by the
actual quotient map. This routine cyclic-quotient source is the one used
in Brough--Spaeth Section 2, Lemmas 2.14--2.15, and FLZ Remark 2.2, p. 537.
The quotient special Clifford/Spin has order q-1, not two.

The checked Type B index argument proves that the join of either actual
downstairs inertia with this preimage is the whole special Clifford group.
No `J_G` symbol, covering relation, or matching compatibility is assumed.
The published definitions of `J_G`, and the precise constituent or covered
weight chosen there, remain separate source joins.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBInertiaHallSource

open ModularRep
open TypeBCliffordCarriers TypeBSpinStabilizer TypeBCliffordIndexCompatibility
open CyclicOuterLemma37Concrete

variable {n : ℕ} {F K k : Type}
variable [Field F] [Field K] [Field k] [CharZero K]
variable (N : NormSource n F)

/-- Actual special Clifford conjugation on the literal norm-one subgroup,
in the opposite-automorphism orientation used for characters and weights. -/
def spinConjugation : SpecialClifford n F →* (MulAut (Spin n F N))ᵐᵒᵖ :=
  inverseOpHom (MulAut.conjNormal (H := SpinSubgroup n F N))

/-- A central ambient element induces the identity on the literal Spin
subgroup. This uses its actual centrality, not a sourced action claim. -/
theorem central_conjNormal_eq_one
    {g : SpecialClifford n F}
    (hg : g ∈ Subgroup.center (SpecialClifford n F)) :
    MulAut.conjNormal (H := SpinSubgroup n F N) g = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change g * (x : SpecialClifford n F) * g⁻¹ = x
  have hc : g * (x : SpecialClifford n F) = (x : SpecialClifford n F) * g :=
    ((Subgroup.mem_center_iff.mp hg) (x : SpecialClifford n F)).symm
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

section ActualInertias

variable {ell : ℕ} [CharP k ell] [IsAlgClosed k] [Finite (Spin n F N)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))

/-- The actual special Clifford inertia of a downstairs Spin Brauer
character, as a comap of the canonical automorphism stabilizer. -/
def brauerInertia (phi : IBr iota) : Subgroup (SpecialClifford n F) :=
  (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ phi).comap (spinConjugation N)

/-- The actual special Clifford inertia of a downstairs Spin weight
conjugacy class. Raw-pair inertia is a different subgroup. -/
def weightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    Subgroup (SpecialClifford n F) :=
  (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ W).comap (spinConjugation N)

@[simp]
theorem mem_brauerInertia (phi : IBr iota) (g : SpecialClifford n F) :
    g ∈ brauerInertia N iota phi ↔
      IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) = phi := Iff.rfl

@[simp]
theorem mem_weightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N))
    (g : SpecialClifford n F) :
    g ∈ weightInertia N W ↔
      CharacterWeight.rightTwistConjugacyClass
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) W = W := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem spin_le_brauerInertia (phi : IBr iota) :
    SpinSubgroup n F N ≤ brauerInertia N iota phi := by
  intro g hg
  rw [mem_brauerInertia]
  let h : Spin n F N := ⟨g, hg⟩
  have hc : MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ =
      MulAut.conj h⁻¹ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hc]
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj phi.1 h⁻¹

theorem center_le_brauerInertia (phi : IBr iota) :
    Subgroup.center (SpecialClifford n F) ≤ brauerInertia N iota phi := by
  intro g hg
  rw [mem_brauerInertia,
    central_conjNormal_eq_one N ((Subgroup.center (SpecialClifford n F)).inv_mem hg)]
  exact IrreducibleBrauerCharacter.twist_refl iota phi

theorem spin_center_le_brauerInertia (phi : IBr iota) :
    SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) ≤
      brauerInertia N iota phi :=
  sup_le (spin_le_brauerInertia N iota phi) (center_le_brauerInertia N iota phi)

set_option maxHeartbeats 1000000 in
theorem spin_le_weightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    SpinSubgroup n F N ≤ weightInertia N W := by
  intro g hg
  rw [mem_weightInertia]
  let h : Spin n F N := ⟨g, hg⟩
  have hc : MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ =
      MulAut.conj h⁻¹ := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  rw [hc]
  have hfixed := inner_fixes_weightClass (p := ell) (K := K)
    (H := Spin n F N) h W
  change CharacterWeight.rightTwistConjugacyClass (MulAut.conj h⁻¹) W = W at hfixed
  exact hfixed

theorem center_le_weightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    Subgroup.center (SpecialClifford n F) ≤ weightInertia N W := by
  intro g hg
  rw [mem_weightInertia,
    central_conjNormal_eq_one N ((Subgroup.center (SpecialClifford n F)).inv_mem hg)]
  exact CharacterWeight.rightTwistConjugacyClass_one W

theorem spin_center_le_weightInertia
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) ≤
      weightInertia N W :=
  sup_le (spin_le_weightInertia N W) (center_le_weightInertia N W)

end ActualInertias

section HallSource

/-- The Hall source lives in the actual quotient by Spin. Its order and
index specify a Hall ell-prime subgroup; no inertia or compatibility
conclusion is among these routine external inputs. -/
structure HallPrimeToQuotientSource (ell : ℕ) where
  prime : Nat.Prime ell
  quotient_cyclic : IsCyclic (SpecialClifford n F ⧸ SpinSubgroup n F N)
  hall : Subgroup (SpecialClifford n F ⧸ SpinSubgroup n F N)
  order_primeTo : ell.Coprime (Nat.card hall)
  exponent : ℕ
  index_eq : hall.index = ell ^ exponent

namespace HallPrimeToQuotientSource

variable {N} {ell : ℕ} (S : HallPrimeToQuotientSource N ell)

/-- The Hall preimage under the literal quotient map, not a caller-chosen
ambient subgroup with only a matching index. -/
def preimage : Subgroup (SpecialClifford n F) :=
  S.hall.comap (QuotientGroup.mk' (SpinSubgroup n F N))

/-- Every subgroup of the source cyclic quotient is normal, hence so is
the literal Hall preimage. -/
instance preimage_normal : S.preimage.Normal := by
  letI : IsCyclic (SpecialClifford n F ⧸ SpinSubgroup n F N) := S.quotient_cyclic
  change (S.hall.comap (QuotientGroup.mk' (SpinSubgroup n F N))).Normal
  infer_instance

theorem preimage_index : S.preimage.index = ell ^ S.exponent := by
  change (S.hall.comap (QuotientGroup.mk' (SpinSubgroup n F N))).index =
    ell ^ S.exponent
  exact (S.hall.index_comap_of_surjective
    (f := QuotientGroup.mk' (SpinSubgroup n F N))
    (QuotientGroup.mk'_surjective (SpinSubgroup n F N))).trans S.index_eq

theorem spin_le_preimage : SpinSubgroup n F N ≤ S.preimage := by
  intro g hg
  change (g : SpecialClifford n F ⧸ SpinSubgroup n F N) ∈ S.hall
  rw [(QuotientGroup.eq_one_iff g).mpr hg]
  exact S.hall.one_mem

end HallPrimeToQuotientSource

end HallSource

section ActualHallJoins

variable {ell : ℕ} [CharP k ell] [IsAlgClosed k] [Finite (Spin n F N)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
variable (hOdd : Odd ell)
variable (diagonal : SpecialClifford n F →* DiagonalGroup)
variable (surjective : Function.Surjective diagonal)
variable (kernel : diagonal.ker =
  SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))
variable (hall : HallPrimeToQuotientSource N ell)

include hOdd diagonal surjective kernel

/-- The actual downstairs Brauer inertia and actual Hall preimage generate
the whole special Clifford group. -/
theorem brauerInertia_sup_hallPreimage_eq_top (phi : IBr iota) :
    brauerInertia N iota phi ⊔ hall.preimage = ⊤ :=
  inertia_sup_hall_eq_top N hOdd diagonal surjective kernel
    (brauerInertia N iota phi) hall.preimage
    (spin_center_le_brauerInertia N iota phi) hall.preimage_index

/-- The same conclusion for the actual downstairs weight conjugacy class.
No chosen relation between this class and the Brauer character is needed. -/
theorem weightInertia_sup_hallPreimage_eq_top
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    weightInertia N W ⊔ hall.preimage = ⊤ :=
  inertia_sup_hall_eq_top N hOdd diagonal surjective kernel
    (weightInertia N W) hall.preimage
    (spin_center_le_weightInertia N W) hall.preimage_index

/-- The literal set product in the published inertia-times-Hall formula,
on an actual downstairs Brauer character. -/
theorem brauerInertia_mul_hallPreimage_eq_univ (phi : IBr iota) :
    (brauerInertia N iota phi : Set (SpecialClifford n F)) *
        (hall.preimage : Set (SpecialClifford n F)) = Set.univ := by
  rw [← Subgroup.mul_normal,
    brauerInertia_sup_hallPreimage_eq_top N iota hOdd diagonal surjective kernel hall phi]
  rfl

/-- The same literal product formula for an actual downstairs Spin weight
conjugacy class. The use of conjugacy classes is essential here. -/
theorem weightInertia_mul_hallPreimage_eq_univ
    (W : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := Spin n F N)) :
    (weightInertia N W : Set (SpecialClifford n F)) *
        (hall.preimage : Set (SpecialClifford n F)) = Set.univ := by
  rw [← Subgroup.mul_normal,
    weightInertia_sup_hallPreimage_eq_top N hOdd diagonal surjective kernel hall W]
  rfl

end ActualHallJoins

end ModularRep.PaperProofs.TypeBInertiaHallSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
