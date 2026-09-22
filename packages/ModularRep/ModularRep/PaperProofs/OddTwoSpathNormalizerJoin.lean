import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The subgroup index in Spath's intermediate block clause

Spath 2013, Definition 4.1(iii)(4), pp. 182--183, compares the block on Xbar H
with the local block on H, for N_Xbar(Qbar) ≤ H ≤ N_A(Qbar). The existing
`IntermediateBlockSource` uses J ≥ Xbar and the concrete group N_J(Qbar).

This module proves the group join at J = Xbar H: if the base is normal,
H ≤ N_A(Q), and base ∩ N_A(Q) ≤ H, then N_(base H)(Q) = H. The equality is
stated for actual subgroup intersections, comaps, and subgroup normalizers.
The resulting multiplicative equivalence preserves the ambient element and
the local inclusion; its coefficient transport uses that same equivalence.

The specialized adapter has exactly the `IntermediateLocalNormalizer`
carrier. It closes the group-index comparison only. Transport of the chosen
Brauer restrictions, block catalogues, and block-induction equality through
this equivalence remains separate, and no original iBAW target or final
source application is asserted here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoSpathNormalizerJoin

universe u v

section Groups

variable {A : Type u} [Group A]
variable (base H N Q : Subgroup A) [base.Normal]

/-- The elementary product/intersection identity underlying the source join. -/
theorem join_inf_eq_of_normal
    (hHN : H ≤ N) (hbaseN : base ⊓ N ≤ H) :
    (base ⊔ H) ⊓ N = H := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, hb, h, hh, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hx.1
    have hbN : b ∈ N := by
      have hproduct := N.mul_mem hx.2 (N.inv_mem (hHN hh))
      simpa only [mul_inv_cancel_right] using hproduct
    exact H.mul_mem (hbaseN ⟨hb, hbN⟩) hh
  · exact le_inf le_sup_right hHN

/-- The same equality on the exact comap carrier used by the intermediate
block interface. -/
theorem comap_join_eq_of_normal
    (hHN : H ≤ N) (hbaseN : base ⊓ N ≤ H) :
    N.comap (base ⊔ H).subtype = H.comap (base ⊔ H).subtype := by
  ext x
  change x.1 ∈ N ↔ x.1 ∈ H
  constructor
  · intro hx
    exact (join_inf_eq_of_normal base H N hHN hbaseN).le ⟨x.2, hx⟩
  · intro hx
    exact hHN hx

/-- Every element of Q lies in the allowed local subgroup, because Q
normalizes itself and lies in the base. -/
theorem radical_le_local
    (hQbase : Q ≤ base)
    (hbaseN : base ⊓ Subgroup.normalizer (Q : Set A) ≤ H) : Q ≤ H := by
  intro q hq
  exact hbaseN ⟨hQbase hq, Subgroup.le_normalizer hq⟩

/-- The actual subgroup normalizer inside the join equals the subgroup H
viewed inside that join. -/
theorem normalizer_subgroupOf_join_eq
    (hQbase : Q ≤ base)
    (hHN : H ≤ Subgroup.normalizer (Q : Set A))
    (hbaseN : base ⊓ Subgroup.normalizer (Q : Set A) ≤ H) :
    Subgroup.normalizer (Q.subgroupOf (base ⊔ H) : Set ↥(base ⊔ H)) =
      H.subgroupOf (base ⊔ H) := by
  rw [← Subgroup.subgroupOf_normalizer_eq (hQbase.trans le_sup_left)]
  exact comap_join_eq_of_normal base H
    (Subgroup.normalizer (Q : Set A)) hHN hbaseN

/-- The exact normalizer comap in the joined group is isomorphic to H. Both
directions retain the underlying element of A. -/
def normalizerJoinEquiv
    (hHN : H ≤ Subgroup.normalizer (Q : Set A))
    (hbaseN : base ⊓ Subgroup.normalizer (Q : Set A) ≤ H) :
    (Subgroup.normalizer (Q : Set A)).comap (base ⊔ H).subtype ≃* H where
  toFun x := ⟨x.1.1,
    (join_inf_eq_of_normal base H (Subgroup.normalizer (Q : Set A))
      hHN hbaseN).le ⟨x.1.2, x.2⟩⟩
  invFun h := ⟨⟨h.1, (show H ≤ base ⊔ H from le_sup_right) h.2⟩, hHN h.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The equivalence commutes with the literal inclusions into the ambient
group. This fixes the convention for character and group algebra transport. -/
theorem normalizerJoinEquiv_ambient_square
    (hHN : H ≤ Subgroup.normalizer (Q : Set A))
    (hbaseN : base ⊓ Subgroup.normalizer (Q : Set A) ≤ H) :
    H.subtype.comp (normalizerJoinEquiv base H Q hHN hbaseN).toMonoidHom =
      (base ⊔ H).subtype.comp
        ((Subgroup.normalizer (Q : Set A)).comap (base ⊔ H).subtype).subtype := by
  ext x
  rfl

/-- Coefficient transport uses the same underlying ambient element of H.
There is no additional choice of a group or coefficient identification. -/
theorem normalizerJoinEquiv_coeff
    {k : Type v} [CommRing k]
    (hHN : H ≤ Subgroup.normalizer (Q : Set A))
    (hbaseN : base ⊓ Subgroup.normalizer (Q : Set A) ≤ H)
    (z : k[(Subgroup.normalizer (Q : Set A)).comap (base ⊔ H).subtype])
    (h : H) :
    (MonoidAlgebra.domCongr k k (normalizerJoinEquiv base H Q hHN hbaseN) z).coeff h =
      z.coeff ⟨⟨h.1, (show H ≤ base ⊔ H from le_sup_right) h.2⟩, hHN h.2⟩ := by
  rw [MonoidAlgebra.coeff_domCongr]
  rfl

end Groups

section SpathCarriers

open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

variable {P : Definition35Problem.{u}}
variable {reference psi : Definition35Brauer P}
variable {w : Definition35Weight P}
variable {quotient : CentralQuotientBrauerSource P reference psi}

/-- The actual ambient radical lies in the displayed normal base. -/
theorem ambientRadical_le_base
    (ambient : SpathAmbientGroup P reference psi quotient) :
    ambientRadical P reference psi w quotient ambient ≤ ambient.base := by
  intro x hx
  obtain ⟨q, _, rfl⟩ := Subgroup.mem_map.mp hx
  exact (ambient.baseEquiv q).2

/-- The source's local subgroup contains the actual ambient radical. -/
theorem ambientRadical_le_local
    (ambient : SpathAmbientGroup P reference psi quotient)
    (H : Subgroup ambient.A)
    (hbaseN : ambient.base ⊓ AmbientLocalGroup P reference psi w quotient ambient ≤ H) :
    ambientRadical P reference psi w quotient ambient ≤ H :=
  radical_le_local ambient.base H
    (ambientRadical P reference psi w quotient ambient)
    (ambientRadical_le_base ambient) hbaseN

/-- The existing intermediate-normalizer carrier at J = base H is precisely
the source subgroup H, with an explicit multiplicative equivalence. -/
def spathIntermediateJoinEquiv
    (ambient : SpathAmbientGroup P reference psi quotient)
    (H : Subgroup ambient.A)
    (hHN : H ≤ AmbientLocalGroup P reference psi w quotient ambient)
    (hbaseN : ambient.base ⊓ AmbientLocalGroup P reference psi w quotient ambient ≤ H) :
    IntermediateLocalNormalizer (w := w) ambient (ambient.base ⊔ H) ≃* H :=
  normalizerJoinEquiv ambient.base H
    (ambientRadical P reference psi w quotient ambient) hHN hbaseN

/-- The actual local inclusion in `IntermediateBlockEqualityAt` commutes
with the source subgroup inclusion through the constructed equivalence. -/
theorem spathIntermediateJoinEquiv_local_square
    (ambient : SpathAmbientGroup P reference psi quotient)
    (H : Subgroup ambient.A)
    (hHN : H ≤ AmbientLocalGroup P reference psi w quotient ambient)
    (hbaseN : ambient.base ⊓ AmbientLocalGroup P reference psi w quotient ambient ≤ H) :
    (Subgroup.inclusion hHN).comp
        (spathIntermediateJoinEquiv ambient H hHN hbaseN).toMonoidHom =
      intermediateLocalToAmbientLocal (w := w) ambient (ambient.base ⊔ H) := by
  ext x
  rfl

/-- The ambient square for the exact Spath intermediate carrier. -/
theorem spathIntermediateJoinEquiv_ambient_square
    (ambient : SpathAmbientGroup P reference psi quotient)
    (H : Subgroup ambient.A)
    (hHN : H ≤ AmbientLocalGroup P reference psi w quotient ambient)
    (hbaseN : ambient.base ⊓ AmbientLocalGroup P reference psi w quotient ambient ≤ H) :
    H.subtype.comp (spathIntermediateJoinEquiv ambient H hHN hbaseN).toMonoidHom =
      (ambient.base ⊔ H).subtype.comp
        (IntermediateLocalNormalizer (w := w) ambient (ambient.base ⊔ H)).subtype := by
  ext x
  rfl

end SpathCarriers

end ModularRep.PaperProofs.OddTwoSpathNormalizerJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
