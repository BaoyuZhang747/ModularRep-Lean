import ModularRep.PaperProofs.OddTwoLiteralSpathTarget
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# The actual intermediate H / XH normalizer comparison

For X normal in A and X ∩ N ≤ H ≤ N, the actual subgroup
(X ⊔ H) ∩ N equals H. At N = N_A(Q), this identifies the intermediate
normalizer in the relative block condition with the direct H in Spath
Definition 4.1. All equivalences below are identity on the underlying
ambient elements and preserve the two actual inclusions.

The quotient and odd-two specializations reuse their existing subgroups,
not new copies selected by an isomorphism source. No character, root,
block, relation, or published-result premise occurs. This module does not
transport those later data or assert either complete target.
-/

namespace ModularRep.PaperProofs.TypeCIntermediateNormalizerComparison

open ModularRep
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily

universe u

section Groups

variable {A : Type u} [Group A]
variable (X H N : Subgroup A)

/-- The subgroup used by the J-indexed relative target, at J = XH. -/
abbrev LocalNormalizer : Subgroup ↥(X ⊔ H) :=
  N.comap (X ⊔ H).subtype

/-- The direct H-indexed target's copy inside XH. -/
abbrev DirectLocal : Subgroup ↥(X ⊔ H) :=
  H.subgroupOf (X ⊔ H)

/-- The existing relative normalizer's actual inclusion into N. -/
def normalizerInclusion : LocalNormalizer X H N →* N where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The direct H's actual inclusion into N. -/
def directInclusion (hHN : H ≤ N) : DirectLocal X H →* N where
  toFun x := ⟨x.1.1, hHN x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

variable [X.Normal]

/-- The product comparison uses only normality of X and the stated interval
X ∩ N ≤ H ≤ N. No normality of H or N is required. -/
theorem join_inf_eq (hXN : X ⊓ N ≤ H) (hHN : H ≤ N) :
    (X ⊔ H) ⊓ N = H := by
  apply le_antisymm
  · intro z hz
    obtain ⟨x, hx, h, hh, hprod⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hz.1
    have hprodN : x * h ∈ N := by
      rw [hprod]
      exact hz.2
    have hxN : x ∈ N := by
      have hcancel := N.mul_mem hprodN (N.inv_mem (hHN hh))
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hcancel
    rw [← hprod]
    exact H.mul_mem (hXN ⟨hx, hxN⟩) hh
  · exact le_inf le_sup_right hHN

/-- A separate conditional Frattini/Dedekind step for every J containing X.
The full factorization X ⊔ N = top is an explicit group premise; later
applications must derive it from their actual matched radical orbit. -/
theorem intermediate_eq_join_inf (J : Subgroup A) (hXJ : X ≤ J)
    (hcover : X ⊔ N = ⊤) : J = X ⊔ (J ⊓ N) := by
  apply le_antisymm
  · intro z hzJ
    have hz : z ∈ X ⊔ N := by
      rw [hcover]
      exact Subgroup.mem_top z
    obtain ⟨x, hx, n, hn, hprod⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hz
    have hnJ : n ∈ J := by
      have hcancel := J.mul_mem (J.inv_mem (hXJ hx)) hzJ
      rw [← hprod] at hcancel
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using hcancel
    rw [← hprod]
    exact Subgroup.mul_mem_sup hx ⟨hnJ, hn⟩
  · exact sup_le hXJ inf_le_left

/-- Equality in the actual lattice of subgroups of XH. -/
theorem localNormalizer_eq (hXN : X ⊓ N ≤ H) (hHN : H ≤ N) :
    LocalNormalizer X H N = DirectLocal X H := by
  ext x
  change x.1 ∈ N ↔ x.1 ∈ H
  constructor
  · intro hx
    have h : x.1 ∈ (X ⊔ H) ⊓ N := ⟨x.2, hx⟩
    rw [join_inf_eq X H N hXN hHN] at h
    exact h
  · intro hx
    exact hHN hx

/-- The comparison keeps the same element of XH; only its membership
certificate changes. This exposes coordinates without relying on casts. -/
def localEquiv (hXN : X ⊓ N ≤ H) (hHN : H ≤ N) :
    LocalNormalizer X H N ≃* DirectLocal X H where
  toFun x := ⟨x.1, by
    have hx : x.1.1 ∈ (X ⊔ H) ⊓ N := ⟨x.1.2, x.2⟩
    rw [join_inf_eq X H N hXN hHN] at hx
    exact hx⟩
  invFun x := ⟨x.1, hHN x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem localEquiv_coe (hXN : X ⊓ N ≤ H) (hHN : H ≤ N)
    (x : LocalNormalizer X H N) :
    (localEquiv X H N hXN hHN x).1 = x.1 := rfl

@[simp]
theorem localEquiv_symm_coe (hXN : X ⊓ N ≤ H) (hHN : H ≤ N)
    (x : DirectLocal X H) :
    ((localEquiv X H N hXN hHN).symm x).1 = x.1 := rfl

/-- The two maps into the actual global intermediate group agree. -/
theorem localEquiv_global_square (hXN : X ⊓ N ≤ H) (hHN : H ≤ N) :
    (DirectLocal X H).subtype.comp
        (localEquiv X H N hXN hHN).toMonoidHom =
      (LocalNormalizer X H N).subtype := by
  ext x
  rfl

/-- The two maps into the actual ambient normalizer agree. -/
theorem localEquiv_local_square (hXN : X ⊓ N ≤ H) (hHN : H ≤ N) :
    (directInclusion X H N hHN).comp
        (localEquiv X H N hXN hHN).toMonoidHom =
      normalizerInclusion X H N := by
  ext x
  rfl

/-- The comparison with H itself also retains its original A-coordinate. -/
def localEquivOriginal (hXN : X ⊓ N ≤ H) (hHN : H ≤ N) :
    LocalNormalizer X H N ≃* H :=
  (localEquiv X H N hXN hHN).trans
    (Subgroup.subgroupOfEquivOfLe (show H ≤ X ⊔ H from le_sup_right))

@[simp]
theorem localEquivOriginal_coe (hXN : X ⊓ N ≤ H) (hHN : H ≤ N)
    (x : LocalNormalizer X H N) :
    (localEquivOriginal X H N hXN hHN x : A) = x.1.1 := rfl

/-- When Q lies in X, this is the internal normalizer N_(XH)(Q), not just
a notation for an intersection in A. -/
theorem internalNormalizer_eq (Q : Subgroup A) (hQX : Q ≤ X)
    (hXN : X ⊓ Subgroup.normalizer (Q : Set A) ≤ H)
    (hHN : H ≤ Subgroup.normalizer (Q : Set A)) :
    Subgroup.normalizer
        (Q.subgroupOf (X ⊔ H) : Set ↥(X ⊔ H)) =
      DirectLocal X H := by
  rw [← Subgroup.subgroupOf_normalizer_eq (hQX.trans le_sup_left)]
  exact localNormalizer_eq X H (Subgroup.normalizer (Q : Set A)) hXN hHN

end Groups

section QuotientPresentation

variable {P : Definition35Problem.{u}}
variable {reference psi : Definition35Brauer P}
variable {w : Definition35Weight P}
variable {quotient : CentralQuotientBrauerSource P reference psi}
variable (ambient : SpathAmbientGroup P reference psi quotient)
variable (H : Subgroup ambient.A)
variable (hXN : ambient.base ⊓
  AmbientLocalGroup P reference psi w quotient ambient ≤ H)
variable (hHN : H ≤ AmbientLocalGroup P reference psi w quotient ambient)

include hXN hHN in
/-- The exact J-indexed local subgroup stored by the relative witness
inside TypeBFullBlockCondition, with J = base ⊔ H. -/
theorem quotientIntermediate_eq :
    IntermediateLocalNormalizer (w := w) ambient (ambient.base ⊔ H) =
      H.subgroupOf (ambient.base ⊔ H) :=
  localNormalizer_eq ambient.base H
    (AmbientLocalGroup P reference psi w quotient ambient) hXN hHN

/-- No quotient radical, own character or ambient copy is changed. -/
def quotientIntermediateEquiv :
    IntermediateLocalNormalizer (w := w) ambient (ambient.base ⊔ H) ≃*
      H.subgroupOf (ambient.base ⊔ H) :=
  localEquiv ambient.base H
    (AmbientLocalGroup P reference psi w quotient ambient) hXN hHN

/-- Exact compatibility with the relative target's named local inclusion. -/
theorem quotientIntermediate_local_square :
    (directInclusion ambient.base H
        (AmbientLocalGroup P reference psi w quotient ambient) hHN).comp
        (quotientIntermediateEquiv ambient H hXN hHN).toMonoidHom =
      intermediateLocalToAmbientLocal (w := w) ambient (ambient.base ⊔ H) := by
  ext x
  rfl

/-- Exact compatibility with the subgroup used by BlockInducesTo. -/
theorem quotientIntermediate_global_square :
    (H.subgroupOf (ambient.base ⊔ H)).subtype.comp
        (quotientIntermediateEquiv ambient H hXN hHN).toMonoidHom =
      (IntermediateLocalNormalizer (w := w) ambient
        (ambient.base ⊔ H)).subtype := by
  ext x
  rfl

end QuotientPresentation

section OddTwoPresentation

open CharacterWeight OddTwoLiteralSpathTarget

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : OddTwoLiteralSpathTarget.Problem n F)
variable {psi : IBr P.iota} (ambient : P.Ambient psi)
variable (Q : RadicalSubgroup (p := 2) (G := OddTwoLiteralSpathTarget.X n F))
variable (H : Subgroup ambient.A)
variable (hXN : ambient.base ⊓ P.LocalGroup ambient Q ≤ H)
variable (hHN : H ≤ P.LocalGroup ambient Q)

include hXN hHN in
/-- The exact direct-H subgroup in the accepted odd-two literal target. -/
theorem oddTwoIntermediate_eq :
    (P.LocalGroup ambient Q).comap (ambient.base ⊔ H).subtype =
      P.IntermediateLocal ambient H :=
  localNormalizer_eq ambient.base H (P.LocalGroup ambient Q) hXN hHN

def oddTwoIntermediateEquiv :
    (P.LocalGroup ambient Q).comap (ambient.base ⊔ H).subtype ≃*
      P.IntermediateLocal ambient H :=
  localEquiv ambient.base H (P.LocalGroup ambient Q) hXN hHN

/-- Both local inclusions into N_A(Qbar) use the same ambient element. -/
theorem oddTwoIntermediate_local_square :
    (P.intermediateLocalMap ambient Q H hHN).comp
        (oddTwoIntermediateEquiv P ambient Q H hXN hHN).toMonoidHom =
      normalizerInclusion ambient.base H (P.LocalGroup ambient Q) := by
  ext x
  rfl

/-- Both global inclusions into Xbar H use the same element. -/
theorem oddTwoIntermediate_global_square :
    (P.IntermediateLocal ambient H).subtype.comp
        (oddTwoIntermediateEquiv P ambient Q H hXN hHN).toMonoidHom =
      ((P.LocalGroup ambient Q).comap
        (ambient.base ⊔ H).subtype).subtype := by
  ext x
  rfl

end OddTwoPresentation

end ModularRep.PaperProofs.TypeCIntermediateNormalizerComparison


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
