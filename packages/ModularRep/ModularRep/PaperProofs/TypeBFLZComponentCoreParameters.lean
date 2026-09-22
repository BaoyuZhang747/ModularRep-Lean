import ModularRep.PaperProofs.TypeBFLZPolynomialComponents
import ModularRep.PaperProofs.TypeBFLZSymbolCarriers
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Prime.Basic

/-!
# Core parameters on the actual centralizer component field

For an F0 polynomial Gamma the symplectic component field has size
Q_Gamma = q^(degree Gamma). The mode is hooks when ord_ell(Q_Gamma) is odd,
and cohooks when it is even. The removal length is ord_ell(Q_Gamma^2).
The order-square identity gives exactly D or D/2 as appropriate.

This component-relative interpretation uses GM Corollaries 4.4.18 and
4.6.16, together with FLZ Lemma 3.1 and equation (6.1). The globally worded
line in FLZ Section 4.1 is ambiguous for nonsquare multipliers; the separate
source audit records that issue rather than treating it as an exact proof.
No character, centralizer decomposition or block certificate is assumed here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZComponentCoreParameters

open TypeBFLZCoreProfileConjugacy TypeBFLZPolynomialComponents
open TypeBFLZSymbolCarriers

universe u v

/-- The ordinary order calculation behind the published hook/cohook split. -/
theorem orderOf_square {M : Type v} [Monoid M] (x : M) :
    orderOf (x ^ 2) = if Odd (orderOf x) then orderOf x else orderOf x / 2 := by
  rw [orderOf_pow' x (by decide : (2 : ℕ) ≠ 0)]
  by_cases h : Odd (orderOf x)
  · have hg : Nat.gcd (orderOf x) 2 = 1 := Nat.coprime_two_right.mpr h
    simp only [h, if_pos, hg, Nat.div_one]
  · have hd : 2 ∣ orderOf x := Nat.dvd_of_mod_eq_zero (Nat.not_odd_iff.mp h)
    simp [h, Nat.gcd_eq_right hd]

variable {F : Type u} [Field F] (ell : ℕ)

/-- The actual base-field cardinality in the residue ring, with no symbolic q. -/
def baseValue : ZMod ell := (Nat.card F : ZMod ell)

theorem baseValue_ne_zero (nondefining : ¬ ell ∣ Nat.card F) :
    baseValue (F := F) ell ≠ 0 :=
  (ZMod.natCast_eq_zero_iff (Nat.card F) ell).not.mpr nondefining

/-- The actual F0 centralizer component field size modulo ell. -/
def symbolBase (P : Profile F) (Gamma : ProfileComponent P) : ZMod ell :=
  baseValue (F := F) ell ^ Gamma.val.natDegree

def symbolOrder (P : Profile F) (Gamma : ProfileComponent P) : ℕ :=
  orderOf (symbolBase ell P Gamma)

def symbolLength (P : Profile F) (Gamma : ProfileComponent P) : ℕ :=
  orderOf (symbolBase ell P Gamma ^ 2)

def symbolKind (P : Profile F) (Gamma : ProfileComponent P) : RemovalKind :=
  if Odd (symbolOrder ell P Gamma) then .hook else .cohook

/-- On the actual component field the length is D for hooks and D/2 for
cohooks, without replacing the component field by the ambient one. -/
theorem symbolLength_formula (P : Profile F) (Gamma : ProfileComponent P) :
    symbolLength ell P Gamma =
      if Odd (symbolOrder ell P Gamma) then symbolOrder ell P Gamma
      else symbolOrder ell P Gamma / 2 :=
  orderOf_square (symbolBase ell P Gamma)

/-- The same e_Gamma is ord_ell(q^(2 degree Gamma)), as in FLZ4.1. -/
theorem symbolLength_fieldPower (P : Profile F) (Gamma : ProfileComponent P) :
    symbolLength ell P Gamma =
      orderOf (baseValue (F := F) ell ^ (2 * Gamma.val.natDegree)) := by
  unfold symbolLength symbolBase
  rw [← pow_mul, Nat.mul_comm Gamma.val.natDegree 2]

/-- For non-F0 components the sign is minus on F1 and plus on F2, and
the reduced degree is half of the literal polynomial degree. -/
def partitionBase (P : Profile F) (Gamma : ProfileComponent P) : ZMod ell := by
  classical
  exact if IsF1 P.1 Gamma.val then -(baseValue (F := F) ell ^ (Gamma.val.natDegree / 2))
    else baseValue (F := F) ell ^ (Gamma.val.natDegree / 2)

def partitionLength (P : Profile F) (Gamma : ProfileComponent P) : ℕ :=
  orderOf (partitionBase ell P Gamma)

variable [Fact ell.Prime]

theorem symbolLength_pos (nondefining : ¬ ell ∣ Nat.card F)
    (P : Profile F) (Gamma : ProfileComponent P) : 0 < symbolLength ell P Gamma := by
  have hz : symbolBase ell P Gamma ^ 2 ≠ 0 :=
    pow_ne_zero 2 (pow_ne_zero _ (baseValue_ne_zero ell nondefining))
  exact ((isUnit_iff_ne_zero.mpr hz).isOfFinOrder).orderOf_pos

theorem partitionBase_ne_zero (nondefining : ¬ ell ∣ Nat.card F)
    (P : Profile F) (Gamma : ProfileComponent P) : partitionBase ell P Gamma ≠ 0 := by
  have hz : baseValue (F := F) ell ^ (Gamma.val.natDegree / 2) ≠ 0 :=
    pow_ne_zero _ (baseValue_ne_zero ell nondefining)
  unfold partitionBase
  split_ifs
  · exact neg_ne_zero.mpr hz
  · exact hz

theorem partitionLength_pos (nondefining : ¬ ell ∣ Nat.card F)
    (P : Profile F) (Gamma : ProfileComponent P) : 0 < partitionLength ell P Gamma :=
  ((isUnit_iff_ne_zero.mpr (partitionBase_ne_zero ell nondefining P Gamma)).isOfFinOrder).orderOf_pos

end ModularRep.PaperProofs.TypeBFLZComponentCoreParameters


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
