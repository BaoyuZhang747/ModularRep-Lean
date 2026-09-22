import ModularRep.PaperProofs.TypeCWeightTensorFieldAction
import ModularRep.PaperProofs.TypeBCliffordCarriers

/-!
# The radical-kernel join for Type B quotient-character lifts

The ordinary lift of a modular quotient character has `ell'` order
(Navarro, *Characters and Blocks of Finite Groups*, Problem 2.7, p. 46,
with the compatible lift and root realization kept fixed). Every radical
`ell`-subgroup is an `ell`-group. The checked coprime-order argument below
therefore makes the chosen lift trivial on every radical subgroup, exactly
as required by the already constructed character-weight tensor action.

No order-two assertion about the special-Clifford/Spin quotient is used:
that quotient has order `q - 1`. Its effective diagonal quotient modulo
the scalar centre has order two, which is a different statement.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBRadicalLiftKernel

open ModularRep
open TypeCConformalActionAdapter TypeCWeightTensorFieldAction

universe u

section CoprimeKernel

variable {ell : ℕ} {G L : Type u} [Group G] [CommGroup L]

/-- A character of order prime to `ell` is trivial on every `ell`-subgroup.
Both divisibility statements concern the same evaluated group element. -/
theorem isPGroup_le_ker_of_order_coprime
    (chi : G →* L) (hchi : ell.Coprime (orderOf chi))
    (Q : Subgroup G) (hQ : IsPGroup ell Q) : Q ≤ chi.ker := by
  intro g hg
  change chi g = 1
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes
    (hQ.orderOf_coprime hchi (⟨g, hg⟩ : Q))
    (orderOf_map_dvd (chi.comp Q.subtype) (⟨g, hg⟩ : Q))
    (orderOf_map_dvd (MonoidHom.eval g) chi)

end CoprimeKernel

section ExactLift

variable {ell : ℕ} {K k G E : Type u}
variable [Field K] [CharZero K] [Field k] [CharP k ell] [IsAlgClosed k]
variable [Group G] [Finite G] [Group E]
variable (G0 : Subgroup G) [G0.Normal]
variable (field : E →* MulAut G)
variable (hinvariant : FieldInvariantSubgroup.IsInvariant G0 field)
variable (D : OrdinaryReductionEquiv (k := k) (K := K) G0 field hinvariant)

/-- The source assumption concerns only the order of this exact compatible
ordinary lift. The radical-kernel conclusion is a deduction, not an input. -/
def radicalKernelLiftInput_of_primeToOrder
    (liftPrimeTo : ∀ lambda : TensorCharacters (k := k) G0,
      ell.Coprime (orderOf (OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda))) :
    RadicalKernelLiftInput (p := ell) G0 field hinvariant D where
  lift_trivial lambda Q hQ :=
    isPGroup_le_ker_of_order_coprime
      (OrdinaryReductionEquiv.lift
        (G0 := G0) (field := field) (hinvariant := hinvariant) D lambda)
      (liftPrimeTo lambda) Q hQ.isPGroup

end ExactLift

section LiteralSpecialClifford

open TypeBCliffordCarriers

variable {n p f ell : ℕ} [NeZero f]
variable {F K k : Type}
variable [Field F] [Finite F] [CharP F p] [Finite (Clifford n F)]
variable [Field K] [CharZero K] [Field k] [CharP k ell] [IsAlgClosed k]
variable (parameters : OddFieldParameters F p f) (N : NormSource n F)
variable (fs : FieldActionSource n F p f parameters N)

/-- The factory on the literal norm-one Spin subgroup of the same special
Clifford carrier, with the same field action and compatible lift. -/
def specialCliffordRadicalKernel
    (D : OrdinaryReductionEquiv (k := k) (K := K)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs))
    (liftPrimeTo : ∀ lambda : TensorCharacters (k := k) (SpinSubgroup n F N),
      ell.Coprime (orderOf (OrdinaryReductionEquiv.lift
        (G0 := SpinSubgroup n F N) (field := fs.action)
        (hinvariant := field_spinSubgroup_map n F fs) D lambda))) :
    RadicalKernelLiftInput (p := ell)
      (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D :=
  radicalKernelLiftInput_of_primeToOrder
    (SpinSubgroup n F N) fs.action (field_spinSubgroup_map n F fs) D liftPrimeTo

end LiteralSpecialClifford

end ModularRep.PaperProofs.TypeBRadicalLiftKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
