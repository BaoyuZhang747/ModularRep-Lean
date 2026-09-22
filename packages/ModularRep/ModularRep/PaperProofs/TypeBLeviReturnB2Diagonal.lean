import ModularRep.PaperProofs.TypeBLeviReturnB2MatrixAction
import ModularRep.PaperProofs.TypeBLeviReturnB2Coefficient
import ModularRep.PaperProofs.TypeBFiniteFieldSquareClass
import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
The B2 separation deduction on actual matrix Sp4.

The finite odd-field square classes and scalar multipliers imply that every
projective conformal automorphism is inner or the displayed nonsquare
similitude followed by an inner automorphism. The only character source is
Feng--Malle, Corollary 4.6, on this same matrix group, root embedding, and
full prime-field subgroup. Its direct-twist convention is retained; inverse
pullback is handled inside the factorization proof. No involution identity
for the chosen diagonal automorphism is assumed.

This standard-factor result is a supporting deduction. The actual local
return and the original regular-overgroup projection square are supplied by
the separate original-carrier consumer, not replaced by a lift to CSp.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBLeviReturnB2Diagonal

open TypeBConformalDualCarriers TypeBFiniteFieldSquareClass
open TypeBLeviReturnB2MatrixAction TypeBLeviReturnB2Coefficient
open EvenFieldAssumption53Relative
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

universe u v w

variable (F : Type u) [Field F]

/-- Scale the first coordinate half by the specified unit. -/
def diagonalLinear (z : Fˣ) : SymplecticSpace F 2 ≃ₗ[F] SymplecticSpace F 2 :=
  LinearEquiv.prodCongr (LinearEquiv.smulOfUnit z)
    (LinearEquiv.refl F (Fin 2 → F))

/-- The literal similitude with multiplier z, before passing to any quotient. -/
def diagonalElement (z : Fˣ) : CSp F 2 :=
  ⟨(diagonalLinear F z, z), by
    intro v w
    change (∑ i : Fin 2,
      (((z : F) * v.1 i) * w.2 i - v.2 i * ((z : F) * w.1 i))) =
        (z : F) * ∑ i : Fin 2, (v.1 i * w.2 i - v.2 i * w.1 i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring⟩

@[simp] theorem multiplier_diagonalElement (z : Fˣ) :
    multiplier F 2 (diagonalElement F z) = z := rfl

@[simp] theorem diagonalElement_value (z : Fˣ) (v : SymplecticSpace F 2) :
    linearPart F 2 (diagonalElement F z) v =
      (fun i => (z : F) * v.1 i, v.2) := rfl

variable [Finite F]

/-- The actual unit chosen in the nontrivial square class. -/
def diagonalUnit (hOdd : Odd (Nat.card F)) : Fˣ :=
  Classical.choose (squareClassMap_surjective F hOdd
    (Multiplicative.ofAdd (1 : ZMod 2)))

theorem diagonalUnit_class (hOdd : Odd (Nat.card F)) :
    squareClassMap F hOdd (diagonalUnit F hOdd) =
      Multiplicative.ofAdd (1 : ZMod 2) :=
  Classical.choose_spec (squareClassMap_surjective F hOdd
    (Multiplicative.ofAdd (1 : ZMod 2)))

theorem diagonalUnit_not_square (hOdd : Odd (Nat.card F)) :
    ¬ ∃ z : Fˣ, z ^ 2 = diagonalUnit F hOdd := by
  rintro ⟨z, hz⟩
  have h := diagonalUnit_class F hOdd
  rw [← hz, squareClassMap_sq] at h
  exact (by decide : (1 : Multiplicative (ZMod 2)) ≠
    Multiplicative.ofAdd (1 : ZMod 2)) h

private theorem two_square_classes (a : Multiplicative (ZMod 2)) :
    a = 1 ∨ a = Multiplicative.ofAdd (1 : ZMod 2) := by
  change a.toAdd = 0 ∨ a.toAdd = 1
  generalize a.toAdd = t
  fin_cases t
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Every multiplier is a square or the chosen nonsquare times a square. -/
theorem multiplier_square_cases (hOdd : Odd (Nat.card F)) (a : Fˣ) :
    (∃ z : Fˣ, z ^ 2 = a) ∨
      ∃ z : Fˣ, z ^ 2 = (diagonalUnit F hOdd)⁻¹ * a := by
  rcases two_square_classes (squareClassMap F hOdd a) with ha | ha
  · exact Or.inl ((squareClassMap_eq_one_iff F hOdd a).mp ha)
  · apply Or.inr
    apply (squareClassMap_eq_one_iff F hOdd _).mp
    rw [map_mul, map_inv, diagonalUnit_class, ha, inv_mul_cancel]

/-- Square multiplier factors are actual kernel elements times scalars. -/
theorem exists_kernel_scalar (g : CSp F 2) (z : Fˣ)
    (hz : z ^ 2 = multiplier F 2 g) :
    ∃ x : Kernel F, g = x.val * scalar F 2 z := by
  have hx : g * (scalar F 2 z)⁻¹ ∈ (multiplier F 2).ker := by
    change multiplier F 2 (g * (scalar F 2 z)⁻¹) = 1
    rw [map_mul, map_inv, multiplier_scalar, ← hz, mul_inv_cancel]
  refine ⟨⟨g * (scalar F 2 z)⁻¹, hx⟩, ?_⟩
  simp

variable {F}

/-- The displayed diagonal action is computed from the nonsquare similitude. -/
def diagonalAut (coordinates : MatrixKernelSource F) (hOdd : Odd (Nat.card F)) :
    MulAut (Sp4 F) :=
  cspAction coordinates (diagonalElement F (diagonalUnit F hOdd))

theorem cspAction_inner_or_diagonal (coordinates : MatrixKernelSource F)
    (hOdd : Odd (Nat.card F)) (g : CSp F 2) :
    (∃ x : Sp4 F, cspAction coordinates g = MulAut.conj x) ∨
      ∃ x : Sp4 F,
        cspAction coordinates g = diagonalAut coordinates hOdd * MulAut.conj x := by
  rcases multiplier_square_cases F hOdd (multiplier F 2 g) with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨x, hx⟩ := exists_kernel_scalar F g z hz
    refine Or.inl ⟨kernelEquiv coordinates x, ?_⟩
    rw [hx, map_mul, cspAction_scalar, mul_one, cspAction_kernel]
  · let delta := diagonalElement F (diagonalUnit F hOdd)
    have hm : z ^ 2 = multiplier F 2 (delta⁻¹ * g) := by
      simpa only [map_mul, map_inv, multiplier_diagonalElement, delta] using hz
    obtain ⟨x, hx⟩ := exists_kernel_scalar F (delta⁻¹ * g) z hm
    have hg : g = delta * (x.val * scalar F 2 z) := by
      calc
        g = delta * (delta⁻¹ * g) := by simp
        _ = delta * (x.val * scalar F 2 z) := congrArg (fun y => delta * y) hx
    refine Or.inr ⟨kernelEquiv coordinates x, ?_⟩
    change cspAction coordinates g =
      cspAction coordinates delta * MulAut.conj (kernelEquiv coordinates x)
    rw [hg, map_mul, map_mul, cspAction_scalar, mul_one, cspAction_kernel]

/-- Quotient representatives suffice; no homomorphic section is required. -/
theorem pcspAction_inner_or_diagonal (coordinates : MatrixKernelSource F)
    (hOdd : Odd (Nat.card F)) (g : PCSp F 2) :
    (∃ x : Sp4 F, pcspAction coordinates g = MulAut.conj x) ∨
      ∃ x : Sp4 F,
        pcspAction coordinates g = diagonalAut coordinates hOdd * MulAut.conj x := by
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup F 2) g
  exact cspAction_inner_or_diagonal coordinates hOdd c

section Characters

variable {k : Type v} {K : Type w}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (coordinates : MatrixKernelSource F) (hOdd : Odd (Nat.card F))
variable (iota : PrimeRegularRootEmbedding 2 k K (Sp4 F))

private theorem twist_inner (chi : IBr iota) (x : Sp4 F) :
    IrreducibleBrauerCharacter.twist iota chi (MulAut.conj x) = chi := by
  apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
  exact PrimeRegularClassFunction.twist_conj chi.val x

/-- The character-action dichotomy is derived from the actual group factors. -/
theorem pcsp_twist_cases (g : PCSp F 2) (chi : IBr iota) :
    IrreducibleBrauerCharacter.twist iota chi (pcspAction coordinates g) = chi ∨
      IrreducibleBrauerCharacter.twist iota chi (pcspAction coordinates g) =
        IrreducibleBrauerCharacter.twist iota chi (diagonalAut coordinates hOdd) := by
  rcases pcspAction_inner_or_diagonal coordinates hOdd g with ⟨x, hx⟩ | ⟨x, hx⟩
  · apply Or.inl
    rw [hx]
    exact twist_inner iota chi x
  · apply Or.inr
    rw [hx, ← IrreducibleBrauerCharacter.twist_mul]
    exact twist_inner iota
      (IrreducibleBrauerCharacter.twist iota chi (diagonalAut coordinates hOdd)) x

variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- The full standard prime-field image, not an effective version of the
original return subgroup. -/
abbrev StandardField := Subgroup.zpowers (fieldGenerator F p)

/-- FM Corollary 4.6, p.10, with Section 3's actual matrix automorphisms.
This direct-twist source states separation only, on the specified root.
Its applicability to the fixed finite odd field is an E2/U obligation. -/
def FengMalleSeparation : Prop :=
  ∀ chi : IBr iota, ∀ sigma : StandardField (F := F) p,
    IrreducibleBrauerCharacter.twist iota chi (diagonalAut coordinates hOdd) =
        IrreducibleBrauerCharacter.twist iota chi (sigma : MulAut (Sp4 F)) →
      IrreducibleBrauerCharacter.twist iota chi (diagonalAut coordinates hOdd) = chi ∧
        IrreducibleBrauerCharacter.twist iota chi (sigma : MulAut (Sp4 F)) = chi

/-- Separation implies the complete standard product factorization at the
same character. The original-carrier application chooses this base itself. -/
theorem standard_product_factorization
    (separation : FengMalleSeparation coordinates hOdd iota p) (chi : IBr iota) :
    letI := rightAutomorphismAction iota (pcspAction coordinates)
    letI := rightAutomorphismAction iota (StandardField (F := F) p).subtype
    ProductStabilizerFactorization (D := PCSp F 2)
      (E := StandardField (F := F) p) chi := by
  letI := rightAutomorphismAction iota (pcspAction coordinates)
  letI := rightAutomorphismAction iota (StandardField (F := F) p).subtype
  intro d sigma
  constructor
  · intro hcombined
    have hrel : d⁻¹ • chi = sigma • chi := by
      have h := congrArg (fun z : IBr iota => d⁻¹ • z) hcombined
      simpa only [inv_smul_smul] using h.symm
    change IrreducibleBrauerCharacter.twist iota chi
      (pcspAction coordinates ((d⁻¹)⁻¹)) =
        IrreducibleBrauerCharacter.twist iota chi
          ((StandardField (F := F) p).subtype sigma⁻¹) at hrel
    rw [inv_inv] at hrel
    have hfield : sigma • chi = chi := by
      change IrreducibleBrauerCharacter.twist iota chi
        ((StandardField (F := F) p).subtype sigma⁻¹) = chi
      rcases pcsp_twist_cases coordinates hOdd iota d chi with hinner | hdiagonal
      · exact hrel.symm.trans hinner
      · exact (separation chi sigma⁻¹ (hdiagonal.symm.trans hrel)).2
    exact ⟨by simpa only [hfield] using hcombined, hfield⟩
  · rintro ⟨hdiagonal, hfield⟩
    rw [hfield, hdiagonal]

end Characters

end ModularRep.PaperProofs.TypeBLeviReturnB2Diagonal


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
