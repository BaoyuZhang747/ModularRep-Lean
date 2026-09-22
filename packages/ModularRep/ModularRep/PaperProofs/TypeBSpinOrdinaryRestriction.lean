import ModularRep.PaperProofs.TypeBSpinPrincipalProjectiveBinding
import ModularRep.PaperProofs.TypeBSpinInnerClassActions

/-!
# Actual ordinary restriction from special Clifford to Spin

Occurrence is the nonzero ordinary scalar product on the literal Spin
subgroup, using the same K-valued character functions. Simultaneous
automorphism pullback preserves it by finite-sum reindexing. Ambient inner
conjugation fixes the upper character, so diagonal transport needs no
source naturality premise. Field transport uses the actual inclusion square.

No splitting, ordinary algebraic-closure, rational-series, multiplicity or
character-correspondence source is supplied in this file. The interpretation
of this scalar product as an ordinary constituent uses the usual splitting
scope at its later published-source application.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinOrdinaryRestriction

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinPrincipalProjectiveBinding (scalarProductRight scalarProductRight_apply)

variable {n : ℕ} {F K : Type} [Field F] [Field K] [CharZero K]
  (N : NormSource n F) [Finite (Spin n F N)]

/-- Restrict the actual ordinary character along the literal norm-kernel
subgroup inclusion, without choosing a constituent or a representation. -/
def restrictionClassFunction (Phi : Irr K (SpecialClifford n F)) : Spin n F N → K :=
  fun x => Phi ((SpinSubgroup n F N).subtype x)

@[simp]
theorem restrictionClassFunction_apply (Phi : Irr K (SpecialClifford n F))
    (x : Spin n F N) : restrictionClassFunction N Phi x = Phi x.val := rfl

/-- Actual ordinary occurrence, expressed by the literal nonzero scalar
product. No free occurrence relation or selected-family predicate is used. -/
def occurs (Phi : Irr K (SpecialClifford n F)) (theta : Irr K (Spin n F N)) : Prop :=
  scalarProductRight theta.val (restrictionClassFunction N Phi) ≠ 0

/-- The existing scalar-product formula is invariant under reindexing.
This elementary version avoids unrelated splitting/finiteness assumptions
retained in an older Fourier-projection section's twist theorem. -/
theorem scalarProductRight_pullback (beta : MulAut (Spin n F N))
    (x y : Spin n F N → K) :
    scalarProductRight (fun g => x (beta g)) (fun g => y (beta g)) =
      scalarProductRight x y := by
  classical
  letI : Fintype (Spin n F N) := Fintype.ofFinite _
  simp only [scalarProductRight_apply, map_inv]
  congr 1
  exact beta.toEquiv.sum_comp (fun g => x g⁻¹ * y g)

/-- Actual restriction commutes with a pair of automorphisms satisfying the
literal inclusion square. -/
theorem restrictionClassFunction_twist (Phi : Irr K (SpecialClifford n F))
    (alpha : MulAut (SpecialClifford n F)) (beta : MulAut (Spin n F N))
    (square : ∀ x : Spin n F N, (beta x).val = alpha x.val) :
    restrictionClassFunction N (twist K (SpecialClifford n F) Phi alpha) =
      fun x => restrictionClassFunction N Phi (beta x) := by
  funext x
  change Phi (alpha x.val) = Phi (beta x).val
  exact congrArg Phi (square x).symm

/-- Nonzero restriction scalar products are preserved by simultaneous
pullback through an actual compatible ambient/subgroup automorphism pair. -/
theorem occurs_twist (Phi : Irr K (SpecialClifford n F))
    (theta : Irr K (Spin n F N))
    (alpha : MulAut (SpecialClifford n F)) (beta : MulAut (Spin n F N))
    (square : ∀ x : Spin n F N, (beta x).val = alpha x.val) :
    occurs N (twist K (SpecialClifford n F) Phi alpha)
      (twist K (Spin n F N) theta beta) ↔ occurs N Phi theta := by
  unfold occurs
  rw [restrictionClassFunction_twist N Phi alpha beta square]
  change scalarProductRight (fun x => theta (beta x))
      (fun x => restrictionClassFunction N Phi (beta x)) ≠ 0 ↔ _
  rw [scalarProductRight_pullback]

/-- Diagonal conjugation on Spin preserves occurrence in the SAME upper
character, since ordinary characters are ambient class functions. -/
theorem occurs_diagonal (Phi : Irr K (SpecialClifford n F))
    (theta : Irr K (Spin n F N)) (g : SpecialClifford n F) :
    occurs N Phi
      (twist K (Spin n F N) theta (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)) ↔
        occurs N Phi theta := by
  have h := occurs_twist N Phi theta (MulAut.conj g⁻¹)
    (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) (fun _ => rfl)
  simpa only [TypeBSpinInnerClassActions.ordinaryTwist_inner] using h

section Field

variable {p f : ℕ} [Finite F] [CharP F p]
  {parameters : OddFieldParameters F p f}

/-- Positive field action on characters is inverse pullback on both the
actual ambient and Spin carriers, with their inclusion square proved. -/
theorem occurs_field (fs : FieldActionSource n F p f parameters N)
    (Phi : Irr K (SpecialClifford n F)) (theta : Irr K (Spin n F N))
    (e : FieldGroup f) :
    occurs N (twist K (SpecialClifford n F) Phi (fs.action e⁻¹))
      (twist K (Spin n F N) theta (spinFieldAction n F fs e⁻¹)) ↔ occurs N Phi theta :=
  occurs_twist N Phi theta (fs.action e⁻¹) (spinFieldAction n F fs e⁻¹)
    (fun x => spinFieldAction_coe n F fs e⁻¹ x)

end Field

end ModularRep.PaperProofs.TypeBSpinOrdinaryRestriction


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
