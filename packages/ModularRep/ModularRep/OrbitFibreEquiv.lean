import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Equiv.Basic

/-!
# Representatives over a fixed support and orbit fibres

Suppose that a group acts on a type of objects and on a type of supports.
If the support map is equivariant and every element fixing an object's
support also fixes the object, then representatives with one fixed support
are equivalent to the corresponding fibre on orbit spaces.

The construction is independent of representation theory. It uses only the
two orbit quotients and the stated stabiliser condition.
-/

noncomputable section

namespace ModularRep.OrbitFibre

universe uG uW uS

variable {G : Type uG} {W : Type uW} {S : Type uS}
variable [Group G] [MulAction G W] [MulAction G S]

/-- An equivariant support map for which the stabiliser of an object's
support fixes the object itself. -/
structure Data where
  support : W → S
  support_smul :
    ∀ (g : G) (w : W), support (g • w) = g • support w
  support_stabilizer_fixes :
    ∀ (g : G) (w : W), g • support w = support w → g • w = w

namespace Data

variable (D : Data (G := G) (W := W) (S := S))

/-- The support map on orbit spaces. -/
def orbitMap :
    MulAction.orbitRel.Quotient G W →
      MulAction.orbitRel.Quotient G S :=
  Quotient.map D.support (by
    intro x y hxy
    rcases hxy with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    calc
      g • D.support y = D.support (g • y) :=
        (D.support_smul g y).symm
      _ = D.support x := congrArg D.support hg)

/-- Objects with the chosen literal support. -/
abbrev FixedFibre (s : S) :=
  {w : W // D.support w = s}

/-- Orbits whose support orbit is represented by the chosen support. -/
abbrev OrbitMapFibre (s : S) :=
  {c : MulAction.orbitRel.Quotient G W //
    D.orbitMap c =
      (Quotient.mk'' s : MulAction.orbitRel.Quotient G S)}

/-- Send a representative with support `s` to its orbit. -/
def toOrbitFibre (s : S) :
    D.FixedFibre s → D.OrbitMapFibre s :=
  fun w ↦ ⟨Quotient.mk'' w.1, by
    change
      (Quotient.mk'' (D.support w.1) :
        MulAction.orbitRel.Quotient G S) = Quotient.mk'' s
    exact congrArg
      (fun t : S ↦
        (Quotient.mk'' t : MulAction.orbitRel.Quotient G S))
      w.2⟩

/-- Two representatives with support `s` determine the same orbit only when
they are equal. -/
theorem toOrbitFibre_injective (s : S) :
    Function.Injective (D.toOrbitFibre s) := by
  intro x y hxy
  apply Subtype.ext
  have hquot :
      (Quotient.mk'' x.1 : MulAction.orbitRel.Quotient G W) =
        Quotient.mk'' y.1 :=
    congrArg Subtype.val hxy
  obtain ⟨g, hg⟩ := Quotient.exact hquot
  have hsupport : g • D.support y.1 = D.support y.1 := by
    calc
      g • D.support y.1 = D.support (g • y.1) :=
        (D.support_smul g y.1).symm
      _ = D.support x.1 := congrArg D.support hg
      _ = s := x.2
      _ = D.support y.1 := y.2.symm
  exact hg.symm.trans (D.support_stabilizer_fixes g y.1 hsupport)

/-- Every orbit over the orbit of `s` has a unique representative with
literal support `s`. -/
theorem toOrbitFibre_surjective (s : S) :
    Function.Surjective (D.toOrbitFibre s) := by
  intro c
  let w : W := c.1.out
  have hout :
      (Quotient.mk'' w : MulAction.orbitRel.Quotient G W) = c.1 :=
    Quotient.out_eq c.1
  have hclass :
      (Quotient.mk'' (D.support w) :
        MulAction.orbitRel.Quotient G S) = Quotient.mk'' s := by
    calc
      (Quotient.mk'' (D.support w) :
          MulAction.orbitRel.Quotient G S) =
          D.orbitMap (Quotient.mk'' w) := rfl
      _ = D.orbitMap c.1 := congrArg D.orbitMap hout
      _ = Quotient.mk'' s := c.2
  obtain ⟨g, hg⟩ := Quotient.exact hclass
  have hw : D.support (g⁻¹ • w) = s := by
    calc
      D.support (g⁻¹ • w) = g⁻¹ • D.support w :=
        D.support_smul g⁻¹ w
      _ = g⁻¹ • (g • s) := congrArg (fun t ↦ g⁻¹ • t) hg.symm
      _ = s := inv_smul_smul g s
  let x : D.FixedFibre s := ⟨g⁻¹ • w, hw⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change (Quotient.mk'' (g⁻¹ • w) :
    MulAction.orbitRel.Quotient G W) = c.1
  calc
    (Quotient.mk'' (g⁻¹ • w) :
        MulAction.orbitRel.Quotient G W) = Quotient.mk'' w :=
      MulAction.orbitRel.Quotient.quotient_smul_eq
    _ = c.1 := hout

/-- Representatives with fixed support are equivalent to the corresponding
fibre on orbit spaces. -/
def fixedEquivOrbitFibre (s : S) :
    D.FixedFibre s ≃ D.OrbitMapFibre s :=
  Equiv.ofBijective (D.toOrbitFibre s)
    ⟨D.toOrbitFibre_injective s, D.toOrbitFibre_surjective s⟩

@[simp]
theorem fixedEquivOrbitFibre_apply_val
    (s : S) (w : D.FixedFibre s) :
    (D.fixedEquivOrbitFibre s w).1 =
      (Quotient.mk'' w.1 : MulAction.orbitRel.Quotient G W) :=
  rfl

end Data
end ModularRep.OrbitFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
