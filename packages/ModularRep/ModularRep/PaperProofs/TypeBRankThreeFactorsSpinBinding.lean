import ModularRep.PaperProofs.TypeBRankThreeFactorsPointSource

/-!
# The original finite derived Levi inside the literal Spin group

The same geometric derived subgroup and Clifford base-change inclusion are
retained. Its inclusion in the geometric Spin subgroup follows from the
computed primal Levi. The existing norm-compatible Spin membership theorem
then descends this inclusion to the finite field. Restricting the carrier
uses only the standard subgroup equivalence and preserves ambient values.
No additional geometric, finite group or representation source is required.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeFactorsSpinBinding

open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBRegularLeviRationalCarriers TypeBRankThreeFactorsPointSource

variable {A F : Type} [Field A] [Field F] [Finite F]
variable {Nbar : NormSource 3 A} {Lstar : Subgroup (PCSp A 3)}
variable (chart : PairedChart Nbar Lstar) (Frob : MulAut (SpecialClifford 3 A))
variable (p f : ℕ) [CharP F p] [Algebra F A] (N : NormSource 3 F)
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)

theorem finiteDerived_le_spin :
    finiteDerived chart Frob p f N points ≤ SpinSubgroup 3 F N := by
  intro g hg
  apply (inclusion_spin_iff 3 p f F A N Nbar Frob points g).mp
  change points.inclusion g ∈ derivedLevi chart.primalLevi at hg
  exact chart.primalLevi_le_spin (derivedLevi_le chart.primalLevi hg)

/-- The actual finite subgroup of the original norm-kernel Spin carrier. -/
def actualSpinDerived : Subgroup (Spin 3 F N) :=
  (finiteDerived chart Frob p f N points).subgroupOf (SpinSubgroup 3 F N)

/-- The same rational derived group after restricting its finite carrier to Spin. -/
def actualSpinDerivedEquivL0 : actualSpinDerived chart Frob p f N points ≃*
    L0 Frob.toMonoidHom chart.primalLevi :=
  (Subgroup.subgroupOfEquivOfLe (finiteDerived_le_spin chart Frob p f N points)).trans
    (finiteDerivedEquivL0 chart Frob p f N points)

@[simp] theorem actualSpinDerivedEquivL0_value
    (x : actualSpinDerived chart Frob p f N points) :
    (actualSpinDerivedEquivL0 chart Frob p f N points x).val.val =
      points.inclusion x.val.val := rfl

end ModularRep.PaperProofs.TypeBRankThreeFactorsSpinBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
