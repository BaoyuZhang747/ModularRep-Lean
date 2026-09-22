import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBCentralKernelInertia
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Actual automorphisms of the fixed central triple cover

Every automorphism of the existing literal `X` descends through its fixed
projection `q` to the same matrix `G3`. The construction uses surjectivity and
the equality of the kernel with the centre. Its projection square is proved
on actual group elements.

The one additional source statement identifies automorphisms of this exact
matrix `G3` with conjugation by the actual `SO` carrier. Malle--Testerman,
Theorem 24.24 pp.216--217 gives automorphism generation, with the perfectness
scope of Theorem 24.17 p.213. The adjoint type B3 identification with SO
(Table 9.2 p.72), the trivial field part over F3 (16.5 and the definitions
preceding 24.24), and the absence of B3 graph automorphisms (Table 11.1 p.89;
the Coxeter exceptions in Remark 11.13 do not include B3) give the specialized
source statement. Authentication of this specialization and its literal
matrix, derived-subgroup, inclusion and action realization remains E1/U; no
source inhabitant is supplied here.

The final deduction realizes every actual upstairs opposite automorphism by
a compatible SO actor. The inverse of the source-provided SO element is used
to preserve the existing `conjugationOp` convention. There are no character,
weight, correspondence, or universal-prime-to-two-cover assumptions here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms

open TypeBQ3TripleCoverCarrier
open TypeBCentralKernelCarriers TypeBCentralKernelInertia

/-- The narrowly specialized automorphism theorem on the same matrix group.
The source identification with this actual conjugation action remains E1/U. -/
structure MatrixAutomorphismSource : Prop where
  realizes : ∀ beta : MulAut G3,
    ∃ h : TypeBRankThreePrincipalCountBinding.H (ZMod 3),
      originalAction (TypeBRankThreePrincipalCountBinding.G (ZMod 3)) h = beta

variable (source : MatrixExceptionalSource)
variable (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

/-- Canonical descent through the kernel quotient of the fixed projection. -/
def descendAutomorphism (alpha : MulAut X) : MulAut G3 :=
  let hmap : (q source freeSource).ker.map alpha.toMonoidHom =
      (q source freeSource).ker := by
    rw [q_kernel_eq_center source freeSource]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance alpha
  let e : X ⧸ (q source freeSource).ker ≃* G3 :=
    QuotientGroup.quotientKerEquivOfSurjective (q source freeSource)
      (q_surjective source freeSource)
  let aQ := QuotientGroup.congr (q source freeSource).ker
    (q source freeSource).ker alpha hmap
  e.symm.trans (aQ.trans e)

/-- The descended automorphism has the exact value prescribed by `q`. -/
theorem descendAutomorphism_apply_q (alpha : MulAut X) (x : X) :
    descendAutomorphism source freeSource alpha (q source freeSource x) =
      q source freeSource (alpha x) := by
  let e : X ⧸ (q source freeSource).ker ≃* G3 :=
    QuotientGroup.quotientKerEquivOfSurjective (q source freeSource)
      (q_surjective source freeSource)
  have he : e (QuotientGroup.mk x) = q source freeSource x := rfl
  have hes : e.symm (q source freeSource x) = QuotientGroup.mk x := by
    rw [← he, e.symm_apply_apply]
  have hmap : (q source freeSource).ker.map alpha.toMonoidHom =
      (q source freeSource).ker := by
    rw [q_kernel_eq_center source freeSource]
    exact Subgroup.characteristic_iff_map_eq.mp inferInstance alpha
  change e
    (QuotientGroup.congr (q source freeSource).ker (q source freeSource).ker
      alpha hmap (e.symm (q source freeSource x))) =
        q source freeSource (alpha x)
  rw [hes]
  rfl

/-- Every actual upstairs opposite automorphism has a compatible actual SO
actor, in exactly the convention of the accepted principal correspondence. -/
theorem exists_SO_actor (automorphisms : MatrixAutomorphismSource)
    (alpha : (MulAut X)ᵐᵒᵖ) :
    ∃ h : TypeBRankThreePrincipalCountBinding.H (ZMod 3), ∀ x : X,
      q source freeSource (alpha.unop x) =
        (conjugationOp (TypeBRankThreePrincipalCountBinding.G (ZMod 3)) h).unop
          (q source freeSource x) := by
  obtain ⟨h, hh⟩ := automorphisms.realizes
    (descendAutomorphism source freeSource alpha.unop)
  refine ⟨h⁻¹, ?_⟩
  intro x
  change q source freeSource (alpha.unop x) =
    originalAction (TypeBRankThreePrincipalCountBinding.G (ZMod 3))
      ((h⁻¹)⁻¹) (q source freeSource x)
  rw [inv_inv, hh]
  exact (descendAutomorphism_apply_q source freeSource alpha.unop x).symm

end ModularRep.PaperProofs.TypeBQ3TripleCoverAutomorphisms


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
