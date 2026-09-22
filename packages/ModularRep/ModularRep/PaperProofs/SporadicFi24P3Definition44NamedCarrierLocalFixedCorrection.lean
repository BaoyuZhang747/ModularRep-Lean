import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection

/-! # Local ordinary fixedness is independent of the stabilizing inner correction -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalFixedCorrection

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection

universe u

theorem local_fixed_iff_of_innerCorrections
    {p : ℕ} {K G : Type u} [Field K] [CharZero K] [Group G] [Fintype G]
    (hp : p.Prime) (Q : RadicalSubgroup (p := p) (G := G)) (tau : MulAut G) (g h : G)
    (stableG : Q.1.comap (tau * MulAut.conj g).toMonoidHom = Q.1)
    (stableH : Q.1.comap (tau * MulAut.conj h).toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    OrdinaryIrreducibleCharacter.twist K _ theta.1
        (localAut Q.1 (tau * MulAut.conj g) stableG) = theta.1 ↔
      OrdinaryIrreducibleCharacter.twist K _ theta.1
        (localAut Q.1 (tau * MulAut.conj h) stableH) = theta.1 := by
  have hg := classAt_fixed_iff_local_fixed hp Q (tau * MulAut.conj g) stableG theta
  have hh := classAt_fixed_iff_local_fixed hp Q (tau * MulAut.conj h) stableH theta
  rw [innerCorrection_weight_smul] at hg hh
  exact hg.symm.trans hh

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalFixedCorrection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
