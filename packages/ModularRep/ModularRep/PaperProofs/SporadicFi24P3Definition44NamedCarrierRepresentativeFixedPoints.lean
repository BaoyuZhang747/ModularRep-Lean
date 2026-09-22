import ModularRep.PaperProofs.CharacterWeightRepresentativeFibre
import ModularRep.PaperProofs.TypeBCentralKernelNormalizerInertia

/-! # Actual ordinary local fixedness and ambient weight-class fixedness -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints

open ModularRep ModularRep.CharacterWeight
open TypeBCentralKernelNormalizerInertia

universe u

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Fintype G]

def classAt (hp : p.Prime) (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  Quotient.mk'' (Quotient.mk'' (characterWeightAt hp Q theta))

theorem classAt_injective (hp : p.Prime) (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G)) :
    Function.Injective (classAt (K := K) hp Q) := by
  intro theta eta h
  apply (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q).injective
  apply Subtype.ext
  simpa only [classAt, localDefectZeroEquivWeightRadicalFibre_apply_val] using h

def localTwistAt (hp : p.Prime) (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) : LocalDefectZeroCharacter (K := K) Q :=
  ⟨castLocalCharacter stable ((characterWeightAt hp Q theta).rightTwist alpha).localCharacter,
    isDefectZero_castLocalCharacter stable ((characterWeightAt hp Q theta).rightTwist alpha).defectZero⟩

theorem characterWeightAt_localTwistAt (hp : p.Prime)
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    characterWeightAt hp Q (localTwistAt hp Q alpha stable theta) =
      (characterWeightAt hp Q theta).rightTwist alpha := by
  symm
  apply eq_of_isomorphic
  exact ⟨stable, rfl⟩

theorem classAt_localTwistAt (hp : p.Prime)
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    classAt hp Q (localTwistAt hp Q alpha stable theta) = MulOpposite.op alpha • classAt hp Q theta := by
  exact congrArg (fun W : CharacterWeight p K G =>
    (Quotient.mk'' (Quotient.mk'' W) : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G)))
      (characterWeightAt_localTwistAt hp Q alpha stable theta)

theorem classAt_fixed_iff_local_fixed (hp : p.Prime)
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    MulOpposite.op alpha • classAt hp Q theta = classAt hp Q theta ↔
      OrdinaryIrreducibleCharacter.twist K _ theta.1 (localAut Q.1 alpha stable) = theta.1 := by
  have hraw : MulOpposite.op alpha • classAt hp Q theta = classAt hp Q theta ↔
      (characterWeightAt hp Q theta).rightTwist alpha = characterWeightAt hp Q theta := by
    constructor
    · intro h
      have ht : localTwistAt hp Q alpha stable theta = theta :=
        classAt_injective hp Q ((classAt_localTwistAt hp Q alpha stable theta).trans h)
      exact (characterWeightAt_localTwistAt hp Q alpha stable theta).symm.trans
        (congrArg (characterWeightAt hp Q) ht)
    · intro h
      exact congrArg (fun W : CharacterWeight p K G =>
        (Quotient.mk'' (Quotient.mk'' W) :
          CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G))) h
  exact hraw.trans (rightTwist_eq_iff_local_fixed (characterWeightAt hp Q theta) alpha stable)

theorem localTwistAt_fixed_iff (hp : p.Prime)
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    localTwistAt hp Q alpha stable theta = theta ↔
      OrdinaryIrreducibleCharacter.twist K _ theta.1 (localAut Q.1 alpha stable) = theta.1 := by
  constructor
  · intro h
    apply (classAt_fixed_iff_local_fixed hp Q alpha stable theta).mp
    rw [← classAt_localTwistAt hp Q alpha stable theta, h]
  · intro h
    apply classAt_injective hp Q
    rw [classAt_localTwistAt]
    exact (classAt_fixed_iff_local_fixed hp Q alpha stable theta).mpr h

variable {k Block : Type u} [Field k]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

theorem localTwistAt_block (hp : p.Prime)
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1)
    (theta : LocalDefectZeroCharacter (K := K) Q) :
    S.operations.rawWeightBlock (characterWeightAt hp Q (localTwistAt hp Q alpha stable theta)) =
      MulOpposite.op alpha • S.operations.rawWeightBlock (characterWeightAt hp Q theta) := by
  rw [characterWeightAt_localTwistAt]
  exact S.automorphism_transport alpha (characterWeightAt hp Q theta)

def fixedRepresentativeDZEquiv (hp : p.Prime)
    (S : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : CharacterWeight.RadicalSubgroup (p := p) (G := G)) (b : Block)
    (alpha : MulAut G) (stable : Q.1.comap alpha.toMonoidHom = Q.1) :
    {theta : RepresentativeDZ hp S Q b //
      OrdinaryIrreducibleCharacter.twist K _ theta.1.1 (localAut Q.1 alpha stable) = theta.1.1} ≃
    {w : WeightBlockRadicalFibre S Q b // MulOpposite.op alpha • w.1 = w.1} :=
  (representativeDZEquivWeightBlockRadicalFibre hp S Q b).subtypeEquiv (fun theta => by
    change OrdinaryIrreducibleCharacter.twist K _ theta.1.1 (localAut Q.1 alpha stable) = theta.1.1 ↔
      MulOpposite.op alpha • (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q theta.1).1 =
        (localDefectZeroEquivWeightRadicalFibre (K := K) hp Q theta.1).1
    simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt] using
      (classAt_fixed_iff_local_fixed hp Q alpha stable theta.1).symm)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
