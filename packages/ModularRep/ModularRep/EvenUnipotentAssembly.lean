import ModularRep.EvenUnipotentCorrespondence
import ModularRep.IntegralBasicSetBridge
import ModularRep.PaperProofs.ConlonBasicSet

/-!
# Construction of a finite set bijection in the even-field unipotent proposition

This file formalises the manuscript-specific construction of a finite set bijection used in
Proposition 3.8.  It deliberately stops before the cyclic-outer BAW criterion:
that criterion still needs its full character-theoretic realisation.
-/

namespace ModularRep.ManuscriptVerification.EvenUnipotentAssembly

open ModularRep.IntegralBasicSetBridge
open ModularRep.PaperProofs.ConlonBasicSet
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence

universe uE uSource uMiddle uTarget uBlock uCharacter uLabel

variable {E : Type uE} {Source : Type uSource} {Middle : Type uMiddle}
  {Target : Type uTarget}

/-- The inverse of an equivariant equivalence is equivariant. -/
def equivariantEquivSymm
    {sourceAction : E → Source → Source}
    {targetAction : E → Target → Target}
    (D : EquivariantEquiv E Source Target sourceAction targetAction) :
    EquivariantEquiv E Target Source targetAction sourceAction where
  toEquiv := D.toEquiv.symm
  equivariant := by
    intro a y
    apply D.toEquiv.injective
    simpa only [Equiv.apply_symm_apply] using
      (D.equivariant a (D.toEquiv.symm y)).symm

/-- Equivariant equivalences compose in source-to-target order. -/
def equivariantEquivTrans
    {sourceAction : E → Source → Source}
    {middleAction : E → Middle → Middle}
    {targetAction : E → Target → Target}
    (D₁ : EquivariantEquiv E Source Middle sourceAction middleAction)
    (D₂ : EquivariantEquiv E Middle Target middleAction targetAction) :
    EquivariantEquiv E Source Target sourceAction targetAction where
  toEquiv := D₁.toEquiv.trans D₂.toEquiv
  equivariant := by
    intro a x
    rw [Equiv.trans_apply, D₁.equivariant, D₂.equivariant]
    rfl

/-- Equivariance for an ambient action restricts along any map of acting
parameters.  In the manuscript this is applied to the inclusion of `E_H` in
the ambient block stabiliser occurring in Feng--Malle--Zhang, Theorem 6.2. -/
def restrictEquivariantEquiv
    {Ambient : Type*}
    (restrictionMap : E → Ambient)
    {sourceAction : Ambient → Source → Source}
    {targetAction : Ambient → Target → Target}
    (D : EquivariantEquiv Ambient Source Target
      sourceAction targetAction) :
    EquivariantEquiv E Source Target
      (fun a x ↦ sourceAction (restrictionMap a) x)
      (fun a x ↦ targetAction (restrictionMap a) x) where
  toEquiv := D.toEquiv
  equivariant := fun a x ↦ D.equivariant (restrictionMap a) x

variable {Block : Type uBlock} {Character : Type uCharacter} [Group E]
  [MulAction E Block] [MulAction E Character]

/-- A nonempty pointwise fixed set of ambient character labels belonging to
one block forces that block to be fixed, provided taking the block of a
character is equivariant.  The use of an ambient set avoids assuming an action
on the block fibre before its stability has been proved. -/
theorem block_fixed_of_nonempty_pointwise_fixed_characters
    (blockOf : Character → Block) (C : Block) (X : Set Character)
    (X_nonempty : X.Nonempty)
    (blockOf_equivariant : ∀ (a : E) (chi : Character),
      blockOf (a • chi) = a • blockOf chi)
    (all_in_block : ∀ chi ∈ X, blockOf chi = C)
    (characters_fixed : ∀ (a : E) (chi : Character),
      chi ∈ X → a • chi = chi) :
    ∀ a : E, a • C = C := by
  intro a
  obtain ⟨chi, hchi⟩ := X_nonempty
  calc
    a • C = a • blockOf chi :=
      congrArg (a • ·) (all_in_block chi hchi).symm
    _ = blockOf (a • chi) := (blockOf_equivariant a chi).symm
    _ = blockOf chi := congrArg blockOf (characters_fixed a chi hchi)
    _ = C := all_in_block chi hchi

variable {IBr Basic GenericWeight AlperinWeight : Type uLabel}
  [Finite E]
  [MulAction E IBr] [MulAction E Basic]
  [MulAction E GenericWeight] [MulAction E AlperinWeight]
  [Finite Basic] [Finite IBr]

/-- If the free integral modules on two index types are linearly equivalent
and the target type is nonempty, then the source type is nonempty.  This
argument uses no group action, so it can establish nonemptiness of `X_C`
before the stability of `C` and the induced fibre actions are available. -/
theorem nonempty_basic_of_linearEquiv
    {Basic IBr : Type*} [Nonempty IBr]
    (d : MonoidAlgebra ℤ Basic ≃ₗ[ℤ] MonoidAlgebra ℤ IBr) :
    Nonempty Basic := by
  classical
  by_contra h
  let _ : IsEmpty Basic := not_nonempty_iff.mp h
  let y : IBr := Classical.choice inferInstance
  have hz : d.symm (MonoidAlgebra.single y 1) = 0 := by
    ext x
    exact isEmptyElim x
  have hs : MonoidAlgebra.single y (1 : ℤ) = 0 := by
    rw [← d.apply_symm_apply (MonoidAlgebra.single y 1), hz, map_zero]
  exact (MonoidAlgebra.single_ne_zero.mpr one_ne_zero) hs

/-- The exact finite set inputs used to combine the equivariant bijection in
Proposition 3.8.

In the manuscript application, `basicSetLinearEquiv` comes from Geck 1993,
Theorem A and the following paragraph, after identifying the blockwise series
with `X_C`.  `decompositionEquivariant` is the automorphism naturality of the
restricted classical decomposition map.  `outerGroupTwoHypoelementary`,
`conlonMarkDetection`, and `burnsideMarkInjectivity` separate the inputs to
the Conlon and mark argument in Lemma 2.8.  Subgroup inheritance is proved in
`IntegralBasicSetBridge.isPHypoelementary_subgroup`.  `basicToGeneric` is Lemma 3.7.
`genericToAlperin` is Feng--Malle--Zhang 2026, Condition 6.1 and Theorem 6.2,
restricted from the ambient block stabiliser to `E_H`. -/
structure AssemblyData where
  basicSetLinearEquiv :
    MonoidAlgebra ℤ Basic ≃ₗ[ℤ] MonoidAlgebra ℤ IBr
  decompositionEquivariant :
    MatrixEquivariant (A := E) basicSetLinearEquiv.toLinearMap
  outerGroupTwoHypoelementary : IsPHypoelementary 2 E
  conlonMarkDetection :
    PadicConlonMarkDetection.{uE, uLabel} (p := 2) (A := E)
  burnsideMarkInjectivity :
    PublishedBurnsideMarkInjectivity.{uE, uLabel} (A := E)
  basicToGeneric :
    EquivariantEquiv E Basic GenericWeight (· • ·) (· • ·)
  genericToAlperin :
    EquivariantEquiv E GenericWeight AlperinWeight (· • ·) (· • ·)

/-- The integral basic set bridge, the unipotent correspondence, and the map
from generic weights to Alperin weights compose to the required equivariant
bijection. -/
theorem exists_equivariant_alperin_equiv (D :
    AssemblyData (E := E) (IBr := IBr) (Basic := Basic)
      (GenericWeight := GenericWeight) (AlperinWeight := AlperinWeight)) :
    ∃ Ω : IBr ≃ AlperinWeight,
      ∀ (a : E) (phi : IBr), Ω (a • phi) = a • Ω phi := by
  let integralLatticeEquiv := permutationLatticeEquiv
    D.basicSetLinearEquiv D.decompositionEquivariant
  obtain ⟨basicToIBr, hBasicToIBr⟩ :=
    corollary_2_4_conlonMark D.outerGroupTwoHypoelementary
      ⟨permutationLatticeEquivBaseChange
        (S := ℤ_[2]) integralLatticeEquiv⟩
      D.conlonMarkDetection D.burnsideMarkInjectivity
  let first : EquivariantEquiv E IBr Basic (· • ·) (· • ·) :=
    equivariantEquivSymm
      (show EquivariantEquiv E Basic IBr (· • ·) (· • ·) from
        ⟨basicToIBr, hBasicToIBr⟩)
  let result := equivariantEquivTrans
    (equivariantEquivTrans first D.basicToGeneric) D.genericToAlperin
  exact ⟨result.toEquiv, result.equivariant⟩

end ModularRep.ManuscriptVerification.EvenUnipotentAssembly


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
