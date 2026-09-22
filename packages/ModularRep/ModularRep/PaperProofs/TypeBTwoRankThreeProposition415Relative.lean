import ModularRep.PaperProofs.TypeBTwoCommon
import ModularRep.StrictQuasiIsolation

/-!
# Source-shaped deductions for manuscript Proposition 4.13

This module checks the manuscript-specific logical construction in the rank-three
type B argument.  It uses the shared central-double-cover odd-label deduction
from `TypeBTwoCommon`, checks the routing of every possible proper-Levi factor,
and then checks the sequence from factorwise maps to the claimed inductive
conclusion.

The representation theoretic results are supplied through named interfaces.
In particular, the conclusion of the full-cover criterion for the dominated
block of the universal 2'-cover is an explicit input rather than a hidden
consequence of the other steps.
-/

namespace ModularRep.PaperProofs.TypeBTwoRankThreeProposition415Relative

open ModularRep.PaperProofs.TypeBTwoCommon

universe uGhat uG uTarget uSpin uLevi uFactor

section LeviFactors

/-- Simple factors that can occur in the derived subgroup of a proper Levi of
type B3 in the rank-three argument.  The trivial derived subgroup contributes
no factor. -/
inductive FactorKind where
  | typeB2
  | typeA1
  | typeA2
  | twistedTypeA2
  deriving DecidableEq

/-- The six derived-factor configurations displayed in Proposition 4.13. -/
inductive ProperLeviKind where
  | typeB2
  | typeA1A1
  | typeA2
  | twistedTypeA2
  | typeA1
  | torus
  deriving DecidableEq

/-- The simple factors belonging to each displayed proper-Levi case. -/
def factorKinds : ProperLeviKind → List FactorKind
  | .typeB2 => [.typeB2]
  | .typeA1A1 => [.typeA1, .typeA1]
  | .typeA2 => [.typeA2]
  | .twistedTypeA2 => [.twistedTypeA2]
  | .typeA1 => [.typeA1]
  | .torus => []

/-- Exact external inputs used to establish the factorwise maps.  The
classification supplies `kind_of_occurring` and strict quasi-isolation.  The
remaining fields separate the type A and type B2 sources.  When the derived
subgroup is trivial, there are no factors to which a map must be assigned. -/
structure FactorwiseInputs (SpinBlock : Type uSpin) (LeviWitness : Type uLevi)
    (FactorBlock : Type uFactor) where
  Occurs : SpinBlock → LeviWitness → FactorBlock → Prop
  leviKind : LeviWitness → ProperLeviKind
  factorKind : FactorBlock → FactorKind
  StrictlyQuasiIsolated : FactorBlock → Prop
  Principal : FactorBlock → Prop
  HasRequiredMap : FactorBlock → Prop
  kind_of_occurring : ∀ {b L f}, Occurs b L f →
    factorKind f ∈ factorKinds (leviKind L)
  strict_of_occurring : ∀ {b L f}, Occurs b L f → StrictlyQuasiIsolated f
  b2_principal : ∀ {f}, factorKind f = .typeB2 →
    StrictlyQuasiIsolated f → Principal f
  b2_principal_map : ∀ {f}, factorKind f = .typeB2 →
    Principal f → HasRequiredMap f
  typeA_map : ∀ {f},
    factorKind f = .typeA1 ∨ factorKind f = .typeA2 ∨
      factorKind f = .twistedTypeA2 → HasRequiredMap f

namespace FactorwiseInputs

/-- A Levi with trivial derived subgroup has no simple factor. -/
theorem no_factor_occurs_in_torus_case
    {SpinBlock : Type uSpin} {LeviWitness : Type uLevi}
    {FactorBlock : Type uFactor}
    (I : FactorwiseInputs SpinBlock LeviWitness FactorBlock)
    {b : SpinBlock} {L : LeviWitness} (hLevi : I.leviKind L = .torus) :
  ∀ f, ¬ I.Occurs b L f := by
  intro f hOccurs
  simpa [factorKinds, hLevi] using I.kind_of_occurring hOccurs

/-- Every factor in one of the six displayed cases is sent to the correct
source: type B2 first becomes principal and type A uses the type A results.
The case of a trivial derived subgroup is vacuous. -/
theorem map_of_occurring
    {SpinBlock : Type uSpin} {LeviWitness : Type uLevi}
    {FactorBlock : Type uFactor}
    (I : FactorwiseInputs SpinBlock LeviWitness FactorBlock)
    {b : SpinBlock} {L : LeviWitness} {f : FactorBlock}
    (hOccurs : I.Occurs b L f) :
    I.HasRequiredMap f := by
  have hKind := I.kind_of_occurring hOccurs
  have hStrict := I.strict_of_occurring hOccurs
  cases hLevi : I.leviKind L with
  | typeB2 =>
      have hFactorKind : I.factorKind f = .typeB2 := by
        simpa [factorKinds, hLevi] using hKind
      exact I.b2_principal_map hFactorKind
        (I.b2_principal hFactorKind hStrict)
  | typeA1A1 =>
      have hFactorKind : I.factorKind f = .typeA1 := by
        simpa [factorKinds, hLevi] using hKind
      exact I.typeA_map (Or.inl hFactorKind)
  | typeA2 =>
      have hFactorKind : I.factorKind f = .typeA2 := by
        simpa [factorKinds, hLevi] using hKind
      exact I.typeA_map (Or.inr (Or.inl hFactorKind))
  | twistedTypeA2 =>
      have hFactorKind : I.factorKind f = .twistedTypeA2 := by
        simpa [factorKinds, hLevi] using hKind
      exact I.typeA_map (Or.inr (Or.inr hFactorKind))
  | typeA1 =>
      have hFactorKind : I.factorKind f = .typeA1 := by
        simpa [factorKinds, hLevi] using hKind
      exact I.typeA_map (Or.inl hFactorKind)
  | torus =>
      exact False.elim ((I.no_factor_occurs_in_torus_case hLevi) f hOccurs)

end FactorwiseInputs

end LeviFactors

section FieldStabilizerPromotion

open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {A E Theta Psi : Type*}
variable [Group A] [Group E]
variable [MulAction A Theta] [MulAction E Theta]
variable [MulAction A Psi] [MulAction E Psi]

/-- Inputs to the local-to-full field-stabiliser step in Proposition 4.13.

The first field is the compatibility of the diagonal and field actions on
the selected constituent orbit.  The second is the Clifford-theoretic return
of a constituent under an element of the combined stabiliser.  The third is
only the factorisation already obtained over the setwise stabiliser of that
orbit.  In particular, neither the full factorisation nor the equality of
the two field stabilisers is an input. -/
structure FieldStabilizerPromotionInputs
    (phi : E →* MulAut A) (theta : Theta) (psi : Psi) where
  thetaActionCompatible :
    Formalisation.SemidirectActionCompatible (X := Theta) phi
  constituentOrbitReturn : ∀ a : A, ∀ e : E,
    a • (e • psi) = psi → e • theta ∈ MulAction.orbit A theta
  localFactorization : ∀ a : A, ∀ e : E,
    OrbitSetwiseStable (A := A) theta e →
      (a • (e • psi) = psi ↔ a • psi = psi ∧ e • psi = psi)

/-- The field elements that both stabilise the constituent orbit setwise and
fix the selected Brauer character.  This is the elementwise model of
`(D_O)_psi` in Proposition 4.13. -/
def orbitStableFieldFixer (theta : Theta) (psi : Psi) : Set E :=
  {e | OrbitSetwiseStable (A := A) theta e ∧ e • psi = psi}

/-- The full field stabiliser of the selected Brauer character, written as a
set so that it can be compared directly with `orbitStableFieldFixer`. -/
def fieldFixer (psi : Psi) : Set E :=
  {e | e • psi = psi}

/-- The exact promotion used in Proposition 4.13.  Clifford return first
shows that every field element fixing `psi` stabilises the constituent orbit.
The equality `(D_O)_psi = D_psi` follows, and the factorisation known over
the orbit stabiliser then extends to the full field group. -/
theorem local_to_full_field_stabilizer_promotion
    (phi : E →* MulAut A) (theta : Theta) (psi : Psi)
    (I : FieldStabilizerPromotionInputs phi theta psi) :
    orbitStableFieldFixer (A := A) (E := E) theta psi =
        fieldFixer (E := E) psi ∧
      ProductStabilizerFactorization (D := A) (E := E) psi := by
  constructor
  · ext e
    change (OrbitSetwiseStable (A := A) theta e ∧ e • psi = psi) ↔
      e • psi = psi
    exact (field_fix_iff_orbitSetwiseStable_and_field_fix
      phi I.thetaActionCompatible theta psi e I.constituentOrbitReturn).symm
  · exact productStabilizerFactorization_of_orbit_stabilizer
      phi I.thetaActionCompatible theta psi I.constituentOrbitReturn
        I.localFactorization

end FieldStabilizerPromotion

section CentralQuotientBlocks

variable {SpinBlock : Type uSpin} {TargetBlock : Type uTarget}

/-- The block-theoretic part of the central quotient
`Spin_7(q) -> Omega_7(q)`, attached to the literal double-cover map.

The central double cover is routine structural input.  Navarro's normal
`p`-subgroup block theorem supplies the block equivalence, domination, and
principal-block compatibility.  Those source results are deliberately fields
of this structure: Lean checks only the manuscript-specific bookkeeping after
they have been instantiated. -/
structure CentralTwoQuotientBlockCorrespondence
    (SpinBlock : Type uSpin) (TargetBlock : Type uTarget) where
  SpinGroup : Type uSpin
  TargetGroup : Type uTarget
  spinGroup : Group SpinGroup
  targetGroup : Group TargetGroup
  cover : @CentralDoubleCover SpinGroup TargetGroup spinGroup targetGroup
  TargetPrincipal : TargetBlock -> Prop
  SpinPrincipal : SpinBlock -> Prop
  Dominates : SpinBlock -> TargetBlock -> Prop
  blockQuotient : SpinBlock ≃ TargetBlock
  dominates_iff : ∀ spinBlock targetBlock,
    Dominates spinBlock targetBlock ↔ blockQuotient spinBlock = targetBlock
  principal_iff : ∀ spinBlock,
    SpinPrincipal spinBlock ↔ TargetPrincipal (blockQuotient spinBlock)

namespace CentralTwoQuotientBlockCorrespondence

/-- The block of the full double cover corresponding to a target block. -/
def dominatingBlock
    (B : CentralTwoQuotientBlockCorrespondence SpinBlock TargetBlock)
    (b : TargetBlock) : SpinBlock :=
  B.blockQuotient.symm b

@[simp]
theorem blockQuotient_dominatingBlock
    (B : CentralTwoQuotientBlockCorrespondence SpinBlock TargetBlock)
    (b : TargetBlock) :
    B.blockQuotient (B.dominatingBlock b) = b :=
  B.blockQuotient.apply_symm_apply b

/-- The selected block of the full cover dominates the target block. -/
theorem dominatingBlock_dominates
    (B : CentralTwoQuotientBlockCorrespondence SpinBlock TargetBlock)
    (b : TargetBlock) : B.Dominates (B.dominatingBlock b) b :=
  (B.dominates_iff _ _).2 (B.blockQuotient_dominatingBlock b)

/-- Domination identifies the selected full-cover block uniquely. -/
theorem dominates_iff_eq_dominatingBlock
    (B : CentralTwoQuotientBlockCorrespondence SpinBlock TargetBlock)
    (spinBlock : SpinBlock) (targetBlock : TargetBlock) :
    B.Dominates spinBlock targetBlock ↔
      spinBlock = B.dominatingBlock targetBlock := by
  rw [B.dominates_iff]
  constructor
  · intro h
    apply B.blockQuotient.injective
    simpa only [B.blockQuotient_dominatingBlock] using h
  · rintro rfl
    exact B.blockQuotient_dominatingBlock targetBlock

/-- Principal blocks correspond under the central `2`-quotient. -/
theorem dominatingBlock_nonprincipal
    (B : CentralTwoQuotientBlockCorrespondence SpinBlock TargetBlock)
    {b : TargetBlock} (hb : ¬ B.TargetPrincipal b) :
    ¬ B.SpinPrincipal (B.dominatingBlock b) := by
  intro hPrincipal
  apply hb
  simpa only [B.blockQuotient_dominatingBlock] using
    (B.principal_iff (B.dominatingBlock b)).1 hPrincipal

end CentralTwoQuotientBlockCorrespondence

end CentralQuotientBlocks

section QuasiIsolationGeometry

open scoped Pointwise
open ModularRep.ManuscriptVerification.StrictQuasiIsolation

variable {DualGroup : Type uG} [Group DualGroup]

/-- The set-theoretic centraliser data needed to compare strict and ordinary
quasi-isolation for the semisimple label.  Identifying these subgroups and the
proper Levi subsets with the algebraic-group objects is a source adapter. -/
structure QuasiIsolationGeometry where
  IsProperLevi : Set DualGroup -> Prop
  finiteCentralizer : DualGroup -> Subgroup DualGroup
  connectedCentralizer : DualGroup -> Subgroup DualGroup
  finiteCentralizer_le : ∀ s,
    finiteCentralizer s ≤ Subgroup.centralizer {s}
  connectedCentralizer_le : ∀ s,
    connectedCentralizer s ≤ Subgroup.centralizer {s}

namespace QuasiIsolationGeometry

/-- Ordinary quasi-isolation in the source-shaped centraliser model. -/
def QuasiIsolated (Q : QuasiIsolationGeometry (DualGroup := DualGroup))
    (s : DualGroup) : Prop :=
  NotContainedInProperLevi (Subgroup.centralizer {s} : Set DualGroup)
    Q.IsProperLevi

/-- Strict quasi-isolation in the source-shaped centraliser model. -/
def StrictlyQuasiIsolated
    (Q : QuasiIsolationGeometry (DualGroup := DualGroup))
    (s : DualGroup) : Prop :=
  NotContainedInProperLevi
    ((Q.finiteCentralizer s : Set DualGroup) *
      (Q.connectedCentralizer s : Set DualGroup))
    Q.IsProperLevi

/-- Strict quasi-isolation implies ordinary quasi-isolation because the
finite and connected centraliser factors lie in the full centraliser. -/
theorem quasiIsolated_of_strictlyQuasiIsolated
    (Q : QuasiIsolationGeometry (DualGroup := DualGroup)) {s : DualGroup}
    (hStrict : Q.StrictlyQuasiIsolated s) : Q.QuasiIsolated s :=
  ModularRep.ManuscriptVerification.StrictQuasiIsolation.quasiIsolated_of_strictlyQuasiIsolated
    (Q.finiteCentralizer_le s) (Q.connectedCentralizer_le s) hStrict

end QuasiIsolationGeometry

end QuasiIsolationGeometry

section NonexceptionalAssembly

variable {Ghat : Type uGhat} {G : Type uG} [Group Ghat] [Group G]
variable {TargetBlock : Type uTarget} {SpinBlock : Type uSpin}
variable {FactorBlock : Type uFactor}
variable {C : CentralDoubleCover (Ghat := Ghat) (G := G)}

/-- The exact input boundary for the nonexceptional rank-three argument.

`TargetBlock` models blocks of the universal `2'`-cover `Omega_7(q)`, while
`SpinBlock` models blocks of the full cover `Spin_7(q)`.  The block
correspondence and domination relation are therefore explicit.  The later
predicates distinguish the proper rational Levi witness, factorwise
constructions, component and Levi selectors, the ambient Jordan transfer,
and the full-cover criterion data used for the dominated target block. -/
structure NonexceptionalInputs
    (C : CentralDoubleCover (Ghat := Ghat) (G := G)) where
  quotientBlocks : CentralTwoQuotientBlockCorrespondence SpinBlock TargetBlock
  IsAssociated : SpinBlock → G → Prop
  quasiGeometry : QuasiIsolationGeometry (DualGroup := G)
  label : SpinBlock → G
  label_twoPrime : ∀ b, ModularRep.IsPrimeRegular 2 (label b)
  label_associated : ∀ b, IsAssociated b (label b)
  bonnafe : C.BonnafeOrderFourProjectionInterface quasiGeometry.QuasiIsolated
  identityPrincipal :
    ModularRep.TypeBQuasiIsolation.IdentityLabelPrincipalBlockInterface
      IsAssociated quotientBlocks.SpinPrincipal
  LeviWitness : Type uLevi
  IsProperRationalLeviFor : SpinBlock → LeviWitness → Prop
  properRationalLevi_of_not_strictlyQuasi : ∀ b,
    ¬ quasiGeometry.StrictlyQuasiIsolated (label b) →
      ∃ L, IsProperRationalLeviFor b L
  factors : FactorwiseInputs SpinBlock LeviWitness FactorBlock
  FactorMaps : SpinBlock → Prop
  factorMaps_of_properRationalLevi : ∀ {b L},
    IsProperRationalLeviFor b L →
    (∀ f, factors.Occurs b L f → factors.HasRequiredMap f) → FactorMaps b
  ComponentSelector : SpinBlock → Prop
  componentSelector_of_factorMaps : ∀ {b}, FactorMaps b → ComponentSelector b
  LeviSelector : SpinBlock → Prop
  leviSelector_of_componentSelector : ∀ {b}, ComponentSelector b → LeviSelector b
  AmbientSelectorAndExtension : SpinBlock → Prop
  ambient_of_levi : ∀ {b}, LeviSelector b → AmbientSelectorAndExtension b
  FullCoverCriterionData : SpinBlock → Prop
  fullCoverData_of_ambient : ∀ {b},
    FactorMaps b → AmbientSelectorAndExtension b → FullCoverCriterionData b
  TargetBAWGood : TargetBlock → Prop
  full_cover_criterion_for_dominated_block : ∀ {spinBlock targetBlock},
    quotientBlocks.Dominates spinBlock targetBlock →
      FullCoverCriterionData spinBlock →
      TargetBAWGood targetBlock
  TargetInductiveBAW : TargetBlock → Prop
  principal_inductive : ∀ {b},
    quotientBlocks.TargetPrincipal b → TargetInductiveBAW b
  good_implies_inductive : ∀ {b}, TargetBAWGood b → TargetInductiveBAW b

namespace NonexceptionalInputs

/-- The block of the full cover corresponding to a target block.  In the
concrete application it is the unique block of `Spin_7(q)` dominating the
given block of `Omega_7(q)`. -/
def dominatingBlock
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    (b : TargetBlock) : SpinBlock :=
  I.quotientBlocks.blockQuotient.symm b

@[simp]
theorem blockQuotient_dominatingBlock
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    (b : TargetBlock) :
    I.quotientBlocks.blockQuotient (I.dominatingBlock b) = b :=
  I.quotientBlocks.blockQuotient.apply_symm_apply b

/-- The chosen full-cover block really dominates the target block. -/
theorem dominatingBlock_dominates
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    (b : TargetBlock) :
    I.quotientBlocks.Dominates (I.dominatingBlock b) b :=
  (I.quotientBlocks.dominates_iff _ _).2
    (I.blockQuotient_dominatingBlock b)

/-- Domination identifies the full-cover block uniquely. -/
theorem dominates_iff_eq_dominatingBlock
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    (spinBlock : SpinBlock) (targetBlock : TargetBlock) :
    I.quotientBlocks.Dominates spinBlock targetBlock ↔
      spinBlock = I.dominatingBlock targetBlock := by
  rw [I.quotientBlocks.dominates_iff]
  constructor
  · intro h
    apply I.quotientBlocks.blockQuotient.injective
    simpa only [I.blockQuotient_dominatingBlock] using h
  · rintro rfl
    exact I.blockQuotient_dominatingBlock targetBlock

/-- Principal blocks correspond under the quotient by the central
`2`-subgroup.  Hence a block dominating a nonprincipal target block is also
nonprincipal. -/
theorem dominatingBlock_nonprincipal
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    {b : TargetBlock} (hb : ¬ I.quotientBlocks.TargetPrincipal b) :
    ¬ I.quotientBlocks.SpinPrincipal (I.dominatingBlock b) := by
  intro hPrincipal
  apply hb
  simpa only [I.blockQuotient_dominatingBlock] using
    (I.quotientBlocks.principal_iff (I.dominatingBlock b)).1 hPrincipal

/-- The shared TypeBTwoCommon central-double-cover odd-label deduction is
applied to the explicitly chosen dominating block.  The oddness of the label
is derived from its `2'`-property rather than supplied separately. -/
theorem dominating_block_label_not_quasi_isolated
    (C : CentralDoubleCover (Ghat := Ghat) (G := G))
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    {b : TargetBlock} (hb : ¬ I.quotientBlocks.TargetPrincipal b) :
    ¬ I.quasiGeometry.QuasiIsolated (I.label (I.dominatingBlock b)) := by
  exact C.nonprincipal_label_not_quasiIsolated I.bonnafe I.identityPrincipal
    (I.label_associated (I.dominatingBlock b))
    (I.label_twoPrime (I.dominatingBlock b)).odd_of_right
    (I.dominatingBlock_nonprincipal hb)

/-- The proper Levi reduction in Feng--Li--Zhang is stated for a label that
is not strictly quasi-isolated.  The odd-label argument gives the stronger
failure of quasi-isolation, and this theorem checks the intervening
implication for the explicitly selected dominating block. -/
theorem dominating_block_label_not_strictly_quasi_isolated
    (C : CentralDoubleCover (Ghat := Ghat) (G := G))
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    {b : TargetBlock} (hb : ¬ I.quotientBlocks.TargetPrincipal b) :
    ¬ I.quasiGeometry.StrictlyQuasiIsolated
      (I.label (I.dominatingBlock b)) := by
  intro hStrict
  exact I.dominating_block_label_not_quasi_isolated C hb
    (I.quasiGeometry.quasiIsolated_of_strictlyQuasiIsolated hStrict)

/-- Kernel-checked construction of the nonprincipal branch.  Notice that the
full-cover criterion for the dominated target block is used at the final
nontrivial step. -/
theorem nonprincipal_inductive
    (C : CentralDoubleCover (Ghat := Ghat) (G := G))
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    {b : TargetBlock} (hb : ¬ I.quotientBlocks.TargetPrincipal b) :
    I.TargetInductiveBAW b := by
  let spinBlock := I.dominatingBlock b
  have hNotStrictlyQuasi :
      ¬ I.quasiGeometry.StrictlyQuasiIsolated (I.label spinBlock) := by
    exact I.dominating_block_label_not_strictly_quasi_isolated C hb
  obtain ⟨L, hProper⟩ :=
    I.properRationalLevi_of_not_strictlyQuasi spinBlock hNotStrictlyQuasi
  have hEveryFactor : ∀ f, I.factors.Occurs spinBlock L f →
      I.factors.HasRequiredMap f := by
    intro f hf
    exact I.factors.map_of_occurring hf
  have hFactorMaps : I.FactorMaps spinBlock :=
    I.factorMaps_of_properRationalLevi hProper hEveryFactor
  have hComponent : I.ComponentSelector spinBlock :=
    I.componentSelector_of_factorMaps hFactorMaps
  have hLevi : I.LeviSelector spinBlock :=
    I.leviSelector_of_componentSelector hComponent
  have hAmbient : I.AmbientSelectorAndExtension spinBlock :=
    I.ambient_of_levi hLevi
  have hFullCoverData : I.FullCoverCriterionData spinBlock :=
    I.fullCoverData_of_ambient hFactorMaps hAmbient
  have hTargetGood : I.TargetBAWGood b :=
    I.full_cover_criterion_for_dominated_block
      (I.dominatingBlock_dominates b) hFullCoverData
  exact I.good_implies_inductive hTargetGood

/-- The nonexceptional conclusion combines the cited principal-block result
with the manuscript-specific nonprincipal construction. -/
theorem all_blocks_inductive
    (C : CentralDoubleCover (Ghat := Ghat) (G := G))
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    (b : TargetBlock) : I.TargetInductiveBAW b := by
  by_cases hb : I.quotientBlocks.TargetPrincipal b
  · exact I.principal_inductive hb
  · exact I.nonprincipal_inductive C hb

end NonexceptionalInputs

/-- Final case split in Proposition 4.13.  The exceptional parameter is the
separate computation in Proposition 4.11; away from it, the preceding theorem
performs the rank-three construction. -/
theorem proposition_4_15
    (C : CentralDoubleCover (Ghat := Ghat) (G := G))
    (I : NonexceptionalInputs (TargetBlock := TargetBlock)
      (SpinBlock := SpinBlock) (FactorBlock := FactorBlock) C)
    (ExceptionalParameter : Prop)
    (exceptional_case : ExceptionalParameter →
      ∀ b : TargetBlock, I.TargetInductiveBAW b)
    (b : TargetBlock) : I.TargetInductiveBAW b := by
  classical
  by_cases hExceptional : ExceptionalParameter
  · exact exceptional_case hExceptional b
  · exact I.all_blocks_inductive C b

end NonexceptionalAssembly

end ModularRep.PaperProofs.TypeBTwoRankThreeProposition415Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
