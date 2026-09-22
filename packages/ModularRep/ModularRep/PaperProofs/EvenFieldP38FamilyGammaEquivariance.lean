import ModularRep.PaperProofs.EvenFieldP38ChosenFamilyReduction

/-!
# Full block-stabilizer equivariance of the aligned P38 family map

The two actual specified fibres intertwine the family's block stabilizer
with the concrete self-cover presentation. The latter presentation is
identified through its existing canonical automorphism adapter. The SAME
P38 endgame's semidirect equivariance therefore descends through the two
computed fibre equivalences.

The final application uses the rebuilt chosen quotient table. No relation,
own-normalizer packet existence, or new source law occurs here.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldP38FamilyGammaEquivariance

open ModularRep CharacterWeight
open CyclicOuterLemma37Concrete CyclicOuterLemma37ActualBlockFibres
open EvenFieldConcreteTypeC EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldClassifiedP38FamilyPacket EvenFieldP38ChosenFamilyReduction
open EvenFieldBlockGroupEquivCoordinates
open EvenFieldProposition39HighRankU0 EvenFieldFLZ318FixedTheoremGate

variable {ell r a : ℕ} (family : Definition35Family.{0} ell)
variable (ha : 0 < a) [Fintype (FiniteSymplecticFixed r a)]
variable (e : family.H ≃* FiniteSymplecticFixed r a) (b : family.Block)
variable (source : FamilyInputs family ha e b)
variable (dictionary : PhysicalDictionary family ha e b source)
variable (adapter : Definition35AutomorphismStabilizerAdapter (family.problem b))
variable (ambient : HighRankSelfCoverAmbientU0
  (FamilyInputs.toP38 family ha e b source))

/-- Pass through the actual block stabilizer in the concrete automorphism
group, then through the inverse of its canonical self-cover adapter. -/
def gammaEquiv :
    (family.problem b).Gamma ≃*
      (selfCoverProblem (FamilyInputs.toP38 family ha e b source)).Gamma :=
  (FamilyInputs.gammaToConcreteStabilizer family ha e b source dictionary adapter).trans
    (selfCoverAutomorphisms (FamilyInputs.toP38 family ha e b source) ambient).equiv.symm

/-- The exact inverse/opposite convention is preserved by the computed map. -/
theorem gammaEquiv_action (g : (family.problem b).Gamma) :
    inverseOpHom (selfCoverProblem (FamilyInputs.toP38 family ha e b source)).gamma
        (gammaEquiv family ha e b source dictionary adapter ambient g) =
      oppositeAutEquiv e (inverseOpHom (family.problem b).gamma g) := by
  let concreteAdapter :=
    selfCoverAutomorphisms (FamilyInputs.toP38 family ha e b source) ambient
  have hcancel :
      (concreteAdapter.equiv
        (gammaEquiv family ha e b source dictionary adapter ambient g)).1 =
      (FamilyInputs.gammaToConcreteStabilizer family ha e b source dictionary adapter g).1 := by
    change (concreteAdapter.equiv (concreteAdapter.equiv.symm
      (FamilyInputs.gammaToConcreteStabilizer family ha e b source dictionary adapter g))).1 = _
    exact congrArg Subtype.val (concreteAdapter.equiv.apply_symm_apply _)
  exact (concreteAdapter.equiv_coe _).symm.trans
    (hcancel.trans (FamilyInputs.gammaToConcreteStabilizer_coe
      family ha e b source dictionary adapter g))

/-- Naturality on the actual Brauer fibre, with both canonical actions displayed. -/
theorem brauerFibreEquiv_action (g : (family.problem b).Gamma)
    (psi : Definition35Brauer (family.problem b)) :
    FamilyInputs.brauerFibreEquiv family ha e b source
        ((definition35BrauerAction (family.problem b)).smul g psi) =
      (definition35BrauerAction
        (selfCoverProblem (FamilyInputs.toP38 family ha e b source))).smul
        (gammaEquiv family ha e b source dictionary adapter ambient g)
        (FamilyInputs.brauerFibreEquiv family ha e b source psi) := by
  apply Subtype.ext
  change IrreducibleBrauerCharacter.equivAlongMulEquiv family.iota e
      (@HSMul.hSMul (MulAut family.H)ᵐᵒᵖ (IBr family.iota) (IBr family.iota)
        inferInstance (inverseOpHom (family.problem b).gamma g) psi.1) =
    @HSMul.hSMul (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ
      (IBr (concreteRoot family e)) (IBr (concreteRoot family e)) inferInstance
      (inverseOpHom (selfCoverProblem (FamilyInputs.toP38 family ha e b source)).gamma
        (gammaEquiv family ha e b source dictionary adapter ambient g))
      (FamilyInputs.brauerFibreEquiv family ha e b source psi).1
  rw [gammaEquiv_action family ha e b source dictionary adapter ambient g]
  exact FamilyInputs.brauerFibreEquiv_twist family ha e b source psi
    (inverseOpHom (family.problem b).gamma g)

/-- Naturality on whole weight classes, retaining both specified block sources. -/
theorem weightFibreEquiv_action (g : (family.problem b).Gamma)
    (w : Definition35Weight (family.problem b)) :
    FamilyInputs.weightFibreEquiv family ha e b source dictionary
        ((definition35WeightAction (family.problem b)).smul g w) =
      (definition35WeightAction
        (selfCoverProblem (FamilyInputs.toP38 family ha e b source))).smul
        (gammaEquiv family ha e b source dictionary adapter ambient g)
        (FamilyInputs.weightFibreEquiv family ha e b source dictionary w) := by
  apply Subtype.ext
  change conjugacyClassGroupEquiv e
      (@HSMul.hSMul (MulAut family.H)ᵐᵒᵖ
        (CharacterWeight.ConjugacyClass (p := ell) (K := family.K) (G := family.H))
        (CharacterWeight.ConjugacyClass (p := ell) (K := family.K) (G := family.H))
        inferInstance (inverseOpHom (family.problem b).gamma g) w.1) =
    @HSMul.hSMul (MulAut (FiniteSymplecticFixed r a))ᵐᵒᵖ
      (CharacterWeight.ConjugacyClass (p := ell) (K := family.K)
        (G := FiniteSymplecticFixed r a))
      (CharacterWeight.ConjugacyClass (p := ell) (K := family.K)
        (G := FiniteSymplecticFixed r a)) inferInstance
      (inverseOpHom (selfCoverProblem (FamilyInputs.toP38 family ha e b source)).gamma
        (gammaEquiv family ha e b source dictionary adapter ambient g))
      (FamilyInputs.weightFibreEquiv family ha e b source dictionary w).1
  rw [gammaEquiv_action family ha e b source dictionary adapter ambient g]
  exact FamilyInputs.weightFibreEquiv_twist family ha e b source dictionary w
    (inverseOpHom (family.problem b).gamma g)

/-- Re-express THIS protected endgame's existing semidirect equivariance in
the canonical Definition 3.5 actions. No new equivariance input is required. -/
theorem endgame_equivariant :
    letI := source.finiteFieldOpp
    letI := source.cyclicFieldOpp
    letI := source.finiteField
    letI := source.cyclicField
    Definition35Equivariant
      (selfCoverProblem (FamilyInputs.toP38 family ha e b source))
      (FamilyInputs.toP38 family ha e b source).endgame.omega.toEquiv := by
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  intro g psi
  let p38 := FamilyInputs.toP38 family ha e b source
  let omega : Definition35Brauer (selfCoverProblem p38) ≃
      Definition35Weight (selfCoverProblem p38) := p38.endgame.omega.toEquiv
  have hb := definition35BrauerAction_smul_eq_clauseII
    p38.iota p38.hinj p38.blocks (fieldAction r a ha) p38.blockSource
    p38.block p38.T p38.localReduction g psi
  have hw := definition35WeightAction_smul_eq_clauseII
    p38.iota p38.hinj p38.blocks (fieldAction r a ha) p38.blockSource
    p38.block p38.T p38.localReduction g (omega psi)
  have hend :
      omega ((selfCoverBrauerSemidirectAction p38.iota p38.hinj p38.blocks
        (fieldAction r a ha) p38.blockSource p38.block p38.T).smul g psi) =
      (selfCoverWeightSemidirectAction p38.iota p38.hinj p38.blocks
        (fieldAction r a ha) p38.blockSource p38.block p38.T).smul g (omega psi) :=
    p38.endgame.semidirect_equivariant g psi
  exact (congrArg (fun x : Definition35Brauer (selfCoverProblem p38) => omega x) hb).trans
    (hend.trans hw.symm)

include dictionary adapter ambient in
/-- Cancel the actual weight-fibre equivalence after applying the two action
squares and the SAME P38 endgame's equivariance. -/
theorem familyBijection_equivariant :
    Definition35Equivariant (family.problem b)
      (FamilyInputs.familyBijection family ha e b source dictionary) := by
  letI := source.finiteFieldOpp
  letI := source.cyclicFieldOpp
  letI := source.finiteField
  letI := source.cyclicField
  intro g psi
  apply (FamilyInputs.weightFibreEquiv family ha e b source dictionary).injective
  let p38 := FamilyInputs.toP38 family ha e b source
  let omega : Definition35Brauer (selfCoverProblem p38) ≃
      Definition35Weight (selfCoverProblem p38) := p38.endgame.omega.toEquiv
  let gc := gammaEquiv family ha e b source dictionary adapter ambient g
  let pc := FamilyInputs.brauerFibreEquiv family ha e b source psi
  have hfirst := FamilyInputs.familyBijection_formula family ha e b source dictionary
    ((definition35BrauerAction (family.problem b)).smul g psi)
  have hbrauer := congrArg (fun x : Definition35Brauer (selfCoverProblem p38) => omega x)
    (brauerFibreEquiv_action family ha e b source dictionary adapter ambient g psi)
  have hend : omega ((definition35BrauerAction (selfCoverProblem p38)).smul gc pc) =
      (definition35WeightAction (selfCoverProblem p38)).smul gc (omega pc) :=
    endgame_equivariant family ha e b source gc pc
  have hformula := congrArg
    (fun w : Definition35Weight (selfCoverProblem p38) =>
      (definition35WeightAction (selfCoverProblem p38)).smul gc w)
    (FamilyInputs.familyBijection_formula family ha e b source dictionary psi).symm
  have hweight := (weightFibreEquiv_action family ha e b source dictionary adapter ambient g
    (FamilyInputs.familyBijection family ha e b source dictionary psi)).symm
  exact hfirst.trans (hbrauer.trans (hend.trans (hformula.trans hweight)))

include adapter in
/-- Full family-Gamma equivariance for the exact bijection obtained AFTER
the quotient table was rebuilt from the family's chosen reductions. -/
theorem alignedFamilyBijection_equivariant
    (alignedAmbient : HighRankSelfCoverAmbientU0
      (FamilyInputs.toP38 family ha e b (alignedInputs family ha e b source dictionary))) :
    Definition35Equivariant (family.problem b)
      (alignedFamilyBijection family ha e b source dictionary) :=
  familyBijection_equivariant family ha e b
    (alignedInputs family ha e b source dictionary)
    (alignedDictionary family ha e b source dictionary) adapter alignedAmbient

end ModularRep.PaperProofs.EvenFieldP38FamilyGammaEquivariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
