import ModularRep.PaperProofs.TypeBCurrentPrincipalBijection
import ModularRep.PaperProofs.CurrentCentralQuotientReturnAdapter

/-!
# Principal Spin supplier on the complete relative-family coordinates

The input contains subordinate GGGR sources, the literal central quotient
and separate assumptions for the two Omega cases. Its exceptional
interpretation assumption is retained for this conditional interface.
The current manuscript application uses the full family of the exceptional
cover through `ManuscriptIBAW.TypeB.ExceptionalPrincipalDescent` instead.
The branch test uses this Spin factor's own rank and finite field. Both
branches return through the same specified central quotient theorem to the
original family, block, root, automorphism adapter and Definition 3.5 relation.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCurrentPrincipalInputs

open ModularRep CharacterWeight
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open TypeBCurrentStrictRouting TypeBCurrentPrincipalResults
open TypeBCurrentPrincipalBijection TypeBModularGroupRootBinding
open TypeBCliffordCarriers TypeBQ3TripleCoverCarrier CurrentCyclicOuterBAW

local instance finiteFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- The exceptional inputs on the computed central-two quotient. The
universal two-prime cover is the actual X, with its literal q projection.
The nine-block criterion remains a deduction from data, not an input. -/
structure ExceptionalSources (family : Definition35Family 2) (block : family.Block)
    (physical : PhysicalFamilySource family) where
  O : Type
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O family.K]
  matrixSource : MatrixExceptionalSource
  freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource
  [finiteX : Finite X]
  [rootsX : HasEnoughRootsOfUnity family.K (Nat.card X)]
  data : TypeBCurrentQ3Inputs.Inputs (k := family.k) (K := family.K) (O := O)
    (matrixSource := matrixSource) (freeSource := freeSource)
  presentation : Q3PrincipalPresentation family block
  cover : EllPrimeCoverSource 2 X
  calibration : Q3CoverCalibration matrixSource freeSource cover
  familyRoots : family.iota = groupRoot data.before.Msys family.H
  downRoots : RootAgreement data.before.rootDown family.iota
  interpretation : Q3NaturalCriterionDescentAssumption data presentation cover calibration
    physical familyRoots downRoots

attribute [instance] ExceptionalSources.ringO ExceptionalSources.domainO
  ExceptionalSources.algebraO

/-- Apply the established q3 theorem and the explicit interpretation
assumption. All root agreements concern its output pairs. -/
theorem ExceptionalSources.coherent {family : Definition35Family 2} {block : family.Block}
    {physical : PhysicalFamilySource family} (sources : ExceptionalSources family block physical)
    (normalization : PairNormalizationSource (family.problem block)) :
    Nonempty (TypeBCurrentPrincipalBijection.CoherentBlockWitness (family.problem block)) := by
  letI := sources.finiteX
  letI := sources.rootsX
  exact principalQ3_coherent sources.data sources.presentation sources.cover sources.calibration
    physical sources.familyRoots sources.downRoots sources.interpretation normalization

/-- Convert only the record carrier, preserving the actual matching and
every same-pair coherent packet. -/
private def coherentCentral {P : Definition35Problem}
    (good : TypeBCurrentPrincipalBijection.CoherentBlockWitness P) :
    CurrentCentralQuotientReturnAdapter.CoherentBlockWitness P where
  omega := good.omega
  equivariant := good.equivariant
  matched := good.matched

/-- The complete source package for one principal Spin block in the full
relative family. None of its fields is a coherent, compatible, BAW-good or
Definition 3.5 witness. The downstairs family is the canonical p-core
quotient computed by the central theorem, not an arbitrary family. -/
structure PrincipalSpinInputs {p n : ℕ} (family : Definition35Family 2)
    (block : family.Block) (coordinates : SpinCoordinates p n family.H)
    (principal : PrincipalSpinCarrier family block n coordinates)
    (automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (semantics : FLZSourceSemantics (family.problem block) automorphisms) where
  gggr : SpinGGGRSources family block coordinates principal
  central : CurrentCentralQuotientReturnAdapter.CentralReturnInputs
    (family.problem block) automorphisms semantics
  presentation : OmegaPrincipalPresentation (n := n) (F := coordinates.F)
    central.downFamily central.downBlock
  physical : PhysicalFamilySource central.downFamily
  downAutomorphisms : Definition35AutomorphismStabilizerAdapter
    (central.downFamily.problem central.downBlock)
  downRoots : central.downFamily.iota = groupRoot gggr.Msys central.downFamily.H
  normalization : PairNormalizationSource (central.downFamily.problem central.downBlock)
  simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n coordinates.F)
  nonexceptional : by
    letI := gggr.finiteUpper
    letI := gggr.finiteLower
    letI := gggr.rootsUpper
    letI := gggr.rootsLower
    letI := gggr.finiteIrr
    letI := gggr.finiteBlocks
    letI : Algebra gggr.O central.downFamily.K := gggr.algebraO
    letI : HasEnoughRootsOfUnity central.downFamily.K
        (Nat.card (SpecialClifford n coordinates.F)) := gggr.rootsUpper
    letI : HasEnoughRootsOfUnity central.downFamily.K
        (Nat.card (Spin n coordinates.F coordinates.norm)) := gggr.rootsLower
    letI : Finite (OrdinaryIrreducibleCharacter.Irr central.downFamily.K
        (Spin n coordinates.F coordinates.norm)) := gggr.finiteIrr
    letI : Fintype (LiteralPrimitiveBlock central.downFamily.k
        (Spin n coordinates.F coordinates.norm)) := gggr.finiteBlocks
    exact (n, Nat.card coordinates.F) ≠ (3, 3) →
      ∃ cover : EllPrimeCoverSource 2 central.downFamily.H,
        FYZ516SpathSource (family := central.downFamily) (block := central.downBlock)
          gggr.context gggr.fieldAction gggr.clifford presentation
          downAutomorphisms cover physical rfl downRoots
  exceptional : (n, Nat.card coordinates.F) = (3, 3) →
    ExceptionalSources central.downFamily central.downBlock physical

/-- Route on this factor's own rank and field. The FYZ field antecedent
comes from gggr_basis/principalBrauer_fixed; q3 uses the actual nine-block
theorem. The central theorem then constructs the requested original map. -/
theorem PrincipalSpinInputs.exists_witness {p n : ℕ} {family : Definition35Family 2}
    {block : family.Block} {coordinates : SpinCoordinates p n family.H}
    {principal : PrincipalSpinCarrier family block n coordinates}
    {automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : FLZSourceSemantics (family.problem block) automorphisms}
    (sources : PrincipalSpinInputs family block coordinates principal automorphisms semantics) :
    Nonempty (Definition35IBAWBijection (family.problem block) automorphisms semantics) := by
  letI := sources.gggr.finiteUpper
  letI := sources.gggr.finiteLower
  letI := sources.gggr.rootsUpper
  letI := sources.gggr.rootsLower
  letI := sources.gggr.finiteIrr
  letI := sources.gggr.finiteBlocks
  letI : Algebra sources.gggr.O sources.central.downFamily.K := sources.gggr.algebraO
  letI : HasEnoughRootsOfUnity sources.central.downFamily.K
      (Nat.card (SpecialClifford n coordinates.F)) := sources.gggr.rootsUpper
  letI : HasEnoughRootsOfUnity sources.central.downFamily.K
      (Nat.card (Spin n coordinates.F coordinates.norm)) := sources.gggr.rootsLower
  letI : Finite (OrdinaryIrreducibleCharacter.Irr sources.central.downFamily.K
      (Spin n coordinates.F coordinates.norm)) := sources.gggr.finiteIrr
  letI : Fintype (LiteralPrimitiveBlock
      sources.central.downFamily.k (Spin n coordinates.F coordinates.norm)) :=
    sources.gggr.finiteBlocks
  by_cases exceptional : (n, Nat.card coordinates.F) = (3, 3)
  · obtain ⟨good⟩ := (sources.exceptional exceptional).coherent sources.normalization
    exact ⟨sources.central.toDefinition35 (coherentCentral good)⟩
  · obtain ⟨cover, published⟩ := sources.nonexceptional exceptional
    obtain ⟨good⟩ := principalOmega_coherent
      (family := sources.central.downFamily) (block := sources.central.downBlock)
      sources.gggr.context sources.gggr.raw
      sources.gggr.fieldAction sources.gggr.fieldSources sources.gggr.clifford
      sources.presentation sources.downAutomorphisms cover sources.physical rfl sources.downRoots
      published sources.normalization sources.simple exceptional
    exact ⟨sources.central.toDefinition35 (coherentCentral good)⟩

/-- The actual original-family bijection chosen from the proved output. -/
def PrincipalSpinInputs.witness {p n : ℕ} {family : Definition35Family 2}
    {block : family.Block} {coordinates : SpinCoordinates p n family.H}
    {principal : PrincipalSpinCarrier family block n coordinates}
    {automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : FLZSourceSemantics (family.problem block) automorphisms}
    (sources : PrincipalSpinInputs family block coordinates principal automorphisms semantics) :
    Definition35IBAWBijection (family.problem block) automorphisms semantics :=
  Classical.choice sources.exists_witness

end ModularRep.PaperProofs.TypeBCurrentPrincipalInputs


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
