import ModularRep.PaperProofs.TypeBCurrentPrincipalResults
import ModularRep.PaperProofs.CurrentCyclicOuterBAW
import ModularRep.PaperProofs.TypeBCurrentStrictRouting
import ModularRep.PaperProofs.TypeBModularGroupRootBinding
import ModularRep.PaperProofs.TypeBCurrentQ3Inputs

/-!
# Published principal Omega condition with its field antecedent discharged

Feng--Yu--Zhang, *Radical subgroups of finite reductive groups*, arXiv
2401.00156v4, Theorem 5.16, is conditional on principal Spin Brauer field
fixation. This file supplies that antecedent from the all-rank GGGR deduction.
The published implication and Spath's block formulation are explicit E2
inputs on the actual Omega presentation. Coefficient normalization is an
independent, same-pair E1 source; it does not choose a matching.

The output contains an actual equivariant bijection and coherent ambient
extension/intermediate block data for its own matched weights. A separately
authenticated relation passage produces BAW-goodness or Definition 3.5.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentPrincipalBijection

open ModularRep CharacterWeight
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldFLZBAWGoodFamily CurrentCyclicOuterBAW
open CyclicOuterLemma37LiteralLocalExtension
open TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCurrentPrincipalResults TypeBModularGroupRootBinding

/-- The published single-block matching with its concrete Spath data.
The matching is output; neither a selected weight nor a relation predicate
is provided by a caller. -/
structure PublishedBlockWitness (P : Definition35Problem) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  matched : ∀ psi : Definition35Brauer P,
    Nonempty (SpathMatchedBlockCondition P psi psi (omega psi))

/-- The coefficient-normalized output for the same matching. -/
structure CoherentBlockWitness (P : Definition35Problem) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  matched : ∀ psi : Definition35Brauer P,
    Nonempty (CoherentMatchedCondition P psi (omega psi))

/-- E1 coefficient normalization on every actual pair for which a published
ambient packet exists. Its scope includes that packet's existential ambient
groups and all intermediate restrictions, beyond just the roots of Omega.
No algebraic closure of the characteristic-zero DVR fraction field is used. -/
structure PairNormalizationSource (P : Definition35Problem) : Prop where
  normalize : ∀ (psi : Definition35Brauer P) (weight : Definition35Weight P),
    Nonempty (SpathMatchedBlockCondition P psi psi weight) →
      Nonempty (CoherentMatchedCondition P psi weight)

def PublishedBlockWitness.normalize {P : Definition35Problem}
    (normalization : PairNormalizationSource P) (good : PublishedBlockWitness P) :
    CoherentBlockWitness P where
  omega := good.omega
  equivariant := good.equivariant
  matched psi := normalization.normalize psi (good.omega psi) (good.matched psi)

/-- The specified block decomposition, local support and reductions use the
ordinary character of each raw weight. The coefficient field is required
to contain enough roots of unity, without an algebraic closure assumption. -/
structure PhysicalFamilySource (family : Definition35Family 2) : Prop where
  ordinaryRoots : HasEnoughRootsOfUnity family.K (Nat.card family.H)
  catalogue_idempotent : ∀ b : family.Block,
    family.blockSource.operations.ambientBlockData.blockIdempotent b =
      family.blockIdempotent b
  support : OddTwoActualLocalBlockSupport.Source
    family.iota family.blockSource.operations
  reductions : ∀ W : CharacterWeight 2 family.K family.H,
    ∃ root : PrimeRegularRootEmbedding 2 family.k family.K
        (Subgroup.normalizer (W.subgroup : Set family.H)),
      ∃ phi : IBr root,
        OddTwoActualLocalBlockSupport.RootCompatibleAlong family.iota root
          (Subgroup.normalizer (W.subgroup : Set family.H)).subtype ∧
        NormalizerInflatedReduction W.subgroup W.localCharacter root phi

/-- An actual principal Omega block in an arbitrary finite group coordinate
presentation. The constant-one character lies in the selected literal fibre. -/
structure OmegaPrincipalPresentation {n : ℕ} {F : Type} [Field F]
    (family : Definition35Family 2) (block : family.Block) where
  groupEquiv : family.H ≃* TypeBOrthogonalOmegaCarriers.Omega n F
  principalCharacter : Definition35Brauer (family.problem block)
  principalCharacter_value_one : ∀ x, principalCharacter.1.1 x = 1

section Omega

variable {n r f : ℕ} {F : Type} [Field F] [Finite F] [CharP F r]
  {family : Definition35Family 2} {block : family.Block}
  {O : Type} [CommRing O] [IsDomain O] [Algebra O family.K]
  {N : NormSource n F} [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity family.K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity family.K (Nat.card (Spin n F N))]
  [Finite (OrdinaryIrreducibleCharacter.Irr family.K (Spin n F N))]
  {parameters : OddFieldParameters F r f} {rank : 3 ≤ n}
  {Msys : ModularSystem 2 family.K O family.k}
  {iota : PrimeRegularRootEmbedding 2 family.k family.K (Spin n F N)}
  {b : LiteralPrimitiveBlock family.k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock family.k (Spin n F N))]

/-- Exact source scope of FYZ Theorem 5.16, followed by the published Spath
single-block formulation. The antecedent concerns the actual Spin field
action, not a supplied selector. The nonexceptional guard is retained for
the asserted universal two-prime cover presentation of Omega. -/
structure FYZ516SpathSource
    (D : GGGRContext parameters rank Msys iota b)
    (S : FieldActionSource n F r f parameters N)
    (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters rank N)
    (presentation : OmegaPrincipalPresentation (n := n) (F := F) family block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (cover : EllPrimeCoverSource 2 family.H)
    (physical : PhysicalFamilySource family)
    (spinRoots : iota = groupRoot Msys (Spin n F N))
    (familyRoots : family.iota = groupRoot Msys family.H) : Prop where
  apply516 : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F) →
    (n, Nat.card F) ≠ (3, 3) →
    (∀ (e : FieldGroup f) (phi : IBr iota), Supported iota b phi →
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F S e) = phi) →
    Nonempty (PublishedBlockWitness (family.problem block))

/-- The exact FYZ antecedent is constructed by the all-rank GGGR theorem.
Normalization preserves its output matching and every original weight. -/
theorem principalOmega_coherent
    (D : GGGRContext parameters rank Msys iota b) (raw : RankSources D)
    (S : FieldActionSource n F r f parameters N) (field : FieldSources D S)
    (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters rank N)
    (presentation : OmegaPrincipalPresentation (n := n) (F := F) family block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (cover : EllPrimeCoverSource 2 family.H)
    (physical : PhysicalFamilySource family)
    (spinRoots : iota = groupRoot Msys (Spin n F N))
    (familyRoots : family.iota = groupRoot Msys family.H)
    (published : FYZ516SpathSource D S C presentation automorphisms cover
      physical spinRoots familyRoots)
    (normalization : PairNormalizationSource (family.problem block))
    (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F))
    (nonexceptional : (n, Nat.card F) ≠ (3, 3)) :
    Nonempty (CoherentBlockWitness (family.problem block)) := by
  obtain ⟨good⟩ := published.apply516 simple nonexceptional
    (fun e phi supported => principalBrauer_fixed D raw S field e phi supported)
  exact ⟨good.normalize normalization⟩

/-- The nonexceptional principal Omega BAW-good clause of current
Corollary 4.10, with the exact independent Spath relation interpretation. -/
theorem principalOmega_bawGood
    (D : GGGRContext parameters rank Msys iota b) (raw : RankSources D)
    (S : FieldActionSource n F r f parameters N) (field : FieldSources D S)
    (C : TypeBCliffordOrthogonalSourceBinding.Source n F r f parameters rank N)
    (presentation : OmegaPrincipalPresentation (n := n) (F := F) family block)
    (automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (cover : EllPrimeCoverSource 2 family.H)
    (physical : PhysicalFamilySource family)
    (spinRoots : iota = groupRoot Msys (Spin n F N))
    (familyRoots : family.iota = groupRoot Msys family.H)
    (published : FYZ516SpathSource D S C presentation automorphisms cover
      physical spinRoots familyRoots)
    (normalization : PairNormalizationSource (family.problem block))
    (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F))
    (nonexceptional : (n, Nat.card F) ≠ (3, 3))
    (relation : FLZBAWGoodRelation (family.problem block) automorphisms cover)
    (identification : BAWGoodRelationIdentification relation) :
    Nonempty (FLZBAWGoodBlockWitness (family.problem block) automorphisms cover relation) := by
  obtain ⟨good⟩ := principalOmega_coherent D raw S field C presentation automorphisms cover
    physical spinRoots familyRoots published normalization simple nonexceptional
  exact ⟨{
    omega := good.omega
    equivariant := good.equivariant
    blockIsomorphism := fun psi =>
      (identification.relation_iff psi (good.omega psi)).mpr (good.matched psi) }⟩

end Omega

section RelationPassage

variable {P : Definition35Problem}
  {automorphisms : Definition35AutomorphismStabilizerAdapter P}
  {cover : EllPrimeCoverSource P.p P.H}

/-- The explicit same-pair Spath interpretation supplies BAW-goodness.
Only the relation proof changes; the equivalence and action are retained. -/
def CoherentBlockWitness.toBAWGood
    (relation : FLZBAWGoodRelation P automorphisms cover)
    (identification : BAWGoodRelationIdentification relation)
    (good : CoherentBlockWitness P) :
    FLZBAWGoodBlockWitness P automorphisms cover relation where
  omega := good.omega
  equivariant := good.equivariant
  blockIsomorphism psi := (identification.relation_iff psi (good.omega psi)).mpr
    (good.matched psi)

/-- The forward Spath/FLZ passage on every concrete same pair. This is an
E2/U semantic bridge, not a selected-pair or correspondence assumption. -/
structure Definition35PassageSource
    (source : FLZSourceSemantics P automorphisms) : Prop where
  relation_implication : ∀ (psi : Definition35Brauer P) (weight : Definition35Weight P),
    Nonempty (CoherentMatchedCondition P psi weight) →
      source.definition35BlockIsomorphic psi weight

def CoherentBlockWitness.toDefinition35
    (source : FLZSourceSemantics P automorphisms)
    (passage : Definition35PassageSource source) (good : CoherentBlockWitness P) :
    Definition35IBAWBijection P automorphisms source where
  omega := good.omega
  equivariant := good.equivariant
  blockIsomorphism psi := passage.relation_implication psi (good.omega psi) (good.matched psi)

end RelationPassage

section SpinSources

open TypeBCurrentStrictRouting

/-- The subordinate GGGR and field sources on the literal Spin coordinates
of an arbitrary relative-family group. Principality of the target block is
an independently proved constant-one fibre statement. No fixed character,
matching, or Definition 3.5 conclusion is supplied by this record. -/
structure SpinGGGRSources {p n : ℕ} (family : Definition35Family 2)
    (block : family.Block) (coordinates : SpinCoordinates p n family.H)
    (principal : PrincipalSpinCarrier family block n coordinates) where
  O : Type
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O family.K]
  [finiteUpper : Finite (SpecialClifford n coordinates.F)]
  [finiteLower : Finite (Spin n coordinates.F coordinates.norm)]
  [rootsUpper : HasEnoughRootsOfUnity family.K
    (Nat.card (SpecialClifford n coordinates.F))]
  [rootsLower : HasEnoughRootsOfUnity family.K
    (Nat.card (Spin n coordinates.F coordinates.norm))]
  [finiteIrr : Finite (OrdinaryIrreducibleCharacter.Irr family.K
    (Spin n coordinates.F coordinates.norm))]
  [finiteBlocks : Fintype (LiteralPrimitiveBlock family.k
    (Spin n coordinates.F coordinates.norm))]
  Msys : ModularSystem 2 family.K O family.k
  familyRoot : family.iota = groupRoot Msys family.H
  spinBlock : LiteralPrimitiveBlock family.k (Spin n coordinates.F coordinates.norm)
  context : GGGRContext coordinates.parameters principal.rankAtLeastThree Msys
    (groupRoot Msys (Spin n coordinates.F coordinates.norm)) spinBlock
  raw : RankSources context
  fieldAction : FieldActionSource n coordinates.F p coordinates.exponent
    coordinates.parameters coordinates.norm
  fieldSources : FieldSources context fieldAction
  clifford : TypeBCliffordOrthogonalSourceBinding.Source n coordinates.F p
    coordinates.exponent coordinates.parameters principal.rankAtLeastThree coordinates.norm

attribute [instance] SpinGGGRSources.ringO SpinGGGRSources.domainO
  SpinGGGRSources.algebraO

/-- Exact principal Spin field fixation derived from its subordinate data. -/
theorem SpinGGGRSources.fixed {p n : ℕ} {family : Definition35Family 2}
    {block : family.Block} {coordinates : SpinCoordinates p n family.H}
    {principal : PrincipalSpinCarrier family block n coordinates}
    (sources : SpinGGGRSources family block coordinates principal) :
    letI := sources.finiteLower
    ∀ (e : FieldGroup coordinates.exponent)
    (phi : IBr (groupRoot sources.Msys (Spin n coordinates.F coordinates.norm)))
    (supported : Supported
      (groupRoot sources.Msys (Spin n coordinates.F coordinates.norm)) sources.spinBlock phi),
    IrreducibleBrauerCharacter.twist
      (groupRoot sources.Msys (Spin n coordinates.F coordinates.norm)) phi
      (spinFieldAction n coordinates.F sources.fieldAction e) = phi := by
  letI := sources.finiteUpper
  letI := sources.finiteLower
  letI := sources.rootsUpper
  letI := sources.rootsLower
  letI := sources.finiteIrr
  letI := sources.finiteBlocks
  exact principalBrauer_fixed sources.context sources.raw sources.fieldAction sources.fieldSources

end SpinSources

section ExceptionalPublishedPassage

open TypeBQ3TripleCoverCarrier

local instance exceptionalFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

/-- The principal matrix block in the same finite group coordinates as the
canonical central-two quotient. The exceptional cover lies above this
group; this record does not assert that G3 is a universal two-prime cover. -/
structure Q3PrincipalPresentation (family : Definition35Family 2) (block : family.Block) where
  groupEquiv : family.H ≃* G3
  principalCharacter : Definition35Brauer (family.problem block)
  principalCharacter_value_one : ∀ x, principalCharacter.1.1 x = 1

/-- E1 identification of the ACTUAL exceptional two-prime cover and its
literal projection q, including its simple target. -/
structure Q3CoverCalibration (matrixSource : MatrixExceptionalSource)
    (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)
    [Finite X] (cover : EllPrimeCoverSource 2 X) where
  simpleEquiv : cover.S ≃* G3
  quotient_square : simpleEquiv.toMonoidHom.comp cover.quotient =
    q matrixSource freeSource

variable {family : Definition35Family 2} {block : family.Block}
  {O : Type} [CommRing O] [IsDomain O] [Algebra O family.K]
  {matrixSource : MatrixExceptionalSource}
  {freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource}
  [Finite X] [HasEnoughRootsOfUnity family.K (Nat.card X)]

/-- A conditional interpretation of the natural quotient criteria. This
assumption may choose a new matching, and is not asserted to be a published
theorem. The current manuscript application instead transports the proved
full family through `CurrentSpathFiniteSplittingDescent`. This retained
interface is not used for that application. -/
structure Q3NaturalCriterionDescentAssumption
    (data : TypeBCurrentQ3Inputs.Inputs (k := family.k) (K := family.K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource))
    (presentation : Q3PrincipalPresentation family block)
    (cover : EllPrimeCoverSource 2 X)
    (calibration : Q3CoverCalibration matrixSource freeSource cover)
    (physical : PhysicalFamilySource family)
    (familyRoots : family.iota = groupRoot data.before.Msys family.H)
    (downRoots : RootAgreement data.before.rootDown family.iota) : Prop where
  apply_criterion : TypeBCurrentQ3Inputs.AllBlocksCertificate data.before →
    Nonempty (PublishedBlockWitness (family.problem block))

/-- A conditional consequence of the nine-block deductions and the stated
interpretation assumption. The current application uses the established
full-family descent instead. -/
theorem principalQ3_coherent
    (data : TypeBCurrentQ3Inputs.Inputs (k := family.k) (K := family.K) (O := O)
      (matrixSource := matrixSource) (freeSource := freeSource))
    (presentation : Q3PrincipalPresentation family block)
    (cover : EllPrimeCoverSource 2 X)
    (calibration : Q3CoverCalibration matrixSource freeSource cover)
    (physical : PhysicalFamilySource family)
    (familyRoots : family.iota = groupRoot data.before.Msys family.H)
    (downRoots : RootAgreement data.before.rootDown family.iota)
    (interpretation : Q3NaturalCriterionDescentAssumption data presentation cover calibration
      physical familyRoots downRoots)
    (normalization : PairNormalizationSource (family.problem block)) :
    Nonempty (CoherentBlockWitness (family.problem block)) := by
  obtain ⟨good⟩ := interpretation.apply_criterion data.allBlocks
  exact ⟨good.normalize normalization⟩

end ExceptionalPublishedPassage

end ModularRep.PaperProofs.TypeBCurrentPrincipalBijection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
