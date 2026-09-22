import ManuscriptIBAW.Jordan.TypeB
import ManuscriptIBAW.Jordan.SeriesBinding
import ModularRep.PaperProofs.TypeBCurrentStrictRouting
import ModularRep.PaperProofs.TypeBCurrentBrauerTransport
import ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover
import ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource
import ModularRep.PaperProofs.CurrentFiniteSplittingAssembly
import ModularRep.PaperProofs.TypeBModularGroupRootBinding

/-!
# The Type B application of Jordan reduction

Spin is the full universal covering group in this application. The universal
prime-to-two cover is instead constructed on the specified matrix Omega
group from the central kernel of Spin, which has order two.

The external statement combines Feng–Li–Zhang, Theorem 5.7, passage to the
quotient by the central 2-core, and Späth, Theorem 4.4. It assumes the
hypotheses for each label and every strict block, and gives witnesses for
the primitive blocks of Omega. Both hypotheses are constructed before
applying this source.

The proof chooses dominating blocks from their images in the group algebra.
The separately assumed construction of a compatible family then combines the
complete block witnesses. The compatible bijections and local data chosen in
this step need not equal the initial ones.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ManuscriptIBAW.Jordan.TypeBLocalized

open ModularRep.PaperProofs
open ModularRep FDRepSimpleClassKZero CharacterWeight
open TypeBCliffordCarriers TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldFLZFullHG EvenFieldFLZ318FixedTheoremGate
open TypeBCliffordOrthogonalSourceBinding

/-- The assumed relation concerns the same relative class. Each finite group
uses a splitting ordinary field. No algebraic closure of a discrete
valuation field is required. The relation is specified for every character,
weight representative and compatible reduction at the normaliser of its
weight subgroup. -/
structure FullHGInterpretation {p : ℕ} (scope : FLZFullHGUniverse p 2)
    (coverage : FullHGDefinition35Coverage scope)
    (blockSource : FullHGBlockSource coverage)
    (strictSource : FullHGStrictQuasiIsolationAdapter coverage) where
  strictModel : ∀ pair : FullHG scope,
    EvenFieldFLZ57CentrelessGate.SourceStrictBlockModel
      (coverage.presentation pair).family.Block
  strict_iff : ∀ (pair : FullHG scope) (b : (coverage.presentation pair).family.Block),
    (strictModel pair).IsStrict b ↔ strictSource.predicate pair b
  ordinaryRoots : ∀ pair : FullHG scope,
    HasEnoughRootsOfUnity (coverage.presentation pair).family.K
      (Nat.card (coverage.presentation pair).family.H)
  ambient_idempotent : ∀ (pair : FullHG scope)
      (b : (coverage.presentation pair).family.Block),
    (coverage.presentation pair).family.blockSource.operations.ambientBlockData.blockIdempotent b =
      (coverage.presentation pair).family.blockIdempotent b
  physical : ∀ pair : FullHG scope,
    GuardedBlockCompatibility (coverage.presentation pair).family.iota
      (coverage.presentation pair).family.blockSource.operations
  standard : ∀ pair : FullHG scope,
    OddTwoCentralTwoRelationInflation.BlockTripleSourceSemantics 2
      (coverage.presentation pair).family.k (coverage.presentation pair).family.K
  coherentReduction : ∀ (pair : FullHG scope)
      (b : (coverage.presentation pair).family.Block)
      (w : Definition35Weight ((coverage.presentation pair).family.problem b)),
    ∃ R : OddTwoActualStabilizerTriple.OwnNormalizerReduction
        (k := (coverage.presentation pair).family.k)
        (OddTwoFLZ57LiteralMapSource.relativeOwnWeight (coverage.presentation pair).family b w),
      OddTwoFLZ57LiteralMapSource.RelativeRootsCompatible
        (coverage.presentation pair).family b w R
  definition35_iff : ∀ (pair : FullHG scope)
      (b : (coverage.presentation pair).family.Block)
      (psi : Definition35Brauer ((coverage.presentation pair).family.problem b))
      (w : Definition35Weight ((coverage.presentation pair).family.problem b))
      (R : OddTwoActualStabilizerTriple.OwnNormalizerReduction
        (k := (coverage.presentation pair).family.k)
        (OddTwoFLZ57LiteralMapSource.relativeOwnWeight (coverage.presentation pair).family b w)),
    OddTwoFLZ57LiteralMapSource.RelativeRootsCompatible
      (coverage.presentation pair).family b w R →
    ((blockSource.source pair b).definition35BlockIsomorphic psi w ↔
      (OddTwoActualStabilizerTriple.rawStabilizer
        ((coverage.presentation pair).family.automorphisms b).gamma
        (OddTwoFLZ57LiteralMapSource.relativeOwnWeight (coverage.presentation pair).family b w) ≤
      OddTwoActualStabilizerTriple.globalStabilizer (coverage.presentation pair).family.iota
        ((coverage.presentation pair).family.automorphisms b).gamma psi.1) ∧
      (standard pair).blockIsomorphic
        (OddTwoFLZ57LiteralMapSource.relativeArguments (coverage.presentation pair).family b psi w R))

variable {n p f : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F p]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [CommRing O] [IsDomain O] [Algebra O K]
  [Finite (SpecialClifford n F)] [NeZero f]
  (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
  (N : NormSource n F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)


local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _
local instance omegaFintype : Fintype (TypeBOrthogonalOmegaCarriers.Omega n F) := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k (Spin n F N))] [Fintype (LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F))]
  (Msys : ModularSystem 2 K O k)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  (iotaS : PrimeRegularRootEmbedding 2 k K (TypeBOrthogonalOmegaCarriers.Omega n F))
  (blocksG : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val))
  (blocksS : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F) => b.val))
  (localG : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaG)
  (localS : CurrentFiniteSplittingFamily.PrimitivePhysicalSource iotaS)


variable (scope : FLZFullHGUniverse p 2)
  (coverage : FullHGDefinition35Coverage scope)

/-- Source identifications (E1/U) for the specified ambient algebraic pair. Its
finite group presentation is the primitive Spin family above. The scalar and
vector equations identify algebraic Frobenius with the prescribed power map
on the field. -/
structure AmbientBinding where
  family_eq : (coverage.presentation scope.ambientPair).family = (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := Spin n F N) iotaG (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG Nat.prime_two localG)
  Closure : Type
  [fieldClosure : Field Closure]
  [algClosedClosure : IsAlgClosed Closure]
  [charClosure : CharP Closure p]
  fieldEmbedding : F →+* Closure
  algebraicNorm : NormSource n Closure
  algebraicEquiv : scope.ambient.algebraicPair.AlgebraicGroup ≃*
    Spin n Closure algebraicNorm
  algebraicFrobenius : Clifford n Closure →+* Clifford n Closure
  frobenius_scalar : ∀ a : Closure,
    algebraicFrobenius (algebraMap Closure (Clifford n Closure) a) =
      algebraMap Closure (Clifford n Closure) (a ^ (p ^ f))
  frobenius_vector : ∀ v : Vector n Closure,
    algebraicFrobenius (CliffordAlgebra.ι (splitForm n Closure) v) =
      CliffordAlgebra.ι (splitForm n Closure) (fun i => v i ^ (p ^ f))
  frobenius_spin : ∀ x,
    toClifford n Closure (algebraicEquiv (scope.ambient.algebraicPair.steinberg x)).val =
      algebraicFrobenius (toClifford n Closure (algebraicEquiv x).val)
  baseChange : Clifford n F →+* Clifford n Closure
  baseChange_scalar : ∀ a : F,
    baseChange (algebraMap F (Clifford n F) a) =
      algebraMap Closure (Clifford n Closure) (fieldEmbedding a)
  baseChange_vector : ∀ v : Vector n F,
    baseChange (CliffordAlgebra.ι (splitForm n F) v) =
      CliffordAlgebra.ι (splitForm n Closure) (fun i => fieldEmbedding (v i))
  fixedPoint_coordinates : ∀ g : (Spin n F N),
    toClifford n Closure (algebraicEquiv
      ((coverage.presentation scope.ambientPair).fixedPointEquiv
        ((OddTwoFLZ57LiteralMapSource.familyGroupEquivOfEq family_eq).symm g)).val).val =
      baseChange (toClifford n F g.val)

attribute [instance] AmbientBinding.fieldClosure AmbientBinding.algClosedClosure
  AmbientBinding.charClosure

/-- The image of the primitive block under the constructed central quotient.
This is the block correspondence for a central 2-subgroup. It asserts no
character bijection or condition on stabilisers or the inductive condition. -/
structure DominationSource : Prop where
  dominating : ∀ b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F),
    ∃ a : LiteralPrimitiveBlock k (Spin n F N), MonoidAlgebra.mapDomain (spinProjection n F parameters rank N C) a.val = b.val

variable (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
  (fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)) (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F))

def actualCover
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C))
    (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)) (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)) :
    EllPrimeCoverSource 2 (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  TypeBMatrixOmegaPrimeToTwoCover.identityEllPrimeCover n F parameters rank N C
    centre fullCover simple nonabelian

omit [Finite (SpecialClifford n F)] [NeZero f] in
@[simp] theorem actualCover_quotient :
    (actualCover parameters rank N C centre fullCover simple nonabelian).quotient =
      MonoidHom.id (TypeBOrthogonalOmegaCarriers.Omega n F) := rfl

variable (fs : FieldActionSource n F p f parameters N)
  (blockSource : FullHGBlockSource coverage)
  (strictSource : FullHGStrictQuasiIsolationAdapter coverage)

variable (CGeo : GeometricContext (ell := 2) (k := k)
  (S := TypeBCurrentBrauerTransport.SemisimpleIndex (n := n) (p := p) (F := F))
  (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs))

/-- The original primitive Spin family, fixed before the Jordan source is applied. -/
abbrev spinFamily := CurrentFiniteSplittingFamily.primitiveFamily
  (p := 2) (k := k) (K := K) (G := Spin n F N) iotaG
  (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG)
  blocksG Nat.prime_two localG

/-- Transport the ambient strict label along the equality of complete families.
The block is the same primitive idempotent in the original Spin group algebra. -/
def ambientStrictLabel
    (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource) :
    (spinFamily N iotaG blocksG localG).Block →
      (interpretation.strictModel scope.ambientPair).Dual := fun b =>
  (interpretation.strictModel scope.ambientPair).label
    (cast (congrArg (fun family : Definition35Family.{0} 2 => family.Block)
      binding.family_eq.symm) b)

variable (parametersG : TypeBCurrentBrauerTransport.ParameterSource fs (k := k))

/-- The geometric, Broué–Michel and strict block labels concern one specified
Spin family. The finite dual is the given rational PCSp group. Its rational
conjugacy class is the fixed index, and its primitive idempotents are those
used by the nonprincipal Brauer argument. The algebraic dual embedding and
source interpretation remain the specified U identifications. The structure
contains no character representative or inductive condition conclusion. -/
structure AmbientSeriesBinding
    (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
    extends SeriesBinding (spinFamily N iotaG blocksG localG) CGeo
      (ambientStrictLabel N iotaG blocksG localG scope coverage blockSource strictSource
        binding interpretation) where
  dualEquiv : CGeo.DualFiniteGroup ≃* TypeBConformalDualCarriers.PCSp F n
  parameter_class : ∀ s, ConjClasses.mk (dualEquiv (CGeo.parameter s)) = s.val
  semisimple_iff : ∀ t, CGeo.semisimple t ↔ Nat.Coprime p (orderOf (dualEquiv t))
  parameter_idempotent : ∀ s, CGeo.seriesIdempotent s = parametersG.idempotent s
  parameter_action : ∀ e s,
    ConjClasses.mk (dualEquiv (CGeo.dualFieldAction e (CGeo.parameter s))) =
      (parametersG.action e s).val

/-- The block parameter in the primitive sum is the same rational class
used by the nonprincipal Brauer construction. Both identifications follow
from support of this original primitive idempotent. -/
theorem AmbientSeriesBinding.block_parameter_class
    {binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage}
    {interpretation : FullHGInterpretation scope coverage blockSource strictSource}
    (series : AmbientSeriesBinding parameters N iotaG blocksG localG scope coverage
      fs blockSource strictSource CGeo parametersG binding interpretation)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    ConjClasses.mk (series.dualEquiv (series.blockParameter b)) =
      (parametersG.blockParameter b).val := by
  obtain ⟨s, hs⟩ := series.toSeriesBinding.every_block_belongs b
  have hparameter : parametersG.blockParameter b = s := by
    apply (parametersG.unique b s).mp
    change b.val * CGeo.seriesIdempotent s = b.val at hs
    simpa only [series.parameter_idempotent] using hs
  have hconj := (series.toSeriesBinding.block_belongs_iff b s).mp hs
  have hclass := ConjClasses.mk_eq_mk_iff_isConj.mpr
    (series.dualEquiv.toMonoidHom.map_isConj hconj)
  exact hclass.trans ((series.parameter_class s).trans (congrArg Subtype.val hparameter.symm))

/-- The already restricted first hypothesis, including the geometric choice
for every rational semisimple class and every original Brauer orbit. -/
def PerLabelCondition : Prop :=
  GeneralPerLabelHypothesis
    (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) iotaG CGeo

/--
The E2 combination of the published Jordan theorem and passage to the
quotient by the central 2-core. It assumes the proved hypothesis for each
label. Choice of representatives and restriction are not conclusions of this
source. The original and quotient roots come from the same modular system.
Each block idempotent is the image of the chosen upstairs primitive block.

The statement concerns every such block and retains all hypotheses of the
published reduction. It does not assert the proposition for the full field
Brauer action or the inductive condition for all groups of type B. Its
conclusion specifies the roots, weights, central quotients, extensions and
complete local conditions.
-/
structure FLZ57PerLabelDeflatedSource : Prop where
  applyTheorem57 :
    (n, Nat.card F) ≠ (3, 3) →
    ∀ (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
      (interpretation : FullHGInterpretation scope coverage blockSource strictSource),
    AmbientSeriesBinding parameters N iotaG blocksG localG scope coverage fs blockSource strictSource
      CGeo parametersG binding interpretation →
    iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N) →
    iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F) →
    SpathCoefficientField 2 k Nat.prime_two →
    PerLabelCondition (parameters := parameters) (N := N)
      (fs := fs) (iotaG := iotaG) (CGeo := CGeo) →
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource →
    ∀ (a : LiteralPrimitiveBlock k (Spin n F N)) (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega n F)),
      MonoidAlgebra.mapDomain (spinProjection n F parameters rank N C) a.val = b.val →
      Nonempty (BlockWitness (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
        (actualCover parameters rank N C centre fullCover simple nonabelian) b)

/-- Apply Jordan reduction to the already established strict block and
Brauer hypotheses, selecting the actual dominating block internally. -/
theorem blocks_of_hypotheses
    (exception : (n, Nat.card F) ≠ (3, 3))
    (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
    (series : AmbientSeriesBinding parameters N iotaG blocksG localG scope coverage fs blockSource strictSource
      CGeo parametersG binding interpretation)
    (rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N))
    (rootS : iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F))
    (coefficient : SpathCoefficientField 2 k Nat.prime_two)
    (domination : DominationSource (k := k) parameters rank N C)
    (cited : FLZ57PerLabelDeflatedSource parameters rank N C Msys iotaG iotaS
      blocksG blocksS localG localS scope coverage centre fullCover simple nonabelian
      fs blockSource strictSource CGeo parametersG)
    (geometry : GeometricSelection
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) CGeo)
    (assumption53 : TypeBCurrentBrauerTransport.BrauerHypothesis fs iotaG)
    (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource) :
    ∀ b, Nonempty (BlockWitness (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
      (actualCover parameters rank N C centre fullCover simple nonabelian) b) := by
  intro b
  obtain ⟨a, ha⟩ := domination.dominating b
  exact cited.applyTheorem57 exception binding interpretation series rootG rootS coefficient
    (TypeB.generalPerLabel fs iotaG CGeo geometry assumption53) strictBlocks a b ha

/-- The published construction for a family of blocks applies to the complete
block witnesses just constructed, using the same primitive family and cover. -/
theorem full_family_of_hypotheses
    (exception : (n, Nat.card F) ≠ (3, 3))
    (binding : AmbientBinding (f := f) N iotaG blocksG localG scope coverage)
    (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
    (series : AmbientSeriesBinding parameters N iotaG blocksG localG scope coverage fs blockSource strictSource
      CGeo parametersG binding interpretation)
    (rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys (Spin n F N))
    (rootS : iotaS = TypeBModularGroupRootBinding.groupRoot Msys (TypeBOrthogonalOmegaCarriers.Omega n F))
    (coefficient : SpathCoefficientField 2 k Nat.prime_two)
    (domination : DominationSource (k := k) parameters rank N C)
    (cited : FLZ57PerLabelDeflatedSource parameters rank N C Msys iotaG iotaS
      blocksG blocksS localG localS scope coverage centre fullCover simple nonabelian
      fs blockSource strictSource CGeo parametersG)
    (assembly : CurrentFiniteSplittingAssembly.Source)
    (geometry : GeometricSelection
      (MulAut.conjNormal (H := SpinSubgroup n F N)) (spinFieldAction n F fs) CGeo)
    (assumption53 : TypeBCurrentBrauerTransport.BrauerHypothesis fs iotaG)
    (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource) :
    Nonempty (FamilyWitness (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
      (actualCover parameters rank N C centre fullCover simple nonabelian)) := by
  let : Algebra O (CurrentFiniteSplittingFamily.primitiveFamily
      (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F)
      iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS)
      blocksS Nat.prime_two localS).K := inferInstanceAs (Algebra O K)
  apply CurrentFiniteSplittingAssembly.fullFamily (CurrentFiniteSplittingFamily.primitiveFamily (p := 2) (k := k) (K := K) (G := TypeBOrthogonalOmegaCarriers.Omega n F) iotaS (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaS) blocksS Nat.prime_two localS)
    (actualCover parameters rank N C centre fullCover simple nonabelian) Msys assembly
    localS.ordinaryRoots rootS coefficient localS.idempotent localS.blockCompatibility
    localS.reduction_roots
  exact blocks_of_hypotheses parameters rank N C Msys iotaG iotaS blocksG blocksS
    localG localS scope coverage centre fullCover simple nonabelian fs blockSource strictSource CGeo parametersG
    exception binding interpretation series rootG rootS coefficient domination cited geometry assumption53 strictBlocks

end ManuscriptIBAW.Jordan.TypeBLocalized


/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
