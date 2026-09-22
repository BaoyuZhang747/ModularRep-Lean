import ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly
import ModularRep.PaperProofs.OddTwoTypeASourceJoin
import ModularRep.PaperProofs.EvenFieldFLZ57CentrelessGate
import ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
import ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin
import ModularRep.PaperProofs.OddTwoActualStabilizerTriple
import ModularRep.PaperProofs.OddTwoDefinition35OwnReduction

/-!
# The literal odd-field FLZ 5.7 application, retaining only its block maps

The sole ambient H_G family is identified with the canonical family of a
fixed LiteralFengMalleProblem. Actual algebraic Sp coordinates identify its
Steinberg map with entrywise |F|-power and its finite points with those same
matrices. The full-cover input is on that Sp projection. Every relative
pair and strict block remains in the existing unfiltered FullHG carrier.

The full-field hypothesis below uses actual CSp/Sp orbits, stabilizers
and modular representation extensions. The E2 map source includes the
choice of FLZ's groups inside the field group and restriction to them.
It also retains FLZ Remark 5.4 (with FM Corollary 4.6) and the map consequence
of FLZ 5.2/5.7. These sources are not instantiated here; all algebraic,
block and root interpretations remain explicit.

K consumes the given Hypothesis 5.5(b) packet, combines the returned maps,
and applies the already fixed forward FM 3.4 gate. No CompletedPrincipalSeeds,
new central descent, arbitrary final predicate or same-final-map assertion
is a premise. The remaining principal work is not discharged by this gate.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZFullHG
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoDefinition35GlobalAssembly
open ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
open ModularRep.PaperProofs.OddTwoActualStabilizerTriple

-- The accepted full-H_G carrier and coverage are in Type. Keep this
-- application in that same universe; all its finite fields remain included.
variable {n : ℕ} {F : Type} [Field F] [Fintype F]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _
local instance fieldAutomorphismFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

/-! ## Actual regular-overgroup actions and Assumption 5.3 -/

abbrev RegularAmbient := CSp n F ⋊[cspFieldAction] (F ≃+* F)

/-- The literal quotient of the regular overgroup, identity on the field
factor. The compatibility is the already proved entrywise quotient square. -/
def regularToBrough : RegularAmbient (n := n) (F := F) →* Ambient (n := n) (F := F) :=
  SemidirectProduct.map (cspProjection n F) (MonoidHom.id _) (by
    intro sigma
    apply MonoidHom.ext
    intro g
    exact (pcspFieldAction_projection sigma g).symm)

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (cover : OddSymplecticFullCoverSource n F)
variable (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))

/-- The regular action is the unique lift of its fixed natural projective
action through the actual full-cover automorphism map. -/
def regularAction : RegularAmbient (n := n) (F := F) →* MulAut (Sp n F) :=
  (projectiveAutEquiv cover lifting).symm.toMonoidHom.comp
    (S.fullAut.toMonoidHom.comp regularToBrough)

theorem regularAction_field (sigma : F ≃+* F) :
    regularAction S cover lifting (SemidirectProduct.inr sigma) = spFieldAction sigma := by
  apply (projectiveAutEquiv cover lifting).injective
  change (projectiveAutEquiv cover lifting)
      ((projectiveAutEquiv cover lifting).symm
        (S.fullAut (regularToBrough (SemidirectProduct.inr sigma)))) = _
  rw [MulEquiv.apply_symm_apply]
  change S.fullAut (SemidirectProduct.inr sigma) = pspFieldAction sigma
  exact S.fullAut_field sigma

/-- Standard E1 identification of this computed lift with ordinary matrix
conjugation. It is a group-coordinate law on the fixed action, not another
choice of action or any character property. -/
structure RegularActionCoordinates : Prop where
  conjugation_matrix : ∀ (c : CSp n F) (g : Sp n F),
    ((regularAction S cover lifting (SemidirectProduct.inl c) g : Sp n F) :
        Matrix (Coordinate n) (Coordinate n) F) =
      cspMatrix n F c * (g : Matrix (Coordinate n) (Coordinate n) F) *
        cspMatrix n F c⁻¹

variable (P : LiteralFengMalleProblem n F)

def fieldStabilizer (psi : IBr P.iota) : Subgroup (F ≃+* F) :=
  letI : MulAction (F ≃+* F) (IBr P.iota) :=
    rightAutomorphismAction (spFieldAction (n := n) (F := F))
  MulAction.stabilizer (F ≃+* F) psi

abbrev FieldExtensionGroup (psi : IBr P.iota) :=
  Sp n F ⋊[spFieldAction.comp (fieldStabilizer P psi).subtype] (fieldStabilizer P psi)

/-- Literal representation extension to Sp semidirect its actual field
stabilizer. The same vector space and the inl restriction are fixed; no
independent root or ambient Brauer-character lift is chosen. -/
def FieldExtension (psi : IBr P.iota) : Prop :=
  ∃ V : FDRep P.k (Sp n F), Representation.IsIrreducible V.ρ ∧
    Representation.brauerCharacterOfRootEmbedding V.ρ P.iota = psi.1 ∧
    ∃ extended : Representation P.k (FieldExtensionGroup P psi) V,
      ∀ g : Sp n F, extended (SemidirectProduct.inl g) = V.ρ g

/-- One representative of an actual CSp orbit satisfying the stronger
full-field hypothesis used for Assumption 5.3. Factorization is tested on
the inl/inr coordinates of CSp semidirect Aut(F). -/
structure Assumption53Representative (psi : IBr P.iota) where
  representative : IBr P.iota
  inRegularOrbit : ∃ c : CSp n F,
    inverseOpHom (regularAction S cover lifting) (SemidirectProduct.inl c) • psi = representative
  stabilizerFactorization : ∀ g : RegularAmbient (n := n) (F := F),
    (inverseOpHom (regularAction S cover lifting) g • representative = representative ↔
      (inverseOpHom (regularAction S cover lifting) (SemidirectProduct.inl g.left) •
          representative = representative ∧
        inverseOpHom (spFieldAction (n := n) (F := F)) g.right •
          representative = representative))
  fieldExtension : FieldExtension P representative

structure LiteralAssumption53 : Prop where
  representative : ∀ psi : IBr P.iota,
    Nonempty (Assumption53Representative S cover lifting P psi)

/-- Exact E2: FLZ Remark 5.4, p.30, explicitly applies Assumption 5.3 to
all symplectic two-Brauer characters, citing FM Corollary 4.6. The source
interpretation uses these same actual regular and field actions. This
entry does not supply an iBAW seed or any weight correspondence. -/
structure FLZRemark54Source : Prop where
  assumption53 : RegularActionCoordinates S cover lifting →
    LiteralAssumption53 S cover lifting P

/-! ## Sole ambient family, actual Frobenius, and full relative semantics -/

variable (support : OperationsBrauerSupport P.iota P.irreducibleBrauerInjective
  P.blockSource.operations)
variable (reduction : ∀ (b : LiteralBlock P) (w : LiteralWeightFibre P.blockSource b),
  SelectedLocalReductionSource P.blockSource b w)
variable {pDef : ℕ} [CharP F pDef]
variable (scope : FLZFullHGUniverse pDef 2)
variable (coverage : FullHGDefinition35Coverage scope)
variable (blockSource : FullHGBlockSource coverage)
variable (strictSource : FullHGStrictQuasiIsolationAdapter coverage)

def familyGroupEquivOfEq {ell : ℕ} {A B : Definition35Family.{0} ell} (h : A = B) :
    A.H ≃* B.H := by
  cases h
  exact MulEquiv.refl _

/-- Exact E1 source coordinates. No algebraic closure, Frobenius or fixed
point theorem is reconstructed: their actual matrix equations are retained.
The sole ambient family is literally the canonical family of P, including
its coefficient structures, roots, primitive blocks and local reductions.
The finite fixed-point map is COMPUTED from this equality and coverage. -/
structure AmbientBinding where
  family_eq : (coverage.presentation scope.ambientPair).family = literalFamily P support reduction
  fieldCharacteristic : CharP F pDef
  Closure : Type
  [fieldClosure : Field Closure]
  [algClosedClosure : IsAlgClosed Closure]
  [charClosure : CharP Closure pDef]
  fieldEmbedding : F →+* Closure
  exponent : ℕ
  exponentPositive : 0 < exponent
  fieldCard : Fintype.card F = pDef ^ exponent
  algebraicEquiv : scope.ambient.algebraicPair.AlgebraicGroup ≃* Sp n Closure
  frobenius_matrix : ∀ x : scope.ambient.algebraicPair.AlgebraicGroup,
    ((algebraicEquiv (scope.ambient.algebraicPair.steinberg x) : Sp n Closure) :
        Matrix (Coordinate n) (Coordinate n) Closure) =
      ((algebraicEquiv x : Sp n Closure) :
        Matrix (Coordinate n) (Coordinate n) Closure).map (fun a => a ^ Fintype.card F)
  fixedPoint_matrix : ∀ g : Sp n F,
    ((algebraicEquiv
        ((coverage.presentation scope.ambientPair).fixedPointEquiv
          ((familyGroupEquivOfEq family_eq).symm g)).1 : Sp n Closure) :
        Matrix (Coordinate n) (Coordinate n) Closure) =
      (g : Matrix (Coordinate n) (Coordinate n) F).map fieldEmbedding

attribute [instance] AmbientBinding.fieldClosure AmbientBinding.algClosedClosure
  AmbientBinding.charClosure

abbrev relativeOwnWeight (family : Definition35Family.{0} 2) (b : family.Block)
    (w : Definition35Weight (family.problem b)) : CharacterWeight 2 family.K family.H :=
  selectedCharacterWeight family.blockSource b w

abbrev relativeArguments (family : Definition35Family.{0} 2) (b : family.Block)
    (psi : Definition35Brauer (family.problem b))
    (w : Definition35Weight (family.problem b))
    (R : OwnNormalizerReduction (k := family.k) (relativeOwnWeight family b w)) :
    BlockTripleArguments 2 family.k family.K :=
  arguments family.iota (family.automorphisms b).gamma psi.1
    (relativeOwnWeight family b w) R

/-- Both source conventions meet at the OWN normalizer: the ambient root
restricts along inclusion, and the EXACT selected quotient reduction root
pulls back along N -> N/Q. Neither convention may be changed independently. -/
def RelativeRootsCompatible (family : Definition35Family.{0} 2) (b : family.Block)
    (w : Definition35Weight (family.problem b))
    (R : OwnNormalizerReduction (k := family.k) (relativeOwnWeight family b w)) : Prop :=
  RootCompatibleAlong family.iota R.root
      (Subgroup.normalizer ((relativeOwnWeight family b w).subgroup : Set family.H)).subtype ∧
    RootCompatibleAlong (family.localReduction b w).iota R.root
      (OddTwoDefinition35OwnReduction.normalizerProjection
        (relativeOwnWeight family b w).subgroup)

/-- The explicit full-H_G source interpretation at this cut. The original
scope predicates must mean the published algebraic notions and all eligible
pairs; coverage must present their actual fixed-point groups. These remain
E1/U, not predicates authenticated by their names. The displayed strict iff
and compatible own-normalizer semantics apply to EVERY pair and block.
The generic TypeAInputSemantics record used here contains only coefficient,
catalogue, root and local block support data, with no type-A hypothesis.
The additional coherent-root existence prevents the interpretation iff
from being vacuous. Its RHS includes actual full-raw containment and the
SAME standard relation on the computed tuple; it asserts neither relation.
The standard predicate must mean the published modular block-triple
definition. Every matched object and every coherent root packet is used. -/
structure FullHGInterpretation where
  strictModel : ∀ pair : FullHG scope,
    EvenFieldFLZ57CentrelessGate.SourceStrictBlockModel
      (coverage.presentation pair).family.Block
  strict_iff : ∀ (pair : FullHG scope) (b : (coverage.presentation pair).family.Block),
    (strictModel pair).IsStrict b ↔ strictSource.predicate pair b
  blockSemantics : ∀ pair : FullHG scope,
    OddTwoTypeASourceJoin.TypeAInputSemantics (coverage.presentation pair).family
  standard : ∀ pair : FullHG scope,
    BlockTripleSourceSemantics 2 (coverage.presentation pair).family.k
      (coverage.presentation pair).family.K
  coherentReduction : ∀ (pair : FullHG scope)
    (b : (coverage.presentation pair).family.Block)
    (w : Definition35Weight ((coverage.presentation pair).family.problem b)),
    ∃ R : OwnNormalizerReduction (k := (coverage.presentation pair).family.k)
      (relativeOwnWeight (coverage.presentation pair).family b w),
      RelativeRootsCompatible (coverage.presentation pair).family b w R
  definition35_iff : ∀ (pair : FullHG scope)
    (b : (coverage.presentation pair).family.Block)
    (psi : Definition35Brauer ((coverage.presentation pair).family.problem b))
    (w : Definition35Weight ((coverage.presentation pair).family.problem b))
    (R : OwnNormalizerReduction (k := (coverage.presentation pair).family.k)
      (relativeOwnWeight (coverage.presentation pair).family b w)),
    RelativeRootsCompatible (coverage.presentation pair).family b w R →
    ((blockSource.source pair b).definition35BlockIsomorphic psi w ↔
      (rawStabilizer ((coverage.presentation pair).family.automorphisms b).gamma
          (relativeOwnWeight (coverage.presentation pair).family b w) ≤
        globalStabilizer (coverage.presentation pair).family.iota
          ((coverage.presentation pair).family.automorphisms b).gamma psi.1) ∧
      (standard pair).blockIsomorphic
        (relativeArguments (coverage.presentation pair).family b psi w R))

/-! ## Exact source theorem and short K consumers -/

/-- E2 composite from FLZ Proposition 5.2 and Theorem 5.7, including the
choice of permissible groups inside the full field group and restriction
of the stronger full-field premise. It retains the actual equivariant
Sp block maps, so no prime-to-two-cover premise on Sp or later
BAW-good/eq.(3.17) passage is used. The full-H_G, strict-block and
Definition 3.5 interpretations remain fixed by the parameters.
No arbitrary conclusion or assumed principal supplier occurs here. -/
structure FLZTheorem57MapSource : Prop where
  applyTheorem57 :
    AmbientBinding P support reduction scope coverage →
    FullHGInterpretation scope coverage blockSource strictSource →
    InputSemantics P →
    RegularActionCoordinates S cover lifting →
    LiteralAssumption53 S cover lifting P →
    FullHGRelativeHypothesis55StrictBlocks blockSource strictSource →
    Nonempty (BlockMapFamily (literalFamily P support reduction))

variable (binding : AmbientBinding P support reduction scope coverage)
variable (interpretation : FullHGInterpretation scope coverage blockSource strictSource)
variable (input : InputSemantics P)
variable (coordinates : RegularActionCoordinates S cover lifting)
variable (assumptionSource : FLZRemark54Source S cover lifting P)
variable (theoremSource : FLZTheorem57MapSource S cover lifting P support reduction
  scope coverage blockSource strictSource)

include binding interpretation input coordinates assumptionSource theoremSource in
/-- K consumes the actual Hypothesis 5.5(b) packet and combines only the
returned fibre maps. The completed principal supplier is not assumed here. -/
def globalMap (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource) :
    LiteralGlobalMap P :=
  literalGlobalMap P support reduction
    (Classical.choice (theoremSource.applyTheorem57 binding interpretation input coordinates
      (assumptionSource.assumption53 coordinates) strictBlocks))

include binding interpretation input coordinates assumptionSource theoremSource in
/-- The fixed forward FM 3.4 consumer supplies the independent original
Spath target, using exactly the constructed global map. Existence only. -/
theorem originalIBAW
    (strictBlocks : FullHGRelativeHypothesis55StrictBlocks blockSource strictSource)
    (O : LiteralDiagonalFieldRealisation n F) (target : TargetData P)
    (fm34 : FengMalleProposition34Source P O target)
    (cor46 : LiteralFengMalleCorollary46Certificate P O) :
    OddTwoLiteralSpathTarget.OriginalIBAW target.toProblem :=
  originalIBAW_of_literalGlobalMap P O target fm34 input
    (globalMap S cover lifting P support reduction scope coverage blockSource strictSource
      binding interpretation input coordinates assumptionSource theoremSource strictBlocks) cor46

end ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
