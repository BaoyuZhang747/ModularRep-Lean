import ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
import ModularRep.PaperProofs.IntrinsicGlobalToRepresentativeMaps
import ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
import ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII
import ModularRep.BrauerCharacterCommonRootCompatibility
import ModularRep.NavarroLocalReductionInflationBlockCompatibility

/-!
# A literal original Spath Definition 4.1 target for odd-field PSp

This file defines a target independently of a Feng--Malle certificate. The
group is the displayed matrix quotient PSp, the prime is two, and the cover
is the actual identity prime-to-two cover constructed from the full cover.
It does not assert that the target is inhabited.

The global map determines the radical partition and all representative maps
by the existing intrinsic-fibre theorems. The remaining fields state actual
central character restrictions, Brauer extensions, intermediate block
induction, and both normalizations at the trivial radical. There is no
caller-selected final proposition or modular-character-triple predicate.

The direct-Q/direct-H records below are needed because the older matched
block record uses a selected representative of a weight class. An arbitrary
source radical Q need not equal that representative. Here Q is used in the
actual subgroup maps; H is a subgroup of its actual ambient normalizer.
The finite ambient-group record and the character-extension and block
primitives are reused. No projective-representation foundation is needed.

Source: Spath (2013), Definition 4.1, pp. 182--183. Standard coefficient,
local-reduction, and complete block-catalogue data are explicit E1/E2 inputs.
An eventual published forward theorem must return this fixed target; this
file supplies neither that theorem nor the principal/Jordan hypotheses.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoLiteralSpathTarget

open ModularRep
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal
  (IsBrauerReduction inflateOrdinaryCharacter)

universe u

abbrev X (n : ℕ) (F : Type u) [Field F] := LiteralPSp n F

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) : Fintype H := Fintype.ofFinite _

local instance automorphismFinite : Finite (MulAut (X n F)) :=
  Finite.of_injective (fun a : MulAut (X n F) => (a : X n F → X n F))
    DFunLike.coe_injective

local instance automorphismOppositeFinite : Finite (MulAut (X n F))ᵐᵒᵖ :=
  Finite.of_equiv (MulAut (X n F)) MulOpposite.opEquiv

/-- Compatibility on the eigenvalues used by actual representation
restrictions. This is supplied by restricting one common root convention;
it does not equate zero-extended lift functions for different exponents. -/
def RootCompatibleAlong
    {k K G H : Type u} [Field k] [Field K] [CharP k 2]
    [IsAlgClosed k] [CharZero K] [Group G] [Finite G] [Group H] [Finite H]
    (iotaG : PrimeRegularRootEmbedding 2 k K G)
    (iotaH : PrimeRegularRootEmbedding 2 k K H) (f : H →* G) : Prop :=
  ∀ W : FDRep k G,
    Representation.BrauerRootLiftCompatibleAlong W.ρ iotaG iotaH f

/-- Fixed coefficient and actual local-block data on the literal PSp group.
The trivial radical is standard simple-group data; it is not a partition
or a normalization of any character map. -/
structure Problem (n : ℕ) (F : Type u) [Field F] [Finite F] where
  coverSource : OddSymplecticFullCoverSource n F
  k : Type u
  K : Type u
  [fieldk : Field k]
  [fieldK : Field K]
  [charPk : CharP k 2]
  [algClosedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  ordinarySplitting : IsAlgClosed K
  iota : PrimeRegularRootEmbedding 2 k K (X n F)
  injective : IrreducibleBrauerCharacterInjectivity iota
  blockSource : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := X n F)
    (Block := LiteralPrimitiveBlock k (X n F))
  catalogue_idempotent : ∀ b : LiteralPrimitiveBlock k (X n F),
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  support_transport : OperationsBrauerSupport iota injective blockSource.operations
  localReduction : ∀ (b : LiteralPrimitiveBlock k (X n F))
      (w : LiteralWeightFibre blockSource b),
    SelectedLocalReductionSource blockSource b w
  oneRadical : RadicalSubgroup (p := 2) (G := X n F)
  oneRadical_eq_bot : oneRadical.1 = ⊥

attribute [instance] Problem.fieldk Problem.fieldK Problem.charPk
  Problem.algClosedk Problem.charZeroK

namespace Problem

variable (P : Problem n F)

/-- This is the fixed covering map required by Definition 4.1. -/
abbrev cover : EllPrimeCoverSource 2 (X n F) :=
  P.coverSource.identityEllPrimeCover

include P in
theorem center_eq_bot : Subgroup.center (X n F) = ⊥ :=
  center_eq_bot_of_nonabelian_simple P.coverSource.simple P.coverSource.nonabelian

abbrev Block := LiteralPrimitiveBlock P.k (X n F)

def brauerBlock (psi : IBr P.iota) : P.Block := by
  letI := P.blockSource.operations.ambientBlockData.fintypeBlock
  exact irreducibleBrauerCharacterBlock P.iota P.injective
    P.blockSource.operations.ambientBlockData.blocks psi

abbrev BlockStabilizer (b : P.Block) :=
  MulAction.stabilizer (MulAut (X n F))ᵐᵒᵖ b

local instance blockStabilizerFinite (b : P.Block) : Finite (P.BlockStabilizer b) :=
  Finite.of_injective
    (fun a : P.BlockStabilizer b => (a : (MulAut (X n F))ᵐᵒᵖ))
    Subtype.val_injective

/-- The actual block stabilizer acts through its underlying automorphisms,
with the inversion required by the repository's right-action convention. -/
def blockGamma (b : P.Block) : P.BlockStabilizer b →* MulAut (X n F) where
  toFun a := a.1.unop⁻¹
  map_one' := by simp
  map_mul' a c := by
    change (c.1.unop * a.1.unop)⁻¹ = a.1.unop⁻¹ * c.1.unop⁻¹
    exact mul_inv_rev _ _

theorem blockGamma_fixed (b : P.Block) (a : P.BlockStabilizer b) :
    inverseOpHom (P.blockGamma b) a • b = b := by
  change MulOpposite.op ((a.1.unop⁻¹)⁻¹) • b = b
  have h : (a.1 : (MulAut (X n F))ᵐᵒᵖ) • b = b := a.2
  simpa only [inv_inv, MulOpposite.op_unop] using h

/-- Existing block-problem bookkeeping, with a literal group and the actual
block stabilizer. No Definition 3.5 relation is introduced. -/
def blockProblem (b : P.Block) : Definition35Problem :=
  Definition35Problem.ofOperations P.iota P.injective P.blockSource b
    (P.blockGamma b) (P.blockGamma_fixed b) P.support_transport (P.localReduction b)

def ownBrauer (psi : IBr P.iota) :
    Definition35Brauer (P.blockProblem (P.brauerBlock psi)) := ⟨psi, rfl⟩

abbrev quotientSource (psi : IBr P.iota) :=
  centerlessCentralQuotientBrauerSource
    (P.blockProblem (P.brauerBlock psi)) P.center_eq_bot (P.ownBrauer psi)

/-- The existing concrete ambient record at the canonical central character
quotient. That quotient is canonically X because X is centreless. -/
abbrev Ambient (psi : IBr P.iota) :=
  SpathAmbientGroup (P.blockProblem (P.brauerBlock psi))
    (P.ownBrauer psi) (P.ownBrauer psi) (P.quotientSource psi)

def baseEmbedding {psi : IBr P.iota} (A : P.Ambient psi) : X n F →* A.A :=
  (quotientToAmbient (P.blockProblem (P.brauerBlock psi))
    (P.ownBrauer psi) (P.ownBrauer psi) (P.quotientSource psi) A).comp
      (centralCharacterQuotientMap (P.blockProblem (P.brauerBlock psi))
        (P.ownBrauer psi))

def ambientRadical {psi : IBr P.iota} (A : P.Ambient psi)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) : Subgroup A.A :=
  Q.1.map (P.baseEmbedding A)

abbrev LocalGroup {psi : IBr P.iota} (A : P.Ambient psi)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) :=
  Subgroup.normalizer (P.ambientRadical A Q : Set A.A)

def localBase {psi : IBr P.iota} (A : P.Ambient psi)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) : Subgroup (P.LocalGroup A Q) :=
  A.base.comap (P.LocalGroup A Q).subtype

abbrev Normalizer (_P : Problem n F)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) :=
  Subgroup.normalizer (Q.1 : Set (X n F))

/-- The actual irreducible ordinary lift in Definition 4.1(ii)(1),(3). -/
def inflatedOrdinary (Q : RadicalSubgroup (p := 2) (G := X n F))
    (theta : LocalDefectZeroCharacter (K := P.K) Q) : Irr P.K (P.Normalizer Q) :=
  inflateOrdinaryCharacter (Q.1.subgroupOf (P.Normalizer Q)) theta.1

/-- An actual local Brauer reduction of the prescribed ordinary inflation.
Existence is explicit, rather than hidden in an arbitrary relation. -/
structure LocalReduction (Q : RadicalSubgroup (p := 2) (G := X n F))
    (theta : LocalDefectZeroCharacter (K := P.K) Q) where
  root : PrimeRegularRootEmbedding 2 P.k P.K (P.Normalizer Q)
  rootCompatible : RootCompatibleAlong P.iota root (P.Normalizer Q).subtype
  brauer : IBr root
  reduction : IsBrauerReduction root (P.inflatedOrdinary Q theta) brauer
  /-- The narrow standard block-support law for this prescribed ordinary
  inflation and this compatible modular root convention. Navarro (3.3),
  (3.11), (3.13)(b), and (3.18) justify the source interpretation. This field
  neither selects an ambient block nor assumes its block induction. -/
  block_support :
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := localData.fintypeBlock
    irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
        localData.blocks brauer =
      O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2)

/-- Exact extension data for the actual Q, using the existing ambient and
Brauer-character extension witness types. -/
structure Extensions (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : IBr P.iota) (theta : LocalDefectZeroCharacter (K := P.K) Q)
    (A : P.Ambient psi) (L : P.LocalReduction Q theta) where
  ambientRoot : PrimeRegularRootEmbedding 2 P.k P.K A.A
  ambientRootCompatible : RootCompatibleAlong ambientRoot P.iota (P.baseEmbedding A)
  globalExtension : Representation.Extension.BrauerCharacterExtensionWitness
    ambientRoot ((P.quotientSource psi).iota.alongMulEquiv A.baseEquiv)
    (IrreducibleBrauerCharacter.alongMulEquiv
      (P.quotientSource psi).iota A.baseEquiv (P.quotientSource psi).brauer)
  localBaseEquiv : P.Normalizer Q ≃* P.localBase A Q
  localBaseEquiv_natural : ∀ x : P.Normalizer Q,
    (localBaseEquiv x).1.1 = P.baseEmbedding A x.1
  localAmbientRoot : PrimeRegularRootEmbedding 2 P.k P.K (P.LocalGroup A Q)
  ambientLocalRootCompatible : RootCompatibleAlong ambientRoot localAmbientRoot
    (P.LocalGroup A Q).subtype
  localRootCompatible : RootCompatibleAlong localAmbientRoot L.root
    ((P.localBase A Q).subtype.comp localBaseEquiv.toMonoidHom)
  localExtension : Representation.Extension.BrauerCharacterExtensionWitness
    localAmbientRoot (L.root.alongMulEquiv localBaseEquiv)
    (IrreducibleBrauerCharacter.alongMulEquiv L.root localBaseEquiv L.brauer)

/-- H is represented as its literal subgroup inside Xbar H. This is the
source subgroup itself, not the possibly larger N_(Xbar H)(Qbar). -/
abbrev IntermediateLocal {psi : IBr P.iota} (A : P.Ambient psi)
    (H : Subgroup A.A) := H.subgroupOf (A.base ⊔ H)

def intermediateLocalMap {psi : IBr P.iota} (A : P.Ambient psi)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) (H : Subgroup A.A)
    (hHN : H ≤ P.LocalGroup A Q) :
    P.IntermediateLocal A H →* P.LocalGroup A Q where
  toFun x := ⟨x.1.1, hHN x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Spath 4.1(iii)(4) on the actual source H: both restrictions and the
literal induced block relation on H ≤ Xbar H. Complete block catalogues
retain the same standard source provenance as IntermediateBlockEqualityAt.
-/
structure IntermediateBlockAt
    (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : IBr P.iota) (theta : LocalDefectZeroCharacter (K := P.K) Q)
    (A : P.Ambient psi) (L : P.LocalReduction Q theta)
    (E : P.Extensions Q psi theta A L) (H : Subgroup A.A)
    (hHN : H ≤ P.LocalGroup A Q) where
  globalRoot : PrimeRegularRootEmbedding 2 P.k P.K ↥(A.base ⊔ H)
  globalRootCompatible : RootCompatibleAlong E.ambientRoot globalRoot
    (A.base ⊔ H).subtype
  globalBrauer : IBr globalRoot
  globalRestriction : PrimeRegularClassFunction.pullback (A.base ⊔ H).subtype
    E.globalExtension.1.1 = globalBrauer.1
  localRoot : PrimeRegularRootEmbedding 2 P.k P.K (P.IntermediateLocal A H)
  localRootCompatible : RootCompatibleAlong E.localAmbientRoot localRoot
    (P.intermediateLocalMap A Q H hHN)
  intermediateRootCompatible : RootCompatibleAlong globalRoot localRoot
    (P.IntermediateLocal A H).subtype
  localBrauer : IBr localRoot
  localRestriction : PrimeRegularClassFunction.pullback
    (P.intermediateLocalMap A Q H hHN) E.localExtension.1.1 = localBrauer.1
  GlobalBlock : Type u
  LocalBlock : Type u
  [fintypeGlobalBlock : Fintype GlobalBlock]
  [fintypeLocalBlock : Fintype LocalBlock]
  globalBlockIdempotent : GlobalBlock → P.k[↥(A.base ⊔ H)]
  localBlockIdempotent : LocalBlock → P.k[P.IntermediateLocal A H]
  globalBlocks : BlockIdempotentDecomposition globalBlockIdempotent
  localBlocks : BlockIdempotentDecomposition localBlockIdempotent
  globalBrauerInjective : IrreducibleBrauerCharacterInjectivity globalRoot
  localBrauerInjective : IrreducibleBrauerCharacterInjectivity localRoot
  globalCentralCharacters : BlockCentralCharacterCatalogue globalBlocks
  localCentralCharacters : BlockCentralCharacterCatalogue localBlocks
  globalCentralCharactersNavarro311 : Navarro311CatalogueProvenance 2 Nat.prime_two
    globalBlocks globalCentralCharacters
  localCentralCharactersNavarro311 : Navarro311CatalogueProvenance 2 Nat.prime_two
    localBlocks localCentralCharacters
  inductionEquality : BlockInducesTo (P.IntermediateLocal A H)
    localCentralCharacters globalCentralCharacters
    (irreducibleBrauerCharacterBlock localRoot localBrauerInjective localBlocks localBrauer)
    (irreducibleBrauerCharacterBlock globalRoot globalBrauerInjective globalBlocks globalBrauer)

/-- All of (iii), for the same actual psi,Q,theta. -/
structure MatchedPair (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : IBr P.iota) (theta : LocalDefectZeroCharacter (K := P.K) Q) where
  ambient : P.Ambient psi
  localReduction : P.LocalReduction Q theta
  extensions : P.Extensions Q psi theta ambient localReduction
  intermediate : ∀ (H : Subgroup ambient.A)
      (hHN : H ≤ P.LocalGroup ambient Q),
    ambient.base ⊓ P.LocalGroup ambient Q ≤ H →
      P.IntermediateBlockAt Q psi theta ambient localReduction extensions H hHN

/-- Literal central restriction for the Brauer side of (ii)(1). -/
def BrauerLiesOver (nu : Irr P.K (Subgroup.center (X n F)))
    (psi : IBr P.iota) : Prop :=
  ∀ z : Subgroup.center (X n F),
    psi.1 (EvenFieldFLZ318SelfCoverEqualGroupClauseIII.centrePrimeRegularElement
      (p := 2) P.center_eq_bot z) = psi.1 ⟨1, isPrimeRegular_one⟩ * nu z

/-- Literal restriction of the actual ordinary inflation to the centre.
The quotient evaluation is inflation followed by restriction. -/
def LocalLiesOver (Q : RadicalSubgroup (p := 2) (G := X n F))
    (theta : LocalDefectZeroCharacter (K := P.K) Q)
    (nu : Irr P.K (Subgroup.center (X n F))) : Prop :=
  ∀ z : Subgroup.center (X n F),
    theta.1 (EvenFieldFLZ318SelfCoverEqualGroupClauseIII.centreToNormalizerQuotient
      P.center_eq_bot Q.1 z) = theta.1 1 * nu z

end Problem

/-- The intrinsic global map supplies (i), the local bijections in (ii),
their covariance, and (ii)(3) through the imported representative-map joins.
This is data selected by the target, not an independently fixed FM input map.
-/
structure GlobalMap (P : Problem n F) where
  equiv : IBr P.iota ≃ ConjugacyClass (p := 2) (K := P.K) (G := X n F)
  equivariant : ∀ (a : (MulAut (X n F))ᵐᵒᵖ) (psi : IBr P.iota),
    equiv (a • psi) = a • equiv psi
  block_preserving : ∀ psi,
    P.blockSource.weightBlock (equiv psi) = P.brauerBlock psi

namespace GlobalMap

variable {P : Problem n F} (M : GlobalMap P)

abbrev Part (Q : RadicalSubgroup (p := 2) (G := X n F)) :=
  IntrinsicGlobalToRepresentativeMaps.BrauerAtRadical P.iota M.equiv Q

def localMap (Q : RadicalSubgroup (p := 2) (G := X n F)) :
    M.Part Q ≃ LocalDefectZeroCharacter (K := P.K) Q :=
  IntrinsicGlobalToRepresentativeMaps.localMap P.iota M.equiv Nat.prime_two Q

/-- Clause (i)(2): every character belongs to a radical-class part. -/
theorem part_exists (psi : IBr P.iota) :
    ∃ Q : RadicalSubgroup (p := 2) (G := X n F),
      radicalClass (M.equiv psi) =
        (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X n F)) :=
  IntrinsicGlobalToRepresentativeMaps.exists_radical P.iota M.equiv psi

/-- Parts intersect only for conjugate radicals, giving the disjointness in
the partition indexed by conjugacy classes. -/
theorem part_intersection
    (Q R : RadicalSubgroup (p := 2) (G := X n F)) (psi : IBr P.iota)
    (hQ : radicalClass (M.equiv psi) =
      (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X n F)))
    (hR : radicalClass (M.equiv psi) =
      (Quotient.mk'' R : RadicalConjugacyClass (p := 2) (G := X n F))) :
    (Quotient.mk'' Q : RadicalConjugacyClass (p := 2) (G := X n F)) =
      Quotient.mk'' R :=
  IntrinsicGlobalToRepresentativeMaps.radical_classes_eq_of_common_member
    P.iota M.equiv Q R psi hQ hR

/-- Clause (i)(1), with the actual automorphism transport of Q. Applying
this map also to the inverse automorphism gives equality of the parts. -/
def partTransport (a : (MulAut (X n F))ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) (psi : M.Part Q) :
    M.Part (Q.rightTwist a.unop) :=
  IntrinsicGlobalToRepresentativeMaps.brauerTransport
    P.iota M.equiv M.equivariant a Q psi

/-- Clause (ii)(2) for the derived map and the literal quotient-character
transport. No equivariant choice of raw weight representatives is assumed. -/
theorem localMap_covariance (a : (MulAut (X n F))ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := 2) (G := X n F)) (psi : M.Part Q) :
    M.localMap (Q.rightTwist a.unop) (M.partTransport a Q psi) =
      IntrinsicGlobalToRepresentativeMaps.localCharacterTwist Nat.prime_two Q a
        (M.localMap Q psi) :=
  IntrinsicGlobalToRepresentativeMaps.localMap_covariance
    P.iota M.equiv M.equivariant Nat.prime_two a Q psi

/-- Preparatory clause-(ii)(3) deduction with the fixed local operations.
The actual reduction-block interpretation is supplied and consumed below
by Definition41.localMap_actualBlockInducesTo. -/
theorem localMap_blockInducesTo
    (Q : RadicalSubgroup (p := 2) (G := X n F)) (psi : M.Part Q) :
    let theta := M.localMap Q psi
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (Q.1 : Set (X n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2))
      (P.brauerBlock psi.1) :=
  IntrinsicGlobalToRepresentativeMaps.localMap_blockInducesTo
    P.iota M.equiv P.blockSource P.brauerBlock M.block_preserving Nat.prime_two Q psi

end GlobalMap

set_option maxHeartbeats 1000000 in
/-- The fixed literal original inductive BAW target, with every clause of
Spath Definition 4.1. Clauses (i) and the bijection/covariance/block parts of
(ii) are supplied by GlobalMap and its imported proved representative joins.
The remaining fields state (ii)(1), (iii), and both parts of (iv) literally.
-/
structure Definition41 (P : Problem n F) where
  map : GlobalMap P
  centralCharacter : ∀ (Q : RadicalSubgroup (p := 2) (G := X n F))
      (psi : map.Part Q) (nu : Irr P.K (Subgroup.center (X n F))),
    P.BrauerLiesOver nu psi.1 → P.LocalLiesOver Q (map.localMap Q psi) nu
  matched : ∀ (Q : RadicalSubgroup (p := 2) (G := X n F)) (psi : map.Part Q),
    P.MatchedPair Q psi.1 (map.localMap Q psi)
  /-- Actual reduction existence and Omega_1(chi^0)=chi. Comparing the
  inflated character with chi uses the canonical normalizer inclusion;
  oneRadical_eq_bot makes that normalizer all of X. -/
  oneReduction : ∀ (chi : Irr P.K (X n F)),
    IsDefectZeroOrdinaryCharacter 2 chi →
      ∃ psi : map.Part P.oneRadical,
        IsBrauerReduction P.iota chi psi.1 ∧
          ∀ x : P.Normalizer P.oneRadical,
            P.inflatedOrdinary P.oneRadical (map.localMap P.oneRadical psi) x = chi x.1
  /-- The same chosen extensions coincide at Q=1. This is equality of
  actual prime regular class functions through the local-group inclusion,
  not merely the independent existence of two extensions. -/
  oneExtensions : ∀ (psi : map.Part P.oneRadical),
    let W := matched P.oneRadical psi
    ∀ x : PrimeRegularElement (G := P.LocalGroup W.ambient P.oneRadical) 2,
      W.extensions.localExtension.1.1 x =
        W.extensions.globalExtension.1.1
          (PrimeRegularElement.map (P.LocalGroup W.ambient P.oneRadical).subtype x)

namespace Definition41

variable {P : Problem n F} (D : Definition41 P)

/-- Clause (ii)(3) with the block of the actual compatible Brauer reduction
of the prescribed ordinary inflation. The source law supplies only the
local block identity; induction to the Brauer character's ambient block is
the already-proved representative-map deduction. -/
theorem localMap_actualBlockInducesTo
    (Q : RadicalSubgroup (p := 2) (G := X n F)) (psi : D.map.Part Q) :
    let L := (D.matched Q psi).localReduction
    let O := P.blockSource.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (Q.1 : Set (X n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (irreducibleBrauerCharacterBlock L.root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding L.root)
        localData.blocks L.brauer)
      (P.brauerBlock psi.1) := by
  let L := (D.matched Q psi).localReduction
  let O := P.blockSource.operations
  let localData := O.inflatedNormalizerBlockData Q.1
  letI := O.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  change BlockInducesTo (Subgroup.normalizer (Q.1 : Set (X n F)))
    localData.catalogue O.ambientBlockData.catalogue
    (irreducibleBrauerCharacterBlock L.root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding L.root)
      localData.blocks L.brauer) (P.brauerBlock psi.1)
  rw [L.block_support]
  exact D.map.localMap_blockInducesTo Q psi

end Definition41

/-- A fixed target proposition for a future named forward published theorem.
No theorem in this file constructs an inhabitant. -/
def OriginalIBAW (P : Problem n F) : Prop := Nonempty (Definition41 P)

end ModularRep.PaperProofs.OddTwoLiteralSpathTarget


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
