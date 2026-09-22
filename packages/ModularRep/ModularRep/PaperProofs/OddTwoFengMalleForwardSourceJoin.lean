import ModularRep.PaperProofs.OddTwoLiteralSpathTarget
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

/-!
# The forward Feng--Malle Proposition 3.4 source join

The conclusion is the independently defined original Spath Definition 4.1
target on the literal PSp group and its actual identity prime-to-two cover.
It is not a caller-selected proposition. Its coefficient fields and their
instances are literally those of the Sp input problem.

The licensed E2 input is Feng--Malle (2022), Proposition 3.4, pp. 5--6,
applied only forwards. Its condition (1) is the actual equivariant,
block-preserving Sp map; conditions (2)--(3) refer to that same map and the
displayed matrix diagonal and field automorphisms. Remark 3.5 transports
condition (2) to (3), and Corollary 4.6, p. 10, supplies condition (2).
The source theorem supplies existence: the final Definition 4.1 map is not
asserted to equal the input map, or any fixed quotient of it.

The source scope is n >= 2 and odd finite field order, including (n,q) =
(2,3). Rank one is outside this interface. The actual full Sp-to-PSp cover
and its order-two kernel identify the prime-to-two cover with PSp. The
proof of Proposition 3.4 includes this central passage; no separate assumed
central-descent relation or reconstruction of projective representations is
inserted here.

E1 coefficient and local-block semantics remain explicit on BOTH groups.
Their local roots are compatible with their own ambient root convention,
and the PSp convention pulls back to the Sp convention along the literal
projection. Navarro (1998), Theorems 3.3, 3.11, 3.18 and Lemma 3.13(b),
with one common root convention, license the shared local-support law and
actual defect-zero reductions. Auxiliary selected quotient reductions are
source choices used by the existing ambient-record bookkeeping; they are
not substituted for the prescribed normalizer reductions below.

K packages these exact carriers, constructs the target's actual local
reduction from the shared source law, and applies the explicit E2 theorem
to the existing hypothesis endpoint, including its map obtained from orbit representatives.
No E2 instance or principal/Jordan component family is constructed here.
This conditional join does not assert the full Type C proposition or the
manuscript.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin

open Formalisation
open Formalisation.IBAW
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow

universe u

/-! ## Actual local reduction data, without any ambient block conclusion -/

/-- A compatible local convention and the actual irreducible reduction of
the prescribed ordinary character inflated to its normalizer. Existence
for each raw weight is standard source data, independent of any global map.
-/
structure CompatibleReduction
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G]
    (iota : PrimeRegularRootEmbedding p k K G)
    (W : CharacterWeight p K G) where
  root : PrimeRegularRootEmbedding p k K
    (Subgroup.normalizer (W.subgroup : Set G))
  rootCompatible : OddTwoActualLocalBlockSupport.RootCompatibleAlong
    iota root (Subgroup.normalizer (W.subgroup : Set G)).subtype
  brauer : IBr root
  reduction : NormalizerInflatedReduction W.subgroup W.localCharacter root brauer

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

/-- Interpretation of the exact Sp local-block operations used by condition
(1). The existence field prevents the support law from being merely a
conditional statement with no available compatible local reductions. -/
structure InputSemantics (P : LiteralFengMalleProblem n F) : Prop where
  support : OddTwoActualLocalBlockSupport.Source P.iota P.blockSource.operations
  reductions : ∀ W : CharacterWeight 2 P.K (LiteralSp n F),
    Nonempty (CompatibleReduction P.iota W)

/-! ## Bind the independently fixed target to the same coefficients -/

/-- Actual PSp source data, using the same n, F, k and K as the Sp problem.
No correspondence, ambient extension, intermediate block induction, or
Definition 4.1 witness is a field of this record. -/
structure TargetData (P : LiteralFengMalleProblem n F) where
  coverSource : OddTwoUniversalPrimeToTwoSelfCover.OddSymplecticFullCoverSource n F
  iota : PrimeRegularRootEmbedding 2 P.k P.K (LiteralPSp n F)
  /-- Pull back a PSp representation to Sp along the actual central
  projection. The direction of this compatibility is target to input. -/
  projectionRootCompatible : OddTwoActualLocalBlockSupport.RootCompatibleAlong
    iota P.iota (literalProjection n F)
  injective : IrreducibleBrauerCharacterInjectivity iota
  blockSource : LocalBlockInductionSource
    (p := 2) (k := P.k) (K := P.K) (G := LiteralPSp n F)
    (Block := LiteralPrimitiveBlock P.k (LiteralPSp n F))
  catalogue_idempotent : ∀ b : LiteralPrimitiveBlock P.k (LiteralPSp n F),
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  support_transport : OperationsBrauerSupport iota injective blockSource.operations
  /-- Auxiliary selected quotient reductions required by the existing
  Definition35Problem ambient bookkeeping. These are ordinary source
  choices, not the target's normalizer reductions or a matched-pair seed. -/
  selectedQuotientReduction : ∀ (b : LiteralPrimitiveBlock P.k (LiteralPSp n F))
      (w : LiteralWeightFibre blockSource b),
    SelectedLocalReductionSource blockSource b w
  oneRadical : RadicalSubgroup (p := 2) (G := LiteralPSp n F)
  oneRadical_eq_bot : oneRadical.1 = ⊥
  support : OddTwoActualLocalBlockSupport.Source iota blockSource.operations
  reductions : ∀ W : CharacterWeight 2 P.K (LiteralPSp n F),
    Nonempty (CompatibleReduction iota W)

namespace TargetData

variable {P : LiteralFengMalleProblem n F} (T : TargetData P)

/-- The independently defined target problem, with literal shared field
instances. In particular, no field equivalence or unnamed coefficient
identification is needed to state the forward theorem. -/
def toProblem : OddTwoLiteralSpathTarget.Problem n F where
  coverSource := T.coverSource
  k := P.k
  K := P.K
  fieldk := P.fieldk
  fieldK := P.fieldK
  charPk := P.charPk
  algClosedk := P.algClosedk
  charZeroK := P.charZeroK
  ordinarySplitting := P.algClosedK
  iota := T.iota
  injective := T.injective
  blockSource := T.blockSource
  catalogue_idempotent := T.catalogue_idempotent
  support_transport := T.support_transport
  localReduction := T.selectedQuotientReduction
  oneRadical := T.oneRadical
  oneRadical_eq_bot := T.oneRadical_eq_bot

@[simp] theorem toProblem_k : T.toProblem.k = P.k := rfl

@[simp] theorem toProblem_K : T.toProblem.K = P.K := rfl

@[simp] theorem toProblem_iota : T.toProblem.iota = T.iota := rfl

/-- The covering homomorphism is the actual identity on PSp, obtained from
the full Sp cover with two-group kernel by the existing cover theorem. -/
theorem toProblem_cover_quotient :
    T.toProblem.cover.quotient = MonoidHom.id (LiteralPSp n F) := rfl

/-- The source's compatible reduction at this exact Q and theta yields the
target's prescribed normalizer reduction and its actual primitive block.
The block equality is supplied by the shared local source law; no ambient
block membership or induction is assumed in this construction. -/
def actualLocalReduction
    (Q : RadicalSubgroup (p := 2) (G := LiteralPSp n F))
    (theta : LocalDefectZeroCharacter (K := P.K) Q) :
    T.toProblem.LocalReduction Q theta := by
  let W : CharacterWeight 2 P.K (LiteralPSp n F) :=
    characterWeightAt Nat.prime_two Q theta
  let R : CompatibleReduction T.iota W := Classical.choice (T.reductions W)
  exact
    { root := R.root
      rootCompatible := R.rootCompatible
      brauer := R.brauer
      reduction := R.reduction
      block_support := T.support.normalizer_block_of_reduction
        W R.root R.brauer R.rootCompatible R.reduction }

end TargetData

/-! ## Exact forward E2 theorem and its kernel consumers -/

/-- The one licensed substantial external theorem in this join:
Feng--Malle Proposition 3.4, interpreted on the exact displayed carriers.
The conclusion is existence of the independent original Definition 4.1
target. This record neither permits an arbitrary conclusion nor extracts
anything backwards from that conclusion. No instance is asserted here. -/
structure FengMalleProposition34Source
    (P : LiteralFengMalleProblem n F)
    (O : LiteralDiagonalFieldRealisation n F)
    (T : TargetData P) : Prop where
  applyProposition34 : InputSemantics P →
    ∀ omega : LiteralGlobalMap P,
      LiteralFengMalleHypotheses P O omega →
      OddTwoLiteralSpathTarget.OriginalIBAW T.toProblem

/-- K: Corollary 4.6 and the proved Remark 3.5 transport supply the exact
hypotheses consumed by the forward published theorem. -/
theorem originalIBAW_of_literalGlobalMap
    (P : LiteralFengMalleProblem n F)
    (O : LiteralDiagonalFieldRealisation n F)
    (T : TargetData P)
    (source : FengMalleProposition34Source P O T)
    (input : InputSemantics P)
    (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    OddTwoLiteralSpathTarget.OriginalIBAW T.toProblem :=
  source.applyProposition34 input omega
    (literalFengMalleHypotheses P O omega corollary46)

section OrbitConsumer

variable (P : LiteralFengMalleProblem n F)
variable {R S DZ : Type u}
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ R]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ S]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ DZ]
variable
  (literalContext : Context (MulAut (LiteralSp n F))ᵐᵒᵖ
    (LiteralPrimitiveBlock P.k (LiteralSp n F)) R S
    (IBr P.iota) (LiteralWeight n F P.K) DZ)

/-- K: the actual existing construction from orbit representatives feeds the forward theorem. There
is no second global map input. The extra abstract component predicates are
not identified with original iBAW by this theorem; only the combined
literal map and its actual block/equivariance equations are consumed. -/
theorem originalIBAW_of_representativeComponents
    (D : RepresentativeBlockComponents literalContext)
    (brauerBlock_eq : literalContext.brauerBlock = P.brauerBlock)
    (weightBlock_eq : literalContext.weightBlock = P.blockSource.weightBlock)
    (O : LiteralDiagonalFieldRealisation n F)
    (T : TargetData P)
    (source : FengMalleProposition34Source P O T)
    (input : InputSemantics P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    OddTwoLiteralSpathTarget.OriginalIBAW T.toProblem :=
  source.applyProposition34 input
    (literalGlobalMapOfRepresentativeComponents P literalContext D
      brauerBlock_eq weightBlock_eq)
    (literalFengMalleHypothesesOfRepresentativeComponents P literalContext D
      brauerBlock_eq weightBlock_eq O corollary46)

end OrbitConsumer

end ModularRep.PaperProofs.OddTwoFengMalleForwardSourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
