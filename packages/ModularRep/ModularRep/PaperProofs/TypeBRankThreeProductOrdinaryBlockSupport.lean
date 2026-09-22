import ModularRep.PaperProofs.TypeBRankThreeProductBlockSource
import ModularRep.PaperProofs.TypeBRankThreeProductRawWeight
import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding
import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks

/-!
# Ordinary product support on the actual normalizers

The routine E1 source concerns actual ordinary characters, their literal
value square, and the specified ordinary block selectors in one modular
system.  Every selector is already tied to the nonzero multiplicities of
the actual chosen stable-lattice reduction at that system's groupRoot.
The source has no local operations or weight variable.

The local consumer uses that statement for the actual inflated characters.
The SAME OrdinaryInflationMembership then identifies the own normalizer
blocks.  No ambient block assignment is an input or a conclusion here.

The source meaning is finite ordinary external products and their block
support: Isaacs (4.20)--(4.21), pp. 59--60, with finite splitting as in
(10.3), p. 161; Navarro (3.1), (3.3), and (3.11)--(3.12), pp. 48--58.
The source inhabitants and their actual catalogue interpretation remain
external.  This file does not derive those facts from CharZero alone.
-/

noncomputable section

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeProductOrdinaryBlockSupport

open OrdinaryIrreducibleCharacter CharacterWeight FDRepSimpleClassKZero
open TypeBModularGroupRootBinding TypeBOrdinaryBlockSplitting
open TypeBLocalPhysicalBlockBinding
open TypeBRankThreeProductBlockSource TypeBRankThreeProductRawWeight
open TypeBRankThreeProductRadical
open OddTwoGroupEquivWeightBlocks

variable {p : ℕ} {I K O k : Type} [Fintype I]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [CharP k p] [IsAlgClosed k]
variable (Msys : ModularSystem p K O k)

section Uniform

variable (N : Type) [Group N] [Finite N]
variable (A : I → Type) [∀ i, Group (A i)] [∀ i, Finite (A i)]
variable (e : N ≃* (∀ i, A i))
variable [HasEnoughRootsOfUnity K (Nat.card N)]
variable [∀ i, HasEnoughRootsOfUnity K (Nat.card (A i))]
variable [Fintype (LiteralPrimitiveBlock k N)]
variable [∀ i, Fintype (LiteralPrimitiveBlock k (A i))]
variable (blocksN : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k N => b.val))
variable (blocksA : ∀ i, BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (A i) => b.val))
variable (ordinaryN : OrdinaryBlockSource Msys (groupRoot Msys N)
  (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) blocksN)
variable (ordinaryA : ∀ i, OrdinaryBlockSource Msys (groupRoot Msys (A i))
  (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _) (blocksA i))

/-- Uniform E1 ordinary product-block support for one specified modular system.
The hypothesis is the exact character-value square, not a selected matching. -/
structure OrdinaryProductBlockSource : Prop where
  supporting_block : ∀ (theta : Irr K N) (chi : ∀ i, Irr K (A i)),
    (∀ n : N, theta n = ∏ i, chi i (e n i)) →
      MonoidAlgebra.domCongr k k e (ordinaryN.physical.ordinaryBlock theta).val =
        productIdempotent A (fun i => (ordinaryA i).physical.ordinaryBlock (chi i))

end Uniform

section Local

local instance indexDecidableEq : DecidableEq I := Classical.decEq I

variable (G : I → Type) [∀ i, Group (G i)] [∀ i, Fintype (G i)]
variable [HasEnoughRootsOfUnity K (Nat.card (∀ i, G i))]
variable [∀ i, HasEnoughRootsOfUnity K (Nat.card (G i))]
variable (hp : Nat.Prime p) (W : ∀ i, CharacterWeight p K (G i))
variable (ordinaryQuotients : TypeBRankThreeProductOrdinarySource.ExternalProductSource
  (fun i => NormalizerQuotient ((W i).subgroup)) p hp
  (quotientProductRoots (K := K) G (fun i => (W i).subgroup)))

/-- The actual inflated product character satisfies the literal normalizer
value square.  No block or product reduction premise is needed. -/
theorem inflatedOrdinary_product_value
    (n : Subgroup.normalizer
      (Subgroup.pi Set.univ (fun i => (W i).subgroup) : Set (∀ i, G i))) :
    inflatedOrdinary (Subgroup.pi Set.univ (fun i => (W i).subgroup))
        (rawProduct G hp W ordinaryQuotients).localCharacter n =
      ∏ i, inflatedOrdinary (W i).subgroup (W i).localCharacter
        (normalizerPiEquiv G (fun i => (W i).subgroup) n i) := by
  change (rawProduct G hp W ordinaryQuotients).localCharacter (QuotientGroup.mk n) =
    ∏ i, (W i).localCharacter
      (QuotientGroup.mk (normalizerPiEquiv G (fun i => (W i).subgroup) n i))
  exact rawProduct_localCharacter_mk G hp W ordinaryQuotients n

variable {BP : Type} {B : I → Type}
variable (operationsP : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := (∀ i, G i)) (Block := BP))
variable (operationsI : ∀ i, LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := G i) (Block := B i))
variable (ordinaryP : ∀ Q : Subgroup (∀ i, G i),
  NormalizerOrdinarySource Msys operationsP Q)
variable (ordinaryI : ∀ i, ∀ Q : Subgroup (G i),
  NormalizerOrdinarySource Msys (operationsI i) Q)
variable (membershipP : OrdinaryInflationMembership Msys operationsP ordinaryP)
variable (membershipI : ∀ i,
  OrdinaryInflationMembership Msys (operationsI i) (ordinaryI i))

include membershipP membershipI in
/-- Ordinary product support and the SAME inflation membership derive the
own-normalizer primitive equation for the literal raw product weight. -/
theorem ownNormalizerBlock_product
    (support :
      letI := normalizerOrdinaryRoots (K := K)
        (Subgroup.pi Set.univ (fun i => (W i).subgroup))
      letI : ∀ i, HasEnoughRootsOfUnity K
          (Nat.card (Subgroup.normalizer ((W i).subgroup : Set (G i)))) :=
        fun i => normalizerOrdinaryRoots (K := K) (W i).subgroup
      letI := (operationsP.inflatedNormalizerBlockData
        (Subgroup.pi Set.univ (fun i => (W i).subgroup))).fintypeBlock
      letI : ∀ i, Fintype (InflatedNormalizerBlock (k := k) (W i).subgroup) :=
        fun i => ((operationsI i).inflatedNormalizerBlockData (W i).subgroup).fintypeBlock
      OrdinaryProductBlockSource Msys
        (Subgroup.normalizer
          (Subgroup.pi Set.univ (fun i => (W i).subgroup) : Set (∀ i, G i)))
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (G i)))
        (normalizerPiEquiv G (fun i => (W i).subgroup))
        (operationsP.inflatedNormalizerBlockData
          (Subgroup.pi Set.univ (fun i => (W i).subgroup))).blocks
        (fun i => ((operationsI i).inflatedNormalizerBlockData (W i).subgroup).blocks)
        (ordinaryP (Subgroup.pi Set.univ (fun i => (W i).subgroup)))
        (fun i => ordinaryI i (W i).subgroup)) :
    MonoidAlgebra.domCongr k k (normalizerPiEquiv G (fun i => (W i).subgroup))
        (ownNormalizerBlock operationsP (rawProduct G hp W ordinaryQuotients)).val =
      productIdempotent
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (G i)))
        (fun i => ownNormalizerBlock (operationsI i) (W i)) := by
  letI := normalizerOrdinaryRoots (K := K)
    (Subgroup.pi Set.univ (fun i => (W i).subgroup))
  letI : ∀ i, HasEnoughRootsOfUnity K
      (Nat.card (Subgroup.normalizer ((W i).subgroup : Set (G i)))) :=
    fun i => normalizerOrdinaryRoots (K := K) (W i).subgroup
  letI := (operationsP.inflatedNormalizerBlockData
    (Subgroup.pi Set.univ (fun i => (W i).subgroup))).fintypeBlock
  letI : ∀ i, Fintype (InflatedNormalizerBlock (k := k) (W i).subgroup) :=
    fun i => ((operationsI i).inflatedNormalizerBlockData (W i).subgroup).fintypeBlock
  have hP := membershipP.membership
    (Subgroup.pi Set.univ (fun i => (W i).subgroup))
    (rawProduct G hp W ordinaryQuotients).radical
    (rawProduct G hp W ordinaryQuotients).localCharacter
    (rawProduct G hp W ordinaryQuotients).defectZero
  calc
    MonoidAlgebra.domCongr k k (normalizerPiEquiv G (fun i => (W i).subgroup))
        (ownNormalizerBlock operationsP (rawProduct G hp W ordinaryQuotients)).val =
      MonoidAlgebra.domCongr k k (normalizerPiEquiv G (fun i => (W i).subgroup))
        (ordinaryNormalizerBlock Msys operationsP
          (Subgroup.pi Set.univ (fun i => (W i).subgroup))
          (ordinaryP (Subgroup.pi Set.univ (fun i => (W i).subgroup)))
          (inflatedOrdinary (Subgroup.pi Set.univ (fun i => (W i).subgroup))
            (rawProduct G hp W ordinaryQuotients).localCharacter)).val :=
      congrArg (fun b : InflatedNormalizerBlock (k := k)
          (Subgroup.pi Set.univ (fun i => (W i).subgroup)) =>
        MonoidAlgebra.domCongr k k (normalizerPiEquiv G (fun i => (W i).subgroup)) b.val)
          hP.symm
    _ = productIdempotent
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (G i)))
        (fun i => ordinaryNormalizerBlock Msys (operationsI i) (W i).subgroup
          (ordinaryI i (W i).subgroup)
          (inflatedOrdinary (W i).subgroup (W i).localCharacter)) :=
      support.supporting_block
        (inflatedOrdinary (Subgroup.pi Set.univ (fun i => (W i).subgroup))
          (rawProduct G hp W ordinaryQuotients).localCharacter)
        (fun i => inflatedOrdinary (W i).subgroup (W i).localCharacter)
        (inflatedOrdinary_product_value G hp W ordinaryQuotients)
    _ = _ :=
      congrArg (productIdempotent
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (G i))))
        (funext (fun i => (membershipI i).membership (W i).subgroup
          (W i).radical (W i).localCharacter (W i).defectZero))

end Local

end ModularRep.PaperProofs.TypeBRankThreeProductOrdinaryBlockSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
