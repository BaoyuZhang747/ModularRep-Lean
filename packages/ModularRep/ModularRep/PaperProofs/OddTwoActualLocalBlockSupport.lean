import ModularRep.BrauerCharacterHomPullback
import ModularRep.NavarroLocalReductionInflationBlockCompatibility
import ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin
import ModularRep.PaperProofs.OddTwoQuaternionClassPair

/-!
# Actual local blocks for the principal pair joins

The existing principal pair joins prove block induction for the composite
of the specified local-character block and normalizer-inflation operations.
This file isolates the additional source identification with the literal
primitive-idempotent block of an actual inflated Brauer reduction.

The source law is indexed by the exact ambient root convention and exact
operations. Local roots must agree with that convention on the eigenvalues
used by representation restriction along the actual normalizer inclusion.
It is not the older law quantified over arbitrary independent local roots,
and it does not identify zero-extended root lifts on the whole field.

Source scope: SF-BRAUER-ROOT-COHERENCE (Navarro, Lemma 2.1 and the Brauer
character definition, pp. 16--18) supplies the common convention. For
SF-NAVARRO-LOCAL-REDUCTION-BLOCK, Theorem 3.18, pp. 61--62, supplies the
defect-zero reduction; Theorem 3.3, pp. 50--51, supplies its decomposition
support; Theorem 3.11, pp. 55--56, and Lemma 3.13(b), p. 58, identify the
primitive block. Authentication of the operations' local-character block
and inflation labels is part of this E1 source law, not a consequence for
arbitrary operations. Quotient containment alone supplies no block
bijection. No source instance or compatible-root construction is declared.

K then rewrites the proved operations endpoint. Both principal consumers
use the candidate's own local character and its actual inflated reduction.
They add no candidate principal-membership or ambient-induction premise.
The reduction and compatible local root convention remain explicit inputs.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoActualLocalBlockSupport

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.NavarroLocalReductionInflationBlockCompatibility

universe u v

/-- The common root convention on exactly the eigenvalues used by actual
representation restrictions. The homomorphism is retained in the type. -/
def RootCompatibleAlong
    {p : ℕ} {k K G H : Type u} [Field k] [Field K] [CharP k p]
    [IsAlgClosed k] [CharZero K] [Group G] [Finite G] [Group H] [Finite H]
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaH : PrimeRegularRootEmbedding p k K H) (f : H →* G) : Prop :=
  ∀ W : FDRep k G,
    Representation.BrauerRootLiftCompatibleAlong W.ρ iotaG iotaH f

section LocalBlockSupport

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [MulAction (MulAut G)ᵐᵒᵖ Block]

/-- Shared E1 interpretation of these exact operations under this exact
ambient root convention. Its conclusion identifies only a local block;
the actual reduction, compatible roots, and ambient induction are separate.
In particular, this is not a theorem that arbitrary operations have the law. -/
structure Source
    (iota : PrimeRegularRootEmbedding p k K G)
    (operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block)) : Prop where
  normalizer_block_of_reduction :
    ∀ (W : CharacterWeight p K G)
      (iotaN : PrimeRegularRootEmbedding p k K
        (Subgroup.normalizer (W.subgroup : Set G)))
      (phiN : IBr iotaN),
      RootCompatibleAlong iota iotaN
        (Subgroup.normalizer (W.subgroup : Set G)).subtype →
      NormalizerInflatedReduction W.subgroup W.localCharacter iotaN phiN →
        normalizerBrauerBlock operations W.subgroup iotaN phiN =
          operations.inflateToNormalizer W.subgroup
            (operations.localCharacterBlock
              W.subgroup W.localCharacter W.defectZero)

/-- K: replace the operations' local block by the literal block of the
same raw pair's actual inflated reduction, retaining the ambient endpoint. -/
theorem blockInducesTo_actualNormalizerBlock
    {iota : PrimeRegularRootEmbedding p k K G}
    {operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block)}
    (source : Source iota operations) (W : CharacterWeight p K G)
    (iotaN : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (W.subgroup : Set G)))
    (phiN : IBr iotaN)
    (hroots : RootCompatibleAlong iota iotaN
      (Subgroup.normalizer (W.subgroup : Set G)).subtype)
    (hReduction : NormalizerInflatedReduction
      W.subgroup W.localCharacter iotaN phiN)
    (b : Block)
    (hInduces :
      let localData := operations.inflatedNormalizerBlockData W.subgroup
      letI := operations.ambientBlockData.fintypeBlock
      letI := localData.fintypeBlock
      BlockInducesTo (Subgroup.normalizer (W.subgroup : Set G))
        localData.catalogue operations.ambientBlockData.catalogue
        (operations.inflateToNormalizer W.subgroup
          (operations.localCharacterBlock
            W.subgroup W.localCharacter W.defectZero)) b) :
    let localData := operations.inflatedNormalizerBlockData W.subgroup
    letI := operations.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (W.subgroup : Set G))
      localData.catalogue operations.ambientBlockData.catalogue
      (normalizerBrauerBlock operations W.subgroup iotaN phiN) b := by
  let localData := operations.inflatedNormalizerBlockData W.subgroup
  letI := operations.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  change BlockInducesTo (Subgroup.normalizer (W.subgroup : Set G))
    localData.catalogue operations.ambientBlockData.catalogue
    (normalizerBrauerBlock operations W.subgroup iotaN phiN) b
  rw [source.normalizer_block_of_reduction W iotaN phiN hroots hReduction]
  exact hInduces

end LocalBlockSupport

section PrincipalConsumers

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoPrincipalLocalEnumerationJoin
open ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin
open ModularRep.PaperProofs.OddTwoQuaternionClassPair
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

variable {n : ℕ} {F k K Block : Type u} {Index : Type v}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (support : Source D.iota D.blockSource.operations)

include support in
/-- The selected member of an actual exhaustive local enumeration has
actual normalizer block inducing to the principal block. The index and
operations endpoint are supplied by the checked own-character join. -/
theorem enumeratedPair_actualBlockInducesTo
    (w : D.PrincipalWeight) (R : Subgroup (Sp n F)) (g : Sp n F)
    (hR : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj g⁻¹)).subgroup = R)
    (enumeration : Index ≃ LocalDefectZeroCharacters (K := K) R)
    (iotaN : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer
        ((selectedEnumeratedPair D w R g hR enumeration).subgroup : Set (Sp n F))))
    (phiN : IBr iotaN)
    (hroots : RootCompatibleAlong D.iota iotaN
      (Subgroup.normalizer
        ((selectedEnumeratedPair D w R g hR enumeration).subgroup : Set (Sp n F))).subtype)
    (hReduction : NormalizerInflatedReduction
      (selectedEnumeratedPair D w R g hR enumeration).subgroup
      (selectedEnumeratedPair D w R g hR enumeration).localCharacter iotaN phiN) :
    let V := selectedEnumeratedPair D w R g hR enumeration
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData V.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (normalizerBrauerBlock O V.subgroup iotaN phiN) D.principalBlock := by
  exact blockInducesTo_actualNormalizerBlock support
    (selectedEnumeratedPair D w R g hR enumeration) iotaN phiN hroots hReduction
    D.principalBlock (selectedEnumeratedPair_blockInducesTo D w R g hR enumeration)

include support in
/-- Either actual quaternion candidate uses its own local character,
including the diagonal companion whose uniqueness was proved by transport.
Only the genuine subgroup match and the shared local support law are used. -/
theorem quaternionCandidate_actualBlockInducesTo
    (C : QuaternionBasicModel n F)
    (S : AnQuaternionBasicLocalSource (K := K) C)
    (O : OddTwoFinalBlockOrbitCentralCoverDescentWindow.LiteralDiagonalFieldRealisation n F)
    (w : D.PrincipalWeight) (i : Fin 2) (g : Sp n F)
    (hQ : ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj g⁻¹)).subgroup = (candidate C S O i).subgroup)
    (iotaN : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer ((candidate C S O i).subgroup : Set (Sp n F))))
    (phiN : IBr iotaN)
    (hroots : RootCompatibleAlong D.iota iotaN
      (Subgroup.normalizer ((candidate C S O i).subgroup : Set (Sp n F))).subtype)
    (hReduction : NormalizerInflatedReduction
      (candidate C S O i).subgroup (candidate C S O i).localCharacter iotaN phiN) :
    let V := candidate C S O i
    let B := D.blockSource.operations
    let localData := B.inflatedNormalizerBlockData V.subgroup
    letI := B.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (V.subgroup : Set (Sp n F)))
      localData.catalogue B.ambientBlockData.catalogue
      (normalizerBrauerBlock B V.subgroup iotaN phiN) D.principalBlock := by
  exact blockInducesTo_actualNormalizerBlock support
    (candidate C S O i) iotaN phiN hroots hReduction D.principalBlock
    (candidate_blockInducesTo C S O D w i g hQ)

end PrincipalConsumers

end ModularRep.PaperProofs.OddTwoActualLocalBlockSupport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
