import ModularRep.CharacterWeightBlockAssignment
import ModularRep.IBrBlock
import ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation

/-!
# Literal block transport through the normal core

This file removes the abstract sets of blocks and four arbitrary block maps
from the block-preservation endpoint for manuscript Lemma 2.6.  A block is
literally a primitive central idempotent of the appropriate modular group
algebra.  The Brauer block maps are the maps constructed from complete
block-idempotent decompositions, and the weight block maps are the maps
constructed by local block induction.

The correspondence between the downstairs and upstairs primitive blocks,
and its compatibility with Brauer inflation and lifting of weights, remains
an exact sourced input.  No Brauer-to-weight correspondence, BAW statement,
iBAW statement, or normal-core conclusion is assumed.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.NormalCoreLemma48LiteralBlocks

open CharacterWeight
open FDRepSimpleClassKZero
open NormalCoreLemma48SourceInstantiation

universe u

/-- The literal carrier of blocks of the modular group algebra `k[H]`. -/
abbrev PrimitiveBlock (k H : Type u) [Field k] [Group H] :=
  {b : k[H] // IsPrimitiveCentralIdempotent b}

/-- The idempotent indexed by a literal primitive block. -/
def blockIdempotent {k H : Type u} [Field k] [Group H] :
    PrimitiveBlock k H -> k[H] :=
  Subtype.val

section LiteralBlockMaps

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable [Fintype (G ⧸ pCore p G)]

abbrev DownBlock := PrimitiveBlock k (G ⧸ pCore p G)
abbrev UpBlock := PrimitiveBlock k G

variable [Fintype (DownBlock (p := p) (k := k) (G := G))]
variable [Fintype (UpBlock (k := k) (G := G))]

variable (iotaDown :
  PrimeRegularRootEmbedding p k K (G ⧸ pCore p G))
variable (iotaUp : PrimeRegularRootEmbedding p k K G)
variable (hinjDown : IrreducibleBrauerCharacterInjectivity iotaDown)
variable (hinjUp : IrreducibleBrauerCharacterInjectivity iotaUp)

variable (downBlocks : BlockIdempotentDecomposition
  (blockIdempotent : DownBlock (p := p) (k := k) (G := G) ->
    k[G ⧸ pCore p G]))
variable (upBlocks : BlockIdempotentDecomposition
  (blockIdempotent : UpBlock (k := k) (G := G) -> k[G]))

/-- The literal block containing a downstairs irreducible Brauer
character. -/
def brauerBlockDown (phi : IBr iotaDown) :
    DownBlock (p := p) (k := k) (G := G) :=
  irreducibleBrauerCharacterBlock iotaDown hinjDown downBlocks phi

/-- The literal block containing an upstairs irreducible Brauer
character. -/
def brauerBlockUp (phi : IBr iotaUp) :
    UpBlock (k := k) (G := G) :=
  irreducibleBrauerCharacterBlock iotaUp hinjUp upBlocks phi

variable [MulAction (MulAut (G ⧸ pCore p G))ᵐᵒᵖ
  (DownBlock (p := p) (k := k) (G := G))]
variable [MulAction (MulAut G)ᵐᵒᵖ (UpBlock (k := k) (G := G))]

variable (downLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G ⧸ pCore p G)
  (Block := DownBlock (p := p) (k := k) (G := G)))
variable (upLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G)
  (Block := UpBlock (k := k) (G := G)))

/-- The downstairs weight block map is definitionally the map obtained by
local block induction. -/
def weightBlockDown
    (omega : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    DownBlock (p := p) (k := k) (G := G) :=
  downLocal.weightBlock omega

/-- The upstairs weight block map is definitionally the map obtained by
local block induction. -/
def weightBlockUp
    (omega : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G)) :
    UpBlock (k := k) (G := G) :=
  upLocal.weightBlock omega

/-- The downstairs weight-block square for an induced quotient
automorphism.  This is a kernel consequence of the literal local block
induction construction. -/
theorem weightBlockDown_twist (alpha : MulAut G)
    (omega : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    weightBlockDown downLocal
        (MulOpposite.op
          (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)) •
            omega) =
      MulOpposite.op
          (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)) •
        weightBlockDown downLocal omega :=
  downLocal.weightBlock_transport _ omega

/-- The upstairs weight-block square for an automorphism of `G`. -/
theorem weightBlockUp_twist (alpha : MulAut G)
    (omega : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G)) :
    weightBlockUp upLocal (MulOpposite.op alpha • omega) =
      MulOpposite.op alpha • weightBlockUp upLocal omega :=
  upLocal.weightBlock_transport _ omega

end LiteralBlockMaps

section SourcedBlockCorrespondence

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable [Fintype (G ⧸ pCore p G)]

variable [Fintype (DownBlock (p := p) (k := k) (G := G))]
variable [Fintype (UpBlock (k := k) (G := G))]
variable [MulAction (MulAut (G ⧸ pCore p G))ᵐᵒᵖ
  (DownBlock (p := p) (k := k) (G := G))]
variable [MulAction (MulAut G)ᵐᵒᵖ (UpBlock (k := k) (G := G))]

variable (iotaDown :
  PrimeRegularRootEmbedding p k K (G ⧸ pCore p G))
variable (iotaUp : PrimeRegularRootEmbedding p k K G)
variable (hinjDown : IrreducibleBrauerCharacterInjectivity iotaDown)
variable (hinjUp : IrreducibleBrauerCharacterInjectivity iotaUp)

variable (downBlocks : BlockIdempotentDecomposition
  (blockIdempotent : DownBlock (p := p) (k := k) (G := G) ->
    k[G ⧸ pCore p G]))
variable (upBlocks : BlockIdempotentDecomposition
  (blockIdempotent : UpBlock (k := k) (G := G) -> k[G]))

variable (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
variable (W : WeightTransportInput (p := p) (K := K) (G := G))
variable (charactersDown : LocalSplittingCharacterInput K
  (G ⧸ pCore p G))
variable (charactersUp : LocalSplittingCharacterInput K G)
variable (downLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G ⧸ pCore p G)
  (Block := DownBlock (p := p) (k := k) (G := G)))
variable (upLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G)
  (Block := UpBlock (k := k) (G := G)))

/-- Lift an actual character-weight conjugacy class through the normal
core.  The two conversions between representation weights and character
weights are the canonical equivalences constructed from the local splitting
character input. -/
def liftCharacterWeight
    (omega : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  CharacterWeight.conjugacyClassEquiv charactersUp
    (W.liftConjugacyClass
      ((CharacterWeight.conjugacyClassEquiv charactersDown).symm omega))

/-- The transported equivalence with its weight endpoint on actual
character-weight conjugacy classes. -/
def transportedCharacterEquiv
    (downstairs : IBr iotaDown ≃ CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    IBr iotaUp ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  (B.equiv (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp)).symm.trans
    (downstairs.trans
      ((CharacterWeight.conjugacyClassEquiv charactersDown).symm.trans
        (W.conjugacyClassEquiv.trans
          (CharacterWeight.conjugacyClassEquiv charactersUp))))

@[simp]
theorem transportedCharacterEquiv_inflate
    (downstairs : IBr iotaDown ≃ CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G))
    (phi : IBr iotaDown) :
    transportedCharacterEquiv iotaDown iotaUp B W charactersDown
        charactersUp downstairs
        (B.inflate (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp) phi) =
      liftCharacterWeight W charactersDown charactersUp
        (downstairs phi) := by
  change CharacterWeight.conjugacyClassEquiv charactersUp
      (W.liftConjugacyClass
        ((CharacterWeight.conjugacyClassEquiv charactersDown).symm
          (downstairs
            ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
              (iotaUp := iotaUp)).symm
              (B.inflate (P := pCore p G) (iotaDown := iotaDown)
                (iotaUp := iotaUp) phi))))) = _
  have hinflate := B.equiv_apply (P := pCore p G)
    (iotaDown := iotaDown) (iotaUp := iotaUp) phi
  have hsymm :
      (B.equiv (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)).symm
          (B.inflate (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp) phi) = phi := by
    rw [← hinflate]
    exact (B.equiv (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp)).symm_apply_apply phi
  rw [hsymm]
  rfl

/-- Equivariance of the transported equivalence on actual character-weight
conjugacy classes.  The conversion from representation weights is canonical
and its automorphism compatibility is proved in `WeightCharacterBridge`. -/
theorem transportedCharacterEquiv_equivariant
    (downstairs : IBr iotaDown ≃ CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G))
    (downstairsEquivariant : ∀ (alpha : MulAut G) (phi : IBr iotaDown),
      downstairs
          (IrreducibleBrauerCharacter.twist iotaDown phi
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha))) =
        MulOpposite.op
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha)) •
          downstairs phi)
    (alpha : MulAut G) (phi : IBr iotaUp) :
    transportedCharacterEquiv iotaDown iotaUp B W charactersDown
        charactersUp downstairs
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha) =
      MulOpposite.op alpha •
        transportedCharacterEquiv iotaDown iotaUp B W charactersDown
          charactersUp downstairs phi := by
  let downstairsRep : IBr iotaDown ≃
      RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G) :=
    downstairs.trans
      (CharacterWeight.conjugacyClassEquiv charactersDown).symm
  have hDownRep : ∀ (beta : MulAut G) (psi : IBr iotaDown),
      downstairsRep
          (IrreducibleBrauerCharacter.twist iotaDown psi
            (quotientMulAut (pCore p G) beta
              (pCore_map_equiv p beta))) =
        RepresentationWeight.rightTwistConjugacyClass
          (quotientMulAut (pCore p G) beta
            (pCore_map_equiv p beta))
          (downstairsRep psi) := by
    intro beta psi
    change (CharacterWeight.conjugacyClassEquiv charactersDown).symm
        (downstairs
          (IrreducibleBrauerCharacter.twist iotaDown psi
            (quotientMulAut (pCore p G) beta
              (pCore_map_equiv p beta)))) =
      RepresentationWeight.rightTwistConjugacyClass
        (quotientMulAut (pCore p G) beta (pCore_map_equiv p beta))
        ((CharacterWeight.conjugacyClassEquiv charactersDown).symm
          (downstairs psi))
    apply (CharacterWeight.conjugacyClassEquiv charactersDown).injective
    rw [Equiv.apply_symm_apply]
    let qalpha := quotientMulAut (pCore p G) beta
      (pCore_map_equiv p beta)
    calc
      downstairs
          (IrreducibleBrauerCharacter.twist iotaDown psi qalpha) =
          MulOpposite.op qalpha • downstairs psi :=
        downstairsEquivariant beta psi
      _ = MulOpposite.op qalpha •
          CharacterWeight.conjugacyClassEquiv charactersDown
            ((CharacterWeight.conjugacyClassEquiv charactersDown).symm
              (downstairs psi)) := by rw [Equiv.apply_symm_apply]
      _ = CharacterWeight.conjugacyClassEquiv charactersDown
          (MulOpposite.op qalpha •
            (CharacterWeight.conjugacyClassEquiv charactersDown).symm
              (downstairs psi)) :=
        (CharacterWeight.conjugacyClassEquiv_smul charactersDown
          (MulOpposite.op qalpha) _).symm
  have htransport :=
    NormalCoreLemma48SourceInstantiation.transportedEquiv_equivariant
      iotaDown iotaUp B W downstairsRep hDownRep alpha phi
  change CharacterWeight.conjugacyClassEquiv charactersUp
      (NormalCoreLemma48SourceInstantiation.transportedEquiv
        iotaDown iotaUp B W downstairsRep
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha)) = _
  calc
    CharacterWeight.conjugacyClassEquiv charactersUp
        (NormalCoreLemma48SourceInstantiation.transportedEquiv
          iotaDown iotaUp B W downstairsRep
          (IrreducibleBrauerCharacter.twist iotaUp phi alpha)) =
        CharacterWeight.conjugacyClassEquiv charactersUp
          (RepresentationWeight.rightTwistConjugacyClass alpha
            (NormalCoreLemma48SourceInstantiation.transportedEquiv
              iotaDown iotaUp B W downstairsRep phi)) :=
      congrArg (CharacterWeight.conjugacyClassEquiv charactersUp) htransport
    _ = MulOpposite.op alpha •
          CharacterWeight.conjugacyClassEquiv charactersUp
            (NormalCoreLemma48SourceInstantiation.transportedEquiv
              iotaDown iotaUp B W downstairsRep phi) :=
      CharacterWeight.conjugacyClassEquiv_smul charactersUp
        (MulOpposite.op alpha) _
    _ = MulOpposite.op alpha •
          transportedCharacterEquiv iotaDown iotaUp B W charactersDown
            charactersUp downstairs phi := rfl

/-- Exact sourced normal-core block correspondence on the literal block
carriers.  The first compatibility equation is the block statement for
Brauer inflation.  The second is the block-induction statement for the
literal lift of a character weight.  No character-to-weight bijection is a
field of this structure. -/
structure LiteralBlockCorrespondenceSource where
  blockEquiv :
    DownBlock (p := p) (k := k) (G := G) ≃
      UpBlock (k := k) (G := G)
  brauerInflationBlock : ∀ phi : IBr iotaDown,
    brauerBlockUp iotaUp hinjUp upBlocks
        (B.inflate (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp) phi) =
      blockEquiv (brauerBlockDown iotaDown hinjDown downBlocks phi)
  weightLiftBlock : ∀ omega : CharacterWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G),
    weightBlockUp upLocal
        (liftCharacterWeight W charactersDown charactersUp omega) =
      blockEquiv (weightBlockDown downLocal omega)

namespace LiteralBlockCorrespondenceSource

/-- The source on literal sets of blocks gives the old abstract block input
without introducing any freely chosen block map. -/
def toBlockTransportInput
    (S : LiteralBlockCorrespondenceSource iotaDown iotaUp
      hinjDown hinjUp downBlocks upBlocks B W charactersDown charactersUp
      downLocal upLocal) :
    BlockTransportInput
      (BlockDown := DownBlock (p := p) (k := k) (G := G))
      (BlockUp := UpBlock (k := k) (G := G))
      iotaDown iotaUp B W where
  blockEquiv := S.blockEquiv
  brauerBlockDown := brauerBlockDown iotaDown hinjDown downBlocks
  brauerBlockUp := brauerBlockUp iotaUp hinjUp upBlocks
  weightBlockDown := fun omega =>
    weightBlockDown downLocal
      (CharacterWeight.conjugacyClassEquiv charactersDown omega)
  weightBlockUp := fun omega =>
    weightBlockUp upLocal
      (CharacterWeight.conjugacyClassEquiv charactersUp omega)
  brauerCompatible := S.brauerInflationBlock
  weightCompatible := by
    intro omega
    simpa [liftCharacterWeight] using
      S.weightLiftBlock
        (CharacterWeight.conjugacyClassEquiv charactersDown omega)

/-- On the sets of Brauer characters and weights, the transported
correspondence preserves the primitive central idempotent assigned by local
block induction. -/
theorem transportedEquiv_block_preserving
    (S : LiteralBlockCorrespondenceSource iotaDown iotaUp
      hinjDown hinjUp downBlocks upBlocks B W charactersDown charactersUp
      downLocal upLocal)
    (downstairs : IBr iotaDown ≃
      CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G))
    (downstairsBlock : ∀ phi : IBr iotaDown,
      weightBlockDown downLocal (downstairs phi) =
        brauerBlockDown iotaDown hinjDown downBlocks phi)
    (phi : IBr iotaUp) :
    weightBlockUp upLocal
        (transportedCharacterEquiv iotaDown iotaUp B W charactersDown
          charactersUp downstairs phi) =
      brauerBlockUp iotaUp hinjUp upBlocks phi := by
  let phiDown := (B.equiv (P := pCore p G) (iotaDown := iotaDown)
    (iotaUp := iotaUp)).symm phi
  have hphi : B.inflate (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp) phiDown = phi := by
    exact (B.equiv (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp)).apply_symm_apply phi
  calc
    weightBlockUp upLocal
        (transportedCharacterEquiv iotaDown iotaUp B W charactersDown
          charactersUp downstairs phi) =
        weightBlockUp upLocal
          (liftCharacterWeight W charactersDown charactersUp
            (downstairs phiDown)) := by
      rw [← hphi, transportedCharacterEquiv_inflate]
    _ = S.blockEquiv
          (weightBlockDown downLocal (downstairs phiDown)) :=
      S.weightLiftBlock _
    _ = S.blockEquiv
          (brauerBlockDown iotaDown hinjDown downBlocks phiDown) :=
      congrArg S.blockEquiv (downstairsBlock phiDown)
    _ = brauerBlockUp iotaUp hinjUp upBlocks
          (B.inflate (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp) phiDown) :=
      (S.brauerInflationBlock phiDown).symm
    _ = brauerBlockUp iotaUp hinjUp upBlocks phi :=
      congrArg (brauerBlockUp iotaUp hinjUp upBlocks) hphi

/-- The block-preservation square remains compatible with the upstairs
automorphism action.  The weight side is proved from local block induction;
the Brauer side is identified with it through the transported
correspondence. -/
theorem transportedEquiv_weight_action_square
    (S : LiteralBlockCorrespondenceSource iotaDown iotaUp
      hinjDown hinjUp downBlocks upBlocks B W charactersDown charactersUp
      downLocal upLocal)
    (downstairs : IBr iotaDown ≃
      CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G))
    (downstairsBlock : ∀ phi : IBr iotaDown,
      weightBlockDown downLocal (downstairs phi) =
        brauerBlockDown iotaDown hinjDown downBlocks phi)
    (alpha : MulAut G) (phi : IBr iotaUp) :
    weightBlockUp upLocal
        (MulOpposite.op alpha •
          transportedCharacterEquiv iotaDown iotaUp B W charactersDown
            charactersUp downstairs phi) =
      MulOpposite.op alpha •
        brauerBlockUp iotaUp hinjUp upBlocks phi := by
  rw [weightBlockUp_twist]
  exact congrArg (fun b => MulOpposite.op alpha • b)
    (transportedEquiv_block_preserving iotaDown iotaUp hinjDown hinjUp
      downBlocks upBlocks B W charactersDown charactersUp downLocal upLocal
      S downstairs downstairsBlock phi)

/-- The downstairs Brauer block map has the automorphism square forced by
an equivariant block-preserving downstairs correspondence.  Both sides use
the literal block index of an actual irreducible Brauer character. -/
theorem brauerBlockDown_twist_of_downstairs
    (downstairs : IBr iotaDown ≃
      CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G))
    (downstairsEquivariant : ∀ (alpha : MulAut G) (phi : IBr iotaDown),
      downstairs
          (IrreducibleBrauerCharacter.twist iotaDown phi
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha))) =
        MulOpposite.op
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha)) •
          downstairs phi)
    (downstairsBlock : ∀ phi : IBr iotaDown,
      weightBlockDown downLocal (downstairs phi) =
        brauerBlockDown iotaDown hinjDown downBlocks phi)
    (alpha : MulAut G) (phi : IBr iotaDown) :
    brauerBlockDown iotaDown hinjDown downBlocks
        (IrreducibleBrauerCharacter.twist iotaDown phi
          (quotientMulAut (pCore p G) alpha
            (pCore_map_equiv p alpha))) =
      MulOpposite.op
          (quotientMulAut (pCore p G) alpha
            (pCore_map_equiv p alpha)) •
        brauerBlockDown iotaDown hinjDown downBlocks phi := by
  let qalpha := quotientMulAut (pCore p G) alpha
    (pCore_map_equiv p alpha)
  calc
    brauerBlockDown iotaDown hinjDown downBlocks
        (IrreducibleBrauerCharacter.twist iotaDown phi qalpha) =
        weightBlockDown downLocal
          (downstairs
            (IrreducibleBrauerCharacter.twist iotaDown phi qalpha)) :=
      (downstairsBlock _).symm
    _ = weightBlockDown downLocal
          (MulOpposite.op qalpha • downstairs phi) :=
      congrArg (weightBlockDown downLocal)
        (downstairsEquivariant alpha phi)
    _ = MulOpposite.op qalpha •
          weightBlockDown downLocal (downstairs phi) :=
      weightBlockDown_twist downLocal alpha _
    _ = MulOpposite.op qalpha •
          brauerBlockDown iotaDown hinjDown downBlocks phi :=
      congrArg (fun b => MulOpposite.op qalpha • b)
        (downstairsBlock phi)

/-- The literal upstairs Brauer block map has the required automorphism
square on every transported correspondence.  No separate arbitrary Brauer
block map or equivariance equation is assumed: the result follows from
equivariance of the transported correspondence, block preservation, and
naturality of local block induction. -/
theorem brauerBlockUp_twist_of_transport
    (S : LiteralBlockCorrespondenceSource iotaDown iotaUp
      hinjDown hinjUp downBlocks upBlocks B W charactersDown charactersUp
      downLocal upLocal)
    (downstairs : IBr iotaDown ≃
      CharacterWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G))
    (downstairsEquivariant : ∀ (alpha : MulAut G) (phi : IBr iotaDown),
      downstairs
          (IrreducibleBrauerCharacter.twist iotaDown phi
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha))) =
        MulOpposite.op
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha)) •
          downstairs phi)
    (downstairsBlock : ∀ phi : IBr iotaDown,
      weightBlockDown downLocal (downstairs phi) =
        brauerBlockDown iotaDown hinjDown downBlocks phi)
    (alpha : MulAut G) (phi : IBr iotaUp) :
    brauerBlockUp iotaUp hinjUp upBlocks
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha) =
      MulOpposite.op alpha •
        brauerBlockUp iotaUp hinjUp upBlocks phi := by
  calc
    brauerBlockUp iotaUp hinjUp upBlocks
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha) =
        weightBlockUp upLocal
          (transportedCharacterEquiv iotaDown iotaUp B W charactersDown
            charactersUp downstairs
            (IrreducibleBrauerCharacter.twist iotaUp phi alpha)) :=
      (transportedEquiv_block_preserving iotaDown iotaUp hinjDown hinjUp
        downBlocks upBlocks B W charactersDown charactersUp downLocal upLocal
        S downstairs downstairsBlock _).symm
    _ = weightBlockUp upLocal
          (MulOpposite.op alpha •
            transportedCharacterEquiv iotaDown iotaUp B W charactersDown
              charactersUp downstairs phi) :=
      congrArg (weightBlockUp upLocal)
        (transportedCharacterEquiv_equivariant iotaDown iotaUp B W
          charactersDown charactersUp downstairs downstairsEquivariant
          alpha phi)
    _ = MulOpposite.op alpha •
          weightBlockUp upLocal
            (transportedCharacterEquiv iotaDown iotaUp B W charactersDown
              charactersUp downstairs phi) :=
      weightBlockUp_twist upLocal alpha _
    _ = MulOpposite.op alpha •
          brauerBlockUp iotaUp hinjUp upBlocks phi :=
      congrArg (fun b => MulOpposite.op alpha • b)
        (transportedEquiv_block_preserving iotaDown iotaUp hinjDown hinjUp
          downBlocks upBlocks B W charactersDown charactersUp downLocal
          upLocal S downstairs downstairsBlock phi)

end LiteralBlockCorrespondenceSource

end SourcedBlockCorrespondence

end ModularRep.PaperProofs.NormalCoreLemma48LiteralBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
