import ModularRep.PaperProofs.CurrentCentralQuotientBijection
import ModularRep.PaperProofs.CurrentCyclicOuterBAW
import ModularRep.PaperProofs.CurrentFiniteSplittingFamily

/-!
# Specified block families and return from a central normal-core quotient

The ordinary coefficient field needs the finite splitting roots actually
used; it is not required to be algebraically closed.  The canonical block
families and the character/weight reindexing maps contain no matching.
Published Spath implications and identifications of the fixed modular-triple
relations are universal in the actual pair and are kept separate from the
kernel transport of a given matching.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CurrentCentralQuotientReturnAdapter

open ModularRep Formalisation CharacterWeight FDRepSimpleClassKZero
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open NormalCoreLemma48LiteralBlocks NormalCoreLemma48SourceInstantiation
open CurrentCentralQuotientBijection CurrentCyclicOuterBAW
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open CyclicOuterLemma37ActualBlockFibres CyclicOuterLemma37LiteralLocalExtension
open OddTwoActualStabilizerTriple OddTwoCentralTwoRelationInflation

universe u

/-- A coefficient-normalized output on one literal problem. -/
structure CoherentBlockWitness (P : Definition35Problem.{u}) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  matched : ∀ psi : Definition35Brauer P,
    Nonempty (CoherentMatchedCondition P psi (omega psi))

export CurrentFiniteSplittingFamily (PrimitivePhysicalSource primitiveFamily primitiveFamily_automorphisms)

section CoherentToCompatible

variable (P : Definition35Problem.{u})
variable {A : Type u} [Group A] [Finite A]
variable (pair : NormalPair A P.H)
variable (coordinates : ∀ (psi : IBr P.iota) (w : CharacterWeight P.p P.K P.H),
  PairCoordinates pair P.iota psi w)
variable (reductions : ∀ w : CharacterWeight P.p P.K P.H,
  OwnNormalizerReduction (k := P.k) w)
variable (standard : BlockTripleSourceSemantics P.p P.k P.K)

/-- The general finite group FORWARD construction of the standard modular
triple relation from the displayed coherent ambient extensions and every
intermediate block equality.  This E1/E2 source is universal in the actual
pair and its raw representative; it supplies neither a BAW claim nor a
block witness.  Unlike the covering-group equivalence, this direction uses
only the already supplied ambient packet and has no covering hypothesis.

The precise finite group source is Spath, *Inductive conditions for counting
conjectures via character triples* (2017), Proposition 3.6(b), printed p. 670,
and Theorem 3.5(b), pp. 669--670, after restriction to the prescribed action
image and the actual tuple/root identifications.  The forward proof of
Theorem 4.4, p. 678, uses these two steps on the displayed ambient extensions.
DOI: 10.4171/171-1/23.  The covering hypothesis of the equivalence is not
an input to this finite forward construction. The given matching's
equivariance and the same-pair equation are retained: these imply the
factorization by the base group and weight normalizer required in
Proposition 3.6(b). A lone ambient packet is not that antecedent. -/
structure FiniteMatchedCompatibleSource where
  actionLift : A →* P.Gamma
  actionLift_action : ∀ a, P.gamma (actionLift a) = pair.action a
  own_normalizer_roots : ∀ w : CharacterWeight P.p P.K P.H,
    RootAgreement (reductions w).root P.iota
  relation_of_matched : ∀ (omega : Definition35Brauer P ≃ Definition35Weight P),
    Definition35Equivariant P omega →
    ∀ (psi : Definition35Brauer P) (weight : Definition35Weight P)
      (w : CharacterWeight P.p P.K P.H),
    weight = omega psi →
    (Quotient.mk'' (Quotient.mk'' w : CharacterWeight.IsoClass) :
      CharacterWeight.ConjugacyClass) = weight.1 →
    Nonempty (CoherentMatchedCondition P psi weight) →
    standard.blockIsomorphic
      (pairArguments pair P.iota psi.1 w (coordinates psi.1 w) (reductions w))

/-- Cover-scoped Spath source, retained separately from the general finite
forward construction.  Its inherited projection is usable in that direction. -/
structure SpathCompatibleSource extends
    FiniteMatchedCompatibleSource P pair coordinates reductions standard where
  cover : EllPrimeCoverSource P.p P.H

/-- Reuse the published matching and restrict its graph equivariance.
The pointwise Spath implication changes only the relation proof. -/
def coherentToCompatible
    (source : FiniteMatchedCompatibleSource P pair coordinates reductions standard)
    (good : CoherentBlockWitness P) :
    CompatibleBijection pair P.iota P.irreducibleBrauerInjective P.blocks
      P.blockSource P.block coordinates reductions standard where
  omega := good.omega
  equivariant := by
    letI := definition35BrauerAction P
    letI := definition35WeightAction P
    intro a chi
    refine ⟨source.actionLift a⁻¹ • chi, ?_, ?_⟩
    · change MulOpposite.op (P.gamma ((source.actionLift a⁻¹)⁻¹)) • chi.1 = _
      rw [← map_inv, inv_inv, source.actionLift_action]
      rfl
    · have h := congrArg Subtype.val (good.equivariant (source.actionLift a⁻¹) chi)
      change (good.omega (source.actionLift a⁻¹ • chi)).1 =
        MulOpposite.op (P.gamma ((source.actionLift a⁻¹)⁻¹)) • (good.omega chi).1 at h
      rw [← map_inv, inv_inv, source.actionLift_action] at h
      exact h
  blockIsomorphism psi w matched :=
    source.relation_of_matched good.omega good.equivariant psi (good.omega psi) w
      rfl matched (good.matched psi)

end CoherentToCompatible

section PhysicalReindexing

variable (P : Definition35Problem.{u})
variable [Fintype (PrimitiveBlock P.k P.H)]
variable (primitiveBlocks : BlockIdempotentDecomposition
  (blockIdempotent : PrimitiveBlock P.k P.H → P.k[P.H]))
variable (primitiveLocal : LocalBlockInductionSource
  (p := P.p) (k := P.k) (K := P.K) (G := P.H) (Block := PrimitiveBlock P.k P.H))

/-- The specified selected idempotent, computed from the target catalogue. -/
abbrev physicalBlock : PrimitiveBlock P.k P.H := P.blocks.primitiveBlockOfIndex P.block

/-- Universal specified block-index identifications in the same group and
root convention.  The reindexing function is the already proved equivalence
between a complete block catalogue and its actual primitive idempotents. -/
structure PhysicalReindexing : Prop where
  brauer_block : ∀ psi : IBr P.iota,
    irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective primitiveBlocks psi =
      P.blocks.primitiveBlockOfIndex
        (irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective P.blocks psi)
  weight_block : ∀ w : CharacterWeight.ConjugacyClass (p := P.p) (K := P.K) (G := P.H),
    primitiveLocal.weightBlock w = P.blocks.primitiveBlockOfIndex (P.blockSource.weightBlock w)

variable (reindex : PhysicalReindexing P primitiveBlocks primitiveLocal)

/-- Reindex the Brauer fibre by the identity character function. -/
def brauerReindex : Definition35Brauer P ≃
    IBrBlock P.iota P.irreducibleBrauerInjective primitiveBlocks (physicalBlock P) :=
  (Equiv.refl (IBr P.iota)).subtypeEquiv (fun psi ↦ by
    change irreducibleBrauerCharacterBlock P.iota P.irreducibleBrauerInjective P.blocks psi =
      P.block ↔ _
    rw [reindex.brauer_block]
    exact P.blocks.primitiveBlockOfIndex_injective.eq_iff.symm)

/-- Reindex the weight fibre by the identity ambient weight class. -/
def weightReindex : Definition35Weight P ≃ WeightFibre primitiveLocal (physicalBlock P) :=
  (Equiv.refl (CharacterWeight.ConjugacyClass (p := P.p) (K := P.K) (G := P.H))).subtypeEquiv
    (fun w ↦ by
      change P.blockSource.weightBlock w = P.block ↔ primitiveLocal.weightBlock w = physicalBlock P
      rw [reindex.weight_block]
      exact P.blocks.primitiveBlockOfIndex_injective.eq_iff.symm)

end PhysicalReindexing

section CompatibleToDefinition35

variable (P : Definition35Problem.{u})
variable [Fintype (PrimitiveBlock P.k P.H)]
variable (primitiveBlocks : BlockIdempotentDecomposition
  (blockIdempotent : PrimitiveBlock P.k P.H → P.k[P.H]))
variable (primitiveLocal : LocalBlockInductionSource
  (p := P.p) (k := P.k) (K := P.K) (G := P.H) (Block := PrimitiveBlock P.k P.H))
variable (reindex : PhysicalReindexing P primitiveBlocks primitiveLocal)
variable {A : Type u} [Group A] [Finite A]
variable (pair : NormalPair A P.H)
variable (coordinates : ∀ (psi : IBr P.iota) (w : CharacterWeight P.p P.K P.H),
  PairCoordinates pair P.iota psi w)
variable (reductions : ∀ w : CharacterWeight P.p P.K P.H,
  OwnNormalizerReduction (k := P.k) w)
variable (standard : BlockTripleSourceSemantics P.p P.k P.K)
variable (automorphisms : Definition35AutomorphismStabilizerAdapter P)
variable (semantics : FLZSourceSemantics P automorphisms)

/-- U identification with the exact Definition 3.5 semidirect ambient and
relation.  The same-pair iff retains FULL raw stabilizer containment, which
the compatible-bijection theorem proves from equivariance. -/
structure Definition35CompatibleIdentification where
  ambient : A ≃* (P.H ⋊[P.gamma] P.Gamma)
  embedding_ambient : ∀ g, ambient (pair.embedding g) = SemidirectProduct.inl g
  action_ambient : ∀ a, pair.action a = semidirectToMulAut P.gamma (ambient a)
  own_normalizer_roots : ∀ w : CharacterWeight P.p P.K P.H,
    RootAgreement (reductions w).root P.iota
  relation_iff : ∀ (psi : Definition35Brauer P) (weight : Definition35Weight P),
    semantics.definition35BlockIsomorphic psi weight ↔
      ∀ w : CharacterWeight P.p P.K P.H,
        (Quotient.mk'' (Quotient.mk'' w : CharacterWeight.IsoClass) :
          CharacterWeight.ConjugacyClass) = weight.1 →
        weightStabilizer pair w ≤ characterStabilizer pair P.iota psi.1 ∧
          standard.blockIsomorphic
            (pairArguments pair P.iota psi.1 w (coordinates psi.1 w) (reductions w))

/-- Return the constructed compatible bijection to the original specified
block labels, preserving the actual character and ambient weight class. -/
def compatibleToDefinition35
    (identification : Definition35CompatibleIdentification P pair coordinates reductions
      standard automorphisms semantics)
    (good : CompatibleBijection pair P.iota P.irreducibleBrauerInjective primitiveBlocks
      primitiveLocal (physicalBlock P) coordinates reductions standard) :
    Definition35IBAWBijection P automorphisms semantics := by
  let cb := brauerReindex P primitiveBlocks primitiveLocal reindex
  let cw := weightReindex (P := P) (primitiveBlocks := primitiveBlocks)
    (primitiveLocal := primitiveLocal) reindex
  let omega := cb.trans (good.omega.trans cw.symm)
  refine { omega := omega, equivariant := ?_, blockIsomorphism := ?_ }
  · letI := definition35BrauerAction P
    letI := definition35WeightAction P
    intro a psi
    let aAmbient := identification.ambient.symm (SemidirectProduct.inr a⁻¹)
    obtain ⟨chi, hchi, homega⟩ := good.equivariant aAmbient (cb psi)
    have haction : pair.action aAmbient = P.gamma a⁻¹ := by
      rw [identification.action_ambient, MulEquiv.apply_symm_apply]
      simp
    rw [haction] at hchi homega
    have hchar : chi = cb (a • psi) := by
      apply Subtype.ext
      exact hchi
    apply Subtype.ext
    change (good.omega (cb (a • psi))).1 =
      MulOpposite.op (P.gamma a⁻¹) • (good.omega (cb psi)).1
    rw [← hchar]
    exact homega
  · intro psi
    apply (identification.relation_iff psi (omega psi)).mpr
    intro w matched
    have hm : (Quotient.mk'' (Quotient.mk'' w : CharacterWeight.IsoClass) :
        CharacterWeight.ConjugacyClass) = (good.omega (cb psi)).1 := matched
    exact ⟨CompatibleBijection.rawStabilizer_contained pair P.iota P.irreducibleBrauerInjective
      primitiveBlocks primitiveLocal (physicalBlock P) coordinates reductions standard good
      (cb psi) w hm, good.blockIsomorphism (cb psi) w hm⟩

end CompatibleToDefinition35

section CentralReturn

variable (P : Definition35Problem.{u})
variable [Fintype (P.H ⧸ pCore P.p P.H)]
variable [Fintype (PrimitiveBlock P.k P.H)]
variable [Fintype (PrimitiveBlock P.k (P.H ⧸ pCore P.p P.H))]
variable (iotaDown : PrimeRegularRootEmbedding P.p P.k P.K (P.H ⧸ pCore P.p P.H))
variable (hinjDown : IrreducibleBrauerCharacterInjectivity iotaDown)
variable (downBlocks : BlockIdempotentDecomposition
  (blockIdempotent : PrimitiveBlock P.k (P.H ⧸ pCore P.p P.H) → P.k[P.H ⧸ pCore P.p P.H]))
variable (upBlocks : BlockIdempotentDecomposition
  (blockIdempotent : PrimitiveBlock P.k P.H → P.k[P.H]))
variable (physicalDown : PrimitivePhysicalSource iotaDown)
variable (upLocal : LocalBlockInductionSource
  (p := P.p) (k := P.k) (K := P.K) (G := P.H) (Block := PrimitiveBlock P.k P.H))
variable (reindex : PhysicalReindexing P upBlocks upLocal)
variable (B : BrauerInflationInput (pCore P.p P.H) iotaDown P.iota)
variable (W : WeightTransportInput (p := P.p) (K := P.K) (G := P.H))
variable (charactersDown : LocalSplittingCharacterInput P.K (P.H ⧸ pCore P.p P.H))
variable (charactersUp : LocalSplittingCharacterInput P.K P.H)
variable (C : CentralBlockSource iotaDown P.iota hinjDown P.irreducibleBrauerInjective
  downBlocks upBlocks B W charactersDown charactersUp physicalDown.blockSource upLocal)
variable {A : Type u} [Group A] [Finite A]
variable (pair : NormalPair A P.H)
variable [coreNormal : ((pCore P.p P.H).map pair.embedding).Normal]
variable (qpair : QuotientNormalPair (p := P.p) pair)
variable (upCoordinates : ∀ (psi : IBr P.iota) (w : CharacterWeight P.p P.K P.H),
  PairCoordinates pair P.iota psi w)
variable (downCoordinates : ∀ (psi : IBr iotaDown)
    (w : CharacterWeight P.p P.K (P.H ⧸ pCore P.p P.H)),
  PairCoordinates qpair.quotientPair iotaDown psi w)
variable (upReductions : ∀ w : CharacterWeight P.p P.K P.H, OwnNormalizerReduction (k := P.k) w)
variable (downReductions : ∀ w : CharacterWeight P.p P.K (P.H ⧸ pCore P.p P.H),
  OwnNormalizerReduction (k := P.k) w)
variable (standard : BlockTripleSourceSemantics P.p P.k P.K)
variable (automorphisms : Definition35AutomorphismStabilizerAdapter P)
variable (semantics : FLZSourceSemantics P automorphisms)

local notation "bdown" => C.correspondence.blockEquiv.symm (physicalBlock P)
local notation "DP" => Definition35Family.problem
  (primitiveFamily iotaDown hinjDown downBlocks P.iota.prime physicalDown) bdown

/-- Cover-free return from an already established downstairs compatible
bijection.  In particular this entry does not require the quotient group
itself to be a universal prime-to-p cover. -/
def returnCompatibleThroughCentralQuotient
    (rawIdentification : RawQuotientClassIdentification W charactersDown charactersUp)
    (triples : TripleQuotientSource pair qpair P.iota iotaDown B upCoordinates
      downCoordinates upReductions downReductions standard)
    (mrr : MRRLemma314Source standard)
    (identification : Definition35CompatibleIdentification P pair upCoordinates upReductions
      standard automorphisms semantics)
    (down : CompatibleBijection qpair.quotientPair iotaDown hinjDown downBlocks
      physicalDown.blockSource bdown downCoordinates downReductions standard) :
    Definition35IBAWBijection P automorphisms semantics :=
  compatibleToDefinition35 P upBlocks upLocal reindex pair upCoordinates upReductions
    standard automorphisms semantics identification
    (lemma_2_6_compatibleBijection iotaDown P.iota hinjDown P.irreducibleBrauerInjective
      downBlocks upBlocks B W charactersDown charactersUp physicalDown.blockSource upLocal
      C (physicalBlock P) pair qpair upCoordinates downCoordinates upReductions downReductions
      standard rawIdentification triples mrr down)

/-- The complete return telescope.  The only supplied block witness is the
independently published, coefficient-normalized witness DOWNSTAIRS.  Every
other input is a specified carrier/coordinate identification, an actual
coefficient condition, or a universally quantified published pair relation.
The output matching is constructed by the proved central-core fibre maps
and the identity reindexing of the original specified block. -/
def returnThroughCentralQuotient
    (rawIdentification : RawQuotientClassIdentification W charactersDown charactersUp)
    (triples : TripleQuotientSource pair qpair P.iota iotaDown B upCoordinates
      downCoordinates upReductions downReductions standard)
    (mrr : MRRLemma314Source standard)
    (spath : FiniteMatchedCompatibleSource DP qpair.quotientPair downCoordinates downReductions standard)
    (identification : Definition35CompatibleIdentification P pair upCoordinates upReductions
      standard automorphisms semantics)
    (good : CoherentBlockWitness DP) :
    Definition35IBAWBijection P automorphisms semantics :=
  compatibleToDefinition35 P upBlocks upLocal reindex pair upCoordinates upReductions
    standard automorphisms semantics identification
    (lemma_2_6_compatibleBijection iotaDown P.iota hinjDown P.irreducibleBrauerInjective
      downBlocks upBlocks B W charactersDown charactersUp physicalDown.blockSource upLocal
      C (physicalBlock P) pair qpair upCoordinates downCoordinates upReductions downReductions
      standard rawIdentification triples mrr
      (coherentToCompatible DP qpair.quotientPair downCoordinates downReductions standard spath good))

end CentralReturn

/-- The independent specified and source inputs for the central return.
The source stores no coherent, compatible or Definition 3.5 block witness.
Its canonical downstairs family and block are computed by the accessors. -/
structure CentralReturnInputs (P : Definition35Problem.{u})
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (semantics : FLZSourceSemantics P automorphisms) where
  [quotientFintype : Fintype (P.H ⧸ pCore P.p P.H)]
  [upBlockFintype : Fintype (PrimitiveBlock P.k P.H)]
  [downBlockFintype : Fintype (PrimitiveBlock P.k (P.H ⧸ pCore P.p P.H))]
  iotaDown : PrimeRegularRootEmbedding P.p P.k P.K (P.H ⧸ pCore P.p P.H)
  hinjDown : IrreducibleBrauerCharacterInjectivity iotaDown
  downBlocks : BlockIdempotentDecomposition
    (blockIdempotent : PrimitiveBlock P.k (P.H ⧸ pCore P.p P.H) → P.k[P.H ⧸ pCore P.p P.H])
  upBlocks : BlockIdempotentDecomposition
    (blockIdempotent : PrimitiveBlock P.k P.H → P.k[P.H])
  physicalDown : PrimitivePhysicalSource iotaDown
  upLocal : LocalBlockInductionSource
    (p := P.p) (k := P.k) (K := P.K) (G := P.H) (Block := PrimitiveBlock P.k P.H)
  reindex : PhysicalReindexing P upBlocks upLocal
  brauer : BrauerInflationInput (pCore P.p P.H) iotaDown P.iota
  weights : WeightTransportInput (p := P.p) (K := P.K) (G := P.H)
  charactersDown : LocalSplittingCharacterInput P.K (P.H ⧸ pCore P.p P.H)
  charactersUp : LocalSplittingCharacterInput P.K P.H
  centralBlocks : CentralBlockSource iotaDown P.iota hinjDown P.irreducibleBrauerInjective
    downBlocks upBlocks brauer weights charactersDown charactersUp physicalDown.blockSource upLocal
  A : Type u
  [groupA : Group A]
  [finiteA : Finite A]
  pair : NormalPair A P.H
  [coreNormal : ((pCore P.p P.H).map pair.embedding).Normal]
  quotientPair : QuotientNormalPair (p := P.p) pair
  upCoordinates : ∀ (psi : IBr P.iota) (w : CharacterWeight P.p P.K P.H),
    PairCoordinates pair P.iota psi w
  downCoordinates : ∀ (psi : IBr iotaDown)
      (w : CharacterWeight P.p P.K (P.H ⧸ pCore P.p P.H)),
    PairCoordinates quotientPair.quotientPair iotaDown psi w
  upReductions : ∀ w : CharacterWeight P.p P.K P.H, OwnNormalizerReduction (k := P.k) w
  downReductions : ∀ w : CharacterWeight P.p P.K (P.H ⧸ pCore P.p P.H),
    OwnNormalizerReduction (k := P.k) w
  standard : BlockTripleSourceSemantics P.p P.k P.K
  rawIdentification : RawQuotientClassIdentification weights charactersDown charactersUp
  triples : TripleQuotientSource pair quotientPair P.iota iotaDown brauer upCoordinates
    downCoordinates upReductions downReductions standard
  mrr : MRRLemma314Source standard
  spath : FiniteMatchedCompatibleSource
    ((primitiveFamily iotaDown hinjDown downBlocks P.iota.prime physicalDown).problem
      (centralBlocks.correspondence.blockEquiv.symm (physicalBlock P)))
    quotientPair.quotientPair downCoordinates downReductions standard
  identification : Definition35CompatibleIdentification P pair upCoordinates upReductions
    standard automorphisms semantics

namespace CentralReturnInputs

variable {P : Definition35Problem.{u}}
variable {automorphisms : Definition35AutomorphismStabilizerAdapter P}
variable {semantics : FLZSourceSemantics P automorphisms}

/-- The specified quotient family is computed before a published witness is
supplied, using the same coefficient fields and chosen quotient root. -/
def downFamily (D : CentralReturnInputs P automorphisms semantics) : Definition35Family P.p := by
  letI := D.quotientFintype
  letI := D.downBlockFintype
  exact primitiveFamily D.iotaDown D.hinjDown D.downBlocks P.iota.prime D.physicalDown

/-- The block dominated by the original specified block. -/
def downBlock (D : CentralReturnInputs P automorphisms semantics) : D.downFamily.Block := by
  letI := D.quotientFintype
  letI := D.upBlockFintype
  letI := D.downBlockFintype
  exact D.centralBlocks.correspondence.blockEquiv.symm (physicalBlock P)

/-- Use the independently proved coherent witness on precisely the computed
quotient family/block, then run all central and specified return joins. -/
def toDefinition35 (D : CentralReturnInputs P automorphisms semantics)
    (good : CoherentBlockWitness (D.downFamily.problem D.downBlock)) :
    Definition35IBAWBijection P automorphisms semantics := by
  letI := D.quotientFintype
  letI := D.upBlockFintype
  letI := D.downBlockFintype
  letI := D.groupA
  letI := D.finiteA
  letI := D.coreNormal
  exact returnThroughCentralQuotient P D.iotaDown D.hinjDown D.downBlocks D.upBlocks
    D.physicalDown D.upLocal D.reindex D.brauer D.weights D.charactersDown D.charactersUp
    D.centralBlocks D.pair D.quotientPair D.upCoordinates D.downCoordinates D.upReductions
    D.downReductions D.standard automorphisms semantics D.rawIdentification D.triples D.mrr
    D.spath D.identification good

end CentralReturnInputs

end ModularRep.PaperProofs.CurrentCentralQuotientReturnAdapter


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
