import ModularRep.PaperProofs.NormalCoreLemma48LiteralBlocks
import ModularRep.PaperProofs.OddTwoActualStabilizerTriple

/-!
# Current Lemma 2.6: central normal-core transport on a single block

The quotient maps below are fixed by the normal core.  Navarro, Theorem
9.10, supplies the central-p block correspondence; normal-core character
inflation and the standard local splitting identifications are separate
inputs.  No full Spath packet, trivial-radical normalization or upstairs
character-to-weight correspondence is an input.

The raw quotient weight is constructed from the ORIGINAL local ordinary
character.  Its own reduction satisfies the literal normalizer inflation
equation.  The block-fibre bijection, its equivariance, and the upward MRR
application are proved below.  All relation interpretation assumptions
identify actual triples and assert no relation truth.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.CurrentCentralQuotientBijection

open ModularRep CharacterWeight FDRepSimpleClassKZero
open NormalCoreLemma48SourceInstantiation NormalCoreLemma48LiteralBlocks
open OddTwoCentralTwoRelationInflation
open CyclicOuterLemma37ActualBlockFibres

universe u

section RawQuotient

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

/-- Every radical subgroup contains the actual normal core. -/
theorem core_le_raw (w : CharacterWeight p K G) :
    pCore p G ≤ w.subgroup :=
  pCore_le_of_isRadicalSubgroup w.prime w.subgroup w.radical

/-- The canonical normalizer quotient equivalence for the original weight. -/
def rawLocalQuotientEquiv (w : CharacterWeight p K G) :
    NormalizerQuotient w.subgroup ≃*
      NormalizerQuotient (w.subgroup.map (QuotientGroup.mk' (pCore p G))) :=
  normalizerQuotientEquivOfSurjectiveOfKerLE
    (QuotientGroup.mk' (pCore p G)) (QuotientGroup.mk'_surjective _) w.subgroup
    (by simpa only [QuotientGroup.ker_mk'] using core_le_raw w)

/-- The quotient raw pair transports the same ordinary character along the
literal normalizer quotient map. -/
def quotientRawWeight (w : CharacterWeight p K G) :
    CharacterWeight p K (G ⧸ pCore p G) where
  prime := w.prime
  subgroup := w.subgroup.map (QuotientGroup.mk' (pCore p G))
  radical := (isRadicalSubgroup_iff_map_surjective_of_ker_le
    (QuotientGroup.mk' (pCore p G)) (QuotientGroup.mk'_surjective _) w.subgroup
    (by simpa only [QuotientGroup.ker_mk'] using core_le_raw w)
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup p G)).mp w.radical
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv w.localCharacter
    (rawLocalQuotientEquiv w)
  defectZero := w.defectZero.mapEquiv (rawLocalQuotientEquiv w)

@[simp] theorem quotientRawWeight_character (w : CharacterWeight p K G)
    (x : NormalizerQuotient w.subgroup) :
    (quotientRawWeight w).localCharacter (rawLocalQuotientEquiv w x) =
      w.localCharacter x := by
  change w.localCharacter ((rawLocalQuotientEquiv w).symm
    (rawLocalQuotientEquiv w x)) = _
  rw [MulEquiv.symm_apply_apply]

@[simp] theorem rawLocalQuotientEquiv_mk (w : CharacterWeight p K G)
    (x : Subgroup.normalizer (w.subgroup : Set G)) :
    rawLocalQuotientEquiv w (QuotientGroup.mk x) =
      QuotientGroup.mk (normalizerMap (QuotientGroup.mk' (pCore p G)) w.subgroup x) := rfl

/-- Own-character reductions commute with the actual normalizer map at
every prime.  No local reduction of a replacement weight occurs here. -/
theorem ownReduction_inflation
    {k : Type u} [Field k] [CharP k p] [IsAlgClosed k]
    (w : CharacterWeight p K G)
    (upRoot : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer (w.subgroup : Set G)))
    (downRoot : PrimeRegularRootEmbedding p k K
      (Subgroup.normalizer ((quotientRawWeight w).subgroup : Set (G ⧸ pCore p G))))
    (up : IBr upRoot) (down : IBr downRoot)
    (hup : NormalizerInflatedReduction w.subgroup w.localCharacter upRoot up)
    (hdown : NormalizerInflatedReduction (quotientRawWeight w).subgroup
      (quotientRawWeight w).localCharacter downRoot down) :
    up.1 = pullbackPrimeRegularClassFunction
      (normalizerMap (QuotientGroup.mk' (pCore p G)) w.subgroup) down.1 := by
  ext x
  change up.1 x = down.1
    (PrimeRegularElement.map (normalizerMap (QuotientGroup.mk' (pCore p G)) w.subgroup) x)
  calc
    up.1 x = w.localCharacter (QuotientGroup.mk x.1) := (hup x).symm
    _ = (quotientRawWeight w).localCharacter
        (rawLocalQuotientEquiv w (QuotientGroup.mk x.1)) :=
      (quotientRawWeight_character w _).symm
    _ = down.1 (PrimeRegularElement.map
        (normalizerMap (QuotientGroup.mk' (pCore p G)) w.subgroup) x) := by
      rw [rawLocalQuotientEquiv_mk]
      exact hdown (PrimeRegularElement.map
        (normalizerMap (QuotientGroup.mk' (pCore p G)) w.subgroup) x)

end RawQuotient

section Fibres

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype (G ⧸ pCore p G)]
variable [Fintype (DownBlock (p := p) (k := k) (G := G))]
variable [Fintype (UpBlock (k := k) (G := G))]
variable [MulAction (MulAut (G ⧸ pCore p G))ᵐᵒᵖ
  (DownBlock (p := p) (k := k) (G := G))]
variable [MulAction (MulAut G)ᵐᵒᵖ (UpBlock (k := k) (G := G))]
variable (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ pCore p G))
variable (iotaUp : PrimeRegularRootEmbedding p k K G)
variable (hinjDown : IrreducibleBrauerCharacterInjectivity iotaDown)
variable (hinjUp : IrreducibleBrauerCharacterInjectivity iotaUp)
variable (downBlocks : BlockIdempotentDecomposition
  (blockIdempotent : DownBlock (p := p) (k := k) (G := G) → k[G ⧸ pCore p G]))
variable (upBlocks : BlockIdempotentDecomposition
  (blockIdempotent : UpBlock (k := k) (G := G) → k[G]))
variable (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
variable (W : WeightTransportInput (p := p) (K := K) (G := G))
variable (charactersDown : LocalSplittingCharacterInput K (G ⧸ pCore p G))
variable (charactersUp : LocalSplittingCharacterInput K G)
variable (downLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G ⧸ pCore p G)
  (Block := DownBlock (p := p) (k := k) (G := G)))
variable (upLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G)
  (Block := UpBlock (k := k) (G := G)))

/-- Navarro's central-p correspondence is explicitly restricted to a central
normal core.  Its maps are the existing literal primitive-block maps. -/
structure CentralBlockSource where
  central : pCore p G ≤ Subgroup.center G
  correspondence : LiteralBlockCorrespondenceSource iotaDown iotaUp
    hinjDown hinjUp downBlocks upBlocks B W charactersDown charactersUp downLocal upLocal

variable (C : CentralBlockSource iotaDown iotaUp hinjDown hinjUp downBlocks upBlocks
  B W charactersDown charactersUp downLocal upLocal)
variable (b : UpBlock (k := k) (G := G))

local notation "bdown" => C.correspondence.blockEquiv.symm b
local notation "BE" => B.equiv (P := pCore p G) (iotaDown := iotaDown) (iotaUp := iotaUp)

/-- The existing weight lift, now as an equivalence with literal character
weight endpoints. -/
def weightEquiv :
    CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G ⧸ pCore p G) ≃
      CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G) :=
  (CharacterWeight.conjugacyClassEquiv charactersDown).symm.trans
    (W.conjugacyClassEquiv.trans (CharacterWeight.conjugacyClassEquiv charactersUp))

/-- Naturality of the literal weight equivalence, independently of any
character-to-weight matching. -/
theorem weightEquiv_twist (alpha : MulAut G)
    (w : CharacterWeight.ConjugacyClass (p := p) (K := K) (G := G ⧸ pCore p G)) :
    weightEquiv W charactersDown charactersUp
        (MulOpposite.op (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)) • w) =
      MulOpposite.op alpha • weightEquiv W charactersDown charactersUp w := by
  let qa := quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)
  have hsymm : (CharacterWeight.conjugacyClassEquiv charactersDown).symm
        (MulOpposite.op qa • w) = MulOpposite.op qa •
          (CharacterWeight.conjugacyClassEquiv charactersDown).symm w := by
    apply (CharacterWeight.conjugacyClassEquiv charactersDown).injective
    rw [Equiv.apply_symm_apply, CharacterWeight.conjugacyClassEquiv_smul,
      Equiv.apply_symm_apply]
  change CharacterWeight.conjugacyClassEquiv charactersUp
      (W.liftConjugacyClass ((CharacterWeight.conjugacyClassEquiv charactersDown).symm
        (MulOpposite.op qa • w))) = _
  rw [hsymm]
  change CharacterWeight.conjugacyClassEquiv charactersUp
      (W.liftConjugacyClass (RepresentationWeight.rightTwistConjugacyClass qa
        ((CharacterWeight.conjugacyClassEquiv charactersDown).symm w))) = _
  rw [W.liftConjugacyClass_rightTwist]
  exact CharacterWeight.conjugacyClassEquiv_smul charactersUp (MulOpposite.op alpha) _

local notation "WE" => weightEquiv W charactersDown charactersUp

/-- Restrict actual Brauer inflation to this single arbitrary block. -/
def brauerFibreEquiv :
    IBrBlock iotaDown hinjDown downBlocks bdown ≃ IBrBlock iotaUp hinjUp upBlocks b :=
  (BE).subtypeEquiv (fun phi ↦ by
    change brauerBlockDown iotaDown hinjDown downBlocks phi = bdown ↔
      brauerBlockUp iotaUp hinjUp upBlocks (BE phi) = b
    rw [B.equiv_apply, C.correspondence.brauerInflationBlock]
    exact C.correspondence.blockEquiv.eq_symm_apply)

/-- Restrict the existing weight equivalence to the same specified block. -/
def weightFibreEquiv :
    WeightFibre downLocal bdown ≃ WeightFibre upLocal b :=
  (WE).subtypeEquiv (fun w ↦ by
    change weightBlockDown downLocal w = bdown ↔
      weightBlockUp upLocal (liftCharacterWeight W charactersDown charactersUp w) = b
    rw [C.correspondence.weightLiftBlock]
    exact C.correspondence.blockEquiv.eq_symm_apply)

/-- The upstairs block bijection uses only the given downstairs block
bijection.  It does not require a bijection on every block. -/
def blockEquiv
    (omega : IBrBlock iotaDown hinjDown downBlocks bdown ≃ WeightFibre downLocal bdown) :
    IBrBlock iotaUp hinjUp upBlocks b ≃ WeightFibre upLocal b :=
  (brauerFibreEquiv iotaDown iotaUp hinjDown hinjUp downBlocks upBlocks B W
    charactersDown charactersUp downLocal upLocal C b).symm.trans
    (omega.trans (weightFibreEquiv iotaDown iotaUp hinjDown hinjUp downBlocks upBlocks B W
      charactersDown charactersUp downLocal upLocal C b))

end Fibres

section NormalPairTriples

open Formalisation ModularRep.ManuscriptVerification.CyclicOuterBAW
open CyclicOuterLemma37Concrete OddTwoActualStabilizerTriple

variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Finite A]

/-- A literal finite normal pair, with its actual conjugation action. -/
structure NormalPair (A G : Type u) [Group A] [Group G] where
  embedding : G →* A
  injective : Function.Injective embedding
  normal : embedding.range.Normal
  action : A →* MulAut G
  conjugation : ∀ a g, embedding (action a g) = a * embedding g * a⁻¹

variable (pair : NormalPair A G)
variable (iota : PrimeRegularRootEmbedding p k K G)

def characterStabilizer (psi : IBr iota) : Subgroup A :=
  letI := rightAutomorphismAction (X := IBr iota) pair.action
  MulAction.stabilizer A psi

def weightStabilizer (w : CharacterWeight p K G) : Subgroup A :=
  letI := rightAutomorphismAction
    (X := CharacterWeight.IsoClass (p := p) (K := K) (G := G)) pair.action
  MulAction.stabilizer A (Quotient.mk'' w : CharacterWeight.IsoClass)

def tripleBase (psi : IBr iota) : Subgroup (characterStabilizer pair iota psi) :=
  pair.embedding.range.comap (characterStabilizer pair iota psi).subtype

instance tripleBase_normal (psi : IBr iota) : (tripleBase pair iota psi).Normal := by
  letI := pair.normal
  exact inferInstanceAs (pair.embedding.range.comap _).Normal

def tripleLocal (psi : IBr iota) (w : CharacterWeight p K G) :
    Subgroup (characterStabilizer pair iota psi) :=
  (weightStabilizer pair w).comap (characterStabilizer pair iota psi).subtype

/-- E1/U coordinate identifications only.  The ambient group, normal base
and local subgroup are already the actual stabilizers and intersections.
The ambient equations disallow unrelated abstract presentations. -/
structure PairCoordinates (psi : IBr iota) (w : CharacterWeight p K G) where
  base : G ≃* tripleBase pair iota psi
  base_ambient : ∀ g, (base g).1.1 = pair.embedding g
  normalizer : Subgroup.normalizer (w.subgroup : Set G) ≃*
    ↥(tripleBase pair iota psi ⊓ tripleLocal pair iota psi w)
  normalizer_ambient : ∀ g, (normalizer g).1.1 = pair.embedding g.1

/-- Construct the actual pair of modular triples in these fixed coordinates.
The local character is the original weight's own inflated Brauer reduction. -/
abbrev pairArguments (psi : IBr iota) (w : CharacterWeight p K G)
    (coords : PairCoordinates pair iota psi w)
    (reduction : OwnNormalizerReduction (k := k) w) : BlockTripleArguments p k K where
  G := characterStabilizer pair iota psi
  N := tripleBase pair iota psi
  H := tripleLocal pair iota psi w
  iotaN := iota.alongMulEquiv coords.base
  iotaM := reduction.root.alongMulEquiv coords.normalizer
  theta := IrreducibleBrauerCharacter.alongMulEquiv iota coords.base psi
  phi := IrreducibleBrauerCharacter.alongMulEquiv reduction.root coords.normalizer reduction.brauer

/-- The local argument is tied to the same ordinary character pointwise. -/
theorem pairArguments_own_character (psi : IBr iota) (w : CharacterWeight p K G)
    (coords : PairCoordinates pair iota psi w)
    (reduction : OwnNormalizerReduction (k := k) w)
    (x : PrimeRegularElement
      (G := ↥(tripleBase pair iota psi ⊓ tripleLocal pair iota psi w)) p) :
    (pairArguments pair iota psi w coords reduction).phi.1 x =
      w.localCharacter (QuotientGroup.mk (coords.normalizer.symm x.1)) :=
  (reduction.own_reduction (PrimeRegularElement.map coords.normalizer.symm.toMonoidHom x)).symm

variable [coreNormal : ((pCore p G).map pair.embedding).Normal]

/-- The actual ambient quotient and its conjugation action.  Normality of
the image of the characteristic core and these map identifications are
standard group-theoretic inputs, independent of any correspondence. -/
structure QuotientNormalPair where
  quotientPair : NormalPair (A ⧸ (pCore p G).map pair.embedding) (G ⧸ pCore p G)
  embedding_projection : ∀ g,
    quotientPair.embedding (QuotientGroup.mk' (pCore p G) g) =
      @QuotientGroup.mk' A _ ((pCore p G).map pair.embedding) coreNormal (pair.embedding g)
  action_projection : ∀ a,
    quotientPair.action
        (@QuotientGroup.mk' A _ ((pCore p G).map pair.embedding) coreNormal a) =
      quotientMulAut (pCore p G) (pair.action a) (pCore_map_equiv p (pair.action a))

end NormalPairTriples

section CompatibleBijections

open Formalisation ModularRep.ManuscriptVerification.CyclicOuterBAW
open OddTwoActualStabilizerTriple

variable {p : ℕ} {k K G A ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Finite A] [Fintype ι]
variable [MulAction (MulAut G)ᵐᵒᵖ ι]
variable (pair : NormalPair A G)
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {idempotents : ι → k[G]} (blocks : BlockIdempotentDecomposition idempotents)
variable (localBlocks : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G) (Block := ι)) (b : ι)
variable (coordinates : ∀ (psi : IBr iota) (w : CharacterWeight p K G),
  PairCoordinates pair iota psi w)
variable (reductions : ∀ w : CharacterWeight p K G, OwnNormalizerReduction (k := k) w)
variable (standard : BlockTripleSourceSemantics p k K)

/-- A compatible block bijection on a finite normal pair.  Equivariance is
expressed as invariance of its graph, which also records preservation of the
literal block fibre.  Relations are required for EVERY representative of
each matched ambient weight class. -/
structure CompatibleBijection where
  omega : IBrBlock iota hinj blocks b ≃ WeightFibre localBlocks b
  equivariant : ∀ (a : A) (chi : IBrBlock iota hinj blocks b),
    ∃ psi : IBrBlock iota hinj blocks b,
      psi.1 = IrreducibleBrauerCharacter.twist iota chi.1 (pair.action a) ∧
        (omega psi).1 = MulOpposite.op (pair.action a) • (omega chi).1
  blockIsomorphism : ∀ (chi : IBrBlock iota hinj blocks b)
      (w : CharacterWeight p K G),
    (Quotient.mk'' (Quotient.mk'' w : CharacterWeight.IsoClass) :
      CharacterWeight.ConjugacyClass) = (omega chi).1 →
    standard.blockIsomorphic
      (pairArguments pair iota chi.1 w (coordinates chi.1 w) (reductions w))

/-- Equivariance forces the full raw-pair stabilizer into the Brauer
stabilizer.  Thus the local group in `pairArguments` is precisely the
required full `N_A(Q)_theta`, not an unproved intersection replacement. -/
theorem CompatibleBijection.rawStabilizer_contained
    (good : CompatibleBijection pair iota hinj blocks localBlocks b coordinates reductions standard)
    (chi : IBrBlock iota hinj blocks b) (w : CharacterWeight p K G)
    (matched : (Quotient.mk'' (Quotient.mk'' w : CharacterWeight.IsoClass) :
      CharacterWeight.ConjugacyClass) = (good.omega chi).1) :
    weightStabilizer pair w ≤ characterStabilizer pair iota chi.1 := by
  intro a ha
  have hraw : MulOpposite.op (pair.action a⁻¹) •
      (Quotient.mk'' w : CharacterWeight.IsoClass) = Quotient.mk'' w := ha
  have hclass : MulOpposite.op (pair.action a⁻¹) • (good.omega chi).1 =
      (good.omega chi).1 := by
    rw [← matched]
    exact congrArg
      (fun r : CharacterWeight.IsoClass (p := p) (K := K) (G := G) ↦
        (Quotient.mk'' r : CharacterWeight.ConjugacyClass)) hraw
  obtain ⟨psi, hpsi, homega⟩ := good.equivariant a⁻¹ chi
  have heq : psi = chi := good.omega.injective (Subtype.ext (homega.trans hclass))
  change MulOpposite.op (pair.action a⁻¹) • chi.1 = chi.1
  exact hpsi.symm.trans (congrArg Subtype.val heq)

end CompatibleBijections

section TripleCoordinateEquivalence

variable {p : ℕ} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Data identifying two presentations of the same modular triple pair.
Ambient, base and intersection maps, the whole local subgroup, both root
conventions and both character functions must agree.  No relation is a field. -/
structure TripleCoordinateEquivalence (T U : BlockTripleArguments p k K) where
  ambient : T.G ≃* U.G
  base : T.N ≃* U.N
  intersection : ↥(T.N ⊓ T.H) ≃* ↥(U.N ⊓ U.H)
  base_ambient : ∀ x, (base x : U.G) = ambient x
  intersection_ambient : ∀ x, (intersection x : U.G) = ambient x
  local_image : T.H.map ambient.toMonoidHom = U.H
  global_roots : ∀ V : FDRep k U.N,
    Representation.BrauerRootLiftCompatibleAlong V.ρ U.iotaN T.iotaN base.toMonoidHom
  local_roots : ∀ V : FDRep k ↥(U.N ⊓ U.H),
    Representation.BrauerRootLiftCompatibleAlong V.ρ U.iotaM T.iotaM intersection.toMonoidHom
  global_values : ∀ x : PrimeRegularElement (G := T.N) p,
    T.theta.1 x = U.theta.1 (PrimeRegularElement.map base.toMonoidHom x)
  local_values : ∀ x : PrimeRegularElement (G := ↥(T.N ⊓ T.H)) p,
    T.phi.1 x = U.phi.1 (PrimeRegularElement.map intersection.toMonoidHom x)

end TripleCoordinateEquivalence

section TripleQuotients

open OddTwoActualStabilizerTriple

variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Group A] [Finite A]
variable (pair : NormalPair A G)
variable [coreNormal : ((pCore p G).map pair.embedding).Normal]
variable (qpair : QuotientNormalPair (p := p) pair)
variable [Fintype (G ⧸ pCore p G)]
variable (iotaUp : PrimeRegularRootEmbedding p k K G)
variable (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ pCore p G))
variable (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
variable (upCoordinates : ∀ (psi : IBr iotaUp) (w : CharacterWeight p K G),
  PairCoordinates pair iotaUp psi w)
variable (downCoordinates : ∀ (psi : IBr iotaDown)
    (w : CharacterWeight p K (G ⧸ pCore p G)),
  PairCoordinates qpair.quotientPair iotaDown psi w)
variable (upReductions : ∀ w : CharacterWeight p K G, OwnNormalizerReduction (k := k) w)
variable (downReductions : ∀ w : CharacterWeight p K (G ⧸ pCore p G),
  OwnNormalizerReduction (k := k) w)

/-- The quotient kernel inside the actual Brauer stabilizer. -/
def stabilizerCore (psi : IBr iotaUp) : Subgroup (characterStabilizer pair iotaUp psi) :=
  ((pCore p G).map pair.embedding).comap (characterStabilizer pair iotaUp psi).subtype

instance stabilizerCore_normal (psi : IBr iotaUp) :
    (stabilizerCore pair iotaUp psi).Normal := by
  exact inferInstanceAs (((pCore p G).map pair.embedding).comap _).Normal

include upCoordinates in
/-- The core lies in the local group of the SAME raw weight.  This is
derived from radical containment and the literal coordinate equations. -/
theorem stabilizerCore_le (psi : IBr iotaUp) (w : CharacterWeight p K G) :
    stabilizerCore pair iotaUp psi ≤
      tripleBase pair iotaUp psi ⊓ tripleLocal pair iotaUp psi w := by
  intro x hx
  obtain ⟨g, hg, hgx⟩ := hx
  let n : Subgroup.normalizer (w.subgroup : Set G) :=
    ⟨g, w.subgroup.le_normalizer (core_le_raw w hg)⟩
  have heq : ((upCoordinates psi w).normalizer n).1 = x := by
    apply Subtype.ext
    exact ((upCoordinates psi w).normalizer_ambient n).trans hgx
  rw [← heq]
  exact ((upCoordinates psi w).normalizer n).2

local notation "BE" => B.equiv (P := pCore p G) (iotaDown := iotaDown) (iotaUp := iotaUp)
local notation "upArgs" => (fun (psi : IBr iotaDown) (w : CharacterWeight p K G) ↦
  pairArguments pair iotaUp ((BE) psi) w (upCoordinates ((BE) psi) w) (upReductions w))
local notation "downArgs" => (fun (psi : IBr iotaDown)
  (w : CharacterWeight p K (G ⧸ pCore p G)) ↦
  pairArguments qpair.quotientPair iotaDown psi w (downCoordinates psi w) (downReductions w))

/-- U/E1 identifications of quotient stabilizers, common roots and literal
inflated characters; U invariance of the SAME MRR relation under those
coordinates.  Every pair is quantified, independently of any matching.
The data contain no relation truth, equivariant bijection or BAW conclusion. -/
structure TripleQuotientSource (standard : BlockTripleSourceSemantics p k K) where
  quotient_roots : ∀ V : FDRep k (G ⧸ pCore p G),
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaDown iotaUp
      (QuotientGroup.mk' (pCore p G))
  up_normalizer_roots : ∀ (w : CharacterWeight p K G) (V : FDRep k G),
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaUp (upReductions w).root
      (Subgroup.normalizer (w.subgroup : Set G)).subtype
  down_normalizer_roots : ∀ (w : CharacterWeight p K (G ⧸ pCore p G))
      (V : FDRep k (G ⧸ pCore p G)),
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaDown (downReductions w).root
      (Subgroup.normalizer (w.subgroup : Set (G ⧸ pCore p G))).subtype
  stabilizerEquiv : ∀ psi : IBr iotaDown,
    (characterStabilizer pair iotaUp ((BE) psi) ⧸
      stabilizerCore pair iotaUp ((BE) psi)) ≃*
        characterStabilizer qpair.quotientPair iotaDown psi
  stabilizer_projection : ∀ (psi : IBr iotaDown)
      (x : characterStabilizer pair iotaUp ((BE) psi)),
    (stabilizerEquiv psi (QuotientGroup.mk x)).1 =
      QuotientGroup.mk' ((pCore p G).map pair.embedding) x.1
  inflation : ∀ (psi : IBr iotaDown) (w : CharacterWeight p K G),
    (upArgs psi w).QuotientInflationData (stabilizerCore pair iotaUp ((BE) psi))
  quotientCoordinates : ∀ (psi : IBr iotaDown) (w : CharacterWeight p K G),
    TripleCoordinateEquivalence (inflation psi w).downstairs (downArgs psi (quotientRawWeight w))
  quotientCoordinates_ambient : ∀ (psi : IBr iotaDown) (w : CharacterWeight p K G),
    (quotientCoordinates psi w).ambient = stabilizerEquiv psi
  relation_iff : ∀ (psi : IBr iotaDown) (w : CharacterWeight p K G),
    standard.blockIsomorphic (inflation psi w).downstairs ↔
      standard.blockIsomorphic (downArgs psi (quotientRawWeight w))

/-- Lift the actual relation at the same character and original raw weight
using MRR, Lemma 3.14, with its arbitrary normal-kernel hypothesis. -/
theorem sameWeight_relation_upward
    (standard : BlockTripleSourceSemantics p k K)
    (source : TripleQuotientSource pair qpair iotaUp iotaDown B upCoordinates
      downCoordinates upReductions downReductions standard)
    (mrr : MRRLemma314Source standard) (psi : IBr iotaDown)
    (w : CharacterWeight p K G)
    (hdown : standard.blockIsomorphic (downArgs psi (quotientRawWeight w))) :
    standard.blockIsomorphic (upArgs psi w) :=
  blockIsomorphic_of_quotient mrr (upArgs psi w)
    (stabilizerCore pair iotaUp ((BE) psi))
    (stabilizerCore_le pair iotaUp upCoordinates ((BE) psi) w)
    (source.inflation psi w) ((source.relation_iff psi w).mpr hdown)

end TripleQuotients

section Assembly

open OddTwoActualStabilizerTriple

variable {p : ℕ} {k K G A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype (G ⧸ pCore p G)] [Group A] [Finite A]
variable [Fintype (DownBlock (p := p) (k := k) (G := G))]
variable [Fintype (UpBlock (k := k) (G := G))]
variable [MulAction (MulAut (G ⧸ pCore p G))ᵐᵒᵖ
  (DownBlock (p := p) (k := k) (G := G))]
variable [MulAction (MulAut G)ᵐᵒᵖ (UpBlock (k := k) (G := G))]
variable (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ pCore p G))
variable (iotaUp : PrimeRegularRootEmbedding p k K G)
variable (hinjDown : IrreducibleBrauerCharacterInjectivity iotaDown)
variable (hinjUp : IrreducibleBrauerCharacterInjectivity iotaUp)
variable (downBlocks : BlockIdempotentDecomposition
  (blockIdempotent : DownBlock (p := p) (k := k) (G := G) → k[G ⧸ pCore p G]))
variable (upBlocks : BlockIdempotentDecomposition
  (blockIdempotent : UpBlock (k := k) (G := G) → k[G]))
variable (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
variable (W : WeightTransportInput (p := p) (K := K) (G := G))
variable (charactersDown : LocalSplittingCharacterInput K (G ⧸ pCore p G))
variable (charactersUp : LocalSplittingCharacterInput K G)
variable (downLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G ⧸ pCore p G)
  (Block := DownBlock (p := p) (k := k) (G := G)))
variable (upLocal : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G)
  (Block := UpBlock (k := k) (G := G)))
variable (C : CentralBlockSource iotaDown iotaUp hinjDown hinjUp downBlocks upBlocks
  B W charactersDown charactersUp downLocal upLocal)
variable (b : UpBlock (k := k) (G := G))
variable (pair : NormalPair A G)
variable [coreNormal : ((pCore p G).map pair.embedding).Normal]
variable (qpair : QuotientNormalPair (p := p) pair)
variable (upCoordinates : ∀ (psi : IBr iotaUp) (w : CharacterWeight p K G),
  PairCoordinates pair iotaUp psi w)
variable (downCoordinates : ∀ (psi : IBr iotaDown)
    (w : CharacterWeight p K (G ⧸ pCore p G)),
  PairCoordinates qpair.quotientPair iotaDown psi w)
variable (upReductions : ∀ w : CharacterWeight p K G, OwnNormalizerReduction (k := k) w)
variable (downReductions : ∀ w : CharacterWeight p K (G ⧸ pCore p G),
  OwnNormalizerReduction (k := k) w)
variable (standard : BlockTripleSourceSemantics p k K)

local notation "bdown" => C.correspondence.blockEquiv.symm b
local notation "BE" => B.equiv (P := pCore p G) (iotaDown := iotaDown) (iotaUp := iotaUp)
local notation "WE" => weightEquiv W charactersDown charactersUp
local notation "BF" => brauerFibreEquiv iotaDown iotaUp hinjDown hinjUp downBlocks upBlocks
  B W charactersDown charactersUp downLocal upLocal C b
local notation "WF" => weightFibreEquiv iotaDown iotaUp hinjDown hinjUp downBlocks upBlocks
  B W charactersDown charactersUp downLocal upLocal C b

/-- E1/U identification of the canonical representation-weight lift with
the same raw ordinary character transported by `rawLocalQuotientEquiv`.
This holds for every raw weight and contains no character matching. -/
def RawQuotientClassIdentification : Prop :=
  ∀ w : CharacterWeight p K G,
    (WE) (Quotient.mk'' (Quotient.mk'' (quotientRawWeight w) : CharacterWeight.IsoClass)) =
      (Quotient.mk'' (Quotient.mk'' w : CharacterWeight.IsoClass) : CharacterWeight.ConjugacyClass)

/-- Current Lemma 2.6.  The hypothesis concerns only the dominated block.
Lean constructs its upstairs equivalence, transports its graph under the
actual A/P action, and applies the general normal-kernel MRR implication
for every representative of the SAME matched weight class. -/
def lemma_2_6_compatibleBijection
    (rawIdentification : RawQuotientClassIdentification W charactersDown charactersUp)
    (triples : TripleQuotientSource pair qpair iotaUp iotaDown B upCoordinates
      downCoordinates upReductions downReductions standard)
    (mrr : MRRLemma314Source standard)
    (down : CompatibleBijection qpair.quotientPair iotaDown hinjDown downBlocks
      downLocal bdown downCoordinates downReductions standard) :
    CompatibleBijection pair iotaUp hinjUp upBlocks upLocal b upCoordinates upReductions standard := by
  let omega := (BF).symm.trans (down.omega.trans (WF))
  refine { omega := omega, equivariant := ?_, blockIsomorphism := ?_ }
  · intro a chi
    let chiDown := (BF).symm chi
    obtain ⟨psiDown, hpsi, homega⟩ :=
      down.equivariant (QuotientGroup.mk' ((pCore p G).map pair.embedding) a) chiDown
    rw [qpair.action_projection] at hpsi homega
    have hchi : (BE) chiDown.1 = chi.1 :=
      congrArg Subtype.val ((BF).apply_symm_apply chi)
    refine ⟨(BF) psiDown, ?_, ?_⟩
    · change (BE) psiDown.1 = IrreducibleBrauerCharacter.twist iotaUp chi.1 (pair.action a)
      rw [hpsi, B.equiv_apply, B.inflate_twist, ← B.equiv_apply, hchi]
    · change (WE) (down.omega ((BF).symm ((BF) psiDown))).1 =
        MulOpposite.op (pair.action a) • (WE) (down.omega chiDown).1
      rw [Equiv.symm_apply_apply, homega]
      exact weightEquiv_twist W charactersDown charactersUp (pair.action a) _
  · intro chi w matched
    let chiDown := (BF).symm chi
    have hchi : (BE) chiDown.1 = chi.1 :=
      congrArg Subtype.val ((BF).apply_symm_apply chi)
    have downMatched :
        (Quotient.mk'' (Quotient.mk'' (quotientRawWeight w) : CharacterWeight.IsoClass) :
          CharacterWeight.ConjugacyClass) = (down.omega chiDown).1 := by
      apply (WE).injective
      rw [rawIdentification w]
      exact matched
    have hdown := down.blockIsomorphism chiDown (quotientRawWeight w) downMatched
    have hup := sameWeight_relation_upward pair qpair iotaUp iotaDown B upCoordinates
      downCoordinates upReductions downReductions standard triples mrr chiDown.1 w hdown
    dsimp only at hup
    rw [hchi] at hup
    exact hup

end Assembly
end ModularRep.PaperProofs.CurrentCentralQuotientBijection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
