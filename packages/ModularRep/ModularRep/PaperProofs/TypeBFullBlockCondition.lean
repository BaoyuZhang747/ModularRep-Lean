import ModularRep.PaperProofs.EvenFieldFLZQuotientBlockFibre
import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily

/-!
# A fixed, literal output for the complete block condition

This file defines output data only. It contains no published-result axiom,
no source implication, and no caller-selected result relation. In particular,
none of the records below is an admissible hypothesis asserting the Type B
conclusion. A source theorem must have its independent, literal hypotheses
and produce these data as its conclusion.

The block output completes the existing `RelativeBlockConditionWitness` on
both quotient fibres. Its quotient weight is constructed from the already
matched ordinary character and the actual image of the radical subgroup.
Completeness and automorphism equivariance concern that map, rather than a
new unrestricted matching. The local block catalogue uses the same specified
idempotents as the quotient Brauer block decomposition.

The family output records the radical-fibre and central character clauses of
Spath (2013), Definition 4.1(i)--(ii), and the normalization in (iv), in
addition to the actual ambient extension/intermediate block data in the
relative witness. Brough--Spath (2022), Definition 4.3 and Remark 4.4, is the
single-block formulation. Koshitani--Spath (2016), Lemma 3.3, is the published
passage from an automorphism transversal of blocks to the global formulation.
This file does not apply that passage or theorems 4.5 / 2.1 / 1.1.

Uniform character-value conventions remain a requirement on the independent
source domain. A theorem about ordinary and Brauer characters does not give
extensions for arbitrary incompatible root embeddings stored in a family.
Reference characters, common kernels and ambient extension groups below are
output choices, not preselected inputs to a criterion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBFullBlockCondition

open Formalisation ModularRep
open CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37ActualBlockFibres
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily EvenFieldFLZQuotientBlockFibre

universe u

variable {ell : ℕ} {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H} {block : family.Block}

/-- Two character-value conventions agree on every root used by the first
literal group. The subgroup/quotient maps relating the groups are fixed in
the surrounding matched data. No equality outside that root domain is used. -/
def RootLiftAgreement {k K H A : Type u}
    [Field k] [Field K] [Group H] [Finite H] [Group A] [Finite A]
    (iotaH : PrimeRegularRootEmbedding ell k K H)
    (iotaA : PrimeRegularRootEmbedding ell k K A) : Prop :=
  ∀ zeta : rootsOfUnity (primeRegularExponent ell H) k,
    iotaH.lift (((zeta : kˣ) : k)) = iotaA.lift (((zeta : kˣ) : k))

/-- The quotient group is fixed by the actual reference central kernel. -/
abbrev QuotientCarrier
    (W : RelativeBlockConditionWitness family cover block) :=
  CentralCharacterQuotient (family.problem block) W.reference

local instance quotientFintype
    (W : RelativeBlockConditionWitness family cover block) :
    Fintype (QuotientCarrier W) := Fintype.ofFinite _

/-- The raw quotient weight is computed from the matched local ordinary
character. No independent weight label or quotient radical is selected. -/
def quotientRawWeight
    (W : RelativeBlockConditionWitness family cover block)
    (psi : Definition35Brauer (family.problem block)) :
    CharacterWeight ell family.K (QuotientCarrier W) where
  prime := family.ellPrime
  subgroup := quotientRadical (family.problem block) W.reference (W.omega psi)
  radical := (W.matched psi).weight.radical
  localCharacter := (W.matched psi).weight.ordinary
  defectZero := (W.matched psi).weight.defectZero

/-- Ambient conjugacy class of the constructed quotient weight. -/
def quotientWeightClass
    (W : RelativeBlockConditionWitness family cover block)
    (psi : Definition35Brauer (family.problem block)) :
    CharacterWeight.ConjugacyClass
      (p := ell) (K := family.K) (G := QuotientCarrier W) :=
  Quotient.mk'' (Quotient.mk'' (quotientRawWeight W psi))

/-- Complete literal single-block output. This is an output carrier, never
an independently accepted input stating the desired block condition. -/
structure BlockWitness
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H) (block : family.Block) where
  relative : RelativeBlockConditionWitness family cover block
  roots : FixedQuotientRootSource relative
  brauerReverse : QuotientBlockFibreReverseSource relative roots
  [quotientBlockAction :
    MulAction (MulAut (QuotientCarrier relative))ᵐᵒᵖ relative.QuotientBlock]
  quotientBlockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := family.k) (K := family.K)
    (G := QuotientCarrier relative) (Block := relative.QuotientBlock)
  quotientBlockIdempotent : ∀ b : relative.QuotientBlock,
    quotientBlockSource.operations.ambientBlockData.blockIdempotent b =
      relative.quotientBlockIdempotent b
  /-- The quotient block operation is interpreted in the same root
  convention as its actual Brauer fibre. The unguarded all-root source is
  deliberately absent. -/
  quotientBlockCompatibility :
    TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
      (fixedQuotientRoot relative) quotientBlockSource.operations
  quotientRoots_agree : ∀ zeta : rootsOfUnity
      (primeRegularExponent ell (QuotientCarrier relative)) family.k,
    (fixedQuotientRoot relative).lift (((zeta : family.kˣ) : family.k)) =
      family.iota.lift (((zeta : family.kˣ) : family.k))
  quotientWeight_roots : ∀ psi : Definition35Brauer (family.problem block),
    TypeBFixedRootDefinitionFamily.QuotientRootAgreement
      (fixedQuotientRoot relative)
      (quotientRadical (family.problem block) relative.reference
        (relative.omega psi)) (relative.matched psi).weight.iota
  quotientInflation_roots : ∀ psi : Definition35Brauer (family.problem block),
    TypeBFixedRootDefinitionFamily.NormalizerRootAgreement
      (fixedQuotientRoot relative)
      (quotientRadical (family.problem block) relative.reference
        (relative.omega psi)) (relative.matched psi).localInflation.iota
  /-- The extensions and all their restrictions use one root convention
  within each actual ambient group. Function-value equality alone would
  not identify modular blocks under unrelated root lifts. -/
  quotientAmbient_roots : ∀ psi : Definition35Brauer (family.problem block),
    RootLiftAgreement (relative.matched psi).quotient.iota
      (relative.matched psi).extensions.ambientRoot
  localAmbient_roots : ∀ psi : Definition35Brauer (family.problem block),
    RootLiftAgreement (relative.matched psi).extensions.localAmbientRoot
      (relative.matched psi).extensions.ambientRoot
  intermediate_roots : ∀ (psi : Definition35Brauer (family.problem block))
      (J : Subgroup (relative.matched psi).ambient.A)
      (hJ : (relative.matched psi).ambient.base ≤ J),
    RootLiftAgreement
        ((relative.matched psi).intermediateBlocks.equalityAt J hJ).globalRoot
        (relative.matched psi).extensions.ambientRoot ∧
      RootLiftAgreement
        ((relative.matched psi).intermediateBlocks.equalityAt J hJ).localRoot
        (relative.matched psi).extensions.ambientRoot
  quotientBrauerBlock_transport : ∀
      (alpha : (MulAut (QuotientCarrier relative))ᵐᵒᵖ)
      (phi : IBr (fixedQuotientRoot relative)),
    irreducibleBrauerCharacterBlock (fixedQuotientRoot relative)
        (fixedQuotientBrauerInjective relative) relative.quotientBlocks
        (alpha • phi) =
      alpha • irreducibleBrauerCharacterBlock (fixedQuotientRoot relative)
        (fixedQuotientBrauerInjective relative) relative.quotientBlocks phi
  weight_liesInQuotientBlock :
    ∀ psi : Definition35Brauer (family.problem block),
      quotientBlockSource.weightBlock (quotientWeightClass relative psi) =
        relative.quotientBlock
  weight_injective : Function.Injective (quotientWeightClass relative)
  weight_reverse : ∀ w : WeightFibre quotientBlockSource relative.quotientBlock,
    ∃ psi : Definition35Brauer (family.problem block),
      quotientWeightClass relative psi = w.1
  /-- The graph of the already fixed quotient correspondence is invariant
  under the actual quotient automorphisms. Both character arguments belong
  to the same specified quotient block by construction. -/
  quotient_equivariant : ∀
      (alpha : (MulAut (QuotientCarrier relative))ᵐᵒᵖ)
      (psi chi : Definition35Brauer (family.problem block)),
    fixedDescendedBrauer relative roots chi =
        alpha • fixedDescendedBrauer relative roots psi →
      quotientWeightClass relative chi =
        alpha • quotientWeightClass relative psi

attribute [instance] BlockWitness.quotientBlockAction

/-- The complete quotient weight fibre of the same specified block. -/
abbrev QuotientWeightFibre (W : BlockWitness family cover block) :=
  WeightFibre W.quotientBlockSource W.relative.quotientBlock

/-- Restrict the computed weight descent to the complete quotient fibre. -/
def descentToWeightFibre (W : BlockWitness family cover block)
    (psi : Definition35Brauer (family.problem block)) :
    QuotientWeightFibre W :=
  ⟨quotientWeightClass W.relative psi, W.weight_liesInQuotientBlock psi⟩

/-- Both inverse laws follow from the explicit injectivity and complete
reverse fibre clauses of the output, with no new choice of correspondence. -/
def originalEquivQuotientWeight (W : BlockWitness family cover block) :
    Definition35Brauer (family.problem block) ≃ QuotientWeightFibre W :=
  Equiv.ofBijective (descentToWeightFibre W) ⟨by
    intro psi chi h
    exact W.weight_injective (congrArg Subtype.val h), by
    intro w
    obtain ⟨psi, hpsi⟩ := W.weight_reverse w
    exact ⟨psi, Subtype.ext hpsi⟩⟩

/-- The full quotient-block matching uses exactly the two existing descent
maps. It is not another externally supplied equivalence. -/
def quotientEquiv (W : BlockWitness family cover block) :
    FixedQuotientBrauerFibre W.relative ≃ QuotientWeightFibre W :=
  (originalBrauerFibreEquivFixedQuotientBrauerFibre
    W.relative W.roots W.brauerReverse).symm.trans
      (originalEquivQuotientWeight W)

/-- The specified block containing an actual global Brauer character. -/
abbrev brauerBlock (family : Definition35Family.{u} ell)
    (phi : IBr family.iota) : family.Block :=
  irreducibleBrauerCharacterBlock family.iota
    family.irreducibleBrauerInjective family.blocks phi

/-- Regard a character as an element of its own block fibre. -/
def inOwnBlock (family : Definition35Family.{u} ell)
    (phi : IBr family.iota) :
    Definition35Brauer (family.problem (brauerBlock family phi)) :=
  ⟨phi, rfl⟩

/-- The global map is computed from the block maps and the actual block
assignment. It cannot be chosen independently of the matched-pair data. -/
def globalWeight
    (W : ∀ b : family.Block, BlockWitness family cover b)
    (phi : IBr family.iota) :
    CharacterWeight.ConjugacyClass (p := ell) (K := family.K) (G := family.H) :=
  ((W (brauerBlock family phi)).relative.omega (inOwnBlock family phi)).1

/-- Literal radical subgroups, with their radicality proof. -/
abbrev Radical (family : Definition35Family.{u} ell) :=
  {Q : Subgroup family.H // IsRadicalSubgroup ell Q}

/-- The entire ordinary defect-zero character fibre at one radical. -/
abbrev RadicalOrdinary (Q : Radical family) :=
  {chi : OrdinaryIrreducibleCharacter.Irr family.K (NormalizerQuotient Q.1) //
    IsDefectZeroOrdinaryCharacter ell chi}

/-- Actual raw weight determined by the literal radical and its character. -/
def radicalRawWeight (Q : Radical family) (chi : RadicalOrdinary Q) :
    CharacterWeight ell family.K family.H where
  prime := family.ellPrime
  subgroup := Q.1
  radical := Q.2
  localCharacter := chi.1
  defectZero := chi.2

def radicalWeightClass (Q : Radical family) (chi : RadicalOrdinary Q) :
    CharacterWeight.ConjugacyClass (p := ell) (K := family.K) (G := family.H) :=
  Quotient.mk'' (Quotient.mk'' (radicalRawWeight Q chi))

/-- The radical partition is defined by the actual weight-class map. There
is no arbitrary predicate naming which characters belong to a radical. -/
def RadicalBrauerFibre
    (W : ∀ b : family.Block, BlockWitness family cover b) (Q : Radical family) :=
  {phi : IBr family.iota //
    ∃ chi : RadicalOrdinary Q, radicalWeightClass Q chi = globalWeight W phi}

/-- The ordinary character inflated along the actual local quotient map. -/
def inflatedRadicalOrdinary (Q : Radical family) (chi : RadicalOrdinary Q)
    (x : Subgroup.normalizer (Q.1 : Set family.H)) : family.K :=
  chi.1 (QuotientGroup.mk'
    (Q.1.subgroupOf (Subgroup.normalizer (Q.1 : Set family.H))) x)

/-- Literal trivial-radical normalization of the two matched extension
characters. Equality is expressed by pullback along the actual normalizer
inclusion, so no equality of independently selected root records is hidden. -/
def TrivialExtensionNormalization
    (W : RelativeBlockConditionWitness family cover block) : Prop :=
  ∀ psi : Definition35Brauer (family.problem block),
    selectedRadical (family.problem block) (W.omega psi) = ⊥ →
      PrimeRegularClassFunction.pullback
          (AmbientLocalGroup (family.problem block) W.reference psi
            (W.omega psi) (W.matched psi).quotient
            (W.matched psi).ambient).subtype
          (W.matched psi).extensions.globalExtension.1.1 =
        (W.matched psi).extensions.localExtension.1.1

/-- Complete global output on an independently fixed literal family and
cover. Every field is an explicit carrier, map, value equality, or actual
extension/block datum; no `globallyCoherent` or target predicate is accepted.

The source statement must produce this record, not receive it as a Type B
hypothesis. The root-agreement and coefficient field realization needed for
that statement belong to its separate, independently audited domain. -/
structure FamilyWitness
    (family : Definition35Family.{u} ell)
    (cover : EllPrimeCoverSource ell family.H) where
  blocks : ∀ b : family.Block, BlockWitness family cover b
  naturality : ∀ (alpha : (MulAut family.H)ᵐᵒᵖ) (b : family.Block)
      (psi : Definition35Brauer (family.problem b)),
    (blocks (alpha • b)).relative.omega (family.transportBrauer alpha psi) =
      family.transportWeight alpha ((blocks b).relative.omega psi)
  global_bijective : Function.Bijective (globalWeight blocks)
  global_equivariant : ∀ (alpha : (MulAut family.H)ᵐᵒᵖ)
      (phi : IBr family.iota),
    globalWeight blocks (alpha • phi) = alpha • globalWeight blocks phi
  radicalEquiv : ∀ Q : Radical family,
    RadicalBrauerFibre blocks Q ≃ RadicalOrdinary Q
  radical_matches : ∀ (Q : Radical family)
      (phi : RadicalBrauerFibre blocks Q),
    radicalWeightClass Q (radicalEquiv Q phi) = globalWeight blocks phi.1
  /-- The literal transported raw weight determines radical equivariance,
  including transport of its normalizer-quotient ordinary character. -/
  radical_transport : ∀ (Q : Radical family)
      (phi : RadicalBrauerFibre blocks Q) (alpha : MulAut family.H)
      (Q' : Radical family) (phi' : RadicalBrauerFibre blocks Q'),
    Q'.1 = Q.1.comap alpha.toMonoidHom →
    phi'.1 = MulOpposite.op alpha • phi.1 →
    CharacterWeight.Isomorphic
      ((radicalRawWeight Q (radicalEquiv Q phi)).rightTwist alpha)
      (radicalRawWeight Q' (radicalEquiv Q' phi'))
  /-- Equality of central scalar characters, expressed directly on values
  after inflation. Central elements of a prime-to-ell centre are regular;
  retaining the actual regular argument avoids an unstated lifting map. -/
  central_values : ∀ (Q : Radical family)
      (phi : RadicalBrauerFibre blocks Q)
      (z : PrimeRegularElement
        (G := Subgroup.normalizer (Q.1 : Set family.H)) ell),
    z.1.1 ∈ Subgroup.center family.H →
    inflatedRadicalOrdinary Q (radicalEquiv Q phi) z.1 *
        phi.1.1 ⟨1, isPrimeRegular_one⟩ =
      inflatedRadicalOrdinary Q (radicalEquiv Q phi) 1 *
        (PrimeRegularClassFunction.pullback
          (Subgroup.normalizer (Q.1 : Set family.H)).subtype phi.1.1) z
  /-- Spath 4.1(iv): at the trivial radical the ordinary character reduces
  to the original Brauer character, on the actual normalizer inclusion. -/
  trivial_reduction : ∀ (Q : Radical family)
      (phi : RadicalBrauerFibre blocks Q), Q.1 = ⊥ →
    ∀ x : PrimeRegularElement
        (G := Subgroup.normalizer (Q.1 : Set family.H)) ell,
      inflatedRadicalOrdinary Q (radicalEquiv Q phi) x.1 =
        (PrimeRegularClassFunction.pullback
          (Subgroup.normalizer (Q.1 : Set family.H)).subtype phi.1.1) x
  trivial_extensions : ∀ b : family.Block,
    TrivialExtensionNormalization (blocks b).relative

end ModularRep.PaperProofs.TypeBFullBlockCondition


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
