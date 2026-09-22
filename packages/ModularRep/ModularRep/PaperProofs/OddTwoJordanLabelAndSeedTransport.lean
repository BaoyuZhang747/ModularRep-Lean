import ModularRep.OddQuasiIsolation
import ModularRep.StrictQuasiIsolation
import ModularRep.PaperProofs.OddTwoPrincipalBlockMovingWindow
import ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# Guarded labels and transport of a named principal symplectic seed

This moving window checks three small joins needed by the odd-field type-C
Jordan argument.  It does not replace the source class `H_G`, apply FLZ
Theorem 5.7, or assert all-block BAW-goodness.

* The label argument retains semisimplicity as a premise on the selected
  element of its ambient dual group.  It never asserts that every element
  of a special-orthogonal group is semisimple.  The dual group can vary
  between calls, as it must for different pairs in `H_G`.
* The rank argument sends rank one through the supplied type-A fact and
  retains rank at least two in every remaining type-C branch.
* The principal seed is the existing named construction
  `PrincipalSpMapSource.toDefinition35IBAWBijection`, followed by the
  existing `Definition35ForwardTransport.map`.  The source problem is tied
  by an actual group equivalence to `Sp_(2r)(F)`, with `r >= 2`, finite odd
  `F`, and coefficient prime two.  Its block contains a Brauer character
  whose literal values are all one.  Prime, group, coefficient field,
  Brauer-value, and automorphism compatibility are retained during
  transport; in particular, the target block's constant-one character is
  derived rather than supplied as a new principal-block assertion.

The group, character, action, and relation maps remain explicit source
bindings.  This file constructs none of those bindings.  In particular,
`PrincipalSpDefinition35LocalSource.blockIsomorphism_at` and the forward
Definition 3.5 relation remain U/E2; transporting them does not prove them.
There is no source-clean principal seed, literal FLZ instance, projective
descent, or manuscript verification claim here.

Source locators: Bonnafe, Proposition 4.11(a), Section 4.E, pp. 2330--2331,
requires the odd-characteristic special-orthogonal and semisimple setting;
FLZ, Definition 3.5, p. 10, fixes the equivariant map and matched modular
character-triple relation; FLZ, Remark 5.8, p. 34, is restricted to simple
`PSp_(2n)(q)` with odd `q`, `Sp_(2n)(q)`, and the type-A reduction.  That
remark is not invoked in this file.  The rank inputs are
`SF-RANK-ONE-ROOT` (Malle--Testerman, Theorem 9.6) and `SF-C-SUBDIAGRAMS`
(Table 9.1 and the definition before Theorem 9.6).  The finite symplectic
carrier uses `SF-C-ODD-FORMS` and `SF-FIXED-CLASSICAL`; their source
interpretation and the appropriate covering hypotheses are separate.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport

open ModularRep
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.OddTwoPrincipalBlockMovingWindow
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Transport
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u v w

/-! ## A semisimple-guarded pointwise label deduction -/

/-- The strictly quasi-isolated, semisimple, two-regular label is one.

The square implication must be supplied on the actual dual-group carrier
with its source scope established separately.  In contrast to an
unconditional square predicate on the whole ambient group, this argument
passes the selected label's semisimplicity proof to that implication.
Centraliser and proper-Levi interpretations remain explicit E1/U inputs. -/
theorem semisimple_strictlyQuasiIsolated_label_eq_one
    {Dual : Type*} [Group Dual]
    {label : Dual}
    (IsSemisimple : Dual → Prop)
    (IsProperLevi : Set Dual → Prop)
    (finiteCentralizer connectedCentralizer : Subgroup Dual)
    (finiteCentralizer_le :
      finiteCentralizer ≤ Subgroup.centralizer {label})
    (connectedCentralizer_le :
      connectedCentralizer ≤ Subgroup.centralizer {label})
    (semisimple : IsSemisimple label)
    (twoRegular : IsPrimeRegular 2 label)
    (strict : NotContainedInProperLevi
      ((finiteCentralizer : Set Dual) *
        (connectedCentralizer : Set Dual)) IsProperLevi)
    (squareOfSemisimpleQuasiIsolated : ∀ s : Dual,
      IsSemisimple s →
        NotContainedInProperLevi
          (Subgroup.centralizer {s} : Set Dual) IsProperLevi →
        s ^ 2 = 1) :
    label = 1 := by
  have quasi : NotContainedInProperLevi
      (Subgroup.centralizer {label} : Set Dual) IsProperLevi :=
    quasiIsolated_of_strictlyQuasiIsolated
      finiteCentralizer_le connectedCentralizer_le strict
  exact twoRegular.eq_one_of_sq_eq_one
    (squareOfSemisimpleQuasiIsolated label semisimple quasi)

/-- The same pointwise deduction when the literal label's order is supplied
as an odd natural number.  Conversion to two-regularity is K. -/
theorem semisimple_strictlyQuasiIsolated_oddOrder_label_eq_one
    {Dual : Type*} [Group Dual]
    {label : Dual}
    (IsSemisimple : Dual → Prop)
    (IsProperLevi : Set Dual → Prop)
    (finiteCentralizer connectedCentralizer : Subgroup Dual)
    (finiteCentralizer_le :
      finiteCentralizer ≤ Subgroup.centralizer {label})
    (connectedCentralizer_le :
      connectedCentralizer ≤ Subgroup.centralizer {label})
    (semisimple : IsSemisimple label)
    (oddOrder : Odd (orderOf label))
    (strict : NotContainedInProperLevi
      ((finiteCentralizer : Set Dual) *
        (connectedCentralizer : Set Dual)) IsProperLevi)
    (squareOfSemisimpleQuasiIsolated : ∀ s : Dual,
      IsSemisimple s →
        NotContainedInProperLevi
          (Subgroup.centralizer {s} : Set Dual) IsProperLevi →
        s ^ 2 = 1) :
    label = 1 :=
  semisimple_strictlyQuasiIsolated_label_eq_one
    IsSemisimple IsProperLevi finiteCentralizer connectedCentralizer
    finiteCentralizer_le connectedCentralizer_le semisimple
    oddOrder.coprime_two_right strict squareOfSemisimpleQuasiIsolated

/-! ## The rank-one route is type A -/

/-- A positive connected-subdiagram rank is one or at least two. -/
theorem rank_one_or_rankAtLeastTwo {rank : ℕ} (positive : 0 < rank) :
    rank = 1 ∨ 2 ≤ rank := by
  by_cases one : rank = 1
  · exact Or.inl one
  · exact Or.inr ((Nat.two_le_iff rank).mpr ⟨Nat.ne_of_gt positive, one⟩)

/-- Combine the supplied diagram classification with the rank-one root
classification.  No type-C branch of the result has rank one.

`rankOneIsTypeA` is the exact E1 input `SF-RANK-ONE-ROOT`; the alternative is
the supplied connected-subdiagram classification.  Neither input concerns
blocks, character correspondences, or an iBAW conclusion. -/
theorem typeA_or_typeC_rankAtLeastTwo
    {rank : ℕ} {IsTypeA IsTypeC : Prop}
    (positive : 0 < rank)
    (rankOneIsTypeA : rank = 1 → IsTypeA)
    (typeAlternative : IsTypeA ∨ IsTypeC) :
    IsTypeA ∨ (IsTypeC ∧ 2 ≤ rank) := by
  rcases rank_one_or_rankAtLeastTwo positive with one | atLeastTwo
  · exact Or.inl (rankOneIsTypeA one)
  · rcases typeAlternative with typeA | typeC
    · exact Or.inl typeA
    · exact Or.inr ⟨typeC, atLeastTwo⟩

/-! ## Literal principal-carrier information -/

/-- Source-facing identification of one fixed Definition 3.5 principal
problem with the actual odd finite symplectic matrix carrier.

The principal character is an element of the problem's literal block fibre;
its values, rather than a selectable principal-block predicate, identify it
with the trivial Brauer character.  This structure supplies no bijection or
character-triple relation.  The matrix equivalence, field, and rank do not
identify the published FYZ/Feng--Malle local factors or actions by themselves.
-/
structure OddSymplecticPrincipalCarrier
    (P : Definition35Problem.{u})
    (rank : ℕ) (F : Type w) [Field F] [Fintype F] where
  rankAtLeastTwo : 2 ≤ rank
  fieldOdd : Odd (Fintype.card F)
  coefficientTwo : P.p = 2
  symplecticEquiv : P.H ≃* Matrix.symplecticGroup (Fin rank) F
  principalCharacter : Definition35Brauer P
  principalCharacter_value_one :
    ∀ x : PrimeRegularElement (G := P.H) P.p,
      principalCharacter.1.1 x = 1

/-- Membership of the constant-one Brauer character names the principal
block through the literal block operation already fixed by `P`. -/
theorem OddSymplecticPrincipalCarrier.block_eq_blockOf_principalCharacter
    {P : Definition35Problem.{u}}
    {rank : ℕ} {F : Type w} [Field F] [Fintype F]
    (C : OddSymplecticPrincipalCarrier P rank F) :
    P.block = FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock
      P.iota P.irreducibleBrauerInjective P.blocks C.principalCharacter.1 :=
  C.principalCharacter.2.symm

/-- An actual group equivalence and equality of coefficient primes induce
an equivalence of the literal prime regular element carriers. -/
def primeRegularElementEquiv
    {H : Type u} {J : Type v} [Group H] [Group J]
    {p q : ℕ} (e : H ≃* J) (prime_eq : p = q) :
    PrimeRegularElement (G := H) p ≃ PrimeRegularElement (G := J) q where
  toFun x := ⟨e x.1, by
    rw [← prime_eq]
    exact x.2.map e.toMonoidHom⟩
  invFun x := ⟨e.symm x.1, by
    rw [prime_eq]
    exact x.2.map e.symm.toMonoidHom⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x.1

/-- Source-facing maps on the selected actual weight pairs.

The target representative is chosen to be compatible with the source
representative under `groupEquiv`; it need not be the independently chosen
representative returned by `selectedCharacterWeight` on the target side.
Its class is required to be the precise target of `weightEquiv`.

The normaliser and quotient maps commute with the ambient group map and
the literal quotient maps.  The local-character equation concerns only the
selected irreducible ordinary characters, with their actual value fields.
Radicality and defect zero are already fields of each `CharacterWeight`.
These are E1/U carrier and character identifications, not a theorem that
every source provides them and not a modular-character-triple assertion.
-/
structure SelectedWeightTransport
    (P : Definition35Problem.{u}) (Q : Definition35Problem.{v})
    (groupEquiv : P.H ≃* Q.H)
    (coefficientFieldEquiv : P.K ≃+* Q.K)
    (weightEquiv : Definition35Weight P ≃ Definition35Weight Q) where
  targetRepresentative : Definition35Weight P → CharacterWeight Q.p Q.K Q.H
  target_class : ∀ w : Definition35Weight P,
    (Quotient.mk'' (Quotient.mk'' (targetRepresentative w)) :
      CharacterWeight.ConjugacyClass (p := Q.p) (K := Q.K) (G := Q.H)) =
        (weightEquiv w).1
  subgroup_map : ∀ w : Definition35Weight P,
    (targetRepresentative w).subgroup =
      (selectedCharacterWeight P.blockSource P.block w).subgroup.map
        groupEquiv.toMonoidHom
  normalizerEquiv : ∀ w : Definition35Weight P,
    Subgroup.normalizer
        ((selectedCharacterWeight P.blockSource P.block w).subgroup : Set P.H) ≃*
      Subgroup.normalizer ((targetRepresentative w).subgroup : Set Q.H)
  normalizer_coe : ∀ (w : Definition35Weight P)
      (x : Subgroup.normalizer
        ((selectedCharacterWeight P.blockSource P.block w).subgroup : Set P.H)),
    (normalizerEquiv w x : Q.H) = groupEquiv (x : P.H)
  quotientEquiv : ∀ w : Definition35Weight P,
    NormalizerQuotient
        (selectedCharacterWeight P.blockSource P.block w).subgroup ≃*
      NormalizerQuotient (targetRepresentative w).subgroup
  quotient_mk : ∀ (w : Definition35Weight P)
      (x : Subgroup.normalizer
        ((selectedCharacterWeight P.blockSource P.block w).subgroup : Set P.H)),
    quotientEquiv w (QuotientGroup.mk x) =
      QuotientGroup.mk (normalizerEquiv w x)
  localCharacter_values : ∀ (w : Definition35Weight P)
      (x : NormalizerQuotient
        (selectedCharacterWeight P.blockSource P.block w).subgroup),
    (targetRepresentative w).localCharacter (quotientEquiv w x) =
      coefficientFieldEquiv
        ((selectedCharacterWeight P.blockSource P.block w).localCharacter x)

/-- The compatible target representative belongs to the actual target
block.  This is a consequence of its class equation and the literal fibre
membership, so no extra block-membership field is required. -/
theorem SelectedWeightTransport.targetRepresentative_block
    {P : Definition35Problem.{u}} {Q : Definition35Problem.{v}}
    {groupEquiv : P.H ≃* Q.H}
    {coefficientFieldEquiv : P.K ≃+* Q.K}
    {weightEquiv : Definition35Weight P ≃ Definition35Weight Q}
    (T : SelectedWeightTransport P Q groupEquiv coefficientFieldEquiv weightEquiv)
    (w : Definition35Weight P) :
    Q.blockSource.operations.rawWeightBlock (T.targetRepresentative w) = Q.block := by
  have member := (weightEquiv w).2
  rw [← T.target_class w] at member
  exact member

/-- The compatible target representative's actual local block induces to
the target block.  This follows from the fixed local block operations and
the derived membership equation; it is not an additional transport field.
-/
theorem SelectedWeightTransport.targetRepresentative_blockInducesTo
    {P : Definition35Problem.{u}} {Q : Definition35Problem.{v}}
    {groupEquiv : P.H ≃* Q.H}
    {coefficientFieldEquiv : P.K ≃+* Q.K}
    {weightEquiv : Definition35Weight P ≃ Definition35Weight Q}
    (T : SelectedWeightTransport P Q groupEquiv coefficientFieldEquiv weightEquiv)
    (w : Definition35Weight P) :
    let W := T.targetRepresentative w
    let O := Q.blockSource.operations
    let localData := O.inflatedNormalizerBlockData W.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo
      (Subgroup.normalizer (W.subgroup : Set Q.H))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
      Q.block := by
  let W := T.targetRepresentative w
  let O := Q.blockSource.operations
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI := O.ambientBlockData.fintypeBlock
  letI := localData.fintypeBlock
  have inducedBlock_eq : O.induceToAmbient W = Q.block :=
    T.targetRepresentative_block w
  change BlockInducesTo
    (Subgroup.normalizer (W.subgroup : Set Q.H))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    Q.block
  rw [← inducedBlock_eq]
  exact inducedBlock_spec
    (Subgroup.normalizer (W.subgroup : Set Q.H))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (O.blockInductionDefined W)

/-- Additional literal carrier bindings around the existing full
Definition 3.5 transport.

`brauer_values` ties the supplied fibre equivalence to the actual finite
group and coefficient field maps.  It forces the source constant-one
character to transport to the target constant-one character.  The target
and source block memberships are already part of the two fibre types.
`gamma_compatible` ties the group equivalence to the same acting-group map
used by the Brauer and weight naturality fields of `transport`.
`selectedWeights` ties that weight map to actual subgroup, normaliser,
quotient, and selected local-character maps under the same group and
coefficient field equivalences.

The weight equivalence, its action naturality, and the forward
modular-character-triple relation remain the explicit fields of
`Definition35ForwardTransport`.  No new principal iBAW result is assumed.
-/
structure PrincipalSeedCarrierTransport
    (P : Definition35Problem.{u})
    (Paut : Definition35AutomorphismStabilizerAdapter P)
    (Psource : FLZSourceSemantics P Paut)
    (Q : Definition35Problem.{v})
    (Qaut : Definition35AutomorphismStabilizerAdapter Q)
    (Qsource : FLZSourceSemantics Q Qaut)
    (rank : ℕ) (F : Type w) [Field F] [Fintype F] where
  sourceCarrier : OddSymplecticPrincipalCarrier P rank F
  transport : Definition35ForwardTransport P Paut Psource Q Qaut Qsource
  groupEquiv : P.H ≃* Q.H
  coefficientPrime_eq : P.p = Q.p
  coefficientFieldEquiv : P.K ≃+* Q.K
  selectedWeights : SelectedWeightTransport P Q groupEquiv
    coefficientFieldEquiv transport.weightEquiv
  brauer_values : ∀ (psi : Definition35Brauer P)
      (x : PrimeRegularElement (G := P.H) P.p),
    (transport.brauerEquiv psi).1.1
        (primeRegularElementEquiv groupEquiv coefficientPrime_eq x) =
      coefficientFieldEquiv (psi.1.1 x)
  gamma_compatible : ∀ (a : P.Gamma) (g : P.H),
    groupEquiv (P.gamma a g) =
      Q.gamma (transport.gammaEquiv a) (groupEquiv g)

namespace PrincipalSeedCarrierTransport

variable {P : Definition35Problem.{u}}
variable {Paut : Definition35AutomorphismStabilizerAdapter P}
variable {Psource : FLZSourceSemantics P Paut}
variable {Q : Definition35Problem.{v}}
variable {Qaut : Definition35AutomorphismStabilizerAdapter Q}
variable {Qsource : FLZSourceSemantics Q Qaut}
variable {rank : ℕ} {F : Type w} [Field F] [Fintype F]

/-- Derive the target principal-block identification on the same actual
symplectic matrix model.  Both the target constant-one character and its
block membership follow from the supplied fibre map and value equation. -/
def targetCarrier
    (T : PrincipalSeedCarrierTransport
      P Paut Psource Q Qaut Qsource rank F) :
    OddSymplecticPrincipalCarrier Q rank F where
  rankAtLeastTwo := T.sourceCarrier.rankAtLeastTwo
  fieldOdd := T.sourceCarrier.fieldOdd
  coefficientTwo := T.coefficientPrime_eq.symm.trans
    T.sourceCarrier.coefficientTwo
  symplecticEquiv := T.groupEquiv.symm.trans T.sourceCarrier.symplecticEquiv
  principalCharacter :=
    T.transport.brauerEquiv T.sourceCarrier.principalCharacter
  principalCharacter_value_one := by
    intro x
    rcases (primeRegularElementEquiv T.groupEquiv
      T.coefficientPrime_eq).surjective x with ⟨y, rfl⟩
    rw [T.brauer_values, T.sourceCarrier.principalCharacter_value_one, map_one]

/-- Transport the named principal symplectic seed, including its exact
Definition 3.5(ii) relation, to the fixed target block problem.

The pointwise `Local` relation is still an explicit U/E2 input.  This
definition merely packages that named seed and applies the established
full Definition 3.5 transport in the forward direction. -/
def principalSeed
    (T : PrincipalSeedCarrierTransport
      P Paut Psource Q Qaut Qsource rank F)
    {ULabel TLabel : Type u}
    {fieldAutomorphisms diagonalAutomorphisms : Subgroup P.Gamma}
    {isUOne : ULabel → Prop} {isTOne : TLabel → Prop}
    (Map : PrincipalSpMapSource P Paut fieldAutomorphisms
      diagonalAutomorphisms isUOne isTOne)
    (Local : PrincipalSpDefinition35LocalSource P Paut Psource Map) :
    Definition35IBAWBijection Q Qaut Qsource :=
  T.transport.map
    (PrincipalSpMapSource.toDefinition35IBAWBijection P Map Local)

/-- The transported map is the named seed conjugated by the supplied
equivalences on Brauer characters and weights. -/
theorem principalSeed_omega_apply
    (T : PrincipalSeedCarrierTransport
      P Paut Psource Q Qaut Qsource rank F)
    {ULabel TLabel : Type u}
    {fieldAutomorphisms diagonalAutomorphisms : Subgroup P.Gamma}
    {isUOne : ULabel → Prop} {isTOne : TLabel → Prop}
    (Map : PrincipalSpMapSource P Paut fieldAutomorphisms
      diagonalAutomorphisms isUOne isTOne)
    (Local : PrincipalSpDefinition35LocalSource P Paut Psource Map)
    (psi : Definition35Brauer Q) :
    (T.principalSeed Map Local).omega psi =
      T.transport.weightEquiv
        (Map.omega (T.transport.brauerEquiv.symm psi)) :=
  rfl

end PrincipalSeedCarrierTransport

/-! ## The exact intrinsic Feng--Malle principal construction -/

namespace IntrinsicPrincipalSeed

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)
variable (FM : D.FengMalleTheorem62LiteralCertificate)

/-- Construct the principal-carrier binding from the actual intrinsic
problem.  The group equivalence and coefficient-prime equality are
identities; the block is definitionally the block of `D.trivialCharacter`.
The rank and odd field hypotheses are the same ones carried by the exact
intrinsic Feng--Malle certificate. -/
def principalCarrier :
    OddSymplecticPrincipalCarrier (D.problem reduction) n F where
  rankAtLeastTwo := FM.rank_ge_two
  fieldOdd := by
    simpa only [Nat.card_eq_fintype_card] using FM.odd_field
  coefficientTwo := rfl
  symplecticEquiv := MulEquiv.refl _
  principalCharacter := ⟨D.trivialCharacter, rfl⟩
  principalCharacter_value_one := D.trivial_value

variable (source : FLZSourceSemantics
  (D.problem reduction) (D.automorphisms reduction))
variable {Q : Definition35Problem.{v}}
variable {Qaut : Definition35AutomorphismStabilizerAdapter Q}
variable {Qsource : FLZSourceSemantics Q Qaut}

/-- Replace the source carrier component by the one constructed directly
from `D` and `FM`.  All actual group, character, weight, and action maps are
the supplied maps; their source problem is already the literal intrinsic
problem `D.problem reduction`. -/
def transportWithIntrinsicCarrier
    (T : PrincipalSeedCarrierTransport
      (D.problem reduction) (D.automorphisms reduction) source
      Q Qaut Qsource n F) :
    PrincipalSeedCarrierTransport
      (D.problem reduction) (D.automorphisms reduction) source
      Q Qaut Qsource n F :=
  { T with sourceCarrier := principalCarrier D reduction FM }

/-- Forward transport of the exact intrinsic Feng--Malle principal seed.

The map is `D.definition35Seed`, not an independently supplied
`PrincipalSpMapSource`.  The precise pointwise modular-character-triple
relation remains explicit.  The transport requires selected actual weight
maps as well as the Brauer, group, and action compatibilities; no source
instance or Hypothesis 5.5 is concluded here. -/
def seed
    (T : PrincipalSeedCarrierTransport
      (D.problem reduction) (D.automorphisms reduction) source
      Q Qaut Qsource n F)
    (localTriple : ∀ psi : Definition35Brauer (D.problem reduction),
      source.definition35BlockIsomorphic psi
        (D.definition35Equiv reduction FM psi)) :
    Definition35IBAWBijection Q Qaut Qsource :=
  (transportWithIntrinsicCarrier D reduction FM source T).transport.map
    (D.definition35Seed reduction FM source localTriple)

/-- The resulting map is the same literal intrinsic map conjugated by the
fixed fibre equivalences.  The local-triple proof cannot select a different
correspondence. -/
theorem seed_omega_apply
    (T : PrincipalSeedCarrierTransport
      (D.problem reduction) (D.automorphisms reduction) source
      Q Qaut Qsource n F)
    (localTriple : ∀ psi : Definition35Brauer (D.problem reduction),
      source.definition35BlockIsomorphic psi
        (D.definition35Equiv reduction FM psi))
    (psi : Definition35Brauer Q) :
    (seed D reduction FM source T localTriple).omega psi =
      T.transport.weightEquiv
        (FM.omega (T.transport.brauerEquiv.symm psi)) :=
  rfl

end IntrinsicPrincipalSeed

end ModularRep.PaperProofs.OddTwoJordanLabelAndSeedTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
