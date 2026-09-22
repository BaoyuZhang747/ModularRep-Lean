import ModularRep.PaperProofs.EvenFieldAssumption53Actual
import ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

/-!
# Source-shaped conditions for the even-field Jordan reduction

This module introduces fixed carriers for the source statements used in the
even-field proof of Proposition 3.9.  It mirrors Feng--Li--Zhang, Definition
3.5, equation (3.17), Assumption 5.3, the class `H_G`, and Hypothesis 5.5.
It does not apply Feng--Li--Zhang, Theorem 3.18 or Theorem 5.7 and contains no
BAW-good or iBAW conclusion for a manuscript group.

The project does not yet formalise Spath's block-isomorphism relation for
modular character triples.  Its occurrence in Definition 3.5 is therefore
isolated in the cover-free structure `FLZSourceSemantics`.  The stronger
quotient-and-lift relation in equation (3.17) is isolated separately in
`Equation317SourceSemantics` and is indexed by one concrete universal
prime-to-`ell` cover.  Both are U/E2 semantic interfaces supplied by the
caller, not caller-selected conclusion predicates.  No declaration in this
file eliminates either relation into an unrelated proposition.

The Assumption 5.3 carrier is different: its orbit, stabiliser, and extension
fields use the literal carriers already present in the project.  The final
adapter is a kernel-checked construction from `EvenFieldAssumption53Actual`.
Its extension is over the project's literal embedded stabiliser.  Identifying
the concrete factors `C` and `FieldGroup a`, and that embedded subgroup, with
Feng--Li--Zhang's regular overgroup, group `A`, and stabiliser remains E1/U.

The legacy relative Hypothesis 5.5 package is not retained.  Its full-family
formulation lives downstream in `EvenFieldFLZFullHG`, where Definition 3.5
is stated directly for the arbitrary fixed-point groups occurring in
Hypothesis 5.5(b).  A universal prime-to-`ell` cover is introduced only in
the separate equation-(3.17) lane and at the final ambient applicability
gate.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZSourceConditions

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldAssumption53Actual
open ModularRep.PaperProofs.EvenFieldConcreteTypeC

universe u

/-! ## A concrete universal prime-to-`ell` cover -/

/-- Literal source data saying that `H` is the maximal perfect central
prime-to-`ell` cover of a finite nonabelian simple group.

The final field expresses maximality in Brough--Spath, Definition 3.1:
every other finite perfect central extension by an `ell'`-group is a quotient
of `H` over the fixed simple group.  The structure is generic in `ell` and
`H`, so the equation-(3.17) relation and the final ambient applicability
gates can be indexed by an exact cover before any block family or individual
block is selected. -/
structure EllPrimeCoverSource (ell : ℕ) (H : Type u)
    [Group H] [Fintype H] where
  S : Type u
  [groupS : Group S]
  [fintypeS : Fintype S]
  quotient : H →* S
  quotient_surjective : Function.Surjective quotient
  quotient_kernel : quotient.ker = Subgroup.center H
  perfect : commutator H = ⊤
  simple : IsSimpleGroup S
  nonabelian : ¬ IsMulCommutative S
  centerPrimeTo : ¬ ell ∣ Nat.card (Subgroup.center H)
  maximal : ∀ (D : Type u) [Group D] [Fintype D] (f : D →* S),
    Function.Surjective f →
      f.ker ≤ Subgroup.center D →
      commutator D = ⊤ →
      ¬ ell ∣ Nat.card f.ker →
      ∃ lift : H →* D,
        Function.Surjective lift ∧ f.comp lift = quotient

attribute [instance]
  EllPrimeCoverSource.groupS EllPrimeCoverSource.fintypeS

/-! ## Literal data for Feng--Li--Zhang, Definition 3.5 -/

/-- A bundled literal block problem on which the source definition can be
stated.  `Gamma` acts through actual automorphisms of `H`; its identification
with `Aut(H)_block` is kept in the separate source adapter below.

The chosen local reduction is part of the literal weight data because the
local member of the modular character triple is the Brauer reduction of the
defect-zero ordinary character. -/
structure Definition35Problem where
  p : ℕ
  k : Type u
  K : Type u
  H : Type u
  Gamma : Type u
  Block : Type u
  [fieldk : Field k]
  [fieldK : Field K]
  [charPk : CharP k p]
  [algClosedk : IsAlgClosed k]
  [charZeroK : CharZero K]
  [groupH : Group H]
  [fintypeH : Fintype H]
  [groupGamma : Group Gamma]
  [finiteGamma : Finite Gamma]
  [fintypeBlock : Fintype Block]
  [blockAction : MulAction (MulAut H)ᵐᵒᵖ Block]
  blockIdempotent : Block → k[H]
  iota : PrimeRegularRootEmbedding p k K H
  irreducibleBrauerInjective : IrreducibleBrauerCharacterInjectivity iota
  blocks : BlockIdempotentDecomposition blockIdempotent
  blockSource : LocalBlockInductionSource
    (p := p) (k := k) (K := K) (G := H) (Block := Block)
  block : Block
  gamma : Gamma →* MulAut H
  gammaBlock_fixed : ∀ a : Gamma, inverseOpHom gamma a • block = block
  brauerBlock_transport : ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
    irreducibleBrauerCharacterBlock iota irreducibleBrauerInjective blocks
        (alpha • psi) =
      alpha • irreducibleBrauerCharacterBlock iota
        irreducibleBrauerInjective blocks psi
  localReduction : ∀ w : LiteralWeightFibre blockSource block,
    SelectedLocalReductionSource blockSource block w

attribute [instance]
  Definition35Problem.fieldk Definition35Problem.fieldK
  Definition35Problem.charPk Definition35Problem.algClosedk
  Definition35Problem.charZeroK Definition35Problem.groupH
  Definition35Problem.fintypeH Definition35Problem.groupGamma
  Definition35Problem.finiteGamma Definition35Problem.fintypeBlock
  Definition35Problem.blockAction

/-- Automorphism transport of Brauer support for the exact ambient block
catalogue stored in local block-induction operations. -/
def OperationsBrauerSupport
    {p : ℕ} {k K H Block : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group H] [Fintype H]
    [MulAction (MulAut H)ᵐᵒᵖ Block]
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (operations : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := H) (Block := Block)) : Prop :=
  let O := operations
  letI : Fintype Block := O.ambientBlockData.fintypeBlock
  ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
    irreducibleBrauerCharacterBlock iota hinj
        O.ambientBlockData.blocks (alpha • psi) =
      alpha • irreducibleBrauerCharacterBlock iota hinj
        O.ambientBlockData.blocks psi

namespace Definition35Problem

/-- Construct a Definition 3.5 problem using the exact finite set of blocks,
idempotent family, and decomposition stored in the local block-induction
operations. -/
def ofOperations
    {p : ℕ} {k K H Gamma Block : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group H] [Fintype H]
    [Group Gamma] [Finite Gamma]
    [MulAction (MulAut H)ᵐᵒᵖ Block]
    (iota : PrimeRegularRootEmbedding p k K H)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blockSource : LocalBlockInductionSource
      (p := p) (k := k) (K := K) (G := H) (Block := Block))
    (block : Block)
    (gamma : Gamma →* MulAut H)
    (gammaBlock_fixed : ∀ a : Gamma,
      inverseOpHom gamma a • block = block)
    (brauerSupport :
      OperationsBrauerSupport iota hinj blockSource.operations)
    (localReduction : ∀ w : LiteralWeightFibre blockSource block,
      SelectedLocalReductionSource blockSource block w) :
    Definition35Problem := by
  let O := blockSource.operations
  letI : Fintype Block := O.ambientBlockData.fintypeBlock
  have hbrauer :
      ∀ (alpha : (MulAut H)ᵐᵒᵖ) (psi : IBr iota),
        irreducibleBrauerCharacterBlock iota hinj
            O.ambientBlockData.blocks (alpha • psi) =
          alpha • irreducibleBrauerCharacterBlock iota hinj
            O.ambientBlockData.blocks psi := by
    simpa only [OperationsBrauerSupport] using brauerSupport
  exact {
    p := p
    k := k
    K := K
    H := H
    Gamma := Gamma
    Block := Block
    fintypeBlock := O.ambientBlockData.fintypeBlock
    blockIdempotent := O.ambientBlockData.blockIdempotent
    iota := iota
    irreducibleBrauerInjective := hinj
    blocks := O.ambientBlockData.blocks
    blockSource := blockSource
    block := block
    gamma := gamma
    gammaBlock_fixed := gammaBlock_fixed
    brauerBlock_transport := hbrauer
    localReduction := localReduction
  }

section OperationsProjections

variable {p : ℕ} {k K H Gamma Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H]
variable [Group Gamma] [Finite Gamma]
variable [MulAction (MulAut H)ᵐᵒᵖ Block]
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := Block))
variable (block : Block)
variable (gamma : Gamma →* MulAut H)
variable (gammaBlock_fixed : ∀ a : Gamma,
  inverseOpHom gamma a • block = block)
variable (brauerSupport :
  OperationsBrauerSupport iota hinj blockSource.operations)
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

@[simp] theorem ofOperations_p :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).p = p := rfl
@[simp] theorem ofOperations_k :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).k = k := rfl
@[simp] theorem ofOperations_K :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).K = K := rfl
@[simp] theorem ofOperations_H :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).H = H := rfl
@[simp] theorem ofOperations_Gamma :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).Gamma = Gamma := rfl
@[simp] theorem ofOperations_Block :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).Block = Block := rfl

@[simp] theorem ofOperations_blockIdempotent :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).blockIdempotent =
      blockSource.operations.ambientBlockData.blockIdempotent := rfl

@[simp] theorem ofOperations_iota :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).iota = iota := rfl

@[simp] theorem ofOperations_irreducibleBrauerInjective :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).irreducibleBrauerInjective = hinj := rfl

@[simp] theorem ofOperations_blocks :
    letI : Fintype Block :=
      blockSource.operations.ambientBlockData.fintypeBlock
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).blocks =
      blockSource.operations.ambientBlockData.blocks := by
  rfl

@[simp] theorem ofOperations_blockSource :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).blockSource = blockSource := rfl

@[simp] theorem ofOperations_block :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).block = block := rfl
@[simp] theorem ofOperations_gamma :
    (ofOperations iota hinj blockSource block gamma gammaBlock_fixed
      brauerSupport localReduction).gamma = gamma := rfl

end OperationsProjections

end Definition35Problem

/-- The literal irreducible-Brauer-character fibre of the selected block. -/
abbrev Definition35Brauer (P : Definition35Problem) :=
  BrauerFibre P.iota P.irreducibleBrauerInjective P.blocks P.block

/-- The literal Alperin-weight fibre of the selected block, where block
membership is defined by local block induction. -/
abbrev Definition35Weight (P : Definition35Problem) :=
  WeightFibre P.blockSource P.block

/-- The canonical action of the proposed source automorphism stabiliser on
the literal Brauer block fibre. -/
@[instance_reducible]
def definition35BrauerAction (P : Definition35Problem) :
    MulAction P.Gamma (Definition35Brauer P) :=
  rightIBrBlockMulAction P.iota P.irreducibleBrauerInjective P.blocks
    P.gamma P.block P.gammaBlock_fixed P.brauerBlock_transport

/-- The canonical action of the same group on the literal weight fibre. -/
@[instance_reducible]
def definition35WeightAction (P : Definition35Problem) :
    MulAction P.Gamma (Definition35Weight P) :=
  rightWeightFibreMulAction P.gamma P.blockSource P.block
    P.gammaBlock_fixed

/-- U adapter identifying the acting group with the literal stabiliser of
the block in `Aut(H)`.  This is the source equality
`Gamma = Aut(H)_B` in Feng--Li--Zhang, Definition 3.5, p. 10.  The arbitrary
presentation `Gamma` is used only through this actual equivalence and its
exact coercion formula; this adapter is the extra U layer between it and the
canonical stabiliser subtype. -/
structure Definition35AutomorphismStabilizerAdapter
    (P : Definition35Problem) where
  equiv : P.Gamma ≃*
    MulAction.stabilizer (MulAut P.H)ᵐᵒᵖ P.block
  equiv_coe : ∀ a : P.Gamma,
    (equiv a : (MulAut P.H)ᵐᵒᵖ) = inverseOpHom P.gamma a

/-- The exact Definition 3.5(ii) source relation that is not yet represented
internally.

This is the relation
`(H ⋊ Gamma_psi,H,psi) >=_b ((H ⋊ Gamma)_(Q,phi),N_H(Q),phi^0)`
in Feng--Li--Zhang, Definition 3.5(ii), p. 10.  It is indexed by the literal
matched objects and the source automorphism-stabiliser adapter.  Definition
3.5 applies to arbitrary fixed-point groups `H^{F'}` and does not require a
universal prime-to-`p` cover.  The relation is graded U/E2 until the
projective-representation definition of `>=_b` is formalised. -/
structure FLZSourceSemantics (P : Definition35Problem)
    (automorphisms : Definition35AutomorphismStabilizerAdapter P) where
  definition35BlockIsomorphic :
    Definition35Brauer P → Definition35Weight P → Prop

/-- The exact quotient-and-lift relation in equation (3.17), p. 17.

Unlike Definition 3.5(ii), this source relation belongs to the stronger
BAW-goodness lane and is bound to the displayed concrete universal
prime-to-`p` cover.  Keeping it separate prevents the relative Hypothesis
5.5(b) carrier from imposing an ambient-cover hypothesis on every fixed-point
group occurring downstairs. -/
structure Equation317SourceSemantics (P : Definition35Problem)
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (cover : EllPrimeCoverSource P.p P.H) where
  equation317BlockIsomorphic :
    Definition35Brauer P → Definition35Weight P → Prop

/-- Equivariance under the literal action of the source block stabiliser. -/
def Definition35Equivariant (P : Definition35Problem)
    (omega : Definition35Brauer P → Definition35Weight P) : Prop :=
  let _ : MulAction P.Gamma (Definition35Brauer P) :=
    definition35BrauerAction P
  let _ : MulAction P.Gamma (Definition35Weight P) :=
    definition35WeightAction P
  ∀ (a : P.Gamma) (psi : Definition35Brauer P),
    omega (a • psi) = a • omega psi

/-- Fixed source-shaped carrier for an iBAW-bijection in the sense of
Feng--Li--Zhang, Definition 3.5.  The equivalence and its action are literal;
only the indexed modular-character-triple relation comes from the explicit
U/E2 semantic interface. -/
structure Definition35IBAWBijection (P : Definition35Problem)
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (source : FLZSourceSemantics P automorphisms) where
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  blockIsomorphism : ∀ psi : Definition35Brauer P,
    source.definition35BlockIsomorphic psi (omega psi)

/-- Fixed source-shaped carrier for the centreless specialisation of equation
(3.17).  It is indexed by the exact universal `p'`-cover and explicitly
retains the centreless hypothesis.  It is not called a BAW-good witness because the full definition
and its quotient-and-lift semantics have not yet been connected.  No source
theorem constructs this carrier in this module. -/
structure Equation317Witness (P : Definition35Problem)
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (cover : EllPrimeCoverSource P.p P.H)
    (source : Equation317SourceSemantics P automorphisms cover) where
  centerless : Subgroup.center P.H = ⊥
  omega : Definition35Brauer P ≃ Definition35Weight P
  equivariant : Definition35Equivariant P omega
  blockIsomorphism : ∀ psi : Definition35Brauer P,
    source.equation317BlockIsomorphic psi (omega psi)

/-- Exact E2 source interface for the observation following equation (3.17),
p. 17, that its block-isomorphism relation implies Definition 3.5(ii).
It is deliberately relation-level and has no BAW-good or iBAW conclusion. -/
structure Equation317ToDefinition35Source (P : Definition35Problem)
    (automorphisms : Definition35AutomorphismStabilizerAdapter P)
    (definition35Source : FLZSourceSemantics P automorphisms)
    {cover : EllPrimeCoverSource P.p P.H}
    (equation317Source : Equation317SourceSemantics P automorphisms cover) where
  relation_implication : ∀ (psi : Definition35Brauer P)
      (w : Definition35Weight P),
    equation317Source.equation317BlockIsomorphic psi w →
      definition35Source.definition35BlockIsomorphic psi w

/-- Relation-level conversion from the centreless form of equation (3.17)
to the fixed Definition 3.5 carrier.  This applies only the explicitly named
source interface above, not Theorem 3.18 or Theorem 5.7. -/
def Equation317Witness.toDefinition35
    {P : Definition35Problem}
    {automorphisms : Definition35AutomorphismStabilizerAdapter P}
    {definition35Source : FLZSourceSemantics P automorphisms}
    {cover : EllPrimeCoverSource P.p P.H}
    {equation317Source :
      Equation317SourceSemantics P automorphisms cover}
    (conversion : Equation317ToDefinition35Source P automorphisms
      definition35Source equation317Source)
    (witness : Equation317Witness P automorphisms cover equation317Source) :
    Definition35IBAWBijection P automorphisms definition35Source where
  omega := witness.omega
  equivariant := witness.equivariant
  blockIsomorphism := fun psi ↦
    conversion.relation_implication psi (witness.omega psi)
      (witness.blockIsomorphism psi)

/-! ## Feng--Li--Zhang, Assumption 5.3 -/

section Assumption53

variable {p r a : ℕ} {C Fq k K : Type}
variable [Group C] [Finite C]
variable [Field Fq] [Finite Fq] [CharP Fq 2]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable (ha : 0 < a)
variable [Finite (FiniteSymplecticFixed r a)]
variable [Finite (FieldGroup a)] [IsCyclic (FieldGroup a)]
variable (iota : PrimeRegularRootEmbedding p k K
  (FiniteSymplecticFixed r a))
variable (conformal : ConformalStructuralSource r a ha C Fq)

/-- Membership in the literal regular-overgroup orbit in Assumption 5.3,
p. 30. -/
def Assumption53InRegularOrbit
    (psi representative : IBr iota) : Prop :=
  let _ : MulAction C (IBr iota) :=
    conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
  representative ∈ MulAction.orbit C psi

/-- The exact semidirect-product membership form of the stabiliser equality
in Assumption 5.3.  Conformal fixation makes the regular-overgroup stabiliser
the whole left factor. -/
def Assumption53StabilizerFactorization
    (psi : IBr iota) : Prop :=
  let _ : MulAction C (IBr iota) :=
    conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
  let _ : MulAction (FieldGroup a) (IBr iota) :=
    canonicalFieldIBrAction r a ha iota
  let compatible : SemidirectActionCompatible (X := IBr iota)
      conformal.conformalFieldAction :=
    conformalSemidirectCompatible_actual r a ha iota conformal
  let _ : MulAction
      (C ⋊[conformal.conformalFieldAction] FieldGroup a) (IBr iota) :=
    semidirectMulAction conformal.conformalFieldAction compatible
  ∀ g : C ⋊[conformal.conformalFieldAction] FieldGroup a,
    g ∈ MulAction.stabilizer
        (C ⋊[conformal.conformalFieldAction] FieldGroup a) psi ↔
      ∃ c : C, ∃ sigma : FieldGroup a,
        sigma ∈ MulAction.stabilizer (FieldGroup a) psi ∧
          g = SemidirectProduct.inl c * SemidirectProduct.inr sigma

/-- The literal representation-level extension used for Assumption 5.3.
The ambient group is the embedded stabiliser of `psi` in the actual semidirect
product of the fixed-point group by field automorphisms.  Matching it to the
source subgroup `G^F ⋊ A_psi` remains an explicit E1/U boundary. -/
def Assumption53FieldExtension
    (psi : IBr iota) : Prop :=
  let field := fieldAction r a ha
  let _ : MulAction (FiniteSymplecticFixed r a) (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : FiniteSymplecticFixed r a →*
        MulAut (FiniteSymplecticFixed r a))
  let _ : MulAction (FieldGroup a) (IBr iota) :=
    canonicalFieldIBrAction r a ha iota
  let compatible := rightAutomorphismSemidirectCompatible
    (X := IBr iota) field
  let _ : MulAction
      (FiniteSymplecticFixed r a ⋊[field] FieldGroup a) (IBr iota) :=
    semidirectMulAction field compatible
  let innerFixed : ∀ h : FiniteSymplecticFixed r a,
      (SemidirectProduct.inl h :
        FiniteSymplecticFixed r a ⋊[field] FieldGroup a) • psi = psi :=
    fun h ↦ by
      rw [semidirect_inl_smul]
      exact inner_fixes_ibr iota h psi
  let groupEquiv := canonicalHToEmbeddedEquiv psi innerFixed
  let embeddedRoot := iota.alongMulEquiv groupEquiv
  ∃ W : FDRep k (embeddedHStabilizer (phi := field) psi),
    Representation.IsIrreducible W.ρ ∧
    pullbackPrimeRegularAlongEquiv groupEquiv psi.1 =
      Representation.brauerCharacterOfRootEmbedding W.ρ embeddedRoot ∧
    Nonempty (Representation.Extension
      (embeddedHStabilizer (phi := field) psi) W.ρ)

/-- One representative satisfying all three clauses of Assumption 5.3. -/
structure Assumption53Representative (psi : IBr iota) where
  representative : IBr iota
  inRegularOrbit : Assumption53InRegularOrbit ha iota conformal
    psi representative
  stabilizerFactorization : Assumption53StabilizerFactorization
    ha iota conformal representative
  fieldExtension : Assumption53FieldExtension ha iota representative

/-- Fixed source-shaped carrier for Feng--Li--Zhang, Assumption 5.3. -/
structure FLZAssumption53 where
  representative : ∀ psi : IBr iota,
    Assumption53Representative ha iota conformal psi

/-- Kernel-checked construction of Assumption 5.3 from the literal conformal
action, stabiliser factorisation, and cyclic field-extension endpoint.  The
only mathematical input is the separately graded cyclic-extension principle;
the exact regular-overgroup and field-action model is `conformal`. -/
def flzAssumption53_of_actual
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} p k) :
    FLZAssumption53 ha iota conformal where
  representative psi := {
    representative := psi
    inRegularOrbit := by
      dsimp only [Assumption53InRegularOrbit]
      letI : MulAction C (IBr iota) :=
        conformalIBrAction r a iota conformal.multiplier conformal.kernelEquiv
      exact ⟨1, one_smul C psi⟩
    stabilizerFactorization := by
      exact conformal_stabilizer_factorization_actual
        r a ha iota conformal psi
    fieldExtension := by
      exact field_stabilizer_extension_actual r a ha iota principle psi
  }

end Assumption53

/-! ## The dependent class `H_G` and Hypothesis 5.5 -/

/-- Source interface for the class `H_G` on p. 31.  `Pair` represents a
simple simply connected algebraic group with a Steinberg endomorphism and
`Block` its blocks.  The five membership predicates and the separate strict
quasi-isolation predicate are source semantics that remain E1/U because the
project has no algebraic-group or Dynkin-diagram library.  None is a BAW or
iBAW predicate. -/
structure FLZHGClass where
  Pair : Type u
  Block : Pair → Type u
  problem : ∀ pair : Pair, Block pair → Definition35Problem
  sameDefiningCharacteristic : Pair → Prop
  simpleSimplyConnected : Pair → Prop
  steinbergEndomorphism : Pair → Prop
  fixedPointCentralQuotientSimple : Pair → Prop
  dynkinDiagramSubgraph : Pair → Prop
  strictlyQuasiIsolated : ∀ pair : Pair, Block pair → Prop

/-- Exact conjunction defining membership in the source class `H_G`. -/
def FLZHGClass.IsMember (HG : FLZHGClass) (pair : HG.Pair) : Prop :=
  HG.sameDefiningCharacteristic pair ∧
  HG.simpleSimplyConnected pair ∧
  HG.steinbergEndomorphism pair ∧
  HG.fixedPointCentralQuotientSimple pair ∧
  HG.dynkinDiagramSubgraph pair

end ModularRep.PaperProofs.EvenFieldFLZSourceConditions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
