import ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel

/-!
# The fixed quotient-block Brauer fibre

`EvenFieldFLZBAWGoodFamily` records, for every Brauer character `psi` in the
selected block of `H`, an irreducible Brauer character of the common central
quotient whose inflation is `psi`.  It also proves that every displayed
descent belongs to one selected quotient block.  Those facts do **not** imply
the converse: the selected quotient block may contain further irreducible
Brauer characters, and the root embedding stored in the displayed descent is
allowed to vary with `psi`.

This module closes exactly those two interface gaps without importing a
BAW/iBAW endpoint.

## Trust grading

* **K.** Transport along an equality of root embeddings, inflation of every
  fixed descent, injectivity of the fixed descent map, its restriction to the
  two literal block fibres, the exact membership iff, and the resulting
  equivalence of literal fibres are proved in the kernel.
* **E1/U (carrier identification).** `FixedQuotientRootSource` says that the
  per-character quotient root embeddings already stored in the old witness
  are the single reference embedding.  It chooses no character map and has no
  block or BAW conclusion.  For a witness produced by the canonical
  centreless conversion, `coverBoundFixedQuotientRootSource` constructs this
  identification in K; no such source input is then needed.
* **E1/U (reverse block fact).** `QuotientBlockFibreReverseSource` is the one
  new representation theoretic boundary.  It says only that an irreducible
  Brauer character in the selected quotient block is one of the already fixed
  descents.  It does not accept a bijection, a desired result predicate, a
  BAW/iBAW assertion, or an arbitrary conclusion.
* **E2/U.** The intermediate block-induction operation and the cited
  equation-(3.17) implication remain exactly where they were in the imported
  witness.  No E2 operation is introduced or invoked here.

The quotient radical and normaliser constructions are weight-side data and
cannot rule out extra quotient-block Brauer characters.  Likewise, the
inflation equalities prove injectivity of descent but not its surjectivity.
Consequently the reverse source below is logically substantive rather than a
restatement of a kernel consequence.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.EvenFieldFLZQuotientBlockFibre

open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel
open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

variable {ell : ℕ}
variable {family : Definition35Family.{u} ell}
variable {cover : EllPrimeCoverSource ell family.H}
variable {block : family.Block}

/-! ## A fixed set of characters of the quotient -/

/-- The quotient root embedding attached to the reference character.  The
quotient group itself was already fixed by the reference character in the
imported witness. -/
abbrev fixedQuotientRoot
    (W : RelativeBlockConditionWitness family cover block) :=
  (W.matched W.reference).quotient.iota

/-- The kernel theorem that the fixed quotient root embedding separates
simple modules.  This is deliberately reconstructed from the root embedding,
rather than exposed as another source field. -/
abbrev fixedQuotientBrauerInjective
    (W : RelativeBlockConditionWitness family cover block) :
    IrreducibleBrauerCharacterInjectivity (fixedQuotientRoot W) :=
  irreducibleBrauerCharacterInjectivity_of_rootEmbedding
    (fixedQuotientRoot W)

/-- Exact E1/U identification of the quotient root embeddings already stored
for the different descended characters.  The reference root is fixed by the
old witness, so this structure adds no freely chosen root or character map. -/
structure FixedQuotientRootSource
    (W : RelativeBlockConditionWitness family cover block) : Prop where
  matchedRoot_eq_reference :
    ∀ psi : Definition35Brauer (family.problem block),
      (W.matched psi).quotient.iota = fixedQuotientRoot W

/-- The canonical centreless conversion uses one quotient root embedding for
every descended character, so its fixed-root identification is a kernel
construction rather than an additional source field. -/
def coverBoundFixedQuotientRootSource
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {source : Equation317SourceSemantics
      (family.problem block) automorphisms cover}
    (witness : Equation317Witness
      (family.problem block) automorphisms cover source)
    (conversion : CentrelessEquation317ToRelativeBlockConditionSource
      family cover block automorphisms source witness.centerless) :
    FixedQuotientRootSource
      (ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel.Equation317Witness.toCoverBoundRelativeBlockCondition
        witness conversion) where
  matchedRoot_eq_reference := fun _psi ↦ rfl

/-- Transport an `IBr` element along a literal equality of its root
embeddings.  Its underlying prime regular class function is unchanged. -/
def transportIBrRoot
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G]
    {iota j : PrimeRegularRootEmbedding p k K G}
    (h : iota = j) : IBr iota → IBr j :=
  h ▸ id

@[simp]
theorem transportIBrRoot_val
    {p : ℕ} {k K G : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G]
    {iota j : PrimeRegularRootEmbedding p k K G}
    (h : iota = j) (phi : IBr iota) :
    (transportIBrRoot h phi).1 = phi.1 := by
  subst j
  rfl

/-- Block assignment is unchanged by literal root-embedding transport.  The
two injectivity witnesses are propositions and hence proof irrelevant. -/
theorem irreducibleBrauerCharacterBlock_transportIBrRoot
    {p : ℕ} {k K G ι : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Finite G] [Fintype ι]
    {blockIdempotent : ι → k[G]}
    {iota j : PrimeRegularRootEmbedding p k K G}
    (h : iota = j)
    (hinjIota : IrreducibleBrauerCharacterInjectivity iota)
    (hinjJ : IrreducibleBrauerCharacterInjectivity j)
    (blocks : BlockIdempotentDecomposition blockIdempotent)
    (phi : IBr iota) :
    irreducibleBrauerCharacterBlock j hinjJ blocks
        (transportIBrRoot h phi) =
      irreducibleBrauerCharacterBlock iota hinjIota blocks phi := by
  subst j
  have hinj : hinjJ = hinjIota := Subsingleton.elim _ _
  subst hinjJ
  rfl

/-- The old per-character descent, transported to the single reference root
embedding. -/
def fixedDescendedBrauer
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (psi : Definition35Brauer (family.problem block)) :
    IBr (fixedQuotientRoot W) :=
  transportIBrRoot (roots.matchedRoot_eq_reference psi)
    (W.matched psi).quotient.brauer

@[simp]
theorem fixedDescendedBrauer_val
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (psi : Definition35Brauer (family.problem block)) :
    (fixedDescendedBrauer W roots psi).1 =
      (W.matched psi).quotient.brauer.1 :=
  transportIBrRoot_val _ _

/-- Every fixed descent still inflates to the original literal Brauer
character.  This is just the old inflation equality after root transport. -/
theorem fixedDescendedBrauer_inflation
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (psi : Definition35Brauer (family.problem block)) :
    PrimeRegularClassFunction.pullback
        (centralCharacterQuotientMap
          (family.problem block) W.reference)
        (fixedDescendedBrauer W roots psi).1 = psi.1.1 := by
  rw [fixedDescendedBrauer_val]
  exact (W.matched psi).quotient.inflation

/-- The fixed descent map is injective.  No regular-element lifting theorem
is needed: equality downstairs can simply be pulled back, and both pullbacks
are the original function-valued characters. -/
theorem fixedDescendedBrauer_injective
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W) :
    Function.Injective (fixedDescendedBrauer W roots) := by
  intro psi chi h
  apply Subtype.ext
  apply Subtype.ext
  have hpull := congrArg
    (PrimeRegularClassFunction.pullback
      (centralCharacterQuotientMap
        (family.problem block) W.reference))
    (congrArg Subtype.val h)
  simpa only [fixedDescendedBrauer_inflation] using hpull

/-- Root transport turns the imported one-way membership statement into a
statement on the single fixed quotient `IBr` carrier. -/
theorem fixedDescendedBrauer_liesInQuotientBlock
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (psi : Definition35Brauer (family.problem block)) :
    irreducibleBrauerCharacterBlock
        (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
        W.quotientBlocks (fixedDescendedBrauer W roots psi) =
      W.quotientBlock := by
  calc
    irreducibleBrauerCharacterBlock
          (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
          W.quotientBlocks (fixedDescendedBrauer W roots psi) =
        irreducibleBrauerCharacterBlock
          (W.matched psi).quotient.iota
          (W.matched psi).quotient.irreducibleBrauerInjective
          W.quotientBlocks (W.matched psi).quotient.brauer :=
      irreducibleBrauerCharacterBlock_transportIBrRoot
        (roots.matchedRoot_eq_reference psi)
        (W.matched psi).quotient.irreducibleBrauerInjective
        (fixedQuotientBrauerInjective W) W.quotientBlocks
        (W.matched psi).quotient.brauer
    _ = W.quotientBlock :=
      W.descendedBrauer_liesInQuotientBlock psi

/-- The literal `IBr` fibre of the selected quotient block, using the fixed
reference root embedding and the already supplied quotient block
decomposition. -/
abbrev FixedQuotientBrauerFibre
    (W : RelativeBlockConditionWitness family cover block) :=
  IBrBlock (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
    W.quotientBlocks W.quotientBlock

/-- Restrict fixed descent to the two actual block fibres. -/
def descentToFixedQuotientFibre
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W) :
    Definition35Brauer (family.problem block) →
      FixedQuotientBrauerFibre W :=
  fun psi ↦
    ⟨fixedDescendedBrauer W roots psi,
      fixedDescendedBrauer_liesInQuotientBlock W roots psi⟩

@[simp]
theorem descentToFixedQuotientFibre_val
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (psi : Definition35Brauer (family.problem block)) :
    (descentToFixedQuotientFibre W roots psi).1 =
      fixedDescendedBrauer W roots psi :=
  rfl

theorem descentToFixedQuotientFibre_injective
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W) :
    Function.Injective (descentToFixedQuotientFibre W roots) := by
  intro psi chi h
  apply fixedDescendedBrauer_injective W roots
  exact congrArg Subtype.val h

/-! ## The sole reverse-fibre source and its kernel consequences -/

/-- Narrow source-shaped reverse implication for the fixed literal carrier.

It says that membership in the selected quotient block implies equality with
one of the descents already present in `W`.  The converse is the kernel
theorem `fixedDescendedBrauer_liesInQuotientBlock`; hence it is intentionally
absent from this source. -/
structure QuotientBlockFibreReverseSource
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W) : Prop where
  of_quotientBlock :
    ∀ phi : IBr (fixedQuotientRoot W),
      irreducibleBrauerCharacterBlock
          (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
          W.quotientBlocks phi = W.quotientBlock →
        ∃ psi : Definition35Brauer (family.problem block),
          fixedDescendedBrauer W roots psi = phi

/-- The reverse quotient-block implication specialised to the canonical
centreless equation-(3.17) conversion.  The fixed root source is constructed
in K, so this abbreviation retains only the genuinely external reverse
membership implication. -/
abbrev CentrelessQuotientBlockFibreReverseSource
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {source : Equation317SourceSemantics
      (family.problem block) automorphisms cover}
    (witness : Equation317Witness
      (family.problem block) automorphisms cover source)
    (conversion : CentrelessEquation317ToRelativeBlockConditionSource
      family cover block automorphisms source witness.centerless) : Prop :=
  QuotientBlockFibreReverseSource
    (ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel.Equation317Witness.toCoverBoundRelativeBlockCondition
      witness conversion)
    (coverBoundFixedQuotientRootSource witness conversion)

/-- Exact two-way characterisation of the fixed quotient block.  Uniqueness
is a kernel consequence of literal inflation and is not part of the reverse
source. -/
theorem quotientBlock_iff_existsUnique_fixedDescent
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (reverse : QuotientBlockFibreReverseSource W roots)
    (phi : IBr (fixedQuotientRoot W)) :
    irreducibleBrauerCharacterBlock
        (fixedQuotientRoot W) (fixedQuotientBrauerInjective W)
        W.quotientBlocks phi = W.quotientBlock ↔
      ∃! psi : Definition35Brauer (family.problem block),
        fixedDescendedBrauer W roots psi = phi := by
  constructor
  · intro hphi
    rcases reverse.of_quotientBlock phi hphi with ⟨psi, hpsi⟩
    refine ⟨psi, hpsi, ?_⟩
    intro chi hchi
    exact fixedDescendedBrauer_injective W roots
      (hchi.trans hpsi.symm)
  · rintro ⟨psi, hpsi, _⟩
    rw [← hpsi]
    exact fixedDescendedBrauer_liesInQuotientBlock W roots psi

/-- The source-shaped reverse implication makes the fixed descent map onto
the literal quotient-block fibre. -/
theorem descentToFixedQuotientFibre_surjective
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (reverse : QuotientBlockFibreReverseSource W roots) :
    Function.Surjective (descentToFixedQuotientFibre W roots) := by
  intro phi
  rcases reverse.of_quotientBlock phi.1 phi.2 with ⟨psi, hpsi⟩
  refine ⟨psi, ?_⟩
  apply Subtype.ext
  exact hpsi

/-- The strongest fixed carrier-level conclusion: the original literal
Brauer block fibre is equivalent to the literal fibre of the selected block
of the fixed central quotient. -/
def originalBrauerFibreEquivFixedQuotientBrauerFibre
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (reverse : QuotientBlockFibreReverseSource W roots) :
    Definition35Brauer (family.problem block) ≃
      FixedQuotientBrauerFibre W :=
  Equiv.ofBijective (descentToFixedQuotientFibre W roots)
    ⟨descentToFixedQuotientFibre_injective W roots,
      descentToFixedQuotientFibre_surjective W roots reverse⟩

/-- The canonical centreless equation-(3.17) conversion gives the fixed
quotient-fibre equivalence once the sole reverse quotient-block implication is
supplied.  The cover and quotient root are inherited definitionally from the
equation-(3.17) witness and conversion. -/
def Equation317Witness.centrelessOriginalBrauerFibreEquivFixedQuotientBrauerFibre
    {automorphisms : Definition35AutomorphismStabilizerAdapter
      (family.problem block)}
    {source : Equation317SourceSemantics
      (family.problem block) automorphisms cover}
    (witness : Equation317Witness
      (family.problem block) automorphisms cover source)
    (conversion : CentrelessEquation317ToRelativeBlockConditionSource
      family cover block automorphisms source witness.centerless)
    (reverse : CentrelessQuotientBlockFibreReverseSource
      witness conversion) :
    Definition35Brauer (family.problem block) ≃
      FixedQuotientBrauerFibre
        (ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel.Equation317Witness.toCoverBoundRelativeBlockCondition
          witness conversion) :=
  originalBrauerFibreEquivFixedQuotientBrauerFibre
    (ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel.Equation317Witness.toCoverBoundRelativeBlockCondition
      witness conversion)
    (coverBoundFixedQuotientRootSource witness conversion) reverse

@[simp]
theorem originalBrauerFibreEquivFixedQuotientBrauerFibre_apply
    (W : RelativeBlockConditionWitness family cover block)
    (roots : FixedQuotientRootSource W)
    (reverse : QuotientBlockFibreReverseSource W roots)
    (psi : Definition35Brauer (family.problem block)) :
    originalBrauerFibreEquivFixedQuotientBrauerFibre
        W roots reverse psi =
      descentToFixedQuotientFibre W roots psi :=
  rfl

/-! ## Family-level packaging without a family-level endpoint -/

/-- The two narrowly indexed sources for every block of an existing relative
family witness.  This contains neither the resulting equivalences nor a BAW
or iBAW conclusion. -/
structure QuotientBlockFibreFamilySource
    (W : RelativeBlockConditionFamilyWitness family) : Prop where
  roots : ∀ block : family.Block,
    FixedQuotientRootSource (W.blockWitness block)
  reverse : ∀ block : family.Block,
    QuotientBlockFibreReverseSource
      (W.blockWitness block) (roots block)

/-- Every block in the family has the fixed literal fibre equivalence once
the two source-shaped fields above are supplied. -/
def originalBrauerFibreEquivFixedQuotientBrauerFibre_family
    (W : RelativeBlockConditionFamilyWitness family)
    (source : QuotientBlockFibreFamilySource W)
    (block : family.Block) :
    Definition35Brauer (family.problem block) ≃
      FixedQuotientBrauerFibre (W.blockWitness block) :=
  originalBrauerFibreEquivFixedQuotientBrauerFibre
    (W.blockWitness block) (source.roots block) (source.reverse block)

end ModularRep.PaperProofs.EvenFieldFLZQuotientBlockFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
