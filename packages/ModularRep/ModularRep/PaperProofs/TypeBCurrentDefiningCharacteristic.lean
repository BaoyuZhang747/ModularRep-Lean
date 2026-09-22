import ModularRep.PaperProofs.TypeBFullBlockCondition
import ModularRep.PaperProofs.TypeBCliffordOrthogonalSourceBinding

/-!
# Defining characteristic on the actual Type B covering group

Späth, *A reduction theorem for the blockwise Alperin weight conjecture*,
J. Group Theory 16 (2013), 159--220, Theorem C and its proof on
pp. 215--217, gives the complete inductive condition in defining
characteristic. The proof specifies the universal prime-to-p cover and
observes that the exceptional Schur multiplier part is a p-group.

Here the cover is the literal Clifford norm-one Spin group, with the
constructed vector-conjugation projection onto the independently defined
matrix Omega group. Exact structural maximality is an E1/U premise.
There is no exclusion of Spin7(3) at its defining prime three and no
assumption that Spin7(3) is the full universal central cover.

The output is the fixed complete primitive-block FamilyWitness. No
caller-selected relation, target proposition or block correspondence is
an input to the published source application.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCurrentDefiningCharacteristic

open ModularRep FDRepSimpleClassKZero TypeBCliffordCarriers TypeBCliffordOrthogonalSourceBinding
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open EvenFieldFLZSourceConditions

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
variable (N : NormSource n F)
variable (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)

/-- Standard finite group and prime-to-defining-characteristic covering
facts on the exact matrix projection. Unlike GenericSpinCoverSource, this
contract includes the exceptional `(n,q)=(3,3)` in characteristic three.
Its maximality is the prime-to-p universal property, not the full-cover
property that fails for Spin7(3). -/
structure CoverFacts where
  centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N
  perfect : commutator (Spin n F N) = ⊤
  simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n F)
  nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega n F)
  maximal : ∀ (D : Type) [Group D] [Fintype D]
      (q : D →* TypeBOrthogonalOmegaCarriers.Omega n F),
    Function.Surjective q → q.ker ≤ Subgroup.center D →
      commutator D = ⊤ → ¬ p ∣ Nat.card q.ker →
      ∃ lift : Spin n F N →* D,
        Function.Surjective lift ∧ q.comp lift = spinProjection n F parameters rank N C

namespace CoverFacts

variable {parameters rank N C}

/-- The centre has order two, hence is prime to the actual odd defining
prime. This deduction also covers `(n,q,p)=(3,3,3)`. -/
theorem center_primeTo (facts : CoverFacts parameters rank N C) :
    ¬ p ∣ Nat.card (Subgroup.center (Spin n F N)) := by
  rw [facts.centre.centre_order parameters rank]
  exact parameters.prime.coprime_iff_not_dvd.mp parameters.odd.coprime_two_right

variable [Fintype (Spin n F N)]
local instance omegaFintype : Fintype (TypeBOrthogonalOmegaCarriers.Omega n F) :=
  Fintype.ofFinite _

/-- The same actual Spin-to-matrix-Omega projection is used throughout. -/
def actualCover (facts : CoverFacts parameters rank N C) :
    EllPrimeCoverSource p (Spin n F N) where
  S := TypeBOrthogonalOmegaCarriers.Omega n F
  quotient := spinProjection n F parameters rank N C
  quotient_surjective := spinProjection_surjective n F parameters rank N C
  quotient_kernel := spin_kernel_eq_center n F N parameters rank C facts.centre
  perfect := facts.perfect
  simple := facts.simple
  nonabelian := facts.nonabelian
  centerPrimeTo := facts.center_primeTo
  maximal := facts.maximal

@[simp] theorem actualCover_quotient (facts : CoverFacts parameters rank N C) :
    facts.actualCover.quotient = spinProjection n F parameters rank N C := rfl

end CoverFacts

/-- Theorem C specialized to the literal Type B carrier and constructed
prime-to-p cover. The fixed coefficient and local-source conventions are
the authenticated Definition 4.1/complete block-family interpretation.
This is an E2/U certificate type; no inhabitant is asserted. -/
structure TheoremCCertificate : Prop where
  allBlocks : ∀ (n p f : ℕ) (F k K : Type)
      [Field F] [Finite F] [CharP F p]
      [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
      (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
      (N : NormSource n F) [Finite (Spin n F N)]
      [Fintype (Spin n F N)] [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
      (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)
      (facts : CoverFacts parameters rank N C)
      (iota : PrimeRegularRootEmbedding p k K (Spin n F N))
      (hinj : IrreducibleBrauerCharacterInjectivity iota)
      (blocks : BlockIdempotentDecomposition
        (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val))
      (localSource : PrimitiveLocalSource iota)
      (coefficient : SpathCoefficientField p k parameters.prime),
    Nonempty (FamilyWitness
      (primitiveFamily iota hinj blocks parameters.prime localSource) facts.actualCover)

variable [Finite (Spin n F N)]

local instance inputSpinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

/-- Compact source packet for the final prime split. The prime and covering
group are fixed by the surrounding literal Type B parameters. -/
structure DefiningInputs where
  k : Type
  K : Type
  [fieldk : Field k]
  [fieldK : Field K]
  [chark : CharP k p]
  [closedk : IsAlgClosed k]
  [zeroK : CharZero K]
  [finiteBlocks : Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  facts : CoverFacts parameters rank N C
  iota : PrimeRegularRootEmbedding p k K (Spin n F N)
  hinj : IrreducibleBrauerCharacterInjectivity iota
  blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val)
  localSource : PrimitiveLocalSource iota
  coefficient : SpathCoefficientField p k parameters.prime
  published : TheoremCCertificate

attribute [instance] DefiningInputs.fieldk DefiningInputs.fieldK DefiningInputs.chark
  DefiningInputs.closedk DefiningInputs.zeroK DefiningInputs.finiteBlocks

namespace DefiningInputs

variable {parameters rank N C}

/-- The actual primitive family, independent of the source theorem. -/
def family (inputs : DefiningInputs parameters rank N C) :=
  primitiveFamily inputs.iota inputs.hinj inputs.blocks parameters.prime inputs.localSource

/-- Fixed complete defining-prime conclusion, including every actual block. -/
def target (inputs : DefiningInputs parameters rank N C) : Prop :=
  Nonempty (FamilyWitness inputs.family inputs.facts.actualCover)

/-- Apply the exact published theorem after constructing the literal cover
and proving its prime-to-p centre condition. -/
theorem complete (inputs : DefiningInputs parameters rank N C) : inputs.target := by
  exact inputs.published.allBlocks n p f F inputs.k inputs.K parameters rank N C
    inputs.facts inputs.iota inputs.hinj inputs.blocks inputs.localSource inputs.coefficient

end DefiningInputs

end ModularRep.PaperProofs.TypeBCurrentDefiningCharacteristic


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
