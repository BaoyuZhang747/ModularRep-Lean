import ModularRep.PaperProofs.TypeBModularGroupRootBinding
import ModularRep.PaperProofs.TypeBFixedRootCriterionFamilySplitting
import ModularRep.PaperProofs.TypeBFullBlockCondition

/-!
# The full published criterion over one actual modular system

The domain is the existing generic all-blocks domain on finite G <= M and
M semidirect E, with every original extension and structural clause.
The ordinary coefficients contain the roots needed by M. The two initial
Brauer roots are the constructed roots of the same complete modular
system. Upstairs local block compatibility is retained separately from
the ambient idempotent catalogue; downstairs the full local-reduction
record is retained.

The one-way E2 source is Brough--Spath Theorem 4.5, pp. 476--477, with
Definition 4.3 and Remark 4.4, pp. 475--476, followed by Koshitani--Spath
Lemma 3.3, p. 783, and Spath Definition 4.1, p. 182. The splitting-field,
specified-block and common-root interpretations are the corresponding E1
finite-character identifications. All output carriers are fixed by the
independent complete condition, not selected by a caller.

The output also records a choice of the root convention on each
existentially produced ambient group. This is only a normalization of
character values to the same modular system. Existing quotient, local and
intermediate comparisons are retained in the full output.

This module declares no inhabitant of the generic certificate. A Type B
application must construct its complete input from independent sources
and checked deductions. Neither a downstairs matching nor the Type B
proposition is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFullCriterionSplittingSource

open ModularRep FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions
open EvenFieldFLZDefinition35Family TypeBCriterionHypotheses
open TypeCWeightTensorFieldAction

local instance finiteFintype {T : Type} [Finite T] : Fintype T := Fintype.ofFinite T

section NormalizedOutput

variable {ell : ℕ} {family : Definition35Family ell}
variable {O : Type} [CommRing O] [IsDomain O] [familyAlgebra : Algebra O family.K]

/-- The actual ambient roots used by the full output follow one residue
convention, including roots beyond the original group's exponent. -/
def FamilyAmbientRootAgreement
    (Msys : ModularSystem ell family.K O family.k)
    {cover : EllPrimeCoverSource ell family.H}
    (W : TypeBFullBlockCondition.FamilyWitness family cover) : Prop :=
  ∀ (b : family.Block) (psi : Definition35Brauer (family.problem b))
    (zeta : rootsOfUnity
      (primeRegularExponent ell ((W.blocks b).relative.matched psi).ambient.A) family.k),
    ((W.blocks b).relative.matched psi).extensions.ambientRoot.lift
        ((zeta : family.kˣ) : family.k) =
      (TypeBModularGroupRootBinding.groupRoot Msys
        ((W.blocks b).relative.matched psi).ambient.A).lift
          ((zeta : family.kˣ) : family.k)

/-- A complete condition together with the common modular-system
normalization of its existential ambient character conventions. -/
structure NormalizedFamilyWitness
    (Msys : ModularSystem ell family.K O family.k)
    (cover : EllPrimeCoverSource ell family.H) where
  full : TypeBFullBlockCondition.FamilyWitness family cover
  ambient_roots : FamilyAmbientRootAgreement Msys full

end NormalizedOutput

/-- The generic, fully scoped published implication. Its conclusion is
fixed and complete; no source supplies an combined Type B input. -/
structure Theorem45SplittingCertificate : Prop where
  allBlocks : ∀ {ell : ℕ} {k K O M E : Type}
      [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
      [CharP k ell] [IsAlgClosed k] [CharZero K]
      [Group M] [Finite M] [Group E] [Finite E]
      [HasEnoughRootsOfUnity K (Nat.card M)]
      (Msys : ModularSystem ell K O k)
      (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
      (action : NaturalAction G field)
      (iotaM : PrimeRegularRootEmbedding ell k K M)
      (iotaG : PrimeRegularRootEmbedding ell k K G)
      (rootM : iotaM = TypeBModularGroupRootBinding.groupRoot Msys M)
      (rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys G)
      [Fintype (LiteralPrimitiveBlock k M)]
      [Fintype (LiteralPrimitiveBlock k G)]
      (blocks : BlockData (ell := ell) (k := k) (K := K) G)
      (upstairsPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
        iotaM blocks.weightUpstairs.operations)
      (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
      (hinvariant :
        TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant G field)
      (D : TypeCConformalActionAdapter.OrdinaryReductionEquiv
        (k := k) (K := K) G field hinvariant)
      (productFormula : BrauerLinearTensorProductFormula iotaM)
      (radicalKernel : RadicalKernelLiftInput (p := ell) G field hinvariant D)
      (hypotheses : AllBlocksHypotheses G field action iotaM iotaG
        blocks hinjM hinvariant D productFormula radicalKernel),
    Nonempty (NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBFixedRootCriterionFamilySplitting.downstairsFamily
        G iotaG blocks hypotheses.prime
        hypotheses.brauer_injective_downstairs hypotheses.localReduction)
      Msys hypotheses.cover)

section Apply

variable {ell : ℕ} {k K O M E : Type}
variable [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable [HasEnoughRootsOfUnity K (Nat.card M)]
variable (Msys : ModularSystem ell K O k)
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)
variable (iotaM : PrimeRegularRootEmbedding ell k K M)
variable (iotaG : PrimeRegularRootEmbedding ell k K G)
variable (rootM : iotaM = TypeBModularGroupRootBinding.groupRoot Msys M)
variable (rootG : iotaG = TypeBModularGroupRootBinding.groupRoot Msys G)
variable [Fintype (LiteralPrimitiveBlock k M)] [Fintype (LiteralPrimitiveBlock k G)]
variable (blocks : BlockData (ell := ell) (k := k) (K := K) G)
variable (upstairsPhysical : TypeBFixedRootDefinitionFamily.GuardedBlockCompatibility
  iotaM blocks.weightUpstairs.operations)
variable (hinjM : IrreducibleBrauerCharacterInjectivity iotaM)
variable (hinvariant :
  TypeCConformalActionAdapter.FieldInvariantSubgroup.IsInvariant G field)
variable (D : TypeCConformalActionAdapter.OrdinaryReductionEquiv
  (k := k) (K := K) G field hinvariant)
variable (productFormula : BrauerLinearTensorProductFormula iotaM)
variable (radicalKernel : RadicalKernelLiftInput (p := ell) G field hinvariant D)
variable (hypotheses : AllBlocksHypotheses G field action iotaM iotaG
  blocks hinjM hinvariant D productFormula radicalKernel)

/-- Apply the independently quantified source to its literal inputs. -/
def witness (source : Theorem45SplittingCertificate) :
    NormalizedFamilyWitness
      (familyAlgebra := (show Algebra O K from inferInstance))
      (family := TypeBFixedRootCriterionFamilySplitting.downstairsFamily
        G iotaG blocks hypotheses.prime
        hypotheses.brauer_injective_downstairs hypotheses.localReduction)
      Msys hypotheses.cover :=
  Classical.choice (source.allBlocks Msys G field action iotaM iotaG rootM rootG
    blocks upstairsPhysical hinjM hinvariant D productFormula radicalKernel hypotheses)

end Apply

end ModularRep.PaperProofs.TypeBFullCriterionSplittingSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
