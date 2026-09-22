import ModularRep.PaperProofs.TypeCOddTwoCoherentFamilyApplication
import ModularRep.BrauerCharacterHomPullback

/-!
# The original family's exact canonical primitive presentation

The actual group, cover, coefficients, block source, block action and
selected quotient table are unchanged. The displayed ambient idempotent
function is replaced by its proved literal value function. The two actual
block-stabilizer homomorphisms already have the same values.

The existing local-block support law supplies the guarded canonical law:
agreement on every relevant finite root implies representation compatibility.
The implication is used in that direction only. Selected finite-root guards
come from the actual coherent table. No new dictionary or target source is
introduced. The final caller transports the already constructed family,
retaining the exact cover rather than introducing a second covering map.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeCOddTwoCanonicalPrimitiveFamily

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open TypeBFixedRootDefinitionFamily TypeBFullBlockCondition
open OddTwoLiteralSpathTarget TypeCCoherentFiniteRootConvention
open TypeCOddTwoOriginalBlockMatching TypeCOddTwoCoherentTargetData
open TypeCOddTwoChosenRootMetadata TypeCOddTwoCoherentFamilyApplication
open OddTwoFinalBlockOrbitCentralCoverDescentWindow OddTwoFengMalleForwardSourceJoin

universe u

section FixedPresentation

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]
variable (hp : p.Prime) (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (source : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G) (Block := Block))
variable (reduction : ∀ b : Block, ∀ w : LiteralWeightFibre source b,
  SelectedLocalReductionSource source b w)

/- These private helpers expose only the dependent record bookkeeping.
All their non-proof data are fixed before either presentation is formed. -/
private def presentationFamily
    (f : Block → k[G]) (blocks : BlockIdempotentDecomposition f)
    (transport : ∀ (a : (MulAut G)ᵐᵒᵖ) (psi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (a • psi) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks psi)
    (automorphisms : ∀ b : Block, Definition35BlockAutomorphisms G Block b) :
    Definition35Family p where
  ellPrime := hp
  k := k
  K := K
  H := G
  Block := Block
  blockIdempotent := f
  iota := iota
  irreducibleBrauerInjective := hinj
  blocks := blocks
  blockSource := source
  brauerBlock_transport := transport
  automorphisms := automorphisms
  localReduction := reduction

variable {f f' : Block → k[G]}
variable (blocks : BlockIdempotentDecomposition f)
variable (blocks' : BlockIdempotentDecomposition f')
variable (transport : ∀ (a : (MulAut G)ᵐᵒᵖ) (psi : IBr iota),
  irreducibleBrauerCharacterBlock iota hinj blocks (a • psi) =
    a • irreducibleBrauerCharacterBlock iota hinj blocks psi)
variable (transport' : ∀ (a : (MulAut G)ᵐᵒᵖ) (psi : IBr iota),
  irreducibleBrauerCharacterBlock iota hinj blocks' (a • psi) =
    a • irreducibleBrauerCharacterBlock iota hinj blocks' psi)
variable (autos autos' : ∀ b : Block, Definition35BlockAutomorphisms G Block b)

private theorem presentationFamily_eq
    (hf : f = f') (ha : autos = autos') :
    presentationFamily hp iota hinj source reduction f blocks transport autos =
      presentationFamily hp iota hinj source reduction f' blocks' transport' autos' := by
  cases hf
  cases ha
  rfl

/-- Equality transport with a FIXED actual covering map. The group and its
instances never vary in this helper, so no cover projection cast remains. -/
private def presentationWitness
    (hf : f = f') (ha : autos = autos') (cover : EllPrimeCoverSource p G)
    (W : FamilyWitness
      (presentationFamily hp iota hinj source reduction f blocks transport autos) cover) :
    FamilyWitness
      (presentationFamily hp iota hinj source reduction f' blocks' transport' autos') cover := by
  cases hf
  cases ha
  exact W

end FixedPresentation

section Original

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : Problem n F)

local instance canonicalPrimitiveGroupFintype : Fintype (X n F) := Fintype.ofFinite _
local instance canonicalPrimitiveSubgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) : Fintype H := Fintype.ofFinite _

/-- The ambient catalogue function is the actual literal primitive value. -/
theorem idempotent_eq :
    P.blockSource.operations.ambientBlockData.blockIdempotent =
      (fun b : P.Block => b.1) := funext P.catalogue_idempotent

/-- Cast only the existing decomposition proof along its actual function
identity. No new catalogue or finite enumeration is selected. -/
def literalBlocks :
    letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
      P.blockSource.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (fun b : P.Block => b.1) := by
  letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
    P.blockSource.operations.ambientBlockData.fintypeBlock
  exact (idempotent_eq P) ▸ P.blockSource.operations.ambientBlockData.blocks

/-- The old and canonical stabilizer homomorphisms have identical values. -/
theorem stabilizerHom_eq (b : P.Block) :
    P.blockGamma b = primitiveStabilizerHom b := by
  apply MonoidHom.ext
  intro a
  rfl

/-- The full acting-group records coincide; the finite/fixedness witnesses
are proof fields, and the group is the same actual opposite stabilizer. -/
theorem automorphisms_eq :
    letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
      P.blockSource.operations.ambientBlockData.fintypeBlock
    (family P).automorphisms = primitiveBlockAutomorphisms (k := P.k) (G := X n F) := by
  letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
    P.blockSource.operations.ambientBlockData.fintypeBlock
  funext b
  rfl

variable (C : Convention 2 P.k P.K)
variable (hRoot : P.iota = C.rootAt (X n F))
variable (hSelected : ∀ (b : P.Block) (w : LiteralWeightFibre P.blockSource b),
  (P.localReduction b w).iota =
    C.rootAt (NormalizerQuotient (SelectedRadical P.blockSource b w)))
variable (support : OddTwoActualLocalBlockSupport.Source P.iota P.blockSource.operations)

include support in
/-- The old specified support law already yields the guarded canonical law.
All finite source roots imply the required eigenvalue compatibility. -/
def guardedCompatibility : GuardedBlockCompatibility P.iota P.blockSource.operations where
  normalizer_block_of_reduction W iotaN phiN roots reduction :=
    support.normalizer_block_of_reduction W iotaN phiN
      (fun rho => Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
        rho.ρ P.iota iotaN (Subgroup.normalizer (W.subgroup : Set (X n F))).subtype roots)
      reduction

include hRoot hSelected in
/-- The selected table uses C on its actual own normalizer quotient. -/
theorem selected_roots (b : P.Block) (w : LiteralWeightFibre P.blockSource b) :
    QuotientRootAgreement P.iota (SelectedRadical P.blockSource b w)
      (P.localReduction b w).iota := by
  rw [hSelected b w, hRoot]
  intro z
  let Q := SelectedRadical P.blockSource b w
  let N := Subgroup.normalizer (Q : Set (X n F))
  exact C.rootAt_lift_of_card_dvd
    ((Q.subgroupOf N).card_quotient_dvd_card.trans
      (Subgroup.card_subgroup_dvd_card N)) z

/-- The canonical source retains the EXACT original operations and chosen
reductions. Its two guards are derived, not new source fields. -/
def localSource : PrimitiveLocalSource P.iota where
  splitting := P.ordinarySplitting
  blockSource := P.blockSource
  idempotent := P.catalogue_idempotent
  blockCompatibility := guardedCompatibility P support
  reduction := P.localReduction
  reduction_roots := selected_roots P C hRoot hSelected

/-- The fixed canonical factory, on the same finite enumerations. -/
def canonicalFamily : Definition35Family 2 := by
  letI : Fintype (X n F) := (family P).fintypeH
  letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
    P.blockSource.operations.ambientBlockData.fintypeBlock
  exact primitiveFamily P.iota P.injective (literalBlocks P) Nat.prime_two
    (localSource P C hRoot hSelected support)

/-- Equality of the WHOLE dependent family, not just its idempotent values. -/
theorem family_eq_canonical :
    family P = canonicalFamily P C hRoot hSelected support := by
  letI : Fintype (X n F) := (family P).fintypeH
  letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
    P.blockSource.operations.ambientBlockData.fintypeBlock
  exact presentationFamily_eq Nat.prime_two P.iota P.injective P.blockSource
    P.localReduction P.blockSource.operations.ambientBlockData.blocks (literalBlocks P)
    P.support_transport (primitiveBrauerBlock_transport P.iota P.injective (literalBlocks P))
    (family P).automorphisms (primitiveBlockAutomorphisms (k := P.k) (G := X n F))
    (idempotent_eq P) (automorphisms_eq P)

/-- The canonical presentation keeps the SAME actual cover object and map. -/
abbrev canonicalCover : EllPrimeCoverSource 2
    (canonicalFamily P C hRoot hSelected support).H := P.cover

/-- Transport an already constructed witness on fixed actual carriers.
The generic W input is not a published Type C premise; the final caller below
computes W from the joint source before this ordinary equality transport. -/
def toCanonical
    (W : FamilyWitness (family P) (familyCover P)) :
    FamilyWitness (canonicalFamily P C hRoot hSelected support)
      (canonicalCover P C hRoot hSelected support) := by
  letI : Fintype (X n F) := (family P).fintypeH
  letI : Fintype (LiteralPrimitiveBlock P.k (X n F)) :=
    P.blockSource.operations.ambientBlockData.fintypeBlock
  exact presentationWitness Nat.prime_two P.iota P.injective P.blockSource
    P.localReduction P.blockSource.operations.ambientBlockData.blocks (literalBlocks P)
    P.support_transport (primitiveBrauerBlock_transport P.iota P.injective (literalBlocks P))
    (family P).automorphisms (primitiveBlockAutomorphisms (k := P.k) (G := X n F))
    (idempotent_eq P) (automorphisms_eq P) P.cover W

@[simp] theorem canonicalCover_quotient :
    (canonicalCover P C hRoot hSelected support).quotient = P.cover.quotient := rfl

@[simp] theorem canonicalFamily_localReduction (b : P.Block)
    (w : LiteralWeightFibre P.blockSource b) :
    (canonicalFamily P C hRoot hSelected support).localReduction b w =
      P.localReduction b w := rfl

end Original

section PublishedApplication

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : LiteralFengMalleProblem n F) (O : LiteralDiagonalFieldRealisation n F)
variable (C : Convention 2 P.k P.K) (S : CanonicalTargetData P C)
variable (admissible : P.iota = C.rootAt (LiteralSp n F))
variable (physical : PhysicalInputs (S.targetData admissible).toProblem)
variable (source : JointFengMalleProposition34Source P O C S admissible)

/-- Canonical primitive-family output from the actual constructed complete
family. SAME S.support supplies the specified law; no new E1 input is added. -/
def canonicalFamilyWitnessFromFengMalle
    (input : InputSemantics P) (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    FamilyWitness
      (canonicalFamily (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support)
      (canonicalCover (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support) :=
  toCanonical (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support
    (familyWitnessFromFengMalle P O C S admissible physical source input omega corollary46)

include source physical in
theorem complete_canonical_family
    (input : InputSemantics P) (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    Nonempty (FamilyWitness
      (canonicalFamily (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support)
      (canonicalCover (S.targetData admissible).toProblem C rfl (fun _ _ => rfl) S.support)) :=
  ⟨canonicalFamilyWitnessFromFengMalle P O C S admissible physical source input omega corollary46⟩

end PublishedApplication

end ModularRep.PaperProofs.TypeCOddTwoCanonicalPrimitiveFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
