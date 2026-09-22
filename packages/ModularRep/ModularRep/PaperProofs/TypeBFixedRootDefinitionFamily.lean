import ModularRep.PaperProofs.TypeBSpinDefinitionFamily

/-!
# Type B local blocks in one fixed root convention

Navarro (3.3), (3.11), (3.13)(b), and (3.18) concern one splitting modular
system. A fixed ordinary-character block selector cannot be identified with
the Brauer-block selector for every unrelated root embedding: changing the
root correspondence can change the underlying modular character and its
specified primitive idempotent.

`GuardedBlockCompatibility` therefore applies only when the normalizer root
lift agrees with the fixed global lift on the normalizer's actual roots.
It is the narrowly scoped replacement used in the Type B lane; the shared
unrestricted source is neither modified nor assumed. The selected quotient
reductions have the same root agreement. This file constructs the literal
Spin family from these data without a matching or block-condition input.

The exact identification with a chosen splitting modular system is E1/U.
The guard and family construction are K. Earlier endpoints parameterized by the
old `TypeBSpinDefinitionFamily.LocalSource` retain their literal, stronger
conditional hypotheses; this file does not silently discharge or weaken
those hypotheses.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily

open ModularRep FDRepSimpleClassKZero CharacterWeight
open TypeBCliffordCarriers
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family

universe u

variable {ell : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

/-- Agreement only on the roots used by the actual normalizer. -/
def NormalizerRootAgreement
    (iotaG : PrimeRegularRootEmbedding ell k K G) (Q : Subgroup G)
    (iotaN : PrimeRegularRootEmbedding ell k K
      (Subgroup.normalizer (Q : Set G))) : Prop :=
  ∀ zeta : rootsOfUnity
      (primeRegularExponent ell (Subgroup.normalizer (Q : Set G))) k,
    iotaN.lift (((zeta : kˣ) : k)) = iotaG.lift (((zeta : kˣ) : k))

/-- Agreement on the roots used by the literal local quotient. -/
def QuotientRootAgreement
    (iotaG : PrimeRegularRootEmbedding ell k K G) (Q : Subgroup G)
    (iotaQ : PrimeRegularRootEmbedding ell k K (NormalizerQuotient Q)) : Prop :=
  ∀ zeta : rootsOfUnity (primeRegularExponent ell (NormalizerQuotient Q)) k,
    iotaQ.lift (((zeta : kˣ) : k)) = iotaG.lift (((zeta : kˣ) : k))

/-- The exact local reduction/block identification in the fixed modular
system. Unlike the unrestricted shared law, its root hypothesis is retained
in the quantified implication. It concludes only a local specified block
identity, not a matching, extension, or inductive condition. -/
structure GuardedBlockCompatibility
    (iotaG : PrimeRegularRootEmbedding ell k K G)
    (operations : LocalBlockInductionOperations
      (p := ell) (k := k) (K := K) (G := G) (Block := Block)) : Prop where
  normalizer_block_of_reduction : ∀ (W : CharacterWeight ell K G)
      (iotaN : PrimeRegularRootEmbedding ell k K
        (Subgroup.normalizer (W.subgroup : Set G)))
      (phiN : IBr iotaN),
    NormalizerRootAgreement iotaG W.subgroup iotaN →
    NormalizerInflatedReduction W.subgroup W.localCharacter iotaN phiN →
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        operations W.subgroup iotaN phiN =
      operations.inflateToNormalizer W.subgroup
        (operations.localCharacterBlock
          W.subgroup W.localCharacter W.defectZero)

section PrimitiveFamily

variable {ell : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype (LiteralPrimitiveBlock k G)]

local instance automorphismFinite : Finite (MulAut G) :=
  Finite.of_injective DFunLike.coe DFunLike.coe_injective

/-- The stabilizer of an actual primitive idempotent under the canonical
opposite-automorphism action. -/
abbrev PrimitiveBlockStabilizer (b : LiteralPrimitiveBlock k G) :=
  MulAction.stabilizer (MulAut G)ᵐᵒᵖ b

local instance primitiveStabilizerFinite (b : LiteralPrimitiveBlock k G) :
    Finite (PrimitiveBlockStabilizer b) :=
  Finite.of_injective
    (fun a : PrimitiveBlockStabilizer b => ((MulOpposite.unop a.1 : MulAut G) : G → G))
    (fun a c h => Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

/-- The natural homomorphism from that opposite stabilizer. -/
def primitiveStabilizerHom (b : LiteralPrimitiveBlock k G) :
    PrimitiveBlockStabilizer b →* MulAut G where
  toFun a := (MulOpposite.unop a.1)⁻¹
  map_one' := by simp
  map_mul' a c := by simp

@[simp]
theorem inverseOpHom_primitiveStabilizerHom (b : LiteralPrimitiveBlock k G)
    (a : PrimitiveBlockStabilizer b) :
    inverseOpHom (primitiveStabilizerHom b) a = a.1 := by
  simp [inverseOpHom, primitiveStabilizerHom]

def primitiveBlockAutomorphisms (b : LiteralPrimitiveBlock k G) :
    Definition35BlockAutomorphisms G (LiteralPrimitiveBlock k G) b where
  Gamma := PrimitiveBlockStabilizer b
  gamma := primitiveStabilizerHom b
  gammaBlock_fixed a := by
    rw [inverseOpHom_primitiveStabilizerHom]
    exact a.2

variable (iota : PrimeRegularRootEmbedding ell k K G)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k G => b.1))

theorem primitiveBrauerBlock_transport (alpha : (MulAut G)ᵐᵒᵖ)
    (phi : IBr iota) :
    irreducibleBrauerCharacterBlock iota hinj blocks (alpha • phi) =
      alpha • irreducibleBrauerCharacterBlock iota hinj blocks phi := by
  simpa only [BlockIdempotentDecomposition.primitiveBlockOfIndex] using
    primitiveBlockOfIndex_irreducibleBrauerCharacterBlock_op_smul
      iota hinj blocks alpha phi

/-- Source data in one modular system, on the actual primitive blocks of
an arbitrary finite group. This is an independent input carrier for a
universally quantified criterion, and contains no matching. -/
structure PrimitiveLocalSource where
  splitting : IsAlgClosed K
  blockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := G)
    (Block := LiteralPrimitiveBlock k G)
  idempotent : ∀ b : LiteralPrimitiveBlock k G,
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  blockCompatibility : GuardedBlockCompatibility iota blockSource.operations
  reduction : ∀ (b : LiteralPrimitiveBlock k G)
      (w : LiteralWeightFibre blockSource b),
    SelectedLocalReductionSource blockSource b w
  reduction_roots : ∀ (b : LiteralPrimitiveBlock k G)
      (w : LiteralWeightFibre blockSource b),
    QuotientRootAgreement iota
      (SelectedRadical blockSource b w) (reduction b w).iota

/-- A canonical family for a fixed ordinary/Brauer root convention. The
block and stabilizer carriers are literal, even in the generic theorem. -/
def primitiveFamily (hEll : Nat.Prime ell)
    (localSource : PrimitiveLocalSource iota) : Definition35Family ell where
  ellPrime := hEll
  k := k
  K := K
  H := G
  Block := LiteralPrimitiveBlock k G
  blockIdempotent b := b.1
  iota := iota
  irreducibleBrauerInjective := hinj
  blocks := blocks
  blockSource := localSource.blockSource
  brauerBlock_transport := primitiveBrauerBlock_transport iota hinj blocks
  automorphisms := primitiveBlockAutomorphisms
  localReduction := localSource.reduction

/-- The generic factory also uses the full actual stabilizer. -/
def primitiveFamily_stabilizerAdapter (hEll : Nat.Prime ell)
    (localSource : PrimitiveLocalSource iota) (b : LiteralPrimitiveBlock k G) :
    Definition35AutomorphismStabilizerAdapter
      ((primitiveFamily iota hinj blocks hEll localSource).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (inverseOpHom_primitiveStabilizerHom b a).symm

end PrimitiveFamily

section Spin

variable {n : ℕ} {F k K : Type}
variable [Field F] [Field k] [Field K] [CharP k ell] [IsAlgClosed k]
variable [CharZero K]
variable (N : NormSource n F) [Finite (Spin n F N)]

local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

abbrev SpinBlock := TypeBSpinDefinitionFamily.SpinBlock (k := k) N

variable [Fintype (SpinBlock (k := k) N)]
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition
  (fun b : SpinBlock (k := k) N => b.1))

/-- The local sources in one fixed root convention. Source identification
does not silently quantify over different splitting modular systems. -/
structure LocalSource where
  splitting : IsAlgClosed K
  blockSource : CharacterWeight.LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := Spin n F N)
    (Block := SpinBlock (k := k) N)
  idempotent : ∀ b : SpinBlock (k := k) N,
    blockSource.operations.ambientBlockData.blockIdempotent b = b.1
  blockCompatibility : GuardedBlockCompatibility iota blockSource.operations
  reduction : ∀ (b : SpinBlock (k := k) N)
      (w : LiteralWeightFibre blockSource b),
    SelectedLocalReductionSource blockSource b w
  reduction_roots : ∀ (b : SpinBlock (k := k) N)
      (w : LiteralWeightFibre blockSource b),
    QuotientRootAgreement iota
      (SelectedRadical blockSource b w) (reduction b w).iota

/-- The same literal Spin group, primitive block decomposition and canonical
automorphism stabilizers, combined with the guarded local source. -/
def spinFamily (hEll : Nat.Prime ell)
    (localSource : LocalSource (ell := ell) (k := k) (K := K) N iota) :
    Definition35Family ell where
  ellPrime := hEll
  k := k
  K := K
  H := Spin n F N
  Block := SpinBlock (k := k) N
  fintypeH := Fintype.ofFinite _
  blockIdempotent b := b.1
  iota := iota
  irreducibleBrauerInjective := hinj
  blocks := blocks
  blockSource := localSource.blockSource
  brauerBlock_transport := TypeBSpinDefinitionFamily.brauerBlock_transport
    N iota hinj blocks
  automorphisms := TypeBSpinDefinitionFamily.blockAutomorphisms N
  localReduction := localSource.reduction

/-- The new family still uses the full literal opposite-automorphism block
stabilizer, so its adapter remains the identity in K. -/
def spinFamily_stabilizerAdapter (hEll : Nat.Prime ell)
    (localSource : LocalSource (ell := ell) (k := k) (K := K) N iota)
    (b : SpinBlock (k := k) N) :
    Definition35AutomorphismStabilizerAdapter
      ((spinFamily N iota hinj blocks hEll localSource).problem b) where
  equiv := MulEquiv.refl _
  equiv_coe a := (TypeBSpinDefinitionFamily.inverseOpHom_stabilizerHom N b a).symm

end Spin

end ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
