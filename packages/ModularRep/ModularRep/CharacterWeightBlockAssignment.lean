import ModularRep.BlockInduction
import ModularRep.LocalNormalizerBlockOperations

/-!
# Block assignment on literal character weights

An Alperin weight consists of a radical subgroup `Q` and a defect-zero
ordinary character of `N_G(Q) / Q`.  Its ambient block is obtained in three
steps: take the block of the local character, inflate that block to `N_G(Q)`,
and induce it to `G`.

This file isolates the local-character block and inflation operations together
with complete catalogues of the block central characters of the normaliser and
the ambient group.  Definedness of induction is supplied only for the local
block attached to each raw character weight.  The ambient block itself is then
selected by the kernel proved existence and uniqueness theorem in
`BlockInduction`.

The resulting composite descends first through isomorphism of character
weights and then through ambient conjugacy.  It gives an equivariant block
assignment on literal character-weight conjugacy classes.  The source
interface contains no function selecting an ambient block, character-weight
bijection, block preservation for such a bijection, BAW-goodness, or iBAW
conclusion.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.CharacterWeight

universe u

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharZero K]
variable [Group G] [Fintype G]
variable [MulAction (MulAut G)ᵐᵒᵖ Block]

local instance subgroupFintype (Q : Subgroup G) : Fintype Q :=
  Fintype.ofFinite Q

/-- A complete ambient block decomposition together with its block central
characters.  The finite block index is stored in the data, so users of the
outer source structure need not supply a global `Fintype Block` instance. -/
structure AmbientBlockCatalogueData [IsAlgClosed k] where
  [fintypeBlock : Fintype Block]
  blockIdempotent : Block → k[G]
  blocks : BlockIdempotentDecomposition blockIdempotent
  catalogue : BlockCentralCharacterCatalogue blocks

/-- The complete block decomposition of a normaliser, indexed by the
canonical subtype of its primitive central idempotents, together with the
corresponding block central characters. -/
structure InflatedNormalizerBlockCatalogueData [IsAlgClosed k]
    (Q : Subgroup G) where
  [fintypeBlock : Fintype (InflatedNormalizerBlock (k := k) Q)]
  blocks : BlockIdempotentDecomposition
    (inflatedNormalizerBlockIdempotent (k := k) Q)
  catalogue : BlockCentralCharacterCatalogue blocks

namespace InflatedNormalizerBlockCatalogueData

variable [IsAlgClosed k]
variable {Q : Subgroup G}

/-- Forget the central character catalogue while retaining its paired finite
index and literal block decomposition. -/
def toDecompositionData
    (D : InflatedNormalizerBlockCatalogueData (k := k) Q) :
    InflatedNormalizerBlockDecompositionData (k := k) Q := by
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) :=
    D.fintypeBlock
  exact
    { fintypeBlock := D.fintypeBlock
      blocks := D.blocks }

end InflatedNormalizerBlockCatalogueData

/-- The source operations and catalogue data defining the ambient block of a
raw character weight.  The only block-induction input is multiplicativity of
the induced central function.  No ambient block is supplied. -/
structure LocalBlockInductionOperations where
  [isAlgClosed : IsAlgClosed k]
  /-- The block of an irreducible defect-zero character of `N_G(Q) / Q`. -/
  localCharacterBlock : ∀ (Q : Subgroup G),
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q)) →
      IsDefectZeroOrdinaryCharacter p chi →
      LocalQuotientBlock (k := k) Q
  /-- Inflation of a quotient block to the normaliser. -/
  inflateToNormalizer : ∀ (Q : Subgroup G),
    LocalQuotientBlock (k := k) Q → InflatedNormalizerBlock (k := k) Q
  /-- The complete ambient block decomposition and its central characters. -/
  ambientBlockData : AmbientBlockCatalogueData
    (k := k) (G := G) (Block := Block)
  /-- The complete normaliser block decomposition and its central characters,
  for every subgroup occurring in a raw character weight. -/
  inflatedNormalizerBlockData : ∀ (Q : Subgroup G),
    InflatedNormalizerBlockCatalogueData (k := k) Q
  /-- Block induction is defined for the inflated local block attached to
  each raw character weight. -/
  blockInductionDefined : ∀ W : CharacterWeight p K G,
    let localData := inflatedNormalizerBlockData W.subgroup
    letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
      localData.fintypeBlock
    ModularRep.IsBlockInductionDefined
      (Subgroup.normalizer (W.subgroup : Set G))
      (localData.catalogue.centralCharacter
        (inflateToNormalizer W.subgroup
          (localCharacterBlock W.subgroup W.localCharacter W.defectZero)))

namespace LocalBlockInductionOperations

omit [MulAction (MulAut G)ᵐᵒᵖ Block] in
/-- Forget the ambient and all-weight block-induction data, retaining only
the block operations and decomposition at the fixed subgroup `Q`. -/
noncomputable def toLocalNormalizerBlockOperations
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (Q : Subgroup G) :
    LocalNormalizerBlockOperations
      (p := p) (k := k) (K := K) (G := G) Q := by
  letI : IsAlgClosed k := O.isAlgClosed
  exact
    { localCharacterBlock := fun chi hchi =>
        O.localCharacterBlock Q chi hchi
      inflateToNormalizer := O.inflateToNormalizer Q
      normalizerBlockData :=
        (O.inflatedNormalizerBlockData Q).toDecompositionData }

/-- Block induction from a normaliser to the ambient group.  The result is
selected from the kernel proved existence and uniqueness theorem for block
central characters, rather than supplied as source data. -/
noncomputable def induceToAmbient
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (W : CharacterWeight p K G) : Block :=
  letI : IsAlgClosed k := O.isAlgClosed
  let localData := O.inflatedNormalizerBlockData W.subgroup
  letI : Fintype Block := O.ambientBlockData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) :=
    localData.fintypeBlock
  ModularRep.inducedBlock (Subgroup.normalizer (W.subgroup : Set G))
    localData.catalogue O.ambientBlockData.catalogue
    (O.inflateToNormalizer W.subgroup
      (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
    (O.blockInductionDefined W)

/-- The ambient block assigned by the local-character block, inflation, and
kernel-defined block-induction operations to a raw character weight. -/
def rawWeightBlock
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (W : CharacterWeight p K G) : Block :=
  O.induceToAmbient W

omit [MulAction (MulAut G)ᵐᵒᵖ Block] in
@[simp]
theorem rawWeightBlock_eq
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    (W : CharacterWeight p K G) :
    O.rawWeightBlock W = O.induceToAmbient W :=
  rfl

omit [MulAction (MulAut G)ᵐᵒᵖ Block] in
/-- The raw block composite respects character-weight isomorphism because
that relation is equality on the data-bearing fields of a character weight. -/
theorem rawWeightBlock_eq_of_isomorphic
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := G) (Block := Block))
    {W W' : CharacterWeight p K G} (h : Isomorphic W W') :
    O.rawWeightBlock W = O.rawWeightBlock W' :=
  congrArg O.rawWeightBlock (eq_of_isomorphic h)

end LocalBlockInductionOperations

/-- Exact source facts needed to transport local block induction through
automorphisms and then through ambient conjugacy.

Isomorphism invariance is kernel-derived from equality of character weights.
`automorphism_transport` is the standard compatibility of local blocks,
inflation, and block induction with automorphisms.  `inner_blocks_fixed`
records that ambient blocks are fixed by inner automorphisms.  These two
fields imply ambient-conjugation invariance; it is not assumed separately. -/
structure LocalBlockInductionSource where
  operations : LocalBlockInductionOperations
    (p := p) (k := k) (K := K) (G := G) (Block := Block)
  automorphism_transport : ∀ (alpha : MulAut G)
    (W : CharacterWeight p K G),
    operations.rawWeightBlock (W.rightTwist alpha) =
      MulOpposite.op alpha • operations.rawWeightBlock W
  inner_blocks_fixed : ∀ (g : G) (b : Block),
    MulOpposite.op (MulAut.conj g⁻¹) • b = b

namespace LocalBlockInductionSource

variable (S : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := G) (Block := Block))

/-- The composite local block operation descends through isomorphism of raw
character weights. -/
def isoClassBlock : IsoClass (p := p) (K := K) (G := G) → Block :=
  Quotient.lift S.operations.rawWeightBlock
    (fun _ _ h ↦
      LocalBlockInductionOperations.rawWeightBlock_eq_of_isomorphic
        S.operations h)

@[simp]
theorem isoClassBlock_mk (W : CharacterWeight p K G) :
    S.isoClassBlock (Quotient.mk'' W) = S.operations.rawWeightBlock W :=
  rfl

/-- Block induction on weight isomorphism classes commutes with the manuscript
right automorphism action. -/
theorem isoClassBlock_rightTwist (alpha : MulAut G)
    (w : IsoClass (p := p) (K := K) (G := G)) :
    S.isoClassBlock
        (rightTwistIsoClass (p := p) (K := K) (G := G) alpha w) =
      MulOpposite.op alpha • S.isoClassBlock w := by
  refine Quotient.inductionOn w ?_
  intro W
  exact S.automorphism_transport alpha W

/-- Inner automorphisms do not change the block assigned to a weight
isomorphism class. -/
theorem isoClassBlock_conjugation (g : G)
    (w : IsoClass (p := p) (K := K) (G := G)) :
    S.isoClassBlock (g • w) = S.isoClassBlock w := by
  change S.isoClassBlock
      (rightTwistIsoClass (p := p) (K := K) (G := G)
        (MulAut.conj g⁻¹) w) = S.isoClassBlock w
  rw [S.isoClassBlock_rightTwist]
  exact S.inner_blocks_fixed g (S.isoClassBlock w)

/-- The induced ambient block of a literal character-weight conjugacy class.
Both quotient descents are constructed in the kernel. -/
def weightBlock : ConjugacyClass (p := p) (K := K) (G := G) → Block :=
  Quotient.lift S.isoClassBlock (by
    intro w w' h
    rcases h with ⟨g, rfl⟩
    exact S.isoClassBlock_conjugation g w')

@[simp]
theorem weightBlock_mkIsoClass
    (w : IsoClass (p := p) (K := K) (G := G)) :
    S.weightBlock (Quotient.mk'' w) = S.isoClassBlock w :=
  rfl

@[simp]
theorem weightBlock_mk (W : CharacterWeight p K G) :
    S.weightBlock (Quotient.mk'' (Quotient.mk'' W)) =
      S.operations.rawWeightBlock W :=
  rfl

/-- The constructed block assignment commutes with all automorphisms. -/
theorem weightBlock_transport (alpha : (MulAut G)ᵐᵒᵖ)
    (w : ConjugacyClass (p := p) (K := K) (G := G)) :
    S.weightBlock (alpha • w) = alpha • S.weightBlock w := by
  refine Quotient.inductionOn w ?_
  intro W
  exact S.isoClassBlock_rightTwist alpha.unop W

/-- The actual block assignment obtained from local block induction. -/
def equivariantBlockAssignment :
    EquivariantBlockAssignment
      (p := p) (K := K) (G := G) Block where
  blockOf := S.weightBlock
  map_smul := S.weightBlock_transport

@[simp]
theorem equivariantBlockAssignment_blockOf
    (w : ConjugacyClass (p := p) (K := K) (G := G)) :
    S.equivariantBlockAssignment.blockOf w = S.weightBlock w :=
  rfl

/-- The block fibre defined by local block induction. -/
abbrev Fibre (b : Block) := S.equivariantBlockAssignment.Fibre b

/-- The stabiliser action on a local-block-induction fibre acts on its
underlying literal character-weight conjugacy class. -/
@[simp]
theorem fibre_smul_val (b : Block)
    (alpha : MulAction.stabilizer (MulAut G)ᵐᵒᵖ b)
    (w : S.Fibre b) :
    ((alpha • w : S.Fibre b).1) =
      (alpha : (MulAut G)ᵐᵒᵖ) • w.1 :=
  rfl

end LocalBlockInductionSource

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
