import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting

/-!
# Construct the block index from a full ordinary-series partition

Coverage, disjointness and constancy on an ordinary block determine a block
index. No block index is supplied. The specified specialization uses the SAME
ordinary selector and actual stable-reduction decomposition numbers.

The Brauer union is defined by a nonzero decomposition number. Its converse
identification retains the separate ordinary-existence-above hypothesis;
nonempty ordinary rows are not used as a substitute for nonempty columns.
The last inclusion square preserves actual Brauer generators and is ready
for reindexing individual integral-series maps.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBBroueMichelBlockIndex

universe u v w

section Partition

variable {X : Type u} {B : Type v} {I : Type w}
  (U : I → X → Prop) (blockOf : X → B)
  (blockSurj : Function.Surjective blockOf)
  (coverage : ∀ x, ∃ s, U s x)
  (blockClosed : ∀ s x y, blockOf x = blockOf y → U s x → U s y)

include blockSurj coverage blockClosed in
/-- Every specified block has a single candidate union containing all its
ordinary characters. Uniqueness is established from disjointness below. -/
theorem block_has_union (b : B) :
    ∃ s, ∀ x, blockOf x = b → U s x := by
  obtain ⟨x, hx⟩ := blockSurj b
  obtain ⟨s, hs⟩ := coverage x
  refine ⟨s, ?_⟩
  intro y hy
  exact blockClosed s x y (hx.trans hy.symm) hs

/-- The union index of a block, constructed from coverage and block closure. -/
def blockIndex (b : B) : I :=
  Classical.choose (block_has_union U blockOf blockSurj coverage blockClosed b)

/-- Every character of a block belongs to its constructed union. -/
theorem blockIndex_mem (b : B) (x : X) (hx : blockOf x = b) :
    U (blockIndex U blockOf blockSurj coverage blockClosed b) x :=
  Classical.choose_spec (block_has_union U blockOf blockSurj coverage blockClosed b) x hx

variable (disjoint : ∀ s t x, U s x → U t x → s = t)

include disjoint in
/-- Exact membership in the ordinary union is equality with the constructed
block index. The index is not part of the input partition. -/
theorem union_iff_blockIndex (s : I) (x : X) :
    U s x ↔ blockIndex U blockOf blockSurj coverage blockClosed (blockOf x) = s := by
  have hx := blockIndex_mem U blockOf blockSurj coverage blockClosed (blockOf x) x rfl
  constructor
  · intro hs
    exact disjoint _ s x hx hs
  · intro hs
    exact hs ▸ hx

include disjoint in
/-- The construction is independent of the choices used to select block
representatives or union witnesses. -/
theorem blockIndex_unique (index : B → I)
    (hindex : ∀ x, U (index (blockOf x)) x) :
    blockIndex U blockOf blockSurj coverage blockClosed = index := by
  funext b
  obtain ⟨x, hx⟩ := blockSurj b
  have h := (union_iff_blockIndex U blockOf blockSurj coverage blockClosed disjoint
    (index (blockOf x)) x).mp (hindex x)
  simpa only [hx] using h

end Partition

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBOrdinaryBlockSplitting
open TypeBRationalSeriesBasicSet
open TypeBIntegralSeriesSplitting (brauerIndex)

section Physical

variable {p : ℕ} {K O k G I : Type u}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k p] [IsAlgClosed k] [Group G] [Finite G]
  (Msys : ModularSystem p K O k)
  (iota : PrimeRegularRootEmbedding p k K G)
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  [Fintype (LiteralPrimitiveBlock k G)]
  (blocks : BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k G => b.val))
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (ordinary : OrdinaryBlockSource Msys iota hinj blocks)

/-- Specified block soundness at the actual nonnegative decomposition number. -/
theorem block_of_nonzero_decompositionNumber (chi : Irr K G) (phi : IBr iota)
    (h : decompositionNumber Msys iota chi phi ≠ 0) :
    irreducibleBrauerCharacterBlock iota hinj blocks phi =
      ordinary.physical.ordinaryBlock chi := by
  have hb := (ordinary.physical.support_nonempty_and_sound chi).2 phi h
  have heq : literalBrauerBlock iota hinj blocks phi =
      irreducibleBrauerCharacterBlock iota hinj blocks phi := by
    apply Subtype.ext
    rfl
  exact heq.symm.trans hb

variable (U : I → Irr K G → Prop)
  (coverage : ∀ chi, ∃ s, U s chi)
  (blockClosed : ∀ s chi psi,
    ordinary.physical.ordinaryBlock chi = ordinary.physical.ordinaryBlock psi →
      U s chi → U s psi)

/-- The block index of the SAME literal ordinary selector. Its surjectivity
comes from the existing specified source, not a duplicate assumption. -/
def physicalBlockIndex : LiteralPrimitiveBlock k G → I :=
  blockIndex U ordinary.physical.ordinaryBlock ordinary.physical.ordinaryBlock_surjective
    coverage blockClosed

variable (disjoint : ∀ s t chi, U s chi → U t chi → s = t)

include disjoint in
/-- The full ordinary union is precisely a fibre of the constructed specified
block index. -/
theorem ordinaryUnion_iff_index (s : I) (chi : Irr K G) :
    U s chi ↔ physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed
      (ordinary.physical.ordinaryBlock chi) = s :=
  union_iff_blockIndex U ordinary.physical.ordinaryBlock
    ordinary.physical.ordinaryBlock_surjective coverage blockClosed disjoint s chi

/-- The actual Brauer union: membership is witnessed by a nonzero specified
decomposition number of an ordinary character in the full ordinary union. -/
def brauerUnion (s : I) (phi : IBr iota) : Prop :=
  ∃ chi : Irr K G, U s chi ∧ decompositionNumber Msys iota chi phi ≠ 0

/-- Keep the actual Brauer character as the value of the membership subtype. -/
abbrev BrauerUnion (s : I) := {phi : IBr iota // brauerUnion Msys iota U s phi}

/-- Inclusion in the free integral group on the SAME actual Brauer characters. -/
def brauerUnionInclusion (s : I) :
    MonoidAlgebra ℤ (BrauerUnion Msys iota U s) →ₗ[ℤ] MonoidAlgebra ℤ (IBr iota) :=
  MonoidAlgebra.mapDomainLinearMap ℤ ℤ Subtype.val

@[simp]
theorem brauerUnionInclusion_single (s : I) (phi : BrauerUnion Msys iota U s) :
    brauerUnionInclusion Msys iota U s (MonoidAlgebra.single phi 1) =
      MonoidAlgebra.single phi.val 1 := by
  simp only [brauerUnionInclusion, MonoidAlgebra.mapDomainLinearMap_single]

variable (existsAbove : ∀ phi : IBr iota, ∃ chi : Irr K G,
  decompositionNumber Msys iota chi phi ≠ 0)

include disjoint existsAbove in
/-- The specified Brauer union equals the constructed block-index fibre.
Existence above each Brauer character is the separate nonzero-column input. -/
theorem brauerUnion_iff_index (s : I) (phi : IBr iota) :
    brauerUnion Msys iota U s phi ↔
      brauerIndex iota hinj blocks
        (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed) phi = s := by
  constructor
  · rintro ⟨chi, hchi, hn⟩
    have hb := block_of_nonzero_decompositionNumber Msys iota hinj blocks ordinary chi phi hn
    have hi := (ordinaryUnion_iff_index Msys iota hinj blocks ordinary U coverage blockClosed
      disjoint s chi).mp hchi
    exact (congrArg
      (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed) hb).trans hi
  · intro hphi
    obtain ⟨chi, hn⟩ := existsAbove phi
    refine ⟨chi, ?_, hn⟩
    apply (ordinaryUnion_iff_index Msys iota hinj blocks ordinary U coverage blockClosed
      disjoint s chi).mpr
    have hb := block_of_nonzero_decompositionNumber Msys iota hinj blocks ordinary chi phi hn
    exact (congrArg
      (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed) hb).symm.trans hphi

/-- Reindex by the proven equality of membership predicates, fixing the
actual Brauer character in both directions. -/
def brauerUnionEquivFibre (s : I) :
    BrauerUnion Msys iota U s ≃
      SeriesFibre (brauerIndex iota hinj blocks
        (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed)) s where
  toFun phi := ⟨phi.val, (brauerUnion_iff_index Msys iota hinj blocks ordinary U coverage
    blockClosed disjoint existsAbove s phi.val).mp phi.property⟩
  invFun phi := ⟨phi.val, (brauerUnion_iff_index Msys iota hinj blocks ordinary U coverage
    blockClosed disjoint existsAbove s phi.val).mpr phi.property⟩
  left_inv phi := by apply Subtype.ext; rfl
  right_inv phi := by apply Subtype.ext; rfl

@[simp]
theorem brauerUnionEquivFibre_val (s : I) (phi : BrauerUnion Msys iota U s) :
    (brauerUnionEquivFibre Msys iota hinj blocks ordinary U coverage blockClosed disjoint
      existsAbove s phi).val = phi.val := rfl

@[simp]
theorem brauerUnionEquivFibre_symm_val (s : I)
    (phi : SeriesFibre (brauerIndex iota hinj blocks
      (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed)) s) :
    ((brauerUnionEquivFibre Msys iota hinj blocks ordinary U coverage blockClosed disjoint
      existsAbove s).symm phi).val = phi.val := rfl

variable [Fintype I]

/-- Individual integral-series maps can be reindexed through the constructed
block index without changing their inclusion or decomposition equation. -/
theorem brauerUnionInclusion_reindex (s : I)
    (v : MonoidAlgebra ℤ (BrauerUnion Msys iota U s)) :
    seriesInclusion (brauerIndex iota hinj blocks
        (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed)) s
      (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
        (brauerUnionEquivFibre Msys iota hinj blocks ordinary U coverage blockClosed disjoint
          existsAbove s) v) = brauerUnionInclusion Msys iota U s v := by
  have h :
      (seriesInclusion (brauerIndex iota hinj blocks
          (physicalBlockIndex Msys iota hinj blocks ordinary U coverage blockClosed)) s).comp
        (MonoidAlgebra.mapDomainLinearEquiv ℤ ℤ
          (brauerUnionEquivFibre Msys iota hinj blocks ordinary U coverage blockClosed disjoint
            existsAbove s)).toLinearMap = brauerUnionInclusion Msys iota U s := by
    apply MonoidAlgebra.lhom_ext'
    intro phi
    apply LinearMap.ext_ring
    simp only [MonoidAlgebra.lsingle_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      MonoidAlgebra.mapDomainLinearEquiv_single, seriesInclusion_single,
      brauerUnionEquivFibre_val, brauerUnionInclusion_single]
  exact DFunLike.congr_fun h v

end Physical

end ModularRep.PaperProofs.TypeBBroueMichelBlockIndex


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
