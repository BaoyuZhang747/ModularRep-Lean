import ModularRep.PaperProofs.TypeBRankThreeProductBlockCatalogue
import ModularRep.PaperProofs.TypeBRankThreeProductBlockInduction
import ModularRep.PaperProofs.TypeBRankThreeProductOrdinaryBlockSupport
import ModularRep.PaperProofs.TypeBGroupEquivLocalBlockOperations

/-!
# The block of the actual raw product weight

All tuple catalogues below are constructed from the supplied local operations.
The own-normalizer primitive equation comes from the SAME specified ordinary
inflation membership and ordinary product support. Factor block inductions
then give the product induction on the literal subgroup product. The actual
normalizer equality and uniqueness of induced blocks give the final primitive
equation. No ambient weight-block assignment or product induction is supplied
as a source, and no ordinary algebraic closure is required.
-/

noncomputable section
set_option autoImplicit false

open scoped BigOperators MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeProductRawWeightBlock

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreeProductRadical TypeBRankThreeProductRawWeight
open TypeBRankThreeProductBlockSource TypeBRankThreeProductBlockCatalogue
open TypeBRankThreeProductBlockInduction TypeBRankThreeProductOrdinaryBlockSupport
open TypeBLocalPhysicalBlockBinding TypeBLiteralBlockReindex
open TypeBGroupEquivLocalBlockOperations OddTwoGroupEquivWeightBlocks

variable {I k : Type} [Fintype I] [Field k]

local instance indexDecidableEq : DecidableEq I := Classical.decEq I

local instance subgroupFintype {G : Type} [Group G] [Finite G]
    (S : Subgroup G) : Fintype S := Fintype.ofFinite S

section Subgroups

variable (H : I → Type) [∀ i, Group (H i)] [∀ i, Fintype (H i)]
variable (S : ∀ i, Subgroup (H i))

/-- The subgroup-product coordinates retain the original ambient entries. -/
def subgroupPiEquiv : Subgroup.pi Set.univ S ≃* (∀ i, S i) where
  toFun x i := subgroupCoordinate H S x i
  invFun x := ⟨fun i => (x i).val,
    (Subgroup.mem_pi Set.univ).mpr (fun i _ => (x i).property)⟩
  left_inv x := Subtype.ext rfl
  right_inv x := funext (fun i => Subtype.ext rfl)
  map_mul' _ _ := rfl

/-- The fixed coefficient product on the subgroup is the transported product. -/
theorem subgroup_product_idempotent
    (b : ∀ i, LiteralPrimitiveBlock k (S i)) :
    MonoidAlgebra.domCongr k k (subgroupPiEquiv H S).symm
        (productIdempotent (fun i => S i) b) =
      subgroupCoefficientProduct H S (fun i => (b i).val) := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  rw [MonoidAlgebra.coeff_domCongr, productIdempotent_apply,
    subgroupCoefficientProduct_coeff]
  rfl

variable (Q : ∀ i, Subgroup (H i))

/-- The normalizer equality is used as an identity on the ambient group. -/
def normalizerProductEquiv :
    Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i)) ≃*
      Subgroup.pi Set.univ (fun i => Subgroup.normalizer (Q i : Set (H i))) :=
  MulEquiv.subgroupCongr (normalizer_pi H Q)

theorem normalizerProduct_inclusion_square :
    (MulEquiv.refl (∀ i, H i)).toMonoidHom.comp
        (Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i))).subtype =
      (Subgroup.pi Set.univ (fun i => Subgroup.normalizer (Q i : Set (H i)))).subtype.comp
        (normalizerProductEquiv H Q).toMonoidHom := by
  ext x
  rfl

/-- The two normalizer coordinate descriptions have the same original values. -/
theorem normalizerProduct_coordinate (x : Subgroup.normalizer
    (Subgroup.pi Set.univ Q : Set (∀ i, H i))) :
    subgroupPiEquiv H (fun i => Subgroup.normalizer (Q i : Set (H i)))
        (normalizerProductEquiv H Q x) = normalizerPiEquiv H Q x := by
  funext i
  apply Subtype.ext
  rfl

/-- A primitive equation in coordinate normalizers gives the actual subgroup equation. -/
theorem normalizer_primitive_to_subgroup
    (v : k[Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i))])
    (b : ∀ i, LiteralPrimitiveBlock k (Subgroup.normalizer (Q i : Set (H i))))
    (h : MonoidAlgebra.domCongr k k (normalizerPiEquiv H Q) v =
      productIdempotent (fun i => Subgroup.normalizer (Q i : Set (H i))) b) :
    MonoidAlgebra.domCongr k k (normalizerProductEquiv H Q) v =
      subgroupCoefficientProduct H
        (fun i => Subgroup.normalizer (Q i : Set (H i))) (fun i => (b i).val) := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun z : k[∀ i, Subgroup.normalizer (Q i : Set (H i))] => z.coeff
    (subgroupPiEquiv H (fun i => Subgroup.normalizer (Q i : Set (H i))) x)) h
  rw [MonoidAlgebra.coeff_domCongr, productIdempotent_apply] at hx
  rw [MonoidAlgebra.coeff_domCongr, subgroupCoefficientProduct_coeff]
  exact hx

end Subgroups

section CatalogueIdentity

variable {G B : Type} [Group G] [Fintype G] [Fintype B] [IsAlgClosed k]
variable {b c : B → k[G]}

/-- A proved equality of idempotent functions changes only the displayed indexing formula. -/
private def catalogueOfIdempotentEq
    (D : BlockIdempotentDecomposition b) (E : BlockIdempotentDecomposition c)
    (C : BlockCentralCharacterCatalogue D) (h : b = c) :
    BlockCentralCharacterCatalogue E := by
  subst c
  exact C

end CatalogueIdentity

section Operations

variable {p : ℕ} {K O BP : Type} {B : I → Type}
variable [Field K] [CharZero K] [CommRing O] [IsDomain O] [Algebra O K]
variable [CharP k p] [IsAlgClosed k]
variable (Msys : ModularSystem p K O k)
variable (H : I → Type) [∀ i, Group (H i)] [∀ i, Fintype (H i)]
variable [HasEnoughRootsOfUnity K (Nat.card (∀ i, H i))]

local instance factorOrdinaryRoots (i : I) :
    HasEnoughRootsOfUnity K (Nat.card (H i)) :=
  HasEnoughRootsOfUnity.of_dvd K
    (Subgroup.card_dvd_of_surjective (projection H i) (fun x =>
      ⟨Pi.mulSingle i x, Pi.mulSingle_eq_same i x⟩))

variable (OP : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := (∀ i, H i)) (Block := BP))
variable (Oi : ∀ i, LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := H i) (Block := B i))
variable (W : ∀ i, CharacterWeight p K (H i))

@[instance_reducible] def ambientIndexFintype : Fintype BP := OP.ambientBlockData.fintypeBlock
@[instance_reducible] def factorIndexFintype (i : I) : Fintype (B i) :=
  (Oi i).ambientBlockData.fintypeBlock
@[instance_reducible] def factorPrimitiveFintype (i : I) : Fintype (LiteralPrimitiveBlock k (H i)) :=
  letI := (Oi i).ambientBlockData.fintypeBlock
  literalBlockFintype (Oi i).ambientBlockData.blocks
@[instance_reducible] def localPrimitiveFintype (i : I) :
    Fintype (LiteralPrimitiveBlock k (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
  ((Oi i).inflatedNormalizerBlockData (W i).subgroup).fintypeBlock
@[instance_reducible] def productLocalPrimitiveFintype : Fintype (LiteralPrimitiveBlock k
    (Subgroup.normalizer
      (Subgroup.pi Set.univ (fun i => (W i).subgroup) : Set (∀ i, H i)))) :=
  (OP.inflatedNormalizerBlockData
    (Subgroup.pi Set.univ (fun i => (W i).subgroup))).fintypeBlock

/-- The factor ambient catalogue is the supplied one in literal primitive labels. -/
def factorAmbientBlocks (i : I) :
  letI := (Oi i).ambientBlockData.fintypeBlock
  letI := factorPrimitiveFintype H Oi i
  BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (H i) => b.val) := by
  letI := (Oi i).ambientBlockData.fintypeBlock
  letI := factorPrimitiveFintype H Oi i
  exact literalBlocks (Oi i).ambientBlockData.blocks

def factorAmbientCatalogue (i : I) :
  letI := (Oi i).ambientBlockData.fintypeBlock
  letI := factorPrimitiveFintype H Oi i
  BlockCentralCharacterCatalogue (factorAmbientBlocks H Oi i) := by
  letI := (Oi i).ambientBlockData.fintypeBlock
  letI := factorPrimitiveFintype H Oi i
  exact literalCatalogue (Oi i).ambientBlockData.blocks (Oi i).ambientBlockData.catalogue

variable (primH : PrimitiveProductSource (k := k) H)
variable (primN : PrimitiveProductSource (k := k)
  (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i))))

/-- The local product catalogue before returning from coordinate normalizers. -/
def coordinateLocalCatalogue :=
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  letI := productLocalPrimitiveFintype H OP W
  productTupleCatalogue
    (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i))) primN
    ((OP.inflatedNormalizerBlockData
      (Subgroup.pi Set.univ (fun i => (W i).subgroup))).blocks.alongMulEquiv
        (normalizerPiEquiv H (fun i => (W i).subgroup)))
    ((OP.inflatedNormalizerBlockData
      (Subgroup.pi Set.univ (fun i => (W i).subgroup))).catalogue.alongMulEquiv
        (normalizerPiEquiv H (fun i => (W i).subgroup)))

/-- The transported tuple decomposition has the prescribed subgroup coefficients. -/
def subgroupTupleBlocks :
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  BlockIdempotentDecomposition
    (fun b : ∀ i, LiteralPrimitiveBlock k
        (Subgroup.normalizer ((W i).subgroup : Set (H i))) =>
      subgroupCoefficientProduct H
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))
        (fun i => (b i).val)) := by
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  letI := productLocalPrimitiveFintype H OP W
  have D := (productTupleBlocks
    (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i))) primN
    ((OP.inflatedNormalizerBlockData
      (Subgroup.pi Set.univ (fun i => (W i).subgroup))).blocks.alongMulEquiv
        (normalizerPiEquiv H (fun i => (W i).subgroup)))).alongMulEquiv
      (subgroupPiEquiv H
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))).symm
  simpa only [subgroup_product_idempotent] using D

/-- The subgroup catalogue is transported from the SAME actual OP local catalogue. -/
def subgroupTupleCatalogue :
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  BlockCentralCharacterCatalogue
    (subgroupTupleBlocks H OP Oi W primN) := by
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  letI := productLocalPrimitiveFintype H OP W
  let D := (productTupleBlocks
    (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i))) primN
    ((OP.inflatedNormalizerBlockData
      (Subgroup.pi Set.univ (fun i => (W i).subgroup))).blocks.alongMulEquiv
        (normalizerPiEquiv H (fun i => (W i).subgroup)))).alongMulEquiv
      (subgroupPiEquiv H
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))).symm
  exact catalogueOfIdempotentEq D (subgroupTupleBlocks H OP Oi W primN)
    ((coordinateLocalCatalogue H OP Oi W primN).alongMulEquiv
      (subgroupPiEquiv H
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))).symm)
    (funext (subgroup_product_idempotent H
      (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))))

/-- The factor induction uses the operations' own selected block, in literal coordinates. -/
theorem factor_induces (i : I) :
  letI := (Oi i).ambientBlockData.fintypeBlock
  letI := factorPrimitiveFintype H Oi i
  letI := localPrimitiveFintype H Oi W i
  BlockInducesTo (Subgroup.normalizer ((W i).subgroup : Set (H i)))
      ((Oi i).inflatedNormalizerBlockData (W i).subgroup).catalogue
      (factorAmbientCatalogue H Oi i)
      (ownNormalizerBlock (Oi i) (W i))
      ((Oi i).ambientBlockData.blocks.primitiveBlockEquiv ((Oi i).rawWeightBlock (W i))) := by
  letI := (Oi i).ambientBlockData.fintypeBlock
  letI := factorPrimitiveFintype H Oi i
  letI := localPrimitiveFintype H Oi W i
  unfold BlockInducesTo
  change ∃ hdefined, inducedCentralCharacter _ _ hdefined =
    (literalCatalogue (Oi i).ambientBlockData.blocks
      (Oi i).ambientBlockData.catalogue).centralCharacter
        ((Oi i).ambientBlockData.blocks.primitiveBlockEquiv ((Oi i).rawWeightBlock (W i)))
  rw [literalCatalogue_centralCharacter, Equiv.symm_apply_apply]
  exact inducedBlock_spec
    (Subgroup.normalizer ((W i).subgroup : Set (H i)))
    ((Oi i).inflatedNormalizerBlockData (W i).subgroup).catalogue
    (Oi i).ambientBlockData.catalogue (ownNormalizerBlock (Oi i) (W i))
    ((Oi i).blockInductionDefined (W i))

variable (center : CenterProductSource (k := k) H
  (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i))))
variable (dictionary :
  letI := ambientIndexFintype H OP
  letI : ∀ i, Fintype (B i) := factorIndexFintype H Oi
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k (H i)) :=
    factorPrimitiveFintype H Oi
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  letI := productLocalPrimitiveFintype H OP W
  CatalogueProductSource H
  (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))
  (factorAmbientBlocks H Oi)
  (fun i => ((Oi i).inflatedNormalizerBlockData (W i).subgroup).blocks)
  (productTupleBlocks H primH OP.ambientBlockData.blocks)
  (subgroupTupleBlocks H OP Oi W primN)
  (factorAmbientCatalogue H Oi)
  (fun i => ((Oi i).inflatedNormalizerBlockData (W i).subgroup).catalogue)
  (productTupleCatalogue H primH OP.ambientBlockData.blocks OP.ambientBlockData.catalogue)
  (subgroupTupleCatalogue H OP Oi W primN) center)

variable (hp : Nat.Prime p)
variable (ordinaryQuotients : TypeBRankThreeProductOrdinarySource.ExternalProductSource
  (fun i => NormalizerQuotient ((W i).subgroup)) p hp
  (quotientProductRoots (K := K) H (fun i => (W i).subgroup)))
variable (ordinaryP : ∀ Q : Subgroup (∀ i, H i), NormalizerOrdinarySource Msys OP Q)
variable (ordinaryI : ∀ i, ∀ Q : Subgroup (H i), NormalizerOrdinarySource Msys (Oi i) Q)
variable (membershipP : OrdinaryInflationMembership Msys OP ordinaryP)
variable (membershipI : ∀ i, OrdinaryInflationMembership Msys (Oi i) (ordinaryI i))

include dictionary membershipP membershipI in
/-- The ambient primitive is derived by product induction and the uniqueness in OP. -/
theorem rawWeightBlock_primitive
    (support :
      letI := normalizerOrdinaryRoots (K := K)
        (Subgroup.pi Set.univ (fun i => (W i).subgroup))
      letI : ∀ i, HasEnoughRootsOfUnity K
          (Nat.card (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
        fun i => normalizerOrdinaryRoots (K := K) (W i).subgroup
      letI : ∀ i, Fintype (LiteralPrimitiveBlock k
          (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
        localPrimitiveFintype H Oi W
      letI := productLocalPrimitiveFintype H OP W
      OrdinaryProductBlockSource Msys
        (Subgroup.normalizer
          (Subgroup.pi Set.univ (fun i => (W i).subgroup) : Set (∀ i, H i)))
        (fun i => Subgroup.normalizer ((W i).subgroup : Set (H i)))
        (normalizerPiEquiv H (fun i => (W i).subgroup))
        (OP.inflatedNormalizerBlockData
          (Subgroup.pi Set.univ (fun i => (W i).subgroup))).blocks
        (fun i => ((Oi i).inflatedNormalizerBlockData (W i).subgroup).blocks)
        (ordinaryP (Subgroup.pi Set.univ (fun i => (W i).subgroup)))
        (fun i => ordinaryI i (W i).subgroup)) :
  letI := ambientIndexFintype H OP
  letI : ∀ i, Fintype (B i) := factorIndexFintype H Oi
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k (H i)) :=
    factorPrimitiveFintype H Oi
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  letI := productLocalPrimitiveFintype H OP W
  OP.ambientBlockData.blocks.primitiveBlockEquiv
        (OP.rawWeightBlock (rawProduct H hp W ordinaryQuotients)) =
      productBlock H primH (fun i =>
        (Oi i).ambientBlockData.blocks.primitiveBlockEquiv ((Oi i).rawWeightBlock (W i))) := by
  letI := ambientIndexFintype H OP
  letI : ∀ i, Fintype (B i) := factorIndexFintype H Oi
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k (H i)) :=
    factorPrimitiveFintype H Oi
  letI : ∀ i, Fintype (LiteralPrimitiveBlock k
      (Subgroup.normalizer ((W i).subgroup : Set (H i)))) :=
    localPrimitiveFintype H Oi W
  letI := productLocalPrimitiveFintype H OP W
  let V := rawProduct H hp W ordinaryQuotients
  let Q := fun i => (W i).subgroup
  let N := Subgroup.normalizer (Subgroup.pi Set.univ Q : Set (∀ i, H i))
  let S := fun i => Subgroup.normalizer (Q i : Set (H i))
  let T := Subgroup.pi Set.univ S
  let b := fun i => ownNormalizerBlock (Oi i) (W i)
  let B0 := fun i =>
    (Oi i).ambientBlockData.blocks.primitiveBlockEquiv ((Oi i).rawWeightBlock (W i))
  let target := productTupleLabelEquiv H primH OP.ambientBlockData.blocks B0
  have own := ownNormalizerBlock_product Msys H hp W ordinaryQuotients
    OP Oi ordinaryP ordinaryI membershipP membershipI support
  have ownSubgroup := normalizer_primitive_to_subgroup H Q
    (ownNormalizerBlock OP V).val b own
  have localForward : centralCharacterAlongMulEquiv (normalizerProductEquiv H Q)
      ((OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue.centralCharacter
        (ownNormalizerBlock OP V)) =
      (subgroupTupleCatalogue H OP Oi W primN).centralCharacter b := by
    apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
      (normalizerProductEquiv H Q)
      (OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue
      (subgroupTupleCatalogue H OP Oi W primN)
    apply Subtype.ext
    exact ownSubgroup
  have productInduction := blockInducesTo_product H S
    (factorAmbientBlocks H Oi)
    (fun i => ((Oi i).inflatedNormalizerBlockData (W i).subgroup).blocks)
    (productTupleBlocks H primH OP.ambientBlockData.blocks)
    (subgroupTupleBlocks H OP Oi W primN)
    (factorAmbientCatalogue H Oi)
    (fun i => ((Oi i).inflatedNormalizerBlockData (W i).subgroup).catalogue)
    (productTupleCatalogue H primH OP.ambientBlockData.blocks OP.ambientBlockData.catalogue)
    (subgroupTupleCatalogue H OP Oi W primN) center dictionary b B0
    (factor_induces H Oi W)
  have localBackward : centralCharacterAlongMulEquiv (normalizerProductEquiv H Q).symm
      ((subgroupTupleCatalogue H OP Oi W primN).centralCharacter b) =
      (OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue.centralCharacter
        (ownNormalizerBlock OP V) := by
    rw [← localForward]
    ext z
    change (OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue.centralCharacter
        (ownNormalizerBlock OP V)
        ((centerDomCongr (k := k) (normalizerProductEquiv H Q)).symm
          (centerDomCongr (k := k) (normalizerProductEquiv H Q) z)) = _
    rw [AlgEquiv.symm_apply_apply]
  have ambientBackward : centralCharacterAlongMulEquiv (MulEquiv.refl (∀ i, H i))
      ((productTupleCatalogue H primH OP.ambientBlockData.blocks
        OP.ambientBlockData.catalogue).centralCharacter B0) =
      OP.ambientBlockData.catalogue.centralCharacter target := by
    apply centralCharacterAlongMulEquiv_eq_of_blockIdempotent
      (MulEquiv.refl (∀ i, H i))
      (productTupleCatalogue H primH OP.ambientBlockData.blocks OP.ambientBlockData.catalogue)
      OP.ambientBlockData.catalogue
    apply Subtype.ext
    change MonoidAlgebra.domCongr k k (MulEquiv.refl (∀ i, H i))
      (productIdempotent H B0) = OP.ambientBlockData.blockIdempotent target
    rw [MonoidAlgebra.domCongr_refl]
    change productIdempotent H B0 = OP.ambientBlockData.blockIdempotent target
    exact (productTupleLabelEquiv_idempotent H primH OP.ambientBlockData.blocks B0).symm
  have square : (MulEquiv.refl (∀ i, H i)).toMonoidHom.comp T.subtype =
      N.subtype.comp (normalizerProductEquiv H Q).symm.toMonoidHom := by
    ext x
    rfl
  have actualInduction := blockInducesTo_alongMulEquiv T N
    (MulEquiv.refl (∀ i, H i)) (normalizerProductEquiv H Q).symm square
    (subgroupTupleCatalogue H OP Oi W primN)
    (productTupleCatalogue H primH OP.ambientBlockData.blocks OP.ambientBlockData.catalogue)
    (OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue
    OP.ambientBlockData.catalogue localBackward ambientBackward productInduction
  have unique := eq_inducedBlock_of_blockInducesTo N
    (OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue
    OP.ambientBlockData.catalogue (ownNormalizerBlock OP V)
    (OP.blockInductionDefined V) actualInduction
  have assignment : OP.rawWeightBlock V = target := by
    change inducedBlock N
      (OP.inflatedNormalizerBlockData (Subgroup.pi Set.univ Q)).catalogue
      OP.ambientBlockData.catalogue (ownNormalizerBlock OP V)
      (OP.blockInductionDefined V) = target
    exact unique.symm
  rw [assignment]
  exact OP.ambientBlockData.blocks.primitiveBlockEquiv.apply_symm_apply
    (productBlock H primH B0)

end Operations

end ModularRep.PaperProofs.TypeBRankThreeProductRawWeightBlock


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
