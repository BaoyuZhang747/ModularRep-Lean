import ModularRep.PaperProofs.OddTwoGroupEquivWeightBlocks
import ModularRep.PaperProofs.TypeBLiteralBlockReindex
import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification

/-!
# Local block operations along a specified group equivalence

The target selectors, inflation, and complete catalogues are constructed
from the original operations. Each target subgroup is sent back through the
specified equivalence. Literal normalizer blocks retain their actual
primitive idempotents, and defined induction is transported through the
normalizer inclusion square.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBGroupEquivLocalBlockOperations

open ModularRep CharacterWeight
open TypeBLiteralBlockReindex
open TypeBCentralKernelSpinFibreIdentification

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A]
    (Q : Subgroup A) : Fintype Q := Fintype.ofFinite Q

section LiteralCatalogue

variable {k X Index : Type u} [Field k] [IsAlgClosed k]
  [Group X] [Fintype X] [Fintype Index]
  {blockIdempotent : Index → k[X]}
  (D : BlockIdempotentDecomposition blockIdempotent)
  (C : BlockCentralCharacterCatalogue D)
  [Fintype {b : k[X] // IsPrimitiveCentralIdempotent b}]

private theorem literalBlockInCenter (b : {b : k[X] // IsPrimitiveCentralIdempotent b}) :
    D.blockIdempotentInCenter (D.primitiveBlockEquiv.symm b) =
      (literalBlocks D).blockIdempotentInCenter b := by
  apply Subtype.ext
  change blockIdempotent (D.primitiveBlockEquiv.symm b) = b.1
  exact congrArg (fun c : {c : k[X] // IsPrimitiveCentralIdempotent c} => c.1)
    (D.primitiveBlockEquiv.apply_symm_apply b)

/-- Reindex the supplied catalogue by all its literal primitive blocks. -/
def literalCatalogue : BlockCentralCharacterCatalogue (literalBlocks D) where
  centralCharacter b := C.centralCharacter (D.primitiveBlockEquiv.symm b)
  delta_own b := by
    rw [← literalBlockInCenter D b]
    exact C.delta_own _
  delta_other b c hbc := by
    rw [← literalBlockInCenter D c]
    exact C.delta_other _ _ (fun h => hbc (D.primitiveBlockEquiv.symm.injective h))
  exhaustive := by
    intro lambda
    obtain ⟨i, hi⟩ := C.exhaustive lambda
    refine ⟨D.primitiveBlockEquiv i, ?_⟩
    change C.centralCharacter (D.primitiveBlockEquiv.symm (D.primitiveBlockEquiv i)) =
      lambda
    rw [Equiv.symm_apply_apply]
    exact hi

@[simp] theorem literalCatalogue_centralCharacter
    (b : {b : k[X] // IsPrimitiveCentralIdempotent b}) :
    (literalCatalogue D C).centralCharacter b =
      C.centralCharacter (D.primitiveBlockEquiv.symm b) := rfl

end LiteralCatalogue

variable {p : ℕ} {k K G H Block : Type u}
  [Field k] [Field K] [CharZero K]
  [Group G] [Fintype G] [Group H] [Fintype H]
  (OG : LocalBlockInductionOperations
    (p := p) (k := k) (K := K) (G := G) (Block := Block))
  (e : G ≃* H)

/-- Select the quotient block through the original own-character selector. -/
def localCharacterBlock (R : Subgroup H)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient R))
    (hchi : IsDefectZeroOrdinaryCharacter p chi) : LocalQuotientBlock (k := k) R :=
  (primitiveBlockEquiv (normalizerQuotientEquiv e.symm R)).symm
    (OG.localCharacterBlock (R.map e.symm.toMonoidHom)
      (OrdinaryIrreducibleCharacter.mapEquiv chi (normalizerQuotientEquiv e.symm R))
      (hchi.mapEquiv (normalizerQuotientEquiv e.symm R)))

/-- Inflate using the original quotient and normalizer primitive maps. -/
def inflateToNormalizer (R : Subgroup H) (b : LocalQuotientBlock (k := k) R) :
    InflatedNormalizerBlock (k := k) R :=
  (primitiveBlockEquiv (normalizerEquiv e.symm R)).symm
    (OG.inflateToNormalizer (R.map e.symm.toMonoidHom)
      (primitiveBlockEquiv (normalizerQuotientEquiv e.symm R) b))

private theorem localComposite_eq (V : CharacterWeight p K H) :
    inflateToNormalizer OG e V.subgroup
        (localCharacterBlock OG e V.subgroup V.localCharacter V.defectZero) =
      (primitiveBlockEquiv (normalizerEquiv e.symm V.subgroup)).symm
        (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG
          (V.mapGroupEquiv e.symm)) := by
  dsimp only [inflateToNormalizer, localCharacterBlock]
  rw [Equiv.apply_symm_apply]
  rfl

/-- The transported ambient catalogue keeps the original finite labels. -/
def ambientBlockData :
    letI : IsAlgClosed k := OG.isAlgClosed
    AmbientBlockCatalogueData (k := k) (G := H) (Block := Block) := by
  letI : IsAlgClosed k := OG.isAlgClosed
  letI : Fintype Block := OG.ambientBlockData.fintypeBlock
  exact {
    fintypeBlock := OG.ambientBlockData.fintypeBlock
    blockIdempotent := fun b =>
      MonoidAlgebra.domCongr k k e (OG.ambientBlockData.blockIdempotent b)
    blocks := OG.ambientBlockData.blocks.alongMulEquiv e
    catalogue := OG.ambientBlockData.catalogue.alongMulEquiv e }

/-- Every target normalizer catalogue is indexed by its literal primitives. -/
def inflatedNormalizerBlockData (R : Subgroup H) :
    letI : IsAlgClosed k := OG.isAlgClosed
    InflatedNormalizerBlockCatalogueData (k := k) R := by
  letI : IsAlgClosed k := OG.isAlgClosed
  let Q : Subgroup G := R.map e.symm.toMonoidHom
  let n : Subgroup.normalizer (R : Set H) ≃*
      Subgroup.normalizer (Q : Set G) := normalizerEquiv e.symm R
  let oldData : InflatedNormalizerBlockCatalogueData (k := k) Q :=
    OG.inflatedNormalizerBlockData Q
  letI : Fintype (InflatedNormalizerBlock (k := k) Q) := oldData.fintypeBlock
  let D := oldData.blocks.alongMulEquiv n.symm
  let C := oldData.catalogue.alongMulEquiv n.symm
  letI : Fintype (InflatedNormalizerBlock (k := k) R) := literalBlockFintype D
  exact {
    fintypeBlock := literalBlockFintype D
    blocks := literalBlocks D
    catalogue := literalCatalogue D C }

private theorem blockInductionDefined (V : CharacterWeight p K H) :
    letI : IsAlgClosed k := OG.isAlgClosed
    let data := inflatedNormalizerBlockData OG e V.subgroup
    letI : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) := data.fintypeBlock
    IsBlockInductionDefined (Subgroup.normalizer (V.subgroup : Set H))
      (data.catalogue.centralCharacter
        (inflateToNormalizer OG e V.subgroup
          (localCharacterBlock OG e V.subgroup V.localCharacter V.defectZero))) := by
  letI : IsAlgClosed k := OG.isAlgClosed
  let W : CharacterWeight p K G := V.mapGroupEquiv e.symm
  let n : Subgroup.normalizer (V.subgroup : Set H) ≃*
      Subgroup.normalizer (W.subgroup : Set G) :=
    normalizerEquiv e.symm V.subgroup
  let oldData : InflatedNormalizerBlockCatalogueData (k := k) W.subgroup :=
    OG.inflatedNormalizerBlockData W.subgroup
  let data : InflatedNormalizerBlockCatalogueData (k := k) V.subgroup :=
    inflatedNormalizerBlockData OG e V.subgroup
  letI : Fintype (InflatedNormalizerBlock (k := k) W.subgroup) := oldData.fintypeBlock
  letI : Fintype (InflatedNormalizerBlock (k := k) V.subgroup) := data.fintypeBlock
  have primitive : MonoidAlgebra.domCongr k k n.symm
        (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W).1 =
      (inflateToNormalizer OG e V.subgroup
        (localCharacterBlock OG e V.subgroup V.localCharacter V.defectZero)).1 := by
    exact (congrArg Subtype.val (localComposite_eq OG e V)).symm
  have character := centralCharacterAlongMulEquiv_eq_of_blockIdempotent
    n.symm oldData.catalogue data.catalogue
    (b := OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W)
    (b' := inflateToNormalizer OG e V.subgroup
      (localCharacterBlock OG e V.subgroup V.localCharacter V.defectZero)) (by
      apply Subtype.ext
      exact primitive)
  have square : e.toMonoidHom.comp (Subgroup.normalizer (W.subgroup : Set G)).subtype =
      (Subgroup.normalizer (V.subgroup : Set H)).subtype.comp n.symm.toMonoidHom := by
    ext x
    apply e.symm.injective
    change e.symm (e (x : G)) =
      e.symm ((n.symm x : Subgroup.normalizer (V.subgroup : Set H)) : H)
    have hx := congrArg Subtype.val (n.apply_symm_apply x)
    change e.symm ((n.symm x : Subgroup.normalizer (V.subgroup : Set H)) : H) =
      (x : G) at hx
    simpa only [MulEquiv.symm_apply_apply] using hx.symm
  have defined := isBlockInductionDefined_alongMulEquiv
    (Subgroup.normalizer (W.subgroup : Set G))
    (Subgroup.normalizer (V.subgroup : Set H)) e n.symm square
    (oldData.catalogue.centralCharacter
      (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W))
    (OG.blockInductionDefined W)
  rw [character] at defined
  exact defined

/-- Construct all target operations from the original operations and e. -/
def operations : LocalBlockInductionOperations
    (p := p) (k := k) (K := K) (G := H) (Block := Block) := by
  letI : IsAlgClosed k := OG.isAlgClosed
  exact {
    isAlgClosed := OG.isAlgClosed
    localCharacterBlock := localCharacterBlock OG e
    inflateToNormalizer := inflateToNormalizer OG e
    ambientBlockData := ambientBlockData OG e
    inflatedNormalizerBlockData := inflatedNormalizerBlockData OG e
    blockInductionDefined := blockInductionDefined OG e }

@[simp] theorem operations_ambientBlockIdempotent (b : Block) :
    letI : IsAlgClosed k := OG.isAlgClosed
    (operations OG e).ambientBlockData.blockIdempotent b =
      MonoidAlgebra.domCongr k k e (OG.ambientBlockData.blockIdempotent b) := rfl

/-- The own primitive block goes back through the exact normalizer map. -/
theorem ownNormalizerBlock_backward (V : CharacterWeight p K H) :
    primitiveBlockEquiv (normalizerEquiv e.symm V.subgroup)
        (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock (operations OG e) V) =
      OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG (V.mapGroupEquiv e.symm) := by
  let n : Subgroup.normalizer (V.subgroup : Set H) ≃*
      Subgroup.normalizer ((V.mapGroupEquiv e.symm).subgroup : Set G) :=
    normalizerEquiv e.symm V.subgroup
  let E : InflatedNormalizerBlock (k := k) V.subgroup ≃
      InflatedNormalizerBlock (k := k) (V.mapGroupEquiv e.symm).subgroup :=
    primitiveBlockEquiv n
  change E
      (inflateToNormalizer OG e V.subgroup
        (localCharacterBlock OG e V.subgroup V.localCharacter V.defectZero)) = _
  have composite : inflateToNormalizer OG e V.subgroup
      (localCharacterBlock OG e V.subgroup V.localCharacter V.defectZero) =
      E.symm (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG
        (V.mapGroupEquiv e.symm)) := localComposite_eq OG e V
  exact (congrArg E composite).trans (E.apply_symm_apply _)

private def normalizerBlockInAmbient {A : Type u} [Group A] [Fintype A]
    (O : LocalBlockInductionOperations
      (p := p) (k := k) (K := K) (G := A) (Block := Block))
    (W : CharacterWeight p K A) : k[A] :=
  MonoidAlgebra.mapDomain (Subgroup.normalizer (W.subgroup : Set A)).subtype
    (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock O W).1

private theorem normalizerAlgebra_square (W : CharacterWeight p K G)
    (b : k[Subgroup.normalizer (W.subgroup : Set G)]) :
    MonoidAlgebra.mapDomain
        (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype
        (MonoidAlgebra.domCongr k k (normalizerEquiv e W.subgroup) b) =
      MonoidAlgebra.domCongr k k e
        (MonoidAlgebra.mapDomain (Subgroup.normalizer (W.subgroup : Set G)).subtype b) := by
  let n : Subgroup.normalizer (W.subgroup : Set G) ≃*
      Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H) :=
    normalizerEquiv e W.subgroup
  change ((MonoidAlgebra.mapDomainAlgHom k k
      (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype).comp
      (MonoidAlgebra.mapDomainAlgHom k k n.toMonoidHom)) b =
    ((MonoidAlgebra.mapDomainAlgHom k k e.toMonoidHom).comp
      (MonoidAlgebra.mapDomainAlgHom k k
        (Subgroup.normalizer (W.subgroup : Set G)).subtype)) b
  calc
    _ = MonoidAlgebra.mapDomainAlgHom k k
        ((Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype.comp
          n.toMonoidHom) b :=
      congrArg (fun f : k[Subgroup.normalizer (W.subgroup : Set G)] →ₐ[k] k[H] => f b)
        (MonoidAlgebra.mapDomainAlgHom_comp (R := k) (A := k) n.toMonoidHom
          (Subgroup.normalizer ((W.mapGroupEquiv e).subgroup : Set H)).subtype).symm
    _ = MonoidAlgebra.mapDomainAlgHom k k
        (e.toMonoidHom.comp (Subgroup.normalizer (W.subgroup : Set G)).subtype) b :=
      congrArg
        (fun f : Subgroup.normalizer (W.subgroup : Set G) →* H =>
          MonoidAlgebra.mapDomainAlgHom k k f b)
        (OddTwoGroupEquivWeightBlocks.normalizer_inclusion_square e W).symm
    _ = _ :=
      congrArg (fun f : k[Subgroup.normalizer (W.subgroup : Set G)] →ₐ[k] k[H] => f b)
        (MonoidAlgebra.mapDomainAlgHom_comp (R := k) (A := k)
          (Subgroup.normalizer (W.subgroup : Set G)).subtype e.toMonoidHom)

/-- The forward primitive equation follows from the backward formula and
the existing inverse law for the actual raw weight map. -/
theorem ownNormalizerBlock_forward (W : CharacterWeight p K G) :
    MonoidAlgebra.domCongr k k (normalizerEquiv e W.subgroup)
        (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W).1 =
      (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock (operations OG e)
        (W.mapGroupEquiv e)).1 := by
  let V : CharacterWeight p K H := W.mapGroupEquiv e
  have backward := congrArg
    (fun b : InflatedNormalizerBlock (k := k) (V.mapGroupEquiv e.symm).subgroup =>
      MonoidAlgebra.mapDomain
        (Subgroup.normalizer ((V.mapGroupEquiv e.symm).subgroup : Set G)).subtype b.1)
    (ownNormalizerBlock_backward OG e V)
  have square := normalizerAlgebra_square (k := k) e.symm V
    (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock (operations OG e) V).1
  have ambientBackward : MonoidAlgebra.domCongr k k e.symm
      (normalizerBlockInAmbient (operations OG e) V) =
      normalizerBlockInAmbient OG (V.mapGroupEquiv e.symm) :=
    square.symm.trans backward
  have inverse : V.mapGroupEquiv e.symm = W := mapGroupEquiv_symm_mapGroupEquiv W e
  rw [inverse] at ambientBackward
  have ambientForward : MonoidAlgebra.domCongr k k e
      (normalizerBlockInAmbient OG W) =
      normalizerBlockInAmbient (operations OG e) V := by
    rw [← ambientBackward]
    exact (MonoidAlgebra.domCongr k k e).apply_symm_apply _
  apply MonoidAlgebra.mapDomain_injective
    (R := k)
    (f := fun x : Subgroup.normalizer (V.subgroup : Set H) => (x : H))
    Subtype.val_injective
  exact (normalizerAlgebra_square (k := k) e W
    (OddTwoGroupEquivWeightBlocks.ownNormalizerBlock OG W).1).trans ambientForward

/-- Both primitive dictionary fields are consequences of the constructed
operations. -/
theorem primitiveDictionary :
    OddTwoGroupEquivWeightBlocks.PrimitiveDictionary OG (operations OG e) e where
  ambient_primitive b := rfl
  normalizer_primitive W := ownNormalizerBlock_forward OG e W

end ModularRep.PaperProofs.TypeBGroupEquivLocalBlockOperations


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
