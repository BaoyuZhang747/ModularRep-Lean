import ModularRep.PaperProofs.TypeBRankThreeMoritaFiniteTensor
import ModularRep.PaperProofs.TypeBRankThreeMoritaDiagonal
import Mathlib.RepresentationTheory.Induced
import Mathlib.Algebra.Group.Center
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Uniform sources for the literal induced Morita construction

The tensor functor and the induced representation are fixed constructions.
The routine support, finiteness and restriction square are separate E1
principles. The degree-zero Marcus consequence is a one-way E2 principle
at the fixed coefficient field. Its specified coefficient and cohomology
interpretations remain explicit in the accompanying input contract.

Right support uses the genuine opposite action without inversion. Only
the previously defined balancing action uses the inverse. No chosen simple
character, field fixer, or final criterion occurs in these sources.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaSources

open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaDiagonal

universe u

variable {k G L : Type u} [CommRing k] [Group G] [Group L]

/-- The given left group algebra element acts as the identity on M. -/
def LeftSupport (M : Rep.{u} k (G × Lᵐᵒᵖ)) (eG : k[G]) : Prop :=
  ∀ m : M, eG.coeff.sum (fun g c => c • M.ρ (g, 1) m) = m

/-- Genuine right support: the coefficient at l acts by op l, not op of its inverse. -/
def RightSupport (M : Rep.{u} k (G × Lᵐᵒᵖ)) (eL : k[L]) : Prop :=
  ∀ m : M, eL.coeff.sum (fun l c => c • M.ρ (1, MulOpposite.op l) m) = m

/-- The same algebra element in the actual split overgroup. -/
def inlImage {Q : Type u} [Group Q] (aG : Q →* MulAut G)
    (eG : k[G]) : k[G ⋊[aG] Q] :=
  MonoidAlgebra.mapDomainRingHom k
    (SemidirectProduct.inl : G →* G ⋊[aG] Q) eG

/-- E1: the actual diagonal induction of a finite module is finite. -/
def FiniteInductionPrinciple (k : Type u) [Field k] : Prop :=
  ∀ {G L Q : Type u} [Group G] [Group L] [Group Q]
    [Finite G] [Finite L] [Finite Q]
    (aG : Q →* MulAut G) (aL : Q →* MulAut L)
    (M' : Rep.{u} k (D aG aL)) [Module.Finite k M'],
    Module.Finite k (Rep.ind (D aG aL).subtype M')

/-- E1: the literal left support descends to every balanced tensor output. -/
def TensorSupportPrinciple (k : Type u) [Field k] : Prop :=
  ∀ {G L : Type u} [Group G] [Group L]
    (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (eG : k[G]),
    LeftSupport M eG →
      ∀ V : FDRep.{u} k L, supported eG (tensorFDObj M V)

/-- E1: invariant central support passes to this actual induced pair representation. -/
def InducedSupportPrinciple (k : Type u) [Field k] : Prop :=
  ∀ {G L Q : Type u} [Group G] [Group L] [Group Q]
    [Finite G] [Finite L] [Finite Q]
    (aG : Q →* MulAut G) (aL : Q →* MulAut L)
    (eG : k[G]) (eL : k[L]),
    IsMulCentral eG → IsIdempotentElem eG →
    IsMulCentral eL → IsIdempotentElem eL →
    (∀ q : Q, MonoidAlgebra.mapDomainRingEquiv k (aG q) eG = eG) →
    (∀ q : Q, MonoidAlgebra.mapDomainRingEquiv k (aL q) eL = eL) →
    ∀ (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
      (M' : Rep.{u} k (D aG aL)) [Module.Finite k M'],
      LeftSupport M eG → RightSupport M eL →
      (Rep.res (baseEmbedding aG aL) M' ≅ M) →
      LeftSupport (Rep.ind (D aG aL).subtype M') (inlImage aG eG) ∧
        RightSupport (Rep.ind (D aG aL).subtype M') (inlImage aL eL)

/-- E1: the full finite-representation restriction square for the actual induced tensor.

This is the diagonal Mackey and tensor square in Ruhstorfer Remark 1.8(a),
lines 875--879 of the pinned author text. Its objects are not arbitrary
functors, and the isomorphism retains the residual G action.
-/
def RestrictionSquarePrinciple (k : Type u) [Field k]
    (finiteInduction : FiniteInductionPrinciple k) : Prop :=
  ∀ {G L Q : Type u} [Group G] [Group L] [Group Q]
    [Finite G] [Finite L] [Finite Q]
    (aG : Q →* MulAut G) (aL : Q →* MulAut L)
    (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (M' : Rep.{u} k (D aG aL)) [Module.Finite k M'],
    (Rep.res (baseEmbedding aG aL) M' ≅ M) →
    letI : Module.Finite k (Rep.ind (D aG aL).subtype M') :=
      finiteInduction aG aL M'
    Nonempty
      ((tensorFDFunctor (Rep.ind (D aG aL).subtype M') ⋙
          fdRestriction (SemidirectProduct.inl : G →* G ⋊[aG] Q)) ≅
        (fdRestriction (SemidirectProduct.inl : L →* L ⋊[aL] Q) ⋙
          tensorFDFunctor M))

/-- E2: the split degree-zero Marcus/Ruhstorfer implication for the fixed k.

The injective equivariant inclusion identifies the original groups with
the normal/intersection/product setup of Theorem 1.7. The base Morita
property is an antecedent; equivalence for the actual induced supported
tensor functor is the conclusion. The source scope is Theorem 1.7 with
Remark 1.8(b), not a weakened geometric Theorem 5.8.
-/
def SplitMarcusPrinciple (k : Type u) [Field k] [CharP k 2] [IsAlgClosed k]
    (finiteInduction : FiniteInductionPrinciple k)
    (tensorSupport : TensorSupportPrinciple k)
    (inducedSupport : InducedSupportPrinciple k) : Prop :=
  ∀ {G L Q : Type u} [Group G] [Group L] [Group Q]
    [Finite G] [Finite L] [Finite Q]
    (aG : Q →* MulAut G) (aL : Q →* MulAut L)
    (j : L →* G),
    Function.Injective j →
    (∀ (q : Q) (l : L), j (aL q l) = aG q (j l)) →
    ∀ (eG : k[G]) (eL : k[L])
      (centralG : IsMulCentral eG) (idempotentG : IsIdempotentElem eG)
      (centralL : IsMulCentral eL) (idempotentL : IsIdempotentElem eL)
      (invariantG : ∀ q : Q,
        MonoidAlgebra.mapDomainRingEquiv k (aG q) eG = eG)
      (invariantL : ∀ q : Q,
        MonoidAlgebra.mapDomainRingEquiv k (aL q) eL = eL)
      (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
      (M' : Rep.{u} k (D aG aL)) [Module.Finite k M']
      (leftSupport : LeftSupport M eG) (rightSupport : RightSupport M eL)
      (baseIso : Rep.res (baseEmbedding aG aL) M' ≅ M),
      letI : Module.Finite k (Rep.ind (D aG aL).subtype M') :=
        finiteInduction aG aL M'
      let baseMaps : ∀ V : FDRep.{u} k L,
          supported eL V → supported eG (tensorFDObj M V) :=
        fun V _ => tensorSupport M eG leftSupport V
      let inducedSupports := inducedSupport aG aL eG eL
        centralG idempotentG centralL idempotentL invariantG invariantL
        M M' leftSupport rightSupport baseIso
      let inducedMaps : ∀ V : FDRep.{u} k (L ⋊[aL] Q),
          supported (inlImage aL eL) V →
            supported (inlImage aG eG)
              (tensorFDObj (Rep.ind (D aG aL).subtype M') V) :=
        fun V _ => tensorSupport (Rep.ind (D aG aL).subtype M')
          (inlImage aG eG) inducedSupports.1 V
      (supportedTensorFDFunctor M eL eG baseMaps).IsEquivalence →
        (supportedTensorFDFunctor (Rep.ind (D aG aL).subtype M')
          (inlImage aL eL) (inlImage aG eG) inducedMaps).IsEquivalence

end ModularRep.PaperProofs.TypeBRankThreeMoritaSources


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
