import ModularRep.PaperProofs.TypeBRankThreeMoritaInduced
import ModularRep.PaperProofs.TypeBRankThreeMoritaSources

/-!
# Apply the split induced Morita implication to the same honest actor

The base restriction is derived from the literal equality on the same module.
For each actual subgroup of the original actor, the induced object is the
fixed diagonal induction. Its supported tensor equivalence and full finite
representation restriction square follow from the existing uniform sources.
No induced object, functor, base isomorphism or induced equivalence is supplied.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaSplitApplication

open TypeBRankThreeMoritaDiagonal TypeBRankThreeMoritaInduced
open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources

universe u

variable {k G L E : Type u} [Field k] [Group G] [Group L] [Group E]

/-- The displayed base equality identifies the canonical restriction with M. -/
def diagonalBaseIsoOfRestriction
    (aG : E →* MulAut G) (aL : E →* MulAut L)
    (M : Rep.{u} k (G × Lᵐᵒᵖ))
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) M)
    (baseRestriction : rho.comp
      (SemidirectProduct.inl : G × Lᵐᵒᵖ →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) = M.ρ)
    (Q : Subgroup E) :
    Rep.res (baseEmbedding (aG.comp Q.subtype) (aL.comp Q.subtype))
        (Rep.of (diagonalRepresentation aG aL Q rho)) ≅ M :=
  diagonalBaseIso aG aL Q rho ≪≫ eqToIso (by
    change Rep.of (rho.comp SemidirectProduct.inl) = M
    rw [baseRestriction])

/-- The same diagonal representation is finite before and after induction. -/
theorem inducedModule_finite [Finite G] [Finite L] [Finite E]
    (finiteInduction : FiniteInductionPrinciple k)
    (aG : E →* MulAut G) (aL : E →* MulAut L)
    (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) M)
    (Q : Subgroup E) : Module.Finite k (inducedModule aG aL Q rho) :=
  finiteInduction (aG.comp Q.subtype) (aL.comp Q.subtype)
    (Rep.of (diagonalRepresentation aG aL Q rho))

/-- Full-actor invariance restricts to Q and supplies the actual induced supports. -/
theorem inducedModule_support [Finite G] [Finite L] [Finite E]
    (inducedSupport : InducedSupportPrinciple k)
    (aG : E →* MulAut G) (aL : E →* MulAut L)
    (eG : k[G]) (eL : k[L])
    (centralG : IsMulCentral eG) (idempotentG : IsIdempotentElem eG)
    (centralL : IsMulCentral eL) (idempotentL : IsIdempotentElem eL)
    (invariantG : ∀ e : E, MonoidAlgebra.mapDomainRingEquiv k (aG e) eG = eG)
    (invariantL : ∀ e : E, MonoidAlgebra.mapDomainRingEquiv k (aL e) eL = eL)
    (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) M)
    (baseRestriction : rho.comp
      (SemidirectProduct.inl : G × Lᵐᵒᵖ →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) = M.ρ)
    (leftSupport : LeftSupport M eG) (rightSupport : RightSupport M eL)
    (Q : Subgroup E) :
    LeftSupport (inducedModule aG aL Q rho) (inlImage (aG.comp Q.subtype) eG) ∧
      RightSupport (inducedModule aG aL Q rho) (inlImage (aL.comp Q.subtype) eL) :=
  inducedSupport (aG.comp Q.subtype) (aL.comp Q.subtype) eG eL
    centralG idempotentG centralL idempotentL
    (fun q => invariantG q.val) (fun q => invariantL q.val)
    M (Rep.of (diagonalRepresentation aG aL Q rho)) leftSupport rightSupport
    (diagonalBaseIsoOfRestriction aG aL M rho baseRestriction Q)

/-- Apply the uniform sources to the literal induced module for every Q ≤ E. -/
theorem subgroup_induced_morita [Finite G] [Finite L] [Finite E]
    [CharP k 2] [IsAlgClosed k]
    (finiteInduction : FiniteInductionPrinciple k)
    (tensorSupport : TensorSupportPrinciple k)
    (inducedSupport : InducedSupportPrinciple k)
    (restrictionSquare : RestrictionSquarePrinciple k finiteInduction)
    (marcus : SplitMarcusPrinciple k finiteInduction tensorSupport inducedSupport)
    (aG : E →* MulAut G) (aL : E →* MulAut L)
    (j : L →* G) (jInjective : Function.Injective j)
    (jEquivariant : ∀ (e : E) (l : L), j (aL e l) = aG e (j l))
    (eG : k[G]) (eL : k[L])
    (centralG : IsMulCentral eG) (idempotentG : IsIdempotentElem eG)
    (centralL : IsMulCentral eL) (idempotentL : IsIdempotentElem eL)
    (invariantG : ∀ e : E, MonoidAlgebra.mapDomainRingEquiv k (aG e) eG = eG)
    (invariantL : ∀ e : E, MonoidAlgebra.mapDomainRingEquiv k (aL e) eL = eL)
    (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (rho : Representation k ((G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) M)
    (baseRestriction : rho.comp
      (SemidirectProduct.inl : G × Lᵐᵒᵖ →* (G × Lᵐᵒᵖ) ⋊[baseAction aG aL] E) = M.ρ)
    (leftSupport : LeftSupport M eG) (rightSupport : RightSupport M eL)
    (baseEquivalence :
      (supportedTensorFDFunctor M eL eG
        (fun V _ => tensorSupport M eG leftSupport V)).IsEquivalence)
    (Q : Subgroup E) :
    letI : Module.Finite k (inducedModule aG aL Q rho) :=
      inducedModule_finite finiteInduction aG aL M rho Q
    let inducedMaps : ∀ V : FDRep k (L ⋊[aL.comp Q.subtype] Q),
        supported (inlImage (aL.comp Q.subtype) eL) V →
          supported (inlImage (aG.comp Q.subtype) eG)
            (tensorFDObj (inducedModule aG aL Q rho) V) :=
      fun V _ => tensorSupport (inducedModule aG aL Q rho)
        (inlImage (aG.comp Q.subtype) eG)
        (inducedModule_support inducedSupport aG aL eG eL centralG idempotentG
          centralL idempotentL invariantG invariantL M rho baseRestriction
          leftSupport rightSupport Q).1 V
    (supportedTensorFDFunctor (inducedModule aG aL Q rho)
      (inlImage (aL.comp Q.subtype) eL) (inlImage (aG.comp Q.subtype) eG)
      inducedMaps).IsEquivalence ∧
    Nonempty
      ((tensorFDFunctor (inducedModule aG aL Q rho) ⋙
          fdRestriction (SemidirectProduct.inl : G →* G ⋊[aG.comp Q.subtype] Q)) ≅
        (fdRestriction (SemidirectProduct.inl : L →* L ⋊[aL.comp Q.subtype] Q) ⋙
          tensorFDFunctor M)) := by
  letI : Module.Finite k (inducedModule aG aL Q rho) :=
    inducedModule_finite finiteInduction aG aL M rho Q
  refine ⟨?_, ?_⟩
  · exact marcus (aG.comp Q.subtype) (aL.comp Q.subtype) j jInjective
      (fun q l => jEquivariant q.val l) eG eL centralG idempotentG centralL idempotentL
      (fun q => invariantG q.val) (fun q => invariantL q.val)
      M (Rep.of (diagonalRepresentation aG aL Q rho)) leftSupport rightSupport
      (diagonalBaseIsoOfRestriction aG aL M rho baseRestriction Q) baseEquivalence
  · exact restrictionSquare (aG.comp Q.subtype) (aL.comp Q.subtype)
      M (Rep.of (diagonalRepresentation aG aL Q rho))
      (diagonalBaseIsoOfRestriction aG aL M rho baseRestriction Q)

end ModularRep.PaperProofs.TypeBRankThreeMoritaSplitApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
