import ModularRep.PaperProofs.TypeBCriterionHypotheses
import ModularRep.PaperProofs.TypeBCyclicExtensionSource
import ModularRep.PaperProofs.TypeBLocalOrdinaryGeometry

/-!
# Brauer extension on the criterion's literal ambient inertia

The actual natural action and fixed inclusion determine the embedded base.
This file transports the prescribed Brauer character canonically and applies
the representation-level cyclic extension theorem. Only cyclicity of the
actual inertia quotient remains as a geometric argument; there is no
character extension input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBGlobalExtensionBinding

open ModularRep TypeBCriterionHypotheses CyclicOuterLemma37Concrete

variable {ell : ℕ} {k K M E : Type}
variable [Field k] [Field K] [CharP k ell] [IsAlgClosed k] [CharZero K]
variable [Group M] [Finite M] [Group E] [Finite E]
variable (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
variable (action : NaturalAction G field)
variable (iota : PrimeRegularRootEmbedding ell k K G) (phi : IBr iota)

theorem base_le_brauerInertia : embeddedG G field ≤
    brauerInertia G field action iota phi := by
  rintro _ ⟨g, rfl⟩
  change IrreducibleBrauerCharacter.twist iota phi
      (action.hom ((baseEmbedding G field g)⁻¹)) = phi
  rw [← map_inv, TypeBLocalOrdinaryGeometry.naturalAction_base]
  exact inner_fixes_ibr iota g phi

variable (I : Subgroup (Ambient field))
variable (hI : I ≤ brauerInertia G field action iota phi)
variable (hGI : embeddedG G field ≤ I)

abbrev EmbeddedBase : Subgroup I := (embeddedG G field).subgroupOf I

include action in
theorem embeddedBase_normal : (EmbeddedBase G field I).Normal := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  change ((embeddedG G field).subgroupOf I).Normal
  infer_instance

/-- The fixed inclusion, with no choice of an isomorphism of base groups. -/
def baseEquiv : G ≃* EmbeddedBase G field I :=
  MulEquiv.ofBijective
    ({
      toFun := fun g => ⟨⟨baseEmbedding G field g, hGI ⟨g, rfl⟩⟩, ⟨g, rfl⟩⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
      map_mul' := by intro g h; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _ } :
      G →* EmbeddedBase G field I)
    ⟨by
      intro g h hgh
      apply TypeBLocalOrdinaryGeometry.baseEmbedding_injective G field
      exact congrArg (fun x : EmbeddedBase G field I => (x.1 : Ambient field)) hgh,
      by
        intro x
        obtain ⟨g, hg⟩ := x.2
        refine ⟨g, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact hg⟩

include hI in
theorem embedded_character_fixed
    (a : I) :
    letI := embeddedBase_normal G field action I
    IrreducibleBrauerCharacter.twist
      (iota.alongMulEquiv (baseEquiv G field I hGI))
      (IrreducibleBrauerCharacter.alongMulEquiv iota (baseEquiv G field I hGI) phi)
      (MulAut.conjNormal a) =
    IrreducibleBrauerCharacter.alongMulEquiv iota (baseEquiv G field I hGI) phi := by
  letI := embeddedBase_normal G field action I
  have hfix := hI (I.inv_mem a.2)
  change IrreducibleBrauerCharacter.twist iota phi
      (action.hom ((a.1)⁻¹)⁻¹) = phi at hfix
  simp only [inv_inv] at hfix
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  let e := baseEquiv G field I hGI
  have hsquare : e.symm (MulAut.conjNormal a x.1) = action.hom a.1 (e.symm x.1) := by
    apply TypeBLocalOrdinaryGeometry.baseEmbedding_injective G field
    have hx : baseEmbedding G field (e.symm x.1) = (x.1.1 : Ambient field) :=
      congrArg (fun z : EmbeddedBase G field I => (z.1 : Ambient field))
        (e.apply_symm_apply x.1)
    have hy := congrArg (fun z : EmbeddedBase G field I => (z.1 : Ambient field))
      (e.apply_symm_apply (MulAut.conjNormal a x.1))
    rw [TypeBLocalOrdinaryGeometry.baseEmbedding_natural, hx]
    exact hy
  have hv := congrArg (fun psi : IBr iota => psi.1
    (PrimeRegularElement.map e.symm.toMonoidHom x)) hfix
  change phi.1 (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.conjNormal a).toMonoidHom x)) =
    phi.1 (PrimeRegularElement.map e.symm.toMonoidHom x)
  have harg : PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.conjNormal a).toMonoidHom x) =
    PrimeRegularElement.map (action.hom a.1).toMonoidHom
      (PrimeRegularElement.map e.symm.toMonoidHom x) := Subtype.ext hsquare
  rw [harg]
  exact hv

/-- Apply cyclic extension after the embedded-base and character-invariance
identifications. The returned inclusion is pointwise the criterion's base
embedding, as required by its literal extension clause. -/
def extensionIn_of_cyclic
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (cyclic : letI := embeddedBase_normal G field action I
      IsCyclic (I ⧸ EmbeddedBase G field I)) :
    BrauerExtensionIn G field iota phi I := Classical.choice <| by
  letI := embeddedBase_normal G field action I
  let e := baseEquiv G field I hGI
  obtain ⟨V, hV, hchar, ⟨extension⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
      principle (iota.alongMulEquiv e)
      (IrreducibleBrauerCharacter.alongMulEquiv iota e phi) cyclic
      (embedded_character_fixed G field action iota phi I hI hGI)
  exact
    ⟨{
      inclusion := (EmbeddedBase G field I).subtype.comp e.toMonoidHom
      inclusion_value := fun _ => rfl
      witness := brauerExtendsAlong_of_embeddedRealisation
        (EmbeddedBase G field I) e iota phi V hV hchar extension }⟩

/-- The two global extension clauses are consequences of the same cyclic
source and the computed embeddings of the two inertia quotients. -/
def brauer_M
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (quotient_cyclic : IsCyclic (M ⧸ G)) :
    BrauerExtensionIn G field iota phi
      (brauerInertia G field action iota phi ⊓ embeddedM field) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  letI := quotient_cyclic
  exact extensionIn_of_cyclic G field action iota phi
    (brauerInertia G field action iota phi ⊓ embeddedM field) inf_le_left
    (le_inf (base_le_brauerInertia G field action iota phi)
      (TypeBLocalOrdinaryGeometry.embeddedG_le_embeddedM G field)) principle
    (isCyclic_of_injective
      (TypeBLocalOrdinaryGeometry.mInertiaQuotientEmbedding G field _ inf_le_right)
      (TypeBLocalOrdinaryGeometry.mInertiaQuotientEmbedding_injective
        G field _ inf_le_right))

def brauer_GE [IsCyclic E]
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k) :
    BrauerExtensionIn G field iota phi
      (brauerInertia G field action iota phi ⊓ baseFieldGroup G field) := by
  letI := TypeBLocalOrdinaryGeometry.embeddedG_normal G field action
  exact extensionIn_of_cyclic G field action iota phi
    (brauerInertia G field action iota phi ⊓ baseFieldGroup G field) inf_le_left
    (le_inf (base_le_brauerInertia G field action iota phi)
      (TypeBLocalOrdinaryGeometry.embeddedG_le_baseFieldGroup G field)) principle
    (isCyclic_of_injective
      (TypeBLocalOrdinaryGeometry.fieldInertiaQuotientEmbedding
        G field action _ inf_le_right)
      (TypeBLocalOrdinaryGeometry.fieldInertiaQuotientEmbedding_injective
        G field action _ inf_le_right))

/-- All four extension requirements of the original published criterion
are filled by kernel deductions from the two universal cyclic-extension
principles. Each local output uses its actual radical quotient. -/
theorem extensionClauses [IsAlgClosed K] [IsCyclic E]
    (brauerPrinciple : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} ell k)
    (ordinaryPrinciple : Representation.CyclicExtensionPrinciple.{0, 0, 0} K)
    (quotient_cyclic : IsCyclic (M ⧸ G)) :
    ExtensionClauses G field action iota where
  brauer_M phi := ⟨brauer_M G field action iota phi brauerPrinciple quotient_cyclic⟩
  brauer_GE phi := ⟨brauer_GE G field action iota phi brauerPrinciple⟩
  ordinary_M W := TypeBLocalOrdinaryGeometry.ordinary_M
    G field action W ordinaryPrinciple quotient_cyclic
  ordinary_GE W := TypeBLocalOrdinaryGeometry.ordinary_GE
    G field action W ordinaryPrinciple

end ModularRep.PaperProofs.TypeBGlobalExtensionBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
