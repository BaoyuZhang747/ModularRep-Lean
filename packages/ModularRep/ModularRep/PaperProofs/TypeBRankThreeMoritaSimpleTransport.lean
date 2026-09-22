import ModularRep.PaperProofs.TypeBRankThreeMoritaSources
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCarriers
import ModularRep.IBrBlockEquivTransport
import Mathlib.CategoryTheory.Simple

/-!
# Literal packet support and simple tensor transport

The block-action proof uses the shared simple-module/block dictionary and
the canonical root-derived injectivity. Packet membership then proves
support on the same affording representation.

The only new E1 principle identifies categorical simplicity in the
supported full subcategory with irreducibility of its underlying finite
representation. It concerns no tensor, Jordan map or extension. The
actual tensor irreducibility below follows from that dictionary and the
base supported equivalence via the existing simple-object theorem.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaSimpleTransport

open ModularRep FDRepSimpleClassKZero
open TypeBRankThreeMoritaTensor TypeBRankThreeMoritaFiniteTensor
open TypeBRankThreeMoritaSources TypeBRankThreeJordanPacketCarriers

universe u v w

/-- E1: the supported full subcategory has the same simple objects as its
underlying irreducible finite representations. No inhabitant is supplied. -/
def SupportedSimplePrinciple (k : Type u) [Field k] : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (e : k[G]) (V : SupportedFDRep e),
    CategoryTheory.Simple V ↔ Representation.IsIrreducible V.obj.ρ

section AffordingBlock

variable {p : ℕ} {k G : Type u} {K : Type v} {I : Type w}
  [Field k] [Field K] [Group G] [Finite G] [Fintype I]
  [CharP k p] [IsAlgClosed k] [CharZero K]
  {d : I → k[G]}

/-- The named block acts as the identity on every irreducible representation
affording its actual Brauer character. -/
theorem block_smul_of_affording
    (root : PrimeRegularRootEmbedding p k K G)
    (injective : IrreducibleBrauerCharacterInjectivity root)
    (blocks : BlockIdempotentDecomposition d) (phi : IBr root)
    (W : FDRep k G) (irreducible : Representation.IsIrreducible W.ρ)
    (affords : phi.val = Representation.brauerCharacterOfRootEmbedding W.ρ root) :
    ∀ v : Representation.asModule W.ρ,
      d (irreducibleBrauerCharacterBlock root injective blocks phi) • v = v := by
  letI : IsSimpleModule k[G] (Representation.asModule W.ρ) :=
    (Representation.irreducible_iff_isSimpleModule_asModule W.ρ).mp irreducible
  have sameCharacter : simpleClassToIBr root
      (simpleClassOfIrreducibleFDRep W irreducible) = phi := by
    apply Subtype.ext
    change Representation.brauerCharacterOfRootEmbedding
      (simpleClassFDRep (simpleClassOfIrreducibleFDRep W irreducible)).ρ root = phi.val
    rw [affords]
    exact Representation.brauerCharacterOfRootEmbedding_iso root
      (simpleClassOfIrreducibleFDRepIso W irreducible)
  have sameBlock : irreducibleBrauerCharacterBlock root injective blocks phi =
      blocks.moduleBlock (V := Representation.asModule W.ρ) := by
    rw [← sameCharacter, irreducibleBrauerCharacterBlock_simpleClassToIBr]
    exact simpleModuleClassBlock_simpleClassOfIrreducibleFDRep blocks W irreducible
  intro v
  rw [sameBlock]
  exact blocks.moduleBlock_smul v

end AffordingBlock

section PacketSupport

variable {k K G I : Type}
  [Field k] [Field K] [Group G] [Finite G] [Fintype I]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  {d : I → k[G]}

/-- The computed packet supports the SAME affording representation. -/
theorem packet_affording_supported
    (root : PrimeRegularRootEmbedding 2 k K G)
    (blocks : BlockIdempotentDecomposition d) (e : k[G])
    (psi : Packet root blocks e) (W : FDRep k G)
    (irreducible : Representation.IsIrreducible W.ρ)
    (affords : psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ root) :
    supported e W := by
  have blockActs :
      Representation.asAlgebraHom W.ρ (supportingBlock root blocks psi.val).val = 1 := by
    apply LinearMap.ext
    intro v
    have acts := block_smul_of_affording root
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root)
      blocks psi.val W irreducible affords
      ((Representation.asModuleEquiv W.ρ).symm v)
    have values := congrArg (Representation.asModuleEquiv W.ρ) acts
    change Representation.asAlgebraHom W.ρ
      (d (irreducibleBrauerCharacterBlock root
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding root) blocks psi.val)) v = v
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using values
  have packetEquation :
      (supportingBlock root blocks psi.val).val * e =
        (supportingBlock root blocks psi.val).val := psi.property
  have imageEquation := congrArg (Representation.asAlgebraHom W.ρ) packetEquation
  change Representation.asAlgebraHom W.ρ e = 1
  simpa only [map_mul, blockActs, one_mul] using imageEquation

end PacketSupport

section TensorTransport

variable {k G L : Type u} [Field k] [Group G] [Group L] [Finite G] [Finite L]

/-- The base supported equivalence makes the literal tensor of a supported
irreducible input irreducible. The output object is not selected separately. -/
theorem tensor_irreducible_of_base_morita
    (simpleSupported : SupportedSimplePrinciple k)
    (tensorSupport : TensorSupportPrinciple k)
    (M : Rep.{u} k (G × Lᵐᵒᵖ)) [Module.Finite k M]
    (eL : k[L]) (eG : k[G]) (leftSupport : LeftSupport M eG)
    (baseEquivalence :
      (supportedTensorFDFunctor M eL eG
        (fun V _ => tensorSupport M eG leftSupport V)).IsEquivalence)
    (W : FDRep k L) (support : supported eL W)
    (irreducible : Representation.IsIrreducible W.ρ) :
    Representation.IsIrreducible (tensorFDObj M W).ρ := by
  let Ws : SupportedFDRep eL := ⟨W, support⟩
  let F : SupportedFDRep eL ⥤ SupportedFDRep eG :=
    supportedTensorFDFunctor M eL eG
      (fun V _ => tensorSupport M eG leftSupport V)
  letI : F.IsEquivalence := baseEquivalence
  letI : CategoryTheory.Simple Ws := (simpleSupported eL Ws).mpr irreducible
  have tensorSimple : CategoryTheory.Simple (F.obj Ws) :=
    CategoryTheory.simple_obj F Ws
  have result := (simpleSupported eG (F.obj Ws)).mp tensorSimple
  change Representation.IsIrreducible (tensorFDObj M W).ρ at result
  exact result

end TensorTransport

end ModularRep.PaperProofs.TypeBRankThreeMoritaSimpleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
