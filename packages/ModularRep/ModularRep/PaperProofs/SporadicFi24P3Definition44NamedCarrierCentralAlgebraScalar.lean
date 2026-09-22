import ModularRep.CentralAction
import ModularRep.BlockCentralCharacters
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

/-! Identify the central scalar action of an actual irreducible representation
with the central character of its block in the retained catalogue. Schur's
lemma supplies the scalar map; catalogue exhaustivity and actual idempotent
identity action identify the block internally. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierBrauerBlockAction

section Scalar

variable {k G V : Type*}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

def centerAction (rho : Representation k G V) :
    GroupAlgebraCenter k G →ₐ[k]
      Representation.IntertwiningMap rho rho where
  toFun z :=
    { toLinearMap := rho.asAlgebraHom z.val
      isIntertwining' g := by
        change rho.asAlgebraHom z.val * rho g =
          rho g * rho.asAlgebraHom z.val
        rw [← rho.asAlgebraHom_of, ← map_mul, ← map_mul]
        exact congrArg rho.asAlgebraHom
          (Subalgebra.mem_center_iff.mp z.property _).symm }
  map_one' := by
    apply Representation.IntertwiningMap.ext
    exact map_one rho.asAlgebraHom
  map_mul' x y := by
    apply Representation.IntertwiningMap.ext
    exact map_mul rho.asAlgebraHom x.val y.val
  map_zero' := by
    apply Representation.IntertwiningMap.ext
    exact map_zero rho.asAlgebraHom
  map_add' x y := by
    apply Representation.IntertwiningMap.ext
    exact map_add rho.asAlgebraHom x.val y.val
  commutes' a := by
    apply Representation.IntertwiningMap.ext
    change rho.asAlgebraHom (algebraMap k k[G] a) =
      (algebraMap k (Representation.IntertwiningMap rho rho) a).toLinearMap
    rw [rho.asAlgebraHom.commutes,
      Representation.IntertwiningMap.algebraMap_apply,
      Representation.IntertwiningMap.toLinearMap_smul]
    rfl

variable [FiniteDimensional k V] [IsAlgClosed k]

def centerScalar (rho : Representation k G V) [rho.IsIrreducible] :
    GroupAlgebraCenter k G →ₐ[k] k :=
  (Representation.scalarIntertwiningEquiv rho).symm.toAlgHom.comp
    (centerAction rho)

theorem centerScalar_spec
    (rho : Representation k G V) [rho.IsIrreducible]
    (z : GroupAlgebraCenter k G) :
    rho.asAlgebraHom z.val =
      centerScalar rho z • (LinearMap.id : V →ₗ[k] V) := by
  have h := (Representation.scalarIntertwiningEquiv rho).apply_symm_apply
    (centerAction rho z)
  have ht := congrArg
    (fun f : Representation.IntertwiningMap rho rho => f.toLinearMap)
    h.symm
  change rho.asAlgebraHom z.val =
    (Representation.scalarIntertwiningEquiv rho
      (centerScalar rho z)).toLinearMap at ht
  simpa only [Representation.scalarIntertwiningEquiv_toLinearMap] using ht

theorem scalar_id_injective
    (rho : Representation k G V) [rho.IsIrreducible]
    {a b : k}
    (h : a • (LinearMap.id : V →ₗ[k] V) =
      b • (LinearMap.id : V →ₗ[k] V)) :
    a = b := by
  apply (Representation.scalarIntertwiningEquiv rho).injective
  apply (Representation.IntertwiningMap.toLinearMap_injective rho rho)
  simpa only [Representation.scalarIntertwiningEquiv_toLinearMap] using h

end Scalar

section Catalogue

universe u v
variable {p : ℕ} {k G V : Type u} {K : Type v} {I : Type*}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype I]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {idempotent : I → k[G]}

theorem catalogue_character_eq_centerScalar
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition idempotent)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (phi : IBr iota)
    (rho : Representation k G V) [rho.IsIrreducible]
    (hchar : phi.val = rho.brauerCharacterOfRootEmbedding iota) :
    catalogue.centralCharacter
        (irreducibleBrauerCharacterBlock iota hinj blocks phi) =
      centerScalar rho := by
  classical
  let b := irreducibleBrauerCharacterBlock iota hinj blocks phi
  let W : FDRep k G := FDRep.of rho
  have hW : Representation.IsIrreducible W.ρ := by
    change Representation.IsIrreducible rho
    infer_instance
  have hs := block_smul_of_affording iota hinj blocks phi W hW hchar
  change ∀ v : rho.asModule, idempotent b • v = v at hs
  have hb : rho.asAlgebraHom (idempotent b) =
      (LinearMap.id : V →ₗ[k] V) := by
    apply LinearMap.ext
    intro v
    change rho.asAlgebraHom (idempotent b) v = v
    have hv := congrArg rho.asModuleEquiv
      (hs (rho.asModuleEquiv.symm v))
    simpa only [Representation.asModuleEquiv_map_smul,
      LinearEquiv.apply_symm_apply] using hv
  have hscalar :
      centerScalar rho (blocks.blockIdempotentInCenter b) = 1 := by
    apply scalar_id_injective rho
    simpa only [one_smul] using
      (centerScalar_spec rho
        (blocks.blockIdempotentInCenter b)).symm.trans hb
  obtain ⟨c, hc⟩ := catalogue.exhaustive (centerScalar rho)
  have hcb : c = b := by
    by_contra hne
    have hz := catalogue.centralCharacter_other hne
    rw [hc] at hz
    exact zero_ne_one (hz.symm.trans hscalar)
  subst c
  exact hc

theorem catalogue_action_of_affording
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (blocks : BlockIdempotentDecomposition idempotent)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (phi : IBr iota)
    (rho : Representation k G V) [rho.IsIrreducible]
    (hchar : phi.val = rho.brauerCharacterOfRootEmbedding iota)
    (z : GroupAlgebraCenter k G) :
    rho.asAlgebraHom z.val =
      catalogue.centralCharacter
          (irreducibleBrauerCharacterBlock iota hinj blocks phi) z •
        (LinearMap.id : V →ₗ[k] V) := by
  rw [catalogue_character_eq_centerScalar
    iota hinj blocks catalogue phi rho hchar]
  exact centerScalar_spec rho z

end Catalogue

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
