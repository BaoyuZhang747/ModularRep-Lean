import ModularRep.FDRepSimpleClassKZero
import ModularRep.PrimitiveCentralIdempotent
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierPKernelCentralAction
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-! A nonzero central idempotent supports a simple module. Its central scalar
identifies the corresponding catalogue character, so the checked normal-p
kernel action also annihilates every catalogue central character. -/

noncomputable section
open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalSimple

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
open SporadicFi24P3Definition44NamedCarrierPKernelCentralAction

theorem exists_supported_coatom
    {A : Type*} [Ring A] (e : A)
    (he : IsPrimitiveCentralIdempotent e) :
    ∃ M : Submodule A A, IsCoatom M ∧
      ∀ v : A ⧸ M, e • v = v := by
  let J : Submodule A A := Submodule.span A {1 - e}
  have hJ : J ≠ ⊤ := by
    intro htop
    have hmem : (1 : A) ∈ J := by rw [htop]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    change a * (1 - e) = 1 at ha
    have hz : (1 - e) * e = 0 := by
      rw [sub_mul, one_mul, he.idempotent.eq, sub_self]
    have h := congrArg (fun x : A => x * e) ha
    rw [mul_assoc, hz, mul_zero, one_mul] at h
    exact he.ne_zero h.symm
  obtain ⟨M, hM, hJM⟩ := (eq_top_or_exists_le_coatom J).resolve_left hJ
  refine ⟨M, hM, ?_⟩
  have hminus : e - 1 ∈ M := by
    have h := M.neg_mem (hJM (Submodule.mem_span_singleton_self (1 - e)))
    simpa only [neg_sub] using h
  intro v
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective M v
  change (Submodule.Quotient.mk (e * a) : A ⧸ M) = Submodule.Quotient.mk a
  apply (Submodule.Quotient.eq M).mpr
  have hrewrite : e * a - a = a * (e - 1) := by
    rw [mul_sub, mul_one, (he.central.comm a).eq]
  rw [hrewrite]
  exact M.smul_mem a hminus

universe u

theorem exists_irreducible_supported
    {k G : Type u} [Field k] [Group G] [Finite G]
    (e : k[G]) (he : IsPrimitiveCentralIdempotent e) :
    ∃ W : FDRep k G, Representation.IsIrreducible W.ρ ∧
      Representation.asAlgebraHom W.ρ e = 1 := by
  obtain ⟨M, hM, hsupport⟩ := exists_supported_coatom e he
  let : IsSimpleModule k[G] (k[G] ⧸ M) :=
    isSimpleModule_iff_isCoatom.mpr hM
  let Q : ModuleCat.{u} k[G] := ModuleCat.of k[G] (k[G] ⧸ M)
  let : Simple Q := by
    change Simple (ModuleCat.of k[G] (k[G] ⧸ M))
    infer_instance
  let X : SimpleModuleClass k[G] :=
    ⟨toSkeleton Q, Simple.of_iso (fromSkeletonToSkeletonIso Q)⟩
  let E : Representation.asModule (simpleClassFDRep X).ρ ≃ₗ[k[G]]
      (k[G] ⧸ M) :=
    ((simpleClassFDRepModuleIso X) ≪≫
      (fromSkeletonToSkeletonIso Q)).toLinearEquiv
  have hX : ∀ v : Representation.asModule (simpleClassFDRep X).ρ,
      e • v = v := by
    intro v
    apply E.injective
    rw [E.map_smul, hsupport]
  have hW : Representation.IsIrreducible (simpleClassFDRep X).ρ := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule]
    exact simple_iff_isSimpleModule.mp (simpleClassFDRep_underlying_simple X)
  refine ⟨simpleClassFDRep X, hW, ?_⟩
  apply LinearMap.ext
  intro v
  change Representation.asAlgebraHom (simpleClassFDRep X).ρ e v = v
  have h := congrArg (Representation.asModuleEquiv (simpleClassFDRep X).ρ)
    (hX ((Representation.asModuleEquiv (simpleClassFDRep X).ρ).symm v))
  simpa only [Representation.asModuleEquiv_map_smul,
    LinearEquiv.apply_symm_apply] using h

theorem catalogue_character_eq_centerScalar_of_block_action
    {k G V I : Type*} [Field k] [IsAlgClosed k]
    [Group G] [Fintype G] [Fintype I]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {e : I → k[G]}
    (blocks : BlockIdempotentDecomposition e)
    (catalogue : BlockCentralCharacterCatalogue blocks) (b : I)
    (rho : Representation k G V) [rho.IsIrreducible]
    (hb : rho.asAlgebraHom (e b) = (LinearMap.id : V →ₗ[k] V)) :
    catalogue.centralCharacter b = centerScalar rho := by
  have hscalar : centerScalar rho (blocks.blockIdempotentInCenter b) = 1 := by
    apply scalar_id_injective rho
    simpa only [one_smul] using
      (centerScalar_spec rho (blocks.blockIdempotentInCenter b)).symm.trans hb
  obtain ⟨c, hc⟩ := catalogue.exhaustive (centerScalar rho)
  have hcb : c = b := by
    by_contra hne
    have hz := catalogue.centralCharacter_other hne
    rw [hc] at hz
    exact zero_ne_one (hz.symm.trans hscalar)
  subst c
  exact hc

theorem catalogue_zero_of_normal_p_restriction_zero
    {p : ℕ} {k G : Type u} {I : Type*}
    [Field k] [IsAlgClosed k] [CharP k p] [Fact p.Prime]
    [Group G] [Fintype G] [Fintype I]
    {e : I → k[G]}
    (blocks : BlockIdempotentDecomposition e)
    (catalogue : BlockCentralCharacterCatalogue blocks)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup p P)
    (z : GroupAlgebraCenter k G)
    (hz : centralBrauerRestriction P z = 0) (b : I) :
    catalogue.centralCharacter b z = 0 := by
  obtain ⟨W, hW, hb⟩ := exists_irreducible_supported (e b) (blocks.primitive b)
  let : Representation.IsIrreducible W.ρ := hW
  let : Nontrivial W :=
    IsSimpleModule.nontrivial k[G] (Representation.asModule W.ρ)
  have hc := catalogue_character_eq_centerScalar_of_block_action
    blocks catalogue b W.ρ hb
  rw [hc]
  apply scalar_id_injective W.ρ
  rw [zero_smul, ← centerScalar_spec]
  exact central_action_eq_zero_of_normal_p P hP W.ρ hW z hz

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierP3IntervalSimple


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
