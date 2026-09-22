import Mathlib.RepresentationTheory.Character
import ModularRep.IBrSimpleModuleClass

/-!
# Irreducible trace separation over the actual ordinary coefficient field

For a finite group in characteristic zero, the character averaging formula
computes the dimension of the actual intertwining-map space. Equal traces
therefore give a nonzero intertwiner between irreducibles, hence an actual
representation equivalence. No algebraic closure, normalized orthogonality,
scalar endomorphism theorem, or new external certificate is required.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBOrdinaryTraceSeparationSplitting

open CategoryTheory Representation
open ModularRep ModularRep.FDRepSimpleClassKZero
open scoped MonoidAlgebra BigOperators

universe u v w

variable {K G : Type u} [Field K] [CharZero K] [Group G] [Finite G]

section Unbundled

variable {V : Type v} {W : Type w}
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  (rho : Representation K G V) (sigma : Representation K G W)

/-- The identity of an irreducible representation is nonzero, so its
actual endomorphism space has positive dimension. Its dimension need not be one. -/
theorem end_finrank_pos [Representation.IsIrreducible rho] :
    0 < Module.finrank K (IntertwiningMap rho rho) := by
  letI : Nontrivial rho.asModule := IsSimpleModule.nontrivial K[G] rho.asModule
  letI : Nontrivial V := rho.asModuleEquiv.symm.toEquiv.nontrivial
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨1, ?_⟩
  intro identity_zero
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  exact congrArg (fun f : IntertwiningMap rho rho => f x) identity_zero

/-- Characteristic zero and equal literal trace functions identify the
Hom dimension with the End dimension by the checked averaging formula. -/
theorem intertwining_finrank_eq_end_of_character_eq
    (characters : rho.character = sigma.character) :
    Module.finrank K (IntertwiningMap rho sigma) =
      Module.finrank K (IntertwiningMap rho rho) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (NeZero.ne (Nat.card G : K))
  apply Nat.cast_injective (R := K)
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho sigma,
    ← Representation.card_inv_mul_sum_char_mul_char_eq_finrank rho rho]
  rw [characters]

/-- Reverse trace separation for the actual finite-dimensional irreducible
representations. The conclusion is an actual intertwining equivalence. -/
theorem nonempty_equiv_of_character_eq
    [Representation.IsIrreducible rho] [Representation.IsIrreducible sigma]
    (characters : rho.character = sigma.character) :
    Nonempty (Representation.Equiv rho sigma) := by
  have positive : 0 < Module.finrank K (IntertwiningMap rho sigma) := by
    rw [intertwining_finrank_eq_end_of_character_eq rho sigma characters]
    exact end_finrank_pos rho
  obtain ⟨f, nonzero⟩ := Module.finrank_pos_iff_exists_ne_zero.mp positive
  exact ⟨f.ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right nonzero)⟩

end Unbundled

/-- The literal linear equivalence and its intertwining square give the
corresponding isomorphism in the actual finite-dimensional representation category. -/
def fdRepIsoOfRepresentationEquiv (V W : FDRep K G)
    (e : Representation.Equiv V.ρ W.ρ) : V ≅ W := by
  refine Action.mkIso e.toLinearEquiv.toFGModuleCatIso (fun g => ?_)
  ext x
  change e.toLinearEquiv (V.ρ g x) = W.ρ g (e.toLinearEquiv x)
  exact congrArg (fun f : V →ₗ[K] W => f x) (e.isIntertwining' g)

/-- Bundled form with explicit irreducibility proofs for the actual FDRep carriers. -/
theorem fdRep_nonempty_iso_of_character_eq (V W : FDRep K G)
    (hV : Representation.IsIrreducible V.ρ)
    (hW : Representation.IsIrreducible W.ρ)
    (characters : V.character = W.character) : Nonempty (V ≅ W) := by
  letI : Representation.IsIrreducible V.ρ := hV
  letI : Representation.IsIrreducible W.ρ := hW
  obtain ⟨e⟩ := nonempty_equiv_of_character_eq V.ρ W.ρ characters
  exact ⟨fdRepIsoOfRepresentationEquiv V W e⟩

/-- Actual representative trace functions separate the SAME simple
group algebra module classes, without changing their skeleton or labels. -/
theorem simpleModuleClass_character_injective :
    Function.Injective (fun X : SimpleModuleClass K[G] =>
      (simpleClassFDRep X).character) := by
  intro X Y characters
  obtain ⟨e⟩ := fdRep_nonempty_iso_of_character_eq (simpleClassFDRep X) (simpleClassFDRep Y)
    (simpleClassFDRep_irreducible X) (simpleClassFDRep_irreducible Y) characters
  apply Subtype.ext
  rw [← toSkeleton_fromSkeleton_obj X.val, ← toSkeleton_fromSkeleton_obj Y.val]
  apply congr_toSkeleton_of_iso
  exact (simpleClassFDRepModuleIso X).symm ≪≫
    (FDRepFiniteLength.toModuleMonoidAlgebra (k := K) (G := G)).mapIso e ≪≫
    simpleClassFDRepModuleIso Y

end ModularRep.PaperProofs.TypeBOrdinaryTraceSeparationSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
