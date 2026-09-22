import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
# A least Frobenius-stable Levi overgroup from dimension and intersection

This subgroup-order deduction uses a natural-number dimension strictly
increasing on strict Levi inclusions.  Intersections are required only for
Levi overgroups of the fixed subgroup.  A dimension-minimal overgroup is
least, hence unique.  A subgroup automorphism preserving this collection
and the fixed subgroup preserves that least overgroup.  Properness follows
as soon as any proper Levi overgroup exists.

The caller supplies the actual geometric Levi predicate, dimension and
intersection facts.  No least, proper or stable envelope is an input.
-/

set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalLeviEnvelope

universe u

variable {G : Type u} [Group G]

/-- Dimension minimization and intersection give a unique least overgroup. -/
theorem existsUnique_least_levi
    (IsLevi : Subgroup G → Prop) (dim : Subgroup G → ℕ)
    (top_isLevi : IsLevi ⊤)
    (dim_strict : ∀ {L M : Subgroup G},
      IsLevi L → IsLevi M → L < M → dim L < dim M)
    (H : Subgroup G)
    (inf_isLevi : ∀ L M : Subgroup G,
      IsLevi L → H ≤ L → IsLevi M → H ≤ M → IsLevi (L ⊓ M)) :
    ∃! L : Subgroup G,
      IsLevi L ∧ H ≤ L ∧
        ∀ M : Subgroup G, IsLevi M → H ≤ M → L ≤ M := by
  classical
  have nonempty_dimension : ∃ n : ℕ,
      ∃ L : Subgroup G, IsLevi L ∧ H ≤ L ∧ dim L = n :=
    ⟨dim ⊤, ⊤, top_isLevi, le_top, rfl⟩
  obtain ⟨L, hL, hHL, hdim⟩ := Nat.find_spec nonempty_dimension
  have minimal_dimension : ∀ M : Subgroup G,
      IsLevi M → H ≤ M → dim L ≤ dim M := by
    intro M hM hHM
    rw [hdim]
    exact Nat.find_min' nonempty_dimension ⟨M, hM, hHM, rfl⟩
  have least : ∀ M : Subgroup G, IsLevi M → H ≤ M → L ≤ M := by
    intro M hM hHM
    by_contra hLM
    have hinf : IsLevi (L ⊓ M) := inf_isLevi L M hL hHL hM hHM
    have hHinf : H ≤ L ⊓ M := le_inf hHL hHM
    have strict : L ⊓ M < L :=
      lt_of_le_not_ge inf_le_left (fun h => hLM (h.trans inf_le_right))
    exact (not_lt_of_ge (minimal_dimension (L ⊓ M) hinf hHinf))
      (dim_strict hinf hL strict)
  refine ⟨L, ⟨hL, hHL, least⟩, ?_⟩
  intro M hM
  exact le_antisymm (hM.2.2 L hL hHL) (least M hM.1 hM.2.1)

/-- The same least overgroup is stable and inherits available properness. -/
theorem existsUnique_frobeniusStable_leviEnvelope
    (IsLevi : Subgroup G → Prop) (dim : Subgroup G → ℕ)
    (top_isLevi : IsLevi ⊤)
    (dim_strict : ∀ {L M : Subgroup G},
      IsLevi L → IsLevi M → L < M → dim L < dim M)
    (H : Subgroup G)
    (inf_isLevi : ∀ L M : Subgroup G,
      IsLevi L → H ≤ L → IsLevi M → H ≤ M → IsLevi (L ⊓ M))
    (Frob : MulAut G)
    (frobenius_isLevi : ∀ L : Subgroup G,
      IsLevi (L.map Frob.toMonoidHom) ↔ IsLevi L)
    (frobenius_H : H.map Frob.toMonoidHom = H) :
    ∃! L : Subgroup G,
      IsLevi L ∧ H ≤ L ∧
      (∀ M : Subgroup G, IsLevi M → H ≤ M → L ≤ M) ∧
      L.map Frob.toMonoidHom = L ∧
      ((∃ M : Subgroup G, IsLevi M ∧ H ≤ M ∧ M ≠ ⊤) → L ≠ ⊤) := by
  obtain ⟨L, hL, unique⟩ :=
    existsUnique_least_levi IsLevi dim top_isLevi dim_strict H inf_isLevi
  let e : Subgroup G ≃o Subgroup G := Frob.mapSubgroup
  have fixed_H : e H = H := frobenius_H
  have mapped_isLevi : IsLevi (e L) := (frobenius_isLevi L).2 hL.1
  have mapped_contains : H ≤ e L := by
    calc
      H = e H := fixed_H.symm
      _ ≤ e L := e.monotone hL.2.1
  have mapped_least : ∀ M : Subgroup G,
      IsLevi M → H ≤ M → e L ≤ M := by
    intro M hM hHM
    have preimage_isLevi : IsLevi (e.symm M) := by
      apply (frobenius_isLevi (e.symm M)).1
      change IsLevi (e (e.symm M))
      simpa only [e.apply_symm_apply] using hM
    have preimage_contains : H ≤ e.symm M := by
      apply e.le_symm_apply.mpr
      simpa only [fixed_H] using hHM
    have mapped_le : e L ≤ e (e.symm M) :=
      e.monotone (hL.2.2 (e.symm M) preimage_isLevi preimage_contains)
    simpa only [e.apply_symm_apply] using mapped_le
  have fixed_L : L.map Frob.toMonoidHom = L :=
    unique (e L) ⟨mapped_isLevi, mapped_contains, mapped_least⟩
  have proper : (∃ M : Subgroup G, IsLevi M ∧ H ≤ M ∧ M ≠ ⊤) → L ≠ ⊤ := by
    rintro ⟨M, hM, hHM, hMproper⟩ hLtop
    apply hMproper
    apply top_unique
    rw [← hLtop]
    exact hL.2.2 M hM hHM
  refine ⟨L, ⟨hL.1, hL.2.1, hL.2.2, fixed_L, proper⟩, ?_⟩
  intro M hM
  exact unique M ⟨hM.1, hM.2.1, hM.2.2.1⟩

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalLeviEnvelope


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
