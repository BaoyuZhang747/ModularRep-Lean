import ModularRep.PaperProofs.TypeBCliffordScalarNorm
import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The actual Clifford norm modulo unit squares

The scalar norm formula identifies the image of the literal scalar subgroup.
The standard subgroup comap-map identity then computes the norm preimage of
squares as Spin joined with that scalar subgroup. This step uses neither a
centre identification nor a finite-field, rank or norm-surjectivity input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCliffordNormSquareQuotient

open TypeBCliffordCarriers TypeBCliffordScalarNorm

universe u
variable (n : ℕ) (F : Type u) [Field F] (N : NormSource n F)

/-- On the same actual scalar embedding, the norm is the square homomorphism. -/
theorem norm_comp_scalar :
    N.norm.comp (scalar n F) = powMonoidHom 2 := by
  apply MonoidHom.ext
  intro z
  exact norm_scalar n F N z

/-- The image of the actual scalar subgroup is precisely the unit squares. -/
theorem scalar_range_norm :
    (scalar n F).range.map N.norm = Subgroup.square Fˣ := by
  rw [MonoidHom.map_range, norm_comp_scalar]
  ext z
  simp only [MonoidHom.mem_range, powMonoidHom_apply, Subgroup.mem_square,
    isSquare_iff_exists_sq]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

/-- Exact kernel calculation before any centre or finite-field identification. -/
theorem square_norm_preimage :
    (Subgroup.square Fˣ).comap N.norm =
      SpinSubgroup n F N ⊔ (scalar n F).range := by
  calc
    (Subgroup.square Fˣ).comap N.norm =
        ((scalar n F).range.map N.norm).comap N.norm := by rw [scalar_range_norm]
    _ = (scalar n F).range ⊔ N.norm.ker := Subgroup.comap_map_eq N.norm _
    _ = SpinSubgroup n F N ⊔ (scalar n F).range := sup_comm _ _

/-- An element lies in the literal Spin-scalar join exactly when its norm is square. -/
theorem mem_spin_scalar_iff (g : SpecialClifford n F) :
    g ∈ SpinSubgroup n F N ⊔ (scalar n F).range ↔ IsSquare (N.norm g) := by
  rw [← square_norm_preimage]
  rfl

end ModularRep.PaperProofs.TypeBCliffordNormSquareQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
