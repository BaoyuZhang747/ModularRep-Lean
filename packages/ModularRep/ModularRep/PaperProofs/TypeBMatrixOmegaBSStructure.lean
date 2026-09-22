import ModularRep.PaperProofs.TypeBSpinDiagonalNormSource
import ModularRep.PaperProofs.TypeBMatrixOmegaFullAutomorphismBinding
import Mathlib.GroupTheory.Index

/-!
# Structural deductions on the literal matrix Omega carrier

The constructed Clifford norm and its square classes determine the index
of the actual derived SO subgroup. The accepted full ambient centralizer
identity detects its centre through the fixed injective embedding.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBMatrixOmegaBSStructure

open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBCliffordOrthogonalSourceBinding TypeBCliffordOrthogonalAmbientQuotient
open TypeBFiniteFieldSquareClass TypeBOrthogonalAmbientOmegaBinding
open EvenFieldFLZ318FixedTheoremGate

/-- The independently defined matrix subgroup is the actual derived SO. -/
theorem omega_derived (n : ℕ) (F : Type) [Field F] :
    commutator (SpecialOrthogonal n F) = omegaSubgroup n F := rfl

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]

/-- The displayed projection and norm have exactly the same square preimage. -/
theorem omega_comap_projection
    (N : NormSource n F) (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
    (C : Source n F p f parameters rank N) :
    (omegaSubgroup n F).comap (projection n F C.det_one) =
      (squareSubgroup F).comap N.norm := by
  ext g
  change projection n F C.det_one g ∈ omegaSubgroup n F ↔
    N.norm g ∈ squareSubgroup F
  rw [C.norm_square_criterion, mem_squareSubgroup_iff_exists_sq]
  exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩

/-- Surjective preimages and the two unit square classes give the literal index. -/
theorem omega_index_two
    (N : NormSource n F) (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
    (C : Source n F p f parameters rank N) :
    (omegaSubgroup n F).index = 2 := by
  calc
    (omegaSubgroup n F).index =
        ((omegaSubgroup n F).comap (projection n F C.det_one)).index :=
      ((omegaSubgroup n F).index_comap_of_surjective C.onto).symm
    _ = ((squareSubgroup F).comap N.norm).index :=
      congrArg Subgroup.index (omega_comap_projection N parameters rank C)
    _ = (squareSubgroup F).index :=
      (squareSubgroup F).index_comap_of_surjective
        (TypeBCliffordNormSurjectivity.norm_surjective n F
          ((by decide : 1 ≤ 3).trans rank) N)
    _ = 2 := squareClass_card F
      (TypeBSpinDiagonalNormSource.odd_card_of_parameters F parameters)

/-- A central matrix-Omega element lies in the proved trivial ambient centralizer. -/
theorem omega_center_eq_bot
    (N : NormSource n F) (parameters : OddFieldParameters F p f)
    (S : FieldActionSource n F p f parameters N) (rank : 3 ≤ n)
    (C : Source n F p f parameters rank N)
    (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource n p f F N)
    (fullCover : IsUniversalCentralExtension (spinProjection n F parameters rank N C))
    (centreClifford : TypeBCliffordCentreSource.CentreSource n F parameters
      ((by decide : 1 ≤ 3).trans rank))
    (naturalKernel : (TypeBAutomorphismSource.ambientAutomorphism S).ker =
      TypeBAutomorphismSource.embeddedCenter S) :
    Subgroup.center (Omega n F) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  have centralizes : omegaEmbedding S rank C z ∈ Subgroup.centralizer
      (embeddedOmega S rank C : Set (OrthogonalAmbient n F parameters rank N C S)) := by
    apply Subgroup.mem_centralizer_iff.mpr
    rintro _ ⟨x, rfl⟩
    exact (map_mul (omegaEmbedding S rank C) x z).symm.trans
      ((congrArg (omegaEmbedding S rank C) (Subgroup.mem_center_iff.mp hz x)).trans
        (map_mul (omegaEmbedding S rank C) z x))
  rw [TypeBMatrixOmegaFullAutomorphismBinding.centralizer_eq_bot
    S rank C centreSpin fullCover centreClifford naturalKernel] at centralizes
  have value : omegaEmbedding S rank C z = 1 := centralizes
  change z = 1
  exact omegaEmbedding_injective S rank C
    (value.trans (map_one (omegaEmbedding S rank C)).symm)

end ModularRep.PaperProofs.TypeBMatrixOmegaBSStructure


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
