import ModularRep.PaperProofs.TypeBRankThreeJordanCliffordCarriers
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The natural diagonal quotient on the original finite carriers

The map is induced by the actual paired-Levi inclusion into finite special
Clifford, followed by its quotient by the same Spin norm kernel. Geometric
intersection identifies its kernel with the original rational L inside M.
The preceding rational product deduction supplies surjectivity. The first
isomorphism theorem then gives the quotient identification with its value
on every original element. No abstract quotient isomorphism is sourced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreeJordanQuotient

open TypeBCliffordCarriers TypeBRegularLeviRationalCarriers
open TypeBRankThreeJordanCliffordCarriers

variable {p f : ℕ} {F A : Type}
variable [Field F] [Finite F] [CharP F p] [Field A] [Algebra F A]
variable {N : NormSource 3 F} {Nbar : NormSource 3 A}
variable {Frob : MulAut (SpecialClifford 3 A)}
variable (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
variable (Lbar : Subgroup (SpecialClifford 3 A))

/-- The original rational L as a subgroup of the same rational paired Levi. -/
abbrev leviInGamma : Subgroup (M Frob.toMonoidHom Lbar) :=
  (L Frob.toMonoidHom Lbar).subgroupOf (M Frob.toMonoidHom Lbar)

instance leviInGamma_normal : (leviInGamma (Frob := Frob) Lbar).Normal :=
  L_normal_M Frob.toMonoidHom Lbar

/-- The quotient map is the composite of the actual inclusion and Spin quotient. -/
def gammaQuotient : M Frob.toMonoidHom Lbar →*
    SpecialClifford 3 F ⧸ SpinSubgroup 3 F N :=
  (QuotientGroup.mk' (SpinSubgroup 3 F N)).comp (gammaEmbedding points Lbar)

@[simp] theorem gammaQuotient_value (x : M Frob.toMonoidHom Lbar) :
    gammaQuotient points Lbar x =
      QuotientGroup.mk' (SpinSubgroup 3 F N) (gammaEmbedding points Lbar x) := rfl

theorem gammaQuotient_kernel
    (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)
    (intersection : pairedLevi Lbar ⊓ SpinSubgroup 3 A Nbar ≤ Lbar) :
    (gammaQuotient points Lbar).ker = leviInGamma (Frob := Frob) Lbar := by
  ext x
  change (gammaEmbedding points Lbar x : SpecialClifford 3 F ⧸ SpinSubgroup 3 F N) = 1 ↔
    x.val.val ∈ Lbar
  rw [QuotientGroup.eq_one_iff,
    ← inclusion_spin_iff 3 p f F A N Nbar Frob points,
    gammaEmbedding_inclusion]
  exact ⟨fun h => intersection ⟨x.property, h⟩, fun h => levi_le_spin h⟩

/-- Surjectivity follows from the already proved rational product, with the
Spin factor killed by this same quotient map. -/
theorem gammaQuotient_surjective
    (product : ∀ a : SpecialClifford 3 F,
      ∃ g : Spin 3 F N, ∃ m : M Frob.toMonoidHom Lbar,
        a = (g : SpecialClifford 3 F) * gammaEmbedding points Lbar m) :
    Function.Surjective (gammaQuotient points Lbar) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨g, m, rfl⟩ := product a
  refine ⟨m, ?_⟩
  change QuotientGroup.mk' (SpinSubgroup 3 F N) (gammaEmbedding points Lbar m) =
    QuotientGroup.mk' (SpinSubgroup 3 F N)
      ((g : SpecialClifford 3 F) * gammaEmbedding points Lbar m)
  have hg : QuotientGroup.mk' (SpinSubgroup 3 F N) (g : SpecialClifford 3 F) = 1 :=
    (QuotientGroup.eq_one_iff (g : SpecialClifford 3 F)).mpr g.property
  rw [map_mul, hg, one_mul]

/-- The exact quotient identification induced by the original Levi inclusion. -/
def diagonalQuotientEquiv
    (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)
    (intersection : pairedLevi Lbar ⊓ SpinSubgroup 3 A Nbar ≤ Lbar)
    (product : ∀ a : SpecialClifford 3 F,
      ∃ g : Spin 3 F N, ∃ m : M Frob.toMonoidHom Lbar,
        a = (g : SpecialClifford 3 F) * gammaEmbedding points Lbar m) :
    M Frob.toMonoidHom Lbar ⧸ leviInGamma (Frob := Frob) Lbar ≃*
      SpecialClifford 3 F ⧸ SpinSubgroup 3 F N :=
  (QuotientGroup.quotientMulEquivOfEq
    (gammaQuotient_kernel points Lbar levi_le_spin intersection).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (gammaQuotient points Lbar)
        (gammaQuotient_surjective points Lbar product))

@[simp] theorem diagonalQuotientEquiv_value
    (levi_le_spin : Lbar ≤ SpinSubgroup 3 A Nbar)
    (intersection : pairedLevi Lbar ⊓ SpinSubgroup 3 A Nbar ≤ Lbar)
    (product : ∀ a : SpecialClifford 3 F,
      ∃ g : Spin 3 F N, ∃ m : M Frob.toMonoidHom Lbar,
        a = (g : SpecialClifford 3 F) * gammaEmbedding points Lbar m)
    (m : M Frob.toMonoidHom Lbar) :
    diagonalQuotientEquiv points Lbar levi_le_spin intersection product
        (QuotientGroup.mk' (leviInGamma (Frob := Frob) Lbar) m) =
      QuotientGroup.mk' (SpinSubgroup 3 F N) (gammaEmbedding points Lbar m) := rfl

end ModularRep.PaperProofs.TypeBRankThreeJordanQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
