import ModularRep.CharacterWeightBlockAssignment
import ModularRep.GroupAlgebraClassSums

/-! Specified block induction through an actual quotient square.
These neutral algebra proofs are copied narrowly from the read-only Type B
module; no Type B source or transport endpoint is imported. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra

open ModularRep

universe u
section Algebra

variable {k G H : Type u} [Field k] [Group G] [Group H]

/-- The group-basis algebra map for the displayed homomorphism. -/
def algebraMapOf (f : G →* H) : k[G] →ₐ[k] k[H] :=
  MonoidAlgebra.mapDomainAlgHom k k f

@[simp] theorem algebraMapOf_single (f : G →* H) (g : G) (a : k) :
    algebraMapOf f (MonoidAlgebra.single g a) = MonoidAlgebra.single (f g) a := by
  simp [algebraMapOf]

/-- A surjective group map carries central group algebra elements to
central elements.  This does not claim surjectivity on the centres. -/
def centerMap (f : G →* H) (hf : Function.Surjective f) :
    GroupAlgebraCenter k G →ₐ[k] GroupAlgebraCenter k H where
  toFun z := ⟨algebraMapOf f z.val, by
    rw [Subalgebra.mem_center_iff]
    intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [add_mul, mul_add, ha, hb]
    | single h a =>
      obtain ⟨g, rfl⟩ := hf h
      have hz := Subalgebra.mem_center_iff.mp z.property (MonoidAlgebra.single g a)
      simpa only [map_mul, algebraMapOf_single] using congrArg (algebraMapOf f) hz⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  commutes' a := Subtype.ext ((algebraMapOf f).commutes a)

@[simp] theorem centerMap_val (f : G →* H) (hf : Function.Surjective f)
    (z : GroupAlgebraCenter k G) :
    (centerMap f hf z).val = algebraMapOf f z.val := rfl

variable [Fintype G] [Fintype H]

/-- The coefficient-restriction square on a full subgroup preimage.  It
is proved on actual single group algebra terms before restricting to centres. -/
theorem coefficient_restriction_square
    (f : G →* H) (U : Subgroup G) (V : Subgroup H)
    (fU : U →* V) (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V) (z : k[G]) :
    algebraMapOf fU (coeffRestrict U z) =
      coeffRestrict V (algebraMapOf f z) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g a =>
    rw [algebraMapOf_single]
    by_cases hg : g ∈ U
    · have hfg : f g ∈ V := (saturated g).mp hg
      simp only [coeffRestrict_single, dif_pos hg, dif_pos hfg, algebraMapOf_single]
      congr 1
      exact Subtype.ext (square ⟨g, hg⟩)
    · have hfg : f g ∉ V := fun h => hg ((saturated g).mpr h)
      simp only [coeffRestrict_single, dif_neg hg, dif_neg hfg, map_zero]

theorem center_restriction_square
    (f : G →* H) (hf : Function.Surjective f)
    (U : Subgroup G) (V : Subgroup H)
    (fU : U →* V) (hfU : Function.Surjective fU)
    (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V)
    (z : GroupAlgebraCenter k G) :
    centerMap fU hfU (centerCoeffRestrict U z) =
      centerCoeffRestrict V (centerMap f hf z) := by
  apply Subtype.ext
  exact coefficient_restriction_square f U V fU square saturated z.val

end Algebra

section CentralCharacters

variable {k G H I J : Type u} [Field k] [IsAlgClosed k]
  [Group G] [Group H] [Fintype G] [Fintype H] [Fintype I] [Fintype J]
  {eG : I → k[G]} {eH : J → k[H]}
  {dG : BlockIdempotentDecomposition eG} {dH : BlockIdempotentDecomposition eH}

/-- Equality of the specified idempotents under q# forces the corresponding
central character pullback law.  Catalogue exhaustivity and delta suffice. -/
theorem centralCharacter_pullback
    (f : G →* H) (hf : Function.Surjective f)
    (cG : BlockCentralCharacterCatalogue dG)
    (cH : BlockCentralCharacterCatalogue dH)
    (b : I) (c : J) (physical : algebraMapOf f (eG b) = eH c)
    (z : GroupAlgebraCenter k G) :
    cH.centralCharacter c (centerMap f hf z) = cG.centralCharacter b z := by
  let lambda := (cH.centralCharacter c).comp (centerMap f hf)
  obtain ⟨b', hb'⟩ := cG.exhaustive lambda
  have hcenter : centerMap f hf (dG.blockIdempotentInCenter b) =
      dH.blockIdempotentInCenter c := Subtype.ext physical
  have heq : b' = b := by
    by_contra hne
    have hv := congrArg (fun l : GroupAlgebraCenter k G →ₐ[k] k =>
      l (dG.blockIdempotentInCenter b)) hb'
    change cG.centralCharacter b' (dG.blockIdempotentInCenter b) =
      cH.centralCharacter c (centerMap f hf (dG.blockIdempotentInCenter b)) at hv
    rw [cG.centralCharacter_other hne, hcenter, cH.centralCharacter_own] at hv
    exact zero_ne_one hv
  subst b'
  exact (congrArg (fun l : GroupAlgebraCenter k G →ₐ[k] k => l z) hb').symm

end CentralCharacters

section Induction

variable {k G H BU BD LU LD : Type u} [Field k] [IsAlgClosed k]
  [Group G] [Group H] [Fintype G] [Fintype H]
  [Fintype BU] [Fintype BD] [Fintype LU] [Fintype LD]

variable (U : Subgroup G) (V : Subgroup H)
local instance : Fintype U := Fintype.ofFinite _
local instance : Fintype V := Fintype.ofFinite _

variable {eGU : BU → k[G]} {eHD : BD → k[H]}
  {eU : LU → k[U]} {eV : LD → k[V]}
  {dGU : BlockIdempotentDecomposition eGU} {dHD : BlockIdempotentDecomposition eHD}
  {dU : BlockIdempotentDecomposition eU} {dV : BlockIdempotentDecomposition eV}

/-- Block induction is transported using actual q# idempotent equalities.
The target induced function is evaluated at q#B, and its catalogue delta
law identifies the block.  No ambient-block matching is a source premise. -/
theorem blockInducesTo_map
    (f : G →* H) (hf : Function.Surjective f)
    (fU : U →* V) (hfU : Function.Surjective fU)
    (square : ∀ x : U, (fU x : H) = f x)
    (saturated : ∀ g : G, g ∈ U ↔ f g ∈ V)
    (cGU : BlockCentralCharacterCatalogue dGU) (cHD : BlockCentralCharacterCatalogue dHD)
    (cU : BlockCentralCharacterCatalogue dU) (cV : BlockCentralCharacterCatalogue dV)
    (bU : LU) (bV : LD) (BU' : BU) (BD' : BD)
    (localPhysical : algebraMapOf fU (eU bU) = eV bV)
    (globalPhysical : algebraMapOf f (eGU BU') = eHD BD')
    (upInduces : BlockInducesTo U cU cGU bU BU')
    (downDefined : IsBlockInductionDefined V (cV.centralCharacter bV)) :
    BlockInducesTo V cV cHD bV BD' := by
  obtain ⟨hup, hequp⟩ := upInduces
  let B := inducedBlock V cV cHD bV downDefined
  have hcenter : centerMap f hf (dGU.blockIdempotentInCenter BU') =
      dHD.blockIdempotentInCenter BD' := Subtype.ext globalPhysical
  have hvalue : cHD.centralCharacter B (dHD.blockIdempotentInCenter BD') = 1 := by
    rw [inducedBlock_centralCharacter V cV cHD bV downDefined]
    change cV.centralCharacter bV
      (centerCoeffRestrict V (dHD.blockIdempotentInCenter BD')) = 1
    rw [← hcenter, ← center_restriction_square f hf U V fU hfU square saturated]
    rw [centralCharacter_pullback fU hfU cU cV bU bV localPhysical]
    change inducedCentralCharacter U (cU.centralCharacter bU) hup
      (dGU.blockIdempotentInCenter BU') = 1
    rw [hequp, cGU.centralCharacter_own]
  have hB : B = BD' := by
    by_contra hne
    rw [cHD.centralCharacter_other hne] at hvalue
    exact zero_ne_one hvalue
  rw [← hB]
  exact inducedBlock_spec V cV cHD bV downDefined

end Induction


end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
