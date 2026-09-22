import ManuscriptIBAW.Jordan.GeneralGeometry
import ModularRep.PaperProofs.EvenFieldFLZDefinition35Family

/-!
# The same semisimple series on the ambient block family

The geometric choice and the hypothesis on strict blocks use the same
rational semisimple parameters. The geometric idempotents are identified
with sums over all primitive block idempotents, and each block
parameter is identified with the label used in the strict model.

The finite dual group embeds in the algebraic dual group of that model.
Interpreting this embedding as the inclusion of rational points, and the
semisimple elements and series as the published ones, remains an external
source obligation (U/E1). Character bijections and character triple
relations are separate conclusions.

The action in `series_action` is pushforward by the stated automorphism of
the group algebra. Use the inverse automorphism when comparing it with the
opposite convention for characters.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ManuscriptIBAW.Jordan

open ModularRep.PaperProofs.EvenFieldFLZDefinition35Family
attribute [local instance] Classical.propDecidable

universe u

/-- The sum of the original primitive block idempotents with one
rational conjugacy class of semisimple parameters. -/
def rationalSeriesIdempotent {ell : ℕ} (family : Definition35Family.{u} ell)
    {Dual : Type*} [Group Dual] (blockParameter : family.Block → Dual)
    (t : Dual) : family.k[family.H] := by
  classical
  exact ∑ b, if IsConj (blockParameter b) t then family.blockIdempotent b else 0

/-- Source identifications on the same ambient family and strict label map. The
block parameters are rational semisimple elements of order prime to ell.
Their Broué–Michel sums are the idempotents whose actual automorphism
stabilisers occur in the geometric context. -/
structure SeriesBinding {ell : ℕ} (family : Definition35Family.{u} ell)
    {D E S : Type*} [Group D] [Group E]
    {regular : D →* MulAut family.H} {actor : E →* MulAut family.H}
    (C : GeometricContext (ell := ell) (k := family.k) (S := S) regular actor)
    {StrictDual : Type*} [Group StrictDual]
    (strictLabel : family.Block → StrictDual) where
  blockParameter : family.Block → C.DualFiniteGroup
  blockParameter_semisimple : ∀ b, C.semisimple (blockParameter b)
  blockParameter_order : ∀ b, Nat.Coprime (orderOf (blockParameter b)) ell
  series_eq_sum : ∀ s, C.seriesIdempotent s =
    rationalSeriesIdempotent family blockParameter (C.parameter s)
  dualEmbedding : C.DualFiniteGroup →* StrictDual
  dualEmbedding_injective : Function.Injective dualEmbedding
  strictLabel_eq : ∀ b, strictLabel b = dualEmbedding (blockParameter b)
  semisimple_action : ∀ e t,
    C.semisimple (C.dualFieldAction e t) ↔ C.semisimple t
  series_action : ∀ e t, C.semisimple t → Nat.Coprime (orderOf t) ell →
    MonoidAlgebra.mapDomainRingEquiv family.k (actor e) (C.seriesAtParameter t) =
      C.seriesAtParameter (C.dualFieldAction e t)

section Consequences

variable {ell : ℕ} (family : Definition35Family.{u} ell)
  {Dual : Type*} [Group Dual] (blockParameter : family.Block → Dual)

/-- Multiplication by an original primitive block tests its rational series. -/
theorem block_mul_rationalSeriesIdempotent (b : family.Block) (t : Dual) :
    family.blockIdempotent b * rationalSeriesIdempotent family blockParameter t =
      if IsConj (blockParameter b) t then family.blockIdempotent b else 0 := by
  classical
  unfold rationalSeriesIdempotent
  rw [Finset.mul_sum, Finset.sum_eq_single b]
  · by_cases h : IsConj (blockParameter b) t
    · simp only [if_pos h, (family.blocks.primitive b).idempotent.eq]
    · simp only [if_neg h, mul_zero]
  · intro c _ hcb
    by_cases h : IsConj (blockParameter c) t
    · simp only [if_pos h]
      exact family.blocks.complete.ortho (Ne.symm hcb)
    · simp only [if_neg h, mul_zero]
  · intro h
    exact (h (Finset.mem_univ b)).elim

variable {family}
  {D E S : Type*} [Group D] [Group E]
  {regular : D →* MulAut family.H} {actor : E →* MulAut family.H}
  {C : GeometricContext (ell := ell) (k := family.k) (S := S) regular actor}
  {StrictDual : Type*} [Group StrictDual]
  {strictLabel : family.Block → StrictDual}
  (binding : SeriesBinding family C strictLabel)

/-- Multiplication by the primitive idempotent tests membership in the rational
series through conjugacy in the finite dual group. A zero series contains no
primitive block. -/
theorem SeriesBinding.block_belongs_iff (b : family.Block) (s : S) :
    family.blockIdempotent b * C.seriesIdempotent s = family.blockIdempotent b ↔
      IsConj (binding.blockParameter b) (C.parameter s) := by
  classical
  rw [binding.series_eq_sum,
    block_mul_rationalSeriesIdempotent family binding.blockParameter]
  by_cases h : IsConj (binding.blockParameter b) (C.parameter s)
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]
    constructor
    · intro heq
      exact ((family.blocks.primitive b).ne_zero heq.symm).elim
    · intro hc
      exact (h hc).elim

include binding in
/-- Completeness of the geometric labels covers every original block by the
equation for its primitive idempotent. -/
theorem SeriesBinding.every_block_belongs (b : family.Block) :
    ∃ s, family.blockIdempotent b * C.seriesIdempotent s = family.blockIdempotent b := by
  obtain ⟨s, hs⟩ := C.parameter_complete (binding.blockParameter b)
    (binding.blockParameter_semisimple b) (binding.blockParameter_order b)
  exact ⟨s, (binding.block_belongs_iff b s).mpr hs.symm⟩

end Consequences

end ManuscriptIBAW.Jordan

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
