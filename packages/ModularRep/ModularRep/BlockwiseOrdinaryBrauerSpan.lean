import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Blockwise ordinary--Brauer span equality

This source interface is deliberately global. It contains an ordinary-row
decomposition into Brauer functions with same-block support for nonzero
coefficients, and a universal Brauer-to-ordinary spanning law. It contains no
selected-block span conclusion.
-/

open scoped Classical

namespace ModularRep.BlockwiseOrdinaryBrauerSpan

universe u v w z

variable {K : Type u} {W : Type v}
variable {Ordinary : Type w} {Brauer : Type z} {Block : Type*}
variable [Field K] [AddCommGroup W] [Module K W]

/-- The family whose label is literally `b`. -/
def blockFamily
    (f : Ordinary → W) (ordinaryBlock : Ordinary → Block) (b : Block) :
    {chi : Ordinary // ordinaryBlock chi = b} → W :=
  fun chi => f chi.1

/-- The span of the function family with literal block label `b`. -/
def blockSpan
    (f : Ordinary → W) (ordinaryBlock : Ordinary → Block) (b : Block) :
    Submodule K W :=
  Submodule.span K (Set.range (blockFamily f ordinaryBlock b))

/--
Global decomposition data. brauer_eq_ordinary_combination says that every
Brauer function is a finite K-linear combination of ordinary functions; it is
a global, not selected-block, assertion.
-/
structure GlobalOrdinaryBrauerDecompositionSource
    (ordinary : Ordinary → W) (brauer : Brauer → W)
    (ordinaryBlock : Ordinary → Block) (brauerBlock : Brauer → Block) where
  columns : Ordinary → Brauer →₀ K
  ordinary_eq_decomposition :
    ∀ chi,
      ordinary chi =
        Finsupp.linearCombination K brauer (columns chi)
  column_support :
    ∀ chi phi, columns chi phi ≠ 0 →
      ordinaryBlock chi = brauerBlock phi
  brauer_eq_ordinary_combination :
    ∀ phi, ∃ c : Ordinary →₀ K,
      brauer phi = Finsupp.linearCombination K ordinary c

namespace GlobalOrdinaryBrauerDecompositionSource

variable {ordinary : Ordinary → W} {brauer : Brauer → W}
variable {ordinaryBlock : Ordinary → Block} {brauerBlock : Brauer → Block}

/-- Substitute all ordinary decomposition rows into an ordinary coefficient
vector. -/
theorem ordinary_linearCombination_eq_brauer_linearCombination
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (c : Ordinary →₀ K) :
    Finsupp.linearCombination K ordinary c =
      Finsupp.linearCombination K brauer
        (Finsupp.linearCombination K D.columns c) := by
  calc
    Finsupp.linearCombination K ordinary c =
        Finsupp.linearCombination K
          (fun chi => Finsupp.linearCombination K brauer (D.columns chi)) c := by
      exact congrArg
        (fun f : Ordinary → W => Finsupp.linearCombination K f c)
        (funext fun chi => D.ordinary_eq_decomposition chi)
    _ = Finsupp.linearCombination K brauer
          (Finsupp.linearCombination K D.columns c) :=
      (Finsupp.linearCombination_linearCombination K brauer D.columns c).symm

/-- A column of an ordinary row in `b` survives filtering to `b`. -/
theorem column_filter_eq_self_of_block
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (b : Block) (chi : Ordinary) (hchi : ordinaryBlock chi = b) :
    (D.columns chi).filter (fun phi => brauerBlock phi = b) = D.columns chi := by
  classical
  apply (Finsupp.filter_eq_self_iff _ _).2
  intro phi hphi
  exact (D.column_support chi phi hphi).symm.trans hchi

/-- A column of an ordinary row outside `b` vanishes after filtering to `b`. -/
theorem column_filter_eq_zero_of_ne_block
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (b : Block) (chi : Ordinary) (hchi : ordinaryBlock chi ≠ b) :
    (D.columns chi).filter (fun phi => brauerBlock phi = b) = 0 := by
  classical
  apply (Finsupp.filter_eq_zero_iff _ _).2
  intro phi hphi
  by_contra hzero
  exact hchi ((D.column_support chi phi hzero).trans hphi)

/-- Filtering ordinary coefficients to `b` commutes with the global
decomposition coordinate map. -/
theorem columns_filter_commutes
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (b : Block) (c : Ordinary →₀ K) :
    Finsupp.linearCombination K D.columns
        (c.filter (fun chi => ordinaryBlock chi = b)) =
      (Finsupp.linearCombination K D.columns c).filter
        (fun phi => brauerBlock phi = b) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp only [Finsupp.filter_zero, map_zero]
  | add c d hc hd =>
      simpa [Finsupp.filter_add, hc, hd]
  | single chi a =>
      by_cases hchi : ordinaryBlock chi = b
      · rw [Finsupp.filter_single_of_pos
            (fun chi => ordinaryBlock chi = b) hchi,
          Finsupp.linearCombination_single,
          Finsupp.filter_smul,
          column_filter_eq_self_of_block D b chi hchi]
      · rw [Finsupp.filter_single_of_neg
            (fun chi => ordinaryBlock chi = b) hchi]
        simp only [map_zero, Finsupp.linearCombination_single,
          Finsupp.filter_smul,
          column_filter_eq_zero_of_ne_block D b chi hchi, smul_zero]

/-- A filtered ordinary coefficient vector evaluates into the literal span of
ordinary rows carrying the selected label. -/
theorem ordinary_linearCombination_filter_mem_blockSpan
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (b : Block) (c : Ordinary →₀ K) :
    Finsupp.linearCombination K ordinary
        (c.filter (fun chi => ordinaryBlock chi = b)) ∈
      blockSpan (K := K) ordinary ordinaryBlock b := by
  classical
  rw [Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ (fun chi hchi => ?_)
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨⟨chi, ?_⟩, rfl⟩
  have hcoeff :
      (c.filter (fun chi => ordinaryBlock chi = b)) chi ≠ 0 :=
    Finsupp.mem_support_iff.mp hchi
  by_contra hnot
  apply hcoeff
  simp [Finsupp.filter_apply, hnot]

/-- Every ordinary row in `b` lies in the Brauer span of `b`. -/
theorem ordinary_blockSpan_le_brauer_blockSpan
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (b : Block) :
    blockSpan (K := K) ordinary ordinaryBlock b ≤
      blockSpan (K := K) brauer brauerBlock b := by
  classical
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨chi, hchi⟩, rfl⟩
  change ordinary chi ∈ blockSpan (K := K) brauer brauerBlock b
  rw [D.ordinary_eq_decomposition chi, Finsupp.linearCombination_apply]
  refine Submodule.sum_mem _ (fun phi hphi => ?_)
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨⟨phi, ?_⟩, rfl⟩
  exact (D.column_support chi phi (Finsupp.mem_support_iff.mp hphi)).symm.trans hchi

/-- A Brauer generator in `b` belongs to the ordinary span of `b`.  The
essential step is coordinate equality from global Brauer-function independence.
-/
theorem brauer_generator_mem_ordinary_blockSpan
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (hlinear : LinearIndependent K brauer)
    (b : Block) (phi : Brauer) (hphi : brauerBlock phi = b) :
    brauer phi ∈ blockSpan (K := K) ordinary ordinaryBlock b := by
  classical
  obtain ⟨c, hc⟩ := D.brauer_eq_ordinary_combination phi
  have hcoordinates :
      Finsupp.linearCombination K D.columns c = Finsupp.single phi 1 := by
    apply hlinear.finsuppLinearCombination_injective
    calc
      Finsupp.linearCombination K brauer
          (Finsupp.linearCombination K D.columns c) =
          Finsupp.linearCombination K ordinary c :=
        (ordinary_linearCombination_eq_brauer_linearCombination D c).symm
      _ = brauer phi := hc.symm
      _ = Finsupp.linearCombination K brauer (Finsupp.single phi 1) := by
        simp
  have hfiltered :
      Finsupp.linearCombination K D.columns
          (c.filter (fun chi => ordinaryBlock chi = b)) =
        Finsupp.single phi 1 := by
    calc
      Finsupp.linearCombination K D.columns
          (c.filter (fun chi => ordinaryBlock chi = b)) =
          (Finsupp.linearCombination K D.columns c).filter
            (fun psi => brauerBlock psi = b) :=
        columns_filter_commutes D b c
      _ = (Finsupp.single phi 1).filter (fun psi => brauerBlock psi = b) := by
        rw [hcoordinates]
      _ = Finsupp.single phi 1 :=
        Finsupp.filter_single_of_pos (fun psi => brauerBlock psi = b) hphi
  have hcombination :
      brauer phi = Finsupp.linearCombination K ordinary
        (c.filter (fun chi => ordinaryBlock chi = b)) := by
    calc
      brauer phi = Finsupp.linearCombination K brauer (Finsupp.single phi 1) := by
        simp
      _ = Finsupp.linearCombination K brauer
          (Finsupp.linearCombination K D.columns
            (c.filter (fun chi => ordinaryBlock chi = b))) := by
        rw [hfiltered]
      _ = Finsupp.linearCombination K ordinary
          (c.filter (fun chi => ordinaryBlock chi = b)) :=
        (ordinary_linearCombination_eq_brauer_linearCombination D
          (c.filter (fun chi => ordinaryBlock chi = b))).symm
  rw [hcombination]
  exact ordinary_linearCombination_filter_mem_blockSpan D b c

/-- The blockwise equality is a kernel consequence of global decomposition
data and linear independence; neither side occurs in the source record. -/
theorem blockwise_span_eq
    (D : GlobalOrdinaryBrauerDecompositionSource
      (K := K) ordinary brauer ordinaryBlock brauerBlock)
    (hlinear : LinearIndependent K brauer)
    (b : Block) :
    blockSpan (K := K) ordinary ordinaryBlock b =
      blockSpan (K := K) brauer brauerBlock b := by
  apply le_antisymm
  · exact ordinary_blockSpan_le_brauer_blockSpan D b
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨phi, hphi⟩, rfl⟩
    exact brauer_generator_mem_ordinary_blockSpan D hlinear b phi hphi

/-- A complete selected ordinary family has the same span as its literal
labelled block family. -/
theorem selected_span_eq_blockSpan
    {RowIndex : Type*}
    (ordinary : Ordinary → W) (ordinaryBlock : Ordinary → Block)
    (b : Block) (selected : RowIndex → Ordinary)
    (hcomplete : ∀ chi, ordinaryBlock chi = b ↔ ∃ i, selected i = chi) :
    Submodule.span K (Set.range (fun i => ordinary (selected i))) =
      blockSpan (K := K) ordinary ordinaryBlock b := by
  apply congrArg (Submodule.span K)
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine ⟨⟨selected i, (hcomplete (selected i)).2 ⟨i, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨chi, hchi⟩, rfl⟩
    obtain ⟨i, hi⟩ := (hcomplete chi).1 hchi
    exact ⟨i, by simpa only [hi, blockFamily]⟩

end GlobalOrdinaryBrauerDecompositionSource
end ModularRep.BlockwiseOrdinaryBrauerSpan



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
