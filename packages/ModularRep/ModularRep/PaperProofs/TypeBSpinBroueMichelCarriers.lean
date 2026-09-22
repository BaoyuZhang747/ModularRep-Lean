import ModularRep.PaperProofs.TypeBSpinConlonBlockSourceInstantiation

/-!
# The full Broue--Michel union on the actual dual PCSp carrier

The ordinary family is indexed by all defining-prime regular rational
classes, before selecting the ell-prime classes. The full union uses actual
commuting ell-elements of PCSp, the quotient by ALL nonzero scalars. Its
product's defining-prime guard is proved. No block assignment, integral
map, basic set, or character correspondence is supplied here.

FLZ Section 2.4.1--2.4.2, printed p.537, fixes the rational series and this
union; Section 3.1 fixes the Spin/PCSp duality. Authenticating the externally
provided full family, with its coefficient and finite-point interpretation,
remains explicit. Constructing these carriers alone does not do that.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpinBroueMichelCarriers

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBConformalDualCarriers TypeBSpinConlonBlockSourceInstantiation
open TypeBRationalSeriesSource

variable {n p ell : ℕ} {F K : Type} [Field F] [Field K]

/-- All rational semisimple classes, with the finite-point semisimplicity
condition expressed as defining-prime regularity. -/
def FullRationalIndex (p n : ℕ) (F : Type) [Field F] :=
  {c : ConjClasses (PCSp F n) //
    ∃ g : PCSp F n, ConjClasses.mk g = c ∧ p.Coprime (orderOf g)}

/-- Forget only the modular-prime guard, retaining the identical class. -/
def fullIndex (i : RationalIndex p ell n F) : FullRationalIndex p n F :=
  ⟨i.val, by
    obtain ⟨g, hg, hp, _⟩ := i.property
    exact ⟨g, hg, hp⟩⟩

@[simp] theorem fullIndex_val (i : RationalIndex p ell n F) :
    (fullIndex i).val = i.val := rfl

theorem fullIndex_injective : Function.Injective (fullIndex (p := p) (ell := ell)
    (n := n) (F := F)) := by
  intro i j h
  exact Subtype.ext (congrArg (fun c : FullRationalIndex p n F => c.val) h)

/-- Literal representatives of the old selected rational index. -/
abbrev AdmissibleParameter :=
  {s : PCSp F n // p.Coprime (orderOf s) ∧ ell.Coprime (orderOf s)}

def parameterIndex (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F)) :
    RationalIndex p ell n F :=
  ⟨ConjClasses.mk s.val, s.val, rfl, s.property⟩

@[simp] theorem parameterIndex_val
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F)) :
    (parameterIndex s).val = ConjClasses.mk s.val := rfl

theorem parameterIndex_surjective : Function.Surjective
    (parameterIndex (p := p) (ell := ell) (n := n) (F := F)) := by
  intro i
  obtain ⟨s, hs, hp, he⟩ := i.property
  exact ⟨⟨s, hp, he⟩, Subtype.ext hs⟩

/-- The selected family is a restriction of the one full family; no second
rational-series predicate or disjointness source is introduced. -/
def selectedFamily {N : NormSource n F}
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F)) :
    RationalSeriesSource K (Spin n F N) (RationalIndex p ell n F) where
  rationalSeries i := S.rationalSeries (fullIndex i)
  disjoint hi hj := fullIndex_injective (S.disjoint hi hj)

@[simp] theorem selectedFamily_mem {N : NormSource n F}
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))
    (i : RationalIndex p ell n F) (chi : Irr K (Spin n F N)) :
    chi ∈ (selectedFamily S).rationalSeries i ↔
      chi ∈ S.rationalSeries (fullIndex i) := Iff.rfl

/-- Every t is literally in the centralizer of this actual representative.
The order is measured in PCSp, not in a chosen matrix lift. -/
abbrev CentralizerEllElement
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F)) :=
  {t : Subgroup.centralizer ({s.val} : Set (PCSp F n)) //
    ∃ a : ℕ, orderOf (t.val : PCSp F n) = ell ^ a}

def oneEllElement
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F)) :
    CentralizerEllElement s := ⟨1, 0, by simp⟩

theorem centralizerEllElement_commute
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F))
    (t : CentralizerEllElement s) : Commute s.val (t.val : PCSp F n) := by
  exact (Subgroup.mem_centralizer_singleton_iff.mp t.val.property).symm

theorem centralizerEllElement_order_coprime (hp : p.Prime) (he : ell.Prime)
    (hne : ell ≠ p)
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F))
    (t : CentralizerEllElement s) : p.Coprime (orderOf (t.val : PCSp F n)) := by
  obtain ⟨a, ha⟩ := t.property
  rw [ha]
  exact ((Nat.coprime_primes hp he).mpr hne.symm).pow_right a

theorem product_order_coprime (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F))
    (t : CentralizerEllElement s) : p.Coprime (orderOf (s.val * (t.val : PCSp F n))) := by
  exact (s.property.1.mul_right
    (centralizerEllElement_order_coprime hp he hne s t)).of_dvd_right
      (centralizerEllElement_commute s t).orderOf_mul_dvd_mul_orderOf

/-- The full rational class of the actual commuting product. -/
def productIndex (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F))
    (t : CentralizerEllElement s) : FullRationalIndex p n F :=
  ⟨ConjClasses.mk (s.val * (t.val : PCSp F n)),
    s.val * (t.val : PCSp F n), rfl, product_order_coprime hp he hne s t⟩

@[simp] theorem productIndex_val (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F))
    (t : CentralizerEllElement s) :
    (productIndex hp he hne s t).val = ConjClasses.mk (s.val * (t.val : PCSp F n)) := rfl

@[simp] theorem productIndex_one (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F)) :
    productIndex hp he hne s (oneEllElement s) = fullIndex (parameterIndex s) := by
  apply Subtype.ext
  change ConjClasses.mk (s.val * 1) = ConjClasses.mk s.val
  rw [mul_one]

/-- The entire Broue--Michel ordinary union, not merely its t=1 part. -/
def ordinaryUnion {N : NormSource n F}
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))
    (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F))
    (chi : Irr K (Spin n F N)) : Prop :=
  ∃ t : CentralizerEllElement s, chi ∈ S.rationalSeries (productIndex hp he hne s t)

/-- Existential representatives keep the class-indexed union independent
of any separate representative choice or free block map. -/
def indexedOrdinaryUnion {N : NormSource n F}
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))
    (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (i : RationalIndex p ell n F) (chi : Irr K (Spin n F N)) : Prop :=
  ∃ s : AdmissibleParameter (p := p) (ell := ell) (n := n) (F := F),
    parameterIndex s = i ∧ ordinaryUnion S hp he hne s chi

theorem selectedFamily_mem_indexedOrdinaryUnion {N : NormSource n F}
    (S : RationalSeriesSource K (Spin n F N) (FullRationalIndex p n F))
    (hp : p.Prime) (he : ell.Prime) (hne : ell ≠ p)
    (i : RationalIndex p ell n F) (chi : Irr K (Spin n F N))
    (hchi : chi ∈ (selectedFamily S).rationalSeries i) :
    indexedOrdinaryUnion S hp he hne i chi := by
  obtain ⟨s, rfl⟩ := parameterIndex_surjective i
  refine ⟨s, rfl, oneEllElement s, ?_⟩
  simpa only [productIndex_one, selectedFamily_mem] using hchi

end ModularRep.PaperProofs.TypeBSpinBroueMichelCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
