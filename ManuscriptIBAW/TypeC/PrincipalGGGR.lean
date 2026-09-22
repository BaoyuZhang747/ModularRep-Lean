import ManuscriptIBAW.TypeC.GGGRSelection
import ManuscriptIBAW.TypeC.PrincipalParameterActions
import ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness

/-!
# Selected CSp characters and the principal Sp calculation

The finite descent in Taylor 2013, Proposition 5.4, uses restriction,
GGGR induction, Frobenius reciprocity, Clifford theory and condition (P5).
The identities below concern the actual matrix groups and rational
conjugacy classes. Their geometric validity is external. The column sums,
row sums, coverage and lower character selection are proved.

Vanishing from wave front sets is a separate assumption. The character
selection and triangularity proved here are separate from the assumptions
used for principal block Brauer characters. Field invariance and the
required counts are assumed explicitly from Feng–Malle 2022, Sections 4
and 6. The deduction of these statements from the selected rows is not
formalised here.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeC.PrincipalGGGR

open ModularRep OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs
open OddTwoConformalProjectiveRealisation (Sp CSp spEmbedding)
open OddTwoPrincipalIntrinsicCarrier (PrincipalCharacterData)
open OddTwoPrincipalFieldFixedness
open scoped BigOperators

universe u

attribute [local instance] Classical.propDecidable
local instance (priority := low) finiteFintype (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

section Arithmetic

variable {I J U : Type u} [Fintype I] [Fintype J] [Nonempty I] [DecidableEq U]

/-- Column sums, matching cardinalities and row permutation symmetry
force each natural row to have sum one. -/
theorem row_sum_one (entries : I → J → ℕ) (classMap : J → U) (j : U)
    (column_sum : ∀ c, ∑ i, entries i c = if classMap c = j then 1 else 0)
    (p5_count : Fintype.card I = ∑ c : J, if classMap c = j then 1 else 0)
    (row_symmetry : ∀ i k, ∃ e : Equiv.Perm J, ∀ c, entries i (e c) = entries k c)
    (i : I) : ∑ c, entries i c = 1 := by
  classical
  have uniform : ∀ k, ∑ c, entries k c = ∑ c, entries i c := by
    intro k
    obtain ⟨e, he⟩ := row_symmetry k i
    exact (Fintype.sum_equiv e (entries i) (entries k) (fun c => (he c).symm)).symm
  have total : Fintype.card I * (∑ c, entries i c) = Fintype.card I := by
    calc
      Fintype.card I * (∑ c, entries i c) = ∑ k : I, ∑ c, entries k c := by
        simp only [uniform, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      _ = ∑ c : J, ∑ k : I, entries k c := Finset.sum_comm
      _ = ∑ c : J, if classMap c = j then 1 else 0 := by simp only [column_sum]
      _ = Fintype.card I := p5_count.symm
  have card_ne_zero : Fintype.card I ≠ 0 := Nat.ne_of_gt Fintype.card_pos
  apply mul_left_cancel₀ card_ne_zero
  simpa only [mul_one] using total

end Arithmetic

variable {n p : ℕ} {F K : Type u} [Field F] [Fintype F]
  [Field K] [CharZero K]

/-- Actual Sp conjugacy classes containing an element whose order is a power
of the defining prime. Their geometric labels are part of the source interpretation. -/
def LowerClass (n p : ℕ) (F : Type u) [Field F] : Type u :=
  {c : ConjClasses (Sp n F) //
    ∃ g : Sp n F, ConjClasses.mk g = c ∧ ∃ a : ℕ, g ^ (p ^ a) = 1}

instance lowerClass_finite : Finite (LowerClass n p F) := by
  let : Finite (ConjClasses (Sp n F)) :=
    Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  unfold LowerClass
  infer_instance

def lowerRepresentative (c : LowerClass n p F) : Sp n F := Classical.choose c.property

def scalarProduct (x y : Sp n F → K) : K :=
  (Nat.card (Sp n F) : K)⁻¹ * ∑ g, x g⁻¹ * y g

/-- The fixed geometry of the two groups. The class equation ties the map
to the literal matrix inclusion, rather than an arbitrary finite map. -/
structure Geometry (n p : ℕ) (F K : Type u) [Field F] [Finite F]
    [Field K] [CharZero K] where
  Class : Type u
  upperClass : GGGRSelection.UnipotentClass n p F → Class
  classMap : LowerClass n p F → GGGRSelection.UnipotentClass n p F
  classMap_actual : ∀ c, (classMap c).val =
    ConjClasses.mk (spEmbedding n F (lowerRepresentative c))
  family : Class → Set (Irr K (CSp n F))
  upperDual : Irr K (CSp n F) → Irr K (CSp n F)
  lowerDual : Irr K (Sp n F) → Irr K (Sp n F)
  upperGamma : ∀ C, GGGRSelection.RationalFibre upperClass C → CSp n F → K
  gamma : LowerClass n p F → Sp n F → K
  classOrder : Class → ℕ
  classOrder_separates : ∀ c d : LowerClass n p F,
    classOrder (upperClass (classMap c)) = classOrder (upperClass (classMap d)) →
      upperClass (classMap c) = upperClass (classMap d)
  support : Irr K (Sp n F) → Class
  lowerAut : CSp n F → MulAut (Sp n F)
  lowerAut_actual : ∀ g x,
    spEmbedding n F (lowerAut g x) = g * spEmbedding n F x * g⁻¹

namespace Geometry

variable (G : Geometry n p F K)

abbrev geometricClass (c : LowerClass n p F) : G.Class := G.upperClass (G.classMap c)
abbrev Fibre (C : G.Class) := {c : LowerClass n p F // G.geometricClass c = C}

def upperMap {C : G.Class} (c : G.Fibre C) :
    GGGRSelection.RationalFibre G.upperClass C := ⟨G.classMap c.val, c.property⟩

end Geometry

variable (G : Geometry n p F K) (C : G.Class)

/-- Restriction and Clifford data for the selected family.
Taylor 2013, Theorem 3.2(P5), enters the constituent and class counts in
the proof of Proposition 5.4. Here p5_count states their resulting equality:
at a nonzero upper entry, the number of restriction constituents equals
the number of lower rational classes above that upper class.
The lower delta selection and coverage are proved below. -/
structure P5Source where
  constituents : G.family C → Finset (Irr K (Sp n F))
  constituents_nonempty : ∀ Phi, (constituents Phi).Nonempty
  constituent_support : ∀ Phi (theta : ↑(constituents Phi)), G.support theta.val = C
  restriction : ∀ (Phi : G.family C) x, Phi.val.val (spEmbedding n F x) =
    ∑ theta ∈ constituents Phi, theta.val x
  dualRestriction : ∀ (Phi : G.family C) x, (G.upperDual Phi.val).val (spEmbedding n F x) =
    ∑ theta ∈ constituents Phi, (G.lowerDual theta).val x
  reciprocity : ∀ (Phi : G.family C) (c : G.Fibre C),
    scalarProduct (fun x => (G.upperDual Phi.val).val (spEmbedding n F x)) (G.gamma c.val) =
      GGGRSelection.scalarProduct (G.upperDual Phi.val).val (G.upperGamma C (G.upperMap c))
  nonnegative : ∀ theta : Irr K (Sp n F), ∀ c : G.Fibre C,
    ∃ a : ℕ, scalarProduct (G.lowerDual theta).val (G.gamma c.val) = (a : K)
  classAction : CSp n F → Equiv.Perm (G.Fibre C)
  classAction_actual : ∀ g c,
    ((classAction g c).val).val =
      ConjClasses.mk (G.lowerAut g (lowerRepresentative c.val))
  cliffordTransitive : ∀ Phi (theta eta : ↑(constituents Phi)),
    ∃ g : CSp n F, twist K (Sp n F) theta.val (G.lowerAut g).symm = eta.val
  conjugationPairing : ∀ (theta : Irr K (Sp n F)) g (c : G.Fibre C),
    scalarProduct (G.lowerDual (twist K (Sp n F) theta (G.lowerAut g).symm)).val
      (G.gamma (classAction g c).val) =
        scalarProduct (G.lowerDual theta).val (G.gamma c.val)
  p5_count : ∀ (Phi : G.family C) (j : GGGRSelection.RationalFibre G.upperClass C),
    GGGRSelection.scalarProduct (G.upperDual Phi.val).val (G.upperGamma C j) ≠ 0 →
    (constituents Phi).card = ∑ c : G.Fibre C, if G.upperMap c = j then 1 else 0
  waveFront : ∀ Phi (theta : ↑(constituents Phi)) (d : LowerClass n p F),
    G.classOrder (G.geometricClass d) < G.classOrder C →
      scalarProduct (G.lowerDual theta.val).val (G.gamma d) = 0

namespace P5Source

variable {G C} (S : P5Source G C)

def entry (theta : Irr K (Sp n F)) (c : G.Fibre C) : ℕ :=
  Classical.choose (S.nonnegative theta c)

theorem entry_cast (theta : Irr K (Sp n F)) (c : G.Fibre C) :
    (S.entry theta c : K) = scalarProduct (G.lowerDual theta).val (G.gamma c.val) :=
  (Classical.choose_spec (S.nonnegative theta c)).symm

/-- Finite linearity and the stated restriction identity give the column
sum in Frobenius reciprocity. -/
theorem column_sum_cast (Phi : G.family C) (c : G.Fibre C) :
    ((∑ theta : ↑(S.constituents Phi), S.entry theta.val c) : K) =
      GGGRSelection.scalarProduct (G.upperDual Phi.val).val (G.upperGamma C (G.upperMap c)) := by
  rw [← S.reciprocity Phi c]
  simp only [S.entry_cast, scalarProduct]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [S.dualRestriction]
  simp only [Finset.sum_mul]
  exact Finset.sum_attach (S.constituents Phi)
    (fun theta => (G.lowerDual theta).val x⁻¹ * G.gamma c.val x)

/-- Actual Clifford conjugation preserves the row total through its
permutation of all lower rational classes in the geometric fibre. -/
theorem row_symmetry (Phi : G.family C) (theta eta : ↑(S.constituents Phi)) :
    ∃ e : Equiv.Perm (G.Fibre C), ∀ c, S.entry theta.val (e c) = S.entry eta.val c := by
  obtain ⟨g, same⟩ := S.cliffordTransitive Phi eta theta
  refine ⟨S.classAction g, ?_⟩
  intro c
  apply Nat.cast_injective (R := K)
  rw [S.entry_cast, S.entry_cast, ← same]
  exact S.conjugationPairing eta.val g c

end P5Source

/-- Upper geometric sources and lower descent assumptions for the same
geometric class. The upper character selection is proved from these
assumptions. -/
structure FamilySource [CharP F p] where
  Component : Type u
  [componentGroup : Group Component]
  [componentFinite : Finite Component]
  selected : GGGRSelection.SelectedFamilySource Component G.upperClass C
    (G.family C) G.upperDual (G.upperGamma C)
  descent : P5Source G C

attribute [instance] FamilySource.componentGroup FamilySource.componentFinite

variable [CharP F p]

namespace FamilySource

variable {G C} (S : FamilySource G C)

/-- P5 and Clifford symmetry descend the constructed upper delta rows.
Every selected lower row is an actual restriction constituent. -/
theorem lower_selection : ∃ select : G.Fibre C → Irr K (Sp n F),
    (∀ c, ∃ Phi : G.family C, select c ∈ S.descent.constituents Phi) ∧
    Function.Injective select ∧
    ∀ c d, scalarProduct (G.lowerDual (select c)).val (G.gamma d.val) =
      if d = c then 1 else 0 := by
  classical
  obtain ⟨upper, _, upper_delta⟩ := GGGRSelection.delta_selection S.selected
  let Row := Σ j, ↑(S.descent.constituents (upper j))
  let a : Row → G.Fibre C → ℕ := fun r c => S.descent.entry r.2.val c
  have column : ∀ j (c : G.Fibre C),
      ∑ theta : ↑(S.descent.constituents (upper j)),
        S.descent.entry theta.val c = if G.upperMap c = j then 1 else 0 := by
    intro j c
    apply Nat.cast_injective (R := K)
    push_cast
    rw [S.descent.column_sum_cast, upper_delta]
  have sum_one : ∀ r : Row, ∑ c, a r c = 1 := by
    intro r
    let : Nonempty ↑(S.descent.constituents (upper r.1)) :=
      ⟨r.2⟩
    have count : Fintype.card ↑(S.descent.constituents (upper r.1)) =
        ∑ c : G.Fibre C, if G.upperMap c = r.1 then 1 else 0 := by
      rw [Fintype.card_coe]
      apply S.descent.p5_count (upper r.1) r.1
      rw [upper_delta]
      simp
    exact row_sum_one
      (I := ↑(S.descent.constituents (upper r.1)))
      (J := G.Fibre C) (U := GGGRSelection.RationalFibre G.upperClass C)
      (fun theta c => S.descent.entry theta.val c) G.upperMap r.1
      (column r.1) count (S.descent.row_symmetry (upper r.1)) r.2
  have covered : ∀ c : G.Fibre C, ∃ r : Row, a r c ≠ 0 := by
    intro c
    have positive := column (G.upperMap c) c
    simp only [ite_true] at positive
    have witness : ∃ theta : ↑(S.descent.constituents (upper (G.upperMap c))),
        S.descent.entry theta.val c ≠ 0 := by
      by_contra none
      push Not at none
      simp only [none, Finset.sum_const_zero] at positive
      omega
    obtain ⟨theta, nonzero⟩ := witness
    exact ⟨⟨G.upperMap c, theta⟩, nonzero⟩
  obtain ⟨pick, _, delta⟩ :=
    ManuscriptIBAW.FiniteCharacterSelection.exists_delta_injection a sum_one covered
  let select : G.Fibre C → Irr K (Sp n F) := fun c => (pick c).2.val
  have actual_delta : ∀ c d,
      scalarProduct (G.lowerDual (select c)).val (G.gamma d.val) =
        if d = c then 1 else 0 := by
    intro c d
    rw [← S.descent.entry_cast]
    change (a (pick c) d : K) = _
    rw [delta]
    split_ifs <;> simp
  refine ⟨select, ?_, ?_, actual_delta⟩
  · intro c
    exact ⟨upper (pick c).1, (pick c).2.property⟩
  · intro c d same
    by_contra different
    have equal := congrArg
      (fun theta => scalarProduct (G.lowerDual theta).val (G.gamma c.val)) same
    rw [actual_delta c c, actual_delta d c] at equal
    simp [different] at equal

def lowerSelect : G.Fibre C → Irr K (Sp n F) :=
  Classical.choose S.lower_selection

theorem lowerSelect_constituent (c : G.Fibre C) :
    ∃ Phi : G.family C, S.lowerSelect c ∈ S.descent.constituents Phi :=
  (Classical.choose_spec S.lower_selection).1 c

theorem lowerSelect_injective : Function.Injective S.lowerSelect :=
  (Classical.choose_spec S.lower_selection).2.1

theorem lowerSelect_delta (c d : G.Fibre C) :
    scalarProduct (G.lowerDual (S.lowerSelect c)).val (G.gamma d.val) =
      if d = c then 1 else 0 :=
  (Classical.choose_spec S.lower_selection).2.2 c d

theorem lowerSelect_support (c : G.Fibre C) : G.support (S.lowerSelect c) = C := by
  obtain ⟨Phi, member⟩ := S.lowerSelect_constituent c
  exact S.descent.constituent_support Phi ⟨_, member⟩

theorem lowerSelect_vanishing (c : G.Fibre C) (d : LowerClass n p F)
    (earlier : G.classOrder (G.geometricClass d) < G.classOrder C) :
    scalarProduct (G.lowerDual (S.lowerSelect c)).val (G.gamma d) = 0 := by
  obtain ⟨Phi, member⟩ := S.lowerSelect_constituent c
  exact S.descent.waveFront Phi ⟨_, member⟩ d earlier

end FamilySource

variable (sources : ∀ C, FamilySource G C)

/-- Selected lower characters with their upper family constituent witnesses,
injectivity, delta values within each geometric class and vanishing in the
chosen class order. Their construction does not establish the subsequent
statements about principal block Brauer characters. -/
structure LowerTriangularData where
  beforeDual : LowerClass n p F → Irr K (Sp n F)
  upperWitness : ∀ c, ∃ Phi : G.family (G.geometricClass c),
    beforeDual c ∈ (sources (G.geometricClass c)).descent.constituents Phi
  injective : Function.Injective beforeDual
  diagonal : ∀ c d, G.geometricClass c = G.geometricClass d →
    scalarProduct (G.lowerDual (beforeDual c)).val (G.gamma d) = if d = c then 1 else 0
  lower_zero : ∀ c d, G.classOrder (G.geometricClass d) < G.classOrder (G.geometricClass c) →
    scalarProduct (G.lowerDual (beforeDual c)).val (G.gamma d) = 0

namespace LowerTriangularData

variable {G sources} (rows : LowerTriangularData G sources)

/-- In the chosen ordering of geometric classes, the complete matrix has
diagonal entries one and all entries below the diagonal zero. -/
theorem at_or_below (c d : LowerClass n p F)
    (earlier : G.classOrder (G.geometricClass d) ≤ G.classOrder (G.geometricClass c)) :
    scalarProduct (G.lowerDual (rows.beforeDual c)).val (G.gamma d) =
      if d = c then 1 else 0 := by
  rcases lt_or_eq_of_le earlier with before | same
  · have different : d ≠ c := by
      intro equal
      subst d
      exact Nat.lt_irrefl _ before
    rw [rows.lower_zero c d before, if_neg different]
  · exact rows.diagonal c d (G.classOrder_separates d c same).symm

end LowerTriangularData

/-- Combine the selections for individual geometric classes. Support
identifies their geometric classes. The proved delta rows distinguish
rational classes in one fibre. -/
def lowerTriangular : LowerTriangularData G sources := by
  let row : LowerClass n p F → Irr K (Sp n F) := fun c =>
    (sources (G.geometricClass c)).lowerSelect ⟨c, rfl⟩
  have row_support : ∀ c, G.support (row c) = G.geometricClass c := by
    intro c
    exact (sources (G.geometricClass c)).lowerSelect_support ⟨c, rfl⟩
  have diagonal : ∀ c d, G.geometricClass c = G.geometricClass d →
      scalarProduct (G.lowerDual (row c)).val (G.gamma d) = if d = c then 1 else 0 := by
    intro c d same
    have delta := (sources (G.geometricClass c)).lowerSelect_delta
      ⟨c, rfl⟩ ⟨d, same.symm⟩
    simpa only [Subtype.mk.injEq] using delta
  refine
    { beforeDual := row
      upperWitness := ?_
      injective := ?_
      diagonal := diagonal
      lower_zero := ?_ }
  · intro c
    exact (sources (G.geometricClass c)).lowerSelect_constituent ⟨c, rfl⟩
  · intro c d same
    have sameClass : G.geometricClass c = G.geometricClass d := by
      rw [← row_support c, ← row_support d, same]
    by_contra different
    have equal := congrArg
      (fun theta => scalarProduct (G.lowerDual theta).val (G.gamma c)) same
    rw [diagonal c c rfl, diagonal d c sameClass.symm] at equal
    simp [different] at equal
  · intro c d earlier
    exact (sources (G.geometricClass c)).lowerSelect_vanishing ⟨c, rfl⟩ d earlier

section Principal

variable {k Block : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
  [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block)) (diagonal : MulAut (Sp n F))

/-- The external principal block Brauer character statements used in the
higher rank application. Field invariance is Feng–Malle Corollary 4.3(a).
The numerical source lists the parametrisation and counting results it uses.
These statements are not deduced from the character selection above. -/
structure PrincipalSource : Prop where
  fieldFixed : FengMalleCorollary43aSource D
  counts : FMPrincipalCountSource D diagonal

end Principal

end ManuscriptIBAW.TypeC.PrincipalGGGR

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
