import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Fin.Basic

/-!
# Normalising actual monomial cycles without a root of the return

The original factor carrier may vary at every position. The input consists
of the original edge group isomorphisms, the actual wrap isomorphism, and
the coordinate equations of the original automorphism. Successor maps in
the normalised presentation are proved to be identities. The wrap is the
composite of the original edges and is proved to be the literal full power
of that same automorphism on the base coordinate.

Positive cycle lengths are written m(c)+1. Choosing a cycle enumeration is
presentation data; no normalised equation, character action, stabilizer
factorization, or root of a return is a premise. Everything in this file
is finite group-coordinate deduction.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBComponentCycleNormalization

open ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter

universe u v w

section Cycles

variable {C : Type u} (m : C → ℕ)

abbrev Index := Σ c, Fin (m c + 1)

abbrev first (c : C) : Index m := ⟨c, 0⟩
abbrev last (c : C) : Index m := ⟨c, Fin.last (m c)⟩

variable (H : Index m → Type v) [∀ i, Group (H i)]

abbrev Original := (i : Index m) → H i
abbrev Base (c : C) := H (first m c)
abbrev Normalized := (i : Index m) → Base m H i.1

/-- The original monomial edges in one forward pullback step. Different
edges have different literal domain and codomain groups. -/
structure CycleCoordinates where
  edge : ∀ c (j : Fin (m c)),
    H ⟨c, j.succ⟩ ≃* H ⟨c, j.castSucc⟩
  wrap : ∀ c, H (first m c) ≃* H (last m c)

variable (S : CycleCoordinates m H)

/-- Coordinate j is identified with coordinate zero by the actual
successive edge maps. No root of the wrap is selected. -/
def toBase (c : C) : (j : Fin (m c + 1)) → H ⟨c, j⟩ ≃* Base m H c :=
  Fin.induction (MulEquiv.refl _) (fun j e => (S.edge c j).trans e)

@[simp]
theorem toBase_zero (c : C) : toBase m H S c 0 = MulEquiv.refl _ := rfl

@[simp]
theorem toBase_succ (c : C) (j : Fin (m c)) :
    toBase m H S c j.succ = (S.edge c j).trans (toBase m H S c j.castSucc) := rfl

/-- The literal group equivalence from the varying original factors to the
repeated base factor on each cycle. -/
def productEquiv : Original m H ≃* Normalized m H :=
  MulEquiv.piCongrRight fun i => toBase m H S i.1 i.2

@[simp]
theorem productEquiv_apply (g : Original m H) (i : Index m) :
    productEquiv m H S g i = toBase m H S i.1 i.2 (g i) := rfl

@[simp]
theorem productEquiv_symm_apply (g : Normalized m H) (i : Index m) :
    (productEquiv m H S).symm g i = (toBase m H S i.1 i.2).symm (g i) := rfl

/-- The entire original circuit, based at coordinate zero. -/
def fullReturn (c : C) : MulAut (Base m H c) :=
  (S.wrap c).trans (toBase m H S c (Fin.last (m c)))

/-- Conjugation through the constructed group equivalence. -/
def normalizedAut (a : MulAut (Original m H)) : MulAut (Normalized m H) :=
  MulAut.congr (productEquiv m H S) a

@[simp]
theorem normalizedAut_apply (a : MulAut (Original m H)) (g : Normalized m H) :
    normalizedAut m H S a g =
      productEquiv m H S (a ((productEquiv m H S).symm g)) := rfl

/-- These are equations of the ORIGINAL, possibly nonuniform monomial
action; they are not the normalised conclusion. -/
structure MonomialAction (a : MulAut (Original m H)) : Prop where
  successor : ∀ (g : Original m H) c (j : Fin (m c)),
    a g ⟨c, j.castSucc⟩ = S.edge c j (g ⟨c, j.succ⟩)
  wrap : ∀ (g : Original m H) c,
    a g (last m c) = S.wrap c (g (first m c))

variable {a : MulAut (Original m H)} (h : MonomialAction m H S a)

include h in
/-- All successor coordinates become identities under the computed change
of coordinates. -/
theorem normalized_successor (g : Normalized m H) c (j : Fin (m c)) :
    normalizedAut m H S a g ⟨c, j.castSucc⟩ = g ⟨c, j.succ⟩ := by
  change toBase m H S c j.castSucc
    (a ((productEquiv m H S).symm g) ⟨c, j.castSucc⟩) = _
  rw [h.successor]
  change toBase m H S c j.succ
    ((toBase m H S c j.succ).symm (g ⟨c, j.succ⟩)) = _
  exact (toBase m H S c j.succ).apply_symm_apply _

include h in
/-- The only nontrivial normalised edge is the actual full return on the
wrap. No common transport with a prescribed power is assumed. -/
theorem normalized_wrap (g : Normalized m H) c :
    normalizedAut m H S a g (last m c) =
      fullReturn m H S c (g (first m c)) := by
  change toBase m H S c (Fin.last (m c))
    (a ((productEquiv m H S).symm g) (last m c)) = _
  rw [h.wrap]
  rfl

include h in
/-- The coordinate identifications are literally the restrictions of powers
of the original generator, not independently chosen group isomorphisms. -/
theorem toBase_eq_power (c : C) (j : Fin (m c + 1)) :
    ∀ g : Original m H,
      toBase m H S c j (g ⟨c, j⟩) = (a ^ j.1) g (first m c) := by
  refine Fin.induction ?_ ?_ j
  · intro g
    rfl
  · intro i ih g
    change toBase m H S c i.castSucc (S.edge c i (g ⟨c, i.succ⟩)) =
      (a ^ (i.1 + 1)) g (first m c)
    rw [pow_succ]
    change _ = (a ^ i.1) (a g) (first m c)
    change _ = (a ^ i.castSucc.1) (a g) (first m c)
    rw [← ih (a g), h.successor]

include h in
/-- The wrap composite equals the full actual generator power on its first
coordinate, on EVERY original product element. -/
theorem fullReturn_eq_power (c : C) (g : Original m H) :
    fullReturn m H S c (g (first m c)) =
      (a ^ (m c + 1)) g (first m c) := by
  rw [pow_succ]
  change toBase m H S c (Fin.last (m c)) (S.wrap c (g (first m c))) =
    (a ^ m c) (a g) (first m c)
  change _ = (a ^ (Fin.last (m c)).1) (a g) (first m c)
  rw [← toBase_eq_power m H S h c (Fin.last (m c)) (a g), h.wrap]

include h in
/-- The normalized return has the same full-power interpretation. -/
theorem normalized_full_power (c : C) (g : Normalized m H) :
    (normalizedAut m H S a ^ (m c + 1)) g (first m c) =
      fullReturn m H S c (g (first m c)) := by
  have heq : normalizedAut m H S a ^ (m c + 1) =
      normalizedAut m H S (a ^ (m c + 1)) :=
    (map_pow (MulAut.congr (productEquiv m H S)) a (m c + 1)).symm
  rw [heq]
  change (a ^ (m c + 1)) ((productEquiv m H S).symm g) (first m c) = _
  rw [← fullReturn_eq_power m H S h]
  rfl

/-- An entire external action is transported through the same equivalence,
so the normalized generator is a value of a genuine homomorphism. -/
def normalizedAction {E : Type w} [Group E]
    (outer : E →* MulAut (Original m H)) : E →* MulAut (Normalized m H) :=
  (MulAut.congr (productEquiv m H S)).toMonoidHom.comp outer

@[simp]
theorem normalizedAction_apply {E : Type w} [Group E]
    (outer : E →* MulAut (Original m H)) (e : E) :
    normalizedAction m H S outer e = normalizedAut m H S (outer e) := rfl

end Cycles

section PairCompatibility

variable {C : Type u} (m : C → ℕ)
variable (H D : Index m → Type v)
variable [∀ i, Group (H i)] [∀ i, Group (D i)]
variable (SH : CycleCoordinates m H) (SD : CycleCoordinates m D)
variable (diagonal : ∀ i, D i →* MulAut (H i))

/-- The original edge isomorphisms carry the original pairs (H_i,D_i)
to one another. These are pointwise equations in the ORIGINAL factors. -/
structure PairEdges : Prop where
  successor : ∀ c (j : Fin (m c)) (d : D ⟨c, j.succ⟩) (x : H ⟨c, j.succ⟩),
    SH.edge c j (diagonal ⟨c, j.succ⟩ d x) =
      diagonal ⟨c, j.castSucc⟩ (SD.edge c j d) (SH.edge c j x)
  wrap : ∀ c (d : D (first m c)) (x : H (first m c)),
    SH.wrap c (diagonal (first m c) d x) =
      diagonal (last m c) (SD.wrap c d) (SH.wrap c x)

variable (pairs : PairEdges m H D SH SD diagonal)

include pairs in
/-- The derived coordinate identifications preserve the literal diagonal
action. This is proved simultaneously along all edges. -/
theorem toBase_diagonal (c : C) (j : Fin (m c + 1)) :
    ∀ (d : D ⟨c, j⟩) (x : H ⟨c, j⟩),
      toBase m H SH c j (diagonal ⟨c, j⟩ d x) =
        diagonal (first m c) (toBase m D SD c j d) (toBase m H SH c j x) := by
  refine Fin.induction ?_ ?_ j
  · intro d x
    rfl
  · intro i ih d x
    change toBase m H SH c i.castSucc
      (SH.edge c i (diagonal ⟨c, i.succ⟩ d x)) = _
    rw [pairs.successor, ih]
    rfl

include pairs in
/-- Both actual return automorphisms preserve the original base-factor
diagonal action. The return-normalization law is a deduction. -/
theorem fullReturn_diagonal (c : C) (d : D (first m c)) (x : H (first m c)) :
    fullReturn m H SH c (diagonal (first m c) d x) =
      diagonal (first m c) (fullReturn m D SD c d) (fullReturn m H SH c x) := by
  change toBase m H SH c (Fin.last (m c))
    (SH.wrap c (diagonal (first m c) d x)) = _
  rw [pairs.wrap, toBase_diagonal m H D SH SD diagonal pairs]
  rfl

include pairs in
/-- The full coordinate diagonal action is transported to the repeated
base-factor coordinate action. No character action is a premise. -/
theorem normalized_diagonal (d : Original m D) :
    normalizedAut m H SH (coordinateMulAut H D diagonal d) =
      coordinateMulAut (fun i : Index m => Base m H i.1)
        (fun i : Index m => Base m D i.1)
        (fun i => diagonal (first m i.1)) (productEquiv m D SD d) := by
  apply MulEquiv.ext
  intro x
  funext i
  change toBase m H SH i.1 i.2
      (diagonal i (d i) ((toBase m H SH i.1 i.2).symm (x i))) =
    diagonal (first m i.1) (toBase m D SD i.1 i.2 (d i)) (x i)
  rw [toBase_diagonal m H D SH SD diagonal pairs]
  rw [MulEquiv.apply_symm_apply]

include pairs in
/-- Conjugation compatibility survives the simultaneous computed transport
of H and D. It is not a new normalization source premise. -/
theorem normalized_actions_compatible
    {E : Type (max u v)} [Group E]
    (outer : E →* MulAut (Original m H))
    (phi : E →* MulAut (Original m D))
    (compatible : AutomorphismSemidirectCompatible
      (coordinateMulAut H D diagonal) outer phi) :
    AutomorphismSemidirectCompatible
      (coordinateMulAut (fun i : Index m => Base m H i.1)
        (fun i : Index m => Base m D i.1)
        (fun i => diagonal (first m i.1)))
      (normalizedAction m H SH outer) (normalizedAction m D SD phi) := by
  intro e d
  obtain ⟨d0, rfl⟩ := (productEquiv m D SD).surjective d
  have h := congrArg (normalizedAut m H SH) (compatible e d0)
  rw [normalized_diagonal m H D SH SD diagonal pairs] at h
  change _ = normalizedAut m H SH
    (outer e * coordinateMulAut H D diagonal d0 * (outer e)⁻¹) at h
  simp only [normalizedAut, map_mul, map_inv] at h
  rw [← normalized_diagonal m H D SH SD diagonal pairs d0]
  have heD : normalizedAction m D SD phi e (productEquiv m D SD d0) =
      productEquiv m D SD (phi e d0) := by
    change productEquiv m D SD
      (phi e ((productEquiv m D SD).symm (productEquiv m D SD d0))) = _
    rw [MulEquiv.symm_apply_apply]
  rw [heD]
  exact h

end PairCompatibility

end ModularRep.PaperProofs.TypeBComponentCycleNormalization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
