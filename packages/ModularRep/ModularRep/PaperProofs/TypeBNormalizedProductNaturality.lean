import ModularRep.PaperProofs.TypeBComponentReturnSourceInstantiation
import ModularRep.PaperProofs.TypeBFiniteProductNaturality
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The component-return character formula from external-product values

This module removes the monomial-naturality field from the E1 boundary of
the component-return application.  Rotation is an actual permutation of the
finite cycle indices.  The group-level successor and wrap equations imply
the corresponding value equations, and finite-product reindexing determines
the actual tuple of Brauer characters.  The only character-theoretic input
is `ExternalProductData`: prime, coherent roots, the external-product
equivalence and its literal value formula (Navarro (8.21), pp. 176--177).
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBNormalizedProductNaturality

open Formalisation
open ModularRep.ManuscriptVerification.ComponentReturnFull
open TypeBComponentReturnSourceInstantiation
open TypeBFiniteProductNaturality

section Rotation

/-- Rotation of an arbitrary positive cycle sends its last coordinate to zero. -/
theorem rotate_last (n : ℕ) (hn : 0 < n) :
    finRotate n ⟨n - 1, Nat.sub_lt hn Nat.zero_lt_one⟩ = ⟨0, hn⟩ := by
  cases n with
  | zero => omega
  | succ m => simpa using finRotate_last' (n := m)

/-- Rotation sends an interior coordinate to its successor. -/
theorem rotate_succ (n j : ℕ) (hj : j + 1 < n) :
    finRotate n ⟨j, Nat.lt_of_succ_lt hj⟩ = ⟨j + 1, hj⟩ := by
  cases n with
  | zero => omega
  | succ m =>
      have h : j < m := by omega
      exact finRotate_of_lt h

variable {C : Type*} (n : C → ℕ)

/-- The permutation rotates each cycle without changing its cycle label. -/
def cycleRotate : Equiv.Perm (ComponentIndex n) :=
  Equiv.sigmaCongrRight (fun c ↦ finRotate (n c))

@[simp] theorem cycleRotate_apply (c : C) (j : Fin (n c)) :
    cycleRotate n ⟨c, j⟩ = ⟨c, finRotate (n c) j⟩ := rfl

end Rotation

section ActualValues

variable {p : ℕ} {C k K : Type} [Fintype C]
variable (n : C → ℕ) (hn : ∀ c, 0 < n c) (H : C → Type)
variable [∀ c, Group (H c)] [∀ c, Finite (H c)]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K (ProductGroup n H))
variable (factorRoot : ∀ c, PrimeRegularRootEmbedding p k K (H c))
variable (source : ExternalProductData
  (fun i : ComponentIndex n ↦ H i.1) iota (fun i ↦ factorRoot i.1))

/-- The tuple prescribed by identity successor maps and the actual return
at the wrap.  This is a definition for every character, not a selected fixed tuple. -/
def normalisedTuple (psi : IBr iota) (returnAut : ∀ c, MulAut (H c)) :
    (i : ComponentIndex n) → IBr (factorRoot i.1) := fun i ↦
  if hi : i.2.1 = 0 then
    IrreducibleBrauerCharacter.twist (factorRoot i.1)
      (source.characters psi (lastIndex n hn i.1)) (returnAut i.1)
  else
    source.characters psi
      ⟨i.1, ⟨i.2.1 - 1, (Nat.sub_le i.2.1 1).trans_lt i.2.2⟩⟩

@[simp] theorem normalisedTuple_first (psi : IBr iota)
    (returnAut : ∀ c, MulAut (H c)) (c : C) :
    normalisedTuple n hn H iota factorRoot source psi returnAut (firstIndex n hn c) =
      IrreducibleBrauerCharacter.twist (factorRoot c)
        (source.characters psi (lastIndex n hn c)) (returnAut c) := by
  simp [normalisedTuple]

@[simp] theorem normalisedTuple_succ (psi : IBr iota)
    (returnAut : ∀ c, MulAut (H c)) (c : C) (j : ℕ) (hj : j + 1 < n c) :
    normalisedTuple n hn H iota factorRoot source psi returnAut ⟨c, ⟨j + 1, hj⟩⟩ =
      source.characters psi ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ := by
  simp [normalisedTuple]

/-- The group-level normalised coordinate equations determine the full
tuple of the twisted character by the actual finite rotation. -/
theorem characters_twist_normalised
    (a : MulAut (ProductGroup n H)) (returnAut : ∀ c, MulAut (H c))
    (hfirst : ∀ g c,
      a g (lastIndex n hn c) = returnAut c (g (firstIndex n hn c)))
    (hsucc : ∀ g c j (hj : j + 1 < n c),
      a g ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ = g ⟨c, ⟨j + 1, hj⟩⟩)
    (psi : IBr iota) :
    source.characters (IrreducibleBrauerCharacter.twist iota psi a) =
      normalisedTuple n hn H iota factorRoot source psi returnAut := by
  apply characters_twist_of_reindexed_values
    (fun i : ComponentIndex n ↦ H i.1) iota (fun i ↦ factorRoot i.1) source
    a psi _ (cycleRotate n)
  intro g i
  rcases i with ⟨c, j⟩
  change (source.characters psi ⟨c, j⟩).1
      (PrimeRegularElement.map
        (projection (fun i : ComponentIndex n ↦ H i.1) ⟨c, j⟩)
        (PrimeRegularElement.map a.toMonoidHom g)) =
    (normalisedTuple n hn H iota factorRoot source psi returnAut
      ⟨c, finRotate (n c) j⟩).1
      (PrimeRegularElement.map
        (projection (fun i : ComponentIndex n ↦ H i.1) ⟨c, finRotate (n c) j⟩) g)
  by_cases hlast : j.1 = n c - 1
  · have hj : j = (lastIndex n hn c).2 := Fin.ext hlast
    subst j
    rw [rotate_last, normalisedTuple_first]
    change (source.characters psi (lastIndex n hn c)).1
        ⟨a g.1 (lastIndex n hn c), _⟩ =
      (source.characters psi (lastIndex n hn c)).1
        ⟨returnAut c (g.1 (firstIndex n hn c)), _⟩
    congr 1
    apply Subtype.ext
    exact hfirst g.1 c
  · have hj : j.1 + 1 < n c := by omega
    have hrot : finRotate (n c) j = ⟨j.1 + 1, hj⟩ := rotate_succ (n c) j.1 hj
    rw [hrot, normalisedTuple_succ]
    congr 1
    apply Subtype.ext
    exact hsucc g.1 c j.1 hj

variable (D : C → Type) [∀ c, Group (D c)]
variable (diagonal : ∀ c, D c →* MulAut (H c))

/-- The old component-return interface is produced from the strictly
narrower source.  Both coordinate and normalised permutation naturality
are theorems, so neither remains an external input to this constructor. -/
def toFiniteProductSource : FiniteProductSource n hn H D iota factorRoot diagonal where
  characters := source.characters
  coordinate_naturality := TypeBFiniteProductNaturality.coordinate_naturality
    (fun i : ComponentIndex n ↦ H i.1) iota (fun i ↦ factorRoot i.1) source
    (fun i : ComponentIndex n ↦ D i.1) (fun i ↦ diagonal i.1)
  prime := source.prime
  roots_agree c := source.roots_agree (firstIndex n hn c)
  external_product := source.external_product
  normalised_naturality := by
    intro a returnAut hfirst hsucc
    constructor
    · intro psi c
      rw [characters_twist_normalised n hn H iota factorRoot source a returnAut hfirst hsucc]
      exact normalisedTuple_first n hn H iota factorRoot source psi returnAut c
    · intro psi c j hj
      rw [characters_twist_normalised n hn H iota factorRoot source a returnAut hfirst hsucc]
      exact normalisedTuple_succ n hn H iota factorRoot source psi returnAut c j hj

end ActualValues

end ModularRep.PaperProofs.TypeBNormalizedProductNaturality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
