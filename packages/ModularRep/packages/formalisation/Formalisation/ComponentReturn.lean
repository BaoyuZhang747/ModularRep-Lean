import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Function.Iterate

/-!
# The combinatorial component-return argument

This file formalises the representation-free core of the lemma labelled
`lem:type-b-component-return` in the manuscript.  After converting the manuscript's right
actions to Lean's left-action convention, `jointStabilizer` represents the stabiliser inside
the unique normal form of a semidirect product.  The local stabiliser factorisation forces the
return around each component cycle to fix the chosen representative.  Iterating the transport
around each cycle then combines a coherent tuple, and a tuple fixed by the cyclic factor has
the required stabiliser factorisation.

The file does **not** formalise the representation theoretic identifications
`IBr (∏ i, H i) ≃ ∏ i, IBr (H i)`, the diagonal automorphism orbits, or the assertion
that the field automorphism permutes those factors as stated in the manuscript.  Those facts
remain inputs from modular character theory.  No axiom is introduced for them here.
-/

namespace Formalisation

section Stabilizers

variable {D E X : Type*} [Group D] [Group E] [MulAction D X] [MulAction E X]

/-- Pairs whose successive `E`- and `D`-actions fix `x`.  Under the unique normal form in a
semidirect product, this is the underlying set of the stabiliser used in the manuscript. -/
def jointStabilizer (x : X) : Set (D × E) :=
  {p | p.1 • (p.2 • x) = x}

/-- Pairs for which the two factors fix `x` separately. -/
def separatedStabilizer (x : X) : Set (D × E) :=
  {p | p.1 • x = x ∧ p.2 • x = x}

/-- The precise local inference in the component-return proof: if some element in the coset
`D · e` fixes `x`, and joint fixedness separates into fixedness under the two factors, then
the return element `e` itself fixes `x`. -/
theorem fixed_return_of_local_factorization
    (x : X) (e : E)
    (hfactor : jointStabilizer (D := D) (E := E) x = separatedStabilizer x)
    (hcoset : ∃ d : D, d • (e • x) = x) :
    e • x = x := by
  obtain ⟨d, hd⟩ := hcoset
  have hmem : (d, e) ∈ jointStabilizer (D := D) (E := E) x := hd
  rw [hfactor] at hmem
  exact hmem.2

/-- If `e` is the return obtained after `length` transport steps, the same local
factorisation makes the full transport fix the chosen representative. -/
theorem fixed_full_transport_of_local_factorization
    (transport : X → X) (length : Nat) (x : X) (e : E)
    (htransport : transport^[length] x = e • x)
    (hfactor : jointStabilizer (D := D) (E := E) x = separatedStabilizer x)
    (hcoset : ∃ d : D, d • (e • x) = x) :
    transport^[length] x = x := by
  rw [htransport]
  exact fixed_return_of_local_factorization x e hfactor hcoset

/-- If the second group fixes `x` pointwise, joint fixedness is equivalent to fixedness under
the two factors separately.  This is the final stabiliser calculation in the manuscript's
component-return proof. -/
theorem jointStabilizer_eq_separated_of_fixed
    (x : X) (hfixed : ∀ e : E, e • x = x) :
    jointStabilizer (D := D) (E := E) x = separatedStabilizer x := by
  ext p
  constructor
  · intro hp
    have he : p.2 • x = x := hfixed p.2
    refine ⟨?_, he⟩
    simpa [jointStabilizer, he] using hp
  · rintro ⟨hd, he⟩
    simpa [jointStabilizer, he] using hd

end Stabilizers

section Cycles

variable {K : Type*}

/-- The index set obtained by writing a permutation as a family of cycles of lengths `n k`.
The positivity hypothesis below ensures that every cycle has a distinguished coordinate `0`.
-/
abbrev ComponentIndex (n : K → Nat) := Σ k, Fin (n k)

/-- Propagate the chosen representative on each cycle by repeatedly applying its transport
map. -/
def propagatedComponent
    (n : K → Nat) (X : K → Type*)
    (transport : ∀ k, X k → X k) (representative : ∀ k, X k) :
    (i : ComponentIndex n) → X i.1
  | ⟨k, j⟩ => (transport k)^[j.1] (representative k)

/-- Propagation starts at the chosen representative. -/
theorem propagatedComponent_zero
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (X : K → Type*) (transport : ∀ k, X k → X k)
    (representative : ∀ k, X k) (k : K) :
    propagatedComponent n X transport representative
        ⟨k, ⟨0, hn k⟩⟩ = representative k := by
  simp [propagatedComponent]

/-- Away from the end of a cycle, the next coordinate is obtained by one application of the
transport map. -/
theorem propagatedComponent_succ
    (n : K → Nat) (X : K → Type*)
    (transport : ∀ k, X k → X k) (representative : ∀ k, X k)
    (k : K) (j : Nat) (hj : j + 1 < n k) :
    propagatedComponent n X transport representative ⟨k, ⟨j + 1, hj⟩⟩ =
      transport k
        (propagatedComponent n X transport representative
          ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩) := by
  simp only [propagatedComponent]
  rw [Function.iterate_succ_apply']

/-- If the full return fixes the representative, propagation also closes up at the end of the
cycle. -/
theorem propagatedComponent_wrap
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (X : K → Type*) (transport : ∀ k, X k → X k)
    (representative : ∀ k, X k)
    (hreturn : ∀ k, (transport k)^[n k] (representative k) = representative k)
    (k : K) :
    transport k
        (propagatedComponent n X transport representative
          ⟨k, ⟨n k - 1, Nat.sub_lt (hn k) Nat.zero_lt_one⟩⟩) =
      propagatedComponent n X transport representative ⟨k, ⟨0, hn k⟩⟩ := by
  simp only [propagatedComponent]
  rw [← Function.iterate_succ_apply' (transport k) (n k - 1) (representative k)]
  have hsucc : n k - 1 + 1 = n k := Nat.sub_add_cancel (hn k)
  have hsucc' : (n k - 1).succ = n k := by
    simpa [Nat.succ_eq_add_one] using hsucc
  rw [hsucc', hreturn]
  simp

/-- Representatives whose returns are fixed combine into one tuple satisfying the transport
rule on every component cycle, including the return from its last coordinate to its first.

This is the product construction used in the component-return lemma.  The proof works for an
arbitrary family of cycles because finiteness and cyclicity are used in the manuscript only to
obtain the cycle decomposition and the return hypotheses. -/
theorem component_return_assembly
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (X : K → Type*) (transport : ∀ k, X k → X k)
    (representative : ∀ k, X k)
    (hreturn : ∀ k, (transport k)^[n k] (representative k) = representative k) :
    ∃ theta : (i : ComponentIndex n) → X i.1,
      (∀ k,
        theta ⟨k, ⟨0, hn k⟩⟩ = representative k) ∧
      (∀ k j (hj : j + 1 < n k),
        theta ⟨k, ⟨j + 1, hj⟩⟩ =
          transport k (theta ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)) ∧
      (∀ k,
        transport k (theta ⟨k, ⟨n k - 1, Nat.sub_lt (hn k) Nat.zero_lt_one⟩⟩) =
          theta ⟨k, ⟨0, hn k⟩⟩) := by
  let theta := propagatedComponent n X transport representative
  refine ⟨theta, ?_, ?_, ?_⟩
  · exact propagatedComponent_zero n hn X transport representative
  · exact propagatedComponent_succ n X transport representative
  · exact propagatedComponent_wrap n hn X transport representative hreturn

end Cycles

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
