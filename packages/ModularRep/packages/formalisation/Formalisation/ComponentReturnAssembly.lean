import Formalisation.ComponentReturn
import Formalisation.SemidirectStabilizer

/-!
# Component return from actual semidirect-product stabilizers

This module connects the two abstract parts of the manuscript's component-return argument.
First, a stabilizer factorization inside an actual Mathlib semidirect product forces the return
element on each component cycle to fix the chosen representative.  The cycle-propagation
theorem from `Formalisation.ComponentReturn` then combines those representatives into a tuple
that satisfies the transport rule, including the wrap from the last coordinate to the first.

The theorem deliberately stops at that coherent tuple.  The present abstract data do not
include the product-character identification, the component permutation action on the product,
or the diagonal orbit containing the tuple.  Consequently, membership in the character orbit
and the final global stabilizer equality are not asserted here.
-/

namespace Formalisation

section LocalReturn

variable {D E X : Type*} [Group D] [Group E]
variable [MulAction D X] [MulAction E X]

/-- The elementwise form of stabilizer factorization for an actual compatible action of
`D ⋊ E` on `X`. -/
def SemidirectStabilizerFactors (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi) (x : X) : Prop :=
  let _ := semidirectMulAction phi hcompat
  ∀ p : D ⋊[phi] E,
    p ∈ MulAction.stabilizer (D ⋊[phi] E) x ↔
      p.left ∈ MulAction.stabilizer D x ∧
        p.right ∈ MulAction.stabilizer E x

/-- If an element of the coset `D e` fixes `x`, factorization of the actual semidirect-product
stabilizer forces `e` itself to fix `x`. -/
theorem fixed_return_of_semidirect_factorization
    (phi : E →* MulAut D)
    (hcompat : SemidirectActionCompatible (X := X) phi)
    (x : X) (e : E)
    (hfactor : SemidirectStabilizerFactors phi hcompat x)
    (hcoset : ∃ d : D, d • (e • x) = x) :
    e • x = x := by
  let _ := semidirectMulAction phi hcompat
  obtain ⟨d, hd⟩ := hcoset
  have hp : (⟨d, e⟩ : D ⋊[phi] E) ∈ MulAction.stabilizer (D ⋊[phi] E) x := by
    exact hd
  exact ((hfactor ⟨d, e⟩).mp hp).2

end LocalReturn

section Assembly

variable {K : Type*}
variable (D E X : K → Type*)
variable [∀ k, Group (D k)] [∀ k, Group (E k)]
variable [∀ k, MulAction (D k) (X k)] [∀ k, MulAction (E k) (X k)]

/-- Local semidirect-product factorization on each cycle forces every return to close, and the
closed returns combine into a coherent dependent tuple.

The first conjunct records the derived fixedness of each return element.  The second is the
strongest tuple statement available from the abstract cycle data: it gives the selected
representative at coordinate zero, propagation along a cycle, and the wrap condition. -/
theorem component_return_assembly_of_semidirect_factorization
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (phi : ∀ k, E k →* MulAut (D k))
    (hcompat : ∀ k, SemidirectActionCompatible (X := X k) (phi k))
    (transport : ∀ k, X k → X k)
    (representative : ∀ k, X k)
    (returnElement : ∀ k, E k)
    (htransport : ∀ k,
      (transport k)^[n k] (representative k) = returnElement k • representative k)
    (hfactor : ∀ k,
      SemidirectStabilizerFactors (phi k) (hcompat k) (representative k))
    (hcoset : ∀ k, ∃ d : D k,
      d • (returnElement k • representative k) = representative k) :
    (∀ k, returnElement k • representative k = representative k) ∧
      ∃ theta : (i : ComponentIndex n) → X i.1,
        (∀ k, theta ⟨k, ⟨0, hn k⟩⟩ = representative k) ∧
        (∀ k j (hj : j + 1 < n k),
          theta ⟨k, ⟨j + 1, hj⟩⟩ =
            transport k (theta ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)) ∧
        (∀ k,
          transport k
              (theta ⟨k, ⟨n k - 1, Nat.sub_lt (hn k) Nat.zero_lt_one⟩⟩) =
            theta ⟨k, ⟨0, hn k⟩⟩) := by
  have hfixed : ∀ k, returnElement k • representative k = representative k := by
    intro k
    exact fixed_return_of_semidirect_factorization
      (phi k) (hcompat k) (representative k) (returnElement k)
      (hfactor k) (hcoset k)
  have hreturn : ∀ k,
      (transport k)^[n k] (representative k) = representative k := by
    intro k
    rw [htransport, hfixed]
  exact ⟨hfixed,
    component_return_assembly n hn X transport representative hreturn⟩

end Assembly

end Formalisation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
