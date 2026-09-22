import Formalisation.ComponentReturnAssembly

/-!
# Transport of stabiliser factorisations

This file formalises the deduction in manuscript Lemma 3.12 that transfers
the stabiliser factorisation already known for an ordinary character to the
corresponding irreducible Brauer character.  The only input from the
preceding basic-set argument is an equivariant bijection.  The ordinary
factorisation is a separate, source-shaped input.

The two acting groups model the conformal and field automorphisms.  Writing
their actions separately avoids assuming that either action is trivial and
states exactly the elementwise content of
`(G-tilde semidirect E)_x = G-tilde_x semidirect E_x`.
-/

namespace ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {D E X Y : Type*}
variable [Group D] [Group E]
variable [MulAction D X] [MulAction E X]
variable [MulAction D Y] [MulAction E Y]

/-- Elementwise form of factorisation of the stabiliser under the combined
normal-factor and outer-factor actions. -/
def ProductStabilizerFactorization (x : X) : Prop :=
  ∀ d : D, ∀ e : E,
    d • (e • x) = x ↔ d • x = x ∧ e • x = x

/-- An equivalence that is equivariant for both actions transports the
product stabiliser factorisation in either direction. -/
theorem productStabilizerFactorization_iff_of_equivariantEquiv
    (beta : X ≃ Y)
    (equivariantD : ∀ (d : D) (x : X), beta (d • x) = d • beta x)
    (equivariantE : ∀ (e : E) (x : X), beta (e • x) = e • beta x)
    (x : X) :
    ProductStabilizerFactorization (D := D) (E := E) x ↔
      ProductStabilizerFactorization (D := D) (E := E) (beta x) := by
  constructor
  · intro hx d e
    constructor
    · intro hcombined
      have hpreimage : d • (e • x) = x := by
        apply beta.injective
        calc
          beta (d • (e • x)) = d • beta (e • x) :=
            equivariantD d (e • x)
          _ = d • (e • beta x) := congrArg (fun z ↦ d • z)
            (equivariantE e x)
          _ = beta x := hcombined
      obtain ⟨hd, he⟩ := (hx d e).mp hpreimage
      constructor
      · calc
          d • beta x = beta (d • x) := (equivariantD d x).symm
          _ = beta x := congrArg beta hd
      · calc
          e • beta x = beta (e • x) := (equivariantE e x).symm
          _ = beta x := congrArg beta he
    · rintro ⟨hd, he⟩
      rw [he, hd]
  · intro hy d e
    constructor
    · intro hcombined
      have himage : d • (e • beta x) = beta x := by
        calc
          d • (e • beta x) = beta (d • (e • x)) := by
            rw [equivariantD, equivariantE]
          _ = beta x := congrArg beta hcombined
      obtain ⟨hd, he⟩ := (hy d e).mp himage
      constructor
      · apply beta.injective
        calc
          beta (d • x) = d • beta x := equivariantD d x
          _ = beta x := hd
      · apply beta.injective
        calc
          beta (e • x) = e • beta x := equivariantE e x
          _ = beta x := he
    · rintro ⟨hd, he⟩
      rw [he, hd]

/-- The direction used in Lemma 3.12: the equivariant basic-set bijection
transfers the ordinary-character stabiliser factorisation to its Brauer
correspondent. -/
theorem brauerFactorization_of_ordinaryFactorization
    (beta : X ≃ Y)
    (equivariantD : ∀ (d : D) (x : X), beta (d • x) = d • beta x)
    (equivariantE : ∀ (e : E) (x : X), beta (e • x) = e • beta x)
    (x : X)
    (ordinaryFactorization :
      ProductStabilizerFactorization (D := D) (E := E) (beta x)) :
    ProductStabilizerFactorization (D := D) (E := E) x :=
  (productStabilizerFactorization_iff_of_equivariantEquiv
    beta equivariantD equivariantE x).mpr ordinaryFactorization

/-- The product-action formulation is exactly the elementwise stabiliser
factorisation for the compatible semidirect product action. -/
theorem semidirectStabilizerFactors_iff_productStabilizerFactorization
    (phi : E →* MulAut D)
    (hcompat : Formalisation.SemidirectActionCompatible (X := X) phi)
    (x : X) :
    Formalisation.SemidirectStabilizerFactors phi hcompat x ↔
      ProductStabilizerFactorization (D := D) (E := E) x := by
  let _ := Formalisation.semidirectMulAction phi hcompat
  constructor
  · intro h
    change ∀ p : D ⋊[phi] E,
      p.left • (p.right • x) = x ↔
        p.left • x = x ∧ p.right • x = x at h
    intro d e
    exact h (⟨d, e⟩ : D ⋊[phi] E)
  · intro h
    change ∀ p : D ⋊[phi] E,
      p.left • (p.right • x) = x ↔
        p.left • x = x ∧ p.right • x = x
    intro p
    exact h p.left p.right

/-- Actual semidirect-product form of the stabiliser transfer used in
Lemma 3.12. -/
theorem semidirectStabilizerFactors_iff_of_equivariantEquiv
    (phi : E →* MulAut D)
    (hcompatX : Formalisation.SemidirectActionCompatible (X := X) phi)
    (hcompatY : Formalisation.SemidirectActionCompatible (X := Y) phi)
    (beta : X ≃ Y)
    (equivariantD : ∀ (d : D) (x : X), beta (d • x) = d • beta x)
    (equivariantE : ∀ (e : E) (x : X), beta (e • x) = e • beta x)
    (x : X) :
    Formalisation.SemidirectStabilizerFactors phi hcompatX x ↔
      Formalisation.SemidirectStabilizerFactors phi hcompatY (beta x) := by
  rw [semidirectStabilizerFactors_iff_productStabilizerFactorization,
    semidirectStabilizerFactors_iff_productStabilizerFactorization]
  exact productStabilizerFactorization_iff_of_equivariantEquiv
    beta equivariantD equivariantE x

/-- Named direction matching the proof of Lemma 3.12. -/
theorem brauerSemidirectFactorization_of_ordinaryFactorization
    (phi : E →* MulAut D)
    (hcompatX : Formalisation.SemidirectActionCompatible (X := X) phi)
    (hcompatY : Formalisation.SemidirectActionCompatible (X := Y) phi)
    (beta : X ≃ Y)
    (equivariantD : ∀ (d : D) (x : X), beta (d • x) = d • beta x)
    (equivariantE : ∀ (e : E) (x : X), beta (e • x) = e • beta x)
    (x : X)
    (ordinaryFactorization :
      Formalisation.SemidirectStabilizerFactors phi hcompatY (beta x)) :
    Formalisation.SemidirectStabilizerFactors phi hcompatX x :=
  (semidirectStabilizerFactors_iff_of_equivariantEquiv
    phi hcompatX hcompatY beta equivariantD equivariantE x).mpr
      ordinaryFactorization

end ModularRep.ManuscriptVerification.StabilizerFactorizationTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
