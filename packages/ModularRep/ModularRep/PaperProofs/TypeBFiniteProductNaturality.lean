import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter

/-!
# Naturality from literal external-product Brauer values

The only representation theoretic input is the finite-product equivalence
with its actual value formula, in a common modular system and at a prime.
This is the finite iteration of Navarro (8.21), p. 177, with the external
product defined on p-regular elements on p. 176.  Coordinate naturality and
reindexing of the product are deductions, independent of every selected
orbit and every stabiliser.  This file contains no selector input.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBFiniteProductNaturality

open TypeBRegularLeviCharacterActionAdapter

universe u v w x

variable {p : ℕ} {I : Type u} {k : Type v} {K : Type w}
variable (H : I → Type x) [Fintype I]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable (iota : PrimeRegularRootEmbedding p k K (∀ i, H i))
variable (factorRoot : ∀ i, PrimeRegularRootEmbedding p k K (H i))

/-- Evaluation at the literal factor of the product. -/
def projection (i : I) : (∀ i, H i) →* H i where
  toFun g := g i
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Exact E1 source scope.  In particular, naturality is not a field. -/
structure ExternalProductData where
  prime : Nat.Prime p
  characters : IBr iota ≃ (∀ i, IBr (factorRoot i))
  roots_agree : ∀ i (zeta : rootsOfUnity (primeRegularExponent p (H i)) k),
    (factorRoot i).lift (((zeta : kˣ) : k)) = iota.lift (((zeta : kˣ) : k))
  external_product : ∀ (psi : IBr iota)
      (g : PrimeRegularElement (G := (∀ i, H i)) p),
    psi.1 g = ∏ i, (characters psi i).1
      (PrimeRegularElement.map (projection H i) g)

variable (source : ExternalProductData H iota factorRoot)

/-- A factorwise value calculation, with the actual permutation of factors,
determines the tuple of the twisted character.  This is only reindexing a
finite product and equality of function-valued characters. -/
theorem characters_twist_of_reindexed_values
    (a : MulAut (∀ i, H i)) (psi : IBr iota)
    (theta : ∀ i, IBr (factorRoot i)) (sigma : Equiv.Perm I)
    (values : ∀ (g : PrimeRegularElement (G := (∀ i, H i)) p) i,
      (source.characters psi i).1
          (PrimeRegularElement.map (projection H i)
            (PrimeRegularElement.map a.toMonoidHom g)) =
        (theta (sigma i)).1
          (PrimeRegularElement.map (projection H (sigma i)) g)) :
    source.characters (IrreducibleBrauerCharacter.twist iota psi a) = theta := by
  have heq : IrreducibleBrauerCharacter.twist iota psi a =
      source.characters.symm theta := by
    apply Subtype.ext
    apply PrimeRegularClassFunction.ext
    intro g
    change psi.1 (PrimeRegularElement.map a.toMonoidHom g) = _
    rw [source.external_product, source.external_product]
    simp only [Equiv.apply_symm_apply]
    exact Fintype.prod_equiv sigma _ _ (values g)
  rw [heq, Equiv.apply_symm_apply]

/-- Coordinate automorphism naturality follows from the value formula. -/
theorem coordinate_naturality (D : I → Type x) [∀ i, Group (D i)]
    (diagonal : ∀ i, D i →* MulAut (H i))
    (d : ∀ i, D i) (psi : IBr iota) :
    source.characters (IrreducibleBrauerCharacter.twist iota psi
      (coordinateMulAut H D diagonal d)) =
      fun i ↦ IrreducibleBrauerCharacter.twist (factorRoot i)
        (source.characters psi i) (diagonal i (d i)) := by
  apply characters_twist_of_reindexed_values H iota factorRoot source
    (coordinateMulAut H D diagonal d) psi _ (Equiv.refl I)
  intro g i
  rfl

/-- Supply the older direct-product interface using the narrower source and
the checked value calculation. -/
def toDirectProductIBrIdentification (D : I → Type x) [∀ i, Group (D i)]
    (diagonal : ∀ i, D i →* MulAut (H i)) :
    DirectProductIBrIdentification H D iota factorRoot diagonal where
  characters := source.characters
  coordinate_naturality := coordinate_naturality H iota factorRoot source D diagonal

end ModularRep.PaperProofs.TypeBFiniteProductNaturality


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
