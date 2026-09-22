import ModularRep.OrdinaryCharacterDefectZero
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Ordinary characters of the literal finite product

The routine source is the finite iteration of Isaacs (4.20)--(4.21),
with finite cyclotomic splitting as in Isaacs (10.3).  Its defect-zero
clause combines the value at the identity, degree divisibility (3.11),
and the definition of defect zero.  The source uses the actual ordinary
irreducible-character and defect-zero carriers.  The external-product
function is fixed before the source, and its bijectivity is derived.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.TypeBRankThreeProductOrdinarySource

open OrdinaryIrreducibleCharacter

universe u

variable {I K : Type u} (H : I → Type u) [Fintype I]
variable [∀ i, Group (H i)] [∀ i, Finite (H i)]
variable [Field K] [CharZero K]

/-- The prescribed ordinary external-product values on every group element. -/
def externalValues (chi : ∀ i, Irr K (H i)) (g : ∀ i, H i) : K :=
  ∏ i, chi i (g i)

/-- Uniform finite-splitting E1 input, with ordinary completeness explicit. -/
structure ExternalProductSource (p : ℕ) (_prime : Nat.Prime p)
    (_roots : HasEnoughRootsOfUnity K (Nat.card (∀ i, H i))) : Prop where
  realises : ∀ chi : ∀ i, Irr K (H i),
    Nonempty (Realisation K (∀ i, H i) (externalValues H chi))
  factorization : ∀ psi : Irr K (∀ i, H i),
    ∃! chi : ∀ i, Irr K (H i), externalValues H chi = psi.1
  defect_zero : ∀ chi : ∀ i, Irr K (H i),
    IsDefectZeroOrdinaryCharacter p
        (⟨externalValues H chi, realises chi⟩ : Irr K (∀ i, H i)) ↔
      ∀ i, IsDefectZeroOrdinaryCharacter p (chi i)

variable {p : ℕ} {prime : Nat.Prime p}
variable {roots : HasEnoughRootsOfUnity K (Nat.card (∀ i, H i))}
variable (source : ExternalProductSource H p prime roots)

/-- The character is the prescribed value function, with supplied realization. -/
def product (chi : ∀ i, Irr K (H i)) : Irr K (∀ i, H i) :=
  ⟨externalValues H chi, source.realises chi⟩

@[simp]
theorem product_apply (chi : ∀ i, Irr K (H i)) (g : ∀ i, H i) :
    product H source chi g = ∏ i, chi i (g i) :=
  rfl

/-- Unique factorization of the literal values gives injectivity. -/
theorem product_injective : Function.Injective (product H source) := by
  intro chi theta h
  obtain ⟨factors, hfactor, hunique⟩ :=
    source.factorization (product H source chi)
  have hchi : externalValues H chi = (product H source chi).1 := rfl
  have htheta : externalValues H theta = (product H source chi).1 :=
    congrArg (fun psi : Irr K (∀ i, H i) ↦ psi.1) h.symm
  exact (hunique chi hchi).trans (hunique theta htheta).symm

/-- Every actual ordinary irreducible character is reached. -/
theorem product_surjective : Function.Surjective (product H source) := by
  intro psi
  obtain ⟨chi, hchi, hunique⟩ := source.factorization psi
  exact ⟨chi, Subtype.ext hchi⟩

/-- The equivalence is constructed from the literal product and factorization. -/
def productEquiv : (∀ i, Irr K (H i)) ≃ Irr K (∀ i, H i) :=
  Equiv.ofBijective (product H source)
    ⟨product_injective H source, product_surjective H source⟩

@[simp]
theorem productEquiv_apply (chi : ∀ i, Irr K (H i)) (g : ∀ i, H i) :
    productEquiv H source chi g = ∏ i, chi i (g i) :=
  rfl

/-- Defect zero refers to the same prescribed external-product character. -/
theorem product_defect_zero_iff (chi : ∀ i, Irr K (H i)) :
    IsDefectZeroOrdinaryCharacter p (product H source chi) ↔
      ∀ i, IsDefectZeroOrdinaryCharacter p (chi i) :=
  source.defect_zero chi

end ModularRep.PaperProofs.TypeBRankThreeProductOrdinarySource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
