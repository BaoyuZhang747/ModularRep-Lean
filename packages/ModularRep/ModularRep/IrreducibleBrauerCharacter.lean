import ModularRep.BrauerCharacter
import Mathlib.RepresentationTheory.FDRep

/-!
# Irreducible Brauer characters as character functions

An element of `IBr` is a prime regular class function together with a witness
that it is afforded by an irreducible finite dimensional modular
representation.  Equality is therefore equality of character functions and
does not assume injectivity of a map from simple module classes.

This is the function-valued convention of Navarro, *Characters and Blocks of
Finite Groups*, Chapter 2, pp. 17--18.  The chosen lift of prime-to-`p` roots
is represented here by `PrimeRegularRootEmbedding`.

The automorphism action is the right action used in the manuscript.  Lean
encodes it as a left action of the opposite of `MulAut G`.
-/

noncomputable section

namespace ModularRep

universe u v w

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- A prime regular class function is an irreducible Brauer character when
it is afforded by an explicitly irreducible finite dimensional modular
representation. -/
def IsIrreducibleBrauerCharacter
    (iota : PrimeRegularRootEmbedding p k K G)
    (phi : PrimeRegularClassFunction K G p) : Prop :=
  ∃ V : FDRep k G,
    Representation.IsIrreducible V.ρ ∧
      phi = Representation.brauerCharacterOfRootEmbedding V.ρ iota

/-- The set of irreducible Brauer characters, represented by their actual
prime regular class functions rather than by module labels. -/
def IrreducibleBrauerCharacter
    (iota : PrimeRegularRootEmbedding p k K G) :=
  {phi : PrimeRegularClassFunction K G p //
    IsIrreducibleBrauerCharacter iota phi}

/-- Standard short notation for the function-valued set of irreducible
Brauer characters associated with the chosen root lift. -/
abbrev IBr (iota : PrimeRegularRootEmbedding p k K G) :=
  IrreducibleBrauerCharacter iota

namespace IrreducibleBrauerCharacter

/-- Twisting an irreducible Brauer character by an automorphism again gives
an irreducible Brauer character. -/
def twist (iota : PrimeRegularRootEmbedding p k K G)
    (phi : IBr iota) (alpha : MulAut G) : IBr iota := by
  refine ⟨phi.1.twist alpha, ?_⟩
  rcases phi.2 with ⟨V, hV, hphi⟩
  refine ⟨FDRep.of (Representation.twist V.ρ alpha), hV.twist alpha, ?_⟩
  rw [FDRep.of_ρ', hphi, Representation.brauerCharacterOfRootEmbedding_twist]

@[simp]
theorem val_twist (iota : PrimeRegularRootEmbedding p k K G)
    (phi : IBr iota) (alpha : MulAut G) :
    (twist iota phi alpha).1 = phi.1.twist alpha :=
  rfl

/-- The identity automorphism acts trivially. -/
@[simp]
theorem twist_refl (iota : PrimeRegularRootEmbedding p k K G)
    (phi : IBr iota) :
    twist iota phi (MulEquiv.refl G) = phi := by
  apply Subtype.ext
  simp

/-- Successive twists obey the manuscript's right action convention. -/
@[simp]
theorem twist_mul (iota : PrimeRegularRootEmbedding p k K G)
    (phi : IBr iota) (alpha beta : MulAut G) :
    twist iota (twist iota phi alpha) beta =
      twist iota phi (alpha * beta) := by
  apply Subtype.ext
  simp

/-- The right action by automorphisms, encoded as a left action by the
opposite automorphism group. -/
instance (iota : PrimeRegularRootEmbedding p k K G) :
    MulAction (MulAut G)ᵐᵒᵖ (IBr iota) where
  smul alpha phi := twist iota phi alpha.unop
  one_smul phi := by
    change twist iota phi (MulOpposite.unop 1) = phi
    rw [MulOpposite.unop_one]
    exact twist_refl iota phi
  mul_smul alpha beta phi := by
    change twist iota phi (MulOpposite.unop (alpha * beta)) =
      twist iota (twist iota phi beta.unop) alpha.unop
    rw [MulOpposite.unop_mul]
    exact (twist_mul iota phi beta.unop alpha.unop).symm

/-- The opposite-group action has the expected underlying class function. -/
@[simp]
theorem op_smul_val (iota : PrimeRegularRootEmbedding p k K G)
    (alpha : (MulAut G)ᵐᵒᵖ) (phi : IBr iota) :
    (alpha • phi).1 = phi.1.twist alpha.unop :=
  rfl

/-- Function-level fixation implies fixation in the irreducible Brauer
character subtype.  No injectivity result about module labels is needed. -/
theorem twist_eq_self_of_underlying
    (iota : PrimeRegularRootEmbedding p k K G)
    (phi : IBr iota) (alpha : MulAut G)
    (hfixed : phi.1.twist alpha = phi.1) :
    twist iota phi alpha = phi :=
  Subtype.ext hfixed

end IrreducibleBrauerCharacter

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
