import ModularRep.PaperProofs.TypeBOrdinaryTraceSeparationSplitting
import ModularRep.PaperProofs.TypeBOrdinaryLabelSplitting
import ModularRep.IBrBlockBasicSetBridge
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.Complex.Basic

/-!
# The same ordinary labels over two coefficient fields

This file compares the ordinary labels in the basic set argument over two
coefficient fields. The principal weight construction uses complex
characters directly.

Fix the cyclotomic field Q(zeta_N) and embeddings into C and K before
choosing characters. Serre, Section 12.3, Theorem 24 and its corollary,
together with Section 12.1, Propositions 32–33, supply the character
realisations assumed below. The equations for their values identify the
chosen simple K[G]-module labels with the same complex characters. These
equations imply compatibility with automorphisms. The realisation source
supplies no block assignment, decomposition map or character bijection.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ManuscriptIBAW.Characters

open ModularRep OrdinaryIrreducibleCharacter
open ExactGrothendieckGroup FDRepSimpleClassKZero
open DecompositionBasicSetBridge
open PaperProofs.TypeBOrdinaryTraceSeparationSplitting

/-- The common coefficient field has a fixed finite conductor. -/
abbrev ValueField (N : ℕ) := CyclotomicField N ℚ

variable {N : ℕ} [NeZero N] {K G : Type}
  [Field K] [CharZero K] [Group G] [Finite G]

/-- The conductor is divisible by the order of G. Both embeddings are fixed
before the ordinary characters and basic set labels. An embedding from C to
K and algebraic closure of K are not required. -/
structure CyclotomicComparison (N : ℕ) (K G : Type)
    [NeZero N] [Field K] [CharZero K] [Group G] [Finite G] where
  order_dvd : Nat.card G ∣ N
  complexEmbedding : ValueField N →ₐ[ℚ] ℂ
  ordinaryEmbedding : ValueField N →ₐ[ℚ] K

variable (C : CyclotomicComparison N K G)

/-- External splitting field realisation (E1) for every irreducible complex
character of G. The common character is afforded by an irreducible
representation over Q(zeta_N), and both value equations use it. Divisibility
of N by the group order implies Serre's exponent hypothesis. Actions on
labels, block assignments, decomposition maps and character bijections are
separate data. -/
structure SerreRealisationSource : Prop where
  realises : ∀ chi : Irr ℂ G,
    ∃ common : Irr (ValueField N) G, ∃ ordinary : Irr K G,
      (∀ g, C.complexEmbedding (common g) = chi g) ∧
      (∀ g, C.ordinaryEmbedding (common g) = ordinary g)

variable {Basic : Type} (characters : Basic → Irr ℂ G)

/-- An interpretation of a chosen family of simple K[G]-module labels. Both
equations use the same character over Q(zeta_N), so they identify each label
with its specified complex character. -/
structure OrdinaryLabelRealisation
    (label : Basic → SimpleModuleClass K[G]) where
  commonCharacter : Basic → Irr (ValueField N) G
  complex_value : ∀ x g,
    C.complexEmbedding (commonCharacter x g) = characters x g
  ordinary_value : ∀ x g,
    C.ordinaryEmbedding (commonCharacter x g) =
      (simpleClassFDRep (label x)).character g

namespace SerreRealisationSource

variable {C} (source : SerreRealisationSource C)

def commonCharacter (chi : Irr ℂ G) : Irr (ValueField N) G :=
  Classical.choose (source.realises chi)

def ordinaryCharacter (chi : Irr ℂ G) : Irr K G :=
  Classical.choose (Classical.choose_spec (source.realises chi))

theorem complex_value (chi : Irr ℂ G) (g : G) :
    C.complexEmbedding (source.commonCharacter chi g) = chi g :=
  (Classical.choose_spec (Classical.choose_spec (source.realises chi))).1 g

theorem ordinary_value (chi : Irr ℂ G) (g : G) :
    C.ordinaryEmbedding (source.commonCharacter chi g) =
      source.ordinaryCharacter chi g :=
  (Classical.choose_spec (Classical.choose_spec (source.realises chi))).2 g

/-- The common character values imply injectivity of the ordinary character map. -/
theorem ordinaryCharacter_injective : Function.Injective source.ordinaryCharacter := by
  intro chi psi h
  apply OrdinaryIrreducibleCharacter.ext
  intro g
  have hv : source.commonCharacter chi g = source.commonCharacter psi g := by
    apply C.ordinaryEmbedding.injective
    exact (source.ordinary_value chi g).trans
      ((congrArg (fun theta : Irr K G => theta g) h).trans
        (source.ordinary_value psi g).symm)
  exact (source.complex_value chi g).symm.trans
    ((congrArg C.complexEmbedding hv).trans (source.complex_value psi g))

def ordinaryLabel : Basic → SimpleModuleClass K[G] := fun x =>
  PaperProofs.TypeBOrdinaryLabelSplitting.ordinaryLabel
    (source.ordinaryCharacter (characters x))

/-- The labels constructed from the realisation source satisfy the character
identities required by the basic set application. -/
def labelRealisation : OrdinaryLabelRealisation C characters
    (source.ordinaryLabel characters) where
  commonCharacter x := source.commonCharacter (characters x)
  complex_value x := source.complex_value (characters x)
  ordinary_value x g := by
    rw [source.ordinary_value]
    exact (congrFun
      (PaperProofs.TypeBOrdinaryLabelSplitting.ordinaryLabel_character
        (source.ordinaryCharacter (characters x))) g).symm

end SerreRealisationSource

namespace OrdinaryLabelRealisation

variable {C characters} {label : Basic → SimpleModuleClass K[G]}
  (R : OrdinaryLabelRealisation C characters label)
  {A : Type} [Group A] [MulAction A Basic]
  (automorphism : A →* (MulAut G)ᵐᵒᵖ)

include R

/-- Transport of the complex character values determines transport of the
K-valued traces through the common field, using the same group automorphism. -/
theorem trace_action
    (action : ∀ (a : A) (x : Basic) (g : G),
      characters (a • x) g = characters x ((automorphism a).unop g))
    (a : A) (x : Basic) (g : G) :
    (simpleClassFDRep (label (a • x))).character g =
      (simpleClassFDRep (label x)).character ((automorphism a).unop g) := by
  have common : R.commonCharacter (a • x) g =
      R.commonCharacter x ((automorphism a).unop g) := by
    apply C.complexEmbedding.injective
    exact (R.complex_value (a • x) g).trans
      ((action a x g).trans (R.complex_value x ((automorphism a).unop g)).symm)
  exact (R.ordinary_value (a • x) g).symm.trans
    ((congrArg C.ordinaryEmbedding common).trans
      (R.ordinary_value x ((automorphism a).unop g)))

/-- Equal traces of irreducible representations give an isomorphism over K and
hence equality of their classes in the exact Grothendieck group. Algebraic
closure of K is not required. -/
theorem simple_generator_action
    (action : ∀ (a : A) (x : Basic) (g : G),
      characters (a • x) g = characters x ((automorphism a).unop g))
    (a : A) (x : Basic) :
    simpleClassToFDRepKZeroGenerator (label (a • x)) =
      twistKZero (k := K) (automorphism a).unop
        (simpleClassToFDRepKZeroGenerator (label x)) := by
  let V := simpleClassFDRep (label (a • x))
  let W := (FDRep.twistEquivalence K G (automorphism a).unop).functor.obj
    (simpleClassFDRep (label x))
  have hV : Representation.IsIrreducible V.ρ :=
    simpleClassFDRep_irreducible (label (a • x))
  have hW : Representation.IsIrreducible W.ρ :=
    (simpleClassFDRep_irreducible (label x)).twist (automorphism a).unop
  have traces : V.character = W.character := by
    funext g
    exact R.trace_action automorphism action a x g
  obtain ⟨e⟩ := fdRep_nonempty_iso_of_character_eq V W hV hW traces
  change classOf (FDRep K G) V =
    twistKZero (k := K) (automorphism a).unop
      (classOf (FDRep K G) (simpleClassFDRep (label x)))
  rw [twistKZero_classOf]
  exact classOf_iso (FDRep K G) e

end OrdinaryLabelRealisation

section BasicSet

open IBrBlockBasicSetBridge
open IBrBlockBasicSetBridge.RestrictedIntegralBasicSetOnIBrBlock

variable {ell : ℕ} {k I A : Type} [Field k] [CharP k ell] [IsAlgClosed k]
  [Fintype I] [Group A] [MulAction A Basic]
  {iota : PrimeRegularRootEmbedding ell k K G}
  {injective : IrreducibleBrauerCharacterInjectivity iota}
  {idempotent : I → k[G]} {blocks : BlockIdempotentDecomposition idempotent}
  {block : I} {decomposition : FDRepKZero K G →+ FDRepKZero k G}

/-- This theorem proves compatibility of the ordinary labels with twisting for
the even characteristic application, using the specified basic set and
decomposition map. -/
theorem ordinaryTwistCompatibleLabels
    (basic : RestrictedIntegralBasicSetOnIBrBlock iota injective blocks block
      Basic decomposition)
    (R : OrdinaryLabelRealisation C characters basic.ordinaryLabel)
    (automorphism : A →* (MulAut G)ᵐᵒᵖ)
    (action : ∀ (a : A) (x : Basic) (g : G),
      characters (a • x) g = characters x ((automorphism a).unop g)) :
    OrdinaryTwistCompatibleLabels basic automorphism where
  ordinary_single a x := by
    rw [labelledSimpleClassKZero_single, labelledSimpleClassKZero_single]
    exact R.simple_generator_action automorphism action a x

end BasicSet

end ManuscriptIBAW.Characters

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
