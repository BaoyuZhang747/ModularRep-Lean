import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionFixedBlockSource
import ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionSelectors
import ModularRep.PaperProofs.TypeBGlobalExtensionBinding
import ModularRep.PaperProofs.TypeBLocalOrdinaryExtensionSplitting

/-!
# The fixed-block extension and selector antecedents

The actual quotient of index two is cyclic. The two established cyclic
extension consumers then give the Brauer and ordinary M-extension clauses
on the selected block. The G-by-field extension consumers use cyclicity
of the actual field group and the same canonical subgroup embeddings.

An actual restriction constituent is selected from the upper covering
union. Its field fixation gives the character stabilizer product. Every
M-conjugate receives its own extension to its own G-by-field inertia;
no common-inertia assertion or selected-pair extension is assumed.

A weight class supplies an actual raw representative. Class fixation gives
the class-inertia product, and ordinary cyclic extension applies to that
representative's raw inertia quotient. The selector uses m = 1. This does
not claim that field actors fix the raw representative.

The only extension inputs are the uniform representation-level Brauer
cyclic theorem and the fixed-group ordinary cyclic theorem with its actual
sufficient-root guard. No ordinary algebraic closure, completed matching,
paired extension packet or criterion conclusion is a source input.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionExtensions

open ModularRep CharacterWeight
open TypeBCriterionHypotheses TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBQ3PrincipalWeightInflation
open TypeBAllRankPrincipalCriterionFixedBlockSource
open TypeBLocalOrdinaryGeometry TypeBLocalOrdinaryExtensionSplitting
open NavarroCoveringBrauerExtension

local instance finiteFintype (X : Type) [Finite X] : Fintype X := Fintype.ofFinite X
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K M E : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k]
  [CharZero K] [Group M] [Finite M] [Group E] [Finite E]
  (G : Subgroup M) [G.Normal] (field : E →* MulAut M)
  (action : NaturalAction G field)

/-- The order of the actual quotient is the given subgroup index. -/
theorem quotient_cyclic_of_index_two (indexTwo : G.index = 2) : IsCyclic (M ⧸ G) :=
  isCyclic_of_prime_card (G.index_eq_card.symm.trans indexTwo)

variable (root : PrimeRegularRootEmbedding 2 k K G)
  (b : LiteralPrimitiveBlock k G)

/-- Positive field fixation supplies containment for the criterion's
inverse ambient action, by using the inverse element of the same E. -/
theorem brauer_field_le_of_fixed (phi : IBr root)
    (fixed : ∀ e : E, IrreducibleBrauerCharacter.twist root phi
      (action.hom (SemidirectProduct.inr e)) = phi) :
    embeddedE field ≤ brauerInertia G field action root phi := by
  rintro _ ⟨e, rfl⟩
  change IrreducibleBrauerCharacter.twist root phi
    (action.hom ((SemidirectProduct.inr e)⁻¹)) = phi
  simpa only [map_inv] using fixed (e⁻¹)

/-- This is the b-scoped M-extension field of the fixed-block source. -/
theorem brauer_M_on_block (indexTwo : G.index = 2)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k) :
    ∀ phi : BrauerFibre root b,
      Nonempty (BrauerExtensionIn G field root phi.val
        (brauerInertia G field action root phi.val ⊓ embeddedM field)) := by
  intro phi
  exact ⟨TypeBGlobalExtensionBinding.brauer_M G field action root phi.val
    principle (quotient_cyclic_of_index_two G indexTwo)⟩

section CyclicField

variable [IsCyclic E]

/-- The exact CharacterSelector domain. Only existence of an actual
supported constituent is needed from the upper covering-union equation. -/
theorem characterSelector_of_field_fixed
    (rootM : PrimeRegularRootEmbedding 2 k K M)
    (bH : LiteralPrimitiveBlock k M)
    (constituent : ∀ Phi : BrauerFibre rootM bH,
      ∃ phi : BrauerFibre root b,
        BrauerOccursInRestriction G rootM root Phi.val phi.val)
    (fixed : ∀ (phi : BrauerFibre root b) (e : E),
      IrreducibleBrauerCharacter.twist root phi.val
        (action.hom (SemidirectProduct.inr e)) = phi.val)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k) :
    CharacterSelector G field action root rootM b bH := by
  intro Phi
  obtain ⟨phi, occurs⟩ := constituent Phi
  refine ⟨phi, occurs, ?_, ?_⟩
  · exact TypeBAllRankPrincipalCriterionSelectors.brauerFactorization_of_field_fixed
      G field action root phi.val
      (brauer_field_le_of_fixed G field action root phi.val (fixed phi))
  · intro m
    exact ⟨TypeBGlobalExtensionBinding.brauer_GE G field action root
      (IrreducibleBrauerCharacter.twist root phi.val
        (MulAut.conjNormal (H := G) m⁻¹)) principle⟩

end CyclicField

/-- The analogous containment concerns the actual weight CLASS only. -/
theorem weight_field_le_of_fixed
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G))
    (fixed : ∀ e : E, CharacterWeight.rightTwistConjugacyClass
      (action.hom (SemidirectProduct.inr e)) w = w) :
    embeddedE field ≤ weightClassInertia G field action w := by
  rintro _ ⟨e, rfl⟩
  change CharacterWeight.rightTwistConjugacyClass
    (action.hom ((SemidirectProduct.inr e)⁻¹)) w = w
  simpa only [map_inv] using fixed (e⁻¹)

/-- The two actual quotient constructions provide a raw representative. -/
theorem exists_raw_representative
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G)) :
    ∃ W : CharacterWeight 2 K G, TypeBWeightCoveringSource.rawClass W = w := by
  refine Quotient.inductionOn w ?_
  intro v
  refine Quotient.inductionOn v ?_
  intro W
  exact ⟨W, rfl⟩

section Ordinary

variable [HasEnoughRootsOfUnity K (Nat.card (Ambient field))]
  (R : CoverWeightSource (k := k) (K := K) G)

/-- Only the same finite raw inertia quotient is passed to the ordinary
E1 source; its sufficient roots are inherited from the actual ambient. -/
theorem ordinary_M_on_block (indexTwo : G.index = 2)
    (ordinary : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)], ScopedCyclicExtensionSource K H) :
    ∀ (W : CharacterWeight 2 K G), R.operations.induceToAmbient W = b →
      Nonempty (LocalOrdinaryExtension G field W
        (rawNormalizerInertia G field action W ⊓ embeddedM field)) := by
  intro W _
  letI := localRoots_of_ambientRoots G field action W (embeddedM field)
  exact TypeBLocalOrdinaryExtensionSplitting.ordinary_M G field action W
    (ordinary (Inertia G field action W (embeddedM field) ⧸
      RadicalInInertia G field action W (embeddedM field)))
    (quotient_cyclic_of_index_two G indexTwo)

variable [IsCyclic E]

/-- Choose m = 1 and an actual raw representative of the fixed weight
class. The ordinary extension is to that representative's GE inertia,
without assuming the representative is itself fixed by E. -/
theorem weightSelector_of_field_fixed
    (fixed : ∀ (w : CoverWeight R b) (e : E),
      CharacterWeight.rightTwistConjugacyClass
        (action.hom (SemidirectProduct.inr e)) w.val = w.val)
    (ordinary : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)], ScopedCyclicExtensionSource K H) :
    WeightSelector G field action R b := by
  intro w
  obtain ⟨W, represents⟩ := exists_raw_representative G w.val
  have field_le : embeddedE field ≤
      weightClassInertia G field action (TypeBWeightCoveringSource.rawClass W) := by
    rw [represents]
    exact weight_field_le_of_fixed G field action w.val (fixed w)
  refine ⟨1, W, ?_, ?_, ?_⟩
  · simpa only [map_one, inv_one, CharacterWeight.rightTwistConjugacyClass_one]
      using represents
  · exact TypeBAllRankPrincipalCriterionSelectors.weightClassFactorization_of_field_fixed
      G field action W field_le
  · letI := localRoots_of_ambientRoots G field action W (baseFieldGroup G field)
    exact TypeBLocalOrdinaryExtensionSplitting.ordinary_GE G field action W
      (ordinary (Inertia G field action W (baseFieldGroup G field) ⧸
        RadicalInInertia G field action W (baseFieldGroup G field)))

end Ordinary

end ModularRep.PaperProofs.TypeBAllRankPrincipalCriterionExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
