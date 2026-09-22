import ModularRep.PaperProofs.TypeCOddTwoCoherentTargetData

/-!
# One original witness jointly chosen under the fixed scalar convention

The metadata describes only roots already stored by ONE chosen original
matched packet. Its four fields bind the normalizer, ambient, local ambient
and every permitted intermediate root to C.rootAt on their ACTUAL groups.
It asserts no character, extension, block induction or finite-root guard.

The separate E2 interface is Feng--Malle Proposition 3.4 carried out in the
standard fixed modular system of Navarro 2.1 and Spath's preliminaries.
It jointly chooses Definition41 and this convention metadata for the
target computed BEFORE that choice by CanonicalTargetData.targetData.
It does not strengthen an arbitrary old TargetData or Definition41, and
does not identify the final map with the input Sp correspondence.

Authentication of C and the specified inputs remains the stated E1 source
boundary. No source instance or complete-family conclusion is constructed.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoChosenRootMetadata

open ModularRep CharacterWeight FDRepSimpleClassKZero
open OddTwoLiteralSpathTarget
open OddTwoFinalBlockOrbitCentralCoverDescentWindow
open OddTwoFengMalleForwardSourceJoin
open TypeCCoherentFiniteRootConvention TypeCOddTwoCoherentTargetData

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

local instance chosenMetadataSubgroupFintype
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    Fintype H := Fintype.ofFinite _

section Metadata

variable {P : Problem n F} (C : Convention 2 P.k P.K)

/-- Scalar convention metadata for this exact chosen packet. In particular,
the intermediate quantifier ranges over the actual H and both source bounds.
No root equality is inferred from the packet's representation compatibilities. -/
structure MatchedRootMetadata
    {Q : RadicalSubgroup (p := 2) (G := X n F)}
    {psi : IBr P.iota} {theta : LocalDefectZeroCharacter (K := P.K) Q}
    (M : P.MatchedPair Q psi theta) : Prop where
  normalizer_eq : M.localReduction.root = C.rootAt (P.Normalizer Q)
  ambient_eq : M.extensions.ambientRoot = C.rootAt M.ambient.A
  localAmbient_eq : M.extensions.localAmbientRoot =
    C.rootAt (P.LocalGroup M.ambient Q)
  intermediate_eq : ∀ (H : Subgroup M.ambient.A)
      (hHN : H ≤ P.LocalGroup M.ambient Q)
      (hNH : M.ambient.base ⊓ P.LocalGroup M.ambient Q ≤ H),
    let I := M.intermediate H hHN hNH
    I.globalRoot = C.rootAt ↥(M.ambient.base ⊔ H) ∧
      I.localRoot = C.rootAt (P.IntermediateLocal M.ambient H)

/-- Metadata applies only to D.matched at its own localMap character.
It is not a universal assertion for replacements of those chosen packets. -/
structure ChosenRootMetadata (D : Definition41 P) : Prop where
  matched : ∀ (Q : RadicalSubgroup (p := 2) (G := X n F))
      (psi : D.map.Part Q),
    MatchedRootMetadata C (D.matched Q psi)

end Metadata

section JointPublishedChoice

variable (P : LiteralFengMalleProblem n F)
variable (O : LiteralDiagonalFieldRealisation n F)
variable (C : Convention 2 P.k P.K)
variable (S : CanonicalTargetData P C)
variable (admissible : P.iota = C.rootAt (LiteralSp n F))

/-- Exact fixed-convention Proposition 3.4 construction. The one source
field retains the existing specified input, actual Sp map and its literal
FM hypotheses. The output jointly chooses ONE original witness and only
the scalar metadata of its SAME packets, on the already computed target.

The license includes the authentic fixed modular-system interpretation of
C and the specified data; no instance is inferred for arbitrary records.
This is not a K consequence of the older bare original-existence source. -/
structure JointFengMalleProposition34Source : Prop where
  applyProposition34 : InputSemantics P →
    ∀ omega : LiteralGlobalMap P,
      LiteralFengMalleHypotheses P O omega →
      Nonempty {D : Definition41 (S.targetData admissible).toProblem //
        ChosenRootMetadata C D}

namespace JointFengMalleProposition34Source

variable {P O C S admissible}
variable (source : JointFengMalleProposition34Source P O C S admissible)

/-- Forgetting metadata recovers the OLD bare source in the forward
direction only. No old bare witness is used to produce metadata. -/
def toBareSource : FengMalleProposition34Source P O (S.targetData admissible) where
  applyProposition34 input omega hypotheses := by
    obtain ⟨D⟩ := source.applyProposition34 input omega hypotheses
    exact ⟨D.1⟩

/-- A fixed choice from the joint published existential, retaining its
metadata in the result. Both original Q=1 clauses remain fields of D. -/
def choose (input : InputSemantics P) (omega : LiteralGlobalMap P)
    (hypotheses : LiteralFengMalleHypotheses P O omega) :
    {D : Definition41 (S.targetData admissible).toProblem //
      ChosenRootMetadata C D} :=
  Classical.choice (source.applyProposition34 input omega hypotheses)

/-- Corollary 4.6 and the existing K Remark 3.5 argument supply the exact
FM hypothesis packet for this SAME input correspondence. -/
def chooseOfLiteralGlobalMap (input : InputSemantics P)
    (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    {D : Definition41 (S.targetData admissible).toProblem //
      ChosenRootMetadata C D} :=
  source.choose input omega (literalFengMalleHypotheses P O omega corollary46)

include source in
/-- The weaker original condition follows by forgetting only the chosen
metadata. The final PSp map is not asserted equal to the input Sp map. -/
theorem originalIBAW (input : InputSemantics P) (omega : LiteralGlobalMap P)
    (corollary46 : LiteralFengMalleCorollary46Certificate P O) :
    OriginalIBAW (S.targetData admissible).toProblem :=
  ⟨(source.chooseOfLiteralGlobalMap input omega corollary46).1⟩

end JointFengMalleProposition34Source
end JointPublishedChoice

end ModularRep.PaperProofs.TypeCOddTwoChosenRootMetadata


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
