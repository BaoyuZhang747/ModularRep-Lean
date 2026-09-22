import ModularRep.StrictQuasiIsolation
import ModularRep.PaperProofs.EvenFieldProposition39StructuralCases

/-!
# The strictly quasi-isolated branch of Proposition 3.9

This file checks the manuscript-specific logical construction used to verify the
second hypothesis of Jordan reduction in Proposition 3.9.  Routine facts
classifying connected subdiagrams and Steinberg forms are represented by the
explicit finite case `StructuralCase`; they are canonical-source inputs, not
facts to be reconstructed in Lean.

The representation theoretic inputs are kept separate and recognisable:

* Bonnafe's classification of quasi-isolated semisimple elements in adjoint
  type `B` in characteristic two;
* the interpretation of the identity series as the unipotent blocks;
* the established iBAW results for type `A`, the high-rank unipotent type `C`
  blocks, the split low-rank groups, `Sp_6(2)`, and the Suzuki groups.

No input asserts the desired conclusion for all strictly quasi-isolated
blocks.  Lean derives that conclusion by the centraliser inclusion and the
exhaustive case split below.  The file deliberately does not reconstruct
fixed-point groups, the type `B`--`C` isomorphism in characteristic two,
orders, centres, or covering groups.
-/

namespace ModularRep.PaperProofs.EvenFieldProposition39Relative

open scoped Pointwise
open ModularRep.ManuscriptVerification.StrictQuasiIsolation

variable {Dual Block : Type*} [Group Dual]

/-- The concrete semantic data attached to one group occurring in the
strictly quasi-isolated-block hypothesis.

The subgroup fields expose exactly the bridge needed to interpret the two
centralisers in the definition of strict quasi-isolation.  They do not take
ordinary quasi-isolation, identity of the semisimple label, unipotence, or an
iBAW conclusion as inputs. -/
structure Data (Dual Block : Type*) [Group Dual] where
  groupCase : StructuralCase
  IsStrictBlock : Block -> Prop
  HasIBAW : Block -> Prop
  IsUnipotent : Block -> Prop
  label : Block -> Dual
  finiteCentralizer : Block -> Subgroup Dual
  connectedCentralizer : Block -> Subgroup Dual
  IsProperLevi : Set Dual -> Prop
  finiteCentralizer_le : forall b,
    finiteCentralizer b <= Subgroup.centralizer {label b}
  connectedCentralizer_le : forall b,
    connectedCentralizer b <= Subgroup.centralizer {label b}
  strictLabel : forall b, IsStrictBlock b ->
    NotContainedInProperLevi
      ((finiteCentralizer b : Set Dual) *
        (connectedCentralizer b : Set Dual))
      IsProperLevi

/-- Exact external interfaces used after the checked centraliser argument.

The equalities naming the structural case prevent a result for one branch
from being used in another.  `highRankUnipotent` is the only branch supplied
by Proposition 3.8; the remaining branch fields correspond to the cited
type `A`, low-rank, cyclic-defect, Schaeffer Fry, and Suzuki results together
with passage to the simple fixed point group where required and the modern
character-triple reformulation. -/
structure SourceInputs (D : Data Dual Block) where
  outsideOrder : D.groupCase = .primeOutsideOrder ->
    forall b, D.IsStrictBlock b -> D.HasIBAW b
  typeA : D.groupCase = .typeA ->
    forall b, D.IsStrictBlock b -> D.HasIBAW b
  bonnafeIdentity : forall {form : TypeCForm} {s : Dual},
    D.groupCase = .typeC form ->
    NotContainedInProperLevi
      (Subgroup.centralizer {s} : Set Dual) D.IsProperLevi ->
    s = 1
  identitySeriesUnipotent : forall {form} b,
    D.groupCase = .typeC form -> D.IsStrictBlock b ->
    D.label b = 1 -> D.IsUnipotent b
  highRankUnipotent : ∀ parameter : HighRankParameter,
    D.groupCase = .typeC (.rankAtLeastFour parameter) ->
      forall b, D.IsStrictBlock b -> D.IsUnipotent b -> D.HasIBAW b
  splitLowRank : ∀ parameter : SplitLowRankParameter,
    D.groupCase = .typeC (.splitLowRank parameter) ->
      forall b, D.IsStrictBlock b -> D.HasIBAW b
  sp6AtThree :
    D.groupCase = .typeC (.splitSp6Two .three) ->
    forall b, D.IsStrictBlock b -> D.HasIBAW b
  sp6AtFive :
    D.groupCase = .typeC (.splitSp6Two .five) ->
    forall b, D.IsStrictBlock b -> D.HasIBAW b
  sp6AtSeven :
    D.groupCase = .typeC (.splitSp6Two .seven) ->
    forall b, D.IsStrictBlock b -> D.HasIBAW b
  suzuki : forall parameter : SuzukiParameter,
    D.groupCase = .typeC (.simpleSuzuki parameter) ->
      forall b, D.IsStrictBlock b -> D.HasIBAW b

/-- The manuscript-specific verification of the strictly quasi-isolated
block hypothesis, relative to the exact cited branch inputs.

For a type `C` branch, Lean first proves ordinary quasi-isolation from strict
quasi-isolation by the centraliser inclusion.  It then derives that the
semisimple label is the identity, derives unipotence, and dispatches the
exhaustive finite-form case. -/
theorem strict_block_hypothesis_relative
    (D : Data Dual Block) (S : SourceInputs D) :
    forall b, D.IsStrictBlock b -> D.HasIBAW b := by
  intro b hb
  cases hcase : D.groupCase with
  | primeOutsideOrder =>
      exact S.outsideOrder hcase b hb
  | typeA =>
      exact S.typeA hcase b hb
  | typeC form =>
      have hquasi :
          NotContainedInProperLevi
            (Subgroup.centralizer {D.label b} : Set Dual)
            D.IsProperLevi :=
        quasiIsolated_of_strictlyQuasiIsolated
          (D.finiteCentralizer_le b)
          (D.connectedCentralizer_le b)
          (D.strictLabel b hb)
      have hlabel : D.label b = 1 :=
        S.bonnafeIdentity hcase hquasi
      have hunipotent : D.IsUnipotent b :=
        S.identitySeriesUnipotent b hcase hb hlabel
      cases form with
      | rankAtLeastFour parameter =>
          exact S.highRankUnipotent parameter hcase b hb hunipotent
      | splitLowRank parameter =>
          exact S.splitLowRank parameter hcase b hb
      | splitSp6Two prime =>
          cases prime with
          | three => exact S.sp6AtThree hcase b hb
          | five => exact S.sp6AtFive hcase b hb
          | seven => exact S.sp6AtSeven hcase b hb
      | simpleSuzuki parameter =>
          exact S.suzuki parameter hcase b hb

end ModularRep.PaperProofs.EvenFieldProposition39Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
