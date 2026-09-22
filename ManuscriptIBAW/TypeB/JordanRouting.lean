import ManuscriptIBAW.Jordan.TypeBLocalized
import ManuscriptIBAW.TypeC.LiLiSource

/-!
# Strict block labels in the complete Type B relative family

The type A application treats all blocks. In the other cases, the label used
to prove principality is identified with the strict model's label on the
same original block. In rank two, Li–Li supplies the quotient block bijection,
and central lifting gives the bijection on the original relative block.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.JordanRouting

open ModularRep ModularRep.PaperProofs
open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions EvenFieldFLZFullHG
open TypeBCurrentStrictRouting OddTwoFullHGPrincipalRouting
open ManuscriptIBAW.Jordan.TypeBLocalized

variable {p : ℕ} {scope : FLZFullHGUniverse p 2}
  {coverage : FullHGDefinition35Coverage scope}
  {strictSource : FullHGStrictQuasiIsolationAdapter coverage}
  (blockSource : FullHGBlockSource coverage)
  (interpretation : ManuscriptIBAW.Jordan.TypeBLocalized.FullHGInterpretation
    scope coverage blockSource strictSource)

/-- The specified algebraic dual identification for the two principal cases. The
type A argument applies to every block without choosing a particular label. -/
inductive LabelBinding {family : Definition35Family 2}
    {isStrict : family.Block → Prop}
    (model : EvenFieldFLZ57CentrelessGate.SourceStrictBlockModel family.Block) :
    TypeBCurrentStrictRouting.RelativePairSource p family isStrict → Type 1 where
  | typeA {rank : ℕ} {positive : 0 < rank}
      {presentation : TypeAActualPresentation p rank family.H} :
      LabelBinding model (.typeA rank positive presentation)
  | rankTwo {data : SymplecticJordanData p 2 family isStrict}
      (dualEquiv : model.Dual ≃* data.geometry.dual.SO)
      (label_eq : ∀ (b : family.Block) (h : isStrict b),
        dualEquiv (model.label b) = (data.selectedLabel b h).label) :
      LabelBinding model (.rankTwo data)
  | spin {rank : ℕ} {rankAtLeastThree : 3 ≤ rank}
      {data : SpinJordanData p rank family isStrict}
      (dualEquiv : model.Dual ≃* data.geometry.Dual)
      (label_eq : ∀ (b : family.Block) (h : isStrict b),
        dualEquiv (model.label b) = (data.selectedLabel b h).label) :
      LabelBinding model (.spin rank rankAtLeastThree data)

/-- The identification retains every represented pair and strict block. -/
structure FullLabelBinding (routing : FullHGRouting coverage strictSource) where
  atPair : ∀ pair : FullHG scope,
    LabelBinding (interpretation.strictModel pair) (routing.atPair pair)

section RankTwo

variable (pair : FullHG scope) (block : (coverage.presentation pair).family.Block)
  {F : Type} [Field F] [Fintype F]
  (sources : ManuscriptIBAW.TypeC.LiLiSource.RankTwoPrincipalInputs F
    ((coverage.presentation pair).family.problem block)
    (blockSource.automorphisms pair block) (blockSource.source pair block))

/-- Lift the Li–Li bijection to the original relative block, with the
specified automorphism action and character triple interpretation. -/
def rankTwoBijection : Definition35IBAWBijection
    ((coverage.presentation pair).family.problem block)
    (blockSource.automorphisms pair block) (blockSource.source pair block) :=
  sources.seed

end RankTwo

end ManuscriptIBAW.TypeB.JordanRouting

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
