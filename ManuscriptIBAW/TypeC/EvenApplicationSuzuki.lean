import ManuscriptIBAW.TypeC.EvenApplicationSourceCoordinates
import ModularRep.PaperProofs.EvenFieldProposition39Suzuki

/-!
The simple Suzuki source and fixed point descent share one standard
coefficient and root convention on the covering and target families.
-/
noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
open ModularRep.PaperProofs
open EvenFieldFLZFullHG EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open EvenFieldProposition39Relative EvenFieldProposition39Suzuki

structure SuzukiSource {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    (classification : FullHGTypeCClassificationSource scope) (pair : FullHG scope)
    (parameter : SuzukiParameter)
    (hcase : classification.structuralCase coverage pair = .typeC (.simpleSuzuki parameter))
    (automorphisms : ∀ b : (coverage.presentation pair).family.Block,
      Definition35AutomorphismStabilizerAdapter ((coverage.presentation pair).family.problem b))
    (source : ∀ b : (coverage.presentation pair).family.Block,
      FLZSourceSemantics ((coverage.presentation pair).family.problem b) (automorphisms b)) where
  published : SpathSuzukiFamilySource classification pair parameter hcase automorphisms source
  commonRoots : CommonFamilyRoots published.model.coverFamily (coverage.presentation pair).family

theorem SuzukiSource.blockWitness {ell : ℕ} {scope : FLZFullHGUniverse 2 ell}
    {coverage : FullHGDefinition35Coverage scope}
    {classification : FullHGTypeCClassificationSource scope} {pair : FullHG scope}
    {parameter : SuzukiParameter}
    {hcase : classification.structuralCase coverage pair = .typeC (.simpleSuzuki parameter)}
    {automorphisms : ∀ b : (coverage.presentation pair).family.Block,
      Definition35AutomorphismStabilizerAdapter ((coverage.presentation pair).family.problem b)}
    {source : ∀ b : (coverage.presentation pair).family.Block,
      FLZSourceSemantics ((coverage.presentation pair).family.problem b) (automorphisms b)}
    (S : SuzukiSource classification pair parameter hcase automorphisms source)
    (ell_ne_two : ell ≠ 2) (b : (coverage.presentation pair).family.Block) :
    Nonempty (Definition35IBAWBijection ((coverage.presentation pair).family.problem b)
      (automorphisms b) (source b)) :=
  S.published.blockWitness ell_ne_two b

end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
