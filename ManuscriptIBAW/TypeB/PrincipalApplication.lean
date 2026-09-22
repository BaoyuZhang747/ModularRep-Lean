import ManuscriptIBAW.TypeB.ExceptionalPrincipalDescent
import ManuscriptIBAW.TypeB.PrincipalField
import ManuscriptIBAW.TypeB.PrincipalSeries
import ManuscriptIBAW.TypeB.GGGRBasis
import ModularRep.PaperProofs.TypeBCurrentPrincipalInputs

/-!
# The principal GGGR construction and application

The principal series assertion is proved from the underlying context data
and the published source assumptions. The resulting context supplies the
matrix and character selection arguments. The application to the Spin family
uses the published result for Omega outside the exceptional case. For
Omega7(3), it descends the proved family on its triple cover. Both cases
then use the correspondence through the central quotient. The basis, field
invariance of principal Brauer characters and principal iBAW bijection
follow from the stated assumptions.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.PrincipalApplication

open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBCentralKernelBlockSource TypeBCurrentPrincipalResults
open scoped Pointwise

section ActualSpin

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  {parameters : OddFieldParameters F r f} {rank : 3 ≤ n}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]

/-- Every assumption is on one actual context, including its ordinary
coefficient field, modular system root, principal idempotent and GGGRs. -/
structure Inputs (D : PrincipalSeries.ContextData parameters rank Msys iota b)
    (S : FieldActionSource n F r f parameters N) where
  series : PrincipalSeries.Binding D
  rank : GGGRSources.RankSources series.context
  field : PrincipalField.Sources series.context S

/-- Construct the GGGR context after proving its principal series assertion. -/
def Inputs.context {D : PrincipalSeries.ContextData parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Inputs D S) :
    GGGRContext parameters rank Msys iota b := source.series.context

def Inputs.raw {D : PrincipalSeries.ContextData parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Inputs D S) :
    GGGRSources.RankSources source.context :=
  source.rank

def Inputs.fieldSources {D : PrincipalSeries.ContextData parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Inputs D S) :
    FieldSources source.context S :=
  source.field.toLegacy

/-- Proposition 4.9: the original principal projections form a basis of the
rational span of PIM characters, with principal rows and the stated matrix
pattern. -/
theorem gggr_basis {D : PrincipalSeries.ContextData parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Inputs D S) :
    GGGRConclusion source.context :=
  GGGRBasis.gggr_basis source.context source.raw

/-- The hypothesis on the field action in Corollary 4.10, including rank three
over F3. -/
theorem principalBrauer_fixed {D : PrincipalSeries.ContextData parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Inputs D S)
    (e : FieldGroup f) (phi : IBr iota) (supported : Supported iota b phi) :
    IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F S e) = phi :=
  GGGRBasis.principalBrauer_fixed
    source.context source.raw S source.fieldSources e phi supported

/-- The same fixed characters give the specified Clifford stabiliser and an
extension by an irreducible representation to the semidirect product of Spin with the field group. These conclusions do not require the condition on the exceptional
Omega cover. -/
theorem principal_selector {D : PrincipalSeries.ContextData parameters rank Msys iota b}
    {S : FieldActionSource n F r f parameters N} (source : Inputs D S)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (phi : IBr iota) (supported : Supported iota b phi) :
    (∀ e : FieldGroup f, IrreducibleBrauerCharacter.twist iota phi
      (spinFieldAction n F S e) = phi) ∧
    (TypeBAllRankPrincipalSelectorSemidirect.cliffordStabilizer S iota phi :
      Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) =
      (((TypeBInertiaHallSource.brauerInertia N iota phi).map
        (SemidirectProduct.inl (φ := S.action))) :
          Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) *
      ((SemidirectProduct.inr (φ := S.action)).range :
        Set (SpecialClifford n F ⋊[S.action] FieldGroup f)) ∧
    ∃ V : FDRep k (Spin n F N), Representation.IsIrreducible V.ρ ∧
      phi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
      ∃ rho : Representation k (Spin n F N ⋊[spinFieldAction n F S] FieldGroup f) V.V,
        Representation.IsIrreducible rho ∧
        Nonempty (Representation.Equiv
          (Representation.pullback rho
            (SemidirectProduct.inl (φ := spinFieldAction n F S))) V.ρ) :=
  GGGRBasis.principal_selector
    source.context source.raw S source.fieldSources principle phi supported

end ActualSpin

open EvenFieldFLZDefinition35Family EvenFieldFLZSourceConditions
open TypeBCurrentStrictRouting TypeBCurrentPrincipalInputs

open TypeBCurrentPrincipalBijection TypeBModularGroupRootBinding

/-- The specified coefficient fields and groups for the principal construction. -/
structure SpinGGGRInputs {p n : ℕ} (family : Definition35Family 2)
    (block : family.Block) (coordinates : SpinCoordinates p n family.H)
    (principal : PrincipalSpinCarrier family block n coordinates) where
  O : Type
  [ringO : CommRing O]
  [domainO : IsDomain O]
  [algebraO : Algebra O family.K]
  [finiteUpper : Finite (SpecialClifford n coordinates.F)]
  [finiteLower : Finite (Spin n coordinates.F coordinates.norm)]
  [rootsUpper : HasEnoughRootsOfUnity family.K
    (Nat.card (SpecialClifford n coordinates.F))]
  [rootsLower : HasEnoughRootsOfUnity family.K
    (Nat.card (Spin n coordinates.F coordinates.norm))]
  [finiteIrr : Finite (OrdinaryIrreducibleCharacter.Irr family.K
    (Spin n coordinates.F coordinates.norm))]
  [finiteBlocks : Fintype (LiteralPrimitiveBlock family.k
    (Spin n coordinates.F coordinates.norm))]
  Msys : ModularSystem 2 family.K O family.k
  familyRoot : family.iota = groupRoot Msys family.H
  spinBlock : LiteralPrimitiveBlock family.k (Spin n coordinates.F coordinates.norm)
  data : PrincipalSeries.ContextData coordinates.parameters principal.rankAtLeastThree Msys
    (groupRoot Msys (Spin n coordinates.F coordinates.norm)) spinBlock
  fieldAction : FieldActionSource n coordinates.F p coordinates.exponent
    coordinates.parameters coordinates.norm
  current : Inputs data fieldAction
  clifford : TypeBCliffordOrthogonalSourceBinding.Source n coordinates.F p
    coordinates.exponent coordinates.parameters principal.rankAtLeastThree coordinates.norm

attribute [instance] SpinGGGRInputs.ringO SpinGGGRInputs.domainO SpinGGGRInputs.algebraO

/-- The central quotient correspondence, the published nonexceptional
Omega result, and the descent of the exceptional covering family. -/
structure PrincipalRemainder {p n : ℕ} (family : Definition35Family 2)
    (block : family.Block) (coordinates : SpinCoordinates p n family.H)
    (principal : PrincipalSpinCarrier family block n coordinates)
    (automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (semantics : FLZSourceSemantics (family.problem block) automorphisms)
    (gggr : SpinGGGRInputs family block coordinates principal) where
  central : CurrentCentralQuotientReturnAdapter.CentralReturnInputs
    (family.problem block) automorphisms semantics
  presentation : OmegaPrincipalPresentation (n := n) (F := coordinates.F)
    central.downFamily central.downBlock
  physical : PhysicalFamilySource central.downFamily
  downAutomorphisms : Definition35AutomorphismStabilizerAdapter
    (central.downFamily.problem central.downBlock)
  downRoots : central.downFamily.iota = groupRoot gggr.Msys central.downFamily.H
  normalization : PairNormalizationSource (central.downFamily.problem central.downBlock)
  simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega n coordinates.F)
  nonexceptional : by
    letI := gggr.finiteUpper
    letI := gggr.finiteLower
    letI := gggr.rootsUpper
    letI := gggr.rootsLower
    letI := gggr.finiteIrr
    letI := gggr.finiteBlocks
    letI : Algebra gggr.O central.downFamily.K := gggr.algebraO
    letI : HasEnoughRootsOfUnity central.downFamily.K
        (Nat.card (SpecialClifford n coordinates.F)) := gggr.rootsUpper
    letI : HasEnoughRootsOfUnity central.downFamily.K
        (Nat.card (Spin n coordinates.F coordinates.norm)) := gggr.rootsLower
    letI : Finite (OrdinaryIrreducibleCharacter.Irr central.downFamily.K
        (Spin n coordinates.F coordinates.norm)) := gggr.finiteIrr
    letI : Fintype (LiteralPrimitiveBlock central.downFamily.k
        (Spin n coordinates.F coordinates.norm)) := gggr.finiteBlocks
    exact (n, Nat.card coordinates.F) ≠ (3, 3) →
      ∃ cover : EllPrimeCoverSource 2 central.downFamily.H,
        FYZ516SpathSource (family := central.downFamily) (block := central.downBlock)
          gggr.current.context gggr.fieldAction gggr.clifford presentation
          downAutomorphisms cover physical rfl downRoots
  exceptional : (n, Nat.card coordinates.F) = (3, 3) →
    Exceptional.PrincipalSources central.downFamily central.downBlock

/-- The principal inputs consist of the underlying GGGR context data and
separate published assumptions. The principal series assertion and the GGGR
rank and field conclusions follow from these assumptions. -/
structure PrincipalApplicationInputs {p n : ℕ} (family : Definition35Family 2)
    (block : family.Block) (coordinates : SpinCoordinates p n family.H)
    (principal : PrincipalSpinCarrier family block n coordinates)
    (automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block))
    (semantics : FLZSourceSemantics (family.problem block) automorphisms) where
  gggr : SpinGGGRInputs family block coordinates principal
  remainder : PrincipalRemainder family block coordinates principal automorphisms semantics gggr

/-- Construct the principal iBAW bijection from the deductions above,
the two Omega arguments and the central quotient correspondence. -/
theorem PrincipalApplicationInputs.exists_witness {p n : ℕ} {family : Definition35Family 2}
    {block : family.Block} {coordinates : SpinCoordinates p n family.H}
    {principal : PrincipalSpinCarrier family block n coordinates}
    {automorphisms : Definition35AutomorphismStabilizerAdapter (family.problem block)}
    {semantics : FLZSourceSemantics (family.problem block) automorphisms}
    (source : PrincipalApplicationInputs family block coordinates principal automorphisms semantics) :
    Nonempty (Definition35IBAWBijection (family.problem block) automorphisms semantics) := by
  let := source.gggr.finiteUpper
  let := source.gggr.finiteLower
  let := source.gggr.rootsUpper
  let := source.gggr.rootsLower
  let := source.gggr.finiteIrr
  let := source.gggr.finiteBlocks
  let : Algebra source.gggr.O source.remainder.central.downFamily.K := source.gggr.algebraO
  let : HasEnoughRootsOfUnity source.remainder.central.downFamily.K
      (Nat.card (SpecialClifford n coordinates.F)) := source.gggr.rootsUpper
  let : HasEnoughRootsOfUnity source.remainder.central.downFamily.K
      (Nat.card (Spin n coordinates.F coordinates.norm)) := source.gggr.rootsLower
  let : Finite (OrdinaryIrreducibleCharacter.Irr source.remainder.central.downFamily.K
      (Spin n coordinates.F coordinates.norm)) := source.gggr.finiteIrr
  let : Fintype (LiteralPrimitiveBlock source.remainder.central.downFamily.k
      (Spin n coordinates.F coordinates.norm)) := source.gggr.finiteBlocks
  by_cases exceptional : (n, Nat.card coordinates.F) = (3, 3)
  · obtain ⟨good⟩ := (source.remainder.exceptional exceptional).coherent
    exact ⟨source.remainder.central.toDefinition35
      { omega := good.omega, equivariant := good.equivariant, matched := good.matched }⟩
  · obtain ⟨_cover, published⟩ := source.remainder.nonexceptional exceptional
    obtain ⟨good⟩ := published.apply516 source.remainder.simple exceptional
      (fun e phi supported => principalBrauer_fixed source.gggr.current e phi supported)
    let normalized := good.normalize source.remainder.normalization
    exact ⟨source.remainder.central.toDefinition35
      { omega := normalized.omega, equivariant := normalized.equivariant,
        matched := normalized.matched }⟩

end ManuscriptIBAW.TypeB.PrincipalApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/

