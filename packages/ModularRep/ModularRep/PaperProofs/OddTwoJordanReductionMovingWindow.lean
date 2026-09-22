import ModularRep.PaperProofs.OddTwoProposition33Relative

/-!
# Odd-field type-C Jordan-reduction moving window

This file isolates the strictly quasi-isolated/Jordan-reduction paragraph of
manuscript Proposition 3.3 (`prop:odd-two`).  It is deliberately independent
of the even-field centreless FLZ 5.7 gate: an odd-field symplectic group can
have nontrivial centre, and Theorem 5.7 asks instead that its central quotient
be simple and that the fixed-point group be the universal covering group.

## Honest boundary ledger

* **K.** Lean combines the four structural packets with the literal
  label/centraliser binding, reuses
  `strictly_quasi_isolated_typeA_or_principal_typeC`, dispatches its two
  alternatives to the type-A and independently established principal-type-C
  data, constructs both arms of FLZ Hypothesis 5.5, proves that an odd field
  size is not divisible by `2`, and applies the one-way Theorem 5.7 source.
* **E1.** `CSubdiagramSource`, `DualBCSource`, `FixedClassicalSource`, and
  `COddFormsSource` are exactly the routine structural inputs
  `SF-C-SUBDIAGRAMS`, `SF-DUAL-BC`, `SF-FIXED-CLASSICAL`, and
  `SF-C-ODD-FORMS`.  Their canonical locators are recorded below.
* **E2.** Bonnafe, Proposition 4.11(a); Feng--Li--Zhang, Remarks 5.4 and 5.8,
  Assumption 5.3, Hypothesis 5.5, and Theorem 5.7; the Feng--Malle stable-basic-
  set context surrounding Corollary 4.6; the type-A theorem; and the
  BAW-good-to-iBAW passage are represented by separate, one-directional
  packets.  Hypothesis 5.5 is only a cited schema: it is constructed here and
  is never supplied as evidence.
* **U.** The exact dependent carrier of all pairs in `H_G` and all their
  blocks; the semisimple label carrier; the `2'`-label/order adapter; the
  algebraic finite/connected/full centralisers and proper-Levi predicate; the
  identity-label/unipotent/principal identifications; the type-A source match;
  the odd symplectic Assumption 5.3 match; and the ambient algebraic,
  fixed-point, central-quotient, universal-cover, field-size, and block-carrier
  matches remain explicit bindings.  `PrincipalTypeCBlockData` is a parameter
  for the independently established principal-block argument preceding this
  window; this file assigns it no K credit.

No source or carrier binding accepts Proposition 3.3, the strict-block arm of
Hypothesis 5.5, all-block BAW-goodness, an ambient iBAW conclusion, or an
equivalent target as a premise.  The strict-block arm is constructed below
from the K alternative before the exact Hypothesis 5.5 record is formed.  The
final endpoint concludes only BAW-goodness for the fixed-point group's
blocks; the block-orbit aggregation and passage from `Sp` to `PSp` lie outside
this file.
-/

noncomputable section

open scoped Pointwise

namespace ModularRep.PaperProofs.OddTwoJordanReductionMovingWindow

open ModularRep
open ModularRep.ManuscriptVerification.StrictQuasiIsolation
open ModularRep.PaperProofs.OddTwoProposition33Relative

universe u

/-! ## Auditable source locators -/

/-- The four-way trust classification used only by this file's audit ledger. -/
inductive BoundaryKind where
  | K
  | E1
  | E2
  | U
  deriving DecidableEq, Repr

/-- A human-readable, exact locator attached to a narrow source packet. -/
structure SourceLocator where
  boundary : BoundaryKind
  key : String
  item : String
  location : String
  deriving DecidableEq, Repr

def strictAlternativeLocator : SourceLocator :=
  { boundary := .K
    key := "ODD-TWO-STRICT-ALTERNATIVE"
    item :=
      "OddTwoProposition33Relative.strictly_quasi_isolated_typeA_or_principal_typeC"
    location :=
      "ModularRep/PaperProofs/OddTwoProposition33Relative.lean, JordanTransition" }

def cSubdiagramsLocator : SourceLocator :=
  { boundary := .E1
    key := "SF-C-SUBDIAGRAMS"
    item := "connected subdiagrams of C_n have type A or C"
    location :=
      "Malle--Testerman, Table 9.1 and the definition before Theorem 9.6" }

def dualBCLocator : SourceLocator :=
  { boundary := .E1
    key := "SF-DUAL-BC"
    item := "the root systems B_n and C_n are dual"
    location :=
      "Malle--Testerman, Appendix B.4, paragraph after Table B.2" }

def fixedClassicalLocator : SourceLocator :=
  { boundary := .E1
    key := "SF-FIXED-CLASSICAL"
    item := "the relevant classical fixed-point groups are Sp and SO"
    location :=
      "Malle--Testerman, Table 27.1 and Section 27.1, pp. 236--237; Example 21.1 and Definition 21.6" }

def cOddFormsLocator : SourceLocator :=
  { boundary := .E1
    key := "SF-C-ODD-FORMS"
    item := "odd-characteristic simply connected type C has split symplectic fixed points"
    location :=
      "Malle--Testerman, Table 11.1 and Section 22.2, especially Table 22.1" }

def bonnafe411aLocator : SourceLocator :=
  { boundary := .E2
    key := "BONNAFE-4.11A"
    item := "a quasi-isolated semisimple element in odd-characteristic SO has square one"
    location :=
      "Bonnafe, Communications in Algebra 33 (2005), Section 4.E, Proposition 4.11(a), pp. 2330--2331" }

def flzRemark58Locator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-REMARK-5.8"
    item := "the quasi-isolated 2-block of odd symplectic type is the unique unipotent block"
    location :=
      "Feng--Li--Zhang, Advances in Mathematics 408 (2022), Remark 5.8, p. 34" }

def fengMalleBasicSetLocator : SourceLocator :=
  { boundary := .E2
    key := "FM-STABLE-BASIC-SET-4.6-CONTEXT"
    item := "the odd symplectic 2-modular basic set is Aut-stable and unitriangular"
    location :=
      "Feng--Malle, Journal of the Australian Mathematical Society 113 (2022), proof immediately preceding Corollary 4.6 and Corollary 4.6, p. 10" }

def flzAssumption53Locator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-ASSUMPTION-5.3"
    item := "regular-orbit representative, stabiliser factorisation, and extension"
    location :=
      "Feng--Li--Zhang, Advances in Mathematics 408 (2022), Assumption 5.3, p. 30" }

def flzRemark54Locator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-REMARK-5.4"
    item := "an Aut-stable unitriangular basic set implies Assumption 5.3"
    location :=
      "Feng--Li--Zhang, Advances in Mathematics 408 (2022), Remark 5.4, pp. 30--31" }

def flzHypothesis55Locator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-HYPOTHESIS-5.5"
    item := "Assumption 5.3 together with iBAW for every strict block in H_G"
    location :=
      "Feng--Li--Zhang, Advances in Mathematics 408 (2022), Hypothesis 5.5(a)--(b), p. 31" }

def flzTheorem57Locator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-THEOREM-5.7"
    item := "Hypothesis 5.5 implies BAW-goodness of every fixed-point block"
    location :=
      "Feng--Li--Zhang, Advances in Mathematics 408 (2022), Theorem 5.7, pp. 33--34" }

def typeATheoremLocator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-TYPE-A"
    item := "all nondefining-characteristic type-A blocks are BAW-good"
    location :=
      "Feng--Li--Zhang, Transactions of the AMS 376 (2023), Theorem 5.2 and proof of Theorem 1, pp. 6515--6517" }

def bawGoodToIBAWLocator : SourceLocator :=
  { boundary := .E2
    key := "FLZ-SECTION-3.5-IBAW"
    item := "the fixed BAW-good block data supplies an iBAW bijection"
    location :=
      "Feng--Li--Zhang, Advances in Mathematics 408 (2022), Section 3.5" }

def strictCarrierBindingLocator : SourceLocator :=
  { boundary := .U
    key := "ODD-TWO-STRICT-CARRIER-BINDING"
    item := "literal H_G block, label, centraliser, Levi, and identity-series semantics"
    location :=
      "Explicit strict-carrier identification interface (U); see docs/source-assumptions.md" }

/-- The locators used by this moving window, in proof order. -/
def sourceLedger : List SourceLocator :=
  [cSubdiagramsLocator, dualBCLocator, fixedClassicalLocator,
    cOddFormsLocator, strictCarrierBindingLocator, bonnafe411aLocator,
    flzRemark58Locator, typeATheoremLocator, bawGoodToIBAWLocator,
    fengMalleBasicSetLocator, flzRemark54Locator, flzAssumption53Locator,
    flzHypothesis55Locator, flzTheorem57Locator, strictAlternativeLocator]

/-! ## One fixed interpretation of the moving window -/

/-- All predicates in the window are fixed before a source theorem is
selected.  `Pair` is intended to be the full dependent `H_G` carrier and
`FamilyBlock` below bundles every block of every such pair.  The exact source
identifications are deliberately represented by the marker propositions and
discharged only by the U-level binding packets. -/
structure Semantics where
  Pair : Type u
  Block : Pair → Type u
  Parameter : Type u
  [groupParameter : Group Parameter]
  AmbientBlock : Type u
  BrauerCharacter : Type u
  fieldSize : ℕ

  IsStrictBlock : (Σ pair, Block pair) → Prop
  IsTypeA : (Σ pair, Block pair) → Prop
  IsTypeC : (Σ pair, Block pair) → Prop
  IsSemisimpleTwoPrime : Parameter → Prop
  IsAssociated : (Σ pair, Block pair) → Parameter → Prop
  IsPrincipalBlock : (Σ pair, Block pair) → Prop
  IsProperLevi : Set Parameter → Prop

  IsSemisimpleParameter : Parameter → Prop
  IsTypeBDualParameter : Parameter → Prop
  IsSpecialOrthogonalParameter : Parameter → Prop
  IsOddCharacteristicParameter : Parameter → Prop
  IsSymplecticFixedBlock : (Σ pair, Block pair) → Prop
  IsOddSplitTypeCBlock : (Σ pair, Block pair) → Prop
  IsQuasiIsolatedTwoBlock : (Σ pair, Block pair) → Prop
  IsUnipotentBlock : (Σ pair, Block pair) → Prop
  IsSourceTypeABlock : (Σ pair, Block pair) → Prop

  HasIBAW : (Σ pair, Block pair) → Prop
  IsFamilyBlockBAWGood : (Σ pair, Block pair) → Prop
  IsAmbientBlockBAWGood : AmbientBlock → Prop
  CoefficientTwoIsNondefining : Prop

  InSameRegularOrbit : BrauerCharacter → BrauerCharacter → Prop
  StabilizerFactorization : BrauerCharacter → Prop
  ExtendsToFieldStabilizer : BrauerCharacter → Prop
  HasAutStableUnitriangularBasicSet : Prop

  StrictCarrierMatchesHypothesis55 : Prop
  ParameterCarrierMatchesOddSODual : Prop
  TypeAFamilyMatchesSource : Prop
  Assumption53CarrierMatches : Prop
  IsFengMalleOddSymplecticAtTwo : Prop
  AmbientBlockCarrierMatches : Prop
  IsSimpleAlgebraicGroupOfSimplyConnectedType : Prop
  HasSteinbergEndomorphism : Prop
  FixedPointCentralQuotientIsSimple : Prop
  FixedPointGroupIsUniversalCover : Prop

attribute [instance] Semantics.groupParameter

/-- The dependent carrier of all blocks in all represented pairs. -/
abbrev FamilyBlock (S : Semantics) := Σ pair, S.Block pair

/-! ## Exact structural and carrier packets -/

/-- `SF-C-SUBDIAGRAMS`, restricted to the full carrier fixed by `S`. -/
structure CSubdiagramSource (S : Semantics) : Prop where
  cases : S.StrictCarrierMatchesHypothesis55 →
    ∀ b : FamilyBlock S, S.IsStrictBlock b → S.IsTypeA b ∨ S.IsTypeC b

def CSubdiagramSource.locator {S : Semantics} (_ : CSubdiagramSource S) :
    SourceLocator :=
  cSubdiagramsLocator

/-- `SF-DUAL-BC`, after the explicit parameter-carrier match. -/
structure DualBCSource (S : Semantics) : Prop where
  typeBDual : S.ParameterCarrierMatchesOddSODual →
    ∀ s : S.Parameter, S.IsTypeBDualParameter s

def DualBCSource.locator {S : Semantics} (_ : DualBCSource S) :
    SourceLocator :=
  dualBCLocator

/-- The two fixed-classical identifications used in this window. -/
structure FixedClassicalSource (S : Semantics) : Prop where
  specialOrthogonal : S.ParameterCarrierMatchesOddSODual →
    ∀ s : S.Parameter,
      S.IsTypeBDualParameter s → S.IsSpecialOrthogonalParameter s
  symplecticFixed : S.StrictCarrierMatchesHypothesis55 →
    ∀ b : FamilyBlock S, S.IsTypeC b → S.IsSymplecticFixedBlock b

def FixedClassicalSource.locator {S : Semantics}
    (_ : FixedClassicalSource S) : SourceLocator :=
  fixedClassicalLocator

/-- `SF-C-ODD-FORMS` in its actual implication direction: oddness is a
premise, not a conclusion of the classification. -/
structure COddFormsSource (S : Semantics) : Prop where
  oddSpecialOrthogonal : Odd S.fieldSize →
    ∀ s : S.Parameter,
      S.IsSpecialOrthogonalParameter s →
        S.IsOddCharacteristicParameter s
  splitSymplectic : Odd S.fieldSize →
    S.StrictCarrierMatchesHypothesis55 →
      ∀ b : FamilyBlock S,
        S.IsTypeC b → S.IsOddSplitTypeCBlock b

def COddFormsSource.locator {S : Semantics} (_ : COddFormsSource S) :
    SourceLocator :=
  cOddFormsLocator

/-- Application-specific oddness of the field size. -/
structure OddFieldBinding (S : Semantics) : Prop where
  fieldSize_odd : Odd S.fieldSize
  coefficientTwo_nondefining : S.CoefficientTwoIsNondefining

/-- The U-level identification of the parameter type with semisimple elements
of the actual odd special-orthogonal dual carrier. -/
structure ParameterCarrierBinding (S : Semantics) : Prop where
  carrierMatch : S.ParameterCarrierMatchesOddSODual
  semisimple : ∀ s : S.Parameter, S.IsSemisimpleParameter s

/-- The literal strict-block label and centraliser/Levi semantics.  It gives
no type-A/principal-type-C alternative and no iBAW conclusion. -/
structure StrictBlockCarrierBinding (S : Semantics) where
  carrierMatch : S.StrictCarrierMatchesHypothesis55
  label : FamilyBlock S → S.Parameter
  finiteCentralizer : S.Parameter → Subgroup S.Parameter
  connectedCentralizer : S.Parameter → Subgroup S.Parameter
  finiteCentralizer_le : ∀ s,
    finiteCentralizer s ≤ Subgroup.centralizer {s}
  connectedCentralizer_le : ∀ s,
    connectedCentralizer s ≤ Subgroup.centralizer {s}
  typeCLabel : ∀ b : FamilyBlock S,
    S.IsStrictBlock b → S.IsTypeC b →
      S.IsSemisimpleTwoPrime (label b) ∧
      S.IsAssociated b (label b) ∧
      NotContainedInProperLevi
        ((finiteCentralizer (label b) : Set S.Parameter) *
          (connectedCentralizer (label b) : Set S.Parameter))
        S.IsProperLevi

def StrictBlockCarrierBinding.locator {S : Semantics}
    (_ : StrictBlockCarrierBinding S) : SourceLocator :=
  strictCarrierBindingLocator

/-- The concrete `2'`-label to odd-`orderOf` adapter.  Its application is K;
matching the source predicate is the explicit U field below. -/
structure TwoPrimeOrderBinding (S : Semantics) : Prop where
  toPrimeRegular : OddQuasiIsolation.TwoPrimeOrderInterface
    S.IsSemisimpleTwoPrime

/-- The U-level bridges surrounding FLZ Remark 5.8.  In particular, the
published remark does not by itself identify an abstract Lean block with the
principal block. -/
structure IdentityLabelPrincipalBinding (S : Semantics) : Prop where
  typeC_of_associated : ∀ {b : FamilyBlock S} {s : S.Parameter},
    S.IsAssociated b s → S.IsTypeC b
  quasiIsolatedBlock_of_associated_one : ∀ {b : FamilyBlock S},
    S.IsAssociated b 1 → S.IsQuasiIsolatedTwoBlock b
  principal_of_unipotent : ∀ {b : FamilyBlock S},
    S.IsUnipotentBlock b → S.IsPrincipalBlock b

/-! ## Narrow E2 theorem packets -/

/-- The used direction of Bonnafe, Proposition 4.11(a), with every carrier
and characteristic condition visible. -/
structure Bonnafe411aSource (S : Semantics) : Prop where
  square_of_quasiIsolated : ∀ {s : S.Parameter},
    S.IsSemisimpleParameter s →
    S.IsTypeBDualParameter s →
    S.IsSpecialOrthogonalParameter s →
    S.IsOddCharacteristicParameter s →
    NotContainedInProperLevi
      (Subgroup.centralizer {s} : Set S.Parameter)
      S.IsProperLevi →
    s ^ 2 = 1

def Bonnafe411aSource.locator {S : Semantics} (_ : Bonnafe411aSource S) :
    SourceLocator :=
  bonnafe411aLocator

/-- FLZ Remark 5.8 contributes only the unipotent-block assertion on the
matched odd symplectic carrier. -/
structure FLZRemark58Source (S : Semantics) : Prop where
  unipotent : ∀ b : FamilyBlock S,
    S.IsSymplecticFixedBlock b →
    S.IsOddSplitTypeCBlock b →
    S.IsQuasiIsolatedTwoBlock b →
    S.IsUnipotentBlock b

def FLZRemark58Source.locator {S : Semantics} (_ : FLZRemark58Source S) :
    SourceLocator :=
  flzRemark58Locator

/-- The U-level match from a type-A branch to the exact family covered by the
cited type-A theorem. -/
structure TypeABlockCarrierBinding (S : Semantics) : Prop where
  familyMatch : S.TypeAFamilyMatchesSource
  sourceBlock : ∀ b : FamilyBlock S,
    S.IsTypeA b → S.IsSourceTypeABlock b

/-- The type-A result retains its published BAW-good conclusion. -/
structure TypeATheoremSource (S : Semantics) : Prop where
  bawGood : S.CoefficientTwoIsNondefining →
    S.TypeAFamilyMatchesSource →
    ∀ b : FamilyBlock S,
      S.IsSourceTypeABlock b → S.IsFamilyBlockBAWGood b

def TypeATheoremSource.locator {S : Semantics} (_ : TypeATheoremSource S) :
    SourceLocator :=
  typeATheoremLocator

/-- The separate Section 3.5 passage from the fixed BAW-good semantics to an
iBAW bijection for the same block. -/
structure BAWGoodToIBAWSource (S : Semantics) : Prop where
  toIBAW : ∀ b : FamilyBlock S,
    S.IsFamilyBlockBAWGood b → S.HasIBAW b

def BAWGoodToIBAWSource.locator {S : Semantics}
    (_ : BAWGoodToIBAWSource S) : SourceLocator :=
  bawGoodToIBAWLocator

/-- The independently established principal type-C data from the first half
of Proposition 3.3.  This is intentionally narrower than the strict-block
arm of Hypothesis 5.5. -/
structure PrincipalTypeCBlockData (S : Semantics) : Prop where
  iBAW : ∀ b : FamilyBlock S,
    S.IsTypeC b →
    S.IsSymplecticFixedBlock b →
    S.IsOddSplitTypeCBlock b →
    S.IsPrincipalBlock b →
    S.HasIBAW b

/-! ## Reuse of the existing K Jordan alternative -/

/-- Combine exactly the input of the existing K theorem.  The seemingly
odd predicate in the Bonnafe packet is replaced here by the literal proper-
Levi predicate of `Carrier`; thus it cannot drift between strictness and the
square theorem. -/
def strictSubdiagramData
    (S : Semantics)
    (OddField : OddFieldBinding S)
    (Subdiagrams : CSubdiagramSource S)
    (Dual : DualBCSource S)
    (Fixed : FixedClassicalSource S)
    (Forms : COddFormsSource S)
    (Parameters : ParameterCarrierBinding S)
    (Carrier : StrictBlockCarrierBinding S)
    (Order : TwoPrimeOrderBinding S)
    (Bonnafe : Bonnafe411aSource S)
    (Remark58 : FLZRemark58Source S)
    (Identity : IdentityLabelPrincipalBinding S) :
    StrictSubdiagramData
      (Parameter := S.Parameter) (Block := FamilyBlock S) where
  IsStrictBlock := S.IsStrictBlock
  IsTypeA := S.IsTypeA
  IsTypeC := S.IsTypeC
  IsSemisimpleTwoPrime := S.IsSemisimpleTwoPrime
  IsAssociated := S.IsAssociated
  IsPrincipalBlock := S.IsPrincipalBlock
  finiteCentralizer := Carrier.finiteCentralizer
  connectedCentralizer := Carrier.connectedCentralizer
  IsProperLevi := S.IsProperLevi
  finiteCentralizer_le := Carrier.finiteCentralizer_le
  connectedCentralizer_le := Carrier.connectedCentralizer_le
  split := by
    intro b hb
    rcases Subdiagrams.cases Carrier.carrierMatch b hb with hA | hC
    · exact Or.inl hA
    · rcases Carrier.typeCLabel b hb hC with
        ⟨hTwoPrime, hAssociated, hStrict⟩
      exact Or.inr
        ⟨Carrier.label b, hC, hTwoPrime, hAssociated, hStrict⟩
  bonnafeSquare := by
    intro s hQuasi
    exact Bonnafe.square_of_quasiIsolated
      (Parameters.semisimple s)
      (Dual.typeBDual Parameters.carrierMatch s)
      (Fixed.specialOrthogonal Parameters.carrierMatch s
        (Dual.typeBDual Parameters.carrierMatch s))
      (Forms.oddSpecialOrthogonal OddField.fieldSize_odd s
        (Fixed.specialOrthogonal Parameters.carrierMatch s
          (Dual.typeBDual Parameters.carrierMatch s)))
      hQuasi
  twoPrimeOrder := Order.toPrimeRegular
  identityLabelPrincipal := by
    intro b s hAssociated hs
    have hAssociatedOne : S.IsAssociated b 1 := by
      simpa [hs] using hAssociated
    have hTypeC : S.IsTypeC b :=
      Identity.typeC_of_associated hAssociatedOne
    exact Identity.principal_of_unipotent
      (Remark58.unipotent b
        (Fixed.symplecticFixed Carrier.carrierMatch b hTypeC)
        (Forms.splitSymplectic OddField.fieldSize_odd Carrier.carrierMatch b
          hTypeC)
        (Identity.quasiIsolatedBlock_of_associated_one hAssociatedOne))

/-- Dispatch the K-produced alternative.  No premise states that all strict
blocks have iBAW. -/
theorem strictBlock_hasIBAW
    (S : Semantics)
    (OddField : OddFieldBinding S)
    (Subdiagrams : CSubdiagramSource S)
    (Dual : DualBCSource S)
    (Fixed : FixedClassicalSource S)
    (Forms : COddFormsSource S)
    (Parameters : ParameterCarrierBinding S)
    (Carrier : StrictBlockCarrierBinding S)
    (Order : TwoPrimeOrderBinding S)
    (Bonnafe : Bonnafe411aSource S)
    (Remark58 : FLZRemark58Source S)
    (Identity : IdentityLabelPrincipalBinding S)
    (TypeABinding : TypeABlockCarrierBinding S)
    (TypeA : TypeATheoremSource S)
    (BAWToIBAW : BAWGoodToIBAWSource S)
    (PrincipalC : PrincipalTypeCBlockData S)
    (b : FamilyBlock S) (hb : S.IsStrictBlock b) :
    S.HasIBAW b := by
  have hAlternative :=
    strictly_quasi_isolated_typeA_or_principal_typeC
      (strictSubdiagramData S OddField Subdiagrams Dual Fixed Forms Parameters
        Carrier Order Bonnafe Remark58 Identity) hb
  rcases hAlternative with hA | ⟨hC, hPrincipal⟩
  · exact BAWToIBAW.toIBAW b
      (TypeA.bawGood OddField.coefficientTwo_nondefining
        TypeABinding.familyMatch b
        (TypeABinding.sourceBlock b hA))
  · exact PrincipalC.iBAW b hC
      (Fixed.symplecticFixed Carrier.carrierMatch b hC)
      (Forms.splitSymplectic OddField.fieldSize_odd Carrier.carrierMatch b hC)
      hPrincipal

/-! ## Assumption 5.3 and Hypothesis 5.5 -/

/-- The literal quantifier shape of FLZ Assumption 5.3. -/
structure FLZAssumption53 (S : Semantics) : Prop where
  representative : ∀ phi : S.BrauerCharacter,
    ∃ psi : S.BrauerCharacter,
      S.InSameRegularOrbit phi psi ∧
      S.StabilizerFactorization psi ∧
      S.ExtendsToFieldStabilizer psi

def FLZAssumption53.locator {S : Semantics} (_ : FLZAssumption53 S) :
    SourceLocator :=
  flzAssumption53Locator

/-- The exact odd symplectic context in which the basic-set argument is used. -/
structure Assumption53ContextBinding (S : Semantics) : Prop where
  fengMalleContext : S.IsFengMalleOddSymplecticAtTwo
  flzCarrierMatch : S.Assumption53CarrierMatches

/-- Feng--Malle supply the stable unitriangular basic-set input, not the
extension clause of Assumption 5.3 by itself. -/
structure FengMalleStableBasicSetSource (S : Semantics) : Prop where
  stableBasicSet : S.IsFengMalleOddSymplecticAtTwo →
    S.HasAutStableUnitriangularBasicSet

def FengMalleStableBasicSetSource.locator {S : Semantics}
    (_ : FengMalleStableBasicSetSource S) : SourceLocator :=
  fengMalleBasicSetLocator

/-- The implication in FLZ Remark 5.4.  Its conclusion is precisely
Assumption 5.3, including extension. -/
structure FLZRemark54Source (S : Semantics) : Prop where
  assumption53_of_stableBasicSet :
    S.Assumption53CarrierMatches →
    S.HasAutStableUnitriangularBasicSet →
    FLZAssumption53 S

def FLZRemark54Source.locator {S : Semantics} (_ : FLZRemark54Source S) :
    SourceLocator :=
  flzRemark54Locator

/-- The exact two arms of FLZ Hypothesis 5.5 on one fixed full carrier.
This is a constructed record, not a cited source premise. -/
structure FLZHypothesis55 (S : Semantics) : Prop where
  strictCarrierMatch : S.StrictCarrierMatchesHypothesis55
  assumption53 : FLZAssumption53 S
  strictBlocks : ∀ b : FamilyBlock S,
    S.IsStrictBlock b → S.HasIBAW b

def FLZHypothesis55.locator {S : Semantics} (_ : FLZHypothesis55 S) :
    SourceLocator :=
  flzHypothesis55Locator

/-- Construct Assumption 5.3 only through the Feng--Malle context and the
one-way implication of FLZ Remark 5.4. -/
theorem assumption53_of_sources
    (S : Semantics)
    (AssumptionBinding : Assumption53ContextBinding S)
    (FengMalle : FengMalleStableBasicSetSource S)
    (Remark54 : FLZRemark54Source S) :
    FLZAssumption53 S :=
  Remark54.assumption53_of_stableBasicSet
    AssumptionBinding.flzCarrierMatch
    (FengMalle.stableBasicSet AssumptionBinding.fengMalleContext)

/-- The separately constructed Hypothesis 5.5(b) packet.  Its conclusion is
not a field of any source or carrier binding. -/
theorem strictHypothesis55b_of_sources
    (S : Semantics)
    (OddField : OddFieldBinding S)
    (Subdiagrams : CSubdiagramSource S)
    (Dual : DualBCSource S)
    (Fixed : FixedClassicalSource S)
    (Forms : COddFormsSource S)
    (Parameters : ParameterCarrierBinding S)
    (Carrier : StrictBlockCarrierBinding S)
    (Order : TwoPrimeOrderBinding S)
    (Bonnafe : Bonnafe411aSource S)
    (Remark58 : FLZRemark58Source S)
    (Identity : IdentityLabelPrincipalBinding S)
    (TypeABinding : TypeABlockCarrierBinding S)
    (TypeA : TypeATheoremSource S)
    (BAWToIBAW : BAWGoodToIBAWSource S)
    (PrincipalC : PrincipalTypeCBlockData S) :
    ∀ b : FamilyBlock S, S.IsStrictBlock b → S.HasIBAW b :=
  strictBlock_hasIBAW S OddField Subdiagrams Dual Fixed Forms
    Parameters Carrier Order Bonnafe Remark58 Identity TypeABinding TypeA
    BAWToIBAW PrincipalC

/-- Kernel construction of the cited Hypothesis 5.5 schema from its separately
proved (a) and (b) arms on the same literal carrier. -/
theorem hypothesis55_of_parts
    (S : Semantics)
    (strictCarrierMatch : S.StrictCarrierMatchesHypothesis55)
    (assumption53 : FLZAssumption53 S)
    (strictBlocks : ∀ b : FamilyBlock S,
      S.IsStrictBlock b → S.HasIBAW b) :
    FLZHypothesis55 S where
  strictCarrierMatch := strictCarrierMatch
  assumption53 := assumption53
  strictBlocks := strictBlocks

/-- Construct Hypothesis 5.5 from its two independently established arms. -/
theorem hypothesis55_of_sources
    (S : Semantics)
    (OddField : OddFieldBinding S)
    (Subdiagrams : CSubdiagramSource S)
    (Dual : DualBCSource S)
    (Fixed : FixedClassicalSource S)
    (Forms : COddFormsSource S)
    (Parameters : ParameterCarrierBinding S)
    (Carrier : StrictBlockCarrierBinding S)
    (Order : TwoPrimeOrderBinding S)
    (Bonnafe : Bonnafe411aSource S)
    (Remark58 : FLZRemark58Source S)
    (Identity : IdentityLabelPrincipalBinding S)
    (TypeABinding : TypeABlockCarrierBinding S)
    (TypeA : TypeATheoremSource S)
    (BAWToIBAW : BAWGoodToIBAWSource S)
    (PrincipalC : PrincipalTypeCBlockData S)
    (AssumptionBinding : Assumption53ContextBinding S)
    (FengMalle : FengMalleStableBasicSetSource S)
    (Remark54 : FLZRemark54Source S) :
    FLZHypothesis55 S :=
  hypothesis55_of_parts S Carrier.carrierMatch
    (assumption53_of_sources S AssumptionBinding FengMalle Remark54)
    (strictHypothesis55b_of_sources S OddField Subdiagrams Dual Fixed Forms
      Parameters Carrier Order Bonnafe Remark58 Identity TypeABinding TypeA
      BAWToIBAW PrincipalC)

/-! ## The non-centreless odd-field Theorem 5.7 gate -/

/-- U-level ambient identifications required before the cited theorem can be
applied.  Centrelessness is intentionally absent. -/
structure FLZ57OddAmbientBinding (S : Semantics) : Prop where
  blockCarrierMatch : S.AmbientBlockCarrierMatches
  simpleSimplyConnected : S.IsSimpleAlgebraicGroupOfSimplyConnectedType
  steinberg : S.HasSteinbergEndomorphism
  simpleCentralQuotient : S.FixedPointCentralQuotientIsSimple
  universalCover : S.FixedPointGroupIsUniversalCover

/-- The actual one-way implication of FLZ Theorem 5.7 at `ell = 2`.  Every
ambient and Hypothesis 5.5 premise remains visible. -/
structure FLZTheorem57Source (S : Semantics) : Prop where
  bawGood_of_hypothesis55 :
    S.AmbientBlockCarrierMatches →
    S.IsSimpleAlgebraicGroupOfSimplyConnectedType →
    S.HasSteinbergEndomorphism →
    S.FixedPointCentralQuotientIsSimple →
    S.FixedPointGroupIsUniversalCover →
    (¬ 2 ∣ S.fieldSize) →
    FLZHypothesis55 S →
    ∀ block : S.AmbientBlock, S.IsAmbientBlockBAWGood block

def FLZTheorem57Source.locator {S : Semantics} (_ : FLZTheorem57Source S) :
    SourceLocator :=
  flzTheorem57Locator

/-- Odd field size implies the nondefining-characteristic hypothesis used by
Theorem 5.7 at coefficient prime two. -/
theorem two_not_dvd_fieldSize_of_odd
    (S : Semantics) (OddField : OddFieldBinding S) :
    ¬ 2 ∣ S.fieldSize := by
  intro hTwo
  exact (Nat.not_even_iff_odd.mpr OddField.fieldSize_odd)
    (even_iff_two_dvd.mpr hTwo)

/-- The odd-field, non-centreless Theorem 5.7 gate.  Its two logical packets
are Assumption 5.3 and the already proved strict-block arm 5.5(b); it forms
Hypothesis 5.5 internally and uses the cited theorem only in its published
forward direction. -/
theorem oddField_noncentreless_theorem57_gate
    (S : Semantics)
    (OddField : OddFieldBinding S)
    (assumption53 : FLZAssumption53 S)
    (strictCarrierMatch : S.StrictCarrierMatchesHypothesis55)
    (strictBlocks : ∀ b : FamilyBlock S,
      S.IsStrictBlock b → S.HasIBAW b)
    (Ambient : FLZ57OddAmbientBinding S)
    (Theorem57 : FLZTheorem57Source S)
    (block : S.AmbientBlock) :
    S.IsAmbientBlockBAWGood block :=
  Theorem57.bawGood_of_hypothesis55
    Ambient.blockCarrierMatch
    Ambient.simpleSimplyConnected
    Ambient.steinberg
    Ambient.simpleCentralQuotient
    Ambient.universalCover
    (two_not_dvd_fieldSize_of_odd S OddField)
    (hypothesis55_of_parts S strictCarrierMatch assumption53 strictBlocks)
    block

/-- Final endpoint of this moving window: construct Hypothesis 5.5 and feed
it, in the published direction, to FLZ Theorem 5.7.  This is not Proposition
3.3 and does not conclude an ambient or projective-group iBAW statement. -/
theorem allAmbientBlocks_bawGood_of_oddTwoJordanSources
    (S : Semantics)
    (OddField : OddFieldBinding S)
    (Subdiagrams : CSubdiagramSource S)
    (Dual : DualBCSource S)
    (Fixed : FixedClassicalSource S)
    (Forms : COddFormsSource S)
    (Parameters : ParameterCarrierBinding S)
    (Carrier : StrictBlockCarrierBinding S)
    (Order : TwoPrimeOrderBinding S)
    (Bonnafe : Bonnafe411aSource S)
    (Remark58 : FLZRemark58Source S)
    (Identity : IdentityLabelPrincipalBinding S)
    (TypeABinding : TypeABlockCarrierBinding S)
    (TypeA : TypeATheoremSource S)
    (BAWToIBAW : BAWGoodToIBAWSource S)
    (PrincipalC : PrincipalTypeCBlockData S)
    (AssumptionBinding : Assumption53ContextBinding S)
    (FengMalle : FengMalleStableBasicSetSource S)
    (Remark54 : FLZRemark54Source S)
    (Ambient : FLZ57OddAmbientBinding S)
    (Theorem57 : FLZTheorem57Source S) :
    ∀ block : S.AmbientBlock, S.IsAmbientBlockBAWGood block := by
  intro block
  exact oddField_noncentreless_theorem57_gate S OddField
    (assumption53_of_sources S AssumptionBinding FengMalle Remark54)
    Carrier.carrierMatch
    (strictHypothesis55b_of_sources S OddField Subdiagrams Dual Fixed Forms
      Parameters Carrier Order Bonnafe Remark58 Identity TypeABinding TypeA
      BAWToIBAW PrincipalC)
    Ambient Theorem57 block

end ModularRep.PaperProofs.OddTwoJordanReductionMovingWindow


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
