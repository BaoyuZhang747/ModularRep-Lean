/-!
# Structural cases for even-field Proposition 3.9

This neutral module contains only the finite structural alternatives shared by
the legacy relative router and the protected universe-zero route.  It contains
no block predicate, branch theorem, or iBAW conclusion.
-/

namespace ModularRep.PaperProofs.EvenFieldProposition39Relative

/-- The three odd primes occurring for the exceptional split group
`Sp_6(2)`. -/
inductive Sp6PrimeCase where
  | three
  | five
  | seven
  deriving DecidableEq, Repr

/-- The positive parameter `m` in the Suzuki family
`^2B_2(2^(2m+1))`.  Its interpretation as the parameter of the represented
fixed point group remains part of the E1/U structural classification. -/
structure SuzukiParameter where
  twistParameter : Nat
  positiveTwistParameter : 0 < twistParameter
  deriving DecidableEq, Repr

/-- The rank and field exponent of a classified split type `C` branch in the
range used by Proposition 3.8.  Their interpretation for the represented
fixed point group remains part of the E1/U structural classification. -/
structure HighRankParameter where
  rank : Nat
  fieldExponent : Nat
  rankAtLeastFour : 4 ≤ rank
  positiveFieldExponent : 0 < fieldExponent
  deriving DecidableEq, Repr

/-- The two split type `C` ranks covered by the low rank cited result. -/
inductive SplitTypeCLowRank where
  | rankTwo
  | rankThree
  deriving DecidableEq, Repr

namespace SplitTypeCLowRank

/-- The rank represented by the closed low rank index. -/
@[simp]
def rank : SplitTypeCLowRank → Nat
  | .rankTwo => 2
  | .rankThree => 3

end SplitTypeCLowRank

/-- The rank branch and field exponent of a classified split low rank type
`C` group.  The stored bound expresses that the field has size at least four.
Its interpretation for the represented fixed point group remains part of the
E1/U structural classification. -/
structure SplitLowRankParameter where
  branch : SplitTypeCLowRank
  fieldExponent : Nat
  fieldExponentAtLeastTwo : 2 ≤ fieldExponent
  deriving DecidableEq, Repr

/-- The finite forms that remain for a type `C` connected subdiagram after
the standard classification of Steinberg endomorphisms and the simplicity
exclusions. -/
inductive TypeCForm where
  | rankAtLeastFour (parameter : HighRankParameter)
  | splitLowRank (parameter : SplitLowRankParameter)
  | splitSp6Two (prime : Sp6PrimeCase)
  | simpleSuzuki (parameter : SuzukiParameter)
  deriving DecidableEq, Repr

/-- The exhaustive structural alternatives used in the second half of the
proof of Proposition 3.9. -/
inductive StructuralCase where
  | primeOutsideOrder
  | typeA
  | typeC (form : TypeCForm)
  deriving DecidableEq, Repr

/-- The structural alternatives when the coefficient prime divides the group
order.  The outside-order case is deliberately unavailable. -/
inductive NoncoprimeStructuralCase where
  | typeA
  | typeC (form : TypeCForm)
  deriving DecidableEq, Repr

/-- Include a noncoprime structural case in the complete list. -/
def NoncoprimeStructuralCase.toStructuralCase :
    NoncoprimeStructuralCase → StructuralCase
  | .typeA => .typeA
  | .typeC form => .typeC form

@[simp]
theorem NoncoprimeStructuralCase.toStructuralCase_ne_primeOutsideOrder
    (groupCase : NoncoprimeStructuralCase) :
    groupCase.toStructuralCase ≠ .primeOutsideOrder := by
  cases groupCase <;> simp [NoncoprimeStructuralCase.toStructuralCase]

end ModularRep.PaperProofs.EvenFieldProposition39Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
