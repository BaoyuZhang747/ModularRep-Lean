import ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldBinding
import ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding

/-!
# Principal ordinary weight classes over the same splitting modular system

FYZ Corollary 3.63 fixes the principal two-block weight conjugacy classes
of SO and Omega under coordinate defining-prime Frobenius. Its ordinary
character interpretation here uses sufficient roots for the actual SO
order in the current fraction field. The same modular system fixes both
Brauer conventions and both specified local block guards.

The only published conclusions stored below are the two ordinary weight
class generator clauses. The full positive and inverse field statements
reuse the existing actual prime-Frobenius power equations. No chosen raw
representative, Brauer fixation or correspondence is a source field.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldSplitting

open ModularRep CharacterWeight
open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBOrthogonalFieldAutomorphism TypeBCliffordOrthogonalSourceBinding
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalFullFieldBinding
open TypeBCentralKernelBlockSource TypeBFixedRootDefinitionFamily
open TypeBRankThreePrincipalCountBinding
open TypeBModularGroupRootBinding TypeBLocalPhysicalBlockBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- Sufficient ordinary roots restrict from actual SO to its derived subgroup. -/
def omegaOrdinaryRoots (F K : Type) [Field F] [Finite F] [Field K]
    [HasEnoughRootsOfUnity K (Nat.card (H F))] :
    HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  HasEnoughRootsOfUnity.of_dvd K (Subgroup.card_subgroup_dvd_card (G F))

/-- FYZ Corollary 3.63 on the literal principal weight fibres, with its
ordinary values interpreted over the same sufficient splitting system.
The actual root equations and local specified interpretations precede the
two published ordinary class conclusions. -/
structure FYZCorollary363SplittingSource
    (F : Type) [Field F] [Finite F] (r f : ℕ) [CharP F r]
    (parameters : OddFieldParameters F r f)
    {k K O : Type}
    [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
    [CharP k 2] [IsAlgClosed k] [CharZero K]
    (Msys : ModularSystem 2 K O k)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (H F))]
    (coefficient : SpathCoefficientField 2 k Msys.prime)
    (root : PrimeRegularRootEmbedding 2 k K (G F))
    (rootH : PrimeRegularRootEmbedding 2 k K (H F))
    (root_eq : root = groupRoot Msys (G F))
    (rootH_eq : rootH = groupRoot Msys (H F))
    (S : OmegaWeightSource (k := k) (K := K) F)
    (SH : SOWeightSource (k := k) (K := K) F)
    (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
    (literalH : ∀ b, SH.operations.ambientBlockData.blockIdempotent b = b.val)
    (guard : GuardedBlockCompatibility root S.operations)
    (guardH : GuardedBlockCompatibility rootH SH.operations)
    (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
    (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH) : Prop where
  omega_generator : ∀ w : OmegaWeight F S b,
    CharacterWeight.rightTwistConjugacyClass
      (primeFrobeniusOmega 3 F r parameters.prime) w.val = w.val
  so_generator : ∀ v : SOWeight F SH bH,
    CharacterWeight.rightTwistConjugacyClass
      (primeFrobeniusSpecialOrthogonal 3 F r parameters.prime) v.val = v.val

section Physical

variable {F : Type} [Field F] [Finite F]
  {k K O : Type}
  [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
  [CharP k 2] [IsAlgClosed k] [CharZero K]
  (Msys : ModularSystem 2 K O k)
  [HasEnoughRootsOfUnity K (Nat.card (H F))]

local instance omegaRoots : HasEnoughRootsOfUnity K (Nat.card (G F)) :=
  omegaOrdinaryRoots F K

variable
  (expansion : ∀ (T : Type) [Group T] [Finite T]
    [HasEnoughRootsOfUnity K (Nat.card T)],
      ScopedDecompositionExpansionSource (H := T) Msys)

/-- The Omega local guard is derived on the same prescribed root and operations. -/
def omega_blockCompatibility
    (root : PrimeRegularRootEmbedding 2 k K (G F))
    (root_eq : root = groupRoot Msys (G F))
    (S : OmegaWeightSource (k := k) (K := K) F)
    (ordinary : ∀ Q : Subgroup (G F), NormalizerOrdinarySource Msys S.operations Q)
    (membership : OrdinaryInflationMembership Msys S.operations ordinary) :
    GuardedBlockCompatibility root S.operations := by
  apply guardedBlockCompatibility Msys S.operations root _ expansion ordinary membership
  rw [root_eq]
  exact groupRoot_residue Msys (G F)

/-- SO has its own ordinary inflation input and independently derived guard. -/
def so_blockCompatibility
    (rootH : PrimeRegularRootEmbedding 2 k K (H F))
    (rootH_eq : rootH = groupRoot Msys (H F))
    (SH : SOWeightSource (k := k) (K := K) F)
    (ordinary : ∀ Q : Subgroup (H F), NormalizerOrdinarySource Msys SH.operations Q)
    (membership : OrdinaryInflationMembership Msys SH.operations ordinary) :
    GuardedBlockCompatibility rootH SH.operations := by
  apply guardedBlockCompatibility Msys SH.operations rootH _ expansion ordinary membership
  rw [rootH_eq]
  exact groupRoot_residue Msys (H F)

end Physical

section FullField

variable {F : Type} [Field F] [Finite F] {r f : ℕ} [CharP F r]
    {parameters : OddFieldParameters F r f}
    {k K O : Type}
    [Field k] [Field K] [CommRing O] [IsDomain O] [Algebra O K]
    [CharP k 2] [IsAlgClosed k] [CharZero K]
    {Msys : ModularSystem 2 K O k}
    [HasEnoughRootsOfUnity K (Nat.card (H F))]
    {coefficient : SpathCoefficientField 2 k Msys.prime}
    {root : PrimeRegularRootEmbedding 2 k K (G F)}
    {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
    {root_eq : root = groupRoot Msys (G F)}
    {rootH_eq : rootH = groupRoot Msys (H F)}
    {S : OmegaWeightSource (k := k) (K := K) F}
    {SH : SOWeightSource (k := k) (K := K) F}
    {literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val}
    {literalH : ∀ b, SH.operations.ambientBlockData.blockIdempotent b = b.val}
    {guard : GuardedBlockCompatibility root S.operations}
    {guardH : GuardedBlockCompatibility rootH SH.operations}
    {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
    {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
    (source : FYZCorollary363SplittingSource F r f parameters Msys coefficient
      root rootH root_eq rootH_eq S SH literal literalH guard guardH b hb bH hbH)
    {N : NormSource 3 F}
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (rank : 3 ≤ 3)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters rank N)

include source in
/-- The actual positive Omega field actor is a power of the fixed generator. -/
theorem omega_field_fixed (e : FieldGroup f) (w : OmegaWeight F S b) :
    CharacterWeight.rightTwistConjugacyClass
      (omegaFieldAction fieldSource rank C e) w.val = w.val := by
  rw [omegaFieldAction_eq_prime_pow fieldSource rank C e]
  exact TypeBRankThreePrincipalWeightFieldBinding.rightTwist_pow_fixed
    (primeFrobeniusOmega 3 F r parameters.prime) w.val
    (source.omega_generator w) e.toAdd.val

include source in
/-- The same promotion applies to the actual positive SO field actor. -/
theorem so_field_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    CharacterWeight.rightTwistConjugacyClass
      (soFieldAction 3 F parameters rank N C fieldSource e) v.val = v.val := by
  rw [soFieldAction_eq_prime_pow fieldSource rank C e]
  exact TypeBRankThreePrincipalWeightFieldBinding.rightTwist_pow_fixed
    (primeFrobeniusSpecialOrthogonal 3 F r parameters.prime) v.val
    (source.so_generator v) e.toAdd.val

include source in
/-- Inverse actors use the inverse element of the same full field group. -/
theorem omega_inverse_field_fixed (e : FieldGroup f) (w : OmegaWeight F S b) :
    CharacterWeight.rightTwistConjugacyClass
      (omegaFieldAction fieldSource rank C e⁻¹) w.val = w.val :=
  omega_field_fixed source fieldSource rank C e⁻¹ w

include source in
theorem so_inverse_field_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    CharacterWeight.rightTwistConjugacyClass
      (soFieldAction 3 F parameters rank N C fieldSource e⁻¹) v.val = v.val :=
  so_field_fixed source fieldSource rank C e⁻¹ v

end FullField

end ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
