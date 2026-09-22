import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import ModularRep.PaperProofs.TypeBCliffordOrthogonalFullFieldBinding
import ModularRep.PaperProofs.TypeBFixedRootDefinitionFamily

/-!
# Prime Frobenius on the literal principal SO and Omega weight fibres

The sole new published input is the generator specialization of FYZ,
Corollary 3.63: principal ordinary weight conjugacy classes of SO and Omega
are fixed by coordinate prime Frobenius. Both clauses keep the actual
specified block assignments, principal idempotents, modular roots and their
guarded local block interpretations. Their published-source realization
is explicit U; no inhabitant of the certificate is constructed here.

The existing full field actions are powers of that same coordinate
Frobenius. The all-element fixation statements are deductions. They do
not assert fixation of a chosen raw weight, a Brauer character, or a
character-to-weight correspondence.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldBinding

open ModularRep CharacterWeight
open TypeBCliffordCarriers TypeBOrthogonalOmegaCarriers
open TypeBOrthogonalFieldAutomorphism TypeBCliffordOrthogonalSourceBinding
open TypeBCliffordOrthogonalAmbientQuotient TypeBCliffordOrthogonalFullFieldBinding
open TypeBCentralKernelBlockSource TypeBFixedRootDefinitionFamily
open TypeBRankThreePrincipalCountBinding

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-- Fixedness of one actual ordinary weight class is preserved under
nonnegative powers of the same group automorphism. -/
theorem rightTwist_pow_fixed
    {ell : ℕ} {K X : Type} [Field K] [CharZero K] [Group X] [Finite X]
    (alpha : MulAut X)
    (w : CharacterWeight.ConjugacyClass (p := ell) (K := K) (G := X))
    (fixed : CharacterWeight.rightTwistConjugacyClass alpha w = w)
    (m : ℕ) : CharacterWeight.rightTwistConjugacyClass (alpha ^ m) w = w := by
  induction m with
  | zero =>
      simpa only [pow_zero] using CharacterWeight.rightTwistConjugacyClass_one w
  | succ m ih =>
      calc
        CharacterWeight.rightTwistConjugacyClass (alpha ^ (m + 1)) w =
            CharacterWeight.rightTwistConjugacyClass alpha
              (CharacterWeight.rightTwistConjugacyClass (alpha ^ m) w) := by
          simpa only [pow_succ] using
            (CharacterWeight.rightTwistConjugacyClass_mul w (alpha ^ m) alpha).symm
        _ = w := (congrArg (CharacterWeight.rightTwistConjugacyClass alpha) ih).trans fixed

/-- E2/U: FYZ Corollary 3.63, author TeX `cor:act-field-cla`,
lines 2281--2294; the actor is entrywise defining-prime Frobenius from
lines 2258--2259 and Alp is the ordinary weight CLASS carrier at 389--392.

The source is specialized to both literal dimension-seven groups. The
root guards and literal catalogue identities retain their specified source
interpretation. The ordinary coefficient field is explicitly algebraically
closed; its realization of the published ordinary character values remains
U. No rank-three exception, cover, matching, or DGN covariance is assumed.
-/
structure FYZCorollary363Source
    (F : Type) [Field F] [Finite F] (r f : ℕ) [CharP F r]
    (parameters : OddFieldParameters F r f)
    {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    [ordinarySplitting : IsAlgClosed K]
    (root : PrimeRegularRootEmbedding 2 k K (G F))
    (rootH : PrimeRegularRootEmbedding 2 k K (H F))
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

section FullField

variable {F : Type} [Field F] [Finite F] {r f : ℕ} [CharP F r]
    {parameters : OddFieldParameters F r f}
    {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    [IsAlgClosed K]
    {root : PrimeRegularRootEmbedding 2 k K (G F)}
    {rootH : PrimeRegularRootEmbedding 2 k K (H F)}
    {S : OmegaWeightSource (k := k) (K := K) F}
    {SH : SOWeightSource (k := k) (K := K) F}
    {literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val}
    {literalH : ∀ b, SH.operations.ambientBlockData.blockIdempotent b = b.val}
    {guard : GuardedBlockCompatibility root S.operations}
    {guardH : GuardedBlockCompatibility rootH SH.operations}
    {b : LiteralPrimitiveBlock k (G F)} {hb : IsPrincipal b}
    {bH : LiteralPrimitiveBlock k (H F)} {hbH : IsPrincipal bH}
    (source : FYZCorollary363Source F r f parameters root rootH S SH
      literal literalH guard guardH b hb bH hbH)
    {N : NormSource 3 F}
    (fieldSource : FieldActionSource 3 F r f parameters N)
    (rank : 3 ≤ 3)
    (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters rank N)

include source in
/-- The actual full Omega field action fixes each principal ordinary weight
class; the distinguished generator is not replaced by a new actor. -/
theorem omega_field_fixed (e : FieldGroup f) (w : OmegaWeight F S b) :
    CharacterWeight.rightTwistConjugacyClass
      (omegaFieldAction fieldSource rank C e) w.val = w.val := by
  rw [omegaFieldAction_eq_prime_pow fieldSource rank C e]
  exact rightTwist_pow_fixed
    (primeFrobeniusOmega 3 F r parameters.prime) w.val
    (source.omega_generator w) e.toAdd.val

include source in
/-- The same promotion for the literal SO principal ordinary weight fibre. -/
theorem so_field_fixed (e : FieldGroup f) (v : SOWeight F SH bH) :
    CharacterWeight.rightTwistConjugacyClass
      (soFieldAction 3 F parameters rank N C fieldSource e) v.val = v.val := by
  rw [soFieldAction_eq_prime_pow fieldSource rank C e]
  exact rightTwist_pow_fixed
    (primeFrobeniusSpecialOrthogonal 3 F r parameters.prime) v.val
    (source.so_generator v) e.toAdd.val

include source in
/-- The inverse-actor convention used by the existing left action encoding
the manuscript's right automorphism action. -/
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

end ModularRep.PaperProofs.TypeBRankThreePrincipalWeightFieldBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
