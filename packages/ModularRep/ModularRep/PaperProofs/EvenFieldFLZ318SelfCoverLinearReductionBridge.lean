import ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII

/-!
# Ordinary-to-modular linear character reduction in the self-cover

Feng--Li--Zhang, Theorem 3.18(iii), uses the ordinary group
`Lin_{ell'}(G_tilde / G)`, whereas the project's tensor action is expressed
using modular linear characters.  In the self-cover specialisation
`G_tilde = G = H`, both literal homomorphism carriers are trivial.  This file
constructs the unique reduction homomorphism between the characteristic-zero
and modular carriers used in the project and proves that:

* both carriers are singletons;
* the reduction agrees with the inverse of the chosen prime regular root
  correspondence on every value;
* it commutes with the field action; and
* it is compatible with the canonical descriptions by characters of `H / H`.

The remaining source-semantic bridge is the identification of these literal
homomorphism carriers and actions with the exact `Lin_{ell'}` and `LinBr`
carriers in the cited theorem.  This file does not define or prove the DGN
covering relation, the `Delta` correspondence, any clause of that theorem, or
BAW-goodness.
-/

noncomputable section

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverLinearReductionBridge

open ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverEqualGroupClauseIII

universe u

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K]
variable [Group H] [Finite H] [Group E]

/-- The literal modular-homomorphism carrier used by the project for linear
Brauer characters of the self-cover quotient `H / H`.  Its identification
with the exact source carrier `LinBr(H / H)` remains a source adapter. -/
abbrev SelfCoverLinearBrauerCharacters (p : ℕ) [CharP k p] :=
  linearCharactersTrivialOn (k := k) (⊤ : Subgroup H)

/-- Ordinary linear characters of the literal quotient `H / H`, with the
characteristic-zero coefficient hypothesis retained in the public type. -/
abbrev SelfCoverQuotientOrdinaryLinearCharacters [CharZero K] :=
  H ⧸ (⊤ : Subgroup H) →* Kˣ

/-- Modular linear characters of the literal quotient `H / H`, with the
coefficient characteristic retained in the public type. -/
abbrev SelfCoverQuotientLinearBrauerCharacters (p : ℕ) [CharP k p] :=
  H ⧸ (⊤ : Subgroup H) →* kˣ

variable [CharP k p] [CharZero K]

/-- Canonical passage from modular linear characters trivial on `H` to
modular linear characters of the literal quotient `H / H`. -/
def selfCoverLinearBrauerCharactersEquiv :
    SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H) ≃*
      SelfCoverQuotientLinearBrauerCharacters (p := p) (k := k) (H := H) :=
  LinearCharactersTrivialOn.quotientMulEquiv
    (k := k) (⊤ : Subgroup H)

/-- Every modular linear character of the self-cover quotient is trivial. -/
theorem selfCoverLinearBrauerCharacter_eq_one
    (lambda : SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H)) :
    lambda = 1 := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro h
  exact lambda.2 (Subgroup.mem_top h)

/-- The set of modular linear characters of `H / H` is a singleton. -/
instance selfCoverLinearBrauerCharacters_subsingleton :
    Subsingleton (SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H)) where
  allEq lambda mu := by
    rw [selfCoverLinearBrauerCharacter_eq_one lambda,
      selfCoverLinearBrauerCharacter_eq_one mu]

/-- Both literal sets of linear characters for the self-cover consist only of their
identity characters. -/
theorem selfCoverLinearCharacterCarriers_eq_one :
    (∀ lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H),
      lambda = 1) ∧
    (∀ mu : SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H),
      mu = 1) := by
  exact ⟨selfCoverOrdinaryQuotientLinearCharacter_eq_one,
    selfCoverLinearBrauerCharacter_eq_one⟩

/-- The value of a self-cover ordinary linear character, packaged as a root
of unity of the exponent used by the chosen Brauer root correspondence. -/
def selfCoverOrdinaryLinearCharacterRoot
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H))
    (h : H) : rootsOfUnity (primeRegularExponent p H) K := by
  letI : NeZero (primeRegularExponent p H) :=
    ⟨(primeRegularExponent_pos p H).ne'⟩
  apply rootsOfUnity.mkOfPowEq (lambda.1 h : K)
  have hlambda : lambda.1 h = 1 := lambda.2 (Subgroup.mem_top h)
  rw [hlambda]
  simp

@[simp]
theorem selfCoverOrdinaryLinearCharacterRoot_eq_one
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H))
    (h : H) :
    selfCoverOrdinaryLinearCharacterRoot (p := p) lambda h = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (lambda.1 h : K) = 1
  exact congrArg Units.val (lambda.2 (Subgroup.mem_top h))

/-- The unique ordinary-to-modular reduction homomorphism on the sets of linear characters
for the self-cover.  The root formula below verifies that this unique
map is the reduction determined by the chosen root correspondence. -/
def selfCoverOrdinaryToBrauerReduction
    (_iota : PrimeRegularRootEmbedding p k K H) :
    SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H) →*
      SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H) where
  toFun := fun _ ↦ 1
  map_one' := rfl
  map_mul' := fun _ _ ↦ (one_mul 1).symm

@[simp]
theorem selfCoverOrdinaryToBrauerReduction_eq_one
    (iota : PrimeRegularRootEmbedding p k K H)
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) :
    selfCoverOrdinaryToBrauerReduction iota lambda = 1 :=
  rfl

/-- On every element of `H`, the modular value selected by reduction is the
inverse-root-correspondence image of the ordinary value. -/
theorem selfCoverOrdinaryToBrauerReduction_root_formula
    (iota : PrimeRegularRootEmbedding p k K H)
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H))
    (h : H) :
    (selfCoverOrdinaryToBrauerReduction iota lambda).1 h =
      ((iota.toMulEquiv.symm
        (selfCoverOrdinaryLinearCharacterRoot (p := p) lambda h) :
          rootsOfUnity (primeRegularExponent p H) k) : kˣ) := by
  rw [selfCoverOrdinaryLinearCharacterRoot_eq_one]
  simp

/-- Lifting the reduced modular value recovers the ordinary value. -/
theorem selfCoverOrdinaryToBrauerReduction_lift_formula
    (iota : PrimeRegularRootEmbedding p k K H)
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H))
    (h : PrimeRegularElement (G := H) p) :
    iota.liftRoot
        (iota.linearCharacterRoot
          (selfCoverOrdinaryToBrauerReduction iota lambda).1
          h) =
      (lambda.1 h.1 : K) := by
  have hroot : iota.linearCharacterRoot
      (selfCoverOrdinaryToBrauerReduction iota lambda).1 h = 1 := by
    apply Subtype.ext
    apply Units.ext
    rfl
  rw [hroot]
  change ((((iota.toMulEquiv 1 :
    rootsOfUnity (primeRegularExponent p H) K) : Kˣ) : K)) =
      (lambda.1 h.1 : K)
  rw [map_one]
  change 1 = (lambda.1 h.1 : K)
  exact (congrArg Units.val (lambda.2 (Subgroup.mem_top h.1))).symm

/-- Restriction of a literal ordinary self-cover linear character to the
prime regular elements. -/
def selfCoverOrdinaryPrimeRegularRestriction
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) :
    PrimeRegularClassFunction K H p where
  toFun h := (lambda.1 h.1 : K)
  map_conj x h := by
    change (lambda.1 (x * h.1 * x⁻¹) : K) = (lambda.1 h.1 : K)
    have hleft : lambda.1 (x * h.1 * x⁻¹) = 1 :=
      lambda.2 (Subgroup.mem_top _)
    have hright : lambda.1 h.1 = 1 :=
      lambda.2 (Subgroup.mem_top _)
    rw [hleft, hright]

/-- As prime regular class functions, lifting the reduced modular linear
character recovers the restriction of the ordinary linear character. -/
theorem selfCoverOrdinaryToBrauerReduction_liftedCharacter
    (iota : PrimeRegularRootEmbedding p k K H)
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) :
    iota.liftedLinearCharacter
        (selfCoverOrdinaryToBrauerReduction iota lambda).1 =
      selfCoverOrdinaryPrimeRegularRestriction (p := p) lambda := by
  ext h
  exact selfCoverOrdinaryToBrauerReduction_lift_formula iota lambda h

/-- The reduction map is bijective because both self-cover carriers are
singletons. -/
def selfCoverOrdinaryToBrauerReductionEquiv
    (iota : PrimeRegularRootEmbedding p k K H) :
    SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H) ≃*
      SelfCoverLinearBrauerCharacters (p := p) (k := k) (H := H) where
  toFun := selfCoverOrdinaryToBrauerReduction iota
  invFun := fun _ ↦ 1
  left_inv := fun _lambda ↦ Subsingleton.elim _ _
  right_inv := fun _lambda ↦ Subsingleton.elim _ _
  map_mul' := map_mul (selfCoverOrdinaryToBrauerReduction iota)

/-- The top subgroup is stable under every field automorphism. -/
theorem selfCoverTop_isFieldStable
    (field : E →* MulAut H) :
    LinearCharactersTrivialOn.IsFieldStable (⊤ : Subgroup H) field := by
  intro _ _ _
  exact Subgroup.mem_top _

/-- Reduction commutes with field transport on the literal ordinary and
modular self-cover carriers. -/
theorem selfCoverOrdinaryToBrauerReduction_field_equivariant
    (iota : PrimeRegularRootEmbedding p k K H)
    (field : E →* MulAut H) (e : E)
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) :
    selfCoverOrdinaryToBrauerReduction iota
        (LinearCharactersTrivialOn.fieldAction (k := K) field
          (selfCoverTop_isFieldStable field) e lambda) =
      LinearCharactersTrivialOn.fieldAction (k := k) field
        (selfCoverTop_isFieldStable field) e
        (selfCoverOrdinaryToBrauerReduction iota lambda) := by
  exact Subsingleton.elim _ _

/-- The unique reduction homomorphism between the literal ordinary and
modular linear character groups of the quotient `H / H`. -/
def selfCoverQuotientOrdinaryToBrauerReduction
    (_iota : PrimeRegularRootEmbedding p k K H) :
    SelfCoverQuotientOrdinaryLinearCharacters (K := K) (H := H) →*
      SelfCoverQuotientLinearBrauerCharacters (p := p) (k := k) (H := H) where
  toFun := fun _ ↦ 1
  map_one' := rfl
  map_mul' := fun _ _ ↦ by
    ext q
    simp

/-- The reduction of linear characters commutes with the two canonical
descriptions as characters of the quotient `H / H`. -/
theorem selfCoverOrdinaryToBrauerReduction_quotient_square
    (iota : PrimeRegularRootEmbedding p k K H)
    (lambda : SelfCoverOrdinaryQuotientLinearCharacters (K := K) (H := H)) :
    selfCoverLinearBrauerCharactersEquiv
        (selfCoverOrdinaryToBrauerReduction iota lambda) =
      selfCoverQuotientOrdinaryToBrauerReduction iota
        (selfCoverOrdinaryQuotientLinearCharactersEquiv lambda) := by
  apply MonoidHom.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ h =>
      change (selfCoverOrdinaryToBrauerReduction iota lambda).1 h = 1
      rfl

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCoverLinearReductionBridge


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
