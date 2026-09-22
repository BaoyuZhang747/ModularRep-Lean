import ModularRep.PaperProofs.TypeBRankThreePrincipalBrauerOrbitBinding
import ModularRep.PaperProofs.TypeBRankThreePrincipalCoverOrbit

/-!
# The SO matching induced by the same principal Omega seed

The given equivariant Omega seed induces an equivalence from the actual
SO-orbit quotient of principal Omega Brauer characters to the specified
principal SO ordinary-weight fibre. Composing with the inverse of the
checked constituent-orbit equivalence constructs the SO correspondence.

The representative formula holds for every Omega character, for precisely
the input seed and the published literal covering map. Literal restriction
occurrence is then equivalent to literal DGN weight covering on matched
pairs. No overgroup matching, numerical count, pair triple, J relation or
goodness conclusion is supplied as an input.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalOvergroupMatching

open ModularRep CharacterWeight TypeBCliffordCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding TypeBRankThreePrincipalOrbitBinding
open TypeBRankThreePrincipalBrauerOrbitBinding TypeBRankThreePrincipalCoverOrbit
open TypeBGreenPrincipalConstituentSource NavarroCoveringBrauerExtension

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable (F : Type) [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2) (outside : delta ∉ G F)
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  [Fintype (OmegaWeight F S b)] [DecidableEq (SOWeight F SH bH)]
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)
  (seed : OmegaBrauer F root b ≃ OmegaWeight F S b)
  (seed_delta : ∀ theta,
    seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
      weightPermutation F S literal b hb delta indexTwo (seed theta))

/-- The same seed sends each actual Brauer orbit to one specified SO cover. -/
def orbitWeightMap :
    PrincipalBrauerOrbit F S literal root b hb → SOWeight F SH bH :=
  Quotient.lift (fun theta => covering.cover (seed theta)) (by
    intro theta eta related
    have forward :=
      (principalBrauerOrbitRel_iff F S literal root b hb theta eta).mp related
    obtain (heq | heq) :=
      (exists_brauerStep_iff F S literal root b hb delta indexTwo outside theta eta).mp forward
    · rw [heq]
    · rw [heq, seed_delta]
      exact (covering.cover_action (seed theta)).symm)

@[simp] theorem orbitWeightMap_mk (theta : OmegaBrauer F root b) :
    orbitWeightMap F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta (Quotient.mk _ theta) =
        covering.cover (seed theta) := rfl

theorem orbitWeightMap_injective :
    Function.Injective
      (orbitWeightMap F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta) := by
  intro x y
  refine Quotient.inductionOn₂ x y ?_
  intro theta eta equal
  have sameCover : covering.cover (seed theta) = covering.cover (seed eta) := equal
  have weights := (cover_eq_iff F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn covering (seed theta) (seed eta)).mp sameCover
  have characters : eta = theta ∨
      eta = brauerPermutation F S literal root b hb delta indexTwo theta := by
    rcases weights with heq | heq
    · exact Or.inl (seed.injective heq)
    · exact Or.inr (seed.injective (heq.trans (seed_delta theta).symm))
  apply Quotient.sound
  exact (principalBrauerOrbitRel_iff F S literal root b hb theta eta).mpr
    ((exists_brauerStep_iff F S literal root b hb delta indexTwo outside theta eta).mpr
      characters)

theorem orbitWeightMap_surjective :
    Function.Surjective
      (orbitWeightMap F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta) := by
  intro v
  obtain ⟨w, hw⟩ := covering.cover_surjective v
  obtain ⟨theta, htheta⟩ := seed.surjective w
  refine ⟨Quotient.mk _ theta, ?_⟩
  change covering.cover (seed theta) = v
  rw [htheta]
  exact hw

/-- This orbit equivalence needs the actual seed and covering fibres, but
no Green source, character count or assumed SO correspondence. -/
def orbitWeightEquiv :
    PrincipalBrauerOrbit F S literal root b hb ≃ SOWeight F SH bH :=
  Equiv.ofBijective
    (orbitWeightMap F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta)
    ⟨orbitWeightMap_injective F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta,
      orbitWeightMap_surjective F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta⟩

@[simp] theorem orbitWeightEquiv_mk (theta : OmegaBrauer F root b) :
    orbitWeightEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta (Quotient.mk _ theta) =
        covering.cover (seed theta) := rfl

include seed_delta in
/-- Fixed and free points retain their type under the original seed. -/
theorem seed_fixed_iff (theta : OmegaBrauer F root b) :
    brauerPermutation F S literal root b hb delta indexTwo theta = theta ↔
      weightPermutation F S literal b hb delta indexTwo (seed theta) = seed theta := by
  constructor
  · intro fixed
    exact (seed_delta theta).symm.trans (congrArg seed fixed)
  · intro fixed
    exact seed.injective ((seed_delta theta).trans fixed)

include seed_delta in
theorem seed_free_iff (theta : OmegaBrauer F root b) :
    brauerPermutation F S literal root b hb delta indexTwo theta ≠ theta ↔
      weightPermutation F S literal b hb delta indexTwo (seed theta) ≠ seed theta :=
  not_congr (seed_fixed_iff F S literal root b hb delta indexTwo seed seed_delta theta)

section Overgroup

variable (rootH : PrimeRegularRootEmbedding 2 k K (H F))
  (roots : RootAgreement (G F) rootH root)
  (fieldScope : SpathCoefficientField 2 k rootH.prime)
  (green : Green811Source (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (principalLift : PrincipalLiftSource (G F) rootH root roots fieldScope
    (quotient_isTwoGroup (G F) indexTwo))
  (clifford : Clifford85_87Source (G F) rootH root roots fieldScope)
  (principalRestriction : PrincipalRestrictionSource (G F) rootH root roots fieldScope)

/-- The principal SO correspondence constructed from this same Omega
seed, the original character restriction relation and specified covering. -/
def overgroupEquiv : SOBrauer F rootH bH ≃ SOWeight F SH bH :=
  (principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift clifford principalRestriction).symm.trans
    (orbitWeightEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta)

/-- Every actual Omega constituent is anchored to the cover of its image
under precisely the input seed. There is no new representative choice. -/
theorem overgroupEquiv_principalAbove (theta : OmegaBrauer F root b) :
    overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
      green principalLift clifford principalRestriction
      (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift theta) = covering.cover (seed theta) := by
  change orbitWeightEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta
      ((principalOrbitEquiv F S literal root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford principalRestriction).symm
        (principalAbove F root b hb rootH bH hbH roots fieldScope indexTwo
          green principalLift theta)) = _
  rw [← principalOrbitEquiv_mk F S literal root b hb rootH bH hbH roots fieldScope
    indexTwo green principalLift clifford principalRestriction theta,
    Equiv.symm_apply_apply]
  rfl

/-- The overgroup match retains the original literal restriction
occurrence relation, for every prescribed supported constituent. -/
theorem occurs_iff_overgroupEquiv_eq (Phi : SOBrauer F rootH bH)
    (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ↔
      overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
        SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
        green principalLift clifford principalRestriction Phi =
          covering.cover (seed theta) := by
  rw [principalAbove_occurs_iff F root b hb rootH bH hbH roots fieldScope indexTwo
    green principalLift theta Phi]
  constructor
  · intro equal
    rw [← equal]
    exact overgroupEquiv_principalAbove F S literal root b hb delta indexTwo outside
      parameters notThree SH literalH bH hbH dgn covering seed seed_delta
      rootH roots fieldScope green principalLift clifford principalRestriction theta
  · intro equal
    apply (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
      green principalLift clifford principalRestriction).injective
    exact (overgroupEquiv_principalAbove F S literal root b hb delta indexTwo outside
      parameters notThree SH literalH bH hbH dgn covering seed seed_delta
      rootH roots fieldScope green principalLift clifford principalRestriction theta).trans
        equal.symm

/-- On matched pairs, actual Brauer restriction occurrence is precisely
the specified DGN/local ordinary-character covering relation. -/
theorem occurs_iff_coversClass (Phi : SOBrauer F rootH bH)
    (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ↔
      TypeBWeightCoveringSource.CoversClass (G F) dgn
        (overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
          SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
          green principalLift clifford principalRestriction Phi).val (seed theta).val := by
  rw [covering.covers_iff]
  exact (occurs_iff_overgroupEquiv_eq F S literal root b hb delta indexTwo outside
    parameters notThree SH literalH bH hbH dgn covering seed seed_delta
    rootH roots fieldScope green principalLift clifford principalRestriction Phi theta).trans
      eq_comm

/-- The constructed SO correspondence has a literal constituent-cover
description. This statement is a deduction and supplies no pair triple. -/
theorem overgroupEquiv_eq_iff_exists_pair (Phi : SOBrauer F rootH bH)
    (v : SOWeight F SH bH) :
    overgroupEquiv F S literal root b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering seed seed_delta rootH roots fieldScope
      green principalLift clifford principalRestriction Phi = v ↔
        ∃ theta : OmegaBrauer F root b,
          BrauerOccursInRestriction (G F) rootH root Phi.val theta.val ∧
            TypeBWeightCoveringSource.CoversClass (G F) dgn v.val (seed theta).val := by
  constructor
  · intro equal
    obtain ⟨theta, aboveEqual⟩ :=
      principalAbove_surjective F root b hb rootH bH hbH roots fieldScope indexTwo
        green principalLift clifford principalRestriction Phi
    have occurs := (principalAbove_occurs_iff F root b hb rootH bH hbH roots fieldScope
      indexTwo green principalLift theta Phi).mpr aboveEqual
    refine ⟨theta, occurs, ?_⟩
    rw [← equal]
    exact (occurs_iff_coversClass F S literal root b hb delta indexTwo outside
      parameters notThree SH literalH bH hbH dgn covering seed seed_delta
      rootH roots fieldScope green principalLift clifford principalRestriction Phi theta).mp occurs
  · rintro ⟨theta, occurs, covers⟩
    have matched := (occurs_iff_overgroupEquiv_eq F S literal root b hb delta indexTwo outside
      parameters notThree SH literalH bH hbH dgn covering seed seed_delta
      rootH roots fieldScope green principalLift clifford principalRestriction Phi theta).mp occurs
    exact matched.trans ((covering.covers_iff v (seed theta)).mp covers)

end Overgroup

end ModularRep.PaperProofs.TypeBRankThreePrincipalOvergroupMatching


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
