import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import ModularRep.PaperProofs.TypeBCharacteristicTwoConstituentSource

/-!
# Actual SO orbits of the rank-three principal fibres

An element of SO acts on either literal principal fibre as the identity or
as the fixed nontrivial coset representative. This follows from the actual
index-two inclusion and inner fixation. Literal Brauer restriction
occurrence and the published specified weight cover are constant along
these orbits. The checked C2 seed consequently respects the full SO action.

No character triple, final orientation, all-pairs J relation, new source
certificate or chosen character-to-weight correspondence is introduced.
The seed arguments below refer to the already constructed C2 map and make
only elementary transport deductions about it.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitBinding

open ModularRep CharacterWeight
open TypeBCliffordCarriers TypeBCentralKernelCarriers
open TypeBCentralKernelBlockSource TypeBCentralKernelInertia
open TypeBRankThreePrincipalCountBinding
open NavarroCoveringBrauerExtension TypeBCharacteristicTwoConstituentSource

variable (F : Type) [Field F] [Finite F]

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2) (outside : delta ∉ G F)

include indexTwo outside in
/-- Two elements in the nontrivial coset differ by an actual Omega element. -/
theorem mul_delta_inv_mem (h : H F) (hh : h ∉ G F) : h * delta⁻¹ ∈ G F := by
  apply (Subgroup.mul_mem_iff_of_index_two indexTwo).mpr
  simp only [Subgroup.inv_mem_iff, hh, outside]

theorem brauerStep_eq_of_mem (h : H F) (hh : h ∈ G F)
    (theta : OmegaBrauer F root b) : brauerStep F S literal root b hb h theta = theta := by
  apply Subtype.ext
  exact G_le_T (G F) root theta.val hh

include outside in
theorem brauerStep_eq_delta_of_notMem (h : H F) (hh : h ∉ G F)
    (theta : OmegaBrauer F root b) :
    brauerStep F S literal root b hb h theta =
      brauerPermutation F S literal root b hb delta indexTwo theta := by
  apply Subtype.ext
  change conjugationOp (G F) h • theta.val = conjugationOp (G F) delta • theta.val
  have factor : h = (h * delta⁻¹) * delta := by simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [factor, map_mul, mul_smul]
  exact G_le_T (G F) root (conjugationOp (G F) delta • theta.val)
    (mul_delta_inv_mem F delta indexTwo outside h hh)

theorem weightStep_eq_of_mem (h : H F) (hh : h ∈ G F) (w : OmegaWeight F S b) :
    weightStep F S literal b hb h w = w := by
  apply Subtype.ext
  exact inner_fixes_weightClass F ⟨h, hh⟩ w.val

include outside in
theorem weightStep_eq_delta_of_notMem (h : H F) (hh : h ∉ G F)
    (w : OmegaWeight F S b) :
    weightStep F S literal b hb h w = weightPermutation F S literal b hb delta indexTwo w := by
  apply Subtype.ext
  change conjugationOp (G F) h • w.val = conjugationOp (G F) delta • w.val
  have factor : h = (h * delta⁻¹) * delta := by simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [factor, map_mul, mul_smul]
  exact inner_fixes_weightClass F
    ⟨h * delta⁻¹, mul_delta_inv_mem F delta indexTwo outside h hh⟩
    (conjugationOp (G F) delta • w.val)

include outside in
/-- An actual SO-conjugate in the supported fibre is precisely one of its
two C2 orbit points. The fixed-point case is allowed. -/
theorem exists_brauerStep_iff (theta theta' : OmegaBrauer F root b) :
    (∃ h : H F, brauerStep F S literal root b hb h theta = theta') ↔
      theta' = theta ∨ theta' = brauerPermutation F S literal root b hb delta indexTwo theta := by
  constructor
  · rintro ⟨h, rfl⟩
    by_cases hh : h ∈ G F
    · exact Or.inl (brauerStep_eq_of_mem F S literal root b hb h hh theta)
    · exact Or.inr (brauerStep_eq_delta_of_notMem F S literal root b hb
        delta indexTwo outside h hh theta)
  · rintro (heq | heq)
    · exact ⟨1, (brauerStep_eq_of_mem F S literal root b hb 1 (G F).one_mem theta).trans
        heq.symm⟩
    · exact ⟨delta, heq.symm⟩

include outside in
theorem exists_weightStep_iff (w w' : OmegaWeight F S b) :
    (∃ h : H F, weightStep F S literal b hb h w = w') ↔
      w' = w ∨ w' = weightPermutation F S literal b hb delta indexTwo w := by
  constructor
  · rintro ⟨h, rfl⟩
    by_cases hh : h ∈ G F
    · exact Or.inl (weightStep_eq_of_mem F S literal b hb h hh w)
    · exact Or.inr (weightStep_eq_delta_of_notMem F S literal b hb
        delta indexTwo outside h hh w)
  · rintro (heq | heq)
    · exact ⟨1, (weightStep_eq_of_mem F S literal b hb 1 (G F).one_mem w).trans heq.symm⟩
    · exact ⟨delta, heq.symm⟩

theorem brauerStep_inv (h : H F) (theta : OmegaBrauer F root b) :
    brauerStep F S literal root b hb h⁻¹ (brauerStep F S literal root b hb h theta) =
      theta := by
  apply Subtype.ext
  change conjugationOp (G F) h⁻¹ • (conjugationOp (G F) h • theta.val) = theta.val
  rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]

section ConstituentFibres

variable (rootH : PrimeRegularRootEmbedding 2 k K (H F))

/-- Conjugating an actual constituent leaves its SO character unchanged.
This is the existing finite-expansion naturality theorem, specialized to
the actual inclusion and inner conjugation; no Clifford source is needed. -/
theorem occurs_brauerStep (h : H F) (Phi : IBr rootH)
    (theta : OmegaBrauer F root b)
    (occurs : BrauerOccursInRestriction (G F) rootH root Phi theta.val) :
    BrauerOccursInRestriction (G F) rootH root Phi
      (brauerStep F S literal root b hb h theta).val := by
  have transported := occursInRestriction_twist (G F) rootH root
    (MulAut.conj h⁻¹) (originalAction (G F) h⁻¹) (fun _ => rfl)
    Phi theta.val occurs
  have fixed : IrreducibleBrauerCharacter.twist rootH Phi (MulAut.conj h⁻¹) = Phi := by
    apply IrreducibleBrauerCharacter.twist_eq_self_of_underlying
    exact PrimeRegularClassFunction.twist_conj Phi.val h⁻¹
  exact fixed ▸ transported

theorem occurs_brauerStep_iff (h : H F) (Phi : IBr rootH)
    (theta : OmegaBrauer F root b) :
    BrauerOccursInRestriction (G F) rootH root Phi
        (brauerStep F S literal root b hb h theta).val ↔
      BrauerOccursInRestriction (G F) rootH root Phi theta.val := by
  constructor
  · intro occurs
    have back := occurs_brauerStep F S literal root b hb rootH h⁻¹ Phi
      (brauerStep F S literal root b hb h theta) occurs
    have undo := congrArg Subtype.val (brauerStep_inv F S literal root b hb h theta)
    exact undo ▸ back
  · exact occurs_brauerStep F S literal root b hb rootH h Phi theta

/-- Same actual H-orbit gives exactly the same SO constituent fibre,
including after restricting the overgroup character to its principal block. -/
theorem sameOrbit_occurs_iff (theta theta' : OmegaBrauer F root b)
    (sameOrbit : ∃ h : H F, brauerStep F S literal root b hb h theta = theta')
    (Phi : IBr rootH) :
    BrauerOccursInRestriction (G F) rootH root Phi theta'.val ↔
      BrauerOccursInRestriction (G F) rootH root Phi theta.val := by
  obtain ⟨h, rfl⟩ := sameOrbit
  exact occurs_brauerStep_iff F S literal root b hb rootH h Phi theta

end ConstituentFibres

section Seed

variable (seed : OmegaBrauer F root b ≃ OmegaWeight F S b)
  (seed_delta : ∀ theta,
    seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
      weightPermutation F S literal b hb delta indexTwo (seed theta))

include outside seed_delta in
/-- The checked C2 seed automatically respects every actual SO actor.
This is a property of a supplied already checked seed, not a source packet. -/
theorem seed_H_equivariant (h : H F) (theta : OmegaBrauer F root b) :
    seed (brauerStep F S literal root b hb h theta) =
      weightStep F S literal b hb h (seed theta) := by
  by_cases hh : h ∈ G F
  · rw [brauerStep_eq_of_mem F S literal root b hb h hh theta,
      weightStep_eq_of_mem F S literal b hb h hh (seed theta)]
  · rw [brauerStep_eq_delta_of_notMem F S literal root b hb delta indexTwo outside h hh theta,
      weightStep_eq_delta_of_notMem F S literal b hb delta indexTwo outside h hh (seed theta)]
    exact seed_delta theta

include outside seed_delta in
/-- Matched characters and weight classes have the same actual H-stabilizer
membership. This concerns only matched pairs; it is not an all-pairs J claim. -/
theorem seed_stabilizer_iff (h : H F) (theta : OmegaBrauer F root b) :
    conjugationOp (G F) h • (seed theta).val = (seed theta).val ↔
      conjugationOp (G F) h • theta.val = theta.val := by
  have natural := seed_H_equivariant F S literal root b hb delta indexTwo outside
    seed seed_delta h theta
  constructor
  · intro fixed
    have fixedFibre : weightStep F S literal b hb h (seed theta) = seed theta :=
      Subtype.ext fixed
    exact congrArg Subtype.val (seed.injective (natural.trans fixedFibre))
  · intro fixed
    have fixedFibre : brauerStep F S literal root b hb h theta = theta := Subtype.ext fixed
    exact congrArg Subtype.val ((natural.symm.trans (congrArg seed fixedFibre)))

end Seed

section Covers

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (bH : LiteralPrimitiveBlock k (H F)) (hbH : IsPrincipal bH)
  [Fintype (OmegaWeight F S b)] [DecidableEq (OmegaWeight F S b)]
  [Fintype (SOWeight F SH bH)] [DecidableEq (SOWeight F SH bH)]
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)

include covering in
theorem cover_weightStep (h : H F) (w : OmegaWeight F S b) :
    covering.cover (weightStep F S literal b hb h w) = covering.cover w := by
  by_cases hh : h ∈ G F
  · rw [weightStep_eq_of_mem F S literal b hb h hh w]
  · rw [weightStep_eq_delta_of_notMem F S literal b hb delta indexTwo outside h hh w]
    exact covering.cover_action w

include covering in
theorem covers_weightStep_iff (h : H F) (v : SOWeight F SH bH) (w : OmegaWeight F S b) :
    TypeBWeightCoveringSource.CoversClass (G F) dgn v.val
        (weightStep F S literal b hb h w).val ↔
      TypeBWeightCoveringSource.CoversClass (G F) dgn v.val w.val := by
  rw [covering.covers_iff, covering.covers_iff,
    cover_weightStep F S literal b hb delta indexTwo outside parameters notThree
      SH literalH bH hbH dgn covering h w]

include covering in
theorem sameOrbit_cover_eq (w w' : OmegaWeight F S b)
    (sameOrbit : ∃ h : H F, weightStep F S literal b hb h w = w') :
    covering.cover w' = covering.cover w := by
  obtain ⟨h, rfl⟩ := sameOrbit
  exact cover_weightStep F S literal b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering h w

variable (seed : OmegaBrauer F root b ≃ OmegaWeight F S b)
  (seed_delta : ∀ theta,
    seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
      weightPermutation F S literal b hb delta indexTwo (seed theta))

include covering seed_delta in
/-- Reorienting a point inside its actual H-orbit does not change the SO
cover assigned by the seed. This is the precise invariant needed when the
pair lemma selects a conjugate character while keeping its raw weight. -/
theorem seed_cover_eq_of_sameOrbit (theta theta' : OmegaBrauer F root b)
    (sameOrbit : ∃ h : H F, brauerStep F S literal root b hb h theta = theta') :
    covering.cover (seed theta') = covering.cover (seed theta) := by
  obtain ⟨h, rfl⟩ := sameOrbit
  rw [seed_H_equivariant F S literal root b hb delta indexTwo outside seed seed_delta h theta]
  exact cover_weightStep F S literal b hb delta indexTwo outside parameters notThree
    SH literalH bH hbH dgn covering h (seed theta)

end Covers

end ModularRep.PaperProofs.TypeBRankThreePrincipalOrbitBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
