import ModularRep.PaperProofs.TypeBRankThreePrincipalOvergroupMatching

/-!
# Actual inertia equality for the same principal covering pair

The original C2-equivariant seed matches actual SO stabilizers. Every
other principal Omega weight class covered by the same SO weight has the
same stabilizer, since that fibre is precisely one C2 orbit. The formal
endpoints retain the same-cover or two literal covering hypotheses. The
imported overgroup correspondence supplies the occurrence/covering anchor;
its direct specialization is a remaining consumer step.

These are weight-CLASS inertias. No raw inertia equality, all-pairs J
condition, field factorization, extension or character triple is supplied.
Products with the same actual subgroup (in particular a prescribed Hall
preimage) consequently agree. Identifying them with a later criterion's
ambient-factor inertia notation remains an explicit carrier join.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalCoveredInertia

open ModularRep TypeBCliffordCarriers TypeBCentralKernelBlockSource
open TypeBCentralKernelInertia TypeBRankThreePrincipalCountBinding
open TypeBRankThreePrincipalOrbitBinding TypeBRankThreePrincipalCoverOrbit
open TypeBRankThreePrincipalOvergroupMatching TypeBGreenPrincipalConstituentSource
open NavarroCoveringBrauerExtension

local instance finiteGroupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable (F : Type) [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (literal : ∀ b, S.operations.ambientBlockData.blockIdempotent b = b.val)
  (b : LiteralPrimitiveBlock k (G F)) (hb : IsPrincipal b)
  (delta : H F) (indexTwo : (G F).index = 2)
  {r f : ℕ} [CharP F r]
  (SH : SOWeightSource (k := k) (K := K) F)
  (bH : LiteralPrimitiveBlock k (H F))
  [Fintype (OmegaWeight F S b)] [DecidableEq (SOWeight F SH bH)]
  (parameters : OddFieldParameters F r f) (notThree : Nat.card F ≠ 3)
  (outside : delta ∉ G F) (hbH : IsPrincipal bH)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (dgn : WeightCoveringModel (k := k) (K := K) F)
  (covering : PublishedWeightCovering F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn)

/-- The actual SO inertia of the given ordinary weight conjugacy class. -/
def classInertia (w : OmegaWeight F S b) : Subgroup (H F) :=
  (MulAction.stabilizer (MulAut (G F))ᵐᵒᵖ w.val).comap (conjugationOp (G F))

/-- Stabilizer membership is constant on the same actual SO covering fibre. -/
theorem weightStep_fix_iff_of_cover_eq (h : H F) (w v : OmegaWeight F S b)
    (sameCover : covering.cover w = covering.cover v) :
    weightStep F S literal b hb h w = w ↔ weightStep F S literal b hb h v = v := by
  by_cases hh : h ∈ G F
  · rw [weightStep_eq_of_mem F S literal b hb h hh w,
      weightStep_eq_of_mem F S literal b hb h hh v]
    exact iff_of_true rfl rfl
  · rw [weightStep_eq_delta_of_notMem F S literal b hb delta indexTwo outside h hh w,
      weightStep_eq_delta_of_notMem F S literal b hb delta indexTwo outside h hh v]
    change weightPermutation F S literal b hb delta indexTwo w = w ↔
      weightPermutation F S literal b hb delta indexTwo v = v
    obtain heq | heq := (cover_eq_iff F S literal b hb delta indexTwo SH bH
      parameters notThree outside hbH literalH dgn covering w v).mp sameCover
    · rw [heq]
    · rw [heq]
      exact (weightPermutation F S literal b hb delta indexTwo).injective.eq_iff.symm

theorem classInertia_eq_of_cover_eq (w v : OmegaWeight F S b)
    (sameCover : covering.cover w = covering.cover v) :
    classInertia F S b w = classInertia F S b v := by
  ext h
  change (conjugationOp (G F) h • w.val = w.val) ↔
    (conjugationOp (G F) h • v.val = v.val)
  have fixed := weightStep_fix_iff_of_cover_eq F S literal b hb delta indexTwo SH bH
    parameters notThree outside hbH literalH dgn covering h w v sameCover
  constructor
  · intro hw
    exact congrArg Subtype.val (fixed.mp (Subtype.ext hw))
  · intro hv
    exact congrArg Subtype.val (fixed.mpr (Subtype.ext hv))

variable (root : PrimeRegularRootEmbedding 2 k K (G F))
  (seed : OmegaBrauer F root b ≃ OmegaWeight F S b)
  (seed_delta : ∀ theta,
    seed (brauerPermutation F S literal root b hb delta indexTwo theta) =
      weightPermutation F S literal b hb delta indexTwo (seed theta))

include outside seed_delta in
/-- The seed's actual class inertia is the same actual character inertia. -/
theorem seed_classInertia_eq (theta : OmegaBrauer F root b) :
    classInertia F S b (seed theta) = T (G F) root theta.val := by
  ext h
  exact seed_stabilizer_iff F S literal root b hb delta indexTwo outside seed seed_delta h theta

include seed_delta in
theorem covered_classInertia_eq (theta : OmegaBrauer F root b) (w : OmegaWeight F S b)
    (sameCover : covering.cover (seed theta) = covering.cover w) :
    classInertia F S b w = T (G F) root theta.val :=
  (classInertia_eq_of_cover_eq F S literal b hb delta indexTwo SH bH parameters notThree
    outside hbH literalH dgn covering (seed theta) w sameCover).symm.trans
    (seed_classInertia_eq F S literal b hb delta indexTwo outside root seed seed_delta theta)

include seed_delta covering in
/-- Both cover hypotheses use the literal DGN relation and the SAME SO class. -/
theorem coversClass_inertia_eq (theta : OmegaBrauer F root b)
    (v : SOWeight F SH bH) (w : OmegaWeight F S b)
    (coversSeed : TypeBWeightCoveringSource.CoversClass (G F) dgn v.val (seed theta).val)
    (coversWeight : TypeBWeightCoveringSource.CoversClass (G F) dgn v.val w.val) :
    classInertia F S b w = T (G F) root theta.val :=
  covered_classInertia_eq F S literal b hb delta indexTwo SH bH parameters notThree
    outside hbH literalH dgn covering root seed seed_delta theta w
    (((covering.covers_iff v (seed theta)).mp coversSeed).trans
      ((covering.covers_iff v w).mp coversWeight).symm)

include seed_delta in
/-- The two actual inertia products agree for the same subgroup. This
does not assert J equality for unrelated character/weight pairs. -/
theorem covered_inertia_product_eq (theta : OmegaBrauer F root b)
    (w : OmegaWeight F S b) (L : Subgroup (H F))
    (sameCover : covering.cover (seed theta) = covering.cover w) :
    (T (G F) root theta.val : Set (H F)) * (L : Set (H F)) =
      (classInertia F S b w : Set (H F)) * (L : Set (H F)) := by
  rw [covered_classInertia_eq F S literal b hb delta indexTwo SH bH parameters notThree
    outside hbH literalH dgn covering root seed seed_delta theta w sameCover]

end ModularRep.PaperProofs.TypeBRankThreePrincipalCoveredInertia


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
