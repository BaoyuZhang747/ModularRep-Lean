import ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance

/-!
# Principal field fixedness and the actual stabilizer factorizations

Feng--Malle Corollary 4.3(a) is licensed directly on the actual principal
Brauer characters and entrywise field automorphisms. Its named labels are
not reconstructed. K derives weight-CLASS fixedness using the SAME FM map,
then transports both statements through the already computed central
descent. The actual PCSp/field semidirect action is through the fixed
natural fullAut map. Its Brauer and weight-class stabilizers factor because
every actual field element fixes the corresponding object.

This does not choose a field-stable raw representative or a covering
object, and it supplies neither an extension nor a block-triple relation.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance spFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block))

/-- Exact E2 Corollary 4.3(a), at the actual odd-field principal block.
The field action is the literal entrywise automorphism and the character
action is the existing canonical one. No weight or stabilizer statement
is a field. -/
structure FengMalleCorollary43aSource : Prop where
  parameters : ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow.OddFieldParameters n F
  field_fixed : ∀ (sigma : F ≃+* F) (psi : D.PrincipalBrauer),
    let _ := upstreamBrauerAction D
    spFieldAut (n := n) sigma • psi = psi

variable {D} (fixed : FengMalleCorollary43aSource D)
variable (FM : D.FengMalleTheorem62LiteralCertificate)

include fixed FM in
/-- All principal weight classes are fixed by the actual field group,
deduced from the same FM map. -/
theorem upstreamWeight_field_fixed (sigma : F ≃+* F) (w : D.PrincipalWeight) :
    let _ := upstreamWeightAction D
    spFieldAut (n := n) sigma • w = w := by
  dsimp only
  letI := upstreamBrauerAction D
  letI := upstreamWeightAction D
  obtain ⟨psi, rfl⟩ := FM.omega.surjective w
  rw [← FM.equivariant, fixed.field_fixed]

variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)
variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective
  E.downSource.operations)

/-- The entrywise projective field action is exactly the induced action
already used by the central descent. -/
theorem field_projectiveAutHom (sigma : F ≃+* F) :
    pspFieldAction (n := n) sigma = projectiveAutHom (spFieldAut (n := n) sigma) := rfl

include fixed in
theorem downstreamBrauer_field_fixed (sigma : F ≃+* F) (psi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    pspFieldAction (n := n) sigma • psi = psi := by
  dsimp only
  letI := upstreamBrauerAction D
  letI := downstreamBrauerAction E downSupport
  apply E.brauerEquiv.injective
  rw [field_projectiveAutHom, brauerEquiv_equivariant E downSupport]
  exact fixed.field_fixed sigma (E.brauerEquiv psi)

include fixed FM in
theorem downstreamWeight_field_fixed (sigma : F ≃+* F) (w : E.DownPrincipalWeight) :
    let _ := downstreamWeightAction E downSupport
    pspFieldAction (n := n) sigma • w = w := by
  dsimp only
  letI := upstreamWeightAction D
  letI := downstreamWeightAction E downSupport
  obtain ⟨v, rfl⟩ := E.weightEquiv.surjective w
  rw [field_projectiveAutHom, ← weightEquiv_equivariant E downSupport,
    upstreamWeight_field_fixed fixed FM]

variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)

/-- Actual PCSp/field action through its fixed natural automorphism map. -/
@[instance_reducible]
def ambientBrauerAction : MulAction (Ambient (n := n) (F := F)) E.DownPrincipalBrauer :=
  letI := downstreamBrauerAction E downSupport
  MulAction.compHom E.DownPrincipalBrauer S.fullAut.toMonoidHom

@[instance_reducible]
def ambientWeightAction : MulAction (Ambient (n := n) (F := F)) E.DownPrincipalWeight :=
  letI := downstreamWeightAction E downSupport
  MulAction.compHom E.DownPrincipalWeight S.fullAut.toMonoidHom

include fixed in
theorem ambientBrauer_field_fixed (sigma : F ≃+* F) (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    (SemidirectProduct.inr sigma : Ambient (n := n) (F := F)) • psi = psi := by
  dsimp only
  letI := downstreamBrauerAction E downSupport
  change S.fullAut (SemidirectProduct.inr sigma) • psi = psi
  rw [S.fullAut_field]
  exact downstreamBrauer_field_fixed fixed E downSupport sigma psi

include fixed FM in
theorem ambientWeight_field_fixed (sigma : F ≃+* F) (w : E.DownPrincipalWeight) :
    let _ := ambientWeightAction E downSupport S
    (SemidirectProduct.inr sigma : Ambient (n := n) (F := F)) • w = w := by
  dsimp only
  letI := downstreamWeightAction E downSupport
  change S.fullAut (SemidirectProduct.inr sigma) • w = w
  rw [S.fullAut_field]
  exact downstreamWeight_field_fixed fixed FM E downSupport sigma w

include fixed in
/-- The actual character stabilizer factors into its conformal part and
the full field group. No subgroup factorization is supplied as an input. -/
theorem ambientBrauer_stabilizer_factorization
    (g : Ambient (n := n) (F := F)) (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    g ∈ MulAction.stabilizer (Ambient (n := n) (F := F)) psi ↔
      (SemidirectProduct.inl g.left : Ambient (n := n) (F := F)) ∈
        MulAction.stabilizer (Ambient (n := n) (F := F)) psi := by
  dsimp only
  letI := ambientBrauerAction E downSupport S
  change g • psi = psi ↔ (SemidirectProduct.inl g.left) • psi = psi
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g, mul_smul,
    ambientBrauer_field_fixed fixed E downSupport S]

include fixed FM in
/-- The analogous factorization concerns weight CLASSES. It makes no
assertion that a chosen raw representative is field invariant. -/
theorem ambientWeight_stabilizer_factorization
    (g : Ambient (n := n) (F := F)) (w : E.DownPrincipalWeight) :
    let _ := ambientWeightAction E downSupport S
    g ∈ MulAction.stabilizer (Ambient (n := n) (F := F)) w ↔
      (SemidirectProduct.inl g.left : Ambient (n := n) (F := F)) ∈
        MulAction.stabilizer (Ambient (n := n) (F := F)) w := by
  dsimp only
  letI := ambientWeightAction E downSupport S
  change g • w = w ↔ (SemidirectProduct.inl g.left) • w = w
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g, mul_smul,
    ambientWeight_field_fixed fixed FM E downSupport S]

end ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
