import ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers
import ModularRep.PaperProofs.OddTwoPrincipalOrbitAdjustment

/-!
# Actual principal diagonal action and conformal orbit alternatives

The actual PCSp action is lifted through the already constructed full-cover
automorphism map. Its action on the same principal Brauer inflation is the
existing canonical action. Applying the checked two-coset theorem to t inverse
therefore gives the two alternatives for an actual conformal translate.

The chosen Gamma element is the INVERSE of the displayed Sp diagonal
automorphism. Under the canonical inverse/op convention it acts as the
stored opposite-group diagonal. Its action is involutive by the same
two-coset result and action injectivity. Commutation with every actual Sp
automorphism follows from the checked principal ambient-action commutation
and the surjectivity of the same fullAut map. No new source field is added.

These are action joins only. No relation covariance, Brough relation,
orbitWitness, corrected seed or final Type C proposition is asserted.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalDiagonalOrbitActions

open ModularRep
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance
open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin
open ModularRep.PaperProofs.OddTwoPrincipalFieldFixedness
open ModularRep.PaperProofs.OddTwoPrincipalAmbientOrbitStabilizers
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
  (LiteralDiagonalFieldRealisation)
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance spFintype : Fintype (OddTwoConformalProjectiveRealisation.Sp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (PSp n F) := Fintype.ofFinite _

variable {D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block)}
variable {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)
variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective
  E.downSource.operations)
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (L : FullCoverAutomorphismLiftingSource (n := n) (F := F))

/-- Naturality through the ACTUAL lifted PCSp automorphism. Both actions
are the existing canonical principal-fibre actions. -/
theorem brauerEquiv_conformal (t : PCSp n F) (psi : E.DownPrincipalBrauer) :
    let _ := upstreamBrauerAction D
    let _ := ambientBrauerAction E downSupport S
    E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi) =
      pcspToSpAut S cover L t • E.brauerEquiv psi := by
  dsimp only
  letI := upstreamBrauerAction D
  letI := downstreamBrauerAction E downSupport
  change E.brauerEquiv (S.pcspToAut t • psi) =
    pcspToSpAut S cover L t • E.brauerEquiv psi
  rw [← projective_pcspToSpAut S cover L t]
  exact brauerEquiv_equivariant E downSupport (pcspToSpAut S cover L t) psi

variable (O : LiteralDiagonalFieldRealisation n F)
variable (M : ProjectiveMultiplierSource C)

/-- The inverse is required by the manuscript Gamma action convention. -/
def correctionDiagonal : MulAut (OddTwoConformalProjectiveRealisation.Sp n F) :=
  O.outer.diagonal.unop⁻¹

/-- The actual principal action of correctionDiagonal has precisely the
stored FM opposite-group action on the underlying Brauer character. -/
theorem correctionDiagonal_smul_val (psi : D.PrincipalBrauer) :
    let _ := upstreamBrauerAction D
    (correctionDiagonal O • psi).1 = O.outer.diagonal • psi.1 := by
  dsimp only
  change MulOpposite.op ((O.outer.diagonal.unop⁻¹)⁻¹) • psi.1 =
    O.outer.diagonal • psi.1
  rw [inv_inv, MulOpposite.op_unop]

include L M in
/-- K alternatives for the ACTUAL returned conformal element t. The same
principal inflation and character are retained; no relation is asserted. -/
theorem conformal_image_two_actions (t : PCSp n F) (psi : E.DownPrincipalBrauer) :
    let _ := upstreamBrauerAction D
    let _ := ambientBrauerAction E downSupport S
    E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi) =
        E.brauerEquiv psi ∨
      E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi) =
        correctionDiagonal O • E.brauerEquiv psi := by
  dsimp only
  letI := upstreamBrauerAction D
  letI := ambientBrauerAction E downSupport S
  have hv :
      (E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi)).1 =
        MulOpposite.op (pcspToSpAut S cover L t⁻¹) • (E.brauerEquiv psi).1 := by
    rw [brauerEquiv_conformal E downSupport S L]
    change MulOpposite.op ((pcspToSpAut S cover L t)⁻¹) • (E.brauerEquiv psi).1 = _
    rw [map_inv]
  rcases pcsp_ibr_two_actions S O M cover L D.iota t⁻¹ (E.brauerEquiv psi).1 with h | h
  · exact Or.inl (Subtype.ext (hv.trans h))
  · exact Or.inr (Subtype.ext
      ((hv.trans h).trans (correctionDiagonal_smul_val O (E.brauerEquiv psi)).symm))

include cover S M L in
/-- The diagonal action is an involution in K. At the square of the actual
PCSp diagonal, the two-coset theorem gives d²psi=psi or d²psi=dpsi;
injectivity of the action cancels d in the second case. -/
theorem correctionDiagonal_involutive :
    let _ := upstreamBrauerAction D
    Function.Involutive (fun psi : D.PrincipalBrauer => correctionDiagonal O • psi) := by
  dsimp only
  letI := upstreamBrauerAction D
  intro psi
  apply Subtype.ext
  rw [correctionDiagonal_smul_val, correctionDiagonal_smul_val]
  have h := pcsp_ibr_two_actions S O M cover L D.iota
    (diagonalPCSp O * diagonalPCSp O) psi.1
  simp only [map_mul, pcspToSpAut_diagonal, MulOpposite.op_mul,
    MulOpposite.op_unop, mul_smul] at h
  rcases h with h | h
  · exact h
  · exact h.trans ((MulAction.injective O.outer.diagonal) h)

variable (fixed : FengMalleCorollary43aSource D)

include S fixed in
/-- The natural actual A action is surjective onto Aut(PSp). Thus the
checked principal ambient commutation applies to all projective automorphisms.
No arbitrary action-image equality is an input. -/
theorem downstream_fullAut_actions_commute (a b : MulAut (PSp n F))
    (psi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    a • (b • psi) = b • (a • psi) := by
  dsimp only
  obtain ⟨g, rfl⟩ := S.fullAut.surjective a
  obtain ⟨h, rfl⟩ := S.fullAut.surjective b
  exact ambient_actions_commute E downSupport S fixed g h psi

include E downSupport S fixed in
/-- All actual Sp automorphism actions commute on the principal fibre.
This uses the same actual principal inflation equivalence and its naturality.
It does not claim that the automorphism group itself is abelian. -/
theorem upstream_fullAut_actions_commute
    (a b : MulAut (OddTwoConformalProjectiveRealisation.Sp n F))
    (psi : D.PrincipalBrauer) :
    let _ := upstreamBrauerAction D
    a • (b • psi) = b • (a • psi) := by
  dsimp only
  letI := upstreamBrauerAction D
  letI := downstreamBrauerAction E downSupport
  obtain ⟨phi, rfl⟩ := E.brauerEquiv.surjective psi
  calc
    a • (b • E.brauerEquiv phi) =
        E.brauerEquiv (projectiveAutHom a • (projectiveAutHom b • phi)) := by
      rw [brauerEquiv_equivariant E downSupport,
        brauerEquiv_equivariant E downSupport]
    _ = E.brauerEquiv (projectiveAutHom b • (projectiveAutHom a • phi)) :=
      congrArg E.brauerEquiv
        (downstream_fullAut_actions_commute E downSupport S fixed _ _ phi)
    _ = b • (a • E.brauerEquiv phi) := by
      rw [brauerEquiv_equivariant E downSupport,
        brauerEquiv_equivariant E downSupport]

section Definition35Actions

variable (D)
variable (reduction : ∀ w : D.PrincipalWeight,
  SelectedLocalReductionSource D.blockSource D.principalBlock w)

local instance gammaBrauerAction : MulAction (D.problem reduction).Gamma
    (Definition35Brauer (D.problem reduction)) :=
  definition35BrauerAction (D.problem reduction)

/-- The chosen diagonal element belongs to the exact original Gamma. -/
def diagonalGamma : (D.problem reduction).Gamma := correctionDiagonal O

@[simp] theorem diagonalGamma_actual :
    (diagonalGamma (D := D) (O := O) (reduction := reduction) :
      MulAut (OddTwoConformalProjectiveRealisation.Sp n F)) =
      O.outer.diagonal.unop⁻¹ := rfl

include cover S M L in
/-- The involutivity field required by PrincipalOrbitCorrectionInput is
proved for this exact Gamma and the original Definition 3.5 carrier. -/
theorem diagonalGamma_involutive :
    Function.Involutive (fun psi : Definition35Brauer (D.problem reduction) =>
      diagonalGamma (D := D) (O := O) (reduction := reduction) • psi) :=
  correctionDiagonal_involutive (S := S) (L := L) (O := O) (M := M)
    (D := D) (cover := cover)

include E downSupport S fixed in
/-- The commutation field uses the same actual full Gamma action. -/
theorem diagonalGamma_commutes (a : (D.problem reduction).Gamma)
    (psi : Definition35Brauer (D.problem reduction)) :
    diagonalGamma (D := D) (O := O) (reduction := reduction) • (a • psi) =
      a • (diagonalGamma (D := D) (O := O) (reduction := reduction) • psi) :=
  upstream_fullAut_actions_commute E downSupport S fixed
    (correctionDiagonal O) a psi

include L M in
/-- Exact carrier form of the alternatives needed AFTER the Brough theorem
has supplied an actual t and relation. This theorem supplies only the action
alternatives, not the relation or an orbit witness. -/
theorem conformal_image_gamma_alternatives (t : PCSp n F)
    (psi : E.DownPrincipalBrauer) :
    let _ := ambientBrauerAction E downSupport S
    let _ : MulAction (D.problem reduction).Gamma D.PrincipalBrauer := upstreamBrauerAction D
    E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi) =
        E.brauerEquiv psi ∨
      E.brauerEquiv ((SemidirectProduct.inl t : Ambient (n := n) (F := F)) • psi) =
        diagonalGamma (D := D) (O := O) (reduction := reduction) •
          (E.brauerEquiv psi : Definition35Brauer (D.problem reduction)) :=
  conformal_image_two_actions E downSupport S L O M t psi

end Definition35Actions

end ModularRep.PaperProofs.OddTwoPrincipalDiagonalOrbitActions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
