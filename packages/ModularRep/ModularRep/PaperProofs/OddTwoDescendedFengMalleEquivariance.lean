import ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
import ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin

/-!
# Equivariance of the same descended principal Feng--Malle map

The downstairs fibres have the canonical actual Aut(PSp) actions. The only
additional block source is the existing OperationsBrauerSupport on the exact
downstairs operations; the constant-one character then makes the principal
block invariant in K. No action is selected by transporting one through an
arbitrary equivalence.

K proves that actual principal Brauer inflation and actual weight quotienting
commute with the already constructed projectiveAutHom. Their composite with
the SAME FM omega is consequently equivariant. The licensed full-cover
automorphism-lifting source supplies surjectivity of this actual hom, giving
the full Aut(PSp) endpoint. Fixedness and equality of matched character and
weight-CLASS stabilizers then follow from equivariance and injectivity.

The convention remains inverseOpHom: the manuscript right action of alpha
uses the underlying function twist by alpha inverse. No named FM labels,
new correspondence, raw-representative stabilizer, covering-character law,
block-triple relation or final iBAW conclusion is introduced.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
open ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation
open ModularRep.PaperProofs.OddTwoCentralTwoPrincipalWeightDescent
open ModularRep.PaperProofs.OddTwoProjectiveAutomorphismDiagonalJoin

universe u

variable {n : ℕ} {F k K Block J : Type u}
variable [Field F] [Fintype F] [Field k] [IsAlgClosed k] [CharP k 2]
variable [Field K] [CharZero K]
variable [MulAction (MulAut (LiteralSp n F))ᵐᵒᵖ Block]
variable [MulAction (MulAut (LiteralPSp n F))ᵐᵒᵖ J]

local instance spFintype : Fintype (LiteralSp n F) := Fintype.ofFinite _
local instance pspFintype : Fintype (LiteralPSp n F) := Fintype.ofFinite _

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block))

/-- Exactly the canonical upstream action used in the literal FM certificate. -/
@[instance_reducible]
def upstreamBrauerAction : MulAction (MulAut (LiteralSp n F)) D.PrincipalBrauer :=
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  rightIBrBlockMulAction D.iota D.injective
    D.blockSource.operations.ambientBlockData.blocks (MonoidHom.id _)
    D.principalBlock (fun _ => D.principalBlock_fixed _) D.support_transport

@[instance_reducible]
def upstreamWeightAction : MulAction (MulAut (LiteralSp n F)) D.PrincipalWeight :=
  rightWeightFibreMulAction (MonoidHom.id _) D.blockSource D.principalBlock
    (fun _ => D.principalBlock_fixed _)

variable {D} {cover : OddSymplecticFullCoverSource n F}
variable (E : PrincipalDescentData (J := J) D cover)

/-- Constant-one is fixed as an actual Brauer character function. -/
theorem oneDown_fixed (a : (MulAut (LiteralPSp n F))ᵐᵒᵖ) :
    a • E.oneDown = E.oneDown := by
  apply Subtype.ext
  ext g
  change E.oneDown.1 _ = E.oneDown.1 g
  rw [E.oneDown_value, E.oneDown_value]

variable (downSupport : OperationsBrauerSupport E.iotaDown E.downInjective
  E.downSource.operations)

include downSupport

/-- The exact standard Brauer-support transport makes the constant-one
principal block invariant under every actual projective automorphism. -/
theorem downPrincipalBlock_fixed (a : (MulAut (LiteralPSp n F))ᵐᵒᵖ) :
    a • E.downPrincipalBlock = E.downPrincipalBlock := by
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  change a • irreducibleBrauerCharacterBlock E.iotaDown E.downInjective
      E.downSource.operations.ambientBlockData.blocks E.oneDown = _
  rw [← downSupport a E.oneDown, oneDown_fixed E]
  rfl

/-- Canonical action on the actual downstairs principal Brauer fibre. -/
@[instance_reducible]
def downstreamBrauerAction : MulAction (MulAut (LiteralPSp n F)) E.DownPrincipalBrauer :=
  letI := E.downSource.operations.ambientBlockData.fintypeBlock
  rightIBrBlockMulAction E.iotaDown E.downInjective
    E.downSource.operations.ambientBlockData.blocks (MonoidHom.id _)
    E.downPrincipalBlock (fun _ => downPrincipalBlock_fixed E downSupport _) downSupport

/-- Canonical action on the actual downstairs weight-class fibre. -/
@[instance_reducible]
def downstreamWeightAction : MulAction (MulAut (LiteralPSp n F)) E.DownPrincipalWeight :=
  rightWeightFibreMulAction (MonoidHom.id _) E.downSource E.downPrincipalBlock
    (fun _ => downPrincipalBlock_fixed E downSupport _)

/-- Actual Brauer inflation commutes with the same quotient automorphism
homomorphism, restricted to the actual principal fibres. -/
theorem brauerEquiv_equivariant (alpha : MulAut (LiteralSp n F))
    (phi : E.DownPrincipalBrauer) :
    let _ := upstreamBrauerAction D
    let _ := downstreamBrauerAction E downSupport
    E.brauerEquiv (projectiveAutHom alpha • phi) = alpha • E.brauerEquiv phi := by
  dsimp only
  apply Subtype.ext
  change E.brauer.brauerEquiv cover
      (IrreducibleBrauerCharacter.twist E.iotaDown phi.1 (projectiveAutHom alpha)⁻¹) =
    IrreducibleBrauerCharacter.twist D.iota (E.brauer.brauerEquiv cover phi.1) alpha⁻¹
  rw [← map_inv (projectiveAutHom (n := n) (F := F)) alpha,
    projectiveAutHom_eq_global]
  exact E.brauer.brauerEquiv_twist cover alpha⁻¹ phi.1

/-- Quotienting the same corresponding weight pair commutes with that same actual
homomorphism. This theorem is about weight classes, not chosen representatives.
-/
theorem weightEquiv_equivariant (alpha : MulAut (LiteralSp n F))
    (w : D.PrincipalWeight) :
    let _ := upstreamWeightAction D
    let _ := downstreamWeightAction E downSupport
    E.weightEquiv (alpha • w) = projectiveAutHom alpha • E.weightEquiv w := by
  dsimp only
  apply Subtype.ext
  change E.weightNaturality.conjugacyClassEquiv
      (rightTwistConjugacyClass alpha⁻¹ w.1) =
    rightTwistConjugacyClass (projectiveAutHom alpha)⁻¹
      (E.weightNaturality.conjugacyClassEquiv w.1)
  rw [← map_inv (projectiveAutHom (n := n) (F := F)) alpha]
  exact E.weightNaturality.conjugacyClassEquiv_rightTwist alpha⁻¹
    (projectiveAutHom alpha⁻¹) (fun _ => rfl) w.1

/-- Equivariance of the SAME computed map for each actual induced
projective automorphism; no projective lifting source is needed here. -/
theorem descendedOmega_equivariant_image
    (FM : D.FengMalleTheorem62LiteralCertificate)
    (alpha : MulAut (LiteralSp n F)) (phi : E.DownPrincipalBrauer) :
    let _ := upstreamBrauerAction D
    let _ := upstreamWeightAction D
    let _ := downstreamBrauerAction E downSupport
    let _ := downstreamWeightAction E downSupport
    E.descendedFengMalleOmega FM (projectiveAutHom alpha • phi) =
      projectiveAutHom alpha • E.descendedFengMalleOmega FM phi := by
  dsimp only
  letI := upstreamBrauerAction D
  letI := upstreamWeightAction D
  letI := downstreamBrauerAction E downSupport
  letI := downstreamWeightAction E downSupport
  calc
    E.descendedFengMalleOmega FM (projectiveAutHom alpha • phi) =
        E.weightEquiv (FM.omega (E.brauerEquiv (projectiveAutHom alpha • phi))) := rfl
    _ = E.weightEquiv (FM.omega (alpha • E.brauerEquiv phi)) :=
      congrArg (fun x => E.weightEquiv (FM.omega x))
        (brauerEquiv_equivariant E downSupport alpha phi)
    _ = E.weightEquiv (alpha • FM.omega (E.brauerEquiv phi)) :=
      congrArg E.weightEquiv (FM.equivariant alpha (E.brauerEquiv phi))
    _ = projectiveAutHom alpha • E.weightEquiv (FM.omega (E.brauerEquiv phi)) :=
      weightEquiv_equivariant E downSupport alpha (FM.omega (E.brauerEquiv phi))
    _ = projectiveAutHom alpha • E.descendedFengMalleOmega FM phi := rfl

/-- The standard lifting source is used only for surjectivity of the
canonical actual projectiveAutHom. It supplies no correspondence or
stabilizer assertion. K obtains the full actual Aut(PSp) endpoint. -/
theorem descendedOmega_equivariant
    (FM : D.FengMalleTheorem62LiteralCertificate)
    (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
    (beta : MulAut (LiteralPSp n F)) (phi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    let _ := downstreamWeightAction E downSupport
    E.descendedFengMalleOmega FM (beta • phi) =
      beta • E.descendedFengMalleOmega FM phi := by
  dsimp only
  obtain ⟨alpha, rfl⟩ := (lifting.bijective_on_full_cover cover).2 beta
  exact descendedOmega_equivariant_image E downSupport FM alpha phi

/-- Fixedness of a character and its matched weight class is equivalent
for each displayed induced automorphism, even before using full lifting. -/
theorem descendedOmega_fixed_iff_image
    (FM : D.FengMalleTheorem62LiteralCertificate)
    (alpha : MulAut (LiteralSp n F)) (phi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    let _ := downstreamWeightAction E downSupport
    projectiveAutHom alpha • phi = phi ↔
      projectiveAutHom alpha • E.descendedFengMalleOmega FM phi =
        E.descendedFengMalleOmega FM phi := by
  dsimp only
  constructor
  · intro h
    rw [← descendedOmega_equivariant_image E downSupport FM alpha phi, h]
  · intro h
    apply (E.descendedFengMalleOmega FM).injective
    rw [descendedOmega_equivariant_image E downSupport FM alpha phi, h]

/-- Fixedness equivalence for every actual projective automorphism. -/
theorem descendedOmega_fixed_iff
    (FM : D.FengMalleTheorem62LiteralCertificate)
    (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
    (beta : MulAut (LiteralPSp n F)) (phi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    let _ := downstreamWeightAction E downSupport
    beta • phi = phi ↔
      beta • E.descendedFengMalleOmega FM phi = E.descendedFengMalleOmega FM phi := by
  dsimp only
  obtain ⟨alpha, rfl⟩ := (lifting.bijective_on_full_cover cover).2 beta
  exact descendedOmega_fixed_iff_image E downSupport FM alpha phi

/-- Literal stabilizer comaps under the canonical quotient hom are equal.
This uses neither full lifting nor any stabilizer source premise. -/
theorem matchedClassStabilizers_comap_eq
    (FM : D.FengMalleTheorem62LiteralCertificate) (phi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    let _ := downstreamWeightAction E downSupport
    (MulAction.stabilizer (MulAut (LiteralPSp n F)) phi).comap projectiveAutHom =
      (MulAction.stabilizer (MulAut (LiteralPSp n F))
        (E.descendedFengMalleOmega FM phi)).comap projectiveAutHom := by
  dsimp only
  ext alpha
  exact descendedOmega_fixed_iff_image E downSupport FM alpha phi

/-- The actual full character and weight-CLASS stabilizers are equal.
This gives no equality with a chosen raw pair's stabilizer and no
semidirect or block-triple relation identification. -/
theorem matchedClassStabilizers_eq
    (FM : D.FengMalleTheorem62LiteralCertificate)
    (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
    (phi : E.DownPrincipalBrauer) :
    let _ := downstreamBrauerAction E downSupport
    let _ := downstreamWeightAction E downSupport
    MulAction.stabilizer (MulAut (LiteralPSp n F)) phi =
      MulAction.stabilizer (MulAut (LiteralPSp n F))
        (E.descendedFengMalleOmega FM phi) := by
  dsimp only
  ext beta
  exact descendedOmega_fixed_iff E downSupport FM lifting beta phi

end ModularRep.PaperProofs.OddTwoDescendedFengMalleEquivariance


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
