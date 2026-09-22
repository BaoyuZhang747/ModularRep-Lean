import ModularRep.PaperProofs.TypeBBSCentralCharacterQuotient

/-!
# Comparison of computed character-central quotients

Each quotient uses the representation already selected by its own character.
Centrelessness and a specified group equivalence determine the comparison.
Both canonical projections, prescribed roots and actual character values
are retained. The modular-system statement uses the same residue map.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentrelessCharacterQuotientEquiv

open ModularRep

/-- Centrelessness transports through the specified group equivalence. -/
theorem centreless_of_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (centrelessG : Subgroup.center G = ⊥) :
    Subgroup.center H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro h hh
  have hc : e.symm h ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hh (e g)
  have hone : e.symm h = 1 :=
    Subgroup.mem_bot.mp (centrelessG ▸ hc)
  exact Subgroup.mem_bot.mpr
    ((e.apply_symm_apply h).symm.trans ((congrArg e hone).trans e.map_one))

variable {p : ℕ} {k K G H : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G] [Group H] [Finite H]
  (e : G ≃* H)
  (rootG : PrimeRegularRootEmbedding p k K G)
  (rootH : PrimeRegularRootEmbedding p k K H)
  (thetaG : IBr rootG) (thetaH : IBr rootH)
  (centrelessG : Subgroup.center G = ⊥)
  (centrelessH : Subgroup.center H = ⊥)

/-- The comparison uses each actual computed quotient and the given e. -/
def quotientEquiv :
    G ⧸ TypeBBSCentralCharacterQuotient.centralKernel rootG thetaG ≃*
      H ⧸ TypeBBSCentralCharacterQuotient.centralKernel rootH thetaH :=
  ((TypeBBSCentralCharacterQuotient.quotientEquiv
    rootG thetaG centrelessG).trans e).trans
      (TypeBBSCentralCharacterQuotient.quotientEquiv
        rootH thetaH centrelessH).symm

/-- The forward square uses the two canonical quotient projections. -/
theorem quotientEquiv_mk (g : G) :
    quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH
        (QuotientGroup.mk'
          (TypeBBSCentralCharacterQuotient.centralKernel rootG thetaG) g) =
      QuotientGroup.mk'
        (TypeBBSCentralCharacterQuotient.centralKernel rootH thetaH) (e g) := by
  change (TypeBBSCentralCharacterQuotient.quotientEquiv
    rootH thetaH centrelessH).symm (e g) = _
  exact TypeBBSCentralCharacterQuotient.quotientEquiv_symm
    rootH thetaH centrelessH (e g)

/-- The inverse square has the same canonical projections. -/
theorem quotientEquiv_symm_mk (h : H) :
    (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH).symm
        (QuotientGroup.mk'
          (TypeBBSCentralCharacterQuotient.centralKernel rootH thetaH) h) =
      QuotientGroup.mk'
        (TypeBBSCentralCharacterQuotient.centralKernel rootG thetaG) (e.symm h) := by
  change (TypeBBSCentralCharacterQuotient.quotientEquiv
    rootG thetaG centrelessG).symm (e.symm h) = _
  exact TypeBBSCentralCharacterQuotient.quotientEquiv_symm
    rootG thetaG centrelessG (e.symm h)

/-- On every quotient element the comparison lies over the original e. -/
theorem quotientEquiv_down
    (x : G ⧸ TypeBBSCentralCharacterQuotient.centralKernel rootG thetaG) :
    TypeBBSCentralCharacterQuotient.quotientEquiv rootH thetaH centrelessH
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH x) =
      e (TypeBBSCentralCharacterQuotient.quotientEquiv rootG thetaG centrelessG x) :=
  (TypeBBSCentralCharacterQuotient.quotientEquiv
    rootH thetaH centrelessH).apply_symm_apply _

/-- The inverse comparison lies over the original inverse equivalence. -/
theorem quotientEquiv_symm_down
    (y : H ⧸ TypeBBSCentralCharacterQuotient.centralKernel rootH thetaH) :
    TypeBBSCentralCharacterQuotient.quotientEquiv rootG thetaG centrelessG
        ((quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH).symm y) =
      e.symm (TypeBBSCentralCharacterQuotient.quotientEquiv
        rootH thetaH centrelessH y) :=
  (TypeBBSCentralCharacterQuotient.quotientEquiv
    rootG thetaG centrelessG).apply_symm_apply _

variable (lifts : rootH.lift = rootG.lift)

include lifts in
/-- The full field-level lift comparison survives both computed quotients. -/
theorem quotientRoot_lift :
    (TypeBBSCentralCharacterQuotient.quotientRoot rootH thetaH centrelessH).lift =
      (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG).lift :=
  (TypeBBSCentralCharacterQuotient.quotientRoot_lift
    rootH thetaH centrelessH).trans
      (lifts.trans (TypeBBSCentralCharacterQuotient.quotientRoot_lift
        rootG thetaG centrelessG).symm)

include lifts in
/-- Transport along the literal quotient comparison gives the prescribed root. -/
theorem quotientRoot_along :
    (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG).alongMulEquiv
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH) =
      TypeBBSCentralCharacterQuotient.quotientRoot rootH thetaH centrelessH :=
  TypeBCentralKernelSpinFibreIdentification.root_eq_of_lift_eq _ _
    ((funext ((TypeBBSCentralCharacterQuotient.quotientRoot
      rootG thetaG centrelessG).alongMulEquiv_lift
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH))).trans
          (quotientRoot_lift rootG rootH thetaG thetaH centrelessG centrelessH lifts).symm)

/-- All irreducible characters compare on the two prescribed quotient roots. -/
def brauerEquiv :
    IBr (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG) ≃
      IBr (TypeBBSCentralCharacterQuotient.quotientRoot rootH thetaH centrelessH) :=
  TypeBCentralKernelSpinFibreIdentification.brauerEquiv
    (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH)
    (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG)
    (TypeBBSCentralCharacterQuotient.quotientRoot rootH thetaH centrelessH)
    (quotientRoot_lift rootG rootH thetaG thetaH centrelessG centrelessH lifts)

/-- Character transport is pullback along the displayed inverse comparison. -/
theorem brauerEquiv_val
    (phi : IBr (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG)) :
    (brauerEquiv e rootG rootH thetaG thetaH centrelessG centrelessH lifts phi).val =
      PrimeRegularClassFunction.pullback
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH).symm.toMonoidHom
        phi.val :=
  TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val
    (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH)
    (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG)
    (TypeBBSCentralCharacterQuotient.quotientRoot rootH thetaH centrelessH)
    (quotientRoot_lift rootG rootH thetaG thetaH centrelessG centrelessH lifts) phi

/-- Arbitrary corresponding characters descend to independently referenced quotients. -/
theorem descendedBrauer_pullback (phiG : IBr rootG) (phiH : IBr rootH)
    (characterValues : phiH.val =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom phiG.val) :
    (TypeBBSCentralCharacterQuotient.brauerEquiv rootH thetaH centrelessH phiH).val =
      PrimeRegularClassFunction.pullback
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH).symm.toMonoidHom
        (TypeBBSCentralCharacterQuotient.brauerEquiv rootG thetaG centrelessG phiG).val := by
  simp only [TypeBBSCentralCharacterQuotient.brauerEquiv,
    TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val]
  rw [characterValues]
  apply PrimeRegularClassFunction.ext
  intro y
  change phiG.val (PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map
        (TypeBBSCentralCharacterQuotient.quotientEquiv
          rootH thetaH centrelessH).toMonoidHom y)) =
    phiG.val (PrimeRegularElement.map
      (TypeBBSCentralCharacterQuotient.quotientEquiv
        rootG thetaG centrelessG).toMonoidHom
      (PrimeRegularElement.map
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH).symm.toMonoidHom y))
  exact congrArg phiG.val (Subtype.ext
    (quotientEquiv_symm_down e rootG rootH thetaG thetaH
      centrelessG centrelessH y.val).symm)

/-- The full Brauer equivalence commutes with those two descents. -/
theorem brauerEquiv_descended (phiG : IBr rootG) (phiH : IBr rootH)
    (characterValues : phiH.val =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom phiG.val) :
    brauerEquiv e rootG rootH thetaG thetaH centrelessG centrelessH lifts
        (TypeBBSCentralCharacterQuotient.brauerEquiv rootG thetaG centrelessG phiG) =
      TypeBBSCentralCharacterQuotient.brauerEquiv rootH thetaH centrelessH phiH := by
  apply Subtype.ext
  exact (brauerEquiv_val e rootG rootH thetaG thetaH centrelessG centrelessH lifts
    (TypeBBSCentralCharacterQuotient.brauerEquiv rootG thetaG centrelessG phiG)).trans
      (descendedBrauer_pullback e rootG rootH thetaG thetaH
        centrelessG centrelessH phiG phiH characterValues).symm

variable (values : thetaH.val =
  PrimeRegularClassFunction.pullback e.symm.toMonoidHom thetaG.val)

include values in
/-- The actual computed reference characters satisfy the same pullback equation. -/
theorem quotientCharacter_pullback :
    (TypeBBSCentralCharacterQuotient.quotientCharacter rootH thetaH centrelessH).val =
      PrimeRegularClassFunction.pullback
        (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH).symm.toMonoidHom
        (TypeBBSCentralCharacterQuotient.quotientCharacter rootG thetaG centrelessG).val :=
  descendedBrauer_pullback e rootG rootH thetaG thetaH
    centrelessG centrelessH thetaG thetaH values

include values in
/-- The character equivalence sends the computed reference to its counterpart. -/
theorem brauerEquiv_quotientCharacter :
    brauerEquiv e rootG rootH thetaG thetaH centrelessG centrelessH lifts
        (TypeBBSCentralCharacterQuotient.quotientCharacter rootG thetaG centrelessG) =
      TypeBBSCentralCharacterQuotient.quotientCharacter rootH thetaH centrelessH := by
  apply Subtype.ext
  exact (brauerEquiv_val e rootG rootH thetaG thetaH centrelessG centrelessH lifts
    (TypeBBSCentralCharacterQuotient.quotientCharacter rootG thetaG centrelessG)).trans
      (quotientCharacter_pullback e rootG rootH thetaG thetaH
        centrelessG centrelessH values).symm

section ModularSystem

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
  (Msys : ModularSystem p K O k)
  (calibrationG : TypeBLocalReductionInstantiation.RootResidueCompatible Msys rootG)

include e rootG thetaG centrelessG lifts calibrationG in
/-- Calibration of the original root yields calibration on the other quotient. -/
theorem quotientRoot_residue :
    TypeBLocalReductionInstantiation.RootResidueCompatible Msys
      (TypeBBSCentralCharacterQuotient.quotientRoot rootH thetaH centrelessH) := by
  rw [← quotientRoot_along e rootG rootH thetaG thetaH centrelessG centrelessH lifts]
  exact TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue Msys
    (TypeBBSCentralCharacterQuotient.quotientRoot rootG thetaG centrelessG)
    (TypeBBSCentralCharacterQuotient.quotientRoot_residue
      rootG thetaG centrelessG Msys calibrationG)
    (quotientEquiv e rootG rootH thetaG thetaH centrelessG centrelessH)

end ModularSystem

end ModularRep.PaperProofs.TypeBCentrelessCharacterQuotientEquiv


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
