import ModularRep.PaperProofs.TypeBQ3TripleCoverCarrier
import ModularRep.PaperProofs.TypeBQ3PrincipalBrauerInflation
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientRoot

/-!
# The principal character's central quotient on the actual triple cover

The central subgroup is computed from the representation already chosen for
the actual principal character. Existing principal support identifies it with
the kernel of the fixed projection to the same matrix G3. The quotient
equivalence and its projection square are then canonical group deductions.

The chosen representation descends on its original space. Its Brauer values
use the restriction of the original root convention and agree with the
accepted principal deflation. Central faithfulness is the property needed
for the later ambient extension; full representation faithfulness is not
asserted. This support construction adds no external source statement.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalExtensionCentralQuotient

open ModularRep FDRepSimpleClassKZero
open TypeBQ3TripleCoverCarrier
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks
open TypeBCentralKernelPrincipalStability
open EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

variable (source : MatrixExceptionalSource)
  (freeSource : TypeBExceptionalCanonicalCover.FreePresentationCoverSource)

-- The actual consumer installs this instance with `finite_X source`.
variable [Finite X]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]
  (rootX : PrimeRegularRootEmbedding 2 k K X)
  (bX : LiteralPrimitiveBlock k X)
  (phi : {phi : IBr rootX // Supported rootX bX phi})

/-- The literal centre intersected with the kernel of the same chosen representation. -/
abbrev centralSubgroup : Subgroup X :=
  TypeBBSCentralCharacterQuotient.centralKernel rootX phi.val

/-- The quotient does not replace the character's central subgroup by a new carrier. -/
abbrev CentralQuotient : Type := X ⧸ centralSubgroup rootX bX phi

/-- Restrict the original finite root convention to this actual quotient. -/
abbrev quotientRoot : PrimeRegularRootEmbedding 2 k K (CentralQuotient rootX bX phi) :=
  SporadicFi24P3Definition44NamedCarrierQuotientRoot.quotientRoot
    rootX (centralSubgroup rootX bX phi)

/-- Descend the original chosen representation on its same underlying space. -/
def quotientRepresentation :=
  QuotientGroup.lift (centralSubgroup rootX bX phi)
    (chosenIBrRepresentation rootX phi.val).ρ
    (show centralSubgroup rootX bX phi ≤
      (chosenIBrRepresentation rootX phi.val).ρ.ker from inf_le_right)

theorem quotientRepresentation_pullback :
    Representation.pullback (quotientRepresentation rootX bX phi)
      (QuotientGroup.mk' (centralSubgroup rootX bX phi)) =
        (chosenIBrRepresentation rootX phi.val).ρ := by
  apply MonoidHom.ext
  intro x
  rfl

theorem quotientRepresentation_irreducible :
    Representation.IsIrreducible (quotientRepresentation rootX bX phi) := by
  apply (Representation.isIrreducible_pullback_iff
    (quotientRepresentation rootX bX phi)
    (QuotientGroup.mk' (centralSubgroup rootX bX phi))
    (QuotientGroup.mk'_surjective _)).mp
  rw [quotientRepresentation_pullback]
  exact (Classical.choose_spec phi.val.property).1

/-- This character is afforded by the factored original representation. -/
def quotientBrauer : IBr (quotientRoot rootX bX phi) :=
  ⟨Representation.brauerCharacterOfRootEmbedding
      (quotientRepresentation rootX bX phi) (quotientRoot rootX bX phi),
    ⟨FDRep.of (quotientRepresentation rootX bX phi),
      by simpa only [FDRep.of_ρ'] using
        quotientRepresentation_irreducible rootX bX phi, rfl⟩⟩

theorem quotientBrauer_inflation :
    PrimeRegularClassFunction.pullback
      (QuotientGroup.mk' (centralSubgroup rootX bX phi))
      (quotientBrauer rootX bX phi).val = phi.val.val := by
  change PrimeRegularClassFunction.pullback
    (QuotientGroup.mk' (centralSubgroup rootX bX phi))
    (Representation.brauerCharacterOfRootEmbedding
      (quotientRepresentation rootX bX phi) (quotientRoot rootX bX phi)) = _
  rw [← Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    (quotientRepresentation rootX bX phi) (quotientRoot rootX bX phi)
    rootX (QuotientGroup.mk' (centralSubgroup rootX bX phi))
    (SporadicFi24P3Definition44NamedCarrierQuotientRoot.quotientRoot_compatible
      rootX (centralSubgroup rootX bX phi)
      (quotientRepresentation rootX bX phi))]
  rw [quotientRepresentation_pullback]
  exact (chosenIBrRepresentation_character rootX phi.val).symm

variable [Fintype (LiteralPrimitiveBlock k X)]
  [Fintype (LiteralPrimitiveBlock k G3)]
  (DX : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k X => c.val))
  (hbX : IsPrincipal bX)

include DX hbX in
/-- Principal support determines exactly the kernel of the fixed projection. -/
theorem centralKernel_eq_qker :
    centralSubgroup rootX bX phi = (q source freeSource).ker :=
  TypeBQ3PrincipalBrauerInflation.centralKernel_eq
    (q source freeSource) (q_kernel_le_center source freeSource)
    (q_kernel_primeToTwo source freeSource) rootX DX bX hbX
    (q_kernel_eq_center source freeSource) phi

/-- The actual central quotient maps to the same G3 through the fixed projection. -/
def centralQuotientEquiv : CentralQuotient rootX bX phi ≃* G3 :=
  (QuotientGroup.quotientMulEquivOfEq
    (centralKernel_eq_qker source freeSource rootX bX phi DX hbX)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (q source freeSource) (q_surjective source freeSource))

@[simp] theorem centralQuotientEquiv_mk (x : X) :
    centralQuotientEquiv source freeSource rootX bX phi DX hbX
      (QuotientGroup.mk' (centralSubgroup rootX bX phi) x) =
        q source freeSource x := rfl

include source freeSource DX hbX in
theorem centralQuotient_center_eq_bot :
    Subgroup.center (CentralQuotient rootX bX phi) = ⊥ := by
  let e := centralQuotientEquiv source freeSource rootX bX phi DX hbX
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 1
  apply e.injective
  have image : e x ∈ Subgroup.center G3 := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    calc
      e z * e x = e (z * x) := (map_mul e z x).symm
      _ = e (x * z) := congrArg e (Subgroup.mem_center_iff.mp hx z)
      _ = e x * e z := map_mul e x z
  rw [TypeBExceptionalCanonicalCover.center_eq_bot_of_nonabelian_simple
    source.simple source.nonabelian] at image
  exact (Subgroup.mem_bot.mp image).trans (map_one e).symm

include source freeSource in
theorem centralQuotient_perfect :
    commutator (CentralQuotient rootX bX phi) = ⊤ := by
  letI : Group.IsPerfect X := ⟨perfect_X source freeSource⟩
  exact Group.IsPerfect.commutator_eq_top

theorem centralQuotientEquiv_kernel :
    (centralQuotientEquiv source freeSource rootX bX phi DX hbX).toMonoidHom.ker =
      Subgroup.center (CentralQuotient rootX bX phi) := by
  rw [centralQuotient_center_eq_bot source freeSource rootX bX phi DX hbX]
  exact (MonoidHom.ker_eq_bot_iff _).mpr
    (centralQuotientEquiv source freeSource rootX bX phi DX hbX).injective

include source freeSource DX hbX in
theorem centralQuotient_center_primeToTwo :
    ¬ 2 ∣ Nat.card (Subgroup.center (CentralQuotient rootX bX phi)) := by
  rw [centralQuotient_center_eq_bot source freeSource rootX bX phi DX hbX]
  simp

include source freeSource DX hbX in
theorem quotientBrauer_centralFaithful :
    Subgroup.center (CentralQuotient rootX bX phi) ⊓
      (chosenIBrRepresentation (quotientRoot rootX bX phi)
        (quotientBrauer rootX bX phi)).ρ.ker = ⊥ := by
  rw [centralQuotient_center_eq_bot source freeSource rootX bX phi DX hbX, bot_inf_eq]

variable (DB : BlockIdempotentDecomposition (fun c : LiteralPrimitiveBlock k G3 => c.val))
  (b : LiteralPrimitiveBlock k G3) (hb : IsPrincipal b)
  (primitive : CentralPrimeToPrimitiveImageSource (k := k)
    (q source freeSource) (q_surjective source freeSource) rootX.prime
    (q_kernel_le_center source freeSource) (q_kernel_primeToTwo source freeSource))

/-- The descended values agree with the same accepted principal deflation. -/
theorem quotientBrauer_eq_pullback_deflation :
    (quotientBrauer rootX bX phi).val =
      PrimeRegularClassFunction.pullback
        (centralQuotientEquiv source freeSource rootX bX phi DX hbX).toMonoidHom
        (TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation
          (q source freeSource) (q_surjective source freeSource)
          (q_kernel_le_center source freeSource) (q_kernel_primeToTwo source freeSource)
          rootX DX DB bX hbX b hb primitive phi).val.val := by
  let pi := QuotientGroup.mk' (centralSubgroup rootX bX phi)
  have hprime : (Nat.card pi.ker).Coprime 2 := by
    rw [QuotientGroup.ker_mk', centralKernel_eq_qker source freeSource rootX bX phi DX hbX]
    exact (Nat.prime_two.coprime_iff_not_dvd.mpr
      (q_kernel_primeToTwo source freeSource)).symm
  apply IrreducibleBrauerCharacterSurjectiveDescent.primeRegularClassFunction_pullback_injective_of_ker_card_coprime
      pi (QuotientGroup.mk'_surjective _) hprime
  calc
    (PrimeRegularClassFunction.pullback pi (quotientBrauer rootX bX phi).val :
        PrimeRegularClassFunction K X 2) = phi.val.val :=
      quotientBrauer_inflation rootX bX phi
    _ = _ := by
      have inflated := TypeBQ3PrincipalBrauerInflation.principalBrauerDeflation_pullback
        (q source freeSource) (q_surjective source freeSource)
        (q_kernel_le_center source freeSource) (q_kernel_primeToTwo source freeSource)
        rootX DX DB bX hbX b hb primitive phi
      apply PrimeRegularClassFunction.ext
      intro x
      have values := congrArg (fun eta : PrimeRegularClassFunction K X 2 => eta x) inflated
      exact values.symm

end ModularRep.PaperProofs.TypeBQ3PrincipalExtensionCentralQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
