import ModularRep.PaperProofs.TypeBCentralKernelSpinFibreIdentification
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-!
# The computed character-central quotient in the centreless BS application

The subgroup is the centre intersected with the kernel of the irreducible
representation already witnessing the supplied Brauer character. It is not
a freely chosen trivial subgroup. Centrelessness identifies its actual
quotient with the original group by the canonical projection. Roots,
characters, primitive blocks and raw weights use that same equivalence.

These are the quotient identifications required by Brough--Spath Lemma 4.6,
author source lines 742--746. They supply no block-triple witness. The full
ambient and intermediate block-triple transport remains a separate join.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBBSCentralCharacterQuotient

open ModularRep EvenFieldFLZBAWGoodFamily
open TypeBCentralKernelBlockSource TypeBCentralKernelBrauerBlocks

variable {p : ℕ} {k K G : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]
  (root : PrimeRegularRootEmbedding p k K G) (theta : IBr root)

/-- The kernel uses the character's existing irreducible representation. -/
def centralKernel : Subgroup G :=
  Subgroup.center G ⊓ (chosenIBrRepresentation root theta).ρ.ker

instance centralKernel_normal : (centralKernel root theta).Normal := by
  letI := MonoidHom.normal_ker (chosenIBrRepresentation root theta).ρ
  exact Subgroup.normal_inf_normal _ _

/-- This is the literal intersection appearing in the published quotient. -/
theorem centralKernel_eq_intersection :
    centralKernel root theta =
      (chosenIBrRepresentation root theta).ρ.ker ⊓ Subgroup.center G :=
  inf_comm _ _

variable (centreless : Subgroup.center G = ⊥)

include centreless in
theorem centralKernel_eq_bot : centralKernel root theta = ⊥ := by
  unfold centralKernel
  rw [centreless, bot_inf_eq]

/-- The quotient map, followed by this equivalence, is the identity. -/
def quotientEquiv : G ⧸ centralKernel root theta ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (centralKernel_eq_bot root theta centreless)).trans
    QuotientGroup.quotientBot

@[simp] theorem quotientEquiv_mk (g : G) :
    quotientEquiv root theta centreless
      (QuotientGroup.mk' (centralKernel root theta) g) = g := rfl

@[simp] theorem quotientEquiv_symm (g : G) :
    (quotientEquiv root theta centreless).symm g =
      QuotientGroup.mk' (centralKernel root theta) g := by
  apply (quotientEquiv root theta centreless).injective
  exact (quotientEquiv root theta centreless).apply_symm_apply g

/-- The prescribed original convention is transported to its own quotient. -/
def quotientRoot : PrimeRegularRootEmbedding p k K (G ⧸ centralKernel root theta) :=
  root.alongMulEquiv (quotientEquiv root theta centreless).symm

theorem quotientRoot_lift : (quotientRoot root theta centreless).lift = root.lift :=
  funext (root.alongMulEquiv_lift (quotientEquiv root theta centreless).symm)

/-- The complete character equivalence keeps the original fixed root. -/
def brauerEquiv : IBr root ≃ IBr (quotientRoot root theta centreless) :=
  TypeBCentralKernelSpinFibreIdentification.brauerEquiv
    (quotientEquiv root theta centreless).symm root
    (quotientRoot root theta centreless) (quotientRoot_lift root theta centreless)

/-- Every transported character inflates along the actual projection. -/
theorem brauerEquiv_inflation (phi : IBr root) :
    PrimeRegularClassFunction.pullback (QuotientGroup.mk' (centralKernel root theta))
      (brauerEquiv root theta centreless phi).val = phi.val := by
  rw [brauerEquiv, TypeBCentralKernelSpinFibreIdentification.brauerEquiv_val]
  apply PrimeRegularClassFunction.ext
  intro x
  change phi.val (PrimeRegularElement.map
    (quotientEquiv root theta centreless).toMonoidHom
    (PrimeRegularElement.map (QuotientGroup.mk' (centralKernel root theta)) x)) = phi.val x
  congr 1

/-- In particular the reference character itself descends, without an input. -/
def quotientCharacter : IBr (quotientRoot root theta centreless) :=
  brauerEquiv root theta centreless theta

theorem quotientCharacter_inflation :
    PrimeRegularClassFunction.pullback (QuotientGroup.mk' (centralKernel root theta))
      (quotientCharacter root theta centreless).val = theta.val :=
  brauerEquiv_inflation root theta centreless theta

/-- Primitive idempotents move through the same group-basis equivalence. -/
def blockEquiv : LiteralPrimitiveBlock k G ≃
    LiteralPrimitiveBlock k (G ⧸ centralKernel root theta) :=
  TypeBCentralKernelSpinFibreIdentification.primitiveBlockEquiv
    (quotientEquiv root theta centreless).symm

theorem blockEquiv_principal_iff (b : LiteralPrimitiveBlock k G) :
    IsPrincipal (blockEquiv root theta centreless b) ↔ IsPrincipal b :=
  TypeBCentralKernelSpinFibreIdentification.primitiveBlockEquiv_principal_iff
    (quotientEquiv root theta centreless).symm b

theorem brauerEquiv_supported_iff (b : LiteralPrimitiveBlock k G) (phi : IBr root) :
    Supported (quotientRoot root theta centreless) (blockEquiv root theta centreless b)
      (brauerEquiv root theta centreless phi) ↔ Supported root b phi :=
  TypeBCentralKernelSpinFibreIdentification.supported_brauerEquiv_iff
    (quotientEquiv root theta centreless).symm root
    (quotientRoot root theta centreless) (quotientRoot_lift root theta centreless) b phi

/-- Raw weights use the projection itself as the forward group map. -/
def rawWeightEquiv : CharacterWeight p K G ≃
    CharacterWeight p K (G ⧸ centralKernel root theta) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv
    (quotientEquiv root theta centreless).symm

theorem rawWeightEquiv_subgroup (W : CharacterWeight p K G) :
    (rawWeightEquiv root theta centreless W).subgroup =
      W.subgroup.map (QuotientGroup.mk' (centralKernel root theta)) := rfl

theorem rawWeightEquiv_localCharacter (W : CharacterWeight p K G)
    (x : Subgroup.normalizer (W.subgroup : Set G))
    (y : Subgroup.normalizer
      ((rawWeightEquiv root theta centreless W).subgroup :
        Set (G ⧸ centralKernel root theta)))
    (hxy : QuotientGroup.mk' (centralKernel root theta) x.val = y.val) :
    (rawWeightEquiv root theta centreless W).localCharacter
        (TypeBCentralKernelWeightTransport.localMk
          (rawWeightEquiv root theta centreless W).subgroup y) =
      W.localCharacter (TypeBCentralKernelWeightTransport.localMk W.subgroup x) :=
  TypeBCentralKernelSpinFibreIdentification.rawWeightEquiv_localCharacter
    (quotientEquiv root theta centreless).symm W x y
    ((quotientEquiv_symm root theta centreless x.val).trans hxy)

section ModularSystem

variable {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
  (Msys : ModularSystem p K O k)
  (calibration : TypeBLocalReductionInstantiation.RootResidueCompatible Msys root)

include calibration in
theorem quotientRoot_residue :
    TypeBLocalReductionInstantiation.RootResidueCompatible Msys
      (quotientRoot root theta centreless) :=
  TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
    Msys root calibration (quotientEquiv root theta centreless).symm

end ModularSystem

end ModularRep.PaperProofs.TypeBBSCentralCharacterQuotient


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
