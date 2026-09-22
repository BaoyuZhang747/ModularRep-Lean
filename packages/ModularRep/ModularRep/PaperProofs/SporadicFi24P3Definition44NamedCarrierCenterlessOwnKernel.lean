import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessPositiveStabilizer
import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily

/-! The actual Brauer central kernel and its literal quotient when the
original group is centreless. The whole representation kernel may be larger. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOwnKernel
open ModularRep EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G]
variable (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota)

def ownCentralKernel : Subgroup G :=
  Subgroup.center G ⊓ (chosenIBrRepresentation iota phi).ρ.ker

instance ownCentralKernel_normal : (ownCentralKernel iota phi).Normal := by
  let _ : (chosenIBrRepresentation iota phi).ρ.ker.Normal :=
    MonoidHom.normal_ker (chosenIBrRepresentation iota phi).ρ
  exact Subgroup.normal_inf_normal _ _

theorem ownCentralKernel_eq_bot (hcenter : Subgroup.center G = ⊥) :
    ownCentralKernel iota phi = ⊥ := by
  apply bot_unique
  exact inf_le_left.trans hcenter.le

def ownQuotientEquiv (hcenter : Subgroup.center G = ⊥) :
    G ⧸ ownCentralKernel iota phi ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (ownCentralKernel_eq_bot iota phi hcenter)).trans
    QuotientGroup.quotientBot

theorem ownQuotientEquiv_mk (hcenter : Subgroup.center G = ⊥) (x : G) :
    ownQuotientEquiv iota phi hcenter (QuotientGroup.mk' (ownCentralKernel iota phi) x) = x := by
  change QuotientGroup.quotientBot
    (QuotientGroup.quotientMulEquivOfEq (ownCentralKernel_eq_bot iota phi hcenter)
      (QuotientGroup.mk x)) = x
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem ownQuotientEquiv_square (hcenter : Subgroup.center G = ⊥) :
    (ownQuotientEquiv iota phi hcenter).toMonoidHom.comp
      (QuotientGroup.mk' (ownCentralKernel iota phi)) = MonoidHom.id G := by
  ext x
  exact ownQuotientEquiv_mk iota phi hcenter x

theorem ownQuotientEquiv_map_radical (hcenter : Subgroup.center G = ⊥) (Q : Subgroup G) :
    (Q.map (QuotientGroup.mk' (ownCentralKernel iota phi))).map
      (ownQuotientEquiv iota phi hcenter).toMonoidHom = Q := by
  rw [Subgroup.map_map, ownQuotientEquiv_square iota phi hcenter, Subgroup.map_id]

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOwnKernel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
