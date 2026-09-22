import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre
import ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance

/-!
# Brauer block counts under the canonical central quotient

The inverse specified block-fibre map is literal inflation. Its commuting
automorphism square and injectivity identify the fixed subsets while
retaining the exact deflated reference character.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockFixedCounts

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreEquivariance
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre

universe u

variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G) (Z : Subgroup G) [Z.Normal]

theorem canonicalInflation_fixed_iff
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (hcomm : ∀ g : G, QuotientGroup.mk' Z (alpha g) = beta (QuotientGroup.mk' Z g))
    (chi : IBr (quotientRoot iota Z)) :
    MulOpposite.op alpha • inflateIBr iota (quotientRoot iota Z)
        (canonicalQuotientRealisation iota Z) chi =
      inflateIBr iota (quotientRoot iota Z) (canonicalQuotientRealisation iota Z) chi ↔
      MulOpposite.op beta • chi = chi := by
  have htwist : inflateIBr iota (quotientRoot iota Z)
      (canonicalQuotientRealisation iota Z) (MulOpposite.op beta • chi) =
      MulOpposite.op alpha • inflateIBr iota (quotientRoot iota Z)
        (canonicalQuotientRealisation iota Z) chi :=
    inflateIBr_twist_of_quotientSquare iota (quotientRoot iota Z)
      (canonicalQuotientRealisation iota Z) alpha beta hcomm chi
  rw [← htwist]
  have hinj : Function.Injective (inflateIBr iota (quotientRoot iota Z)
      (canonicalQuotientRealisation iota Z)) := by
    intro phi psi h
    apply Subtype.ext
    apply QuotientRealisationSource.pullback_injective
      iota (quotientRoot iota Z) (canonicalQuotientRealisation iota Z)
    exact congrArg Subtype.val h
  exact hinj.eq_iff

variable {I J : Type u} [Fintype I] [Fintype J]
noncomputable local instance subgroupFintype : Fintype Z := Fintype.ofFinite Z
variable [Invertible (Fintype.card Z : k)]
variable {eG : I → k[G]} {eQ : J → k[G ⧸ Z]}
variable (DG : BlockIdempotentDecomposition eG) (DQ : BlockIdempotentDecomposition eQ)
variable (injG : IrreducibleBrauerCharacterInjectivity iota)
variable (injQ : IrreducibleBrauerCharacterInjectivity (quotientRoot iota Z))
variable (hZ : Z ≤ Subgroup.center G) (hprimeTo : ¬ p ∣ Nat.card Z)
variable (S : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hZ)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))

@[simp]
theorem physicalBrauerBlockFibreEquiv_symm_val
    (psi0 : TrivialCentralCharacterFibre iota DG injG hZ)
    (chi : {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
        irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ
          ((quotientIBrEquivTrivialCentralCharacterFibre iota (quotientRoot iota Z)
            (canonicalQuotientRealisation iota Z) DG injG hZ).symm psi0)}) :
    ((physicalBrauerBlockFibreEquiv iota Z DG DQ injG injQ hZ hprimeTo S psi0).symm chi).1 =
      inflateIBr iota (quotientRoot iota Z) (canonicalQuotientRealisation iota Z) chi.1 := by
  rfl

include hprimeTo S in
theorem physicalBrauerBlockFibre_card
    (psi0 : TrivialCentralCharacterFibre iota DG injG hZ) :
    Nat.card {phi : IBr iota //
      irreducibleBrauerCharacterBlock iota injG DG phi =
        irreducibleBrauerCharacterBlock iota injG DG psi0.1} =
    Nat.card {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
        irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ
          ((quotientIBrEquivTrivialCentralCharacterFibre iota (quotientRoot iota Z)
            (canonicalQuotientRealisation iota Z) DG injG hZ).symm psi0)} :=
  Nat.card_congr (physicalBrauerBlockFibreEquiv iota Z DG DQ injG injQ hZ hprimeTo S psi0)

include hprimeTo S in
theorem physicalBrauerBlockFibre_fixed_card
    (psi0 : TrivialCentralCharacterFibre iota DG injG hZ)
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (hcomm : ∀ g : G, QuotientGroup.mk' Z (alpha g) = beta (QuotientGroup.mk' Z g)) :
    Nat.card {phi : IBr iota //
      irreducibleBrauerCharacterBlock iota injG DG phi =
          irreducibleBrauerCharacterBlock iota injG DG psi0.1 ∧
        MulOpposite.op alpha • phi = phi} =
    Nat.card {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
          irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ
            ((quotientIBrEquivTrivialCentralCharacterFibre iota (quotientRoot iota Z)
              (canonicalQuotientRealisation iota Z) DG injG hZ).symm psi0) ∧
        MulOpposite.op beta • chi = chi} := by
  let j := quotientRoot iota Z
  let E : IBr j ≃ TrivialCentralCharacterFibre iota DG injG hZ :=
    quotientIBrEquivTrivialCentralCharacterFibre
      iota j (canonicalQuotientRealisation iota Z) DG injG hZ
  let BG : IBr iota → I := irreducibleBrauerCharacterBlock iota injG DG
  let BQ : IBr j → J := irreducibleBrauerCharacterBlock j injQ DQ
  let chi0 : IBr j := E.symm psi0
  let U : Type u := {phi : IBr iota // BG phi = BG psi0.1}
  let V : Type u := {chi : IBr j // BQ chi = BQ chi0}
  let F : U ≃ V := physicalBrauerBlockFibreEquiv iota Z DG DQ injG injQ hZ hprimeTo S psi0
  change Nat.card {phi : IBr iota // BG phi = BG psi0.1 ∧ MulOpposite.op alpha • phi = phi} =
    Nat.card {chi : IBr j // BQ chi = BQ chi0 ∧ MulOpposite.op beta • chi = chi}
  have hval (chi : V) : (F.symm chi).1 =
      inflateIBr iota j (canonicalQuotientRealisation iota Z) chi.1 :=
    physicalBrauerBlockFibreEquiv_symm_val iota Z DG DQ injG injQ hZ hprimeTo S psi0 chi
  have hfix (chi : V) :
      MulOpposite.op alpha • (F.symm chi).1 = (F.symm chi).1 ↔
        MulOpposite.op beta • chi.1 = chi.1 := by
    rw [hval chi]
    exact canonicalInflation_fixed_iff iota Z alpha beta hcomm chi.1
  let FG : {phi : U // MulOpposite.op alpha • phi.1 = phi.1} ≃
      {phi : IBr iota // BG phi = BG psi0.1 ∧ MulOpposite.op alpha • phi = phi} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun phi : IBr iota => BG phi = BG psi0.1)
      (fun phi : IBr iota => MulOpposite.op alpha • phi = phi)
  let FQ : {chi : V // MulOpposite.op beta • chi.1 = chi.1} ≃
      {chi : IBr j // BQ chi = BQ chi0 ∧ MulOpposite.op beta • chi = chi} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun chi : IBr j => BQ chi = BQ chi0)
      (fun chi : IBr j => MulOpposite.op beta • chi = chi)
  let fixedE : {chi : V // MulOpposite.op beta • chi.1 = chi.1} ≃
      {phi : U // MulOpposite.op alpha • phi.1 = phi.1} :=
    F.symm.subtypeEquiv (fun chi => (hfix chi).symm)
  exact Nat.card_congr (FG.symm.trans (fixedE.symm.trans FQ))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockFixedCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
