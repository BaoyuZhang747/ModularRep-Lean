import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage

/-!
# The actual Brauer block fibre under the canonical central quotient

The quotient block is the block of the deflated reference character.
The specified image law and its injectivity derive both fibre directions.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport

universe u

variable {p : ℕ} {k K G I J : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype I] [Fintype J]
variable (iota : PrimeRegularRootEmbedding p k K G) (Z : Subgroup G) [Z.Normal]

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

set_option maxHeartbeats 2000000 in
def physicalBrauerBlockFibreEquiv
    (psi0 : TrivialCentralCharacterFibre iota DG injG hZ) :
    {phi : IBr iota //
      irreducibleBrauerCharacterBlock iota injG DG phi =
        irreducibleBrauerCharacterBlock iota injG DG psi0.1} ≃
    {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
        irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ
          ((quotientIBrEquivTrivialCentralCharacterFibre
            iota (quotientRoot iota Z)
            (canonicalQuotientRealisation iota Z) DG injG hZ).symm psi0)} := by
  classical
  let j := quotientRoot iota Z
  let E := quotientIBrEquivTrivialCentralCharacterFibre
    iota j (canonicalQuotientRealisation iota Z) DG injG hZ
  let BG := irreducibleBrauerCharacterBlock iota injG DG
  let BQ := irreducibleBrauerCharacterBlock j injQ DQ
  let chi0 := E.symm psi0
  let F := algebraMapOf (k := k) (QuotientGroup.mk' Z)
  change {phi : IBr iota // BG phi = BG psi0.1} ≃
    {chi : IBr j // BQ chi = BQ chi0}
  have image (chi : IBr j) : F (eG (BG (E chi).1)) = eQ (BQ chi) := by
    exact actualBrauerBlock_image
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
      (by simpa only [QuotientGroup.ker_mk'] using hZ)
      (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)
      S iota j (fun W => quotientRoot_compatible iota Z W.ρ)
      injG injQ DG DQ (E chi).1 chi rfl
  have image0 : F (eG (BG psi0.1)) = eQ (BQ chi0) := by
    have h := image chi0
    have he : (E chi0).1 = psi0.1 := congrArg Subtype.val (E.apply_symm_apply psi0)
    simpa only [he] using h
  have hiff (chi : IBr j) : BG (E chi).1 = BG psi0.1 ↔ BQ chi = BQ chi0 := by
    constructor
    · intro h
      apply DQ.primitiveBlockOfIndex_injective
      apply Subtype.ext
      exact (image chi).symm.trans
        ((congrArg (fun b => F (eG b)) h).trans image0)
    · intro h
      have hchi : F (eG (BG (E chi).1)) ≠ 0 := by
        rw [image chi]
        exact (DQ.primitive (BQ chi)).ne_zero
      exact blockIndex_eq_of_map_eq_of_ne_zero DG F.toRingHom
        (BG (E chi).1) (BG psi0.1)
        ((image chi).trans ((congrArg eQ h).trans image0.symm)) hchi
  have hsector {phi : IBr iota} (h : BG phi = BG psi0.1) :
      blockCentralCharacter iota DG injG hZ phi = 1 := by
    change DG.centralCharacterSector Z hZ (BG phi) = 1
    rw [h]
    exact psi0.2
  let flatten :
      {phi : TrivialCentralCharacterFibre iota DG injG hZ // BG phi.1 = BG psi0.1} ≃
      {phi : IBr iota // BG phi = BG psi0.1} :=
    Equiv.subtypeSubtypeEquivSubtype hsector
  let restricted : {chi : IBr j // BQ chi = BQ chi0} ≃
      {phi : TrivialCentralCharacterFibre iota DG injG hZ // BG phi.1 = BG psi0.1} :=
    E.subtypeEquiv (fun chi => (hiff chi).symm)
  exact flatten.symm.trans restricted.symm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerBlockFibre


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
