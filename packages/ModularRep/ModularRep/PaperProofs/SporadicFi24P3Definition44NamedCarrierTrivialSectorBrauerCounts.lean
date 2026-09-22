import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerBlockFixedCounts

/-!
# Actual Brauer counts for every trivial-sector block

The quotient index is computed from the specified primitive idempotent.
No reference character or block-inhabitant source is used.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBrauerCounts

open ModularRep ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CentralEllPrimeIBrFibreTransport
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBrauerTransport
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap
open SporadicFi24P3Definition44NamedCarrierBrauerBlockFixedCounts

universe u

variable {p : ℕ} {k K G I J : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype I] [Fintype J]
variable (iota : PrimeRegularRootEmbedding p k K G) (Z : Subgroup G) [Z.Normal]

local instance subgroupFintype : Fintype Z := Fintype.ofFinite Z

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
def trivialBlockBrauerEquiv (i : I)
    (hi : IsCentralCharacterSector Z (eG i) (1 : Z →* kˣ)) :
    {phi : IBr iota // irreducibleBrauerCharacterBlock iota injG DG phi = i} ≃
    {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
        quotientBlockIndex Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi} := by
  classical
  let j := quotientRoot iota Z
  let E : IBr j ≃ TrivialCentralCharacterFibre iota DG injG hZ :=
    quotientIBrEquivTrivialCentralCharacterFibre
      iota j (canonicalQuotientRealisation iota Z) DG injG hZ
  let BG : IBr iota → I := irreducibleBrauerCharacterBlock iota injG DG
  let BQ : IBr j → J := irreducibleBrauerCharacterBlock j injQ DQ
  let ibar := quotientBlockIndex Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi
  let F := algebraMapOf (k := k) (QuotientGroup.mk' Z)
  change {phi : IBr iota // BG phi = i} ≃ {chi : IBr j // BQ chi = ibar}
  have image (chi : IBr j) : F (eG (BG (E chi).1)) = eQ (BQ chi) :=
    actualBrauerBlock_image
      (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
      (by simpa only [QuotientGroup.ker_mk'] using hZ)
      (by simpa only [QuotientGroup.ker_mk'] using hprimeTo)
      S iota j (fun W => quotientRoot_compatible iota Z W.ρ)
      injG injQ DG DQ (E chi).1 chi rfl
  have imagei : eQ ibar = F (eG i) :=
    quotientBlockIndex_value Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi
  have hiff (chi : IBr j) : BG (E chi).1 = i ↔ BQ chi = ibar := by
    constructor
    · intro h
      apply DQ.primitiveBlockOfIndex_injective
      apply Subtype.ext
      exact (image chi).symm.trans ((congrArg (fun b => F (eG b)) h).trans imagei.symm)
    · intro h
      have hchi : F (eG (BG (E chi).1)) ≠ 0 := by
        rw [image chi]
        exact (DQ.primitive (BQ chi)).ne_zero
      exact blockIndex_eq_of_map_eq_of_ne_zero DG F.toRingHom (BG (E chi).1) i
        ((image chi).trans ((congrArg eQ h).trans imagei)) hchi
  have hsector {phi : IBr iota} (h : BG phi = i) :
      blockCentralCharacter iota DG injG hZ phi = 1 := by
    change DG.centralCharacterSector Z hZ (BG phi) = 1
    rw [h]
    exact ((DG.primitive i).centralCharacterSector_unique Z hZ hi).symm
  let flatten : {phi : TrivialCentralCharacterFibre iota DG injG hZ // BG phi.1 = i} ≃
      {phi : IBr iota // BG phi = i} := Equiv.subtypeSubtypeEquivSubtype hsector
  let restricted : {chi : IBr j // BQ chi = ibar} ≃
      {phi : TrivialCentralCharacterFibre iota DG injG hZ // BG phi.1 = i} :=
    E.subtypeEquiv (fun chi => (hiff chi).symm)
  exact flatten.symm.trans restricted.symm

@[simp]
theorem trivialBlockBrauerEquiv_symm_val (i : I)
    (hi : IsCentralCharacterSector Z (eG i) (1 : Z →* kˣ))
    (chi : {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
        quotientBlockIndex Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi}) :
    ((trivialBlockBrauerEquiv iota Z DG DQ injG injQ hZ hprimeTo S i hi).symm chi).1 =
      inflateIBr iota (quotientRoot iota Z) (canonicalQuotientRealisation iota Z) chi.1 := rfl

theorem trivialBlockBrauer_card (i : I)
    (hi : IsCentralCharacterSector Z (eG i) (1 : Z →* kˣ)) :
    Nat.card {phi : IBr iota // irreducibleBrauerCharacterBlock iota injG DG phi = i} =
    Nat.card {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
        quotientBlockIndex Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi} :=
  Nat.card_congr (trivialBlockBrauerEquiv iota Z DG DQ injG injQ hZ hprimeTo S i hi)

theorem trivialBlockBrauer_fixed_card (i : I)
    (hi : IsCentralCharacterSector Z (eG i) (1 : Z →* kˣ))
    (alpha : MulAut G) (beta : MulAut (G ⧸ Z))
    (hcomm : ∀ g : G, QuotientGroup.mk' Z (alpha g) = beta (QuotientGroup.mk' Z g)) :
    Nat.card {phi : IBr iota //
      irreducibleBrauerCharacterBlock iota injG DG phi = i ∧ MulOpposite.op alpha • phi = phi} =
    Nat.card {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injQ DQ chi =
          quotientBlockIndex Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi ∧
        MulOpposite.op beta • chi = chi} := by
  let j := quotientRoot iota Z
  let BG : IBr iota → I := irreducibleBrauerCharacterBlock iota injG DG
  let BQ : IBr j → J := irreducibleBrauerCharacterBlock j injQ DQ
  let ibar := quotientBlockIndex Z iota.prime hZ hprimeTo S DQ ⟨eG i, DG.primitive i⟩ hi
  let U : Type u := {phi : IBr iota // BG phi = i}
  let V : Type u := {chi : IBr j // BQ chi = ibar}
  let F : U ≃ V := trivialBlockBrauerEquiv iota Z DG DQ injG injQ hZ hprimeTo S i hi
  change Nat.card {phi : IBr iota // BG phi = i ∧ MulOpposite.op alpha • phi = phi} =
    Nat.card {chi : IBr j // BQ chi = ibar ∧ MulOpposite.op beta • chi = chi}
  have hval (chi : V) : (F.symm chi).1 =
      inflateIBr iota j (canonicalQuotientRealisation iota Z) chi.1 :=
    trivialBlockBrauerEquiv_symm_val iota Z DG DQ injG injQ hZ hprimeTo S i hi chi
  have hfix (chi : V) :
      MulOpposite.op alpha • (F.symm chi).1 = (F.symm chi).1 ↔
        MulOpposite.op beta • chi.1 = chi.1 := by
    rw [hval chi]
    exact canonicalInflation_fixed_iff iota Z alpha beta hcomm chi.1
  let FG : {phi : U // MulOpposite.op alpha • phi.1 = phi.1} ≃
      {phi : IBr iota // BG phi = i ∧ MulOpposite.op alpha • phi = phi} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun phi : IBr iota => BG phi = i)
      (fun phi : IBr iota => MulOpposite.op alpha • phi = phi)
  let FQ : {chi : V // MulOpposite.op beta • chi.1 = chi.1} ≃
      {chi : IBr j // BQ chi = ibar ∧ MulOpposite.op beta • chi = chi} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun chi : IBr j => BQ chi = ibar)
      (fun chi : IBr j => MulOpposite.op beta • chi = chi)
  let fixedE : {chi : V // MulOpposite.op beta • chi.1 = chi.1} ≃
      {phi : U // MulOpposite.op alpha • phi.1 = phi.1} :=
    F.symm.subtypeEquiv (fun chi => (hfix chi).symm)
  exact Nat.card_congr (FG.symm.trans (fixedE.symm.trans FQ))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBrauerCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
