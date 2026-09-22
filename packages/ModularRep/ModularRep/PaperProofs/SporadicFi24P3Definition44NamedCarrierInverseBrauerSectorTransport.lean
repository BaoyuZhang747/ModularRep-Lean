import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInverseSectorTransport

/-! # The actual Brauer action pairs the two nontrivial central sectors -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInverseBrauerSectorTransport

open ModularRep ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierInverseSectorTransport

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {I : Type u} [Fintype I] {e : I → k[X]} (blocks : BlockIdempotentDecomposition e)

theorem brauerSector_op_eq_inv
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (phi : IBr iota) :
    brauerSector iota hinj blocks (MulOpposite.op tau • phi) =
      (brauerSector iota hinj blocks phi)⁻¹ := by
  unfold brauerSector
  rw [brauerBlock_transport, blockSector_transport, centralSector_op_eq_inv tau hinverts]

def brauerSectorInvEquiv
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (nu : CentralSector (k := k) (X := X)) :
    {phi : IBr iota // brauerSector iota hinj blocks phi = nu} ≃
      {phi : IBr iota // brauerSector iota hinj blocks phi = nu⁻¹} := by
  let E : Equiv.Perm (IBr iota) := MulAction.toPerm (MulOpposite.op tau)
  refine E.subtypeEquiv ?_
  intro phi
  change brauerSector iota hinj blocks phi = nu ↔
    brauerSector iota hinj blocks (MulOpposite.op tau • phi) = nu⁻¹
  rw [brauerSector_op_eq_inv iota hinj blocks tau hinverts]
  constructor
  · intro h
    exact congrArg (fun mu : CentralSector (k := k) (X := X) => mu⁻¹) h
  · intro h
    apply MonoidHom.ext
    intro z
    have hz := congrArg (fun mu : CentralSector (k := k) (X := X) => mu z) h
    change ((brauerSector iota hinj blocks phi) z)⁻¹ = (nu z)⁻¹ at hz
    exact inv_injective hz

theorem brauerSector_inv_card
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (nu : CentralSector (k := k) (X := X)) :
    Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu⁻¹} =
      Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} :=
  Nat.card_congr (brauerSectorInvEquiv iota hinj blocks tau hinverts nu).symm

theorem brauerSector_card_of_one_nontrivial
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (hcardCenter : Nat.card (Subgroup.center X) = 3)
    (nu0 : CentralSector (k := k) (X := X)) (hnu0 : nu0 ≠ 1) (n : ℕ)
    (hcount : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu0} = n) :
    ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = nu} = n := by
  intro nu hnu
  rcases nontrivialCentralSector_eq_or_eq_inv hcardCenter nu0 nu hnu0 hnu with h | h
  · simpa only [h] using hcount
  · rw [h, brauerSector_inv_card iota hinj blocks tau hinverts]
    exact hcount

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInverseBrauerSectorTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
