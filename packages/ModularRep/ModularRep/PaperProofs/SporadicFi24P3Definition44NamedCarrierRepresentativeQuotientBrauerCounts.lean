import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBrauerCounts

/-! # Brauer counts at the same quotient block as the representative rows -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientBrauerCounts

open ModularRep ModularRep.CharacterWeight ModularRep.FDRepSimpleClassKZero
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockMap
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierTrivialSectorBrauerCounts

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) :=
  Fintype.ofFinite _
local instance subgroupFintype (Z : Subgroup X) : Fintype Z := Fintype.ofFinite Z

variable (iota : PrimeRegularRootEmbedding p k K X) (Z : Subgroup X) [Z.Normal]
variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
variable [Invertible (Fintype.card Z : k)]
variable {BlockU BlockD : Type u}
variable [MulAction (MulAut X)ᵐᵒᵖ BlockU] [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (RU : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := X) (Block := BlockU))
variable (RD : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))

theorem quotientBlock_eq_index (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    let _ := RU.operations.ambientBlockData.fintypeBlock
    let _ := RD.operations.ambientBlockData.fintypeBlock
    quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb =
      quotientBlockIndex Z iota.prime hcentral hprimeTo Sglobal
        RD.operations.ambientBlockData.blocks
        ⟨RU.operations.ambientBlockData.blockIdempotent b,
          RU.operations.ambientBlockData.blocks.primitive b⟩ hb := by
  let _ := RU.operations.ambientBlockData.fintypeBlock
  let _ := RD.operations.ambientBlockData.fintypeBlock
  rfl

variable (injU : IrreducibleBrauerCharacterInjectivity iota)
variable (injD : IrreducibleBrauerCharacterInjectivity (quotientRoot iota Z))

theorem quotientBlock_brauer_card (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ)) :
    let _ := RU.operations.ambientBlockData.fintypeBlock
    let _ := RD.operations.ambientBlockData.fintypeBlock
    Nat.card {phi : IBr iota // irreducibleBrauerCharacterBlock iota injU
      RU.operations.ambientBlockData.blocks phi = b} =
    Nat.card {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injD
        RD.operations.ambientBlockData.blocks chi =
          quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb} := by
  let _ := RU.operations.ambientBlockData.fintypeBlock
  let _ := RD.operations.ambientBlockData.fintypeBlock
  exact trivialBlockBrauer_card iota Z RU.operations.ambientBlockData.blocks
    RD.operations.ambientBlockData.blocks injU injD hcentral hprimeTo Sglobal b hb

theorem quotientBlock_brauer_fixed_card (b : BlockU)
    (hb : IsCentralCharacterSector Z
      (RU.operations.ambientBlockData.blockIdempotent b) (1 : Z →* kˣ))
    (alpha : MulAut X) (beta : MulAut (X ⧸ Z))
    (hcomm : ∀ x : X, QuotientGroup.mk' Z (alpha x) = beta (QuotientGroup.mk' Z x)) :
    let _ := RU.operations.ambientBlockData.fintypeBlock
    let _ := RD.operations.ambientBlockData.fintypeBlock
    Nat.card {phi : IBr iota //
      irreducibleBrauerCharacterBlock iota injU RU.operations.ambientBlockData.blocks phi = b ∧
        MulOpposite.op alpha • phi = phi} =
    Nat.card {chi : IBr (quotientRoot iota Z) //
      irreducibleBrauerCharacterBlock (quotientRoot iota Z) injD
          RD.operations.ambientBlockData.blocks chi =
            quotientBlock iota Z hcentral hprimeTo RU RD Sglobal b hb ∧
        MulOpposite.op beta • chi = chi} := by
  let _ := RU.operations.ambientBlockData.fintypeBlock
  let _ := RD.operations.ambientBlockData.fintypeBlock
  exact trivialBlockBrauer_fixed_card iota Z RU.operations.ambientBlockData.blocks
    RD.operations.ambientBlockData.blocks injU injD hcentral hprimeTo Sglobal b hb alpha beta hcomm

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientBrauerCounts


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
