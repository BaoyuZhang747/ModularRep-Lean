import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorTable8AtTwo
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierInverseSectorTransport

/-!
# Both original faithful-sector totals from one ordinary catalogue

The first count is constructed from actual local ordinary rows. The
actual centre-inverting automorphism transports it to the other sector.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierRootSectorWeightAssembly
open SporadicFi24P3Definition44NamedCarrierFaithfulLocalTableAtTwo
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorTable8AtTwo
open SporadicFi24P3Definition44NamedCarrierInverseSectorTransport

universe u w
variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))
variable (nu0 : CentralSector (k := k) (X := X))
variable {Row : Fin 34 → Type w}
variable (C : SectorCatalogue iota nu0 (Fin 34) Row)
variable (CU : ∀ i (theta : LocalDefectZeroCharacter (K := K) (C.representative i)),
  CanonicalRawReduction iota (characterWeightAt iota.prime (C.representative i) theta))
variable (compatibility : CanonicalLocalBlockCompatibility iota R.1.operations)

include CU compatibility in
theorem allFaithfulSectorCounts_of_table8 [∀ i, Finite (Row i)]
    (tau : MulAut X)
    (hinverts : ∀ z : Subgroup.center X, tau (z : X) = (z : X)⁻¹)
    (hcardCenter : Nat.card (Subgroup.center X) = 3) (hnu0 : nu0 ≠ 1)
    (htable : (List.ofFn (fun i : Fin 34 =>
      Nat.card (RootSectorLocal iota nu0 (C.representative i)))).Perm
        correctedFi24FaithfulTable8AtTwo) :
    ∀ nu : CentralSector (k := k) (X := X), nu ≠ 1 →
      Nat.card {weight : WeightClass (p := 2) (K := K) (X := X) //
        weightSector (R := R) weight = nu} = 25 :=
  weightSector_card_of_one_nontrivial R tau hinverts hcardCenter nu0 hnu0 25
    (actualSectorCount_of_table8 iota nu0 C R CU compatibility htable)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorAllCountsAtTwo


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
