import ModularRep.PaperProofs.SporadicFi24LiteralCarrierBase
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection

/-!
# The actual original trivial-sector weight fibre at one radical

Support is read from the literal specified weight block. The ordinary
representative bridge and its fixed refinement are constructed from
the existing raw block and action laws.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical

open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientRoot
open SporadicFi24P3Definition44NamedCarrierRepresentativeQuotientFibre
open SporadicFi24P3Definition44NamedCarrierTrivialSectorRepresentativeQuotient
open SporadicFi24P3Definition44NamedCarrierRepresentativeFixedPoints
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalReduction
open SporadicFi24P3Definition44NamedCarrierFixedCentralLocalAction
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToBlockImage
open SporadicFi24P3Definition44NamedCarrierRadicalInnerCorrection
open TypeBCentralKernelNormalizerInertia

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
local instance quotientFintype (Z : Subgroup X) [Z.Normal] : Fintype (X ⧸ Z) := Fintype.ofFinite _
local instance subgroupFintype (H : Subgroup X) : Fintype H := Fintype.ofFinite H
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Z : Subgroup X) [Z.Normal]
variable [Invertible (Fintype.card Z : k)]
variable (Q : RadicalSubgroup (p := p) (G := X))

abbrev SectorWeightRadicalFibre :=
  {w : WeightRadicalFibre (K := K) Q //
    IsCentralCharacterSector Z (R.1.weightBlock w.1).1 (1 : Z →* kˣ)}

variable (iota : PrimeRegularRootEmbedding p k K X)

def sectorLocalToWeight :
    {theta : LocalDefectZeroCharacter (K := K) Q //
      IsCentralCharacterSector Z (R.1.operations.ambientBlockData.blockIdempotent
        (R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ)} ≃
      SectorWeightRadicalFibre R Z Q :=
  (localDefectZeroEquivWeightRadicalFibre iota.prime Q).subtypeEquiv (fun theta => by
    rw [localDefectZeroEquivWeightRadicalFibre_apply_val]
    change IsCentralCharacterSector Z (R.1.operations.ambientBlockData.blockIdempotent
        (R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q theta))) (1 : Z →* kˣ) ↔
      IsCentralCharacterSector Z
        (R.1.operations.rawWeightBlock (characterWeightAt iota.prime Q theta)).1 (1 : Z →* kˣ)
    rw [R.2])

variable (hcentral : Z ≤ Subgroup.center X) (hprimeTo : ¬ p ∣ Nat.card Z)
variable {BlockD : Type u} [MulAction (MulAut (X ⧸ Z))ᵐᵒᵖ BlockD]
variable (OD : LocalBlockInductionOperations
  (p := p) (k := k) (K := K) (G := X ⧸ Z) (Block := BlockD))
variable (CU : ∀ theta : LocalDefectZeroCharacter (K := K) Q,
  CanonicalRawReduction iota (characterWeightAt iota.prime Q theta))
variable (CD : ∀ eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q),
  CanonicalRawReduction (quotientRoot iota Z)
    (characterWeightAt iota.prime (fixedRadicalImage iota Z hcentral hprimeTo Q) eta))
variable (compatU : CanonicalLocalBlockCompatibility iota R.1.operations)
variable (compatD : CanonicalLocalBlockCompatibility (quotientRoot iota Z) OD)
variable (Sglobal : CentralPrimeToPrimitiveImageSource (k := k)
  (QuotientGroup.mk' Z) (QuotientGroup.mk'_surjective Z) iota.prime
  (by simpa only [QuotientGroup.ker_mk'] using hcentral)
  (by simpa only [QuotientGroup.ker_mk'] using hprimeTo))
variable (Slocal : CentralPrimeToPrimitiveImageSource (k := k)
  (normalizerMap (QuotientGroup.mk' Z) Q.1)
  (fixedNormalizer_surjective iota.prime Z hcentral hprimeTo Q.1 Q.2) iota.prime
  (fixedNormalizer_kernel_central Z Q.1 hcentral)
  (fixedNormalizer_kernel_primeTo Z Q.1 hcentral hprimeTo))

def trivialSectorWeightRadicalEquiv : SectorWeightRadicalFibre R Z Q ≃
    LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q) :=
  (sectorLocalToWeight (R := R) (Z := Z) (Q := Q) (iota := iota)).symm.trans
    (trivialSectorRepresentativeEquiv (iota := iota) (Z := Z)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (OU := R.1.operations) (OD := OD) (Q := Q)
      (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
      (Sglobal := Sglobal) (Slocal := Slocal))

variable (sigma : MulAut X) (beta : MulAut (X ⧸ Z))
variable (square : ∀ x : X, QuotientGroup.mk' Z (sigma x) = beta (QuotientGroup.mk' Z x))
variable (stableU : Q.1.comap sigma.toMonoidHom = Q.1)

def trivialSectorWeightRadicalFixedEquiv :
    {w : SectorWeightRadicalFibre R Z Q // MulOpposite.op sigma • w.1.1 = w.1.1} ≃
    {eta : LocalDefectZeroCharacter (K := K) (fixedRadicalImage iota Z hcentral hprimeTo Q) //
      OrdinaryIrreducibleCharacter.twist K _ eta.1
        (localAut (fixedRadicalImage iota Z hcentral hprimeTo Q).1 beta
          (image_stable (QuotientGroup.mk' Z) sigma beta square Q.1 stableU)) = eta.1} := by
  let E0 := sectorLocalToWeight (R := R) (Z := Z) (Q := Q) (iota := iota)
  let E0fixed := E0.subtypeEquiv
    (p := fun theta => OrdinaryIrreducibleCharacter.twist K _ theta.1.1
      (localAut Q.1 sigma stableU) = theta.1.1)
    (q := fun w => MulOpposite.op sigma • w.1.1 = w.1.1)
    (fun theta => by
      change OrdinaryIrreducibleCharacter.twist K _ theta.1.1
          (localAut Q.1 sigma stableU) = theta.1.1 ↔
        MulOpposite.op sigma • (localDefectZeroEquivWeightRadicalFibre iota.prime Q theta.1).1 =
          (localDefectZeroEquivWeightRadicalFibre iota.prime Q theta.1).1
      simpa only [localDefectZeroEquivWeightRadicalFibre_apply_val, classAt] using
        (classAt_fixed_iff_local_fixed iota.prime Q sigma stableU theta.1).symm)
  exact E0fixed.symm.trans
    (trivialSectorRepresentativeFixedEquiv (iota := iota) (Z := Z)
      (hcentral := hcentral) (hprimeTo := hprimeTo) (OU := R.1.operations) (OD := OD) (Q := Q)
      (CU := CU) (CD := CD) (compatU := compatU) (compatD := compatD)
      (Sglobal := Sglobal) (Slocal := Slocal)
      (sigma := sigma) (beta := beta) (square := square) (stableU := stableU))

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorWeightRadical


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
