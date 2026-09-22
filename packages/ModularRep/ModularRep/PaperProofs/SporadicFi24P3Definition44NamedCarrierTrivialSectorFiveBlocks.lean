import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorTwoNumerical
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures

/-!
# Actual trivial-sector signatures from five specified blocks

The dictionary identifies the supported specified blocks. Its selected
zero role supplies no count; that role's (33,25) signature is derived.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks

open ModularRep.FDRepSimpleClassKZero
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFiveSupportedSignatures

universe u

variable {k K X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]

local instance centerFintype : Fintype (Subgroup.center X) := Fintype.ofFinite _

variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable {I : Type u} [Fintype I] {e : I → k[X]} (blocks : BlockIdempotentDecomposition e)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

def actualBrauerSignature (tau : MulAut X) (b : ActualBlock (k := k) (X := X)) : Nat × Nat :=
  fibreSignature (brauerBlock iota hinj blocks) (fun phi => MulOpposite.op tau • phi = phi) b

def actualWeightSignature (tau : MulAut X) (b : ActualBlock (k := k) (X := X)) : Nat × Nat :=
  fibreSignature R.1.weightBlock (fun w => MulOpposite.op tau • w = w) b

theorem trivial_signatures_of_five_blocks
    (tau : MulAut X)
    (roles : Fin 5 ≃ {b : ActualBlock (k := k) (X := X) // blockSector b = 1})
    (hBr41 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1} = 41)
    (hBr31 : Nat.card {phi : IBr iota // brauerSector iota hinj blocks phi = 1 ∧
      MulOpposite.op tau • phi = phi} = 31)
    (hWt41 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1} = 41)
    (hWt31 : Nat.card {w : WeightClass (p := 2) (K := K) (X := X) //
      weightSector (R := R) w = 1 ∧ MulOpposite.op tau • w = w} = 31)
    (hBrOther : ∀ j : Fin 4,
      actualBrauerSignature iota hinj blocks tau (roles j.succ).1 = nonprincipalSignature j)
    (hWtOther : ∀ j : Fin 4,
      actualWeightSignature R tau (roles j.succ).1 = nonprincipalSignature j) :
    actualBrauerSignature iota hinj blocks tau (roles 0).1 = (33, 25) ∧
    actualWeightSignature R tau (roles 0).1 = (33, 25) ∧
    ∀ b : ActualBlock (k := k) (X := X), blockSector b = 1 →
      actualBrauerSignature iota hinj blocks tau b = actualWeightSignature R tau b := by
  have hBr := principalSignature_of_five (brauerBlock iota hinj blocks)
    (fun b => blockSector b = 1) (fun phi => MulOpposite.op tau • phi = phi) roles
    (by simpa only [brauerSector] using hBr41) (by simpa only [brauerSector] using hBr31) hBrOther
  have hWt := principalSignature_of_five R.1.weightBlock
    (fun b => blockSector b = 1) (fun w => MulOpposite.op tau • w = w) roles
    (by simpa only [weightSector] using hWt41) (by simpa only [weightSector] using hWt31) hWtOther
  refine ⟨hBr, hWt, ?_⟩
  intro b hb
  obtain ⟨i, hi⟩ := roles.surjective ⟨b, hb⟩
  have hv : (roles i).1 = b := congrArg Subtype.val hi
  rw [← hv]
  exact Fin.cases (hBr.trans hWt.symm) (fun j => (hBrOther j).trans (hWtOther j).symm) i

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorFiveBlocks


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
