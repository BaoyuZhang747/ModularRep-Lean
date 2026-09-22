import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

/-!
# Every actual radical representative uses the same normalized family

The representative local bijection determines its raw weight. Equality of
its weight class with Omega(phi) supplies the inner conjugator, after which
the original stored packet is rebased. No new packet or local matching
source is an input to the Fischer source-facing theorem.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets

open ModularRep ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeTransport
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket

universe u

variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (localReduction : ∀ (b : ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
  SelectedLocalReductionSource R.1 b w)

def ownBrauerAt (phi : IBr iota) : Definition35Brauer (problemAt iota hinj R localReduction phi) :=
  ⟨phi, rfl⟩

abbrev PacketAt (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota Omega Q) :=
  ActualWeightPacket (problemAt iota hinj R localReduction xi.1)
    (ownBrauerAt iota hinj R localReduction xi.1)
    (characterWeightAt iota.prime Q (localMap iota Omega iota.prime Q xi))

theorem exists_packetAt_of_normalized_family
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (alpha : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (alpha • phi) = alpha • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (hcenter : Subgroup.center X = ⊥)
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (family : ∀ phi : IBr iota,
      let P := problemAt iota hinj R localReduction phi
      let M := matchAt iota hinj R localReduction Omega hOmega hblock phi
      NormalizedNamedPairWitness P M S hcenter M.theta haut)
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota Omega Q) :
    Nonempty (PacketAt iota hinj R localReduction Omega Q xi) := by
  let P := problemAt iota hinj R localReduction xi.1
  let M := matchAt iota hinj R localReduction Omega hOmega hblock xi.1
  obtain ⟨g, hg⟩ := exists_selected_inner_raw P M Q xi.2
  exact ⟨rebasePacket (family xi.1).pair.spath hcenter (family xi.1).qOne
    (characterWeightAt iota.prime Q (localMap iota Omega iota.prime Q xi)) g hg⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
