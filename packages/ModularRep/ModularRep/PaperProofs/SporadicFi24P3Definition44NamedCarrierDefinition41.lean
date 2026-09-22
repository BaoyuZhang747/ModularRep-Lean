import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQOne
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalBrauer
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientStabilizer

/-!
# A sufficient centreless presentation of Spath Definition 4.1

The cover and centreless identification are explicit indices. One Omega
determines the partition, every representative local bijection, and every
actual raw weight in the extension data. The methods below expose
clauses (i)--(iv); the packet constructor is an internal construction theorem,
not an external source contract. The manuscript's right action is Lean's
left action by the opposite automorphism group throughout.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41

open ModularRep ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter)
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAllPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierNormalizedPairs
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativePackets
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierRepresentativeQOne
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualRadicalPacket
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientStabilizer
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralLift
open ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierLocalBrauer

universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (localReduction : ∀ (b : SporadicFi24CentralSectorAssemblyLemma56Actual.ActualBlock (k := k) (X := X)) (w : LiteralWeightFibre R.1 b),
  SelectedLocalReductionSource R.1 b w)

structure Definition41Witness (Cover : EllPrimeCoverSource p X)
    (hcenter : Subgroup.center X = ⊥)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X)) where
  Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X)
  equivariant : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi
  block_preserving : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi
  classQOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
    Omega (D.reduce (iota := iota) d) = T.atOne d
  compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations
  packets : ∀ (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota Omega Q),
    PacketAt iota hinj R localReduction Omega Q xi

namespace Definition41Witness

variable {iota hinj R localReduction}
variable {Cover : EllPrimeCoverSource p X} {hcenter : Subgroup.center X = ⊥}
variable {D : DefectZeroReductionSource iota} {T : TrivialWeightSource (p := p) (X := X)}
variable (W : Definition41Witness iota hinj R localReduction Cover hcenter D T)

def partitionEquiv : IBr iota ≃
    Σ r : RadicalConjugacyClass (p := p) (G := X),
      {phi : IBr iota // radicalClass (W.Omega phi) = r} :=
  (Equiv.sigmaFiberEquiv (fun phi : IBr iota => radicalClass (W.Omega phi))).symm

def localEquiv (Q : RadicalSubgroup (p := p) (G := X)) :
    BrauerAtRadical iota W.Omega Q ≃ LocalDefectZeroCharacter (K := K) Q :=
  localMap iota W.Omega iota.prime Q

theorem localEquiv_covariance (a : (MulAut X)ᵐᵒᵖ)
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota W.Omega Q) :
    W.localEquiv (Q.rightTwist a.unop)
        (brauerTransport iota W.Omega W.equivariant a Q xi) =
      localCharacterTwist iota.prime Q a (W.localEquiv Q xi) :=
  localMap_covariance iota W.Omega W.equivariant iota.prime a Q xi

theorem localEquiv_centralLift
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota W.Omega Q) :
    ∃ thetaHat : OrdinaryIrreducibleCharacter.Irr K (Subgroup.normalizer (Q.1 : Set X)),
      (∀ n, thetaHat n = (W.localEquiv Q xi).1 (QuotientGroup.mk n)) ∧
      ∀ nu : OrdinaryIrreducibleCharacter.Irr K (Subgroup.center X),
        ∀ z : Subgroup.center X,
          thetaHat ⟨z.1, Subgroup.center_le_normalizer (Q.1 : Set X) z.2⟩ = thetaHat 1 * nu z :=
  exists_ordinary_lift_over_center hcenter Q.1 (W.localEquiv Q xi).1

theorem localEquiv_blockInducesTo
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota W.Omega Q) :
    let theta := W.localEquiv Q xi
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (Q.1 : Set X))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer Q.1 (O.localCharacterBlock Q.1 theta.1 theta.2))
      (operationsBlock iota hinj R xi.1) :=
  localMap_blockInducesTo iota W.Omega R.1 (operationsBlock iota hinj R)
    W.block_preserving iota.prime Q xi

theorem actualLocalBlockInducesTo
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota W.Omega Q) :
    let O := R.1.operations
    let localData := O.inflatedNormalizerBlockData Q.1
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    BlockInducesTo (Subgroup.normalizer (Q.1 : Set X))
      localData.catalogue O.ambientBlockData.catalogue
      (NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock O Q.1
        (localBrauerRoot (W.packets Q xi)) (localBrauer (W.packets Q xi)))
      (operationsBlock iota hinj R xi.1) := by
  let := R.1.operations.ambientBlockData.fintypeBlock
  let := (R.1.operations.inflatedNormalizerBlockData Q.1).fintypeBlock
  have h := W.compatibility.normalizer_block_of_reduction
    (characterWeightAt iota.prime Q (W.localEquiv Q xi))
    (localBrauerRoot (W.packets Q xi)) (localBrauer (W.packets Q xi))
    (localBrauer_is_actual_reduction (W.packets Q xi))
  dsimp only
  exact (congrArg (fun b => BlockInducesTo (Subgroup.normalizer (Q.1 : Set X))
    (R.1.operations.inflatedNormalizerBlockData Q.1).catalogue
    R.1.operations.ambientBlockData.catalogue b (operationsBlock iota hinj R xi.1)) h).mpr
    (W.localEquiv_blockInducesTo Q xi)

def originalAutomorphismQuotientEquiv
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota W.Omega Q) :
    (W.packets Q xi).ambient.A ⧸ Subgroup.center (W.packets Q xi).ambient.A ≃*
      MulAction.stabilizer (MulAut X)ᵐᵒᵖ xi.1 :=
  (W.packets Q xi).ambient.automorphismQuotientEquiv.trans
    (quotientStabilizerEquiv (problemAt iota hinj R localReduction xi.1) hcenter
      (ownBrauerAt iota hinj R localReduction xi.1)
      (ownBrauerAt iota hinj R localReduction xi.1) (W.packets Q xi).quotient).symm

def sourceHBlocks
    (Q : RadicalSubgroup (p := p) (G := X)) (xi : BrauerAtRadical iota W.Omega Q)
    (H : Subgroup (W.packets Q xi).ambient.A)
    (hHD : H ≤ (W.packets Q xi).localGroup)
    (hbaseD : (W.packets Q xi).ambient.base ⊓ (W.packets Q xi).localGroup ≤ H) :=
  SporadicFi24P3Definition44NamedCarrierSourceHBlocks.sourceHBlockData (W.packets Q xi) H hHD hbaseD

theorem localEquiv_atOne_global
    (d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X)) :
    OrdinaryIrreducibleCharacter.mapEquiv
      (W.localEquiv ⟨⊥, T.trivialRadical⟩
        (atOneBrauer iota W.Omega D T W.classQOne d)).1
      SporadicCompleteCollapseLemma52Actual.trivialNormalizerQuotientEquiv = d.1 :=
  localMap_atOne_global iota W.Omega D T W.classQOne d

theorem atOne_extensions
    (xi : BrauerAtRadical iota W.Omega ⟨⊥, T.trivialRadical⟩) :
    PrimeRegularClassFunction.pullback (W.packets ⟨⊥, T.trivialRadical⟩ xi).localGroup.subtype
      (W.packets ⟨⊥, T.trivialRadical⟩ xi).globalCharacter.1 =
        (W.packets ⟨⊥, T.trivialRadical⟩ xi).localCharacter.1 :=
  (W.packets ⟨⊥, T.trivialRadical⟩ xi).qOne rfl

end Definition41Witness

/-- Internal construction from a family already proved for this same Omega. -/
def ofNormalizedFamily
    (Cover : EllPrimeCoverSource p X) (hcenter : Subgroup.center X = ⊥)
    (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (hOne : ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := X),
      Omega (D.reduce (iota := iota) d) = T.atOne d)
    (compatibility : NavarroLocalReductionInflationBlockCompatibility.Source R.1.operations)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))
    (family : ∀ phi : IBr iota,
      let P := problemAt iota hinj R localReduction phi
      let M := matchAt iota hinj R localReduction Omega hOmega hblock phi
      NormalizedNamedPairWitness P M S hcenter M.theta haut) :
    Definition41Witness iota hinj R localReduction Cover hcenter D T where
  Omega := Omega
  equivariant := hOmega
  block_preserving := hblock
  classQOne := hOne
  compatibility := compatibility
  packets := fun Q xi => Classical.choice
    (exists_packetAt_of_normalized_family iota hinj R localReduction
      Omega hOmega hblock S hcenter haut family Q xi)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierDefinition41



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
