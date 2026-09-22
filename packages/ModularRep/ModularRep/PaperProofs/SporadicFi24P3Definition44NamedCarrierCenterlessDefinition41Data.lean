import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization

/-! Concrete Spath Definition 4.1 data on the original centreless carrier.
The named simple group and its universal prime-to-p cover remain source
identifications; this proposition records the character-theoretic data. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data
open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierRepresentativeMaps
open SporadicFi24P3Definition44NamedCarrierOriginalRadicalFibre
open SporadicFi24P3Definition44NamedCarrierCenterlessOriginalRows
open SporadicFi24P3Definition44NamedCarrierCenterlessOwnKernel
open SporadicFi24P3Definition44NamedCarrierCenterlessPositiveStabilizer
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierGlobalQOneNormalization
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource GlobalDefectZeroCharacter trivialNormalizerQuotientEquiv)

universe u
variable {p : ℕ} {k K G : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (hcenter : Subgroup.center G = ⊥)
variable (Omega : IBr iota ≃ ConjugacyClass (p := p) (K := K) (G := G))
variable (hOmega : ∀ (a : (MulAut G)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
variable (Dzero : DefectZeroReductionSource iota) (Tzero : TrivialWeightSource (p := p) (X := G))

def CenterlessDefinition41Data : Prop :=
  (⋃ q, originalPart iota Omega q) = Set.univ ∧
  Pairwise (fun q r => Disjoint (originalPart iota Omega q) (originalPart iota Omega r)) ∧
  (∀ (a : (MulAut G)ᵐᵒᵖ) q,
    (fun phi : IBr iota => a • phi) '' originalPart iota Omega q = originalPart iota Omega (a • q)) ∧
  (∀ (Q : RadicalSubgroup (p := p) (G := G)) (b : ActualBlock (k := k) (X := G)),
    ∃ eb : BrauerInBlockAtRadical iota Omega (operationsBlock iota hinj R) Q b ≃
      RepresentativeDZ iota.prime R.1 Q b,
      ∀ x, (eb x).val = localMap iota Omega iota.prime Q x.val) ∧
  (∀ (Q : RadicalSubgroup (p := p) (G := G)) (a : (MulAut G)ᵐᵒᵖ)
    (psi : BrauerAtRadical iota Omega Q),
    localMap iota Omega iota.prime (Q.rightTwist a.unop)
      (brauerTransport iota Omega hOmega a Q psi) =
      localCharacterTwist iota.prime Q a (localMap iota Omega iota.prime Q psi)) ∧
  OriginalRowsOutput iota hinj R hcenter Omega hOmega ∧
  (∀ phi : IBr iota,
    ownCentralKernel iota phi = ⊥ ∧
    (∀ x : G, ownQuotientEquiv iota phi hcenter
      (QuotientGroup.mk' (ownCentralKernel iota phi) x) = x) ∧
    (∀ Q : Subgroup G, (Q.map (QuotientGroup.mk' (ownCentralKernel iota phi))).map
      (ownQuotientEquiv iota phi hcenter).toMonoidHom = Q) ∧
    (actualBase iota phi).Normal ∧
    Subgroup.centralizer (actualBase iota phi : Set (ActualAutAmbient iota phi)) =
      Subgroup.center (ActualAutAmbient iota phi) ∧
    ¬ p ∣ Nat.card (Subgroup.center (ActualAutAmbient iota phi))) ∧
  (∀ (phi : IBr iota) (alpha : MulAut G), alpha ∈ positiveBrauerStabilizer iota phi ↔
    IrreducibleBrauerCharacter.twist iota phi alpha = phi) ∧
  (∀ (phi : IBr iota) (a : ActualAutAmbient iota phi) (x : G),
    innerEmbedding iota phi
      ((centralizerPositiveStabilizerEquiv iota phi hcenter
        (QuotientGroup.mk' (Subgroup.centralizer
          (actualBase iota phi : Set (ActualAutAmbient iota phi))) a)).val x) =
      a * innerEmbedding iota phi x * a⁻¹) ∧
  GlobalQOneOutput iota Omega Dzero Tzero ∧
  ∀ d : GlobalDefectZeroCharacter (p := p) (K := K) (X := G),
    ∃ psi : BrauerAtRadical iota Omega ⟨⊥, Tzero.trivialRadical⟩,
      psi.val = Dzero.reduce (iota := iota) d ∧
      localMap iota Omega iota.prime ⟨⊥, Tzero.trivialRadical⟩ psi =
        ⟨(Tzero.rawAtOne d).localCharacter, (Tzero.rawAtOne d).defectZero⟩ ∧
      OrdinaryIrreducibleCharacter.mapEquiv
        (localMap iota Omega iota.prime ⟨⊥, Tzero.trivialRadical⟩ psi).val
        trivialNormalizerQuotientEquiv = d.val

theorem definition41_data_of_original_rows
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota hinj R phi)
    (hRows : OriginalRowsOutput iota hinj R hcenter Omega hOmega)
    (hOne : GlobalQOneOutput iota Omega Dzero Tzero) :
    CenterlessDefinition41Data iota hinj R hcenter Omega hOmega Dzero Tzero := by
  refine ⟨originalPart_cover iota Omega, originalPart_disjoint iota Omega,
    originalPart_covariance iota Omega hOmega, ?_, ?_, hRows, ?_,
    mem_positiveBrauerStabilizer iota,
    (fun phi => centralizerPositiveStabilizerEquiv_conjugation iota phi hcenter), hOne, ?_⟩
  · intro Q b
    exact ⟨blockLocalMap iota Omega R.1 (operationsBlock iota hinj R) hblock iota.prime Q b,
      fun _ => rfl⟩
  · intro Q a psi
    exact localMap_covariance iota Omega hOmega iota.prime a Q psi
  · intro phi
    exact ⟨ownCentralKernel_eq_bot iota phi hcenter,
      ownQuotientEquiv_mk iota phi hcenter, ownQuotientEquiv_map_radical iota phi hcenter,
      centerless_ambient_geometry iota phi hcenter⟩
  · intro d
    let psi : BrauerAtRadical iota Omega ⟨⊥, Tzero.trivialRadical⟩ :=
      ⟨Dzero.reduce (iota := iota) d, by
        rw [hOne.1 d]
        exact Tzero.radicalClass_atOne d⟩
    exact ⟨psi, rfl, hOne.2.2 d
      (localMap iota Omega iota.prime ⟨⊥, Tzero.trivialRadical⟩ psi)
      (localMap_class iota Omega iota.prime ⟨⊥, Tzero.trivialRadical⟩ psi)⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
