import ModularRep.PaperProofs.SpathRootCoherence
import ModularRep.PaperProofs.CoherentCenterlessRows
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data

/-! Extension and block data for Späth's Definition 4.1.
The raw records do not impose agreement between the roots used in different
groups. A full certificate additionally requires the root compatibility
specified below. -/
noncomputable section
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open ModularRep ModularRep.CharacterWeight
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual (DefectZeroReductionSource TrivialWeightSource)
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAllPairs
open SporadicFi24P3Definition44NamedCarrierCenterlessDefinition41Data
universe u
variable {p : ℕ} {k K X : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding p k K X)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := X))
variable (Cover : EllPrimeCoverSource p X)

/-- Raw extension and block constructions. This proposition alone does not
express the inductive condition, since its roots need not be compatible. -/
def RawDefinition41Certificate : Prop :=
  ∃ (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X)),
    (∃ C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V,
      Nonempty (SporadicFi24P3Definition44NamedCarrierOriginalDefinition41.Definition41Witness
        iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R C Cover D T)) ∨
    (∃ (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
       (hc : Subgroup.center X = ⊥),
      Nonempty (SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41.Definition41Witness
        iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R C Cover hc D T)) ∨
    (∃ (hc : Subgroup.center X = ⊥)
       (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
       (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi),
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi) ∧
      CenterlessDefinition41Data iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R hc Omega hOmega D T)

variable (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
variable (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X))

theorem raw_of_original
    (h : Nonempty (SporadicFi24P3Definition44NamedCarrierOriginalDefinition41.Definition41Witness
      iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover D T)) : RawDefinition41Certificate iota R Cover :=
  ⟨D, T, Or.inl ⟨C, h⟩⟩

theorem raw_of_canonical (hc : Subgroup.center X = ⊥)
    (h : Nonempty (SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41.Definition41Witness
      iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover hc D T)) : RawDefinition41Certificate iota R Cover :=
  ⟨D, T, Or.inr (Or.inl ⟨C, hc, h⟩)⟩

theorem raw_of_centerless_rows (hc : Subgroup.center X = ⊥)
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi)
    (h : CenterlessDefinition41Data iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R hc Omega hOmega D T) : RawDefinition41Certificate iota R Cover :=
  ⟨D, T, Or.inr (Or.inr ⟨hc, Omega, hOmega, hblock, h⟩)⟩

open ModularRep.PaperProofs.SpathRootCoherence
open ModularRep.PaperProofs.CoherentCenterlessRows

/-- Root compatibility for the specific original packets in a witness. -/
def OriginalWitnessRoots
    (W : SporadicFi24P3Definition44NamedCarrierOriginalDefinition41.Definition41Witness
      iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover D T) : Prop :=
  ∀ Q xi, OriginalPacketRoots (W.packets Q xi)

/-- Root compatibility for the specific embedded packets in a witness. -/
def CanonicalWitnessRoots {hc : Subgroup.center X = ⊥}
    (W : SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41.Definition41Witness
      iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover hc D T) : Prop :=
  ∀ Q xi, ActualPacketRoots (W.packets Q xi)

/-- A full certificate includes root agreement for every global and local
extension and every intermediate block calculation. The centreless
presentation requires the same agreement in its selected model witnesses. -/
def Definition41Certificate : Prop :=
  ∃ (D : DefectZeroReductionSource iota) (T : TrivialWeightSource (p := p) (X := X)),
    (∃ (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
       (W : SporadicFi24P3Definition44NamedCarrierOriginalDefinition41.Definition41Witness
        iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R C Cover D T), OriginalWitnessRoots iota R Cover C D T W) ∨
    (∃ (C : ∀ V : CharacterWeight p K X, CanonicalRawReduction iota V)
       (hc : Subgroup.center X = ⊥)
       (W : SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41.Definition41Witness
        iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R C Cover hc D T), CanonicalWitnessRoots iota R Cover C D T W) ∨
    (∃ (hc : Subgroup.center X = ⊥)
       (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
       (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi),
      (∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi) ∧
      CenterlessDefinition41Data iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R hc Omega hOmega D T ∧
      CoherentOriginalRowsOutput iota
        (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
        R hc Omega hOmega)

theorem of_original
    (W : SporadicFi24P3Definition44NamedCarrierOriginalDefinition41.Definition41Witness
      iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover D T)
    (roots : OriginalWitnessRoots iota R Cover C D T W) :
    Definition41Certificate iota R Cover :=
  ⟨D, T, Or.inl ⟨C, W, roots⟩⟩

theorem of_canonical (hc : Subgroup.center X = ⊥)
    (W : SporadicFi24P3Definition44NamedCarrierCanonicalDefinition41.Definition41Witness
      iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R C Cover hc D T)
    (roots : CanonicalWitnessRoots iota R Cover C D T W) :
    Definition41Certificate iota R Cover :=
  ⟨D, T, Or.inr (Or.inl ⟨C, hc, W, roots⟩)⟩

theorem of_centerless_rows (hc : Subgroup.center X = ⊥)
    (Omega : IBr iota ≃ WeightClass (p := p) (K := K) (X := X))
    (hOmega : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota), Omega (a • phi) = a • Omega phi)
    (hblock : ∀ phi, R.1.weightBlock (Omega phi) = operationsBlock iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) R phi)
    (h : CenterlessDefinition41Data iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R hc Omega hOmega D T)
    (roots : CoherentOriginalRowsOutput iota
      (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
      R hc Omega hOmega) : Definition41Certificate iota R Cover :=
  ⟨D, T, Or.inr (Or.inr ⟨hc, Omega, hOmega, hblock, h, roots⟩)⟩

theorem Definition41Certificate.toRaw
    (h : Definition41Certificate iota R Cover) : RawDefinition41Certificate iota R Cover := by
  obtain ⟨D, T, h⟩ := h
  rcases h with ⟨C, W, _⟩ | ⟨C, hc, W, _⟩ | ⟨hc, Omega, hOmega, hblock, h, _⟩
  · exact raw_of_original iota R Cover C D T ⟨W⟩
  · exact raw_of_canonical iota R Cover C D T hc ⟨W⟩
  · exact raw_of_centerless_rows iota R Cover D T hc Omega hOmega hblock h

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
