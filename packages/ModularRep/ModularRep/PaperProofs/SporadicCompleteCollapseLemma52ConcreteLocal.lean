import ModularRep.IrreducibleBrauerCharacter
import ModularRep.OrdinaryIrreducibleCharacter
import ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative
import ModularRep.Weight

/-!
# Concrete local-character bridge for manuscript Lemma 5.2

This file replaces the carrier-level reduction and inflation maps in
`SporadicCompleteCollapseLemma52Relative` by the library's actual
function-valued ordinary and Brauer characters.

Let `Q` be normal in a finite group `L`.  An ordinary character of `L / Q`
is inflated by pulling an affording representation back along the quotient
map.  A prime regular class function is inflated by literal pullback along
the same map.  The exact E1 inputs are deliberately narrow:

* Navarro, Theorem (3.18), supplies an irreducible Brauer character equal to
  the reduction of the defect-zero ordinary character on `L / Q`;
* the routine Brauer inflation theorem supplies that the literal pullback of
  this Brauer character is irreducible for `L`.

From those inputs Lean proves that the literal inflated Brauer character is
the reduction of the literal inflated ordinary character.  It then places
that actual `IBr` object in the local identity-extension slot and performs
the quotient-centre and one-intermediate-group collapse.  No extension,
block equality, character-triple relation, BAW-goodness, or iBAW conclusion
is a field of the reduction-and-inflation input.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal

open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative

universe u

section CharacterInfrastructure

variable {p : ℕ} {k K H L : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group H] [Finite H] [Group L] [Finite L]

/-- An actual ordinary irreducible character has defect zero when one of its
affording irreducible representations has the full `p`-part in its degree.
The equality is the character version of `IsDefectZeroRepresentation`. -/
def IsDefectZeroOrdinaryCharacter
    (theta : Irr K H) : Prop :=
  ∃ R : Realisation K H theta.1,
    ordProj[p] R.dimension = ordProj[p] (Nat.card H)

/-- The actual function-valued carrier of defect-zero ordinary irreducible
characters. -/
abbrev DefectZeroIrr :=
  {theta : Irr K H // IsDefectZeroOrdinaryCharacter (p := p) theta}

/-- Equality of an ordinary character restricted to the `p`-regular
elements with an irreducible Brauer character.  This is the literal typed
meaning of `theta^0 = phi`. -/
def IsBrauerReduction
    (iota : PrimeRegularRootEmbedding p k K H)
    (theta : Irr K H) (phi : IBr iota) : Prop :=
  ∀ g : PrimeRegularElement (G := H) p, theta g.1 = phi.1 g

/-- Pull a prime regular class function back along a group homomorphism.
This is the function-level inflation operation when the homomorphism is a
quotient map. -/
def pullbackPrimeRegularClassFunction
    (f : L →* H) (phi : PrimeRegularClassFunction K H p) :
    PrimeRegularClassFunction K L p where
  toFun := phi.toFun.pullback f
  map_conj x g := by
    change phi (PrimeRegularElement.map f
      ⟨x * g.1 * x⁻¹, g.2.conj x⟩) =
        phi (PrimeRegularElement.map f g)
    have hmap :
        PrimeRegularElement.map f
            ⟨x * g.1 * x⁻¹, g.2.conj x⟩ =
          ⟨f x * (PrimeRegularElement.map f g).1 * (f x)⁻¹,
            (PrimeRegularElement.map f g).2.conj (f x)⟩ := by
      apply Subtype.ext
      change f (x * g.1 * x⁻¹) = f x * f g.1 * (f x)⁻¹
      simp
    rw [hmap]
    exact phi.map_conj (f x) (PrimeRegularElement.map f g)

omit [Field K] [CharZero K] [Finite H] [Finite L] in
@[simp]
theorem pullbackPrimeRegularClassFunction_apply
    (f : L →* H) (phi : PrimeRegularClassFunction K H p)
    (g : PrimeRegularElement (G := L) p) :
    pullbackPrimeRegularClassFunction f phi g =
      phi (PrimeRegularElement.map f g) :=
  rfl

variable (Q : Subgroup L) [Q.Normal]

/-- Inflate an actual ordinary irreducible character from `L / Q` to `L`.
Irreducibility follows in the kernel from surjectivity of the quotient map. -/
def inflateOrdinaryCharacter
    (theta : Irr K (L ⧸ Q)) : Irr K L := by
  refine ⟨fun x ↦ theta (QuotientGroup.mk' Q x), ?_⟩
  rcases theta.2 with ⟨R⟩
  refine ⟨{
    dimension := R.dimension
    representation := R.representation.pullback (QuotientGroup.mk' Q)
    irreducible := R.irreducible.pullback (QuotientGroup.mk' Q)
      (QuotientGroup.mk'_surjective Q)
    character_eq := ?_ }⟩
  funext x
  change R.representation.character (QuotientGroup.mk' Q x) =
    theta (QuotientGroup.mk' Q x)
  exact congrFun R.character_eq (QuotientGroup.mk' Q x)

omit [CharZero K] [Finite L] in
@[simp]
theorem inflateOrdinaryCharacter_apply
    (theta : Irr K (L ⧸ Q)) (x : L) :
    inflateOrdinaryCharacter Q theta x = theta (QuotientGroup.mk' Q x) :=
  rfl

end CharacterInfrastructure

section ConcreteReductionInflation

variable {p : ℕ} {k K L : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group L] [Finite L]
  (Q : Subgroup L) [Q.Normal]
  (iotaQuotient : PrimeRegularRootEmbedding p k K (L ⧸ Q))
  (iotaLocal : PrimeRegularRootEmbedding p k K L)
  (theta : DefectZeroIrr (p := p) (K := K) (H := L ⧸ Q))

/-- Exact source-shaped inputs for the local reduction and inflation.

`quotientReduction` is Navarro (3.18) on `L / Q`.  The final field is the
routine E1 assertion that inflation of this irreducible Brauer character is
again irreducible.  Its class function is not abstract: it is literally the
pullback along `QuotientGroup.mk' Q`. -/
structure ConcreteDefectZeroReductionInflation where
  quotientBrauer : IBr iotaQuotient
  quotientReduction :
    IsBrauerReduction iotaQuotient theta.1 quotientBrauer
  inflatedBrauerIrreducible :
    IsIrreducibleBrauerCharacter iotaLocal
      (pullbackPrimeRegularClassFunction (QuotientGroup.mk' Q)
        quotientBrauer.1)

namespace ConcreteDefectZeroReductionInflation

/-- The actual irreducible Brauer character of `L` required in Späth's local
extension clause. -/
def localBrauer
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta) :
    IBr iotaLocal :=
  ⟨pullbackPrimeRegularClassFunction (QuotientGroup.mk' Q)
      D.quotientBrauer.1,
    D.inflatedBrauerIrreducible⟩

@[simp]
theorem localBrauer_val
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta) :
    D.localBrauer.1 =
      pullbackPrimeRegularClassFunction (QuotientGroup.mk' Q)
        D.quotientBrauer.1 :=
  rfl

/-- The manuscript-specific composition step: reduction on `L / Q` and
literal inflation imply that the local Brauer character is the Brauer
reduction of the inflated ordinary character on `L`. -/
theorem localBrauer_isReductionOf_inflateOrdinary
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta) :
    IsBrauerReduction iotaLocal
      (inflateOrdinaryCharacter Q theta.1) D.localBrauer := by
  intro g
  exact D.quotientReduction
    (PrimeRegularElement.map (QuotientGroup.mk' Q) g)

/-- The correctly typed identity extension pair with an arbitrary global
Brauer object and the actual local `IBr` object constructed above. -/
def identityExtensionPair
    {GlobalBrauer : Type u}
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta)
    (global : GlobalBrauer) :
    IdentityExtensionPair global D.localBrauer :=
  ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative.identityExtensionPair
    (GlobalBrauer := GlobalBrauer) (LocalBrauer := IBr iotaLocal)
    global D.localBrauer

@[simp]
theorem identityExtensionPair_localExtension
    {GlobalBrauer : Type u}
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta)
    (global : GlobalBrauer) :
    (identityExtensionPair Q iotaQuotient iotaLocal theta D global).localExtension =
      D.localBrauer :=
  rfl

end ConcreteDefectZeroReductionInflation

end ConcreteReductionInflation

section ConcreteIdentityCollapse

variable {p : ℕ} {k K L X AutStabilizer GlobalBrauer : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group L] [Finite L]
  [Group X] [Group.IsPerfect X] [Group AutStabilizer]
  (Q : Subgroup L) [Q.Normal]
  (iotaQuotient : PrimeRegularRootEmbedding p k K (L ⧸ Q))
  (iotaLocal : PrimeRegularRootEmbedding p k K L)
  (theta : DefectZeroIrr (p := p) (K := K) (H := L ⧸ Q))

/-- Strongest concrete non-character-triple endpoint for the local part of
Lemma 5.2.  It retains both the proof that the actual local `IBr` object is
the reduction of the inflated ordinary character and the full structural
identity-collapse witness. -/
structure ConcreteLocalClauseIIIResult
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta)
    (Z0 : Subgroup X) [Z0.Normal]
    (CentrePrimeTo : Prop) (global : GlobalBrauer)
    (Qbar : Subgroup (X ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (X ⧸ Z0) → Prop) where
  localReduction : IsBrauerReduction iotaLocal
    (inflateOrdinaryCharacter Q theta.1) D.localBrauer
  clauseIII :
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative.IdentityClauseIIIWitness
      (G := X) (GlobalBrauer := GlobalBrauer)
      (LocalBrauer := IBr iotaLocal) Z0 AutStabilizer CentrePrimeTo
      global D.localBrauer Qbar IntermediateBlockEquality

/-- Combine the actual local character with the quotient-centre,
identity-extension, and one-intermediate-group deductions.  The conclusion
does not include a character-triple or iBAW assertion. -/
def concreteLocalClauseIIIResult
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta)
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center X)
    (innerStabilizer :
      (X ⧸ Subgroup.center X) ≃* AutStabilizer)
    (centrePrimeTo : Prop) (hCentrePrimeTo : centrePrimeTo)
    (global : GlobalBrauer)
    (Qbar : Subgroup (X ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (X ⧸ Z0) → Prop)
    (hNormaliser : IntermediateBlockEquality
      (Subgroup.normalizer (Qbar : Set (X ⧸ Z0)))) :
    ConcreteLocalClauseIIIResult (X := X) (AutStabilizer := AutStabilizer)
      (GlobalBrauer := GlobalBrauer) Q iotaQuotient iotaLocal theta D Z0
      centrePrimeTo global Qbar IntermediateBlockEquality where
  localReduction := D.localBrauer_isReductionOf_inflateOrdinary
  clauseIII :=
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52Relative.identityClauseIIIWitness
      (G := X) (AutStabilizer := AutStabilizer)
      (GlobalBrauer := GlobalBrauer) (LocalBrauer := IBr iotaLocal)
      Z0 hZ0 innerStabilizer centrePrimeTo hCentrePrimeTo global
      D.localBrauer Qbar IntermediateBlockEquality hNormaliser

@[simp]
theorem concreteLocalClauseIIIResult_localExtension
    (D : ConcreteDefectZeroReductionInflation Q iotaQuotient iotaLocal theta)
    (Z0 : Subgroup X) [Z0.Normal]
    (hZ0 : Z0 ≤ Subgroup.center X)
    (innerStabilizer :
      (X ⧸ Subgroup.center X) ≃* AutStabilizer)
    (centrePrimeTo : Prop) (hCentrePrimeTo : centrePrimeTo)
    (global : GlobalBrauer)
    (Qbar : Subgroup (X ⧸ Z0))
    (IntermediateBlockEquality : Subgroup (X ⧸ Z0) → Prop)
    (hNormaliser : IntermediateBlockEquality
      (Subgroup.normalizer (Qbar : Set (X ⧸ Z0)))) :
    (concreteLocalClauseIIIResult (X := X) (AutStabilizer := AutStabilizer)
      (GlobalBrauer := GlobalBrauer) Q iotaQuotient iotaLocal theta D Z0
      hZ0 innerStabilizer centrePrimeTo hCentrePrimeTo global Qbar
      IntermediateBlockEquality hNormaliser).clauseIII.extensions.localExtension =
        D.localBrauer :=
  rfl

end ConcreteIdentityCollapse

end ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
