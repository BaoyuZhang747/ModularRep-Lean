import ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier

/-!
# Brauer stabiliser for the selected square-one outer action

This file constructs only the semidirect action on irreducible Brauer
characters, its stabiliser, and the canonical embedded normal factor.  It
does not depend on literal block data or any inductive-condition endpoint.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterBrauerCarrier

open Formalisation
open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.SporadicFi24SelectedOuterInvolutionCarrier

universe u

noncomputable local instance selectedOuterFinite
    {X : Type u} [Group X] [Finite X]
    (S : SelectedOuterInvolutionCarrier X) :
    Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : X → X))
    (fun _a _b h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

noncomputable local instance selectedAmbientFinite
    {X : Type u} [Group X] [Finite X]
    (S : SelectedOuterInvolutionCarrier X) :
    Finite (SelectedOuterAmbient S) :=
  Finite.of_injective
    (fun g : SelectedOuterAmbient S ↦ (g.left, g.right)) (by
      intro a b hab
      exact SemidirectProduct.ext
        (congrArg Prod.fst hab) (congrArg Prod.snd hab))

/-- The canonical right action of the selected semidirect product on
irreducible Brauer characters. -/
@[instance_reducible]
def selectedBrauerSemidirectAction
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : SelectedOuterInvolutionCarrier X) :
    MulAction (SelectedOuterAmbient S) (IBr iota) := by
  letI : MulAction X (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : X →* MulAut X)
  letI : MulAction (SelectedOuterGroup S) (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) (selectedOuterField S)
  exact semidirectMulAction (selectedOuterField S)
    (rightAutomorphismSemidirectCompatible
      (X := IBr iota) (selectedOuterField S))

/-- The stabiliser of one irreducible Brauer character. -/
abbrev SelectedBrauerAmbient
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : SelectedOuterInvolutionCarrier X)
    (psi : IBr iota) :=
  @semidirectStabilizer X _ (SelectedOuterGroup S) (IBr iota) _
    (selectedOuterField S) (selectedBrauerSemidirectAction iota S) psi

/-- The embedded stabiliser of the normal factor. -/
def SelectedBrauerBase
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : SelectedOuterInvolutionCarrier X)
    (psi : IBr iota) :
    Subgroup (SelectedBrauerAmbient iota S psi) :=
  @embeddedHStabilizer X _ (SelectedOuterGroup S) (IBr iota) _
    (selectedOuterField S) (selectedBrauerSemidirectAction iota S) psi

/-- Every element of the normal factor fixes an irreducible Brauer
character. -/
theorem selectedBrauer_inner_fixed
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : SelectedOuterInvolutionCarrier X)
    (psi : IBr iota) (x : X) :
    let _ : MulAction (SelectedOuterAmbient S) (IBr iota) :=
      selectedBrauerSemidirectAction iota S
    (SemidirectProduct.inl x : SelectedOuterAmbient S) • psi = psi := by
  dsimp only
  change IrreducibleBrauerCharacter.twist iota psi (MulAut.conj x⁻¹) = psi
  exact inner_fixes_ibr iota x psi

/-- The original group is canonically equivalent to its embedded stabiliser
inside the selected Brauer stabiliser. -/
def selectedGroupEquivBase
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : SelectedOuterInvolutionCarrier X)
    (psi : IBr iota) :
    X ≃* SelectedBrauerBase iota S psi :=
  @canonicalHToEmbeddedEquiv X (SelectedOuterGroup S) (IBr iota)
    _ _ (selectedOuterField S) (selectedBrauerSemidirectAction iota S)
    psi (selectedBrauer_inner_fixed iota S psi)

end ModularRep.PaperProofs.SporadicFi24SelectedOuterBrauerCarrier


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
