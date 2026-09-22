import ModularRep.PaperProofs.SporadicFi24SelectedOuterBrauerCarrier
import ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtensionCore

/-!
# Bare global extension for the selected Fischer outer carrier

The selected square-one carrier is specialised here to the generic cyclic
Brauer extension theorem.  The conclusion is only a character extension
witness over a supplied ambient root.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterBareGlobalExtension

open Formalisation
open ModularRep
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.SporadicFi24SelectedOuterBrauerCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtensionCore
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

/-- Construct the bare global extension witness for the selected outer
carrier from source-root agreement. -/
theorem selectedGlobalCharacterExtensionWitness
    {p : ℕ} {k K X : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group X] [Finite X]
    (iota : PrimeRegularRootEmbedding p k K X)
    (S : SelectedOuterInvolutionCarrier X)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (psi : IBr iota)
    (baseRoot : PrimeRegularRootEmbedding p k K
      (SelectedBrauerBase iota S psi))
    (baseBrauer : IBr baseRoot)
    (hbase :
      pullbackPrimeRegularAlongEquiv
          (selectedGroupEquivBase iota S psi) psi.1 =
        baseBrauer.1)
    (ambientRoot : PrimeRegularRootEmbedding p k K
      (SelectedBrauerAmbient iota S psi))
    (rootAgreement :
      ∀ zeta : rootsOfUnity
          (primeRegularExponent p (SelectedBrauerBase iota S psi)) k,
        baseRoot.lift (((zeta : kˣ) : k)) =
          ambientRoot.lift (((zeta : kˣ) : k))) :
    Nonempty
      (Representation.Extension.BrauerCharacterExtensionWitness
        ambientRoot baseRoot baseBrauer) := by
  let _ : MulAction (SelectedOuterAmbient S) (IBr iota) :=
    selectedBrauerSemidirectAction iota S
  exact cyclicGlobalCharacterExtensionWitness
    iota (selectedOuterField S) principle psi
      baseRoot baseBrauer hbase ambientRoot rootAgreement

end ModularRep.PaperProofs.SporadicFi24SelectedOuterBareGlobalExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
