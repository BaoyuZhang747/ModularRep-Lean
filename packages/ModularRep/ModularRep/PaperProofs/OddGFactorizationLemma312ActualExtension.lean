import ModularRep.BrauerCharacterEquivTransport
import ModularRep.PaperProofs.CyclicOuterLemma37Concrete
import ModularRep.SemidirectEmbeddedConjugation

/-!
# Actual-carrier extension endpoint for manuscript Lemma 3.12

This module proves the final cyclic-extension deduction in Lemma 3.12 on
function-valued irreducible Brauer characters.  The actions are the canonical
right actions induced by inner and field automorphisms.  The copy of the base
group inside the character stabiliser, its root embedding, the transported
Brauer character, and the conjugation square are all constructed in the
kernel.

The only representation theoretic input is Navarro's cyclic-extension
principle.  No supplied character transport, stabiliser transport, extension,
BAW-goodness, iBAW condition, or conclusion of Lemma 3.12 is an input.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddGFactorizationLemma312ActualExtension

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

universe u

/-- The cyclic-extension conclusion of Lemma 3.12 on the literal `IBr`
carrier.

The homomorphism `phi` is the canonical field-automorphism action supplied by
the routine group structure.  Lean constructs the normal-factor equivalence
and transports both the root embedding and `psi` along it. -/
theorem lemma_3_12_cyclic_extension_actual
    {p : ℕ} {D E k K : Type u}
    [Group D] [Finite D] [Group E] [Finite E] [IsCyclic E]
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding p k K D)
    (phi : E →* MulAut D)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u}
      p k)
    (psi : IBr iota) :
    let _ : MulAction D (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : D →* MulAut D)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := IBr iota) phi
    let _ : MulAction (D ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ d : D,
        (SemidirectProduct.inl d : D ⋊[phi] E) • psi = psi := fun d ↦ by
      rw [semidirect_inl_smul]
      exact inner_fixes_ibr iota d psi
    let eD := canonicalHToEmbeddedEquiv psi hinner
    let iotaEmbedded := iota.alongMulEquiv eD
    let psiEmbedded := IrreducibleBrauerCharacter.alongMulEquiv iota eD psi
    ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
      Representation.IsIrreducible W.ρ ∧
      psiEmbedded.1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
      Nonempty (Representation.Extension
        (embeddedHStabilizer (phi := phi) psi) W.ρ) := by
  dsimp only
  letI : MulAction D (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : D →* MulAut D)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) phi
  have hcompat : SemidirectActionCompatible (X := IBr iota) phi :=
    rightAutomorphismSemidirectCompatible (X := IBr iota) phi
  letI : MulAction (D ⋊[phi] E) (IBr iota) :=
    semidirectMulAction phi hcompat
  have hinner : ∀ d : D,
      (SemidirectProduct.inl d : D ⋊[phi] E) • psi = psi := by
    intro d
    rw [semidirect_inl_smul]
    exact inner_fixes_ibr iota d psi
  let eD := canonicalHToEmbeddedEquiv psi hinner
  let iotaEmbedded := iota.alongMulEquiv eD
  have hpullback : pullbackPrimeRegularAlongEquiv eD psi.1 =
      PrimeRegularClassFunction.pullback eD.symm.toMonoidHom psi.1 := by
    apply PrimeRegularClassFunction.ext
    intro x
    rfl
  have pullbackIrreducible : IsIrreducibleBrauerCharacter iotaEmbedded
      (pullbackPrimeRegularAlongEquiv eD psi.1) := by
    rw [hpullback]
    exact IrreducibleBrauerCharacter.pullback_isIrreducibleBrauerCharacter
      iota eD psi
  obtain ⟨W, hW, hcharacter, hextension⟩ :=
    global_extension_actual iota phi principle psi iotaEmbedded
      pullbackIrreducible (fun d x ↦
        canonicalEmbedded_conjugationSquare
          (phi := phi) psi hinner d x)
  refine ⟨W, hW, ?_, hextension⟩
  have htransport :
      (IrreducibleBrauerCharacter.alongMulEquiv iota eD psi).1 =
        pullbackPrimeRegularAlongEquiv eD psi.1 := by
    rw [IrreducibleBrauerCharacter.alongMulEquiv_val, hpullback]
  exact htransport.trans hcharacter

end ModularRep.PaperProofs.OddGFactorizationLemma312ActualExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
