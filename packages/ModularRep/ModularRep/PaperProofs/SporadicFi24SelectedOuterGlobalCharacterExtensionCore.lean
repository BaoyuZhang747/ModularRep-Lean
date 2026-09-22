import ModularRep.SemidirectEmbeddedConjugation

/-!
# Bare global Brauer character extension

This module constructs the global character extension used by the selected
Fischer outer action.  The theorem is stated for an arbitrary cyclic outer
carrier and returns only a Brauer character extension witness.  It has no
block, weight, BAW, iBAW, or positive-radical conclusion.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtensionCore

open Formalisation
open ModularRep
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete

universe u

/-- A cyclic extension of the embedded base character gives a literal
ambient Brauer character extension when the two root lifts agree on the
prime regular roots of the embedded base. -/
theorem cyclicGlobalCharacterExtensionWitness
    {p : ℕ} {k K H E : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]
    (iota : PrimeRegularRootEmbedding p k K H)
    (phi : E →* MulAut H)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (psi : IBr iota) :
    let _ : MulAction H (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := IBr iota) phi
    let _ : MulAction (H ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ h : H,
        (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := fun h ↦ by
      rw [semidirect_inl_smul]
      exact inner_fixes_ibr iota h psi
    let eH := canonicalHToEmbeddedEquiv psi hinner
    ∀ (baseRoot : PrimeRegularRootEmbedding p k K
        (embeddedHStabilizer (phi := phi) psi))
      (baseBrauer : IBr baseRoot)
      (hbase : pullbackPrimeRegularAlongEquiv eH psi.1 = baseBrauer.1)
      (ambientRoot : PrimeRegularRootEmbedding p k K
        (semidirectStabilizer (phi := phi) psi))
      (rootAgreement :
        ∀ zeta : rootsOfUnity
            (primeRegularExponent p
              (embeddedHStabilizer (phi := phi) psi)) k,
          baseRoot.lift (((zeta : kˣ) : k)) =
            ambientRoot.lift (((zeta : kˣ) : k))),
      Nonempty
        (Representation.Extension.BrauerCharacterExtensionWitness
          ambientRoot baseRoot baseBrauer) := by
  dsimp only
  letI : MulAction H (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) phi
  let hcompat := rightAutomorphismSemidirectCompatible
    (X := IBr iota) phi
  letI : MulAction (H ⋊[phi] E) (IBr iota) :=
    semidirectMulAction phi hcompat
  have hinner : ∀ h : H,
      (SemidirectProduct.inl h : H ⋊[phi] E) • psi = psi := by
    intro h
    rw [semidirect_inl_smul]
    exact inner_fixes_ibr iota h psi
  let eH := canonicalHToEmbeddedEquiv psi hinner
  intro baseRoot baseBrauer hbase ambientRoot rootAgreement
  have pullbackIrreducible :
      IsIrreducibleBrauerCharacter baseRoot
        (pullbackPrimeRegularAlongEquiv eH psi.1) := by
    rw [hbase]
    exact baseBrauer.2
  obtain ⟨W, hW, hcharacter, ⟨extension⟩⟩ :=
    global_extension_actual iota phi principle psi baseRoot
      pullbackIrreducible
        (fun d x ↦ canonicalEmbedded_conjugationSquare
          phi psi hinner d x)
  have haffords :
      Representation.brauerCharacterOfRootEmbedding W.ρ baseRoot =
        baseBrauer.1 :=
    hcharacter.symm.trans hbase
  have rootCompatible :
      Representation.BrauerRootLiftCompatibleAlong
        extension.representation ambientRoot baseRoot
          (embeddedHStabilizer (phi := phi) psi).subtype :=
    Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      extension.representation ambientRoot baseRoot
        (embeddedHStabilizer (phi := phi) psi).subtype rootAgreement
  exact ⟨
    Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
      extension hW ambientRoot baseRoot baseBrauer haffords rootCompatible⟩

end ModularRep.PaperProofs.SporadicFi24SelectedOuterGlobalCharacterExtensionCore


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
