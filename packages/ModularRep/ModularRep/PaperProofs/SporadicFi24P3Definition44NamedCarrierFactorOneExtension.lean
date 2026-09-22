import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel
import ModularRep.BrauerCharacterHomPullback
import ModularRep.PrimeRegularRootEmbeddingSubgroup

/-! Recover an actual extension on the retained factor-one operators.
Only ambient root availability is needed for its Brauer realization. -/

noncomputable section
set_option maxHeartbeats 2000000

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension

open ModularRep
open SporadicFi24P3Definition44NamedCarrierAssociatedProjectiveModel

universe u
variable {k A V : Type u} [Field k] [Group A] [AddCommGroup V] [Module k V]
variable {B : Subgroup A} [B.Normal] {rho : Representation k B V}

def representationOfFactorOne (M : AssociatedProjectiveModel B rho)
    (hM : M.factorSet = ScalarFactorSet.trivial) : Representation k A V where
  toFun := M.operator
  map_one' := M.operator_one
  map_mul' a b := by
    have h := M.operator_mul a b
    rw [hM] at h
    simpa only [ScalarFactorSet.trivial, Units.val_one, one_smul] using h.symm

def extensionOfFactorOne (M : AssociatedProjectiveModel B rho)
    (hM : M.factorSet = ScalarFactorSet.trivial) : Representation.Extension B rho where
  representation := representationOfFactorOne M hM
  restrictionEquiv := Representation.Equiv.mk (LinearEquiv.refl k V) (by
    intro b
    ext v
    change M.operator b v = rho b v
    rw [M.restriction])

theorem extensionOfFactorOne_operator (M : AssociatedProjectiveModel B rho)
    (hM : M.factorSet = ScalarFactorSet.trivial) (a : A) :
    (extensionOfFactorOne M hM).representation a = M.operator a := rfl

variable {p : ℕ} {K : Type u} [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Finite A] [FiniteDimensional k V]

def brauerExtensionOfFactorOne
    (M : AssociatedProjectiveModel B rho) (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (rA : PrimeRegularRootEmbedding p k K A) (rB : PrimeRegularRootEmbedding p k K B)
    (phiB : IBr rB) (haffords : rho.brauerCharacterOfRootEmbedding rB = phiB.val)
    (hroots : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) :
    Representation.Extension.BrauerCharacterExtensionWitness rA rB phiB :=
  Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    (extensionOfFactorOne M hM) hirr rA rB phiB haffords
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      (representationOfFactorOne M hM) rA rB B.subtype hroots)

/-- The exact global character is formed from the original model operators. -/
theorem exists_brauer_extension_of_factor_one
    (M : AssociatedProjectiveModel B rho) (hM : M.factorSet = ScalarFactorSet.trivial)
    (hirr : Representation.IsIrreducible rho)
    (rB : PrimeRegularRootEmbedding p k K B) (phiB : IBr rB)
    (haffords : rho.brauerCharacterOfRootEmbedding rB = phiB.val)
    (seed : Nonempty (PrimeRegularRootEmbedding p k K A)) :
    ∃ rA : PrimeRegularRootEmbedding p k K A,
      (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
        rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      ∃ W : Representation.Extension.BrauerCharacterExtensionWitness rA rB phiB,
        W.val.val = (representationOfFactorOne M hM).brauerCharacterOfRootEmbedding rA := by
  obtain ⟨rA, hroots⟩ := PrimeRegularRootEmbedding.exists_ambient_agreeing_on_subgroup B rB seed
  let W := brauerExtensionOfFactorOne M hM hirr rA rB phiB haffords hroots
  exact ⟨rA, hroots, W, rfl⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFactorOneExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
