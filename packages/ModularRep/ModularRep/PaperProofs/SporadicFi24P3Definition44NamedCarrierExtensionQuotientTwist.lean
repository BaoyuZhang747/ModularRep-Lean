import ModularRep.NavarroBrauerRestrictionCovering

/-! The selected extension need not be afforded by the earlier global
model. Its precise quotient-linear character change is derived from the
existing cyclic source while its base character remains fixed. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierExtensionQuotientTwist

open ModularRep ModularRep.NavarroCoveringBrauerExtension
open Representation.Extension

universe u

theorem quotient_twist_between_extensions
    {p : ℕ} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Fintype A]
    (S820 : Navarro820CyclicBrauerTwistPrinciple p k K)
    (B : Subgroup A) [B.Normal]
    (rA : PrimeRegularRootEmbedding p k K A)
    (rB : PrimeRegularRootEmbedding p k K B)
    (hroots : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k)))
    (hcyclic : IsCyclic (A ⧸ B)) (phiB : IBr rB)
    (initialGlobal selectedGlobal : BrauerCharacterExtensionWitness rA rB phiB) :
    ∃ lambda : (A ⧸ B) →* Kˣ,
      ∀ x : PrimeRegularElement (G := A) p,
        selectedGlobal.val.val x =
          (lambda (QuotientGroup.mk' B x.val) : K) * initialGlobal.val.val x := by
  exact S820 B rA rB hroots hcyclic phiB initialGlobal selectedGlobal.val
    (NavarroBrauerRestrictionCovering.brauerOccursInRestriction_of_pullback_eq
      B rA rB selectedGlobal.val phiB selectedGlobal.property)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierExtensionQuotientTwist


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
