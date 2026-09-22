import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoExtension
import ModularRep.BrauerCharacterExtensionBridge

/-! Extend the actual affording representation supplied by Brauer invariance. -/

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoBrauerExtension

open Representation
open SporadicFi24P3Definition44NamedCarrierIndexTwoExtension

universe u v

theorem exists_extension_realisation_of_ibr_fixed_quotient_card_le_two
    {p : ℕ} {k H : Type u} {K : Type v}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group H] [Finite H] {N : Subgroup H} [N.Normal]
    (iota : PrimeRegularRootEmbedding p k K N) (phi : IBr iota)
    (hcard : Nat.card (H ⧸ N) ≤ 2)
    (hfixed : ∀ h : H,
      IrreducibleBrauerCharacter.twist iota phi (MulAut.conjNormal h) = phi) :
    ∃ W : FDRep k N, Representation.IsIrreducible W.ρ ∧
      phi.val = Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
      Nonempty (Extension N W.ρ) := by
  obtain ⟨W, hW, hchar, hinvariant⟩ :=
    exists_conjugationInvariant_realisation_of_ibr_fixed iota phi hfixed
  exact ⟨W, hW, hchar,
    exists_extension_of_quotient_card_le_two W.ρ hW hcard hinvariant⟩

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierIndexTwoBrauerExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
