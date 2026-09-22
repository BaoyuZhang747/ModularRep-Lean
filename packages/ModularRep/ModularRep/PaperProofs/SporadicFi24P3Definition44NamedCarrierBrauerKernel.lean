import ModularRep.BrauerCharacterSeparation

/-! Kernels of actual irreducible representations are determined by their
Brauer characters for the same root convention. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerKernel

open CategoryTheory
open ModularRep.FDRepSimpleClassKZero

universe u v

theorem fdRep_ker_eq_of_iso {k G : Type u} [Field k] [Group G]
    {V W : FDRep k G} (e : V ≅ W) : V.ρ.ker = W.ρ.ker := by
  ext g
  change V.ρ g = 1 ↔ W.ρ g = 1
  constructor
  · intro h
    rw [FDRep.Iso.conj_ρ e g, h]
    ext w
    simp [LinearEquiv.conj_apply]
  · intro h
    rw [FDRep.Iso.conj_ρ e.symm g, h]
    ext v
    simp [LinearEquiv.conj_apply]

theorem fdRep_ker_eq_of_brauer_eq
    {p : ℕ} {k G : Type u} {K : Type v}
    [Field k] [Field K] [Group G] [Finite G]
    [CharP k p] [IsAlgClosed k] [CharZero K]
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (V W : FDRep k G)
    (hV : Representation.IsIrreducible V.ρ)
    (hW : Representation.IsIrreducible W.ρ)
    (h : Representation.brauerCharacterOfRootEmbedding V.ρ iota =
      Representation.brauerCharacterOfRootEmbedding W.ρ iota) :
    V.ρ.ker = W.ρ.ker := by
  obtain ⟨e⟩ := irreducibleModularTraceDeterminesRepresentation V W hV hW
    (brauerCharacterDeterminesModularTrace_of_rootEmbedding iota V W h)
  exact fdRep_ker_eq_of_iso e

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierBrauerKernel



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
