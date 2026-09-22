import ModularRep.BrauerCharacterSeparation
import ModularRep.CyclicExtension

/-!
# From Brauer-character invariance to cyclic extension

This file formalises the bridge used in the manuscript when a field
stabiliser fixes an irreducible Brauer character.  Equality of the
function-valued Brauer characters first gives equality of modular trace
functions.  Trace separation then identifies the conjugate representation
with the original representation.  The cyclic-extension theorem can
therefore be applied at representation level.

The cyclic-extension theorem itself remains an explicit external input,
represented by `Representation.CyclicExtensionPrinciple`.  No assumption
below states conjugation invariance or the existence of an extension.
-/

noncomputable section

namespace Representation

universe u v

variable {p : ℕ} {k : Type u} {K : Type v}
variable {H V : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {N : Subgroup H} [N.Normal]

/-- If every ambient conjugation fixes the function-valued Brauer character
of an irreducible representation, then the representation is invariant under
ambient conjugation.  The conclusion is obtained from Brauer-character
recovery and trace separation, rather than supplied as an input. -/
theorem conjugationInvariant_of_brauerCharacter_fixed
    (iota : ModularRep.PrimeRegularRootEmbedding p k K N)
    (rho : Representation k N V)
    (hirr : Representation.IsIrreducible rho)
    (hfixed : ∀ h : H,
      (rho.brauerCharacterOfRootEmbedding iota).twist
          (MulAut.conjNormal h) =
        rho.brauerCharacterOfRootEmbedding iota) :
    ConjugationInvariant N rho := by
  intro h
  apply ModularRep.ModularTraceSeparation.representation_equiv_of_character_eq
    (rho.twist (MulAut.conjNormal h)) rho
    (hirr.twist (MulAut.conjNormal h)) hirr
  have hchar :=
    ModularRep.FDRepSimpleClassKZero.brauerCharacterDeterminesModularTrace_of_rootEmbedding iota
      (FDRep.of (rho.twist (MulAut.conjNormal h))) (FDRep.of rho) (by
        simp only [FDRep.of_ρ', brauerCharacterOfRootEmbedding_twist]
        exact hfixed h)
  simpa only [FDRep.of_ρ'] using hchar

/-- A fixed element of the function-valued set `IBr` has an irreducible
representation realisation which is invariant under ambient conjugation.
The representation is extracted from the defining witness for `IBr`; its
invariance is then proved by the preceding theorem. -/
theorem exists_conjugationInvariant_realisation_of_ibr_fixed
    (iota : ModularRep.PrimeRegularRootEmbedding p k K N)
    (phi : ModularRep.IBr iota)
    (hfixed : ∀ h : H,
      ModularRep.IrreducibleBrauerCharacter.twist iota phi
          (MulAut.conjNormal h) = phi) :
    ∃ W : FDRep k N,
      Representation.IsIrreducible W.ρ ∧
      phi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
      ConjugationInvariant N W.ρ := by
  rcases phi.2 with ⟨W, hW, hphi⟩
  refine ⟨W, hW, hphi, ?_⟩
  apply conjugationInvariant_of_brauerCharacter_fixed iota W.ρ hW
  intro h
  calc
    (Representation.brauerCharacterOfRootEmbedding W.ρ iota).twist
        (MulAut.conjNormal h) =
        phi.1.twist (MulAut.conjNormal h) :=
      congrArg
        (fun f : ModularRep.PrimeRegularClassFunction K N p ↦
          f.twist (MulAut.conjNormal h)) hphi.symm
    _ = (ModularRep.IrreducibleBrauerCharacter.twist iota phi
          (MulAut.conjNormal h)).1 := rfl
    _ = phi.1 := congrArg Subtype.val (hfixed h)
    _ = Representation.brauerCharacterOfRootEmbedding W.ρ iota := hphi

/-- A fixed irreducible Brauer character extends across a cyclic quotient,
conditional only on the cited cyclic-extension principle. -/
theorem exists_extension_of_brauerCharacter_fixed_cyclic_quotient
    (principle : BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K N)
    (rho : Representation k N V)
    (hirr : Representation.IsIrreducible rho)
    (hcyclic : IsCyclic (H ⧸ N))
    (hfixed : ∀ h : H,
      (rho.brauerCharacterOfRootEmbedding iota).twist
          (MulAut.conjNormal h) =
        rho.brauerCharacterOfRootEmbedding iota) :
    Nonempty (Extension N rho) :=
  exists_extension_of_cyclic_quotient principle rho hirr hcyclic
    (conjugationInvariant_of_brauerCharacter_fixed iota rho hirr hfixed)

/-- Character-level form of the cyclic-extension application.  Starting
from a fixed irreducible Brauer character, Lean chooses a representation
affording it, proves that representation invariant, and applies the exact
Navarro (8.12) input. -/
theorem exists_extension_realisation_of_ibr_fixed_cyclic_quotient
    (principle : BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K N)
    (phi : ModularRep.IBr iota)
    (hcyclic : IsCyclic (H ⧸ N))
    (hfixed : ∀ h : H,
      ModularRep.IrreducibleBrauerCharacter.twist iota phi
          (MulAut.conjNormal h) = phi) :
    ∃ W : FDRep k N,
      Representation.IsIrreducible W.ρ ∧
      phi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
      Nonempty (Extension N W.ρ) := by
  obtain ⟨W, hW, hphi, hinvariant⟩ :=
    exists_conjugationInvariant_realisation_of_ibr_fixed iota phi hfixed
  exact ⟨W, hW, hphi,
    exists_extension_of_cyclic_quotient
      principle W.ρ hW hcyclic hinvariant⟩

private noncomputable instance finiteSemidirectProduct
    {D E : Type u} [Group D] [Finite D] [Group E] [Finite E]
    (phi : E →* MulAut D) : Finite (D ⋊[phi] E) :=
  Finite.of_injective
    (fun x : D ⋊[phi] E ↦ (x.left, x.right)) (by
      intro x y h
      exact SemidirectProduct.ext
        (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- Semidirect-product form of the preceding theorem.  Lean constructs the
cyclic quotient from the right projection and derives representation
invariance from fixedness of the Brauer character. -/
theorem exists_extension_to_semidirect_of_brauerCharacter_fixed
    (principle : BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    {D E : Type u} [Group D] [Finite D]
    [Group E] [Finite E] [IsCyclic E]
    (phi : E →* MulAut D)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K
      (SemidirectProduct.rightHom (φ := phi)).ker)
    (rho : Representation k
      (SemidirectProduct.rightHom (φ := phi)).ker V)
    (hirr : Representation.IsIrreducible rho)
    (hfixed : ∀ h : D ⋊[phi] E,
      (rho.brauerCharacterOfRootEmbedding iota).twist
          (MulAut.conjNormal h) =
        rho.brauerCharacterOfRootEmbedding iota) :
    Nonempty (Extension
      (SemidirectProduct.rightHom (φ := phi)).ker rho) :=
  exists_extension_to_semidirect_of_cyclic_outer principle phi rho hirr
    (conjugationInvariant_of_brauerCharacter_fixed iota rho hirr hfixed)

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
