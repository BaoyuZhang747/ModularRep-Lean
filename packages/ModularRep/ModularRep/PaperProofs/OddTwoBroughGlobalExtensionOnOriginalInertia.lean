import ModularRep.PaperProofs.OddTwoBroughGlobalBrauerExtension

/-!
# Extensions on the original actual inertia group

BS4.6(i) extends every conformal translate to the ORIGINAL two inertia
groups. Here the base root, base embedding and ambient group are fixed by
the original character. Only the base character changes. The actual
stabilizer equality supplies membership in the new character's inertia;
the existing conjugation square then proves fixedness on the original
base. Navarro8.12 applies with the same compatible ambient root.

There is no substitution of a different group or independently chosen
base coordinate, and no extension is supplied as an external premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoBroughExtensionGroups.Geometry

open ModularRep.PaperProofs.OddTwoConformalProjectiveRealisation
open ModularRep.PaperProofs.OddTwoActualLocalBlockSupport

universe u

variable {n : ℕ} {F k K G T : Type u}
variable [Field F] [Finite F] [Field k] [Field K]
variable [IsAlgClosed k] [CharP k 2] [CharZero K]
variable [Group G] [Finite G] [Group T]
variable {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
variable (L : Geometry (C := C) G T)
variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F))
variable (original target : IBr iota)

local instance originalInertiaFintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

/-- The target character uses the ORIGINAL base coordinates and root. -/
def targetOnOriginalBase : IBr (L.globalBaseRoot S iota original) :=
  IrreducibleBrauerCharacter.alongMulEquiv iota
    (L.globalBaseEquiv S iota original) target

/-- Actual stabilizer equality transports membership, not the group or
the local root convention. -/
theorem targetOnOriginalBase_fixed
    (sameInertia : L.global S iota target = L.global S iota original)
    (g : L.global S iota original) :
    IrreducibleBrauerCharacter.twist (L.globalBaseRoot S iota original)
      (L.targetOnOriginalBase S iota original target) (MulAut.conjNormal g) =
        L.targetOnOriginalBase S iota original target := by
  have hg : g.1 ∈ L.global S iota target := by
    rw [sameInertia]
    exact g.2
  have hfixed := L.global_inertia_fixes_forward S iota target ⟨g.1, hg⟩
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  change target.1 (PrimeRegularElement.map
      (L.globalBaseEquiv S iota original).symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.conjNormal g).toMonoidHom x)) =
    target.1 (PrimeRegularElement.map
      (L.globalBaseEquiv S iota original).symm.toMonoidHom x)
  have harg : PrimeRegularElement.map
      (L.globalBaseEquiv S iota original).symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.conjNormal g).toMonoidHom x) =
    PrimeRegularElement.map (S.fullAut (L.embedding g.1)).toMonoidHom
      (PrimeRegularElement.map
        (L.globalBaseEquiv S iota original).symm.toMonoidHom x) := by
    apply Subtype.ext
    exact L.globalBase_conjugation S iota original g x.1
  rw [harg]
  exact congrArg (fun chi : IBr iota => chi.1 (PrimeRegularElement.map
    (L.globalBaseEquiv S iota original).symm.toMonoidHom x)) hfixed

/-- A definition-shaped extension on the fixed ORIGINAL group, with the
same root convention and literal values on the original base inclusion. -/
structure GlobalExtensionOnOriginal where
  root : PrimeRegularRootEmbedding 2 k K (L.global S iota original)
  compatible : RootCompatibleAlong root (L.globalBaseRoot S iota original)
    (L.globalBase S iota original).subtype
  character : IBr root
  restricts : ∀ x : PrimeRegularElement (G := PSp n F) 2,
    character.1 (PrimeRegularElement.map (L.baseToGlobal S iota original) x) = target.1 x

variable [IsCyclic T]

/-- Both actual groups and the original base coordinates remain fixed
throughout this cyclic-extension construction. -/
theorem extensionOnOriginalInertia
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
    (sameInertia : L.global S iota target = L.global S iota original)
    (root : PrimeRegularRootEmbedding 2 k K (L.global S iota original))
    (compatible : RootCompatibleAlong root (L.globalBaseRoot S iota original)
      (L.globalBase S iota original).subtype) :
    Nonempty (L.GlobalExtensionOnOriginal S iota original target) := by
  obtain ⟨V, hirr, haffords, ⟨extension⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient principle
      (L.globalBaseRoot S iota original) (L.targetOnOriginalBase S iota original target)
      (L.global_outerQuotient_cyclic S iota original)
      (L.targetOnOriginalBase_fixed S iota original target sameInertia)
  let witness := Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    extension hirr root (L.globalBaseRoot S iota original)
    (L.targetOnOriginalBase S iota original target) haffords.symm
    (compatible (FDRep.of extension.representation))
  refine ⟨⟨root, compatible, witness.1, ?_⟩⟩
  intro x
  have h := congrArg
    (fun f : PrimeRegularClassFunction K (L.globalBase S iota original) 2 =>
      f (PrimeRegularElement.map (L.globalBaseEquiv S iota original).toMonoidHom x))
    witness.2
  change witness.1.1 (PrimeRegularElement.map (L.baseToGlobal S iota original) x) =
    target.1 (PrimeRegularElement.map (L.globalBaseEquiv S iota original).symm.toMonoidHom
      (PrimeRegularElement.map (L.globalBaseEquiv S iota original).toMonoidHom x)) at h
  have hinv : PrimeRegularElement.map (L.globalBaseEquiv S iota original).symm.toMonoidHom
      (PrimeRegularElement.map (L.globalBaseEquiv S iota original).toMonoidHom x) = x := by
    apply Subtype.ext
    exact (L.globalBaseEquiv S iota original).symm_apply_apply x.1
  rw [hinv] at h
  exact h

end ModularRep.PaperProofs.OddTwoBroughExtensionGroups.Geometry


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
