import ModularRep.PaperProofs.OddTwoBroughExtensionGroups
import ModularRep.PaperProofs.OddTwoActualLocalBlockSupport
import ModularRep.BrauerCharacterExtensionBridge

/-!
# Actual global Brauer extensions in both Brough lanes

The actual Brauer inertia group in either constructed lane contains the
computed base copy of PSp. Its own character and root are transported by
the already fixed globalBaseEquiv. K identifies conjugation on this base
with the actual fullAut action, derives fixedness from inertia membership,
and applies the existing Navarro cyclic-extension principle.

The ambient root is required to be compatible along the ACTUAL base
inclusion, on representation eigenvalues. No equality of independent root
lifts on the whole coefficient field is assumed. The global character is
arbitrary, so the consumer also applies to an actual conformal translate;
identifying its inertia group with the original one uses the separate
checked principal stabilizer theorem. There is no new source statement.
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
variable (iota : PrimeRegularRootEmbedding 2 k K (PSp n F)) (psi : IBr iota)

local instance globalGroupFintype (H : Type u) [Group H] [Finite H] : Fintype H :=
  Fintype.ofFinite H

/-- The base root is computed from the original PSp root and the actual
base equivalence. There is no independent base-root choice. -/
def globalBaseRoot : PrimeRegularRootEmbedding 2 k K (L.globalBase S iota psi) :=
  iota.alongMulEquiv (L.globalBaseEquiv S iota psi)

/-- The base character is the prescribed actual psi through the SAME
computed base equivalence. -/
def globalBaseBrauer : IBr (L.globalBaseRoot S iota psi) :=
  IrreducibleBrauerCharacter.alongMulEquiv iota (L.globalBaseEquiv S iota psi) psi

theorem globalBaseEquiv_symm_value (x : L.globalBase S iota psi) :
    L.base ((L.globalBaseEquiv S iota psi).symm x) = x.1.1 := by
  have h := congrArg (fun z : L.globalBase S iota psi => z.1.1)
    ((L.globalBaseEquiv S iota psi).apply_symm_apply x)
  exact h

/-- Actual base conjugation is the action prescribed by the lane's fixed
embedding into the Brough ambient group. -/
theorem globalBase_conjugation (g : L.global S iota psi) (x : L.globalBase S iota psi) :
    (L.globalBaseEquiv S iota psi).symm (MulAut.conjNormal g x) =
      S.fullAut (L.embedding g.1) ((L.globalBaseEquiv S iota psi).symm x) := by
  apply L.base_injective
  calc
    L.base ((L.globalBaseEquiv S iota psi).symm (MulAut.conjNormal g x)) =
        g.1 * x.1.1 * g.1⁻¹ := L.globalBaseEquiv_symm_value S iota psi _
    _ = g.1 * L.base ((L.globalBaseEquiv S iota psi).symm x) * g.1⁻¹ := by
      rw [L.globalBaseEquiv_symm_value]
    _ = L.base (S.fullAut (L.embedding g.1)
        ((L.globalBaseEquiv S iota psi).symm x)) :=
      (L.base_conjugate S g.1 _).symm

/-- Using membership of g inverse gives fixedness under the FORWARD
automorphism of g, consistently with the inverse/opposite action. -/
theorem global_inertia_fixes_forward (g : L.global S iota psi) :
    IrreducibleBrauerCharacter.twist iota psi (S.fullAut (L.embedding g.1)) = psi := by
  have hg := (g⁻¹).2
  change IrreducibleBrauerCharacter.twist iota psi
    (S.fullAut ((L.embedding (g⁻¹).1)⁻¹)) = psi at hg
  have hinv : (L.embedding (g⁻¹).1)⁻¹ = L.embedding g.1 := by
    change (L.embedding (g.1⁻¹))⁻¹ = L.embedding g.1
    rw [map_inv, inv_inv]
  rw [hinv] at hg
  exact hg

/-- The actual transported Brauer character is invariant under the full
actual inertia group. This conclusion is not an external assumption. -/
theorem globalBaseBrauer_fixed (g : L.global S iota psi) :
    IrreducibleBrauerCharacter.twist (L.globalBaseRoot S iota psi)
      (L.globalBaseBrauer S iota psi) (MulAut.conjNormal g) =
      L.globalBaseBrauer S iota psi := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  change psi.1 (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom
      (PrimeRegularElement.map (MulAut.conjNormal g).toMonoidHom x)) =
    psi.1 (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom x)
  have harg :
      PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom
          (PrimeRegularElement.map (MulAut.conjNormal g).toMonoidHom x) =
        PrimeRegularElement.map (S.fullAut (L.embedding g.1)).toMonoidHom
          (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom x) := by
    apply Subtype.ext
    exact L.globalBase_conjugation S iota psi g x.1
  rw [harg]
  exact congrArg
    (fun chi : IBr iota => chi.1
      (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom x))
    (L.global_inertia_fixes_forward S iota psi g)

variable [IsCyclic T]

/-- Navarro8.12 supplies an extension after actual fixedness/cyclicity.
The actual ambient IBr is formed only with compatible root conventions
along the exact subgroup inclusion. -/
theorem globalBrauer_extension
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
    (ambientRoot : PrimeRegularRootEmbedding 2 k K (L.global S iota psi))
    (compatible : RootCompatibleAlong ambientRoot (L.globalBaseRoot S iota psi)
      (L.globalBase S iota psi).subtype) :
    Nonempty (Representation.Extension.BrauerCharacterExtensionWitness ambientRoot
      (L.globalBaseRoot S iota psi) (L.globalBaseBrauer S iota psi)) := by
  obtain ⟨V, hirr, haffords, ⟨extension⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient principle
      (L.globalBaseRoot S iota psi) (L.globalBaseBrauer S iota psi)
      (L.global_outerQuotient_cyclic S iota psi) (L.globalBaseBrauer_fixed S iota psi)
  exact ⟨Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    extension hirr ambientRoot (L.globalBaseRoot S iota psi)
    (L.globalBaseBrauer S iota psi) haffords.symm
    (compatible (FDRep.of extension.representation))⟩

/-- The extension restricts on every actual prime regular PSp element to
the prescribed psi, through the original lane base embedding. -/
theorem exists_globalBrauer_extension_values
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} 2 k)
    (ambientRoot : PrimeRegularRootEmbedding 2 k K (L.global S iota psi))
    (compatible : RootCompatibleAlong ambientRoot (L.globalBaseRoot S iota psi)
      (L.globalBase S iota psi).subtype) :
    ∃ psiHat : IBr ambientRoot, ∀ x : PrimeRegularElement (G := PSp n F) 2,
      psiHat.1 (PrimeRegularElement.map (L.baseToGlobal S iota psi) x) = psi.1 x := by
  obtain ⟨extension⟩ := L.globalBrauer_extension S iota psi principle ambientRoot compatible
  refine ⟨extension.1, ?_⟩
  intro x
  have h := congrArg
    (fun f : PrimeRegularClassFunction K (L.globalBase S iota psi) 2 =>
      f (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).toMonoidHom x)) extension.2
  change extension.1.1 (PrimeRegularElement.map (L.baseToGlobal S iota psi) x) =
    psi.1 (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom
      (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).toMonoidHom x)) at h
  have hinv : PrimeRegularElement.map (L.globalBaseEquiv S iota psi).symm.toMonoidHom
      (PrimeRegularElement.map (L.globalBaseEquiv S iota psi).toMonoidHom x) = x := by
    apply Subtype.ext
    exact (L.globalBaseEquiv S iota psi).symm_apply_apply x.1
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
