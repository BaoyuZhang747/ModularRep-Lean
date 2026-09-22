import ModularRep.BrauerCharacterEquivTransport
import ModularRep.CyclicExtension

/-!
# Brauer characters and pullback along homomorphisms

Brauer characters in this project are defined relative to a chosen lift of
prime regular roots of unity.  Pulling a representation back along an
arbitrary group homomorphism therefore commutes with Brauer-character
formation once the two chosen root embeddings induce the same field-level
lift.  This module proves that compatibility directly and applies it to the
restriction of a representation extension.

The existence of compatible root embeddings in a splitting modular system
is an external standard input.  Navarro's construction directly supplies
the usual complex-valued correspondence; an application with an arbitrary
characteristic-zero target field must also supply the corresponding
realisation data.  The deductions below are kernel checked and contain no
representation theoretic existence theorem.
-/

namespace Representation

universe u v w x y

variable {p : ℕ} {k : Type u} {K : Type v}
variable {G : Type w} {H : Type x} {V : Type y}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Compatibility of two chosen root lifts on exactly the characteristic
polynomial roots used after pullback along `f`.  This is weaker, and more
useful, than equality of the two field-level lift functions away from those
roots. -/
def BrauerRootLiftCompatibleAlong
    (rho : Representation k G V)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaH : ModularRep.PrimeRegularRootEmbedding p k K H)
    (f : H →* G) : Prop :=
  ∀ h : ModularRep.PrimeRegularElement (G := H) p,
    ∀ a : {a : k // a ∈ (rho (f h.1)).charpoly.roots},
      iotaH.lift a.1 = iotaG.lift a.1

/-- Agreement of the two lifts on every prime regular root of unity for the
source group implies compatibility along any homomorphism from that group.
This is weaker than equality of the lift functions on the whole coefficient
field and is independent of the representation to which it is applied. -/
theorem brauerRootLiftCompatibleAlong_of_eq_on_source_roots
    (rho : Representation k G V)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaH : ModularRep.PrimeRegularRootEmbedding p k K H)
    (f : H →* G)
    (hroots :
      ∀ zeta : rootsOfUnity (ModularRep.primeRegularExponent p H) k,
        iotaH.lift (((zeta : kˣ) : k)) =
          iotaG.lift (((zeta : kˣ) : k))) :
    BrauerRootLiftCompatibleAlong rho iotaG iotaH f := by
  intro h a
  let aH : {a : k //
      a ∈ ((rho.pullback f) h.1).charpoly.roots} := a
  exact hroots
    ((rho.pullback f).charpolyRootAsRootOfUnity iotaH h aH)

/-- Brauer-character formation commutes with pullback along an arbitrary
group homomorphism when the root lifts agree on all characteristic-polynomial
roots that occur after pullback. -/
theorem brauerCharacterOfRootEmbedding_pullback_of_compatible
    (rho : Representation k G V)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaH : ModularRep.PrimeRegularRootEmbedding p k K H)
    (f : H →* G)
    (hcompat : BrauerRootLiftCompatibleAlong rho iotaG iotaH f) :
    (rho.pullback f).brauerCharacterOfRootEmbedding iotaH =
      ModularRep.PrimeRegularClassFunction.pullback f
        (rho.brauerCharacterOfRootEmbedding iotaG) := by
  apply ModularRep.PrimeRegularClassFunction.ext
  intro h
  change (((rho (f h.1)).charpoly.roots.map iotaH.lift).sum) =
    ((rho (f h.1)).charpoly.roots.map iotaG.lift).sum
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  exact hcompat h ⟨a, ha⟩

/-- Brauer-character formation commutes with pullback along an arbitrary
group homomorphism when the chosen root embeddings have the same lift on the
coefficient field. -/
theorem brauerCharacterOfRootEmbedding_pullback_of_lift_eq
    (rho : Representation k G V)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaH : ModularRep.PrimeRegularRootEmbedding p k K H)
    (f : H →* G)
    (hlift : iotaH.lift = iotaG.lift) :
    (rho.pullback f).brauerCharacterOfRootEmbedding iotaH =
      ModularRep.PrimeRegularClassFunction.pullback f
        (rho.brauerCharacterOfRootEmbedding iotaG) := by
  apply brauerCharacterOfRootEmbedding_pullback_of_compatible
    rho iotaG iotaH f
  intro h a
  exact congrFun hlift a.1

namespace Extension

variable {N : Subgroup G} {rho : Representation k N V}

/-- An actual irreducible Brauer character of the ambient group whose
restriction is the specified irreducible Brauer character of `N`.  This is
the character-level conclusion needed when a representation extension is
used in an inductive-condition argument. -/
def BrauerCharacterExtensionWitness
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaN : ModularRep.PrimeRegularRootEmbedding p k K N)
    (phiN : ModularRep.IBr iotaN) :=
  {phiG : ModularRep.IBr iotaG //
    ModularRep.PrimeRegularClassFunction.pullback N.subtype phiG.1 = phiN.1}

/-- The Brauer character of an ambient representation extension restricts
to that of the original representation when the two root lifts agree on the
roots occurring on the subgroup. -/
theorem restrictedBrauerCharacter_eq_of_compatible
    (extension : Representation.Extension N rho)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaN : ModularRep.PrimeRegularRootEmbedding p k K N)
    (hcompat : BrauerRootLiftCompatibleAlong extension.representation
      iotaG iotaN N.subtype) :
    ModularRep.PrimeRegularClassFunction.pullback N.subtype
        (extension.representation.brauerCharacterOfRootEmbedding iotaG) =
      rho.brauerCharacterOfRootEmbedding iotaN := by
  rw [← brauerCharacterOfRootEmbedding_pullback_of_compatible
    extension.representation iotaG iotaN N.subtype hcompat]
  apply ModularRep.PrimeRegularClassFunction.ext
  intro n
  change
    ((((extension.representation.pullback N.subtype) n.1).charpoly.roots.map
      iotaN.lift).sum) =
      (((rho n.1).charpoly.roots.map iotaN.lift).sum)
  have hconj :
      rho n.1 = extension.restrictionEquiv.toLinearEquiv.conj
        ((extension.representation.pullback N.subtype) n.1) := by
    ext v
    change rho n.1 v = extension.restrictionEquiv
      ((extension.representation.pullback N.subtype) n.1
        (extension.restrictionEquiv.invFun v))
    have hintertwining := DFunLike.congr_fun
      (extension.restrictionEquiv.isIntertwining' n.1)
      (extension.restrictionEquiv.invFun v)
    change extension.restrictionEquiv
        ((extension.representation.pullback N.subtype) n.1
          (extension.restrictionEquiv.invFun v)) =
      rho n.1 (extension.restrictionEquiv
        (extension.restrictionEquiv.invFun v)) at hintertwining
    calc
      rho n.1 v = rho n.1 (extension.restrictionEquiv
          (extension.restrictionEquiv.invFun v)) := by
        exact congrArg (rho (n.1 : N))
          (extension.restrictionEquiv.right_inv v).symm
      _ = extension.restrictionEquiv
          ((extension.representation.pullback N.subtype) n.1
            (extension.restrictionEquiv.invFun v)) :=
        hintertwining.symm
  have hpoly :
      ((extension.representation.pullback N.subtype) n.1).charpoly =
        (rho n.1).charpoly := by
    rw [hconj, LinearEquiv.charpoly_conj]
  rw [hpoly]

/-- The Brauer character of an ambient representation extension restricts
to that of the original representation when the ambient and subgroup root
embeddings use the same field-level lift. -/
theorem restrictedBrauerCharacter_eq_of_lift_eq
    (extension : Representation.Extension N rho)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaN : ModularRep.PrimeRegularRootEmbedding p k K N)
    (hlift : iotaN.lift = iotaG.lift) :
    ModularRep.PrimeRegularClassFunction.pullback N.subtype
        (extension.representation.brauerCharacterOfRootEmbedding iotaG) =
      rho.brauerCharacterOfRootEmbedding iotaN := by
  apply restrictedBrauerCharacter_eq_of_compatible extension iotaG iotaN
  intro n a
  exact congrFun hlift a.1

/-- A representation extension gives an actual ambient irreducible Brauer
character extending the prescribed subgroup character, provided the root
lifts are compatible and the subgroup representation affords that
character.  The carrier is in the coefficient field universe because that
is the universe used by the project's `FDRep` witness inside `IBr`. -/
noncomputable def brauerCharacterExtensionWitnessOfCompatible
    {V₀ : Type u} [AddCommGroup V₀] [Module k V₀]
    [FiniteDimensional k V₀]
    {rho₀ : Representation k N V₀}
    (extension : Representation.Extension N rho₀)
    (hirr : Representation.IsIrreducible rho₀)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaN : ModularRep.PrimeRegularRootEmbedding p k K N)
    (phiN : ModularRep.IBr iotaN)
    (haffords : rho₀.brauerCharacterOfRootEmbedding iotaN = phiN.1)
    (hcompat : BrauerRootLiftCompatibleAlong extension.representation
      iotaG iotaN N.subtype) :
    BrauerCharacterExtensionWitness iotaG iotaN phiN := by
  let phiG : ModularRep.IBr iotaG :=
    ⟨extension.representation.brauerCharacterOfRootEmbedding iotaG,
      ⟨FDRep.of extension.representation,
        extension.representation_isIrreducible hirr, rfl⟩⟩
  refine ⟨phiG, ?_⟩
  change ModularRep.PrimeRegularClassFunction.pullback N.subtype
      (extension.representation.brauerCharacterOfRootEmbedding iotaG) =
    phiN.1
  calc
    ModularRep.PrimeRegularClassFunction.pullback N.subtype
        (extension.representation.brauerCharacterOfRootEmbedding iotaG) =
      rho₀.brauerCharacterOfRootEmbedding iotaN :=
        restrictedBrauerCharacter_eq_of_compatible
          extension iotaG iotaN hcompat
    _ = phiN.1 := haffords

/-- The preceding character-level extension construction under the stronger
assumption that the two root embeddings have the same field-level lift. -/
noncomputable def brauerCharacterExtensionWitnessOfLiftEq
    {V₀ : Type u} [AddCommGroup V₀] [Module k V₀]
    [FiniteDimensional k V₀]
    {rho₀ : Representation k N V₀}
    (extension : Representation.Extension N rho₀)
    (hirr : Representation.IsIrreducible rho₀)
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaN : ModularRep.PrimeRegularRootEmbedding p k K N)
    (phiN : ModularRep.IBr iotaN)
    (haffords : rho₀.brauerCharacterOfRootEmbedding iotaN = phiN.1)
    (hlift : iotaN.lift = iotaG.lift) :
    BrauerCharacterExtensionWitness iotaG iotaN phiN :=
  brauerCharacterExtensionWitnessOfCompatible extension hirr iotaG iotaN
    phiN haffords (fun _ a ↦ congrFun hlift a.1)

/-- Convert the existential output of a cyclic extension argument into the
actual ambient Brauer-character witness used by the inductive condition.
The only additional datum is compatibility of the chosen root lifts. -/
noncomputable def brauerCharacterExtensionWitnessOfExistsExtension
    (iotaG : ModularRep.PrimeRegularRootEmbedding p k K G)
    (iotaN : ModularRep.PrimeRegularRootEmbedding p k K N)
    (phiN : ModularRep.IBr iotaN)
    (hexists : ∃ W : FDRep k N,
      Representation.IsIrreducible W.ρ ∧
      phiN.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iotaN ∧
      Nonempty (Representation.Extension N W.ρ))
    (hlift : iotaN.lift = iotaG.lift) :
    BrauerCharacterExtensionWitness iotaG iotaN phiN := by
  let W := Classical.choose hexists
  have hW := Classical.choose_spec hexists
  let extension := Classical.choice hW.2.2
  exact brauerCharacterExtensionWitnessOfLiftEq extension hW.1
    iotaG iotaN phiN hW.2.1.symm hlift

end Extension

end Representation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
