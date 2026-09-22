import ModularRep.BrauerRootConvention
import ModularRep.PaperProofs.CurrentCyclicOuterBAW
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierOriginalActualPacket

/-!
# Compatible roots in extension and block certificates

A character equality alone does not identify the roots used to define
Brauer characters. These predicates require agreement on every relevant
root, for the ambient groups and all their intermediate subgroups.
The raw extension and block records are full certificates only when these
additional compatibility conditions hold. For an original packet, the ambient
group contains the central character quotient. Root agreement between the
original and ambient groups is required on that quotient, through which the
base representation factors. Agreement on all roots for the original group
is neither required nor implied.
-/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SpathRootCoherence

open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open SporadicFi24P3Definition44NamedCarrierActualRadicalPacket
open SporadicFi24P3Definition44NamedCarrierOriginalActualPacket

universe u

local instance subgroupFintype {A : Type u} [Group A] [Finite A]
    (H : Subgroup A) : Fintype H := Fintype.ofFinite H

/-- The two roots for an intermediate subgroup are restrictions of the
same ambient root correspondence. -/
def IntermediateRoots {P : Definition35Problem.{u}}
    {A : Type u} [Group A] [Fintype A] {D J : Subgroup A}
    {globalCharacter : PrimeRegularClassFunction P.K A P.p}
    {localCharacter : PrimeRegularClassFunction P.K D P.p}
    (rA : PrimeRegularRootEmbedding P.p P.k P.K A)
    (data : ActualIntermediateBlockData P D globalCharacter localCharacter J) : Prop :=
  rA.AgreesOnRoots data.globalRoot ∧ rA.AgreesOnRoots data.localRoot

/-- Root compatibility for the quotient, its global and local extensions,
and every intermediate block calculation in the original ambient group. -/
def OriginalPacketRoots {P : Definition35Problem.{u}}
    {psi : Definition35Brauer P} {V : CharacterWeight P.p P.K P.H}
    (packet : OriginalActualWeightPacket P psi V) : Prop :=
  P.iota.AgreesOnRoots packet.quotient.iota ∧
  packet.globalRoot.AgreesOnRoots packet.quotient.iota ∧
  packet.globalRoot.AgreesOnRoots packet.localRoot ∧
  ∀ (J : Subgroup packet.ambient.A) (hJ : packet.ambient.base ≤ J),
    IntermediateRoots packet.globalRoot (packet.intermediateBlocks J hJ)

namespace OriginalPacketRoots

variable {P : Definition35Problem.{u}}
variable {psi : Definition35Brauer P} {V : CharacterWeight P.p P.K P.H}
variable {packet : OriginalActualWeightPacket P psi V}

/-- The original and ambient conventions agree on every root used by the
central character quotient. -/
theorem original_ambient_lift_eq (h : OriginalPacketRoots packet)
    (zeta : rootsOfUnity (primeRegularExponent P.p (CentralCharacterQuotient P psi)) P.k) :
    P.iota.lift (((zeta : P.kˣ) : P.k)) =
      packet.globalRoot.lift (((zeta : P.kˣ) : P.k)) :=
  (h.1 zeta).trans (h.2.1 zeta).symm

/-- Forming a Brauer character commutes with inflation of a representation
of the central character quotient under the required root agreement. -/
theorem quotient_brauerCharacter_inflation
    {U : Type u} [AddCommGroup U] [Module P.k U] [FiniteDimensional P.k U]
    (h : OriginalPacketRoots packet)
    (rho : Representation P.k (CentralCharacterQuotient P psi) U) :
    (rho.pullback (centralCharacterQuotientMap P psi)).brauerCharacterOfRootEmbedding P.iota =
      PrimeRegularClassFunction.pullback (centralCharacterQuotientMap P psi)
        (rho.brauerCharacterOfRootEmbedding packet.quotient.iota) := by
  apply Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
  exact Representation.brauerRootLiftCompatibleAlong_of_eq_on_target_roots
    rho packet.quotient.iota P.iota (centralCharacterQuotientMap P psi) h.1

/-- In particular, inflating the packet's quotient representation affords
the specified original Brauer character. -/
theorem quotient_representation_affords_original (h : OriginalPacketRoots packet) :
    Representation.brauerCharacterOfRootEmbedding
      (Representation.pullback
        (chosenIBrRepresentation packet.quotient.iota packet.quotient.brauer).ρ
        (centralCharacterQuotientMap P psi)) P.iota =
      psi.1.1 := by
  rw [h.quotient_brauerCharacter_inflation]
  rw [← chosenIBrRepresentation_character packet.quotient.iota packet.quotient.brauer]
  exact packet.quotient.inflation

/-- The restriction from the ambient group to the original group is computed
using the same root convention, because it factors through the central
character quotient. -/
theorem ambient_brauerCharacter_restriction
    {U : Type u} [AddCommGroup U] [Module P.k U] [FiniteDimensional P.k U]
    (h : OriginalPacketRoots packet)
    (rho : Representation P.k packet.ambient.A U) :
    (rho.pullback packet.ambient.rawMap).brauerCharacterOfRootEmbedding P.iota =
      PrimeRegularClassFunction.pullback packet.ambient.rawMap
        (rho.brauerCharacterOfRootEmbedding packet.globalRoot) := by
  have hquotient := Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    rho packet.globalRoot packet.quotient.iota packet.ambient.quotientEmbedding
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      rho packet.globalRoot packet.quotient.iota packet.ambient.quotientEmbedding
      (fun zeta => (h.2.1 zeta).symm))
  calc
    (rho.pullback packet.ambient.rawMap).brauerCharacterOfRootEmbedding P.iota =
        PrimeRegularClassFunction.pullback (centralCharacterQuotientMap P psi)
          ((rho.pullback packet.ambient.quotientEmbedding).brauerCharacterOfRootEmbedding
            packet.quotient.iota) :=
      h.quotient_brauerCharacter_inflation (rho.pullback packet.ambient.quotientEmbedding)
    _ = PrimeRegularClassFunction.pullback packet.ambient.rawMap
          (rho.brauerCharacterOfRootEmbedding packet.globalRoot) := by
      rw [hquotient]
      rfl

/-- The global extension, restricted to the original group, affords its
specified Brauer character under the original root convention. -/
theorem global_representation_affords_original (h : OriginalPacketRoots packet) :
    Representation.brauerCharacterOfRootEmbedding
      (Representation.pullback
        (chosenIBrRepresentation packet.globalRoot packet.globalCharacter).ρ
        packet.ambient.rawMap) P.iota = psi.1.1 := by
  rw [h.ambient_brauerCharacter_restriction]
  rw [← chosenIBrRepresentation_character packet.globalRoot packet.globalCharacter]
  exact packet.globalRestriction

end OriginalPacketRoots

/-- The same compatibility for a packet whose original group embeds into
its ambient group. -/
def ActualPacketRoots {P : Definition35Problem.{u}}
    {psi : Definition35Brauer P} {V : CharacterWeight P.p P.K P.H}
    (packet : ActualWeightPacket P psi V) : Prop :=
  P.iota.AgreesOnRoots packet.quotient.iota ∧
  packet.globalRoot.AgreesOnRoots P.iota ∧
  packet.globalRoot.AgreesOnRoots packet.quotient.iota ∧
  packet.globalRoot.AgreesOnRoots packet.localRoot ∧
  ∀ (J : Subgroup packet.ambient.A) (hJ : packet.ambient.base ≤ J),
    IntermediateRoots packet.globalRoot (packet.intermediateBlocks J hJ)

/-- An original packet together with the root agreements needed to
interpret its restrictions and block induction under one convention. -/
structure CoherentOriginalPacket (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) (V : CharacterWeight P.p P.K P.H) where
  packet : OriginalActualWeightPacket P psi V
  roots : OriginalPacketRoots packet

/-- An embedded packet with the same root compatibility. -/
structure CoherentActualPacket (P : Definition35Problem.{u})
    (psi : Definition35Brauer P) (V : CharacterWeight P.p P.K P.H) where
  packet : ActualWeightPacket P psi V
  roots : ActualPacketRoots packet

/-- The agreement required here is the existing root agreement predicate,
with the ambient correspondence written first. -/
theorem agreesOnRoots_iff_rootAgreement
    {p : ℕ} {k K G A : Type u} [Field k] [Field K]
    [Group G] [Finite G] [Group A] [Finite A]
    (rA : PrimeRegularRootEmbedding p k K A)
    (rG : PrimeRegularRootEmbedding p k K G) :
    rA.AgreesOnRoots rG ↔ CurrentCyclicOuterBAW.RootAgreement rG rA := by
  constructor <;> intro h z <;> exact (h z).symm

end ModularRep.PaperProofs.SpathRootCoherence

/-
Part of the Lean formalisation accompanying Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
The results use the explicit assumptions described in the formalisation report.
-/
