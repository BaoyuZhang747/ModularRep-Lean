import ManuscriptIBAW.Sporadic.TripleCoverWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven

/-!
# The Fischer argument at seven

The deduction cancels the cyclic and defect zero block contributions from
each central sector. This finite cancellation proves the two count
equalities for the specified remaining block. The outer involution inverts
the centre of the universal triple cover, so every fixed block belongs to
the trivial central sector.

The source supplies each sector's total count and the trivial sector's fixed
count through the An–Dietrich correspondence for the whole sector and the
table interpretation with the stated corrections. It supplies no
correspondence for the desired noncyclic block. The group, table and action
identifications, together with cyclicity of the complementary blocks, remain
explicit published, computational and structural assumptions.

The matching preserves the specified cover and local reductions. The full
condition additionally assumes compatible extension and block witnesses
for that matching. The ordinary field has characteristic zero, and its
character interpretation is explicit. Each case uses the specified finite group
`NamedBase`, identified by its covering map.
-/

noncomputable section
namespace ManuscriptIBAW.Sporadic.Fi24Seven
open ModularRep ModularRep.PaperProofs
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
universe u

/-- The underlying application assumptions, with no final correspondence input. -/
abbrev SourceInputs (base : NamedBase.{u}) :=
  SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.Inputs base

namespace SourceInputs

/-- The specified group, root convention and universal prime-to-7 cover. -/
def model {base : NamedBase.{u}} (I : SourceInputs base) : CaseModel base 7 := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C hpne S inputInst10 inputInst11 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed namedBaseEquiv =>
      let selectedCover : ModularRep.PaperProofs.EvenFieldFLZSourceConditions.EllPrimeCoverSource 7 X := (ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts.ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      let M : CaseModel base 7 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      exact M


/-- The proof uses this specified family. -/
theorem model_eq_retained {base : NamedBase.{u}} (I : SourceInputs base) :
    model I = SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Seven.model I := by
  cases I <;> rfl

/-- Existence of compatible extension and block witnesses for the same matching. -/
def PacketCompatibility {base : NamedBase.{u}} (I : SourceInputs base) : Prop := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C hpne S inputInst10 inputInst11 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed namedBaseEquiv =>
      exact TripleCoverWitnesses.PacketCompatibility iota hinj R C tau decomposition (actual_counts_of_seven_sector_cancellation iota hinj R tau cyclicData (center_card_three_of_fullCover q hq hs hna hkernel) hinverts distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed)

/-- The numerical construction with its compatible extension and block witnesses. -/
theorem complete {base : NamedBase.{u}} (I : SourceInputs base) (packets : PacketCompatibility I) :
    CaseConclusion (model I) := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 inputInst9 iota hinj R C hpne S inputInst10 inputInst11 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed namedBaseEquiv =>
      change Definition41Certificate iota R (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      exact TripleCoverWitnesses.complete iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts (actual_counts_of_seven_sector_cancellation iota hinj R tau cyclicData (center_card_three_of_fullCover q hq hs hna hkernel) hinverts distinguished distinguished_sector cyclic_complement sectorCount brauer_sector_counts weight_sector_counts trivialFixedCount brauer_trivial_fixed weight_trivial_fixed) D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 packets

end SourceInputs
/-- Numerical sources and compatible extension and block witnesses for the same matching. -/
structure Inputs (base : NamedBase.{u}) where
  source : SourceInputs base
  packets : source.PacketCompatibility

namespace Inputs

def model {base : NamedBase.{u}} (I : Inputs base) : CaseModel base 7 :=
  I.source.model

theorem complete {base : NamedBase.{u}} (I : Inputs base) :
    CaseConclusion I.model := I.source.complete I.packets

end Inputs

end ManuscriptIBAW.Sporadic.Fi24Seven

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
