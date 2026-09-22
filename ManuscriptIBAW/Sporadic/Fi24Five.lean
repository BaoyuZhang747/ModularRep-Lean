import ManuscriptIBAW.Sporadic.TripleCoverWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five

/-!
# The Fischer argument at five

The deduction uses seven specified blocks, in table order 1, 2, 3, 45, 46,
47, 48. Their counts are 16, 14, 16, 16, 16, 14, 14. The three invariant
blocks have fixed counts 16, 6, 16, and the two remaining pairs of blocks
are exchanged. The complement is assumed to have cyclic defect groups.

The numerical equations identify the specified table rows with the
characters, weights, blocks and outer action. The radical classification and
identifications of named normalisers and class fusions are separate
published interpretations. No completeness assertion about an arbitrary
returned fusion list or its automorphism orbit is used.

The matching preserves the specified cover and local reductions. The full
condition additionally assumes compatible extension and block witnesses
for that matching. The ordinary field has characteristic zero, and its
character interpretation is explicit. Each case uses the specified finite group
`NamedBase`, identified by its covering map.
-/

noncomputable section
namespace ManuscriptIBAW.Sporadic.Fi24Five
open ModularRep ModularRep.PaperProofs
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
universe u

/-- The underlying application assumptions, with no final correspondence input. -/
abbrev SourceInputs (base : NamedBase.{u}) :=
  SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.Inputs base

namespace SourceInputs

/-- The specified group, root convention and universal prime-to-5 cover. -/
def model {base : NamedBase.{u}} (I : SourceInputs base) : CaseModel base 5 := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts namedBaseEquiv =>
      let selectedCover : ModularRep.PaperProofs.EvenFieldFLZSourceConditions.EllPrimeCoverSource 5 X := (ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts.ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      let M : CaseModel base 5 := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      exact M


/-- The proof uses this specified family. -/
theorem model_eq_retained {base : NamedBase.{u}} (I : SourceInputs base) :
    model I = SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Five.model I := by
  cases I <;> rfl

/-- Existence of compatible extension and block witnesses for the same matching. -/
def PacketCompatibility {base : NamedBase.{u}} (I : SourceInputs base) : Prop := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts namedBaseEquiv =>
      exact TripleCoverWitnesses.PacketCompatibility iota hinj R C tau decomposition (actual_counts_of_five_literal_rows iota hinj R tau cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts)

/-- The numerical construction with its compatible extension and block witnesses. -/
theorem complete {base : NamedBase.{u}} (I : SourceInputs base) (packets : PacketCompatibility I) :
    CaseConclusion (model I) := by
  cases I with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts namedBaseEquiv =>
      change Definition41Certificate iota R (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      exact TripleCoverWitnesses.complete iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts (actual_counts_of_five_literal_rows iota hinj R tau cyclicData roles roles_injective coverage role_action brauer_counts weight_counts brauer_fixed_counts weight_fixed_counts) D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 packets

end SourceInputs
/-- Numerical sources and compatible extension and block witnesses for the same matching. -/
structure Inputs (base : NamedBase.{u}) where
  source : SourceInputs base
  packets : source.PacketCompatibility

namespace Inputs

def model {base : NamedBase.{u}} (I : Inputs base) : CaseModel base 5 :=
  I.source.model

theorem complete {base : NamedBase.{u}} (I : Inputs base) :
    CaseConclusion I.model := I.source.complete I.packets

end Inputs

end ManuscriptIBAW.Sporadic.Fi24Five

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
