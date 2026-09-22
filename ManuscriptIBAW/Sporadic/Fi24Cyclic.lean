import ManuscriptIBAW.Sporadic.TripleCoverWitnesses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic

/-!
# The remaining Fischer primes

At 11, 13, 17, 23 and 29 the specified block classification has only cyclic
defect groups, including the trivial group. Späth's Proposition 6.2 supplies
the numerical consequences for cyclic blocks on the universal prime-to-p
cover. The proof constructs an equivariant map from these counts. The full
condition additionally assumes compatible extension and block witnesses
for that matching.

The cover map, kernel of order three, root conventions, primitive blocks and full
automorphism action remain fixed. Interpretations of the named groups and
tables are explicit published, computational and structural assumptions. A
small defect exponent is used only to prove cyclicity in the complement,
without identifying any selected block as noncyclic.
-/

noncomputable section
namespace ManuscriptIBAW.Sporadic.Fi24Cyclic
open ModularRep ModularRep.PaperProofs
open EvenFieldFLZSourceConditions
open SporadicFi24P3Definition44NamedCarrierTripleCoverFacts
open SporadicFi24P3Definition44NamedCarrierOtherPrimeNumericalJoins
open SporadicFi24P3Definition44NamedCarrierAcceleratedDefinition41Certificate
open SporadicFi24P3Definition44NamedCarrierAcceleratedNamedModels
universe u

def ListedPrime (p : ℕ) : Prop := p ∈ [11, 13, 17, 23, 29]


/-- The specified remaining prime and the stated assumptions. -/
structure SourceInputs (base : NamedBase.{u}) (p : ℕ) where
  listed : ListedPrime p
  source : SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.Inputs base p

namespace SourceInputs

def model {base : NamedBase.{u}} {p : ℕ} (I : SourceInputs base p) : CaseModel base p := by
  cases I.source with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData allCyclic namedBaseEquiv =>
      let selectedCover : ModularRep.PaperProofs.EvenFieldFLZSourceConditions.EllPrimeCoverSource p X := (ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTripleCoverFacts.ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      let M : CaseModel base p := {
        k := k, K := K, X := X,
        iota := iota, R := R, Cover := selectedCover, baseEquiv := namedBaseEquiv }
      exact M

/-- The proof uses this specified family. -/
theorem model_eq_retained {base : NamedBase.{u}} {p : ℕ} (I : SourceInputs base p) :
    model I = SporadicFi24P3Definition44NamedCarrierAcceleratedNamedInputsFi24Cyclic.model I.source := by
  cases I with
  | mk listed source => cases source <;> rfl

/-- Existence of compatible extension and block witnesses for the same matching. -/
def PacketCompatibility {base : NamedBase.{u}} {p : ℕ} (I : SourceInputs base p) : Prop := by
  cases I.source with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData allCyclic namedBaseEquiv =>
      exact TripleCoverWitnesses.PacketCompatibility iota hinj R C tau decomposition (actual_counts_of_cyclic_blocks iota hinj R tau cyclicData allCyclic)

/-- The numerical construction with its compatible extension and block witnesses. -/
theorem complete {base : NamedBase.{u}} {p : ℕ} (I : SourceInputs base p) (packets : PacketCompatibility I) :
    CaseConclusion (model I) := by
  rcases I with ⟨listed, source⟩
  cases source with
  | @mk k K X inputInst1 inputInst2 inputInst3 inputInst4 inputInst5 inputInst6 inputInst7 inputInst8 iota hinj R C hpne S inputInst9 inputInst10 q hq hs hna hkernel hOuterS tau decomposition hinverts D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 cyclicData allCyclic namedBaseEquiv =>
      change Definition41Certificate iota R (ellPrimeCover_of_fullCover_kernel_three iota.prime hpne q hq hs hna hkernel)
      exact TripleCoverWitnesses.complete iota hinj R C hpne q hq hs hna hkernel hOuterS tau decomposition hinverts (actual_counts_of_cyclic_blocks iota hinj R tau cyclicData allCyclic) D T Bzero compatibility lower ambientData seed extensionPrinciple fieldSource S9295 S9495 S820 packets

end SourceInputs
/-- Numerical sources and compatible extension and block witnesses for the same matching. -/
structure Inputs (base : NamedBase.{u}) (p : ℕ) where
  source : SourceInputs base p
  packets : source.PacketCompatibility

namespace Inputs

def model {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) : CaseModel base p :=
  I.source.model

theorem complete {base : NamedBase.{u}} {p : ℕ} (I : Inputs base p) :
    CaseConclusion I.model := I.source.complete I.packets

end Inputs

end ManuscriptIBAW.Sporadic.Fi24Cyclic

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
