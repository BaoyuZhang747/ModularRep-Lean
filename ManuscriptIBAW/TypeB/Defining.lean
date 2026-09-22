import ModularRep.PaperProofs.TypeBCurrentDefiningCharacteristic
import ManuscriptIBAW.FamilyCertificate

/-!
# Type B in defining characteristic

Späth's Theorem C is applied on the stated universal prime-to-p cover. The
construction proves that the centre of the specified Spin group is prime to
p and keeps its projection to the matrix Omega group. For Omega7(3) at the
defining prime, this is the double cover Spin7(3).

The theorem and the structural covering facts are explicit published
assumptions. The ordinary field is not required to be the fraction field of
a discrete valuation ring in this application.
-/

noncomputable section

namespace ManuscriptIBAW.TypeB.Defining

open ModularRep.PaperProofs
open TypeBCliffordCarriers TypeBCurrentCertificate

variable {n p f : ℕ} {F : Type} [Field F] [Finite F] [CharP F p]
variable (parameters : OddFieldParameters F p f) (rank : 3 ≤ n)
variable (N : NormSource n F)
variable (C : TypeBCliffordOrthogonalSourceBinding.Source n F p f parameters rank N)
variable [Finite (Spin n F N)]

local instance definingSpinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

/-- The stated assumptions on the same Spin group and projection. -/
abbrev SourceInputs := TypeBCurrentDefiningCharacteristic.DefiningInputs parameters rank N C

/-- The complete inductive condition on the cover for the defining prime,
including the exceptional rank three group over the field of order three. -/
theorem complete (D : SourceInputs parameters rank N C) :
    Nonempty (FamilyCertificate (TypeBOrthogonalOmegaCarriers.Omega n F) p) := by
  obtain ⟨witness⟩ := D.complete
  exact ⟨⟨D.family, D.facts.actualCover, (MulEquiv.refl _), witness⟩⟩

end ManuscriptIBAW.TypeB.Defining

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
