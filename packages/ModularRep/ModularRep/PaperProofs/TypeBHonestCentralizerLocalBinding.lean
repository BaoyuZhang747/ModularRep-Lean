import ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
import ModularRep.PaperProofs.TypeBSpathHonestLocalExtensionSource
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The literal centralizer map for the chosen honest ambient

The centralizer of the base is the center of the chosen Spath ambient, so it
normalizes the selected radical. This determines an inclusion into the actual
local normalizer before any block-triple witness is chosen. Every complete
triple on these same two subgroups uses this very inclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBHonestCentralizerLocalBinding

open ModularRep
open EvenFieldFLZSourceConditions EvenFieldFLZBAWGoodFamily
open TypeBCentralKernelTripleCertificate

variable {P : Definition35Problem} {reference psi : Definition35Brauer P}
  {quotient : CentralQuotientBrauerSource P reference psi}
  (w : Definition35Weight P)
  (ambient : SpathAmbientGroup P reference psi quotient)

/-- The ambient record alone places the actual base centralizer inside the
full normalizer of the selected radical. -/
theorem centralizer_le_local :
    Subgroup.centralizer (ambient.base : Set ambient.A) ≤
      AmbientLocalGroup P reference psi w quotient ambient := by
  rw [ambient.baseCentralizer_eq_center]
  exact Subgroup.center_le_normalizer _

/-- The literal inclusion of the base centralizer into the actual normalizer.
Its definition does not depend on a block-triple witness. -/
def centralizerToLocal :
    Subgroup.centralizer (ambient.base : Set ambient.A) →*
      AmbientLocalGroup P reference psi w quotient ambient :=
  Subgroup.inclusion (centralizer_le_local w ambient)

@[simp] theorem centralizerToLocal_coe
    (x : Subgroup.centralizer (ambient.base : Set ambient.A)) :
    ((centralizerToLocal w ambient x :
      AmbientLocalGroup P reference psi w quotient ambient) : ambient.A) =
        (x : ambient.A) := rfl

@[simp] theorem centralizerToLocal_subtype :
    (AmbientLocalGroup P reference psi w quotient ambient).subtype.comp
        (centralizerToLocal w ambient) =
      (Subgroup.centralizer (ambient.base : Set ambient.A)).subtype := rfl

variable (D : TripleData (p := P.p) (k := P.k) (K := P.K)
    ambient.base (AmbientLocalGroup P reference psi w quotient ambient))
  {theta : IBr D.base.iota} {phi : IBr D.localData.iota}

/-- Every complete block triple on these literal subgroups has the same
centralizer inclusion as the one fixed directly by the ambient record. -/
theorem centralizerToLocal_eq_witness (witness : BlockTripleWitness D theta phi) :
    centralizerToLocal w ambient =
      TypeBSpathHonestLocalExtensionSource.centralizerToLocal D witness := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  rfl

end ModularRep.PaperProofs.TypeBHonestCentralizerLocalBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
