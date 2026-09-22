import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
import ModularRep.PaperProofs.EvenFieldLeviTorus

/-!
# From the characteristic torus to the algebraic-torus label

The manuscript first proves that the concrete algebraic torus
`Z⁰(M)_(phi_e)` is stable under the constructed inner twisted automorphism.
The dependent generic-pair carrier instead needs equality of the corresponding
abstract torus label.  This file supplies that bridge.

Only compatibility for the selected label and selected automorphism is
assumed.  There is no global compatibility axiom for every automorphism and
no label fixedness hypothesis.  Injectivity of the concrete realisation map
turns the subgroup equality proved in `EvenFieldLeviTorus` into the required
label equality.
-/

namespace ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation

open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldLeviTorus

universe u

variable {Gbar H A : Type u}
    [Group Gbar] [Group H] [MulAction (MulAut H) A]

/-- The checked characteristic-torus equality implies equality of the
corresponding abstract torus label.

The map `realise` sends a torus label to its concrete algebraic subgroup in
`Gbar`.  The equality `realise_selected` identifies the selected label with
`Z⁰(g L g⁻¹)_(phi_e)`.  The equality `realise_transport` is the narrowly
stated compatibility between transport of this one label by `tauH` and
transport of its realisation by the algebraic inner twisted automorphism.
-/
theorem label_fixed_of_characteristicTorus_stable
    (sigma : MulAut Gbar) (g : Gbar) (L : Subgroup Gbar)
    (L_stable : L.map sigma.toMonoidHom = L)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (natural : CharacteristicTorusNatural centralSylow)
    (tauH : MulAut H) (T : A)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise)
    (realise_selected :
      realise T = centralSylow (conjugateSubgroup L g))
    (realise_transport :
      realise (tauH • T) =
        (realise T).map (innerTwistedAut sigma g).toMonoidHom) :
    tauH • T = T := by
  apply realise_injective
  calc
    realise (tauH • T) =
        (realise T).map (innerTwistedAut sigma g).toMonoidHom :=
      realise_transport
    _ = (centralSylow (conjugateSubgroup L g)).map
          (innerTwistedAut sigma g).toMonoidHom := by
      rw [realise_selected]
    _ = centralSylow (conjugateSubgroup L g) :=
      characteristicTorus_stable sigma g L L_stable centralSylow natural
    _ = realise T := realise_selected.symm

/-- Pair-level form of
`label_fixed_of_characteristicTorus_stable`, with the selected label read
from the first component of a dependent local pair. -/
theorem localPair_label_fixed_of_characteristicTorus_stable
    {k : Type u} [Field k]
    (sigma : MulAut Gbar) (g : Gbar) (L : Subgroup Gbar)
    (L_stable : L.map sigma.toMonoidHom = L)
    (centralSylow : Subgroup Gbar → Subgroup Gbar)
    (natural : CharacteristicTorusNatural centralSylow)
    (tauH : MulAut H) (P : LocalPair k H A)
    (realise : A → Subgroup Gbar)
    (realise_injective : Function.Injective realise)
    (realise_selected :
      realise P.1 = centralSylow (conjugateSubgroup L g))
    (realise_transport :
      realise (tauH • P.1) =
        (realise P.1).map (innerTwistedAut sigma g).toMonoidHom) :
    tauH • P.1 = P.1 :=
  label_fixed_of_characteristicTorus_stable sigma g L L_stable
    centralSylow natural tauH P.1 realise realise_injective
    realise_selected realise_transport

end ModularRep.PaperProofs.EvenFieldAlgebraicTorusLabelFixation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
