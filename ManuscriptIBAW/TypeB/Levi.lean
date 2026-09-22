import ModularRep.ComponentReturnFull
import ModularRep.PaperProofs.TypeBRegularLeviOrbitAssembly
import ModularRep.PaperProofs.TypeBCurrentCliffordStabilizer
import ModularRep.PaperProofs.TypeBCurrentLeviAssembly

/-!
# The Type B Levi lemmas

The fixed representative construction in Lemma 4.4, the rational product and character orbit
in Lemma 4.5, and Clifford transfer at an arbitrary prime in Lemma 4.6 are
proved below. The Clifford proof requires no additional exponent condition
on the effective quotient.

The product for the regular Levi subgroup uses the specified algebraic
components, Frobenius, connected centre and Lang equations. Identifying each
conjugation image with the full group of inner and diagonal automorphisms
remains a structural source assumption. The character product and Clifford
sources retain their original groups and root agreements.

At the prime two, multiplicity freeness for the regular embedding of the
derived Levi group first gives extension of the constituent to its ambient
inertia group. In the representative construction, one ambient element
conjugates both the constituent and the original Levi character. These steps
are proved from the source assumptions.
-/

namespace ManuscriptIBAW.TypeB.Levi

export ModularRep.ManuscriptVerification.ComponentReturnFull
  (component_return_full component_return_full_of_product_orbit_stable)
export ModularRep.PaperProofs.TypeBRegularLeviOrbitAssembly
  (rationalProduct imageProduct_surjective cartesian_character_orbit)
export ModularRep.PaperProofs.TypeBCurrentCliffordStabilizer (lemma46)
export ModularRep.PaperProofs.TypeBCurrentLeviAssembly (same_y_representative)

end ManuscriptIBAW.TypeB.Levi

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
