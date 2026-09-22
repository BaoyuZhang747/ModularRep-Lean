import Formalisation.EquivariantActions
import Formalisation.FibreTransport
import Formalisation.IBAWCore
import Formalisation.IBAWOrbitTransport
import Mathlib.Tactic

/-!
# Paper proof: equivariant replacement on faithful central sectors

This file checks transport over an orbit of faithful central sectors.
Starting with a stabiliser equivariant equivalence on one faithful
central sector, Lean transports it over the orbit of faithful sectors and
proves that the resulting equivalence

* is independent of the chosen representative of a transported point;
* is equivariant for the full automorphism action;
* preserves its sector and every additional equivariant label, in particular
  a block label;
* induces the required local equivalences after decomposition by radical
  subgroup; and
* gives identical stabilisers to every matched pair.

The final character triple assertion remains relative to the exact
An--Dietrich and cyclic extension input.  Its interface exposes the global
and local factor set classes, their triviality for cyclic outer stabilisers,
and the natural identification separately.  No AWC-goodness, character
triple conclusion, or iBAW conclusion is an input to the transport theorem.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Relative

open Formalisation
open Formalisation.IBAW

universe u

variable {A Sector Block Radical Brauer Weight : Type u}
variable [Group A]
variable [MulAction A Sector] [MulAction A Block] [MulAction A Radical]
variable [MulAction A Brauer] [MulAction A Weight]

/-- The labels and compatibility predicates used by the replacement lemma.
The types model only faithful central sectors.  Routine facts identifying
these sets with the appropriate character theoretic objects are external. -/
structure ReplacementContext where
  brauerSector : Brauer → Sector
  weightSector : Weight → Sector
  brauerBlock : Brauer → Block
  weightBlock : Weight → Block
  weightRadical : Weight → Radical
  brauerSector_equivariant : ∀ (a : A) (x : Brauer),
    brauerSector (a • x) = a • brauerSector x
  weightSector_equivariant : ∀ (a : A) (y : Weight),
    weightSector (a • y) = a • weightSector y
  brauerBlock_equivariant : ∀ (a : A) (x : Brauer),
    brauerBlock (a • x) = a • brauerBlock x
  weightBlock_equivariant : ∀ (a : A) (y : Weight),
    weightBlock (a • y) = a • weightBlock y
  weightRadical_equivariant : ∀ (a : A) (y : Weight),
    weightRadical (a • y) = a • weightRadical y
  characterTripleOK : Brauer → Weight → Prop
  characterTriple_equivariant :
    PairPropertyEquivariant (A := A) (X := Brauer) (Y := Weight)
      characterTripleOK

variable (C : ReplacementContext
  (A := A) (Sector := Sector) (Block := Block) (Radical := Radical)
  (Brauer := Brauer) (Weight := Weight))

/-- The transported family before the representation theoretic character
triple condition is attached.  The radical part is derived from the image,
so it cannot fail to be a partition. -/
structure Candidate where
  equiv : Brauer ≃ Weight
  equiv_equivariant : ∀ (a : A) (x : Brauer),
    equiv (a • x) = a • equiv x
  sector_preserving : ∀ x : Brauer,
    C.weightSector (equiv x) = C.brauerSector x
  block_preserving : ∀ x : Brauer,
    C.weightBlock (equiv x) = C.brauerBlock x

namespace Candidate

/-- The radical subgroup class indexing the part containing `x`. -/
def part (W : Candidate C) (x : Brauer) : Radical :=
  C.weightRadical (W.equiv x)

/-- The radical decomposition transported by the replacement is equivariant. -/
theorem part_equivariant (W : Candidate C) (a : A) (x : Brauer) :
    part C W (a • x) = a • part C W x := by
  simp only [part, W.equiv_equivariant, C.weightRadical_equivariant]

/-- Restriction of the transported equivalence to one sector, block, and
radical subgroup class.  This is the local bijection obtained by decomposing
the global replacement. -/
def localEquiv (W : Candidate C) (sector : Sector) (block : Block)
    (radical : Radical) :
    {x : Brauer // C.brauerSector x = sector ∧
      C.brauerBlock x = block ∧ part C W x = radical} ≃
    {y : Weight // C.weightSector y = sector ∧
      C.weightBlock y = block ∧ C.weightRadical y = radical} where
  toFun x := ⟨W.equiv x, by
    refine ⟨?_, ?_, ?_⟩
    · exact (W.sector_preserving x).trans x.property.1
    · exact (W.block_preserving x).trans x.property.2.1
    · exact x.property.2.2⟩
  invFun y := ⟨W.equiv.symm y, by
    refine ⟨?_, ?_, ?_⟩
    · calc
        C.brauerSector (W.equiv.symm y) =
            C.weightSector (W.equiv (W.equiv.symm y)) :=
          (W.sector_preserving (W.equiv.symm y)).symm
        _ = C.weightSector y :=
          congrArg C.weightSector (W.equiv.apply_symm_apply y)
        _ = sector := y.property.1
    · calc
        C.brauerBlock (W.equiv.symm y) =
            C.weightBlock (W.equiv (W.equiv.symm y)) :=
          (W.block_preserving (W.equiv.symm y)).symm
        _ = C.weightBlock y :=
          congrArg C.weightBlock (W.equiv.apply_symm_apply y)
        _ = block := y.property.2.1
    · change C.weightRadical (W.equiv (W.equiv.symm y)) = radical
      rw [W.equiv.apply_symm_apply]
      exact y.property.2.2⟩
  left_inv x := by
    apply Subtype.ext
    exact W.equiv.symm_apply_apply x
  right_inv y := by
    apply Subtype.ext
    exact W.equiv.apply_symm_apply y

/-- Every matched pair has exactly the same automorphism stabiliser.  This is
the set theoretic step used before applying the cyclic extension theorem to
the two factor set classes. -/
theorem stabilizer_eq (W : Candidate C) (x : Brauer) :
    MulAction.stabilizer A x = MulAction.stabilizer A (W.equiv x) :=
  Formalisation.stabilizer_eq_of_injective_equivariant
    W.equiv.injective W.equiv_equivariant x

/-- Elementwise form: an automorphism fixes a Brauer character precisely
when it fixes its matched weight class. -/
theorem fixed_iff (W : Candidate C) (a : A) (x : Brauer) :
    a • x = x ↔ a • W.equiv x = W.equiv x :=
  Formalisation.fixed_iff_of_injective_equivariant
    W.equiv.injective W.equiv_equivariant a x

end Candidate

/-- Transport the bijection on one faithful sector over the full transitive
orbit of faithful sectors.  The premise `he₀` is exactly equivariance for the
stabiliser of the chosen sector, not a global equivariance assumption. -/
def equivariantReplacement
    (sector₀ : Sector) (transporter : Sector → A)
    (htransporter : ∀ sector, transporter sector • sector₀ = sector)
    (e₀ : Fibre C.brauerSector sector₀ ≃
      Fibre C.weightSector sector₀)
    (he₀ : ∀ (a : A) (ha : a • sector₀ = sector₀)
      (x : Fibre C.brauerSector sector₀),
      e₀ (stabilizerFibreEquiv C.brauerSector
          C.brauerSector_equivariant sector₀ a ha x) =
        stabilizerFibreEquiv C.weightSector
          C.weightSector_equivariant sector₀ a ha (e₀ x))
    (hblock : ∀ x : Fibre C.brauerSector sector₀,
      C.weightBlock (e₀ x) = C.brauerBlock x) : Candidate C where
  equiv := transportedEquiv C.brauerSector C.weightSector
    C.brauerSector_equivariant C.weightSector_equivariant
    sector₀ transporter htransporter e₀
  equiv_equivariant := transportedEquiv_equivariant
    C.brauerSector C.weightSector
    C.brauerSector_equivariant C.weightSector_equivariant
    sector₀ transporter htransporter e₀ he₀
  sector_preserving := transportedEquiv_preserves_base
    C.brauerSector C.weightSector
    C.brauerSector_equivariant C.weightSector_equivariant
    sector₀ transporter htransporter e₀
  block_preserving := transportedEquiv_preserves_label
    C.brauerSector C.weightSector
    C.brauerSector_equivariant C.weightSector_equivariant
    C.brauerBlock C.weightBlock
    C.brauerBlock_equivariant C.weightBlock_equivariant
    sector₀ transporter htransporter e₀ hblock

/-- The global equivalence is independent of the chosen transporters.  This
is the formal well definedness check behind choosing an automorphism carrying
the initial central character to a given faithful central character. -/
theorem equivariantReplacement_equiv_independent
    (sector₀ : Sector) (transporter transporter' : Sector → A)
    (htransporter : ∀ sector, transporter sector • sector₀ = sector)
    (htransporter' : ∀ sector, transporter' sector • sector₀ = sector)
    (e₀ : Fibre C.brauerSector sector₀ ≃
      Fibre C.weightSector sector₀)
    (he₀ : ∀ (a : A) (ha : a • sector₀ = sector₀)
      (x : Fibre C.brauerSector sector₀),
      e₀ (stabilizerFibreEquiv C.brauerSector
          C.brauerSector_equivariant sector₀ a ha x) =
        stabilizerFibreEquiv C.weightSector
          C.weightSector_equivariant sector₀ a ha (e₀ x))
    (hblock : ∀ x : Fibre C.brauerSector sector₀,
      C.weightBlock (e₀ x) = C.brauerBlock x) :
    (equivariantReplacement C sector₀ transporter htransporter
      e₀ he₀ hblock).equiv =
    (equivariantReplacement C sector₀ transporter' htransporter'
      e₀ he₀ hblock).equiv :=
  transportedEquiv_independent_of_transporter
    C.brauerSector C.weightSector
    C.brauerSector_equivariant C.weightSector_equivariant
    sector₀ transporter transporter'
    htransporter htransporter' e₀ he₀

/-- The exact external data used for the character triple sentence in the
manuscript.  `Outer` models the outer automorphism quotient and
`FactorClass` a common target after An--Dietrich's natural identification of
the global and local second cohomology groups.

The two triviality fields are the conclusions of the ordinary and Brauer
cyclic extension theorems together with the factor set criterion.  The final
field merely unpacks An--Dietrich Definition 4.4(3d) after equality of the
outer stabilisers and factor set classes has been established. -/
structure CyclicFactorSetBridge
    (Outer FactorClass : Type u) [Group Outer] [IsCyclic Outer] where
  neutral : FactorClass
  brauerOuterStabilizer : Brauer → Subgroup Outer
  weightOuterStabilizer : Weight → Subgroup Outer
  outerStabilizers_eq_of_stabilizers_eq : ∀ (x : Brauer) (y : Weight),
    MulAction.stabilizer A x = MulAction.stabilizer A y →
      brauerOuterStabilizer x = weightOuterStabilizer y
  brauerFactorClass : Brauer → FactorClass
  weightFactorClass : Weight → FactorClass
  brauerFactorClass_trivial_of_cyclic : ∀ x : Brauer,
    IsCyclic (brauerOuterStabilizer x) → brauerFactorClass x = neutral
  weightFactorClass_trivial_of_cyclic : ∀ y : Weight,
    IsCyclic (weightOuterStabilizer y) → weightFactorClass y = neutral
  characterTriple_of_factorClasses : ∀ (x : Brauer) (y : Weight),
    brauerOuterStabilizer x = weightOuterStabilizer y →
    brauerFactorClass x = weightFactorClass y →
      C.characterTripleOK x y

/-- Every subgroup of the cyclic outer group is cyclic, so the ordinary and
Brauer extension inputs make both factor set classes neutral.  Lean combines
this with the stabiliser equality proved for the transported bijection. -/
theorem characterTriple_of_cyclic_factor_sets
    {Outer FactorClass : Type u} [Group Outer] [IsCyclic Outer]
    (W : Candidate C)
    (bridge : CyclicFactorSetBridge C Outer FactorClass)
    (x : Brauer) : C.characterTripleOK x (W.equiv x) := by
  have hStabilizer := Candidate.stabilizer_eq C W x
  have hOuter : bridge.brauerOuterStabilizer x =
      bridge.weightOuterStabilizer (W.equiv x) :=
    bridge.outerStabilizers_eq_of_stabilizers_eq x (W.equiv x) hStabilizer
  have hBrauerCyclic : IsCyclic (bridge.brauerOuterStabilizer x) :=
    inferInstance
  have hWeightCyclic : IsCyclic
      (bridge.weightOuterStabilizer (W.equiv x)) := inferInstance
  apply bridge.characterTriple_of_factorClasses x (W.equiv x) hOuter
  calc
    bridge.brauerFactorClass x = bridge.neutral :=
      bridge.brauerFactorClass_trivial_of_cyclic x hBrauerCyclic
    _ = bridge.weightFactorClass (W.equiv x) :=
      (bridge.weightFactorClass_trivial_of_cyclic
        (W.equiv x) hWeightCyclic).symm

/-- Alternatively, if the representation theoretic compatibility is
certified on the initial sector, equivariance transports it to every faithful
sector.  This checks preservation of the character triple condition under
transport. -/
theorem transported_characterTriple
    (sector₀ : Sector) (transporter : Sector → A)
    (htransporter : ∀ sector, transporter sector • sector₀ = sector)
    (e₀ : Fibre C.brauerSector sector₀ ≃
      Fibre C.weightSector sector₀)
    (hbase : ∀ x : Fibre C.brauerSector sector₀,
      C.characterTripleOK x (e₀ x))
    (x : Brauer) :
    C.characterTripleOK x
      (transportedEquiv C.brauerSector C.weightSector
        C.brauerSector_equivariant C.weightSector_equivariant
        sector₀ transporter htransporter e₀ x) :=
  transportedEquiv_pairProperty
    C.brauerSector C.weightSector
    C.brauerSector_equivariant C.weightSector_equivariant
    sector₀ transporter htransporter e₀ C.characterTripleOK
    C.characterTriple_equivariant hbase x

/-- The transport conclusion under explicit source assumptions constructs the replacement,
the local radical-subgroup bijections, and character triple compatibility.
The only representation theoretic premise is the separately named cyclic
factor set bridge. -/
theorem lemma_5_5_relative
    {Outer FactorClass : Type u} [Group Outer] [IsCyclic Outer]
    (sector₀ : Sector) (transporter : Sector → A)
    (htransporter : ∀ sector, transporter sector • sector₀ = sector)
    (e₀ : Fibre C.brauerSector sector₀ ≃
      Fibre C.weightSector sector₀)
    (he₀ : ∀ (a : A) (ha : a • sector₀ = sector₀)
      (x : Fibre C.brauerSector sector₀),
      e₀ (stabilizerFibreEquiv C.brauerSector
          C.brauerSector_equivariant sector₀ a ha x) =
        stabilizerFibreEquiv C.weightSector
          C.weightSector_equivariant sector₀ a ha (e₀ x))
    (hblock : ∀ x : Fibre C.brauerSector sector₀,
      C.weightBlock (e₀ x) = C.brauerBlock x)
    (bridge : CyclicFactorSetBridge C Outer FactorClass) :
    ∃ W : Candidate C,
      (∀ x : Brauer, C.characterTripleOK x (W.equiv x)) ∧
      (∀ (sector : Sector) (block : Block) (radical : Radical),
        Nonempty
          ({x : Brauer // C.brauerSector x = sector ∧
              C.brauerBlock x = block ∧
              Candidate.part C W x = radical} ≃
            {y : Weight // C.weightSector y = sector ∧
              C.weightBlock y = block ∧
              C.weightRadical y = radical})) := by
  let W := equivariantReplacement C sector₀ transporter htransporter
    e₀ he₀ hblock
  refine ⟨W, ?_, ?_⟩
  · exact characterTriple_of_cyclic_factor_sets C W bridge
  · intro sector block radical
    exact ⟨Candidate.localEquiv C W sector block radical⟩

end ModularRep.PaperProofs.SporadicEquivariantReplacementLemma55Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
