import ModularRep.IBrSimpleModuleClass
import ModularRep.BrauerTraceRecovery
import ModularRep.ModularTraceFunction
import ModularRep.ModularTraceRegularPart
import ModularRep.ModularTraceSeparation
import Mathlib.RepresentationTheory.Character

/-!
# Separation of simple modules by irreducible Brauer characters

This file proves the separation result needed to identify simple group algebra
module classes with the function-valued set `IBr`.
Navarro, *Characters and Blocks of Finite Groups*, Theorem (1.19), printed
pp. 12--13, proves linear independence of the trace functions of pairwise
nonsimilar irreducible representations.  `ModularTraceSeparation` proves the
pairwise consequence needed here: equal trace functions determine an
irreducible representation up to isomorphism.  Lemma (2.4), printed p. 19,
recovers a modular trace function from its Brauer character.  Its
characteristic-`p` trace calculation is proved in `ModularTraceRegularPart`,
and `BrauerTraceRecovery` proves the required additive compatibility for every
multiplicative equivalence of the relevant root groups.  Thus the explicit
`PrimeRegularRootEmbedding` already suffices for character injectivity.

The proof of Navarro's Theorem (2.6), printed pp. 20--21, also establishes
linear independence of the conventional complex-valued irreducible Brauer
character family.  `BrauerCharacterLinearIndependence` proves that stronger
conclusion over the present characteristic-zero target field by transporting a
nonsingular prime regular evaluation matrix through the root equivalence.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.FDRepSimpleClassKZero

universe u v

variable {p : ℕ} {k G : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Equality of modular trace functions determines an irreducible
representation up to isomorphism.  This is the pairwise consequence of
Navarro, Theorem (1.19), printed pp. 12--13, needed below. -/
def IrreducibleModularTraceDeterminesRepresentation : Prop :=
  ∀ (V W : FDRep k G),
    Representation.IsIrreducible V.ρ →
    Representation.IsIrreducible W.ρ →
    Representation.character V.ρ = Representation.character W.ρ →
      Nonempty (V ≅ W)

omit [Finite G] in
/-- Navarro's trace-separation input is proved from Schur's lemma and
Jacobson density in `ModularTraceSeparation`. -/
theorem irreducibleModularTraceDeterminesRepresentation :
    IrreducibleModularTraceDeterminesRepresentation (k := k) (G := G) := by
  intro V W hV hW hchar
  exact ModularTraceSeparation.fdRep_nonempty_iso_of_character_eq
    V W hV hW hchar

/-- Equality of one lifted Brauer-character value determines equality of the
corresponding modular traces at a `p`-regular element.  This isolates the
remaining additive compatibility of the chosen multiplicative root lift. -/
def BrauerValueDeterminesRegularTrace
    (iota : PrimeRegularRootEmbedding p k K G) : Prop :=
  ∀ (V W : FDRep k G) (g : PrimeRegularElement (G := G) p),
    Representation.brauerCharacterOfRootEmbedding V.ρ iota g =
        Representation.brauerCharacterOfRootEmbedding W.ρ iota g →
      Representation.character V.ρ g.1 =
        Representation.character W.ρ g.1

/-- Equality of lifted Brauer-character functions determines equality of the
modular trace functions. -/
def BrauerCharacterDeterminesModularTrace
    (iota : PrimeRegularRootEmbedding p k K G) : Prop :=
  ∀ (V W : FDRep k G),
    Representation.brauerCharacterOfRootEmbedding V.ρ iota =
      Representation.brauerCharacterOfRootEmbedding W.ρ iota →
    Representation.character V.ρ = Representation.character W.ρ

/-- The trace of a group element equals the trace of its canonical
`p`-regular part.  Consequently the pointwise regular-trace compatibility of
the root lift implies recovery of the whole modular trace function. -/
theorem brauerCharacterDeterminesModularTrace_of_regularTrace
    (iota : PrimeRegularRootEmbedding p k K G)
    (hregular : BrauerValueDeterminesRegularTrace iota) :
    BrauerCharacterDeterminesModularTrace iota := by
  intro V W hBrauer
  funext g
  rw [Representation.character_eq_character_primeRegularPart
      iota.prime V.ρ g,
    Representation.character_eq_character_primeRegularPart
      iota.prime W.ρ g]
  let greg : PrimeRegularElement (G := G) p :=
    ⟨primeRegularPart iota.prime g,
      primeRegular_primeRegularPart iota.prime g⟩
  apply hregular V W greg
  exact congrArg
    (fun f : PrimeRegularClassFunction K G p ↦ f greg) hBrauer

/-- The explicit multiplicative equivalence of prime regular roots reflects
the additive root sums defining the Brauer values, so it determines modular
traces on prime regular elements. -/
theorem brauerValueDeterminesRegularTrace_of_rootEmbedding
    (iota : PrimeRegularRootEmbedding p k K G) :
    BrauerValueDeterminesRegularTrace iota := by
  intro V W g h
  exact BrauerTraceRecovery.character_apply_eq_of_brauerCharacter_apply_eq
    V.ρ W.ρ iota g h

/-- The function-valued Brauer character therefore determines the complete
modular trace function. -/
theorem brauerCharacterDeterminesModularTrace_of_rootEmbedding
    (iota : PrimeRegularRootEmbedding p k K G) :
    BrauerCharacterDeterminesModularTrace iota :=
  brauerCharacterDeterminesModularTrace_of_regularTrace iota
    (brauerValueDeterminesRegularTrace_of_rootEmbedding iota)

/-- The family of function-valued irreducible Brauer characters indexed by
simple group algebra module classes. -/
def simpleClassBrauerFamily
    (iota : PrimeRegularRootEmbedding p k K G) :
    SimpleModuleClass k[G] →
      (PrimeRegularElement (G := G) p → K) :=
  fun X ↦ (simpleClassToIBr iota X).1.toFun

/-- Linear independence of the irreducible Brauer character functions
indexed by simple group algebra module classes. -/
def IrreducibleBrauerCharacterLinearIndependence
    (iota : PrimeRegularRootEmbedding p k K G) : Prop :=
  LinearIndependent K (simpleClassBrauerFamily iota)

/-- Distinct simple group algebra module classes afford distinct
function-valued irreducible Brauer characters. -/
def IrreducibleBrauerCharacterInjectivity
    (iota : PrimeRegularRootEmbedding p k K G) : Prop :=
  Function.Injective (simpleClassToIBr iota)

/-- Linear independence of the simple-class Brauer character family implies
injectivity of the map to function-valued irreducible Brauer characters. -/
theorem irreducibleBrauerCharacterInjectivity_of_linearIndependence
    (iota : PrimeRegularRootEmbedding p k K G)
    (hlin : IrreducibleBrauerCharacterLinearIndependence iota) :
    IrreducibleBrauerCharacterInjectivity iota := by
  intro X Y hXY
  exact hlin.injective
    (congrArg (fun phi : IBr iota ↦ phi.1.toFun) hXY)

/-- The trace-function theorem and recovery of modular traces from Brauer
characters together imply injectivity of the simple-class Brauer character
map. -/
theorem irreducibleBrauerCharacterInjectivity_of_trace
    (iota : PrimeRegularRootEmbedding p k K G)
    (htrace :
      IrreducibleModularTraceDeterminesRepresentation (k := k) (G := G))
    (hrecover : BrauerCharacterDeterminesModularTrace iota) :
    IrreducibleBrauerCharacterInjectivity iota := by
  intro X Y hXY
  have hBrauer :
      Representation.brauerCharacterOfRootEmbedding
          (simpleClassFDRep X).ρ iota =
        Representation.brauerCharacterOfRootEmbedding
          (simpleClassFDRep Y).ρ iota :=
    congrArg (fun phi : IBr iota ↦ phi.1) hXY
  have hchar := hrecover (simpleClassFDRep X) (simpleClassFDRep Y) hBrauer
  obtain ⟨e⟩ := htrace (simpleClassFDRep X) (simpleClassFDRep Y)
    (simpleClassFDRep_irreducible X) (simpleClassFDRep_irreducible Y) hchar
  apply Subtype.ext
  rw [← toSkeleton_fromSkeleton_obj X.1,
    ← toSkeleton_fromSkeleton_obj Y.1]
  apply congr_toSkeleton_of_iso
  exact (simpleClassFDRepModuleIso X).symm ≪≫
    (FDRepFiniteLength.toModuleMonoidAlgebra
      (k := k) (G := G)).mapIso e ≪≫
    simpleClassFDRepModuleIso Y

/-- Conditional form of the trace route: recovery of the modular trace
function implies character injectivity. -/
theorem irreducibleBrauerCharacterInjectivity_of_modularTraceRecovery
    (iota : PrimeRegularRootEmbedding p k K G)
    (hrecover : BrauerCharacterDeterminesModularTrace iota) :
    IrreducibleBrauerCharacterInjectivity iota :=
  irreducibleBrauerCharacterInjectivity_of_trace iota
    irreducibleModularTraceDeterminesRepresentation hrecover

/-- Pointwise recovery on `p`-regular elements is enough for the conditional
trace route to character injectivity. -/
theorem irreducibleBrauerCharacterInjectivity_of_regularTraceRecovery
    (iota : PrimeRegularRootEmbedding p k K G)
    (hregular : BrauerValueDeterminesRegularTrace iota) :
    IrreducibleBrauerCharacterInjectivity iota :=
  irreducibleBrauerCharacterInjectivity_of_modularTraceRecovery iota
    (brauerCharacterDeterminesModularTrace_of_regularTrace iota hregular)

/-- Every explicit prime regular root embedding makes the map from simple
module classes to function-valued irreducible Brauer characters injective. -/
theorem irreducibleBrauerCharacterInjectivity_of_rootEmbedding
    (iota : PrimeRegularRootEmbedding p k K G) :
    IrreducibleBrauerCharacterInjectivity iota :=
  irreducibleBrauerCharacterInjectivity_of_modularTraceRecovery iota
    (brauerCharacterDeterminesModularTrace_of_rootEmbedding iota)

/-- The simple-module map to function-valued irreducible Brauer characters is
bijective for every explicit prime regular root embedding. -/
theorem simpleClassToIBr_bijective_of_rootEmbedding
    (iota : PrimeRegularRootEmbedding p k K G) :
    Function.Bijective (simpleClassToIBr iota) :=
  ⟨irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota,
    simpleClassToIBr_surjective iota⟩

/-- Once irreducible Brauer characters separate simple modules, the chosen
simple-module representatives and function-valued `IBr` are equivalent. -/
noncomputable def simpleModuleClassEquivIBr
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota) :
    SimpleModuleClass k[G] ≃ IBr iota :=
  Equiv.ofBijective (simpleClassToIBr iota)
    ⟨hinj, simpleClassToIBr_surjective iota⟩

/-- The canonical equivalence obtained from the explicit root embedding. -/
noncomputable def simpleModuleClassEquivIBrOfRootEmbedding
    (iota : PrimeRegularRootEmbedding p k K G) :
    SimpleModuleClass k[G] ≃ IBr iota :=
  Equiv.ofBijective (simpleClassToIBr iota)
    (simpleClassToIBr_bijective_of_rootEmbedding iota)

@[simp]
theorem simpleModuleClassEquivIBr_apply
    (iota : PrimeRegularRootEmbedding p k K G)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (X : SimpleModuleClass k[G]) :
    simpleModuleClassEquivIBr iota hinj X = simpleClassToIBr iota X :=
  rfl

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
