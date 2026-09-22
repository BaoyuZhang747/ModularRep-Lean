import ModularRep.BrauerCharacterKZero
import ModularRep.ExactCharacterBridge
import ModularRep.KZeroTwist
import ModularRep.OrdinaryCharacterKZero

/-!
# The decomposition map from stable-reduction character compatibility

This file isolates the remaining classical representation theoretic input
for the decomposition map.  It asks that reduction of every stable lattice
have Brauer character equal to the restriction of the ordinary character to
the `p`-regular elements.  From that one statement, Lean proves lattice
independence and constructs the exact decomposition homomorphism.

The compatibility proposition below is not proved in this library and is
not introduced as an axiom.  It is a theorem parameter at every use site.
-/

namespace ModularRep

open ExactGrothendieckGroup
open FDRepSimpleClassKZero

universe u

variable {p : ℕ} {K O k G : Type u}
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [Group G] [Finite G] [IsAlgClosed k]

/-- The exact remaining character-theoretic statement for stable-lattice
reduction: the Brauer character of every reduction is the ordinary
character restricted to the `p`-regular elements.

The characteristic instances are taken from `Msys`.  Existence of the root
embedding `iota` and the stronger algebraic-closure hypothesis used by the
current Brauer-character separation theorem remain explicit assumptions. -/
def StableReductionBrauerCharacterCompatibility
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G) : Prop := by
  letI := Msys.charP
  letI := Msys.charZero
  exact ∀ {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L : StableLattice O K rho),
    letI := Msys.residueAlgebra
    Representation.brauerCharacterOfRootEmbedding (L.reduction k) iota =
      Representation.regularTraceClassFunction rho p

/-- Stable-reduction character compatibility in the exact `K₀` character
maps. -/
theorem stableReduction_KZero_characterCompatibility
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    letI := Msys.charP
    letI := Msys.charZero
    brauerCharacterKZeroHom iota
        (classOf (FDRep k G) (FDRep.of (L.reduction k))) =
      ordinaryCharacterKZero p
        (classOf (FDRep K G) (FDRep.of rho)) := by
  let _ := Msys.residueAlgebra
  let _ := Msys.charP
  let _ := Msys.charZero
  rw [brauerCharacterKZeroHom_classOf, ordinaryCharacterKZero_classOf]
  exact hcompat rho L

/-- The concrete exact character bridge obtained from the stable-reduction
Brauer-character identity. -/
noncomputable def exactCharacterBridgeOfStableReduction
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota) :
    ExactCharacterBridge (G := G) Msys
      (PrimeRegularClassFunction K G p) := by
  letI := Msys.charP
  letI := Msys.charZero
  exact
    { ordinaryCharacterHom := ordinaryCharacterKZero p
      modularCharacterHom := brauerCharacterKZeroHom iota
      modularCharacterHom_injective :=
        brauerCharacterKZeroHom_injective iota
      stableReduction_compatible := fun rho L ↦
        stableReduction_KZero_characterCompatibility
          Msys iota hcompat rho L }

/-- The exact decomposition-map data constructed from the single
stable-reduction character-compatibility statement. -/
noncomputable def exactDecompositionMapDataOfStableReduction
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota) :
    ExactDecompositionMapData K k G :=
  ExactCharacterBridge.toExactDecompositionMapData Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat)

/-- The exact decomposition homomorphism obtained from stable-reduction
Brauer-character compatibility. -/
noncomputable def decompositionMapOfStableReduction
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota) :
    FDRepKZero K G →+ FDRepKZero k G :=
  ExactCharacterBridge.decompositionMap Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat)

/-- The decomposition homomorphism is characterised by the commuting square
between restricted ordinary characters and Brauer characters. -/
theorem decompositionMapOfStableReduction_characterSquare
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota) :
    letI := Msys.charP
    letI := Msys.charZero
    (brauerCharacterKZeroHom iota).comp
        (decompositionMapOfStableReduction Msys iota hcompat) =
      ordinaryCharacterKZero p := by
  let _ := Msys.charP
  let _ := Msys.charZero
  exact ExactCharacterBridge.decompositionMap_characterSquare Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat)

/-- The decomposition homomorphism is the unique additive map compatible
with the ordinary and Brauer character homomorphisms. -/
theorem existsUnique_decompositionMapOfStableReduction
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota) :
    letI := Msys.charP
    letI := Msys.charZero
    ∃! d : FDRepKZero K G →+ FDRepKZero k G,
      (brauerCharacterKZeroHom iota).comp d = ordinaryCharacterKZero p := by
  let _ := Msys.charP
  let _ := Msys.charZero
  exact ExactCharacterBridge.existsUnique_decompositionMap Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat)

/-- The constructed data represents reduction of every stable lattice. -/
theorem exactDecompositionMapDataOfStableReduction_realises
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota) :
    RealisesStableLatticeReduction Msys
      (exactDecompositionMapDataOfStableReduction Msys iota hcompat) :=
  ExactCharacterBridge.toExactDecompositionMapData_realises Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat)

/-- The decomposition homomorphism sends an ordinary representation class
to the modular exact `K₀` class of every stable-lattice reduction. -/
theorem decompositionMap_classOf_eq_stableLatticeReduction
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    decompositionMapOfStableReduction Msys iota hcompat
        (classOf (FDRep K G) (FDRep.of rho)) =
      classOf (FDRep k G) (FDRep.of (L.reduction k)) :=
  ExactCharacterBridge.decompositionMap_classOf_eq_reduction Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat) rho L

/-- The exact modular `K₀` class of a stable-lattice reduction is
independent of the selected stable lattice. -/
theorem stableLatticeReductionClass_eq
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    {V : Type u} [AddCommGroup V] [Module O V] [Module K V]
    [IsScalarTower O K V] [Module.Finite K V]
    (rho : Representation K G V) (L₁ L₂ : StableLattice O K rho) :
    letI := Msys.residueAlgebra
    classOf (FDRep k G) (FDRep.of (L₁.reduction k)) =
      classOf (FDRep k G) (FDRep.of (L₂.reduction k)) :=
  ExactCharacterBridge.reductionClass_eq Msys
    (exactCharacterBridgeOfStableReduction Msys iota hcompat) rho L₁ L₂

/-- The decomposition homomorphism commutes with automorphism twists.  This
is a formal consequence of its character-square characterisation and the
injectivity of the Brauer-character homomorphism. -/
theorem decompositionMapOfStableReduction_twist
    (Msys : ModularSystem p K O k)
    (iota : PrimeRegularRootEmbedding p k K G)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (alpha : MulAut G) (x : FDRepKZero K G) :
    decompositionMapOfStableReduction Msys iota hcompat
        (twistKZero (k := K) alpha x) =
      twistKZero (k := k) alpha
        (decompositionMapOfStableReduction Msys iota hcompat x) := by
  let _ := Msys.charP
  let _ := Msys.charZero
  apply brauerCharacterKZeroHom_injective iota
  have hsquare :=
    decompositionMapOfStableReduction_characterSquare Msys iota hcompat
  calc
    brauerCharacterKZeroHom iota
        (decompositionMapOfStableReduction Msys iota hcompat
          (twistKZero (k := K) alpha x)) =
        ordinaryCharacterKZero p (twistKZero (k := K) alpha x) := by
          exact DFunLike.congr_fun hsquare (twistKZero (k := K) alpha x)
    _ = (ordinaryCharacterKZero p x).twist alpha := by
          exact DFunLike.congr_fun
            (ordinaryCharacterKZero_twist (p := p) (K := K) alpha) x
    _ = (brauerCharacterKZeroHom iota
          (decompositionMapOfStableReduction Msys iota hcompat x)).twist alpha := by
          exact congrArg
            (fun f : PrimeRegularClassFunction K G p ↦ f.twist alpha)
            (DFunLike.congr_fun hsquare x).symm
    _ = brauerCharacterKZeroHom iota
          (twistKZero (k := k) alpha
            (decompositionMapOfStableReduction Msys iota hcompat x)) := by
          symm
          exact DFunLike.congr_fun
            (brauerCharacterKZeroHom_twist iota alpha)
            (decompositionMapOfStableReduction Msys iota hcompat x)

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
