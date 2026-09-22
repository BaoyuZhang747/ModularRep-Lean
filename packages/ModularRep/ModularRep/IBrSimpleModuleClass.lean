import ModularRep.IrreducibleBrauerCharacter
import ModularRep.SimpleModuleClassFinite

/-!
# Simple-module labels for function-valued irreducible Brauer characters

The Brauer character of a simple `k[G]`-module defines an element of the
function-valued set `IBr`.  Every element of `IBr` has such a label by its
definition, so this construction is surjective.  Together with finiteness of
simple-module classes, this proves finiteness of `IBr` without assuming that
the Brauer-character map is injective.
-/

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra

namespace ModularRep.FDRepSimpleClassKZero

universe u v

variable {p : ℕ} {k G : Type u} {K : Type v}
variable [Field k] [Field K] [Group G] [Finite G]
variable [CharP k p] [IsAlgClosed k] [CharZero K]

omit [IsAlgClosed k] in
/-- The finite dimensional representation chosen from a simple
group algebra module class is irreducible. -/
theorem simpleClassFDRep_irreducible
    (X : SimpleModuleClass k[G]) :
    Representation.IsIrreducible (simpleClassFDRep X).ρ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact simple_iff_isSimpleModule.mp
    (simpleClassFDRep_underlying_simple X)

/-- Send a simple group algebra module class to its function-valued
irreducible Brauer character. -/
def simpleClassToIBr
    (iota : PrimeRegularRootEmbedding p k K G)
    (X : SimpleModuleClass k[G]) : IBr iota :=
  ⟨Representation.brauerCharacterOfRootEmbedding
      (simpleClassFDRep X).ρ iota,
    ⟨simpleClassFDRep X, simpleClassFDRep_irreducible X, rfl⟩⟩

/-- The simple-module class underlying an irreducible finite dimensional
representation. -/
def simpleClassOfIrreducibleFDRep
    (V : FDRep k G) (hV : Representation.IsIrreducible V.ρ) :
    SimpleModuleClass k[G] := by
  let M := (FDRepFiniteLength.toModuleMonoidAlgebra
    (k := k) (G := G)).obj V
  have hM : Simple M := by
    rw [simple_iff_isSimpleModule]
    exact (Representation.irreducible_iff_isSimpleModule_asModule V.ρ).mp hV
  exact ⟨toSkeleton M, Simple.of_iso (fromSkeletonToSkeletonIso M)⟩

/-- The representation chosen from the preceding simple-module class is
isomorphic to the original irreducible representation. -/
def simpleClassOfIrreducibleFDRepIso
    (V : FDRep k G) (hV : Representation.IsIrreducible V.ρ) :
    simpleClassFDRep (simpleClassOfIrreducibleFDRep V hV) ≅ V := by
  let E := FDRepGroupAlgebraEquivalence.equivalenceFGModule k G
  let M := (FDRepFiniteLength.toModuleMonoidAlgebra
    (k := k) (G := G)).obj V
  let eFG : simpleClassFGModule (simpleClassOfIrreducibleFDRep V hV) ≅
      E.functor.obj V := by
    apply (ModuleCat.isFG k[G]).isoMk
    exact fromSkeletonToSkeletonIso M
  exact E.inverse.mapIso eFG ≪≫ (E.unitIso.app V).symm

/-- Every function-valued irreducible Brauer character is afforded by one
of the chosen simple-module representatives. -/
theorem simpleClassToIBr_surjective
    (iota : PrimeRegularRootEmbedding p k K G) :
    Function.Surjective (simpleClassToIBr iota) := by
  intro phi
  rcases phi.2 with ⟨V, hV, hphi⟩
  refine ⟨simpleClassOfIrreducibleFDRep V hV, ?_⟩
  apply Subtype.ext
  change Representation.brauerCharacterOfRootEmbedding
      (simpleClassFDRep (simpleClassOfIrreducibleFDRep V hV)).ρ iota = phi.1
  rw [hphi]
  exact Representation.brauerCharacterOfRootEmbedding_iso iota
    (simpleClassOfIrreducibleFDRepIso V hV)

/-- The function-valued irreducible Brauer characters of a finite group form
a finite type.  This uses only the surjection from simple-module classes and
does not assert injectivity of Brauer characters. -/
noncomputable instance finiteIBr
    (iota : PrimeRegularRootEmbedding p k K G) : Finite (IBr iota) :=
  Finite.of_surjective (simpleClassToIBr iota)
    (simpleClassToIBr_surjective iota)

/-- Every predicate-defined subset of `IBr` is finite.  This supplies the
set-theoretic finiteness needed by later block-fibre constructions once their
membership predicates have been defined. -/
theorem finiteIBrSubtype
    (iota : PrimeRegularRootEmbedding p k K G)
    (P : IBr iota → Prop) : Finite {phi : IBr iota // P phi} :=
  Finite.of_injective Subtype.val Subtype.val_injective

end ModularRep.FDRepSimpleClassKZero


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
