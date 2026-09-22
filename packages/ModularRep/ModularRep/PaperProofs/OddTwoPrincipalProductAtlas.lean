import ModularRep.PaperProofs.OddTwoQuaternionClassPair
import ModularRep.PaperProofs.OddTwoQuaternionExceptionalSourceJoin
import ModularRep.PaperProofs.OddTwoGeneralizedQuaternionPlaneSourceJoin
import ModularRep.PaperProofs.OddTwoQuaternionTensorSourceJoin
import Mathlib.Data.Matrix.Block

/-!
# Actual independent products of the surviving odd-two basic models

The four existing matrix models form one finite-family interface. The
product is the image of independently chosen blocks, with a literal
block-diagonal matrix equation. It is not the repeated diagonal action
inside one FYZ basic factor. Source multiplicities are not constrained to
be triangular: the local-character construction assigns a core to each
local colour, and sums their sizes for a repeated subgroup.

The matrix coordinates and the exhaustive group classification remain
precise E1/E2 inputs. This module does not assert that arbitrary products
are radical. Radicality and principal membership of the selected enumerated
pair are inherited from its genuine match with the same original weight.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalProductAtlas

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalSelectedCharacterUniqueness
open ModularRep.PaperProofs.OddTwoQuaternionBasicSourceJoin
open ModularRep.PaperProofs.OddTwoQuaternionClassPair
open ModularRep.PaperProofs.OddTwoQuaternionExceptionalSourceJoin
open ModularRep.PaperProofs.OddTwoGeneralizedQuaternionPlaneSourceJoin
open ModularRep.PaperProofs.OddTwoQuaternionTensorSourceJoin
open ModularRep.PaperProofs.OddTwoFinalBlockOrbitCentralCoverDescentWindow
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F K : Type u} [Field F] [Fintype F] [Field K] [CharZero K]

local instance spFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

/-- Every constructor contains an existing literal source model, including
the two actual diagonal-related quaternion classes. No arbitrary basic
subgroup or positive-gamma case-(3) constructor is present. -/
inductive BasicModel (r : ℕ) (F : Type u) [Field F] [Fintype F] where
  | quaternion (C : QuaternionBasicModel r F)
      (O : LiteralDiagonalFieldRealisation r F) (i : Fin 2)
  | exceptional (C : QuaternionExceptionalModel r F)
  | generalized (C : GeneralizedQuaternionPlaneModel r F)
  | tensor (C : TensorWreathModel r F)

namespace BasicModel

def subgroup : BasicModel n F → Subgroup (Sp n F)
  | .quaternion C O i => classSubgroup C O i
  | .exceptional C => C.subgroup
  | .generalized C => C.subgroup
  | .tensor C => C.subgroup

def colours : BasicModel n F → ℕ
  | .exceptional _ => 3
  | _ => 1

def sourceFamily : BasicModel n F → PrincipalFamily
  | .quaternion .. => .quaternion
  | _ => .typeFour

def fyzList : BasicModel n F → List ℕ
  | .quaternion C _ _ => C.wreathList
  | .exceptional C => C.wreathList
  | .generalized C => C.wreathList
  | .tensor C => C.wreathList

def fengMalleList (B : BasicModel n F) : List ℕ := B.fyzList.reverse

theorem fengMalleList_eq (B : BasicModel n F) :
    B.fengMalleList = fyzToFengMalleWreathList B.fyzList := rfl

/-- The own local characters of an actual basic subgroup, with its exact
one- or three-colour domain. Constructors below consume the existing An
source packets, so an unrelated numerical character count is insufficient.
-/
structure LocalEnumeration (B : BasicModel n F) where
  ordinarySplitting : IsAlgClosed K
  enumeration : Fin B.colours ≃ LocalDefectZeroCharacters (K := K) B.subgroup

private def singletonEnumeration {X : Type u} (x : X) (unique : Subsingleton X) :
    Fin 1 ≃ X where
  toFun _ := x
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := unique.elim _ _

def quaternionLocal (C : QuaternionBasicModel n F)
    (O : LiteralDiagonalFieldRealisation n F) (i : Fin 2)
    (S : AnQuaternionBasicLocalSource (K := K) C) :
    LocalEnumeration (K := K) (.quaternion C O i) where
  ordinarySplitting := S.ordinarySplitting
  enumeration := by
    change Fin 1 ≃ LocalDefectZeroCharacters (K := K) (classSubgroup C O i)
    rw [← candidate_subgroup C S O i]
    exact singletonEnumeration
      ⟨(candidate C S O i).localCharacter, (candidate C S O i).defectZero⟩
      (candidate_unique C S O i)

def exceptionalLocal (C : QuaternionExceptionalModel n F)
    (S : AnExceptionalLocalCharacters (K := K) C) :
    LocalEnumeration (K := K) (.exceptional C) :=
  ⟨S.ordinarySplitting, S.enumeration⟩

def generalizedLocal (C : GeneralizedQuaternionPlaneModel n F)
    (S : AnGeneralizedQuaternionLocalSource (K := K) C) :
    LocalEnumeration (K := K) (.generalized C) :=
  ⟨S.ordinarySplitting, singletonEnumeration (S.selectedLocal C) S.local_unique⟩

def tensorLocal (C : TensorWreathModel n F)
    (S : AnPositiveGammaLocalCharacters (K := K) C) :
    LocalEnumeration (K := K) (.tensor C) :=
  ⟨S.ordinarySplitting, S.enumeration⟩

end BasicModel

/-- A grouped list of present basic subgroup types. The normalizer source
must use distinct actual conjugacy types; this is stronger than distinct
abstract group isomorphism types. Only positive group multiplicities occur.
-/
structure ProductShape (n : ℕ) (F : Type u) [Field F] [Fintype F] where
  count : ℕ
  rank : Fin count → ℕ
  rank_positive : ∀ i, 0 < rank i
  basic : ∀ i, BasicModel (rank i) F
  copies : Fin count → ℕ
  copies_positive : ∀ i, 0 < copies i
  rank_sum : ∑ i, copies i * rank i = n

namespace ProductShape

variable (P : ProductShape n F)

abbrev Copy := Σ i : Fin P.count, Fin (P.copies i)
abbrev Coordinates := Σ c : P.Copy, (Fin (P.rank c.1) ⊕ Fin (P.rank c.1))

local instance coordinatesDecidableEq : DecidableEq P.Coordinates := Classical.decEq _
local instance copyDecidableEq : DecidableEq P.Copy := Classical.decEq _

abbrev BlockGroups := (c : P.Copy) → Sp (P.rank c.1) F

/-- The completely independent product of the displayed source subgroups. -/
def independentBlocks : Subgroup P.BlockGroups :=
  Subgroup.pi Set.univ (fun c => (P.basic c.1).subgroup)

/-- Standard symplectic direct-sum coordinates, fixed by their matrix
formula on every independently chosen block. This does not identify two
different representations merely by an abstract group isomorphism. -/
structure Geometry where
  basisIndex : P.Coordinates ≃ (Fin n ⊕ Fin n)
  gram_equation : Matrix.reindex basisIndex basisIndex
      (Matrix.blockDiagonal' (fun c : P.Copy => Matrix.J (Fin (P.rank c.1)) F)) =
    Matrix.J (Fin n) F
  embedding : P.BlockGroups →* Sp n F
  embedding_injective : Function.Injective embedding
  embedding_matrix : ∀ g,
    (embedding g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.reindex basisIndex basisIndex
        (Matrix.blockDiagonal' (fun c : P.Copy =>
          (g c : Matrix (Fin (P.rank c.1) ⊕ Fin (P.rank c.1))
            (Fin (P.rank c.1) ⊕ Fin (P.rank c.1)) F)))

namespace Geometry

variable {P} (A : P.Geometry)

def subgroup : Subgroup (Sp n F) := P.independentBlocks.map A.embedding

theorem mem_subgroup (x : Sp n F) :
    x ∈ A.subgroup ↔ ∃ g : P.BlockGroups,
      (∀ c, g c ∈ (P.basic c.1).subgroup) ∧ A.embedding g = x := by
  simp [subgroup, independentBlocks, Subgroup.mem_map, Subgroup.mem_pi]

/-- The same actual product matrices, with each block chosen independently.
No radicality or character assertion is used in this calculation. -/
theorem independent_element_matrix (g : P.BlockGroups)
    (hg : ∀ c, g c ∈ (P.basic c.1).subgroup) :
    A.embedding g ∈ A.subgroup ∧
      (A.embedding g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
        Matrix.reindex A.basisIndex A.basisIndex
          (Matrix.blockDiagonal' (fun c : P.Copy =>
            (g c : Matrix (Fin (P.rank c.1) ⊕ Fin (P.rank c.1))
              (Fin (P.rank c.1) ⊕ Fin (P.rank c.1)) F))) :=
  ⟨(A.mem_subgroup _).mpr ⟨g, hg, rfl⟩, A.embedding_matrix g⟩

end Geometry

end ProductShape

end ModularRep.PaperProofs.OddTwoPrincipalProductAtlas


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
