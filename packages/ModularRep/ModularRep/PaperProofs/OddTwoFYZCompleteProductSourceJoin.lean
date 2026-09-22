import ModularRep.PaperProofs.OddTwoPrincipalProductAtlas

/-!
# Complete FYZ factor passage to actual surviving product models

The substantial FYZ decomposition theorem is an external input, on the
actual subgroup of the selected weight. Its entire independent product
and change of coordinates are explicit. The separate principal-source
packet excludes only cases (1),(2),(5), translates EVERY case-(4)
occurrence into the existing equation-(3.35) realization, and normalizes
each case-(3)/(6) factor using the four already fixed source models.

K applies the reflection/Sylow exclusion to every corrected occurrence,
selects its surviving family, substitutes the normalized basic subgroups
in the SAME product, and derives the full subgroup match. Thus neither a
principal product match nor a local-character comparison is a source field.
No triangular condition on subgroup multiplicities is imposed.

The exact E1/E2 source interpretations are FYZ 3.37,3.48, the restricted
exclusions of 3.50, equation (3.35) and An's basic group classification.
In particular the corrected-occurrence field must be instantiated using
all its actual multiplicities, Gram spaces, wreath lists and complement;
an arbitrary case labelling or incomplete decomposition is not that source.
The normalizer and local induced-character joins follow separately.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoFYZCompleteProductSourceJoin

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
open ModularRep.PaperProofs.OddTwoPrincipalFactorExclusion
open ModularRep.PaperProofs.OddTwoPrincipalProductAtlas
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension

universe u

variable {n : ℕ} {F K : Type u} [Field F] [Fintype F] [Field K] [CharZero K]

local instance spFintype (r : ℕ) : Fintype (Sp r F) := Fintype.ofFinite _

local instance copyDecidableEq (m : ℕ) (copies : Fin m → ℕ) :
    DecidableEq (Σ i : Fin m, Fin (copies i)) := Classical.decEq _

/-- The whole geometric source decomposition, on the actual raw pair.
Equal occurrences can be grouped before this record is supplied. The
normalizer source later checks separation of actual conjugacy types.
The field sourceCase refers to FYZ's six cases for these SAME subgroups.
-/
structure FullFactorData (W : CharacterWeight 2 K (Sp n F)) where
  count : ℕ
  rank : Fin count → ℕ
  rank_positive : ∀ i, 0 < rank i
  factor : ∀ i, Subgroup (Sp (rank i) F)
  sourceCase : Fin count → FYZCase
  copies : Fin count → ℕ
  copies_positive : ∀ i, 0 < copies i
  rank_sum : ∑ i, copies i * rank i = n
  basisIndex : (Σ c : (Σ i : Fin count, Fin (copies i)),
    (Fin (rank c.1) ⊕ Fin (rank c.1))) ≃ (Fin n ⊕ Fin n)
  gram_equation : Matrix.reindex basisIndex basisIndex
      (Matrix.blockDiagonal' (fun c : (Σ i : Fin count, Fin (copies i)) =>
        Matrix.J (Fin (rank c.1)) F)) = Matrix.J (Fin n) F
  embedding : ((c : (Σ i : Fin count, Fin (copies i))) → Sp (rank c.1) F) →* Sp n F
  embedding_injective : Function.Injective embedding
  embedding_matrix : ∀ g,
    (embedding g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.reindex basisIndex basisIndex
        (Matrix.blockDiagonal' (fun c : (Σ i : Fin count, Fin (copies i)) =>
          (g c : Matrix (Fin (rank c.1) ⊕ Fin (rank c.1))
            (Fin (rank c.1) ⊕ Fin (rank c.1)) F)))
  conjugator : Sp n F
  subgroup_formula : W.subgroup.comap (MulAut.conj conjugator⁻¹).toMonoidHom =
    (Subgroup.pi Set.univ (fun c : (Σ i : Fin count, Fin (copies i)) =>
      factor c.1)).map embedding

variable {k Block : Type u} [Field k] [CharP k 2] [IsAlgClosed k]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]
variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))
variable (w : D.PrincipalWeight)
variable (T : FullFactorData (selectedCharacterWeight D.blockSource D.principalBlock w))

/-- Source clauses on this complete actual decomposition. Cases (1),(2),
(5) use only the restricted valid principal exclusion. Case (4) is NOT
excluded by an input: its actual realization feeds the existing K proof.

The last field is individual BASIC subgroup normalization, including actual
matrix coordinates. It supplies no full product or selected-character
comparison. One uses a conjugated basic basis in the full decomposition;
the existing basic coverage lemmas justify that choice of coordinates.
These substantial literature/group source facts remain explicit premises.
-/
structure PrincipalFactorSources where
  not_signs : ∀ i, T.sourceCase i ≠ .signs
  not_regular : ∀ i, T.sourceCase i ≠ .regular
  not_generalLinear : ∀ i, T.sourceCase i ≠ .generalLinear
  corrected_realisation : ∀ i, T.sourceCase i = .correctedEven →
    CorrectedFactorRealisation (selectedCharacterWeight D.blockSource D.principalBlock w)
  basic_normalization : ∀ (i : Fin T.count) (family : PrincipalFamily),
    family.sourceCase = T.sourceCase i →
      ∃ B : BasicModel (T.rank i) F,
        B.sourceFamily = family ∧ B.subgroup = T.factor i

namespace PrincipalFactorSources

variable {D w T} (S : PrincipalFactorSources D w T)
variable (fieldOdd : Odd (Nat.card F)) (lemma23 : FYZLemma23IntrinsicCertificate D)

include S fieldOdd lemma23 in
/-- The same reflection argument excludes EVERY occurrence in the supplied
full decomposition, without a separate primitive case-(4) exclusion. -/
theorem not_corrected (i : Fin T.count) : T.sourceCase i ≠ .correctedEven := by
  intro hi
  letI := intrinsicPrincipal_correctedFactor_isEmpty D fieldOdd lemma23 w
  exact isEmptyElim (S.corrected_realisation i hi)

include S fieldOdd lemma23 in
theorem survivingFamily_exists (i : Fin T.count) :
    ∃ family : PrincipalFamily, family.sourceCase = T.sourceCase i := by
  letI := intrinsicPrincipal_correctedFactor_isEmpty D fieldOdd lemma23 w
  exact principalFactor_has_survivingFamily
    (Factor := ULift.{u} (Fin T.count)) (fun j => T.sourceCase j.down)
    (fun j => S.not_signs j.down) (fun j => S.not_regular j.down)
    (fun j => S.not_generalLinear j.down) (fun j => S.corrected_realisation j.down)
    (ULift.up i)

def family (i : Fin T.count) : PrincipalFamily :=
  Classical.choose (S.survivingFamily_exists fieldOdd lemma23 i)

theorem family_case (i : Fin T.count) :
    (S.family fieldOdd lemma23 i).sourceCase = T.sourceCase i :=
  Classical.choose_spec (S.survivingFamily_exists fieldOdd lemma23 i)

def normalizedBasic (i : Fin T.count) : BasicModel (T.rank i) F :=
  Classical.choose (S.basic_normalization i (S.family fieldOdd lemma23 i)
    (S.family_case fieldOdd lemma23 i))

theorem normalizedBasic_family (i : Fin T.count) :
    (S.normalizedBasic fieldOdd lemma23 i).sourceFamily = S.family fieldOdd lemma23 i :=
  (Classical.choose_spec (S.basic_normalization i (S.family fieldOdd lemma23 i)
    (S.family_case fieldOdd lemma23 i))).1

theorem normalizedBasic_subgroup (i : Fin T.count) :
    (S.normalizedBasic fieldOdd lemma23 i).subgroup = T.factor i :=
  (Classical.choose_spec (S.basic_normalization i (S.family fieldOdd lemma23 i)
    (S.family_case fieldOdd lemma23 i))).2

/-- The complete surviving product shape is computed, rather than stored
as a desired source-classification conclusion. -/
def productShape : ProductShape n F where
  count := T.count
  rank := T.rank
  rank_positive := T.rank_positive
  basic := S.normalizedBasic fieldOdd lemma23
  copies := T.copies
  copies_positive := T.copies_positive
  rank_sum := T.rank_sum

/-- The original coordinates and actual independent-block homomorphism
are retained verbatim after the individual subgroup substitutions. -/
def productGeometry : (S.productShape fieldOdd lemma23).Geometry where
  basisIndex := T.basisIndex
  gram_equation := T.gram_equation
  embedding := T.embedding
  embedding_injective := T.embedding_injective
  embedding_matrix := T.embedding_matrix

theorem product_subgroup_eq :
    (S.productGeometry fieldOdd lemma23).subgroup =
      (Subgroup.pi Set.univ (fun c : (Σ i : Fin T.count, Fin (T.copies i)) =>
        T.factor c.1)).map T.embedding := by
  have hfun : (fun c : (Σ i : Fin T.count, Fin (T.copies i)) =>
      (S.normalizedBasic fieldOdd lemma23 c.1).subgroup) =
    (fun c : (Σ i : Fin T.count, Fin (T.copies i)) => T.factor c.1) :=
    funext (fun c => S.normalizedBasic_subgroup fieldOdd lemma23 c.1)
  change (Subgroup.pi Set.univ (fun c : (Σ i : Fin T.count, Fin (T.copies i)) =>
    (S.normalizedBasic fieldOdd lemma23 c.1).subgroup)).map T.embedding = _
  exact congrArg (fun f => (Subgroup.pi Set.univ f).map T.embedding) hfun

/-- The genuine match of the original selected subgroup with the FULL
surviving product follows from the source decomposition and K exclusion.
No local character or candidate principal membership enters this proof. -/
theorem subgroup_match :
    ((selectedCharacterWeight D.blockSource D.principalBlock w).rightTwist
      (MulAut.conj T.conjugator⁻¹)).subgroup =
        (S.productGeometry fieldOdd lemma23).subgroup :=
  T.subgroup_formula.trans (S.product_subgroup_eq fieldOdd lemma23).symm

end PrincipalFactorSources

end ModularRep.PaperProofs.OddTwoFYZCompleteProductSourceJoin


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
