import ModularRep.PaperProofs.TypeBLeviReturnPowerSelection
import ModularRep.PaperProofs.TypeBGreenPrincipalConstituentSource
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Type A constituents from the literal FLZ theorem

Feng--Conghui Li--Zhang, *Equivariant correspondences and the inductive
Alperin weight condition for type A*, arXiv:2008.05645, Section 2.C and
Theorem 8.1(1), concerns SL/SU inside GL/GU, in every degree at least two
and nondefining characteristic. It chooses a constituent below a specified
upper irreducible. Existence above and modular Clifford conjugacy turn that
statement into a selector in the prescribed orbit. No simplicity or
prime-power quotient assumption occurs here.

The matrix coordinates and prime-field/transpose-inverse value squares are
explicit E1/U data. In degree two, the published actor is field-only. The
explicit finite innerness of transpose-inverse is used to enlarge it to the
field-plus-graph actor before restricting to the original return group.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCurrentTypeASelection

open Formalisation ModularRep
open NavarroCoveringBrauerExtension TypeBGreenPrincipalConstituentSource
open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBRegularLeviCharacterActionAdapter
open TypeBLeviReturnPowerSelection EvenFieldAssumption53Relative
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {Q : Type} [Group Q] (N : Subgroup Q) [N.Normal]

/-- The actual matrix pair, including the determinant-one subgroup. -/
inductive MatrixPresentation (n p f : ℕ) (F : Type) [Field F] [Fintype F]
    (matrix : Q → Matrix (Fin n) (Fin n) F) : Type 1 where
  | linear
      (upper : Q ≃* Matrix.GeneralLinearGroup (Fin n) F)
      (value : ∀ x, matrix x = (upper x).val)
      (cardinality : Fintype.card F = p ^ f)
      (lower : ∀ x, x ∈ N ↔ (matrix x).det = 1)
  | unitary [starF : StarRing F]
      (upper : Q ≃* Matrix.unitaryGroup (Fin n) F)
      (value : ∀ x, matrix x = (upper x).val)
      (cardinality : Fintype.card F = p ^ (2 * f))
      (involution : ∀ x : F, star x = x ^ (p ^ f))
      (lower : ∀ x, x ∈ N ↔ (matrix x).det = 1)

/-- Group and field data only; the lower carrier is the literal normal
determinant-one subgroup under the displayed GL/GU coordinates. -/
structure MatrixModel where
  n : ℕ
  p : ℕ
  f : ℕ
  F : Type
  [fieldF : Field F]
  [fintypeF : Fintype F]
  [charF : CharP F p]
  degree : 2 ≤ n
  prime : p.Prime
  nondefining : p ≠ 2
  exponent : 0 < f
  matrix : Q → Matrix (Fin n) (Fin n) F
  presentation : MatrixPresentation N n p f F matrix

attribute [instance] MatrixModel.fieldF MatrixModel.fintypeF MatrixModel.charF

/-- Standard automorphisms are bound on every matrix entry. The degree-two
inner witness lies in SL/SU itself, including for SL2(3). -/
structure FieldGraphData (model : MatrixModel N) where
  field : MulAut N
  graph : MulAut N
  field_value : ∀ (x : N) i j,
    model.matrix (field x).val i j = model.matrix x.val i j ^ model.p
  graph_value : ∀ (x : N) i j,
    model.matrix (graph x).val i j = model.matrix (x⁻¹).val j i
  graph_inner : model.n = 2 → ∃ x : N, graph = MulAut.conj x

namespace FieldGraphData

variable {N} {model : MatrixModel N} (actors : FieldGraphData N model)

abbrev full : Subgroup (MulAut N) := Subgroup.closure {actors.field, actors.graph}

def published : Subgroup (MulAut N) :=
  if model.n = 2 then Subgroup.zpowers actors.field else actors.full

/-- Inner automorphisms may be moved past any automorphism. This yields a
subgroup of inner multiples of the specified published actor. -/
private def innerMultiples (P : Subgroup (MulAut N)) : Subgroup (MulAut N) where
  carrier := {a | ∃ d : P, ∃ x : N, a = MulAut.conj x * (d : MulAut N)}
  one_mem' := by
    refine ⟨1, 1, ?_⟩
    simp
  mul_mem' := by
    rintro a b ⟨d, x, rfl⟩ ⟨e, y, rfl⟩
    refine ⟨d * e, x * (d : MulAut N) y, ?_⟩
    ext z
    simp
  inv_mem' := by
    rintro a ⟨d, x, rfl⟩
    refine ⟨d⁻¹, (d : MulAut N)⁻¹ x⁻¹, ?_⟩
    ext z
    simp

/-- Every field-plus-graph element differs from a published actor by an
actual inner automorphism; no homomorphism to a field-only quotient is used. -/
theorem full_inner_published (a : actors.full) :
    ∃ d : actors.published, ∃ x : N,
      (a : MulAut N) = MulAut.conj x * (d : MulAut N) := by
  by_cases h : model.n = 2
  · have field_mem : actors.field ∈ actors.published := by
      simp only [published, if_pos h]
      exact Subgroup.mem_zpowers _
    have graph_inner := actors.graph_inner h
    have le : actors.full ≤ innerMultiples actors.published := by
      apply (Subgroup.closure_le _).mpr
      intro g hg
      rcases Set.mem_insert_iff.mp hg with rfl | hg
      · exact ⟨⟨actors.field, field_mem⟩, 1, by simp⟩
      · have eq : g = actors.graph := Set.mem_singleton_iff.mp hg
        obtain ⟨x, hx⟩ := graph_inner
        exact ⟨1, x, by simpa only [eq, Subgroup.coe_one, mul_one] using hx⟩
    exact le a.property
  · have mem : (a : MulAut N) ∈ actors.published := by
      simpa only [published, if_neg h] using a.property
    exact ⟨⟨a, mem⟩, 1, by simp⟩

end FieldGraphData

variable [Finite Q]
variable {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (rootQ : PrimeRegularRootEmbedding 2 k K Q)
variable (rootN : PrimeRegularRootEmbedding 2 k K N)

/-- Literal Theorem 8.1(1), in its constituent quantifier. The pointwise
formula is exactly its semidirect stabilizer equality. Extension clause (2)
is not assumed or used. -/
structure FLZ2021Theorem81 (model : MatrixModel N)
    (actors : FieldGraphData N model)
    (roots : RootAgreement N rootQ rootN)
    (coefficient : SpathCoefficientField 2 k rootQ.prime) : Prop where
  constituent : ∀ upper : IBr rootQ, ∃ psi : IBr rootN,
    BrauerOccursInRestriction N rootQ rootN upper psi ∧
    letI := rightAutomorphismAction rootN (originalAction N)
    letI := rightAutomorphismAction rootN actors.published.subtype
    ProductStabilizerFactorization (D := Q) (E := actors.published) psi

/-- A fixed standard pair's lower inputs. The existence-above premise is
ordinary modular restriction theory, with no uniqueness or p-group quotient. -/
structure Sources (model : MatrixModel N) (actors : FieldGraphData N model) : Prop where
  roots : RootAgreement N rootQ rootN
  coefficient : SpathCoefficientField 2 k rootQ.prime
  above : ∀ psi : IBr rootN, ∃ upper : IBr rootQ,
    BrauerOccursInRestriction N rootQ rootN upper psi
  clifford : Clifford85_87Source N rootQ rootN roots coefficient
  published : FLZ2021Theorem81 N rootQ rootN model actors roots coefficient

/-- Apply FLZ to an irreducible lying over the prescribed base, identify the
chosen constituent by Clifford conjugacy, and enlarge degree-two actors
using the supplied matrix-innerness witness. -/
theorem standard_selector_at (model : MatrixModel N) (actors : FieldGraphData N model)
    (sources : Sources N rootQ rootN model actors) (base : IBr rootN) :
    StandardSelectorAt rootN (originalAction N) actors.full base := by
  letI := rightAutomorphismAction rootN (originalAction N)
  letI := rightAutomorphismAction rootN actors.full.subtype
  letI := rightAutomorphismAction rootN actors.published.subtype
  obtain ⟨upper, hbase⟩ := sources.above base
  obtain ⟨psi, hpsi, hfactor⟩ := sources.published.constituent upper
  obtain ⟨g, hg⟩ := sources.clifford.constituents_conjugate upper base psi hbase hpsi
  refine ⟨psi, ⟨g, hg⟩, ?_⟩
  intro q a
  obtain ⟨d, x, hx⟩ := actors.full_inner_published a⁻¹
  have action : a • psi = d⁻¹ • psi := by
    change IrreducibleBrauerCharacter.twist rootN psi (a⁻¹ : MulAut N) =
      IrreducibleBrauerCharacter.twist rootN psi ((d⁻¹)⁻¹ : MulAut N)
    rw [inv_inv]
    exact brauerTwist_eq_of_eq_inner_mul rootN psi _ _ x hx
  simpa only [action] using hfactor q d⁻¹

end ModularRep.PaperProofs.TypeBCurrentTypeASelection


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
