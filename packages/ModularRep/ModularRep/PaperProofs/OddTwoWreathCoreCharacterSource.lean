import ModularRep.PaperProofs.OddTwoWreathReflection
import ModularRep.PaperProofs.CharacterInductionEquivariance
import ModularRep.WeightCharacterBridge
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# The actual local wreath character construction indexed by coloured cores

An (1993), (6D), pp. 200--202, and Feng--Malle (2022), Proposition 5.4,
pp. 12--13, use the standard wreath ordinary-character theorem. A core is
assigned to each ACTUAL local defect-zero character. Its size contributes
to the multiplicity of that basic subgroup. A three-colour total need not
be triangular. No principal membership or selected-character match occurs
in this module.

The groups are the existing permutation wreath products with their actual
right-action convention `(f,a)(g,b)=(f^b*g,a*b)`. The Young inertia subgroup
is the stabilizer of an explicitly constructed slot colouring. The tensor
extension character is the trace of an explicit finite tensor-permutation
matrix built from representations affording the supplied basic characters.
The final character uses the existing finite-sum `inducedCharacter` API.
Thus no free predicate called a character formula is used.

Standard source data supply the restrictions of those actual permutations
to their colour blocks, with a pointwise commuting square, and the unique
defect-zero symmetric-group character at each triangular size. Their
existence is ordinary finite-permutation/core character theory. The E2
wreath source asserts irreducibility, defect zero, injectivity and
exhaustiveness for THIS displayed induced function. K constructs its
equivalence to the actual local DZ carrier.

This is a local ordinary-character source join, not a global weight map.
Its substantial source fields are not proved or instantiated here. The
actual Sp product normalizer-quotient identification and named actions
remain separate. No general character-theory foundations are reconstructed.
-/

noncomputable section

open scoped BigOperators

namespace ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource

open ModularRep
open ModularRep.PaperProofs.OddTwoWreathReflection
open ModularRep.PaperProofs.CharacterInductionEquivariance

universe u

/-- The size of the staircase partition of height h. -/
def triangular (h : ℕ) : ℕ := h * (h + 1) / 2

theorem height_le_triangular (h : ℕ) : h ≤ triangular h := by
  have hm : 2 * h ≤ h * (h + 1) := by
    by_cases h0 : h = 0
    · simp [h0]
    · have hp : 1 ≤ h := Nat.one_le_iff_ne_zero.mpr h0
      nlinarith
  unfold triangular
  omega

/-- The exceptional three-colour index admits two distinct one-box cores. -/
def twoColouredHeights : Fin 3 → ℕ := ![1, 1, 0]

theorem twoColouredHeights_size :
    ∑ j : Fin 3, triangular (twoColouredHeights j) = 2 := by
  decide

/-- Their total is not itself the size of one staircase. This is only the
arithmetic distinction, not a classification of a symplectic subgroup. -/
theorem triangular_ne_two (h : ℕ) : triangular h ≠ 2 := by
  intro heq
  have hle : h ≤ 2 := by
    have := height_le_triangular h
    omega
  interval_cases h <;> norm_num [triangular] at heq

/-- Multiplicity is the sum of staircase sizes, separately by actual
local-character colour. It need not itself be triangular. -/
def CoreAssignments {m : ℕ} (b multiplicity : Fin m → ℕ) :=
  { height : ∀ i : Fin m, Fin (b i) → ℕ //
    ∀ i, ∑ j : Fin (b i), triangular (height i j) = multiplicity i }

namespace CoreAssignments

variable {m : ℕ} {b multiplicity : Fin m → ℕ}

theorem height_le (h : CoreAssignments b multiplicity) (i : Fin m) (j : Fin (b i)) :
    h.1 i j ≤ multiplicity i := by
  apply (height_le_triangular (h.1 i j)).trans
  rw [← h.2 i]
  exact Finset.single_le_sum (f := fun j : Fin (b i) => triangular (h.1 i j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

instance : Finite (CoreAssignments b multiplicity) := by
  let f : CoreAssignments b multiplicity →
      (∀ i : Fin m, Fin (b i) → Fin (multiplicity i + 1)) :=
    fun h i j => ⟨h.1 i j, Nat.lt_succ_of_le (h.height_le i j)⟩
  apply Finite.of_injective f
  intro h k heq
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun heq i) j)

/-- A finite coordinate identification, constructed from the exact colour
size equation, rather than an additional classification assumption. -/
def slots (h : CoreAssignments b multiplicity) (i : Fin m) :
    (Σ j : Fin (b i), Fin (triangular (h.1 i j))) ≃ Fin (multiplicity i) :=
  Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using h.2 i)

def colour (h : CoreAssignments b multiplicity) (i : Fin m)
    (s : Fin (multiplicity i)) : Fin (b i) :=
  ((h.slots i).symm s).1

@[simp] theorem colour_slots (h : CoreAssignments b multiplicity)
    (i : Fin m) (j : Fin (b i)) (s : Fin (triangular (h.1 i j))) :
    h.colour i (h.slots i ⟨j, s⟩) = j := by
  simp [colour]

end CoreAssignments

section ActualGroups

variable {m : ℕ} (L : Fin m → Type u) [∀ i, Group (L i)]
variable (multiplicity : Fin m → ℕ)

abbrev BasicWreath (i : Fin m) :=
  PermutationWreathProduct (L i) (MonoidHom.id (Equiv.Perm (Fin (multiplicity i))))

abbrev ProductWreath := ∀ i : Fin m, BasicWreath L multiplicity i

def basicWreathCoordinates (i : Fin m) : BasicWreath L multiplicity i ≃
    ((Fin (multiplicity i) → L i) × Equiv.Perm (Fin (multiplicity i))) where
  toFun z := (z.left, z.right)
  invFun z := ⟨z.1, z.2⟩
  left_inv z := by cases z; rfl
  right_inv z := by cases z; rfl

instance [∀ i, Fintype (L i)] (i : Fin m) : Fintype (BasicWreath L multiplicity i) :=
  Fintype.ofEquiv _ (basicWreathCoordinates L multiplicity i).symm

variable {multiplicity} {b : Fin m → ℕ}

/-- The ACTUAL subgroup preserving every colour block of the slot layout. -/
def youngInertia (h : CoreAssignments b multiplicity) :
    Subgroup (ProductWreath L multiplicity) where
  carrier := {z | ∀ i s, h.colour i ((z i).right s) = h.colour i s}
  one_mem' := by intro i s; rfl
  mul_mem' := by
    intro x y hx hy i s
    change h.colour i ((x i).right ((y i).right s)) = h.colour i s
    rw [hx, hy]
  inv_mem' := by
    intro x hx i s
    change h.colour i ((x i).right.symm s) = h.colour i s
    have hi := hx i ((x i).right.symm s)
    simpa only [Equiv.apply_symm_apply] using hi.symm

/-- Elementary permutation restriction data with its exact coordinate
square. The map is determined on every point by this equation. Its type
cannot substitute an unrelated Young subgroup or a free permutation. -/
structure YoungBlockPermutations (h : CoreAssignments b multiplicity) where
  permutation : ∀ (i : Fin m) (j : Fin (b i)),
    youngInertia L h →* Equiv.Perm (Fin (triangular (h.1 i j)))
  slots_commute : ∀ (z : youngInertia L h) (i : Fin m) (j : Fin (b i))
      (s : Fin (triangular (h.1 i j))),
    h.slots i ⟨j, permutation i j z s⟩ = (z.1 i).right (h.slots i ⟨j, s⟩)

end ActualGroups

section CharacterFormula

variable (K : Type u) [Field K] [CharZero K]

/-- Actual function-valued ordinary defect-zero characters. -/
abbrev DZ (G : Type u) [Group G] [Finite G] :=
  {chi : OrdinaryIrreducibleCharacter.Irr K G //
    IsDefectZeroOrdinaryCharacter 2 chi}

/-- A universe lift of the literal symmetric group at a triangular size. -/
abbrev StaircaseGroup (h : ℕ) := ULift.{u} (Equiv.Perm (Fin (triangular h)))

/-- Standard symmetric-group 2-core theory: there is exactly one
defect-zero character at this triangular size, namely the staircase one.
This is an actual character and uniqueness on its actual group, not a
freely interpreted predicate saying that a label is a staircase. -/
structure StaircaseCharacterSource where
  character : ∀ h : ℕ, DZ K (StaircaseGroup.{u} h)
  unique : ∀ h : ℕ, Subsingleton (DZ K (StaircaseGroup.{u} h))

variable {K} {m : ℕ} (L : Fin m → Type u)
variable [∀ i, Group (L i)] [∀ i, Fintype (L i)]
variable {b multiplicity : Fin m → ℕ}
variable (e : ∀ i : Fin m, Fin (b i) ≃ DZ K (L i))

/-- Choose a representation already witnessing the actual basic character.
Its character equality is a field of the existing Realisation carrier. -/
def baseRealisation (i : Fin m) (j : Fin (b i)) :
    OrdinaryIrreducibleCharacter.Realisation K (L i) (e i j).1 :=
  Classical.choice (e i j).1.2

/-- The literal elementary-tensor basis for all coloured slots. -/
abbrev TensorBasis (h : CoreAssignments b multiplicity) :=
  ∀ (i : Fin m) (s : Fin (multiplicity i)),
    Fin ((baseRealisation L e i (h.colour i s)).dimension)

/-- Cast along the proved colour preservation, so the tensor entry uses
the SAME chosen basic representation before and after the permutation. -/
def permutedBasisEntry (h : CoreAssignments b multiplicity)
    (z : youngInertia L h) (v : TensorBasis L e h)
    (i : Fin m) (s : Fin (multiplicity i)) :
    Fin ((baseRealisation L e i (h.colour i s)).dimension) :=
  Fin.cast (congrArg (fun j => (baseRealisation L e i j).dimension) (z.2 i s))
    (v i ((z.1 i).right s))

/-- Trace of the actual tensor-permutation matrix P_pi D_f. The existing
wreath convention places f_s before moving slot s to pi(s), so its matrix
entry is rho(f_s)[v_(pi(s)),w_s]. No arbitrary extension character is stored.
The standard theorem that this is the tensor-extension character is part
of the precisely scoped local source, not a reconstructed foundation. -/
def tensorPermutationCharacter (h : CoreAssignments b multiplicity)
    (z : youngInertia L h) : K := by
  classical
  exact ∑ v : TensorBasis L e h, ∏ i : Fin m, ∏ s : Fin (multiplicity i),
    (baseRealisation L e i (h.colour i s)).representation ((z.1 i).left s)
      (Pi.single (v i s) 1) (permutedBasisEntry L e h z v i s)

/-- Only standard constituent data are supplied. Both the subgroup and
tensor-extension trace are already fixed by the explicit definitions. -/
structure CoreFormulaData (e : ∀ i : Fin m, Fin (b i) ≃ DZ K (L i)) where
  staircase : StaircaseCharacterSource K
  youngPermutations : ∀ h : CoreAssignments b multiplicity, YoungBlockPermutations L h

namespace CoreFormulaData

variable {L e} (D : CoreFormulaData L e)

/-- Tensor extension times the actual staircase characters inflated through
the colour-block permutation maps. -/
def inducingCharacter (h : CoreAssignments b multiplicity)
    (z : youngInertia L h) : K :=
  tensorPermutationCharacter L e h z *
    ∏ i : Fin m, ∏ j : Fin (b i),
      (D.staircase.character (h.1 i j)).1
        (ULift.up ((D.youngPermutations h).permutation i j z))

/-- The actual finite-sum induced character of the full product wreath.
Induction from the product Young subgroup is the product of the usual
single-wreath constructions, with the same underlying groups. -/
def characterFunction (h : CoreAssignments b multiplicity) :
    ProductWreath L multiplicity → K :=
  inducedCharacter (youngInertia L h) (D.inducingCharacter h)

end CoreFormulaData

/-- Exact substantial E2 local wreath theorem from An (6D)/FM 5.4.
It concerns THIS induced function on THIS actual product group. No chosen
weight, character match, principal premise or global bijection is a field.
Splitting over the same characteristic-zero coefficient field is explicit.
-/
structure AnFMCoreCharacterSource (D : CoreFormulaData L e) where
  ordinarySplitting : IsAlgClosed K
  irreducible : ∀ h : CoreAssignments b multiplicity,
    Nonempty (OrdinaryIrreducibleCharacter.Realisation K
      (ProductWreath L multiplicity) (D.characterFunction h))
  defectZero : ∀ h : CoreAssignments b multiplicity,
    IsDefectZeroOrdinaryCharacter 2 ⟨D.characterFunction h, irreducible h⟩
  injective : Function.Injective D.characterFunction
  exhaustive : ∀ chi : DZ K (ProductWreath L multiplicity),
    ∃ h : CoreAssignments b multiplicity, D.characterFunction h = chi.1.1

namespace AnFMCoreCharacterSource

variable {L e} {D : CoreFormulaData L e} (S : AnFMCoreCharacterSource L e D)

/-- The character is constructed from the finite-sum formula and the
source's irreducibility witness; it is not an independently chosen output. -/
def character (h : CoreAssignments b multiplicity) :
    DZ K (ProductWreath L multiplicity) :=
  ⟨⟨D.characterFunction h, S.irreducible h⟩, S.defectZero h⟩

@[simp] theorem character_value (h : CoreAssignments b multiplicity)
    (z : ProductWreath L multiplicity) :
    (S.character h).1 z = inducedCharacter (youngInertia L h) (D.inducingCharacter h) z :=
  rfl

/-- K packages the proven/source-classified actual character functions as
the exhaustive local enumeration consumed by the principal product atlas. -/
def enumeration : CoreAssignments b multiplicity ≃ DZ K (ProductWreath L multiplicity) :=
  Equiv.ofBijective S.character (by
    constructor
    · intro h k heq
      apply S.injective
      exact congrArg (fun chi : DZ K (ProductWreath L multiplicity) => chi.1.1) heq
    · intro chi
      obtain ⟨h, hh⟩ := S.exhaustive chi
      refine ⟨h, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hh)

@[simp] theorem enumeration_value (h : CoreAssignments b multiplicity)
    (z : ProductWreath L multiplicity) :
    (S.enumeration h).1 z = D.characterFunction h z := rfl

end AnFMCoreCharacterSource

end CharacterFormula

end ModularRep.PaperProofs.OddTwoWreathCoreCharacterSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
