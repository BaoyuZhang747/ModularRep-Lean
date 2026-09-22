import ModularRep.PaperProofs.EvenFieldFLZSourceConditions

/-!
# Intrinsic principal weights in the odd symplectic window

Feng--Malle, p. 1 and Theorem 6.2, use conjugacy classes of actual weight
pairs.  They do not define a second, obsolete universe of weights.  This
module fixes the matrix group and the prime, defines the principal block as
the block of a character with constant value one, and uses the existing
literal local-block-induction fibre for both source descriptions.

K: principal-block invariance, the identical-carrier bridge, selected-pair
transport, and the exhaustive routing of the six FYZ cases.  E1/U: the
coefficient system and the interpretation of the supplied local block
operations.  E2: the published principal correspondence on these fixed
carriers.  U: the exhaustive realization of FYZ factors, the two quaternion
class names, the Q-family local characters, and source field/diagonal labels.
No correspondence below supplies FLZ Definition 3.5(ii).
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

abbrev Sp (n : ℕ) (F : Type u) [Field F] :=
  Matrix.symplecticGroup (Fin n) F

section LiteralPrincipal

variable {n : ℕ} {F k K Block : Type u}
variable [Field F] [Fintype F] [Field k] [Field K]
variable [CharP k 2] [IsAlgClosed k] [CharZero K]

local instance spFintype : Fintype (Sp n F) := Fintype.ofFinite _

variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block]

/-- The background data on literal `Sp_(2n)(F)`.  The principal block is
computed below; it is not a freely selected block with a principal tag.
The value equation identifies the trivial Brauer character at the source
boundary without importing a sporadic implementation of that character. -/
structure PrincipalCharacterData where
  ordinarySplitting : IsAlgClosed K
  iota : PrimeRegularRootEmbedding 2 k K (Sp n F)
  injective : IrreducibleBrauerCharacterInjectivity iota
  blockSource : LocalBlockInductionSource
    (p := 2) (k := k) (K := K) (G := Sp n F) (Block := Block)
  trivialCharacter : IBr iota
  trivial_value : ∀ g, trivialCharacter.1 g = 1
  support_transport : OperationsBrauerSupport iota injective
    blockSource.operations

namespace PrincipalCharacterData

variable (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K)
  (Block := Block))

def principalBlock : Block :=
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  irreducibleBrauerCharacterBlock D.iota D.injective
    D.blockSource.operations.ambientBlockData.blocks D.trivialCharacter

theorem trivialCharacter_fixed (a : (MulAut (Sp n F))ᵐᵒᵖ) :
    a • D.trivialCharacter = D.trivialCharacter := by
  apply Subtype.ext
  ext g
  change D.trivialCharacter.1 _ = D.trivialCharacter.1 g
  rw [D.trivial_value, D.trivial_value]

theorem principalBlock_fixed (a : (MulAut (Sp n F))ᵐᵒᵖ) :
    a • D.principalBlock = D.principalBlock := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  change a • irreducibleBrauerCharacterBlock D.iota D.injective
      D.blockSource.operations.ambientBlockData.blocks D.trivialCharacter = _
  rw [← D.support_transport a D.trivialCharacter, D.trivialCharacter_fixed]
  rfl

/-- Both FYZ and FM weights are this one intrinsic principal fibre.  Its
elements are conjugacy classes, not selected representatives or labels. -/
abbrev PrincipalWeight := D.blockSource.Fibre D.principalBlock

abbrev FYZPrincipalWeight := D.PrincipalWeight
abbrev FengMallePrincipalWeight := D.PrincipalWeight

abbrev PrincipalBrauer :=
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  BrauerFibre D.iota D.injective
    D.blockSource.operations.ambientBlockData.blocks D.principalBlock

def intrinsicWeightEquiv : D.FYZPrincipalWeight ≃ D.FengMallePrincipalWeight :=
  Equiv.refl _

/-- The full automorphism action is obtained from actual automorphisms of
the literal symplectic group and the existing quotient action. -/
local instance principalWeightAction :
    MulAction (MulAut (Sp n F)) D.PrincipalWeight :=
  rightWeightFibreMulAction (MonoidHom.id _) D.blockSource D.principalBlock
    (fun _ => D.principalBlock_fixed _)

local instance principalBrauerAction :
    MulAction (MulAut (Sp n F)) D.PrincipalBrauer :=
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  rightIBrBlockMulAction D.iota D.injective
    D.blockSource.operations.ambientBlockData.blocks
    (MonoidHom.id _) D.principalBlock
    (fun _ => D.principalBlock_fixed _) D.support_transport

/-- Feng--Malle Theorem 6.2 on its intrinsic domain.  The group, prime,
principal block, character functions, weight pairs, and full automorphism
actions are fixed by `D`.  This narrow E2 certificate gives no local triple
relation, no all-block map, and no projective-group iBAW conclusion.

The interpretation of `D`'s coefficient/block operations remains E1/U;
defining this type does not construct an authenticated literature instance. -/
structure FengMalleTheorem62LiteralCertificate where
  rank_ge_two : 2 ≤ n
  odd_field : Odd (Nat.card F)
  omega : D.PrincipalBrauer ≃ D.FengMallePrincipalWeight
  equivariant : ∀ (a : MulAut (Sp n F)) (chi : D.PrincipalBrauer),
    omega (a • chi) = a • omega chi

/-- The principal correspondence has no old/new carrier-adapter premise:
FYZ and FM describe the same intrinsic conjugacy class fibre. -/
def intrinsicPrincipalEquiv (T : D.FengMalleTheorem62LiteralCertificate) :
    D.PrincipalBrauer ≃ D.FYZPrincipalWeight := T.omega

theorem intrinsicPrincipalEquiv_equivariant
    (T : D.FengMalleTheorem62LiteralCertificate)
    (a : MulAut (Sp n F)) (chi : D.PrincipalBrauer) :
    D.intrinsicPrincipalEquiv T (a • chi) =
      a • D.intrinsicPrincipalEquiv T chi := T.equivariant a chi

theorem intrinsicWeightEquiv_equivariant
    (a : MulAut (Sp n F)) (w : D.PrincipalWeight) :
    D.intrinsicWeightEquiv (a • w) = a • D.intrinsicWeightEquiv w := rfl

/-- An identical intrinsic weight uses the same chosen pair on both sides.
No equivariance of this choice of representative is asserted. -/
theorem intrinsicWeightEquiv_selectedPair (w : D.PrincipalWeight) :
    selectedCharacterWeight D.blockSource D.principalBlock
        (D.intrinsicWeightEquiv w) =
      selectedCharacterWeight D.blockSource D.principalBlock w := rfl

/-- The literal selected character retains its actual defect-zero proof. -/
theorem selectedCharacter_defectZero (w : D.PrincipalWeight) :
    IsDefectZeroOrdinaryCharacter 2
      (selectedCharacterWeight D.blockSource D.principalBlock w).localCharacter :=
  (selectedCharacterWeight D.blockSource D.principalBlock w).defectZero

theorem selectedPair_principalBlock (w : D.PrincipalWeight) :
    D.blockSource.operations.rawWeightBlock
      (selectedCharacterWeight D.blockSource D.principalBlock w) =
        D.principalBlock := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  exact selectedCharacterWeight_block D.blockSource D.principalBlock w

/-- The full block-induction statement for the selected actual local
character, not merely equality of a label called its induced block. -/
theorem selectedPair_blockInducesTo (w : D.PrincipalWeight) :
    let W := selectedCharacterWeight D.blockSource D.principalBlock w
    let O := D.blockSource.operations
    let localData := O.inflatedNormalizerBlockData W.subgroup
    letI := O.ambientBlockData.fintypeBlock
    letI := localData.fintypeBlock
    ModularRep.BlockInducesTo
      (Subgroup.normalizer (W.subgroup : Set (Sp n F)))
      localData.catalogue O.ambientBlockData.catalogue
      (O.inflateToNormalizer W.subgroup
        (O.localCharacterBlock W.subgroup W.localCharacter W.defectZero))
      D.principalBlock := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  exact selectedCharacterWeight_blockInducesTo D.blockSource D.principalBlock w

/-- Build the fixed Definition 3.5 problem on the literal matrix group.
Only the selected local reduction is additional character-theoretic input. -/
def problem
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w) :
    Definition35Problem :=
  Definition35Problem.ofOperations D.iota D.injective D.blockSource
    D.principalBlock (MonoidHom.id (MulAut (Sp n F)))
    (fun _ => D.principalBlock_fixed _) D.support_transport reduction

@[simp] theorem problem_group
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w) :
    (D.problem reduction).H = Sp n F := rfl

@[simp] theorem problem_prime
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w) :
    (D.problem reduction).p = 2 := rfl

/-- The principal block is invariant under every actual automorphism, so
its automorphism stabilizer is the full group.  This adapter is constructed
in K, rather than left as a separate source-carrier equivalence. -/
def automorphisms
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w) :
    Definition35AutomorphismStabilizerAdapter (D.problem reduction) where
  equiv :=
    { toFun := fun a => ⟨MulOpposite.op a⁻¹, D.principalBlock_fixed _⟩
      invFun := fun a => a.1.unop⁻¹
      left_inv := by
        intro a
        change ((a : MulAut (Sp n F))⁻¹)⁻¹ = a
        exact inv_inv a
      right_inv := by
        intro a
        apply Subtype.ext
        change MulOpposite.op ((a.1.unop : MulAut (Sp n F))⁻¹)⁻¹ = a.1
        rw [inv_inv]
        exact MulOpposite.op_unop a.1
      map_mul' := by
        intro a b
        apply Subtype.ext
        change MulOpposite.op (((a : MulAut (Sp n F)) * b)⁻¹) =
          MulOpposite.op a⁻¹ * MulOpposite.op b⁻¹
        simp only [mul_inv_rev, MulOpposite.op_mul] }
  equiv_coe := fun _ => rfl

/-- The intrinsic Theorem 6.2 map has exactly the fixed Definition 3.5
carriers.  This still makes no claim about the required local triple. -/
def definition35Equiv
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w)
    (T : D.FengMalleTheorem62LiteralCertificate) :
    Definition35Brauer (D.problem reduction) ≃
      Definition35Weight (D.problem reduction) := T.omega

theorem definition35Equiv_equivariant
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w)
    (T : D.FengMalleTheorem62LiteralCertificate) :
    Definition35Equivariant (D.problem reduction) (D.definition35Equiv reduction T) :=
  T.equivariant

/-- The precise unresolved relation is required on the very same intrinsic
map.  Neither Theorem 6.2 nor identity of sets of weights proves it. -/
def definition35Seed
    (reduction : ∀ w : D.PrincipalWeight,
      SelectedLocalReductionSource D.blockSource D.principalBlock w)
    (T : D.FengMalleTheorem62LiteralCertificate)
    (source : FLZSourceSemantics (D.problem reduction) (D.automorphisms reduction))
    (localTriple : ∀ psi : Definition35Brauer (D.problem reduction),
      source.definition35BlockIsomorphic psi (D.definition35Equiv reduction T psi)) :
    Definition35IBAWBijection (D.problem reduction) (D.automorphisms reduction) source where
  omega := D.definition35Equiv reduction T
  equivariant := D.definition35Equiv_equivariant reduction T
  blockIsomorphism := localTriple

end PrincipalCharacterData

/-- Equality of the selected subgroup and of its transported local character
implies equality of the actual weight pair.  Hence normalisers, induced
blocks and all automorphism images agree by K, without an equivalence of
unrelated ambient character universes. -/
theorem selectedPair_eq
    {W V : CharacterWeight 2 K (Sp n F)}
    (hQ : W.subgroup = V.subgroup)
    (hchi : castLocalCharacter hQ W.localCharacter = V.localCharacter) :
    W = V := eq_of_isomorphic ⟨hQ, hchi⟩

/-- Source representatives may differ by actual conjugation.  Equality of
their transported selected local characters then gives the same intrinsic
weight class.  No equality of independently chosen representatives is used. -/
theorem weightClass_eq_of_conjugate_selectedPair
    {W V : CharacterWeight 2 K (Sp n F)} (g : Sp n F)
    (h : Isomorphic (W.rightTwist (MulAut.conj g⁻¹)) V) :
    (Quotient.mk'' (Quotient.mk'' W) :
      CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Sp n F)) =
      Quotient.mk'' (Quotient.mk'' V) := by
  symm
  apply Quotient.sound
  refine ⟨g, ?_⟩
  change (Quotient.mk'' (W.rightTwist (MulAut.conj g⁻¹)) :
    CharacterWeight.IsoClass (p := 2) (K := K) (G := Sp n F)) = Quotient.mk'' V
  exact Quotient.sound h

end LiteralPrincipal

/-! ## Source case names and the honest exhaustive factor join -/

/-- The six alternatives in FYZ Proposition 3.48, printed p. 35. -/
inductive FYZCase
  | signs | regular | quaternion | correctedEven | generalLinear | typeFour
  deriving DecidableEq

/-- The two surviving families have different An locators.  This is a
classification index, not a concrete subgroup or local-character model. -/
inductive PrincipalFamily
  | quaternion   -- FYZ (3), An (4F)(b)
  | typeFour -- FYZ (6), An (4F)(d): generalized quaternion tensor family
  deriving DecidableEq

def PrincipalFamily.sourceCase : PrincipalFamily → FYZCase
  | .quaternion => .quaternion
  | .typeFour => .typeFour

/-- K exhaustive routing.  The case-(4) input must be instantiated by an
exhaustive map to the occurrence carrier already excluded by the checked
reflection/Sylow argument.  An arbitrary empty occurrence type is not a
source realization.  The other three exclusions are the restricted source
clauses in FYZ Remark 3.50, not a claim about local characters. -/
theorem principalFactor_has_survivingFamily
    {Factor Occurrence : Type u} [IsEmpty Occurrence]
    (sourceCase : Factor → FYZCase)
    (not_signs : ∀ f, sourceCase f ≠ .signs)
    (not_regular : ∀ f, sourceCase f ≠ .regular)
    (not_generalLinear : ∀ f, sourceCase f ≠ .generalLinear)
    (correctedOccurrence : ∀ f, sourceCase f = .correctedEven → Occurrence)
    (f : Factor) :
    ∃ family : PrincipalFamily, family.sourceCase = sourceCase f := by
  cases h : sourceCase f with
  | signs => exact (not_signs f h).elim
  | regular => exact (not_regular f h).elim
  | generalLinear => exact (not_generalLinear f h).elim
  | correctedEven => exact isEmptyElim (correctedOccurrence f h)
  | quaternion => exact ⟨.quaternion, rfl⟩
  | typeFour => exact ⟨.typeFour, rfl⟩

/-- FYZ writes `(c_t,...,c_1)` whereas An/FM write `(c_1,...,c_t)`.
This reverses the stored list only; a subgroup/action identification is a
separate source obligation, not a consequence of this numerical identity. -/
def fyzToFengMalleWreathList (cs : List ℕ) : List ℕ := cs.reverse

theorem fyzToFengMalleWreathList_involutive :
    Function.Involutive fyzToFengMalleWreathList := by
  intro cs
  exact List.reverse_reverse cs

end ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
