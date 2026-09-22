import ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation
import ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier
import ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
import ModularRep.PrimeRegularRootEmbeddingPQuotient

/-!
# The actual global Sp/PSp Brauer inflation and principal fibres

K identifies O_2(Sp) with the actual centre using the two-kernel and the
nonabelian simple projective quotient. The precise normal-core source in
MRR, Lemma 6.3, p.359, can consequently use this same quotient.

Navarro, Lemma 2.32 and the proof of Theorem 9.11 (p.201), supply only
kernel triviality of irreducible modular representations and regular-element
lifts. The existing representation inflation/descent constructs the actual
BrauerInflationInput, equivalence and quotient-automorphism naturality.
Root compatibility is along the fixed projection, with the downstairs
convention first. No Brauer equivalence is a source field.

Navarro, Theorem 9.10 (p.201), is used only for the actual central two-kernel.
Its more general hypothesis is G/C_G(P) a p-group; central P satisfies it.
The source fields concern primitive idempotents under the literal quotient
group algebra map and the support of the actual inflated character. K then
restricts the constructed equivalence to the blocks of constant-one
characters. No desired principal-fibre equivalence is assumed.

The source facts and their coefficient/block interpretation remain E1.
Full automorphism lifting, weight-class/block transport, and the FLZ full
semidirect/stabilizer relation join remain separate. No final iBAW witness
or arbitrary target predicate occurs here.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation

open ModularRep.FDRepSimpleClassKZero
open ModularRep.IrreducibleBrauerCharacterSurjectiveDescent
open ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

/-- A finite nonabelian simple group has trivial two-core. This follows
from the existing nilpotent-simple-group theorem, not an additional source.
-/
theorem twoCore_eq_bot_of_nonabelian_simple
    {S : Type u} [Group S] [Finite S]
    (hsimple : IsSimpleGroup S) (hnonabelian : ¬ IsMulCommutative S) :
    pCore 2 S = ⊥ := by
  letI : IsSimpleGroup S := hsimple
  rcases (pCore_normal 2 S).eq_bot_or_eq_top with h | h
  · exact h
  · have hgroup : IsPGroup 2 S := by
      intro x
      obtain ⟨a, ha⟩ := pCore_isPGroup 2 S ⟨x, by rw [h]; trivial⟩
      exact ⟨a, congrArg Subtype.val ha⟩
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Group.IsNilpotent S := hgroup.isNilpotent
    exact (hnonabelian (by infer_instance)).elim

section LiteralGroups

variable {n : ℕ} {F : Type u} [Field F] [Finite F]

/-- The actual O_2 quotient in MRR Lemma 6.3 is the displayed PSp quotient.
No freely selected quotient or p-core identification is a premise. -/
theorem sp_twoCore_eq_center (cover : OddSymplecticFullCoverSource n F) :
    pCore 2 (LiteralSp n F) = Subgroup.center (LiteralSp n F) := by
  have hmap : (pCore 2 (LiteralSp n F)).map (literalProjection n F) = ⊥ :=
    (pCore_map_surjective_of_ker_isPGroup (literalProjection n F)
      cover.fullCover.1.1 cover.projection_twoKernel).trans
      (twoCore_eq_bot_of_nonabelian_simple cover.simple cover.nonabelian)
  have hupper : pCore 2 (LiteralSp n F) ≤ (literalProjection n F).ker := by
    intro x hx
    have hmem : literalProjection n F x ∈
        (pCore 2 (LiteralSp n F)).map (literalProjection n F) := ⟨x, hx, rfl⟩
    rw [hmap] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hkernel : (literalProjection n F).ker =
      Subgroup.center (LiteralSp n F) := QuotientGroup.ker_mk' _
  rw [← hkernel]
  exact le_antisymm hupper
    (normal_pSubgroup_le_pCore 2 (literalProjection n F).ker cover.projection_twoKernel)

/-- Every actual Sp automorphism preserves its actual centre. -/
theorem center_map_eq (alpha : MulAut (LiteralSp n F)) :
    (Subgroup.center (LiteralSp n F)).map alpha.toMonoidHom =
      Subgroup.center (LiteralSp n F) :=
  Subgroup.characteristic_iff_map_eq.mp inferInstance alpha

/-- The induced projective automorphism, constructed from the fixed quotient.
Surjectivity onto all projective automorphisms is not asserted here. -/
def projectiveAutomorphism (alpha : MulAut (LiteralSp n F)) :
    MulAut (LiteralPSp n F) :=
  quotientMulAut (Subgroup.center (LiteralSp n F)) alpha (center_map_eq alpha)

@[simp] theorem projectiveAutomorphism_projection
    (alpha : MulAut (LiteralSp n F)) (g : LiteralSp n F) :
    projectiveAutomorphism alpha (literalProjection n F g) =
      literalProjection n F (alpha g) := rfl

end LiteralGroups

section BrauerInflation

variable {n : ℕ} {F k K : Type u} [Field F] [Finite F]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable (iotaUp : PrimeRegularRootEmbedding 2 k K (LiteralSp n F))
variable (iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F))

/-- Exact standard E1 facts. The kernel field is Navarro 2.32 on actual
irreducible representations, not a preselected downstairs character.
The regular lift is the quotient fact proved in Navarro 9.11. -/
structure BrauerInflationSources : Prop where
  rootCompatible : ∀ V : FDRep k (LiteralPSp n F),
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaDown iotaUp
      (literalProjection n F)
  pCore_kernel : ∀ V : FDRep k (LiteralSp n F),
    Representation.IsIrreducible V.ρ → pCore 2 (LiteralSp n F) ≤ V.ρ.ker
  regularLift : ∀ y : PrimeRegularElement (G := LiteralPSp n F) 2,
    ∃ x : PrimeRegularElement (G := LiteralSp n F) 2,
      PrimeRegularElement.map (literalProjection n F) x = y

namespace BrauerInflationSources

variable {iotaUp iotaDown}
variable (C : BrauerInflationSources iotaUp iotaDown)
variable (cover : OddSymplecticFullCoverSource n F)

/-- Construct the existing inflation input using actual representation
inflation and descent, the proved p-core identity and standard E1 facts.
The prime-to-p-kernel equivalence in the old descent file is not used. -/
def inflationInput : BrauerInflationInput (Subgroup.center (LiteralSp n F))
    iotaDown iotaUp where
  inflatedIrreducible phi := by
    exact (inflateToKernelTrivialIBrAlong (literalProjection n F)
      cover.fullCover.1.1 iotaUp iotaDown C.rootCompatible phi).1.2
  descends phi := by
    obtain ⟨V, hV, hphi⟩ := phi.2
    have hkernel : (literalProjection n F).ker ≤ V.ρ.ker := by
      simpa only [literalProjection, QuotientGroup.ker_mk', sp_twoCore_eq_center cover]
        using C.pCore_kernel V hV
    let kernelTrivial : KernelTrivialIBrAlong (literalProjection n F) iotaUp :=
      ⟨phi, V, hV, hphi, hkernel⟩
    refine ⟨descendIBrAlong (literalProjection n F) cover.fullCover.1.1
      iotaUp iotaDown kernelTrivial, ?_⟩
    exact descendIBrAlong_pullback (literalProjection n F) cover.fullCover.1.1
      iotaUp iotaDown C.rootCompatible kernelTrivial
  regularLift := C.regularLift

/-- The actual IBr equivalence through the same central-two projection. -/
def brauerEquiv : IBr iotaDown ≃ IBr iotaUp := (C.inflationInput cover).equiv

@[simp] theorem brauerEquiv_value (phi : IBr iotaDown)
    (g : PrimeRegularElement (G := LiteralSp n F) 2) :
    (C.brauerEquiv cover phi).1 g =
      phi.1 (PrimeRegularElement.map (literalProjection n F) g) := rfl

/-- Naturality uses the same actual quotient automorphism and exact roots.
It does not choose an independent action on the downstairs character set. -/
theorem brauerEquiv_twist (alpha : MulAut (LiteralSp n F)) (phi : IBr iotaDown) :
    C.brauerEquiv cover
        (IrreducibleBrauerCharacter.twist iotaDown phi (projectiveAutomorphism alpha)) =
      IrreducibleBrauerCharacter.twist iotaUp (C.brauerEquiv cover phi) alpha :=
  BrauerInflationInput.inflate_twist
    (P := Subgroup.center (LiteralSp n F)) (iotaDown := iotaDown) (iotaUp := iotaUp)
    (C.inflationInput cover) alpha (center_map_eq alpha) phi

/-- The constant-one character is preserved by the actual inflation map. -/
theorem brauerEquiv_trivial (oneDown : IBr iotaDown) (oneUp : IBr iotaUp)
    (down_value : ∀ g, oneDown.1 g = 1) (up_value : ∀ g, oneUp.1 g = 1) :
    C.brauerEquiv cover oneDown = oneUp := by
  apply Subtype.ext
  ext g
  rw [brauerEquiv_value, down_value, up_value]

end BrauerInflationSources

end BrauerInflation

section PrimitiveBlocks

variable {n : ℕ} {F k K : Type u} [Field F] [Finite F]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable {iotaUp : PrimeRegularRootEmbedding 2 k K (LiteralSp n F)}
variable {iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F)}
variable (C : BrauerInflationSources iotaUp iotaDown)
variable (cover : OddSymplecticFullCoverSource n F)
variable {I J : Type u} [Fintype I] [Fintype J]
variable {bUp : I → k[LiteralSp n F]} {bDown : J → k[LiteralPSp n F]}
variable (upBlocks : BlockIdempotentDecomposition bUp)
variable (downBlocks : BlockIdempotentDecomposition bDown)
variable (upInjective : IrreducibleBrauerCharacterInjectivity iotaUp)
variable (downInjective : IrreducibleBrauerCharacterInjectivity iotaDown)

/-- The literal group algebra projection. -/
def quotientAlgebraMap : k[LiteralSp n F] →ₐ[k] k[LiteralPSp n F] :=
  MonoidAlgebra.mapDomainAlgHom k k (literalProjection n F)

/-- The precise central-p specialization of Navarro 9.10 on primitive
idempotents and actual Brauer support. The maps, root compatibility,
characters and complete primitive catalogues are fixed by the parameters.
No block-fibre equivalence or principal-character comparison is a field.

This is not asserted for arbitrary normal p-subgroups: the displayed kernel
is central and its order two is supplied by the exact cover packet. -/
structure Navarro910PrimitiveSource : Prop where
  primitive_image : ∀ b : {b : k[LiteralSp n F] // IsPrimitiveCentralIdempotent b},
    IsPrimitiveCentralIdempotent (quotientAlgebraMap b.1)
  primitive_injective : ∀ b c :
      {b : k[LiteralSp n F] // IsPrimitiveCentralIdempotent b},
    quotientAlgebraMap b.1 = quotientAlgebraMap c.1 → b = c
  inflated_support : ∀ phi : IBr iotaDown,
    quotientAlgebraMap
        (bUp (irreducibleBrauerCharacterBlock iotaUp upInjective upBlocks
          (C.brauerEquiv cover phi))) =
      bDown (irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks phi)

namespace Navarro910PrimitiveSource

variable {C cover upBlocks downBlocks upInjective downInjective}
variable (S : Navarro910PrimitiveSource C cover upBlocks downBlocks upInjective downInjective)

/-- The source-prescribed algebra projection gives an actual primitive
block map; no independently chosen map on block labels is used. -/
def primitiveMap :
    {b : k[LiteralSp n F] // IsPrimitiveCentralIdempotent b} →
      {b : k[LiteralPSp n F] // IsPrimitiveCentralIdempotent b} :=
  fun b => ⟨quotientAlgebraMap b.1, S.primitive_image b⟩

theorem primitiveMap_injective : Function.Injective S.primitiveMap := by
  intro b c h
  exact S.primitive_injective b c (congrArg Subtype.val h)

include S in
/-- K derives equality of the two block labels on the inflated characters
from injectivity of the actual primitive-idempotent projection. -/
theorem sameBlock_iff (phi psi : IBr iotaDown) :
    irreducibleBrauerCharacterBlock iotaUp upInjective upBlocks
        (C.brauerEquiv cover phi) =
      irreducibleBrauerCharacterBlock iotaUp upInjective upBlocks
        (C.brauerEquiv cover psi) ↔
    irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks phi =
      irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks psi := by
  constructor
  · intro h
    apply downBlocks.primitiveBlockOfIndex_injective
    apply Subtype.ext
    change bDown (irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks phi) =
      bDown (irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks psi)
    rw [← S.inflated_support phi, ← S.inflated_support psi, h]
  · intro h
    apply upBlocks.primitiveBlockOfIndex_injective
    apply S.primitive_injective
    change quotientAlgebraMap
        (bUp (irreducibleBrauerCharacterBlock iotaUp upInjective upBlocks
          (C.brauerEquiv cover phi))) =
      quotientAlgebraMap
        (bUp (irreducibleBrauerCharacterBlock iotaUp upInjective upBlocks
          (C.brauerEquiv cover psi)))
    rw [S.inflated_support, S.inflated_support, h]

/-- Restrict the already constructed literal IBr equivalence to the actual
principal blocks, each selected by its constant-one character. -/
def principalBrauerEquiv
    (oneDown : IBr iotaDown) (oneUp : IBr iotaUp)
    (down_value : ∀ g, oneDown.1 g = 1) (up_value : ∀ g, oneUp.1 g = 1) :
    IBrBlock iotaDown downInjective downBlocks
        (irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks oneDown) ≃
      IBrBlock iotaUp upInjective upBlocks
        (irreducibleBrauerCharacterBlock iotaUp upInjective upBlocks oneUp) where
  toFun phi := ⟨C.brauerEquiv cover phi.1, by
    have h := (S.sameBlock_iff phi.1 oneDown).mpr phi.2
    rw [C.brauerEquiv_trivial cover oneDown oneUp down_value up_value] at h
    exact h⟩
  invFun psi := ⟨(C.brauerEquiv cover).symm psi.1, by
    apply (S.sameBlock_iff ((C.brauerEquiv cover).symm psi.1) oneDown).mp
    rw [Equiv.apply_symm_apply,
      C.brauerEquiv_trivial cover oneDown oneUp down_value up_value]
    exact psi.2⟩
  left_inv phi := Subtype.ext ((C.brauerEquiv cover).symm_apply_apply phi.1)
  right_inv psi := Subtype.ext ((C.brauerEquiv cover).apply_symm_apply psi.1)

@[simp] theorem principalBrauerEquiv_value
    (oneDown : IBr iotaDown) (oneUp : IBr iotaUp)
    (down_value : ∀ g, oneDown.1 g = 1) (up_value : ∀ g, oneUp.1 g = 1)
    (phi : IBrBlock iotaDown downInjective downBlocks
      (irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks oneDown))
    (g : PrimeRegularElement (G := LiteralSp n F) 2) :
    (S.principalBrauerEquiv oneDown oneUp down_value up_value phi).1.1 g =
      phi.1.1 (PrimeRegularElement.map (literalProjection n F) g) := rfl

end Navarro910PrimitiveSource

end PrimitiveBlocks

section ExistingPrincipalCarrier

open ModularRep.PaperProofs.OddTwoPrincipalIntrinsicCarrier

variable {n : ℕ} {F k K Block J : Type u} [Field F] [Fintype F]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [MulAction (MulAut (Sp n F))ᵐᵒᵖ Block] [Fintype J]
variable {bDown : J → k[LiteralPSp n F]}

local instance existingSpFintype : Fintype (Sp n F) := Fintype.ofFinite _

/-- The target is exactly the existing intrinsic principal Brauer fibre
used by the FM certificate, with its own constant-one character and actual
operations catalogue. No new principal predicate or block choice is added.
-/
def principalBrauerEquivForData
    (D : PrincipalCharacterData (n := n) (F := F) (k := k) (K := K) (Block := Block))
    (cover : OddSymplecticFullCoverSource n F)
    (iotaDown : PrimeRegularRootEmbedding 2 k K (LiteralPSp n F))
    (downInjective : IrreducibleBrauerCharacterInjectivity iotaDown)
    (downBlocks : BlockIdempotentDecomposition bDown)
    (oneDown : IBr iotaDown) (down_value : ∀ g, oneDown.1 g = 1)
    (C : BrauerInflationSources D.iota iotaDown)
    (S : letI := D.blockSource.operations.ambientBlockData.fintypeBlock
      Navarro910PrimitiveSource C cover
        D.blockSource.operations.ambientBlockData.blocks downBlocks
        D.injective downInjective) :
    IBrBlock iotaDown downInjective downBlocks
        (irreducibleBrauerCharacterBlock iotaDown downInjective downBlocks oneDown) ≃
      D.PrincipalBrauer := by
  letI := D.blockSource.operations.ambientBlockData.fintypeBlock
  exact S.principalBrauerEquiv oneDown D.trivialCharacter down_value D.trivial_value

end ExistingPrincipalCarrier

end ModularRep.PaperProofs.OddTwoCentralTwoGlobalInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
