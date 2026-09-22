import ModularRep.BlockInduction
import ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
import ModularRep.PaperProofs.EvenFieldFMZGenericPair
import ModularRep.WeightCharacterBridge
import Mathlib.Data.Complex.Basic

/-!
# Orbit carriers for e-JGC pair data in the even field argument

This module removes the free `PairClass` and free relative Weyl group family
from the Lemma 3.7 interface.  A raw pair is the dependent pair
`(T, lambda)`, where `lambda` is an actual complex irreducible character of
the finite Levi attached to `T`.  The restricted pairs are quotiented by the
finite group action, and the relative Weyl group of a chosen class
representative is definitionally the character inertia group modulo the
embedded Levi.

Membership in `D.inL` is still an E2/U-level interpretation of the FMZ
notions: Deligne--Lusztig theory and the FMZ definitions are not available in
Mathlib.  Complete block catalogues and the ordinary character block
labelling are E1/U inputs.  The implication from `D.inL` to literal block
induction is the separately exposed E2/U input supplied by the proof of FMZ,
Proposition 3.24.  The action formula is exposed on the dependent pair
carrier, so it cannot be replaced by an unrelated permutation action.  No
ambient block selector, bijection, fixedness statement, or Lemmas 3.6 and 3.7
conclusion occurs in the source.
-/

namespace ModularRep.PaperProofs.EvenFieldEJGCPairActual

open scoped MonoidAlgebra

open ModularRep
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPair
open ModularRep.PaperProofs.EvenFieldAlgebraicTorusPairInertiaBridge
open ModularRep.PaperProofs.EvenFieldFMZGenericPair

noncomputable section

variable {H A Block : Type} [Group H] [Fintype H]
    [MulAction (MulAut H) A]

/-- A dependent finite Levi character attached to a semantic torus label.
Instantiation with the FMZ admissible tori remains U-level. -/
abbrev RawPair (D : Definitions ℂ H A Block) :=
  Σ T : A, Irr ℂ (D.levi T)

/-- The embedding of the semantic finite Levi in the ambient finite group. -/
def finiteLeviEmbedding (D : Definitions ℂ H A Block) (T : A) :
    D.levi T →* H :=
  (finiteNormalizer (H := H) T).subtype.comp (D.levi T).subtype

/-- The finite Levi as an actual subgroup of the ambient finite group. -/
def finiteLevi (D : Definitions ℂ H A Block) (T : A) : Subgroup H :=
  (finiteLeviEmbedding D T).range

local instance finiteLeviFintype
    (D : Definitions ℂ H A Block) (T : A) : Fintype (finiteLevi D T) :=
  Fintype.ofFinite _

/-- The canonical equivalence from the semantic Levi carrier to its embedded
image in the ambient finite group. -/
def finiteLeviEquiv (D : Definitions ℂ H A Block) (T : A) :
    D.levi T ≃* finiteLevi D T := by
  apply MulEquiv.ofBijective
    ((finiteLeviEmbedding D T).codRestrict (finiteLevi D T)
      (fun x ↦ ⟨x, rfl⟩))
  constructor
  · intro x y h
    have hH : finiteLeviEmbedding D T x = finiteLeviEmbedding D T y :=
      congrArg (fun z : finiteLevi D T ↦ (z : H)) h
    apply Subtype.ext
    apply Subtype.ext
    exact hH
  · intro y
    obtain ⟨x, hx⟩ := y.2
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/-- The embedded Levi, viewed as a subgroup of its ambient normaliser. -/
def finiteLeviInNormalizer (D : Definitions ℂ H A Block) (T : A) :
    Subgroup (Subgroup.normalizer (finiteLevi D T : Set H)) :=
  (finiteLevi D T).subgroupOf
    (Subgroup.normalizer (finiteLevi D T : Set H))

/-- Transport a finite Levi character to the embedded Levi subgroup. -/
def finiteLeviCharacter (D : Definitions ℂ H A Block) (P : RawPair D) :
    Irr ℂ (finiteLevi D P.1) :=
  mapEquiv P.2 (finiteLeviEquiv D P.1)

/-- The same character on the copy of the Levi inside its normaliser. -/
def finiteLeviNormalizerCharacter
    (D : Definitions ℂ H A Block) (P : RawPair D) :
    Irr ℂ (finiteLeviInNormalizer D P.1) :=
  mapEquiv (finiteLeviCharacter D P)
    (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).symm

/-- A complete ambient block decomposition and the associated block central
characters.  The catalogue is the E1 block theoretic input represented by
Navarro's Theorem 3.11. -/
structure AmbientBlockCatalogueData
    (k H Block : Type) [Field k] [IsAlgClosed k] [Group H] [Fintype H] where
  [fintypeBlock : Fintype Block]
  blockIdempotent : Block → k[H]
  blocks : BlockIdempotentDecomposition blockIdempotent
  catalogue : BlockCentralCharacterCatalogue blocks

/-- The block data attached to one finite Levi.

`blockOfCharacter` is the U-level interpretation of `chi ↦ bl(chi)` on the
set of ordinary characters of this fixed Levi.  In particular, it cannot
vary with another raw pair having the same torus component.  It selects a
block of the finite Levi, not an ambient block.  The ambient block is
constrained only by literal block induction below. -/
structure FiniteLeviBlockCatalogueData
    (k : Type) [Field k] [IsAlgClosed k]
    (D : Definitions ℂ H A Block) (T : A) where
  LocalBlock : Type
  [fintypeLocalBlock : Fintype LocalBlock]
  blockIdempotent : LocalBlock → k[finiteLevi D T]
  blocks : BlockIdempotentDecomposition blockIdempotent
  catalogue : BlockCentralCharacterCatalogue blocks
  blockOfCharacter : Irr ℂ (finiteLevi D T) → LocalBlock

/-- E1/U block data needed to formulate the FMZ condition
`bl(lambda)^H = C` literally.  There is no function selecting an ambient
block. -/
structure PairBlockInductionSource
    (ell : ℕ) (k : Type) [Field k] [CharP k ell] [IsAlgClosed k]
    (D : Definitions ℂ H A Block) where
  ambient : AmbientBlockCatalogueData k H Block
  localBlockData : ∀ T : A, FiniteLeviBlockCatalogueData k D T

namespace PairBlockInductionSource

/-- The block of the finite Levi character belonging to `P` induces to the
ambient block `C`, in the literal central character sense. -/
def BlockInducesTo
    {ell : ℕ} {k : Type} [Field k] [CharP k ell] [IsAlgClosed k]
    {D : Definitions ℂ H A Block}
    (S : PairBlockInductionSource ell k D) (P : RawPair D) (C : Block) :
    Prop :=
  let localData := S.localBlockData P.1
  letI : Fintype Block := S.ambient.fintypeBlock
  letI : Fintype localData.LocalBlock := localData.fintypeLocalBlock
  ModularRep.BlockInducesTo (finiteLevi D P.1)
    localData.catalogue S.ambient.catalogue
    (localData.blockOfCharacter (finiteLeviCharacter D P)) C

end PairBlockInductionSource

/-- Source data needed to interpret conjugation and the pair classes in
Theorem 7.5.

`pairAction_formula` prevents `pairAction` from being an unrelated action:
it is transport of the actual dependent irreducible character along the
specified conjugation equivalence of finite Levi groups.  The ambient
formula for `leviEquiv` is recorded separately.  The conjugation invariance
of `D.inL` is an E2/U semantic input.  The final field is the E2/U adapter
from the proof of FMZ, Proposition 3.24, which ties that semantic predicate
to literal block induction. -/
structure PairClassSource
    (ell : ℕ) (k : Type) [Field k] [CharP k ell] [IsAlgClosed k]
    (D : Definitions ℂ H A Block) where
  normalizerLevi_eq_finiteNormalizer : ∀ T : A,
    Subgroup.normalizer ((finiteLevi D T : Subgroup H) : Set H) =
      finiteNormalizer (H := H) T
  leviEquiv : ∀ (h : H) (T : A),
    D.levi T ≃* D.levi ((MulAut.conj h) • T)
  leviEquiv_coe : ∀ (h : H) (T : A) (x : D.levi T),
    (((leviEquiv h T x : D.levi ((MulAut.conj h) • T)) :
        finiteNormalizer (H := H) ((MulAut.conj h) • T)) : H) =
      h * (((x : D.levi T) : finiteNormalizer (H := H) T) : H) * h⁻¹
  pairAction : H →* Equiv.Perm (RawPair D)
  pairAction_formula : ∀ (h : H) (P : RawPair D),
    pairAction h P =
      ⟨(MulAut.conj h) • P.1,
        transportIrr (leviEquiv h P.1) P.2⟩
  blockInduction : PairBlockInductionSource ell k D
  inL_conjugation : ∀ (h : H) (C : Block) (P : RawPair D),
    D.inL C P.1 P.2 ↔
      D.inL C (pairAction h P).1 (pairAction h P).2
  /-- E2/U source adapter: the block-induction consequence established in
  the proof of Feng--Malle--Zhang, Proposition 3.24. -/
  inL_blockInducesTo : ∀ (C : Block) (P : RawPair D),
    D.inL C P.1 P.2 → blockInduction.BlockInducesTo P C

namespace PairClassSource

variable {ell : ℕ} {k : Type} [Field k] [CharP k ell] [IsAlgClosed k]
variable {D : Definitions ℂ H A Block} (S : PairClassSource ell k D)

/-- The FMZ predicate in equation (7.2).  Its literal block-induction
consequence is derived below from the cited Proposition 3.24 adapter. -/
def IsRestrictedToBlock (_source : PairClassSource ell k D)
    (C : Block) (P : RawPair D) : Prop :=
  D.inL C P.1 P.2

/-- The dependent pairs belonging to `L(C)` in FMZ equation (7.2). -/
abbrev RestrictedPair (C : Block) :=
  {P : RawPair D // S.IsRestrictedToBlock C P}

/-- Literal block induction for a restricted pair, derived in the kernel
from the separately exposed FMZ Proposition 3.24 source field. -/
theorem restrictedPair_blockInducesTo {C : Block}
    (P : S.RestrictedPair C) :
    S.blockInduction.BlockInducesTo P.1 C :=
  S.inL_blockInducesTo C P.1 P.2

/-- The actual conjugation action restricted to the relevant pairs. -/
def restrictedPairAction (C : Block) : H →* Equiv.Perm (S.RestrictedPair C) where
  toFun h :=
    { toFun := fun P ↦
        ⟨S.pairAction h P.1, (S.inL_conjugation h C P.1).mp P.2⟩
      invFun := fun P ↦
        ⟨S.pairAction h⁻¹ P.1, (S.inL_conjugation h⁻¹ C P.1).mp P.2⟩
      left_inv := by
        intro P
        apply Subtype.ext
        change S.pairAction h⁻¹ (S.pairAction h P.1) = P.1
        simpa using (S.pairAction h).symm_apply_apply P.1
      right_inv := by
        intro P
        apply Subtype.ext
        change S.pairAction h (S.pairAction h⁻¹ P.1) = P.1
        simpa using (S.pairAction h).apply_symm_apply P.1 }
  map_one' := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change S.pairAction 1 P.1 = P.1
    rw [S.pairAction.map_one]
    rfl
  map_mul' h g := by
    apply Equiv.ext
    intro P
    apply Subtype.ext
    change S.pairAction (h * g) P.1 =
      S.pairAction h (S.pairAction g P.1)
    rw [S.pairAction.map_mul]
    rfl

/-- The orbit relation for the literal restricted pair carrier. -/
def restrictedPairSetoid (C : Block) : Setoid (S.RestrictedPair C) := by
  let _ : MulAction H (S.RestrictedPair C) :=
    MulAction.compHom (S.RestrictedPair C) (S.restrictedPairAction C)
  exact MulAction.orbitRel H (S.RestrictedPair C)

/-- The orbit quotient of the restricted pairs. -/
abbrev PairClass (C : Block) := Quotient (S.restrictedPairSetoid C)

/-- A selected representative of a pair class.  The final correspondence is
an existence result, so no canonical representative is claimed. -/
def PairClass.representative (C : Block) (p : S.PairClass C) :
    S.RestrictedPair C :=
  Quotient.out p

/-- The literal inertia quotient `N_H(M,lambda)/M` attached to a raw pair.
The Levi is an actual subgroup of `H`, its ambient normaliser is computed in
`H`, and its character is transported canonically from the semantic FMZ
carrier. -/
def RelativeWeylGroupAt (P : RawPair D) : Type := by
  let _normalizerAgreement :=
    S.normalizerLevi_eq_finiteNormalizer P.1
  letI : (finiteLeviInNormalizer D P.1).Normal := by
    unfold finiteLeviInNormalizer
    infer_instance
  exact characterInertia (finiteLeviInNormalizer D P.1)
      (finiteLeviNormalizerCharacter D P) ⧸
    baseInInertia (finiteLeviInNormalizer D P.1)
      (finiteLeviNormalizerCharacter D P)

instance relativeWeylGroupAtGroup (P : RawPair D) :
    Group (S.RelativeWeylGroupAt P) := by
  unfold RelativeWeylGroupAt
  letI : (finiteLeviInNormalizer D P.1).Normal := by
    unfold finiteLeviInNormalizer
    infer_instance
  infer_instance

instance relativeWeylGroupAtFintype (P : RawPair D) :
    Fintype (S.RelativeWeylGroupAt P) := by
  unfold RelativeWeylGroupAt
  letI : (finiteLeviInNormalizer D P.1).Normal := by
    unfold finiteLeviInNormalizer
    infer_instance
  classical
  exact Fintype.ofFinite _

/-- The relative Weyl group attached to the selected representative of an
orbit class. -/
abbrev RelativeWeylGroup (C : Block) (p : S.PairClass C) :=
  S.RelativeWeylGroupAt (PairClass.representative S C p).1

/-- The literal disjoint union of defect-zero ordinary characters in FMZ
equation (7.2).  Defect zero is the standard representation theoretic
predicate, not an application-supplied subset of an arbitrary character
carrier. -/
abbrev DefectZeroUnion (C : Block) :=
  Σ p : S.PairClass C,
    {chi : Irr ℂ (S.RelativeWeylGroup C p) //
      IsDefectZeroOrdinaryCharacter ell chi}

end PairClassSource

end

end ModularRep.PaperProofs.EvenFieldEJGCPairActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
