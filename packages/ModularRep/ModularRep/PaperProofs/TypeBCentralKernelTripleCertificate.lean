import ModularRep.ModularProjectiveRepresentation
import ModularRep.IBrBlock
import ModularRep.BlockInduction
import ModularRep.BlockDefectGroup
import ModularRep.GroupAlgebraCentralBrauerMap
import ModularRep.PrimitiveBlockAutomorphism
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Literal modular block triples and the one-way quotient theorem

This file defines the output of Martínez--Rizo--Rossi, Theorem 3.1 and
Definition 3.4, with the central-scalar formulation of Lemma 3.3. A triple
witness uses actual projective operators, honest restrictions affording the
specified Brauer characters, and the tensor correspondence on EVERY
intermediate character fibre. Blocks are actual primitive central
idempotents; the block clause is the existing `BlockInducesTo` relation.

`Lemma314Certificate` is an E2 source interface with no declared inhabitant for
Lemma 3.14, author PDF pp. 12--13, arXiv:2311.05536. Its only result is the
upstairs literal witness, from the quotient literal witness and the displayed
inflation equations. The quotient kernel need only be normal and contained
in the intersection; centrality and its prime-power order belong to the
separate application. The reverse implication of Lemma 3.15 is NOT used.

The root conventions, splitting fields, block decompositions/catalogues,
and identification of these records with the published modular-system
definitions remain explicit E1/U source obligations. No BAW/iBAW predicate,
universal cover, arbitrary automorphism group, or unspecified triple relation
is accepted. In particular, this source does not assert the Type B target.
-/

noncomputable section

set_option autoImplicit false

open scoped MonoidAlgebra TensorProduct

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate

open ModularRep

universe u

variable {p : ℕ} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

local instance finiteGroupFintype (H : Type u) [Group H] [Finite H] :
    Fintype H := Fintype.ofFinite H

/-- A literal group algebra block catalogue, with the allocation fixed to
the value of the primitive-idempotent subtype. -/
structure PhysicalBlocks (k H : Type u) [Field k] [IsAlgClosed k]
    [Group H] [Finite H] where
  blockFintype : Fintype (LiteralPrimitiveBlock k H)
  decomposition : letI := blockFintype
    BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k H => b.val)
  catalogue : letI := blockFintype
    BlockCentralCharacterCatalogue decomposition

/-- Actual Brauer functions and their physically allocated blocks. -/
structure CharacterData (p : ℕ) (k K H : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group H] [Finite H] where
  iota : PrimeRegularRootEmbedding p k K H
  injective : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota
  blocks : PhysicalBlocks k H

def CharacterData.block {H : Type u} [Group H] [Finite H]
    (D : CharacterData p k K H) (chi : IBr D.iota) : LiteralPrimitiveBlock k H := by
  letI := D.blocks.blockFintype
  exact FDRepSimpleClassKZero.irreducibleBrauerCharacterBlock
    D.iota D.injective D.blocks.decomposition chi

/-- Restriction support is a nonnegative finite expansion of actual Brauer
functions along the specified group homomorphism. -/
def OccursAlong {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    (f : B →* A) (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (chi : IBr iotaA) (theta : IBr iotaB) : Prop :=
  ∃ multiplicity : IBr iotaB →₀ ℕ,
    multiplicity theta ≠ 0 ∧
      ∀ x : PrimeRegularElement (G := B) p,
        chi.val (PrimeRegularElement.map f x) =
          multiplicity.sum (fun eta n => (n : K) * eta.val x)

variable {T : Type u} [Group T] [Finite T]

/-- The actual intersection, viewed inside the second triple's ambient group. -/
abbrev localBase (N U : Subgroup T) : Subgroup U := N.comap U.subtype

def localBaseEquivIntersection (N U : Subgroup T) : localBase N U ≃* ↥(N ⊓ U) where
  toFun x := ⟨x.val.val, x.property, x.val.property⟩
  invFun x := ⟨⟨x.val, x.property.2⟩, x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

abbrev localIntermediate (U J : Subgroup T) : Subgroup J := U.comap J.subtype

def localToU (U J : Subgroup T) : localIntermediate U J →* U where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def baseToLocal (N U J : Subgroup T) (hNJ : N ≤ J) :
    localBase N U →* localIntermediate U J where
  toFun x := ⟨⟨x.val.val, hNJ x.property⟩, x.val.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- All root choices agree with one ambient convention on their actual
root domains. No equality of the extended lift outside these domains is used. -/
structure TripleData (N U : Subgroup T) where
  ambientRoot : PrimeRegularRootEmbedding p k K T
  base : CharacterData p k K N
  localData : CharacterData p k K (localBase N U)
  intermediate : ∀ J : Subgroup T, N ≤ J → CharacterData p k K J
  localIntermediateData : ∀ J : Subgroup T, N ≤ J →
    CharacterData p k K (localIntermediate U J)
  baseRoots : ∀ z : rootsOfUnity (primeRegularExponent p N) k,
    base.iota.lift ((z : kˣ) : k) = ambientRoot.lift ((z : kˣ) : k)
  localRoots : ∀ z : rootsOfUnity (primeRegularExponent p (localBase N U)) k,
    localData.iota.lift ((z : kˣ) : k) = ambientRoot.lift ((z : kˣ) : k)
  intermediateRoots : ∀ (J : Subgroup T) (hNJ : N ≤ J)
      (z : rootsOfUnity (primeRegularExponent p J) k),
    (intermediate J hNJ).iota.lift ((z : kˣ) : k) = ambientRoot.lift ((z : kˣ) : k)
  localIntermediateRoots : ∀ (J : Subgroup T) (hNJ : N ≤ J)
      (z : rootsOfUnity (primeRegularExponent p (localIntermediate U J)) k),
    (localIntermediateData J hNJ).iota.lift ((z : kˣ) : k) = ambientRoot.lift ((z : kˣ) : k)

def GlobalFibre {N U : Subgroup T} (D : TripleData (p := p) (k := k) (K := K) N U)
    (theta : IBr D.base.iota) (J : Subgroup T) (hNJ : N ≤ J) :=
  {chi : IBr (D.intermediate J hNJ).iota //
    OccursAlong (Subgroup.inclusion hNJ) (D.intermediate J hNJ).iota
      D.base.iota chi theta}

def LocalFibre {N U : Subgroup T} (D : TripleData (p := p) (k := k) (K := K) N U)
    (phi : IBr D.localData.iota) (J : Subgroup T) (hNJ : N ≤ J) :=
  {chi : IBr (D.localIntermediateData J hNJ).iota //
    OccursAlong (baseToLocal N U J hNJ) (D.localIntermediateData J hNJ).iota
      D.localData.iota chi phi}

/-- A positive-dimensional matrix model of a projective representation.
Choosing a basis changes no character or source scope. -/
structure ProjectiveData (k H : Type u) [Field k] [Group H] where
  dimensionPred : ℕ
  projective : ModularProjectiveRepresentation k H (Fin (dimensionPred + 1) → k)

abbrev ProjectiveData.Space {H : Type u} [Group H] (P : ProjectiveData k H) :=
  Fin (P.dimensionPred + 1) → k

/-- Association is the literal restriction of the projective operators to
an irreducible honest representation affording the given Brauer function.
The two factor-triviality equations retain the standard association convention. -/
structure Associated {A B : Type u} [Group A] [Group B] [Finite B]
    (f : B →* A) (iota : PrimeRegularRootEmbedding p k K B)
    (theta : IBr iota) (P : ProjectiveData k A) where
  restriction : Representation k B P.Space
  irreducible : Representation.IsIrreducible restriction
  operator_value : ∀ (b : B) (v : P.Space),
    restriction b v = P.projective.operator (f b) v
  character : Representation.brauerCharacterOfRootEmbedding restriction iota = theta.val
  multiplier_left : ∀ (b : B) (a : A), P.projective.multiplier (f b) a = 1
  multiplier_right : ∀ (a : A) (b : B), P.projective.multiplier a (f b) = 1

/-- Irreducibility of actual projective operators, stated by their invariant
subspaces. It is independent of any desired character correspondence. -/
def ProjectiveIrreducible {A : Type u} [Group A] (P : ProjectiveData k A) : Prop :=
  ∀ W : Submodule k P.Space,
    (∀ (a : A) (v : P.Space), v ∈ W → P.projective.operator a v ∈ W) →
      W = ⊥ ∨ W = ⊤

def intermediateQuotientToAmbient (N J : Subgroup T) [N.Normal] :
    J ⧸ N.comap J.subtype →* T ⧸ N :=
  QuotientGroup.map (N.comap J.subtype) N J.subtype le_rfl

/-- The two characters in one intermediate correspondence are afforded by
the SAME inverse-factor projective representation, tensored with the fixed
associated representations. The honest tensor operators are specified on
every pure tensor; there is no abstract tensor-character relation. -/
def TensorRelated {N U : Subgroup T} [N.Normal]
    (D : TripleData (p := p) (k := k) (K := K) N U)
    (P : ProjectiveData k T) (P' : ProjectiveData k U)
    (alpha : NormalizedFactorSet k (T ⧸ N))
    (J : Subgroup T) (hNJ : N ≤ J)
    (chi : IBr (D.intermediate J hNJ).iota)
    (chi' : IBr (D.localIntermediateData J hNJ).iota) : Prop :=
  ∃ Q : ProjectiveData k (J ⧸ N.comap J.subtype),
    ProjectiveIrreducible Q ∧
    (∀ a b, Q.projective.multiplier a b =
      (alpha (intermediateQuotientToAmbient N J a)
        (intermediateQuotientToAmbient N J b))⁻¹) ∧
    ∃ rho : Representation k J (Q.Space ⊗[k] P.Space),
    ∃ rho' : Representation k (localIntermediate U J) (Q.Space ⊗[k] P'.Space),
      Representation.IsIrreducible rho ∧ Representation.IsIrreducible rho' ∧
      (∀ (j : J) (w : Q.Space) (v : P.Space),
        rho j (w ⊗ₜ[k] v) =
          Q.projective.operator (QuotientGroup.mk j) w ⊗ₜ[k]
            P.projective.operator (j : T) v) ∧
      (∀ (j : localIntermediate U J) (w : Q.Space) (v : P'.Space),
        rho' j (w ⊗ₜ[k] v) =
          Q.projective.operator (QuotientGroup.mk (j : J)) w ⊗ₜ[k]
            P'.projective.operator (localToU U J j) v) ∧
      Representation.brauerCharacterOfRootEmbedding rho
        (D.intermediate J hNJ).iota = chi.val ∧
      Representation.brauerCharacterOfRootEmbedding rho'
        (D.localIntermediateData J hNJ).iota = chi'.val

def primitiveInCenter {H : Type u} [Group H]
    (b : LiteralPrimitiveBlock k H) : GroupAlgebraCenter k H :=
  ⟨b.val, by
    rw [Subalgebra.mem_center_iff]
    intro x
    exact (b.property.central.comm x).eq.symm⟩

def IntermediateBlockInduces {N U : Subgroup T}
    (D : TripleData (p := p) (k := k) (K := K) N U)
    (J : Subgroup T) (hNJ : N ≤ J)
    (chi : IBr (D.intermediate J hNJ).iota)
    (chi' : IBr (D.localIntermediateData J hNJ).iota) : Prop := by
  letI := (D.intermediate J hNJ).blocks.blockFintype
  letI := (D.localIntermediateData J hNJ).blocks.blockFintype
  exact BlockInducesTo (localIntermediate U J)
    (D.localIntermediateData J hNJ).blocks.catalogue
    (D.intermediate J hNJ).blocks.catalogue
    ((D.localIntermediateData J hNJ).block chi')
    ((D.intermediate J hNJ).block chi)

/-- Independently fixed literal output of MRR Definition 3.4. The all-fibre
tensor clause is the strong isomorphism of Theorem 3.1; the scalar clause is
Lemma 3.3; the final two fields are precisely the extra block conditions.
The defect group is in the actual local base, and its centralizer is taken
in the actual ambient T after the literal subgroup inclusion. -/
structure BlockTripleWitness {N U : Subgroup T} [N.Normal]
    (D : TripleData (p := p) (k := k) (K := K) N U)
    (theta : IBr D.base.iota) (phi : IBr D.localData.iota) where
  product : N ⊔ U = ⊤
  theta_invariant : ∀ t : T,
    IrreducibleBrauerCharacter.twist D.base.iota theta (MulAut.conjNormal (H := N) t) = theta
  phi_invariant : ∀ u : U,
    IrreducibleBrauerCharacter.twist D.localData.iota phi
      (MulAut.conjNormal (H := localBase N U) u) = phi
  globalProjective : ProjectiveData k T
  localProjective : ProjectiveData k U
  globalAssociation : Associated N.subtype D.base.iota theta globalProjective
  localAssociation : Associated (localBase N U).subtype D.localData.iota phi localProjective
  factor : NormalizedFactorSet k (T ⧸ N)
  globalFactor : ∀ g h : T,
    globalProjective.projective.multiplier g h =
      factor (QuotientGroup.mk g) (QuotientGroup.mk h)
  localFactor : ∀ g h : U,
    localProjective.projective.multiplier g h =
      factor (QuotientGroup.mk (g : T)) (QuotientGroup.mk (h : T))
  centralizer_le : Subgroup.centralizer (N : Set T) ≤ U
  same_scalar : ∀ x : Subgroup.centralizer (N : Set T), ∃ a : kˣ,
    globalProjective.projective.operator (x : T) = scalarLinearAut a ∧
    localProjective.projective.operator ⟨x.val, centralizer_le x.property⟩ =
      scalarLinearAut a
  sigma : ∀ (J : Subgroup T) (hNJ : N ≤ J),
    GlobalFibre D theta J hNJ ≃ LocalFibre D phi J hNJ
  tensor : ∀ (J : Subgroup T) (hNJ : N ≤ J) (chi : GlobalFibre D theta J hNJ),
    TensorRelated D globalProjective localProjective factor J hNJ
      chi.val (sigma J hNJ chi).val
  tensor_unique : ∀ (J : Subgroup T) (hNJ : N ≤ J)
      (chi : GlobalFibre D theta J hNJ) (chi' : LocalFibre D phi J hNJ),
    TensorRelated D globalProjective localProjective factor J hNJ chi.val chi'.val →
      sigma J hNJ chi = chi'
  defect : Subgroup (localBase N U)
  defect_maximal : IsMaximalNonzeroPSubgroup p
    (fun Q : Subgroup (localBase N U) =>
      centralBrauerRestriction Q (primitiveInCenter (D.localData.block phi)) ≠ 0) defect
  defect_centralizer_le :
    Subgroup.centralizer
      ((defect.map (U.subtype.comp (localBase N U).subtype)) : Set T) ≤ U
  block_induces : ∀ (J : Subgroup T) (hNJ : N ≤ J) (chi : GlobalFibre D theta J hNJ),
    IntermediateBlockInduces D J hNJ chi.val (sigma J hNJ chi).val

def quotientSubgroupMap (Z H : Subgroup T) [Z.Normal] :
    H →* H.map (QuotientGroup.mk' Z) where
  toFun x := ⟨QuotientGroup.mk x.val, x.val, x.property, rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

instance quotientBaseNormal (Z N : Subgroup T) [Z.Normal] [N.Normal] :
    (N.map (QuotientGroup.mk' Z)).Normal :=
  (inferInstance : N.Normal).map (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z)

def quotientLocalMap (Z N U : Subgroup T) [Z.Normal] :
    localBase N U →*
      localBase (N.map (QuotientGroup.mk' Z)) (U.map (QuotientGroup.mk' Z)) where
  toFun x := ⟨quotientSubgroupMap Z U x.val,
    x.val.val, x.property, rfl⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Exact one-way MRR Lemma 3.14, universally quantified independently of
the Type B application. The images in T/Z are the actual quotients of N and
U by Z because Z is contained in both. Inflation uses their canonical maps,
including the literal intersection map. No principal-block identification
or arbitrary global block bijection is part of this source.

This is a certificate TYPE, not an axiom or an inhabitant. The published
source-to-Lean identification of the complete output still requires audit. -/
structure Lemma314Certificate (p : ℕ) (k K : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] where
  inflate : ∀ (T : Type u) [Group T] [Finite T]
      (N U Z : Subgroup T) [N.Normal] [Z.Normal]
      (_hZN : Z ≤ N) (_hZU : Z ≤ U)
      (D : TripleData (p := p) (k := k) (K := K) N U)
      (Dbar : TripleData (p := p) (k := k) (K := K)
        (N.map (QuotientGroup.mk' Z)) (U.map (QuotientGroup.mk' Z)))
      (theta : IBr D.base.iota) (phi : IBr D.localData.iota)
      (thetaBar : IBr Dbar.base.iota) (phiBar : IBr Dbar.localData.iota),
    (∀ z : rootsOfUnity (primeRegularExponent p (T ⧸ Z)) k,
      Dbar.ambientRoot.lift ((z : kˣ) : k) = D.ambientRoot.lift ((z : kˣ) : k)) →
    (∀ x : PrimeRegularElement (G := N) p,
      theta.val x = thetaBar.val (PrimeRegularElement.map (quotientSubgroupMap Z N) x)) →
    (∀ x : PrimeRegularElement (G := localBase N U) p,
      phi.val x = phiBar.val (PrimeRegularElement.map (quotientLocalMap Z N U) x)) →
    Nonempty (BlockTripleWitness Dbar thetaBar phiBar) →
    Nonempty (BlockTripleWitness D theta phi)

end ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
