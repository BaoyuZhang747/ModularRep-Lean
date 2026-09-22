import ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation
import ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover
import ModularRep.BrauerReduction
import ModularRep.BrauerCharacterHomPullback
import ModularRep.WeightCharacterBridge

/-!
# The upward block-triple relation through a normal kernel

Martinez--Rizo--Rossi, Algebra & Number Theory 20 (2026), Lemma 3.14,
printed p. 345 (source label
`lem:Lifting isomorphisms from quotients`), lifts the block-isomorphism
relation from G/Z to G when Z and N are normal and Z is contained in N cap H.
The characters upstairs are the actual inflations. This direction does not
require Z to have order prime to the coefficient characteristic. The reverse
direction is deliberately absent.

The project does not yet define the projective-representation relation
`>=_b`. `BlockTripleSourceSemantics` therefore remains an explicit U
interface, now indexed by actual groups, subgroups, root conventions and
irreducible Brauer character functions. The named E2 source law only relates
these literal arguments. It has no bijection or final iBAW conclusion.

The separate K carrier join sends an actual raw character weight through a
surjection with two-group kernel. Its local character is transported along
the existing actual normalizer-quotient equivalence. The own-character
Brauer reductions then satisfy the literal local inflation equation.
The literal Sp-to-PSp application uses the fixed projection and its actual
two-group kernel. No new selected weight or local character is assumed.

Still U: identifying the full Definition 3.5 semidirect-product and
stabilizer triples with these arguments, authenticating its existing
`FLZSourceSemantics` against this relation, and supplying the global Brauer
inflation/block/action correspondence. This module does not manufacture a
`Definition35ForwardTransport` from freely selected relation predicates.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

open ModularRep.CharacterWeight
open ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation
open ModularRep.PaperProofs.OddTwoUniversalPrimeToTwoSelfCover

universe u

section TripleRelation

variable (p : ℕ) (k K : Type u)
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Literal arguments for `(G,N,theta) >=_b (H,N cap H,phi)`.
The U interpretation of the relation includes the character-triple
invariance and the block-isomorphism conditions; none is replaced by an
unrelated proposition. All coefficient fields are shared literally. -/
structure BlockTripleArguments where
  G : Type u
  [groupG : Group G]
  [finiteG : Finite G]
  N : Subgroup G
  H : Subgroup G
  [normalN : N.Normal]
  iotaN : PrimeRegularRootEmbedding p k K N
  iotaM : PrimeRegularRootEmbedding p k K ↥(N ⊓ H)
  theta : IBr iotaN
  phi : IBr iotaM

attribute [instance] BlockTripleArguments.groupG
  BlockTripleArguments.finiteG BlockTripleArguments.normalN

/-- Explicit U semantics for the standard modular block-triple relation
on the actual arguments above. No axiom or source instance is declared. -/
structure BlockTripleSourceSemantics where
  blockIsomorphic : BlockTripleArguments p k K → Prop

variable {p k K}

namespace BlockTripleArguments

variable (T : BlockTripleArguments p k K)
variable (Z : Subgroup T.G) [Z.Normal]

/-- The actual restriction of the quotient projection to N cap H. -/
def localProjection : ↥(T.N ⊓ T.H) →*
    ↥(T.N.map (QuotientGroup.mk' Z) ⊓ T.H.map (QuotientGroup.mk' Z)) where
  toFun x := ⟨QuotientGroup.mk' Z x,
    ⟨⟨x, x.property.1, rfl⟩, ⟨x, x.property.2, rfl⟩⟩⟩
  map_one' := Subtype.ext (map_one (QuotientGroup.mk' Z))
  map_mul' x y := Subtype.ext (map_mul (QuotientGroup.mk' Z) (x : T.G) (y : T.G))

@[simp] theorem localProjection_coe (x : ↥(T.N ⊓ T.H)) :
    (T.localProjection Z x : T.G ⧸ Z) = QuotientGroup.mk' Z (x : T.G) := rfl

/-- The local quotient subgroup is exactly the image of the intersection,
not an independently selected local group. -/
theorem map_intersection (hZ : Z ≤ T.N ⊓ T.H) :
    (T.N ⊓ T.H).map (QuotientGroup.mk' Z) =
      T.N.map (QuotientGroup.mk' Z) ⊓ T.H.map (QuotientGroup.mk' Z) := by
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective Z)
  have hker : (QuotientGroup.mk' Z).ker ≤ T.N ⊓ T.H := by
    simpa only [QuotientGroup.ker_mk'] using hZ
  rw [Subgroup.comap_map_eq_self hker, Subgroup.comap_inf,
    Subgroup.comap_map_eq_self (hker.trans inf_le_left),
    Subgroup.comap_map_eq_self (hker.trans inf_le_right)]

/-- Downstairs irreducible characters whose literal inflations are the
fixed upstairs characters. Root compatibility along the actual quotient
restrictions authenticates representation inflation, in addition to the
pointwise character equations. Independent root conventions are not used.
-/
structure QuotientInflationData where
  iotaN : PrimeRegularRootEmbedding p k K (T.N.map (QuotientGroup.mk' Z))
  iotaM : PrimeRegularRootEmbedding p k K
    ↥(T.N.map (QuotientGroup.mk' Z) ⊓ T.H.map (QuotientGroup.mk' Z))
  theta : IBr iotaN
  phi : IBr iotaM
  theta_root_compatible : ∀ V : FDRep k (T.N.map (QuotientGroup.mk' Z)),
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaN T.iotaN
      ((QuotientGroup.mk' Z).subgroupMap T.N)
  phi_root_compatible : ∀ V : FDRep k
      ↥(T.N.map (QuotientGroup.mk' Z) ⊓ T.H.map (QuotientGroup.mk' Z)),
    Representation.BrauerRootLiftCompatibleAlong V.ρ iotaM T.iotaM
      (T.localProjection Z)
  theta_values : ∀ x : PrimeRegularElement (G := T.N) p,
    T.theta.1 x = theta.1
      (PrimeRegularElement.map ((QuotientGroup.mk' Z).subgroupMap T.N) x)
  phi_values : ∀ x : PrimeRegularElement (G := ↥(T.N ⊓ T.H)) p,
    T.phi.1 x = phi.1 (PrimeRegularElement.map (T.localProjection Z) x)

namespace QuotientInflationData

variable {T Z}

/-- The lower arguments are constructed using the quotient and subgroup
images. No alternative target triple is stored in the source data. -/
def downstairs (D : T.QuotientInflationData Z) : BlockTripleArguments p k K where
  G := T.G ⧸ Z
  N := T.N.map (QuotientGroup.mk' Z)
  H := T.H.map (QuotientGroup.mk' Z)
  normalN := T.normalN.map (QuotientGroup.mk' Z)
    (QuotientGroup.mk'_surjective Z)
  iotaN := D.iotaN
  iotaM := D.iotaM
  theta := D.theta
  phi := D.phi

theorem theta_inflation (D : T.QuotientInflationData Z) :
    T.theta.1 = pullbackPrimeRegularClassFunction
      ((QuotientGroup.mk' Z).subgroupMap T.N) D.theta.1 := by
  ext x
  exact D.theta_values x

theorem phi_inflation (D : T.QuotientInflationData Z) :
    T.phi.1 = pullbackPrimeRegularClassFunction
      (T.localProjection Z) D.phi.1 := by
  ext x
  exact D.phi_values x

end QuotientInflationData
end BlockTripleArguments

/-- Exact relation-only E2 source: MRR's quotient-to-inflation lemma.
Its hypotheses use arbitrary normal Z contained in N cap H. In particular
there is no prime-to-p hypothesis and no converse field. -/
structure MRRLemma314Source (S : BlockTripleSourceSemantics p k K) : Prop where
  prime : p.Prime
  quotient_to_inflation : ∀ (T : BlockTripleArguments p k K)
      (Z : Subgroup T.G) [Z.Normal], Z ≤ T.N ⊓ T.H →
      ∀ D : T.QuotientInflationData Z,
        S.blockIsomorphic D.downstairs → S.blockIsomorphic T

/-- Apply the published upward relation law to the same fixed character
pair and its actual quotient data. It does not construct an orbit witness. -/
theorem blockIsomorphic_of_quotient
    {S : BlockTripleSourceSemantics p k K} (source : MRRLemma314Source S)
    (T : BlockTripleArguments p k K) (Z : Subgroup T.G) [Z.Normal]
    (hZ : Z ≤ T.N ⊓ T.H) (D : T.QuotientInflationData Z)
    (h : S.blockIsomorphic D.downstairs) : S.blockIsomorphic T :=
  source.quotient_to_inflation T Z hZ D h

end TripleRelation

section ActualPairs

variable {K G H : Type u} [Field K] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]
variable (f : G →* H) (hf : Function.Surjective f)
variable (hkernel : IsPGroup 2 f.ker) (W : CharacterWeight 2 K G)

include hkernel in
/-- Every actual two-weight contains the normal two-kernel. -/
theorem kernel_le_selected : f.ker ≤ W.subgroup :=
  (normal_pSubgroup_le_pCore 2 f.ker hkernel).trans
    (pCore_le_of_isRadicalSubgroup W.prime W.subgroup W.radical)

/-- The existing quotient equivalence, with the kernel inclusion derived
from the selected raw weight's own radicality. -/
def selectedLocalQuotientEquiv :
    NormalizerQuotient W.subgroup ≃* NormalizerQuotient (W.subgroup.map f) :=
  normalizerQuotientEquivOfSurjectiveOfKerLE f hf W.subgroup
    (kernel_le_selected f hkernel W)

@[simp] theorem selectedLocalQuotientEquiv_mk
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    selectedLocalQuotientEquiv f hf hkernel W (QuotientGroup.mk x) =
      QuotientGroup.mk (normalizerMap f W.subgroup x) := rfl

/-- The actual quotient raw pair. Its local ordinary character is the
transport of the selected pair's own character, with no uniqueness premise.
This construction therefore also retains a particular character in a
multi-character family. -/
def quotientPair : CharacterWeight 2 K H where
  prime := W.prime
  subgroup := W.subgroup.map f
  radical := (isRadicalSubgroup_iff_map_surjective_of_ker_le f hf W.subgroup
    (kernel_le_selected f hkernel W) hkernel).mp W.radical
  localCharacter := OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
    (selectedLocalQuotientEquiv f hf hkernel W)
  defectZero := W.defectZero.mapEquiv (selectedLocalQuotientEquiv f hf hkernel W)

@[simp] theorem quotientPair_subgroup :
    (quotientPair f hf hkernel W).subgroup = W.subgroup.map f := rfl

/-- The exact ordinary-character equation through the actual local map. -/
theorem quotientPair_localCharacter (x : NormalizerQuotient W.subgroup) :
    (quotientPair f hf hkernel W).localCharacter
        (selectedLocalQuotientEquiv f hf hkernel W x) =
      W.localCharacter x := by
  change W.localCharacter
    ((selectedLocalQuotientEquiv f hf hkernel W).symm
      (selectedLocalQuotientEquiv f hf hkernel W x)) = _
  rw [MulEquiv.symm_apply_apply]

/-- Actual reductions of the two own local characters force the exact
normalizer Brauer-inflation equation required by the source relation.
The existence of such compatible reductions remains standard source input.
This theorem concerns character functions only, with no block conclusion. -/
theorem ownLocalReduction_inflation
    {k : Type u} [Field k] [CharP k 2] [IsAlgClosed k]
    (iotaUp : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer (W.subgroup : Set G)))
    (iotaDown : PrimeRegularRootEmbedding 2 k K
      (Subgroup.normalizer ((W.subgroup.map f : Subgroup H) : Set H)))
    (phiUp : IBr iotaUp) (phiDown : IBr iotaDown)
    (hUp : NormalizerInflatedReduction W.subgroup W.localCharacter iotaUp phiUp)
    (hDown : NormalizerInflatedReduction (quotientPair f hf hkernel W).subgroup
      (quotientPair f hf hkernel W).localCharacter iotaDown phiDown) :
    phiUp.1 = pullbackPrimeRegularClassFunction
      (normalizerMap f W.subgroup) phiDown.1 := by
  ext x
  change phiUp.1 x = phiDown.1
    (PrimeRegularElement.map (normalizerMap f W.subgroup) x)
  calc
    phiUp.1 x = W.localCharacter (QuotientGroup.mk x.1) := (hUp x).symm
    _ = (quotientPair f hf hkernel W).localCharacter
        (selectedLocalQuotientEquiv f hf hkernel W (QuotientGroup.mk x.1)) :=
      (quotientPair_localCharacter f hf hkernel W (QuotientGroup.mk x.1)).symm
    _ = phiDown.1 (PrimeRegularElement.map (normalizerMap f W.subgroup) x) := by
      rw [selectedLocalQuotientEquiv_mk]
      exact hDown (PrimeRegularElement.map (normalizerMap f W.subgroup) x)

end ActualPairs

section LiteralSp

variable {n : ℕ} {F K : Type u} [Field F] [Finite F] [Field K] [CharZero K]

/-- The actual central two-kernel lies in the same selected radical pair.
This supplies the base-group kernel containment needed in the upward
triple passage; its embedding into the full semidirect triple is separate.
-/
theorem spCenter_le_selected (cover : OddSymplecticFullCoverSource n F)
    (W : CharacterWeight 2 K (LiteralSp n F)) :
    Subgroup.center (LiteralSp n F) ≤ W.subgroup := by
  simpa only [literalProjection, QuotientGroup.ker_mk'] using
    kernel_le_selected (literalProjection n F) cover.projection_twoKernel W

/-- K specialization to the same selected raw pair on literal Sp. The
projective pair is computed from the fixed central projection. The supplied
full-cover packet is used only for its exact order-two kernel fact here. -/
def spQuotientPair (cover : OddSymplecticFullCoverSource n F)
    (W : CharacterWeight 2 K (LiteralSp n F)) :
    CharacterWeight 2 K (LiteralPSp n F) :=
  quotientPair (literalProjection n F) cover.fullCover.1.1
    cover.projection_twoKernel W

@[simp] theorem spQuotientPair_subgroup (cover : OddSymplecticFullCoverSource n F)
    (W : CharacterWeight 2 K (LiteralSp n F)) :
    (spQuotientPair cover W).subgroup =
      W.subgroup.map (QuotientGroup.mk' (Subgroup.center (LiteralSp n F))) := rfl

end LiteralSp

end ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
