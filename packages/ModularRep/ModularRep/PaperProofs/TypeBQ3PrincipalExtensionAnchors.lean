import ModularRep.PaperProofs.TypeBQ3PrincipalExtensionApplication
import ModularRep.PaperProofs.TypeBQ3PrincipalWeightInflation

/-! The two extension characters retain the original global and local values
along the actual embeddings and the displayed inflation map. -/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBQ3PrincipalExtensionAnchors

open ModularRep CharacterWeight
open TypeBQ3PrincipalExtensionApplication TypeBQ3PrincipalWeightInflation
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient
open SporadicFi24P3Definition44NamedCarrierActualNormalizerBase

variable {k K Y : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K] [Group Y] [Finite Y]

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T

variable {root : PrimeRegularRootEmbedding 2 k K Y} {phi : IBr root}
  {W : CharacterWeight 2 K Y} {reduction : CanonicalRawReduction root W}
  {hcenter : Subgroup.center Y = ⊥}
  (data : MatchedExtensionData root phi W reduction hcenter)

/-- Restriction uses the literal inner embedding of the original global group. -/
theorem global_value (x : PrimeRegularElement (G := Y) 2) :
    data.globalExtension.val.val
      (PrimeRegularElement.map (innerEmbedding root phi) x) = phi.val x := by
  let e := actualBaseEquiv root phi hcenter
  have value := congrArg
    (fun f : PrimeRegularClassFunction K (actualBase root phi) 2 =>
      f (PrimeRegularElement.map e.toMonoidHom x)) data.globalExtension.property
  have roundtrip : PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map e.toMonoidHom x) = x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  change data.globalExtension.val.val
    (PrimeRegularElement.map (innerEmbedding root phi) x) =
      phi.val (PrimeRegularElement.map e.symm.toMonoidHom
        (PrimeRegularElement.map e.toMonoidHom x)) at value
  exact value.trans (congrArg phi.val roundtrip)

/-- Restriction gives the ordinary quotient value of this same raw weight. -/
theorem local_value
    (n : PrimeRegularElement (G := Subgroup.normalizer (W.subgroup : Set Y)) 2) :
    data.localExtension.val.val
      (PrimeRegularElement.map (ModularRep.normalizerMap (innerEmbedding root phi) W.subgroup) n) =
      W.localCharacter (QuotientGroup.mk n.val) := by
  let e := normalizerBaseEquiv (innerEmbedding root phi)
    (innerEmbedding_injective root phi hcenter) W.subgroup
  have value := congrArg
    (fun f : PrimeRegularClassFunction K
      (embeddedLocalBase (innerEmbedding root phi) W.subgroup) 2 =>
        f (PrimeRegularElement.map e.toMonoidHom n)) data.localExtension.property
  have roundtrip : PrimeRegularElement.map e.symm.toMonoidHom
      (PrimeRegularElement.map e.toMonoidHom n) = n := by
    apply Subtype.ext
    exact e.symm_apply_apply n.val
  change data.localExtension.val.val
    (PrimeRegularElement.map (ModularRep.normalizerMap (innerEmbedding root phi) W.subgroup) n) =
      reduction.localBrauer.val (PrimeRegularElement.map e.symm.toMonoidHom
        (PrimeRegularElement.map e.toMonoidHom n)) at value
  exact (value.trans (congrArg reduction.localBrauer.val roundtrip)).trans
    (reduction.localBrauer_reduction n).symm

variable {X : Type} [Group X] [Finite X]

/-- The target radical equality changes only the codomain of the fixed map. -/
def normalizerImageHom (q : X →* TypeBQ3TripleCoverCarrier.G3)
    {Q : Subgroup X} {R : Subgroup TypeBQ3TripleCoverCarrier.G3}
    (hQ : Q.map q = R) :
    Subgroup.normalizer (Q : Set X) →* Subgroup.normalizer (R : Set TypeBQ3TripleCoverCarrier.G3) where
  toFun := normalizerImage q hQ
  map_one' := Subtype.ext q.map_one
  map_mul' x y := Subtype.ext (q.map_mul x.val y.val)

/-- The exact map used to evaluate the local extension on upstairs elements. -/
def inflatedLocalMap
    (q : X →* TypeBQ3TripleCoverCarrier.G3)
    (r : PrimeRegularRootEmbedding 2 k K TypeBQ3TripleCoverCarrier.G3)
    (psi : IBr r) (U : CharacterWeight 2 K X)
    (V : CharacterWeight 2 K TypeBQ3TripleCoverCarrier.G3)
    (hQ : U.subgroup.map q = V.subgroup) :
    Subgroup.normalizer (U.subgroup : Set X) →*
      embeddedNormalizer (innerEmbedding r psi) V.subgroup :=
  (ModularRep.normalizerMap (innerEmbedding r psi) V.subgroup).comp (normalizerImageHom q hQ)

/-- The local equation is the original raw inflation equation on its own normalizer. -/
theorem local_value_inflated
    (q : X →* TypeBQ3TripleCoverCarrier.G3)
    (r : PrimeRegularRootEmbedding 2 k K TypeBQ3TripleCoverCarrier.G3)
    (psi : IBr r) (U : CharacterWeight 2 K X)
    (V : CharacterWeight 2 K TypeBQ3TripleCoverCarrier.G3)
    (hQ : U.subgroup.map q = V.subgroup)
    (values : ∀ n : Subgroup.normalizer (U.subgroup : Set X),
      U.localCharacter (QuotientGroup.mk n) =
        V.localCharacter (QuotientGroup.mk (normalizerImage q hQ n)))
    (R : CanonicalRawReduction r V)
    (center : Subgroup.center TypeBQ3TripleCoverCarrier.G3 = ⊥)
    (packet : MatchedExtensionData r psi V R center)
    (n : PrimeRegularElement (G := Subgroup.normalizer (U.subgroup : Set X)) 2) :
    packet.localExtension.val.val
      (PrimeRegularElement.map (inflatedLocalMap q r psi U V hQ) n) =
        U.localCharacter (QuotientGroup.mk n.val) := by
  calc
    _ = V.localCharacter (QuotientGroup.mk
        (PrimeRegularElement.map (normalizerImageHom q hQ) n).val) :=
      local_value packet (PrimeRegularElement.map (normalizerImageHom q hQ) n)
    _ = V.localCharacter (QuotientGroup.mk (normalizerImage q hQ n.val)) := rfl
    _ = U.localCharacter (QuotientGroup.mk n.val) := (values n.val).symm

end ModularRep.PaperProofs.TypeBQ3PrincipalExtensionAnchors


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
