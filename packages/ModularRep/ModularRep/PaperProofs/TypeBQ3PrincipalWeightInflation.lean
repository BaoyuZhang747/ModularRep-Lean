import ModularRep.PaperProofs.TypeBRankThreePrincipalCountBinding
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSurjectiveRoot

/-!
# Principal weight inflation along the literal central odd-kernel map

The local graph records the radical image and equality of ordinary values
on the actual normalizer quotients. FLZ Lemma 2.3 supplies its complete
principal class interpretation. Its existence and uniqueness assertions
remain explicit published E2/U inputs, with the same specified block
selectors and canonical reductions. No inhabitant is constructed here.

The equivalence is selected from that graph. Its automorphism naturality
is derived from the commuting group square and graph uniqueness. The
ordinary coefficient field requires only the displayed finite roots.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3PrincipalWeightInflation

open ModularRep CharacterWeight
open TypeBRankThreePrincipalCountBinding
open TypeBCentralKernelBlockSource TypeBCentralKernelPrincipalStability
open TypeBCentralKernelInertia
open SporadicFi24P3Definition44NamedCarrierCentralPrimeToRadicalClasses
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierQuotientBlockAlgebra
open SporadicFi24P3Definition44NamedCarrierSurjectiveRoot

variable {k K X : Type} [Field k] [Field K] [CharZero K]
  [CharP k 2] [IsAlgClosed k] [Group X] [Finite X]

local instance groupFintype (Y : Type) [Group Y] [Finite Y] : Fintype Y :=
  Fintype.ofFinite Y

abbrev CoverWeightSource (X : Type) [Group X] [Finite X] :=
  LocalBlockInductionSource (p := 2) (k := k) (K := K)
    (G := X) (Block := LiteralPrimitiveBlock k X)

abbrev CoverWeight (SX : CoverWeightSource (k := k) (K := K) X)
    (bX : LiteralPrimitiveBlock k X) := SX.Fibre bX

/-- The normalizer map with only its target subgroup rewritten. -/
def normalizerImage (q : X →* G (ZMod 3))
    {Q : Subgroup X} {R : Subgroup (G (ZMod 3))}
    (hQ : Q.map q = R) (n : Subgroup.normalizer (Q : Set X)) :
    Subgroup.normalizer (R : Set (G (ZMod 3))) :=
  ⟨q n.val, by
    have hn := (normalizerMap q Q n).property
    change q n.val ∈ Subgroup.normalizer (Q.map q : Set (G (ZMod 3))) at hn
    rw [hQ] at hn
    exact hn⟩

@[simp]
theorem normalizerImage_val (q : X →* G (ZMod 3))
    {Q : Subgroup X} {R : Subgroup (G (ZMod 3))}
    (hQ : Q.map q = R) (n : Subgroup.normalizer (Q : Set X)) :
    (normalizerImage q hQ n).val = q n.val := rfl

/-- Literal ordinary inflation, evaluated on every normalizer representative.
This is the value characterization of the induced local quotient map;
the central odd kernel has not been removed from the upstairs radical. -/
def RawInflates (q : X →* G (ZMod 3))
    (W : CharacterWeight 2 K X) (V : CharacterWeight 2 K (G (ZMod 3))) : Prop :=
  ∃ hQ : W.subgroup.map q = V.subgroup,
    ∀ n : Subgroup.normalizer (W.subgroup : Set X),
      W.localCharacter (QuotientGroup.mk n) =
        V.localCharacter (QuotientGroup.mk (normalizerImage q hQ n))

def classOf {Y : Type} [Group Y] [Finite Y] (W : CharacterWeight 2 K Y) :
    CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := Y) :=
  Quotient.mk'' (Quotient.mk'' W)

/-- The graph on the actual ordinary weight conjugacy classes. -/
def ClassInflates (q : X →* G (ZMod 3))
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X))
    (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G (ZMod 3))) : Prop :=
  ∃ (W : CharacterWeight 2 K X) (V : CharacterWeight 2 K (G (ZMod 3))),
    classOf W = w ∧ classOf V = v ∧ RawInflates q W V

/-- Ordinary inflation commutes with every literal matched automorphism pair. -/
theorem rawInflates_rightTwist
    (q : X →* G (ZMod 3))
    (alpha : MulAut X) (beta : MulAut (G (ZMod 3)))
    (square : ∀ x, q (alpha x) = beta (q x))
    (W : CharacterWeight 2 K X) (V : CharacterWeight 2 K (G (ZMod 3)))
    (h : RawInflates q W V) :
    RawInflates q (W.rightTwist alpha) (V.rightTwist beta) := by
  obtain ⟨hQ, hvalues⟩ := h
  have hQ' : (W.subgroup.comap alpha.toMonoidHom).map q =
      V.subgroup.comap beta.toMonoidHom :=
    (subgroup_map_comap_of_square q alpha beta square W.subgroup).trans
      (congrArg (fun R => R.comap beta.toMonoidHom) hQ)
  refine ⟨hQ', ?_⟩
  intro n
  have upperStep :
      (W.rightTwist alpha).localCharacter.val (QuotientGroup.mk n) =
        W.localCharacter.val (QuotientGroup.mk (rightNormalizerEquiv alpha W.subgroup n)) :=
    congrArg W.localCharacter.val (rightNormalizerQuotientEquiv_mk alpha W.subgroup n)
  have lowerStep :
      (V.rightTwist beta).localCharacter.val
          (QuotientGroup.mk (normalizerImage q hQ' n)) =
        V.localCharacter.val (QuotientGroup.mk
          (rightNormalizerEquiv beta V.subgroup (normalizerImage q hQ' n))) :=
    congrArg V.localCharacter.val
      (rightNormalizerQuotientEquiv_mk beta V.subgroup (normalizerImage q hQ' n))
  have imageSquare :
      normalizerImage q hQ (rightNormalizerEquiv alpha W.subgroup n) =
        rightNormalizerEquiv beta V.subgroup (normalizerImage q hQ' n) := by
    apply Subtype.ext
    exact square n.val
  exact upperStep.trans ((hvalues (rightNormalizerEquiv alpha W.subgroup n)).trans
    ((congrArg (fun z : Subgroup.normalizer (V.subgroup : Set (G (ZMod 3))) =>
      V.localCharacter.val (QuotientGroup.mk z)) imageSquare).trans lowerStep.symm))

theorem classInflates_op_smul
    (q : X →* G (ZMod 3))
    (alpha : (MulAut X)ᵐᵒᵖ) (beta : (MulAut (G (ZMod 3)))ᵐᵒᵖ)
    (square : ∀ x, q (alpha.unop x) = beta.unop (q x))
    (w : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := X))
    (v : CharacterWeight.ConjugacyClass (p := 2) (K := K) (G := G (ZMod 3)))
    (h : ClassInflates q w v) : ClassInflates q (alpha • w) (beta • v) := by
  obtain ⟨W, V, rfl, rfl, h⟩ := h
  exact ⟨W.rightTwist alpha.unop, V.rightTwist beta.unop, rfl, rfl,
    rawInflates_rightTwist q alpha.unop beta.unop square W V h⟩

variable (SX : CoverWeightSource (k := k) (K := K) X)
    (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)

def coverDecomposition :
    letI := SX.operations.ambientBlockData.fintypeBlock
    BlockIdempotentDecomposition (fun b : LiteralPrimitiveBlock k X => b.val) := by
  letI := SX.operations.ambientBlockData.fintypeBlock
  have values : SX.operations.ambientBlockData.blockIdempotent =
      (fun b : LiteralPrimitiveBlock k X => b.val) := funext literalX
  rw [← values]
  exact SX.operations.ambientBlockData.blocks

def coverWeightStep (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
    (alpha : (MulAut X)ᵐᵒᵖ) (w : CoverWeight SX bX) : CoverWeight SX bX := by
  letI := SX.operations.ambientBlockData.fintypeBlock
  refine ⟨alpha • w.val, ?_⟩
  change SX.weightBlock (alpha • w.val) = bX
  exact (SX.weightBlock_transport alpha w.val).trans
    ((congrArg (fun c : LiteralPrimitiveBlock k X => alpha • c) w.property).trans
      (principal_op_smul_eq (coverDecomposition SX literalX) bX hbX alpha))

@[simp]
theorem coverWeightStep_val (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
    (alpha : (MulAut X)ᵐᵒᵖ) (w : CoverWeight SX bX) :
    (coverWeightStep SX literalX bX hbX alpha w).val = alpha • w.val := rfl

/-- Exact published principal class transport, with explicit specified
interpretation. The graph fields are the FLZ Lemma 2.3 class conclusions,
including complete principal support; they are E2/U source obligations.
The supplied reductions are the precise local use of a modular-system
realization, so this record adds no independent unused modular system. -/
structure FLZ23Source
    (q : X →* G (ZMod 3)) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center X) (hprimeTo : ¬ 2 ∣ Nat.card q.ker)
    (SX : CoverWeightSource (k := k) (K := K) X)
    (literalX : ∀ c, SX.operations.ambientBlockData.blockIdempotent c = c.val)
    (S : OmegaWeightSource (k := k) (K := K) (ZMod 3))
    (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
    (rootX : PrimeRegularRootEmbedding 2 k K X)
    (bX : LiteralPrimitiveBlock k X) (hbX : IsPrincipal bX)
    (b : LiteralPrimitiveBlock k (G (ZMod 3))) (hb : IsPrincipal b)
    (blockImage : algebraMapOf q bX.val = b.val) where
  finiteRoots : HasEnoughRootsOfUnity K (Nat.card X)
  upperReduction : ∀ W : CharacterWeight 2 K X,
    SX.operations.rawWeightBlock W = bX → CanonicalRawReduction rootX W
  lowerReduction : ∀ V : CharacterWeight 2 K (G (ZMod 3)),
    S.operations.rawWeightBlock V = b → CanonicalRawReduction (surjectiveRoot rootX q hq) V
  upperCompatibility : ∀ (W : CharacterWeight 2 K X)
      (hsupp : SX.operations.rawWeightBlock W = bX),
    let D := upperReduction W hsupp
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        SX.operations W.subgroup D.normalizerRoot D.localBrauer =
      SX.operations.inflateToNormalizer W.subgroup
        (SX.operations.localCharacterBlock W.subgroup W.localCharacter W.defectZero)
  lowerCompatibility : ∀ (V : CharacterWeight 2 K (G (ZMod 3)))
      (hsupp : S.operations.rawWeightBlock V = b),
    let D := lowerReduction V hsupp
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock
        S.operations V.subgroup D.normalizerRoot D.localBrauer =
      S.operations.inflateToNormalizer V.subgroup
        (S.operations.localCharacterBlock V.subgroup V.localCharacter V.defectZero)
  total : ∀ w : CoverWeight SX bX,
    ∃ v : OmegaWeight (ZMod 3) S b, ClassInflates q w.val v.val
  unique : ∀ (w : CoverWeight SX bX) (v v' : OmegaWeight (ZMod 3) S b),
    ClassInflates q w.val v.val → ClassInflates q w.val v'.val → v = v'
  reverse_unique : ∀ (w w' : CoverWeight SX bX) (v : OmegaWeight (ZMod 3) S b),
    ClassInflates q w.val v.val → ClassInflates q w'.val v.val → w = w'
  complete : ∀ v : OmegaWeight (ZMod 3) S b,
    ∃ w : CoverWeight SX bX, ClassInflates q w.val v.val

variable {SX literalX}
variable {q : X →* G (ZMod 3)} {hq : Function.Surjective q}
    {hcentral : q.ker ≤ Subgroup.center X} {hprimeTo : ¬ 2 ∣ Nat.card q.ker}
    {S : OmegaWeightSource (k := k) (K := K) (ZMod 3)}
    {literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val}
    {rootX : PrimeRegularRootEmbedding 2 k K X}
    {bX : LiteralPrimitiveBlock k X} {hbX : IsPrincipal bX}
    {b : LiteralPrimitiveBlock k (G (ZMod 3))} {hb : IsPrincipal b}
    {blockImage : algebraMapOf q bX.val = b.val}
    (source : FLZ23Source q hq hcentral hprimeTo SX literalX S literal rootX bX hbX b hb blockImage)

def principalWeightDeflate (w : CoverWeight SX bX) : OmegaWeight (ZMod 3) S b :=
  Classical.choose (source.total w)

theorem principalWeightDeflate_graph (w : CoverWeight SX bX) :
    ClassInflates q w.val (principalWeightDeflate source w).val :=
  Classical.choose_spec (source.total w)

theorem principalWeightDeflate_injective : Function.Injective (principalWeightDeflate source) := by
  intro w w' heq
  apply source.reverse_unique w w' (principalWeightDeflate source w)
  · exact principalWeightDeflate_graph source w
  · rw [heq]
    exact principalWeightDeflate_graph source w'

theorem principalWeightDeflate_surjective : Function.Surjective (principalWeightDeflate source) := by
  intro v
  obtain ⟨w, hw⟩ := source.complete v
  exact ⟨w, source.unique w _ v (principalWeightDeflate_graph source w) hw⟩

def principalWeightEquiv : CoverWeight SX bX ≃ OmegaWeight (ZMod 3) S b :=
  Equiv.ofBijective (principalWeightDeflate source)
    ⟨principalWeightDeflate_injective source, principalWeightDeflate_surjective source⟩

theorem principalWeightEquiv_graph (w : CoverWeight SX bX) :
    ClassInflates q w.val (principalWeightEquiv source w).val :=
  principalWeightDeflate_graph source w

theorem principalWeightEquiv_symm_graph (v : OmegaWeight (ZMod 3) S b) :
    ClassInflates q ((principalWeightEquiv source).symm v).val v.val := by
  have graph := principalWeightEquiv_graph source ((principalWeightEquiv source).symm v)
  simpa only [Equiv.apply_symm_apply] using graph

/-- Naturality is a deduction from literal ordinary values and uniqueness
of the published graph. It is not a field of the source record. -/
theorem principalWeightEquiv_equivariant
    (alpha : (MulAut X)ᵐᵒᵖ) (h : H (ZMod 3))
    (square : ∀ x, q (alpha.unop x) = (conjugationOp (G (ZMod 3)) h).unop (q x))
    (w : CoverWeight SX bX) :
    principalWeightEquiv source (coverWeightStep SX literalX bX hbX alpha w) =
      weightStep (ZMod 3) S literal b hb h (principalWeightEquiv source w) := by
  apply source.unique (coverWeightStep SX literalX bX hbX alpha w)
  · exact principalWeightEquiv_graph source _
  · exact classInflates_op_smul q alpha (conjugationOp (G (ZMod 3)) h) square
      w.val (principalWeightEquiv source w).val (principalWeightEquiv_graph source w)

end ModularRep.PaperProofs.TypeBQ3PrincipalWeightInflation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
