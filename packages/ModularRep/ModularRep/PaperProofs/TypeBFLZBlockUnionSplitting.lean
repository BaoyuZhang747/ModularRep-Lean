import ModularRep.PaperProofs.TypeBFLZLabelSplittingSource
import Mathlib.Data.Nat.Prime.Basic

/-!
# The literal Broue--Michel ordinary union in the fixed Type B packet

The union is defined using actual ell-elements of the actual CSp centralizer
and the full rational-series function from the SAME equation-(3.4) packet.
The product's defining-prime regular order guard is derived. The full union
identification is the final paragraph of the proof of FLZ Theorem 6.3, not
the existing t=1 membership clause. It concerns ALL ordinary characters.

The source certificate retains the prescribed modular root, literal specified
primitive-block decomposition and ordinary block selector. Their published
source realizations remain explicit obligations. It supplies no integral
map, basic set, Brauer matching, equivariance target or numbered conclusion.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBFLZBlockUnionSplitting

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBFLZLabelSource
open TypeBFLZLabelSplittingSource

universe u

variable {F K : Type u} [Field F] [Field K] [CharZero K]
variable {p ell n : ℕ}

/-- The literal centralizer ell-elements, including the identity. The order
is that of the underlying element in the actual finite CSp group. -/
abbrev CentralizerEllElement (s : AdmissibleParameter F p ell n) :=
  {t : parameterCentralizer F p n (admissibleToSemisimple F p ell n s) //
    ∃ a : ℕ, orderOf (t : CSp F n) = ell ^ a}

/-- The identity is an ell-element of the same actual centralizer. -/
def oneEllElement (s : AdmissibleParameter F p ell n) : CentralizerEllElement s :=
  ⟨1, 0, by simp⟩

/-- Commutation comes from literal centralizer membership. -/
theorem centralizerEllElement_commute (s : AdmissibleParameter F p ell n)
    (t : CentralizerEllElement s) : Commute s.val (t.val : CSp F n) := by
  have ht : (t.val : CSp F n) * s.val = s.val * (t.val : CSp F n) :=
    Subgroup.mem_centralizer_singleton_iff.mp t.val.property
  exact ht.symm

/-- Distinct defining and modular primes make an ell-element p-regular. -/
theorem centralizerEllElement_order_coprime (h : Applicability p ell n)
    (s : AdmissibleParameter F p ell n) (t : CentralizerEllElement s) :
    p.Coprime (orderOf (t.val : CSp F n)) := by
  obtain ⟨a, ha⟩ := t.property
  rw [ha]
  have hpe : p.Coprime ell :=
    (Nat.coprime_primes h.defining_prime h.modular_prime).mpr h.nondefining.symm
  exact hpe.pow_right a

/-- The order of the commuting product divides the product of the orders;
both factors are p-regular. No semisimplicity guard is supplied separately. -/
theorem product_order_coprime (h : Applicability p ell n)
    (s : AdmissibleParameter F p ell n) (t : CentralizerEllElement s) :
    p.Coprime (orderOf (s.val * (t.val : CSp F n))) := by
  exact (s.property.1.mul_right (centralizerEllElement_order_coprime h s t)).of_dvd_right
    (centralizerEllElement_commute s t).orderOf_mul_dvd_mul_orderOf

/-- The actual product parameter for the full rational series. -/
def productParameter (h : Applicability p ell n)
    (s : AdmissibleParameter F p ell n) (t : CentralizerEllElement s) :
    SemisimpleParameter F p n :=
  ⟨s.val * (t.val : CSp F n), product_order_coprime h s t⟩

@[simp]
theorem productParameter_val (h : Applicability p ell n)
    (s : AdmissibleParameter F p ell n) (t : CentralizerEllElement s) :
    (productParameter h s t).val = s.val * (t.val : CSp F n) := rfl

@[simp]
theorem productParameter_one (h : Applicability p ell n)
    (s : AdmissibleParameter F p ell n) :
    productParameter h s (oneEllElement s) = admissibleToSemisimple F p ell n s := by
  apply Subtype.ext
  simp [productParameter, oneEllElement, admissibleToSemisimple]

section FullSeries

variable [Finite F] [CharP F p] [Finite (Clifford n F)]
variable {unipotent : UnipotentPredicate F K p n}
variable [MulAction (CSp F n) (FullCharacterPair F K p n unipotent)]
variable (S : TypeBFLZLabelSplittingSource.Equation34Source (ell := ell) unipotent)

/-- FLZ Section 2.4.2: the actual ordinary union over all commuting
semisimple ell-elements. Defining-prime regularity is derived above. -/
def ordinaryUnion (s : AdmissibleParameter F p ell n)
    (chi : Irr K (SpecialClifford n F)) : Prop :=
  ∃ t : CentralizerEllElement s,
    S.rationalSeries (productParameter S.hypotheses s t) chi

/-- Equation (3.4) already implies rational-series conjugacy invariance
for every actual ordinary character. This is not an additional source. -/
theorem rationalSeries_iff_of_isConj (s t : SemisimpleParameter F p n)
    (h : IsConj s.val t.val) (chi : Irr K (SpecialClifford n F)) :
    S.rationalSeries s chi ↔ S.rationalSeries t chi := by
  obtain ⟨l, hl⟩ := S.fullCharacter_surjective chi
  rw [← hl]
  change S.rationalSeries s (S.classification (Quotient.mk _ l)) ↔
    S.rationalSeries t (S.classification (Quotient.mk _ l))
  rw [S.rational_membership, S.rational_membership]
  exact ⟨fun hs => h.symm.trans hs, fun ht => h.trans ht⟩

/-- The t=1 constituent is contained in the full ordinary union. -/
theorem rationalSeries_mem_ordinaryUnion (s : AdmissibleParameter F p ell n)
    (chi : Irr K (SpecialClifford n F))
    (hchi : S.rationalSeries (admissibleToSemisimple F p ell n s) chi) :
    ordinaryUnion S s chi := by
  refine ⟨oneEllElement s, ?_⟩
  simpa only [productParameter_one] using hchi

/-- The same union indexed by actual admissible rational conjugacy classes.
No representative is chosen, and no independent union predicate is supplied. -/
def indexedOrdinaryUnion (i : SourceIndex F p ell n)
    (chi : Irr K (SpecialClifford n F)) : Prop :=
  ∃ s : AdmissibleParameter F p ell n,
    parameterIndex F p ell n s = i ∧ ordinaryUnion S s chi

/-- The selected rational-series family embeds into its full ordinary union. -/
theorem rationalFamily_mem_indexedOrdinaryUnion (i : SourceIndex F p ell n)
    (chi : Irr K (SpecialClifford n F)) (hchi : chi ∈ S.rationalFamily i) :
    indexedOrdinaryUnion S i chi := by
  obtain ⟨s, hs, hseries⟩ := hchi
  exact ⟨s, hs, rationalSeries_mem_ordinaryUnion S s chi hseries⟩

section Blocks

variable {k : Type u} [Field k] [CharP k ell] [IsAlgClosed k]
variable (Core : AdmissibleParameter F p ell n → Type u)
variable [MulAction (CSp F n) (BlockPair F p ell n Core)]
variable (ordinaryBlock : Irr K (SpecialClifford n F) →
  LiteralPrimitiveBlock k (SpecialClifford n F))

/-- E2: the final paragraph of the proof of FLZ Theorem 6.3, printed p.567.
For ALL ordinary Irr, membership in the explicitly defined full union is
equivalent to the SAME block classification having the prescribed rational
index. The t=1 clause in T does not imply this certificate.

The coefficient guards of S, T and the specified iota/blocks arguments are
retained. Realizing their source meanings and the literal ordinary selector
is required; this structure contains no basic-set or matching conclusion. -/
structure BlockUnionCertificate
    (iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    [physicalBlocks : Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
    (blocks : BlockIdempotentDecomposition
      (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val))
    (T : TypeBFLZLabelSplittingSource.Theorem63Source
      unipotent S Core ordinaryBlock iota blocks) where
  modular_characteristic : CharP k ell
  modular_splitting : IsAlgClosed k
  membership : ∀ (s : AdmissibleParameter F p ell n)
    (chi : Irr K (SpecialClifford n F)),
    ordinaryUnion S s chi ↔
      T.blockSeries (ordinaryBlock chi) = parameterIndex F p ell n s

variable {Core ordinaryBlock}
variable {iota : PrimeRegularRootEmbedding ell k K (SpecialClifford n F)}
variable [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
variable {blocks : BlockIdempotentDecomposition
  (fun b : LiteralPrimitiveBlock k (SpecialClifford n F) => b.val)}
variable {T : TypeBFLZLabelSplittingSource.Theorem63Source
  unipotent S Core ordinaryBlock iota blocks}
variable (U : BlockUnionCertificate S Core ordinaryBlock iota blocks T)

include U in
/-- Class-indexed source transport follows from the exact full-union
certificate and surjectivity of the actual parameter-index map. -/
theorem indexedOrdinaryUnion_iff_blockSeries (i : SourceIndex F p ell n)
    (chi : Irr K (SpecialClifford n F)) :
    indexedOrdinaryUnion S i chi ↔ T.blockSeries (ordinaryBlock chi) = i := by
  constructor
  · rintro ⟨s, hs, hchi⟩
    exact (U.membership s chi).mp hchi |>.trans hs
  · intro hchi
    obtain ⟨s, hs⟩ := parameterIndex_surjective F p ell n i
    exact ⟨s, hs, (U.membership s chi).mpr (hchi.trans hs.symm)⟩

include U in
/-- Representative independence is derived here through the exact E2
full-union identification, not accepted as a second invariance source. -/
theorem ordinaryUnion_iff_of_parameterIndex_eq
    (s t : AdmissibleParameter F p ell n)
    (h : parameterIndex F p ell n s = parameterIndex F p ell n t)
    (chi : Irr K (SpecialClifford n F)) :
    ordinaryUnion S s chi ↔ ordinaryUnion S t chi := by
  rw [U.membership, U.membership, h]

include U in
theorem ordinaryUnion_iff_of_isConj (s t : AdmissibleParameter F p ell n)
    (h : IsConj s.val t.val) (chi : Irr K (SpecialClifford n F)) :
    ordinaryUnion S s chi ↔ ordinaryUnion S t chi :=
  ordinaryUnion_iff_of_parameterIndex_eq S U s t
    ((parameterIndex_eq_iff F p ell n s t).mpr h) chi

/-- Exact membership transport keeps the actual ordinary character fixed. -/
def ordinaryUnionEquivBlockUnion (s : AdmissibleParameter F p ell n) :
    {chi : Irr K (SpecialClifford n F) // ordinaryUnion S s chi} ≃
      {chi : Irr K (SpecialClifford n F) //
        T.blockSeries (ordinaryBlock chi) = parameterIndex F p ell n s} where
  toFun chi := ⟨chi.val, (U.membership s chi.val).mp chi.property⟩
  invFun chi := ⟨chi.val, (U.membership s chi.val).mpr chi.property⟩
  left_inv chi := by apply Subtype.ext; rfl
  right_inv chi := by apply Subtype.ext; rfl

@[simp]
theorem ordinaryUnionEquivBlockUnion_val (s : AdmissibleParameter F p ell n)
    (chi : {chi : Irr K (SpecialClifford n F) // ordinaryUnion S s chi}) :
    (ordinaryUnionEquivBlockUnion S U s chi).val = chi.val := rfl

/-- The class-indexed ordinary union is the literal block-index fibre. -/
def indexedOrdinaryUnionEquivBlockUnion (i : SourceIndex F p ell n) :
    {chi : Irr K (SpecialClifford n F) // indexedOrdinaryUnion S i chi} ≃
      {chi : Irr K (SpecialClifford n F) // T.blockSeries (ordinaryBlock chi) = i} where
  toFun chi := ⟨chi.val, (indexedOrdinaryUnion_iff_blockSeries S U i chi.val).mp chi.property⟩
  invFun chi := ⟨chi.val, (indexedOrdinaryUnion_iff_blockSeries S U i chi.val).mpr chi.property⟩
  left_inv chi := by apply Subtype.ext; rfl
  right_inv chi := by apply Subtype.ext; rfl

@[simp]
theorem indexedOrdinaryUnionEquivBlockUnion_val (i : SourceIndex F p ell n)
    (chi : {chi : Irr K (SpecialClifford n F) // indexedOrdinaryUnion S i chi}) :
    (indexedOrdinaryUnionEquivBlockUnion S U i chi).val = chi.val := rfl

include U in
/-- Membership is constant on each literal ordinary block fibre. -/
theorem ordinaryUnion_of_same_block (s : AdmissibleParameter F p ell n)
    (chi psi : Irr K (SpecialClifford n F))
    (hblock : ordinaryBlock chi = ordinaryBlock psi) (hchi : ordinaryUnion S s chi) :
    ordinaryUnion S s psi := by
  apply (U.membership s psi).mpr
  exact (congrArg T.blockSeries hblock).symm.trans ((U.membership s chi).mp hchi)

end Blocks
end FullSeries

end ModularRep.PaperProofs.TypeBFLZBlockUnionSplitting


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
