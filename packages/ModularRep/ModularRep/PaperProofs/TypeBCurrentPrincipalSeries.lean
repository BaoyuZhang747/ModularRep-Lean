import ModularRep.PaperProofs.TypeBSpinPrincipalDecompositionBinding
import ModularRep.PaperProofs.TypeBSpinGGGRPrincipalSeriesBinding
import ModularRep.PaperProofs.TypeBCentralKernelPrincipalStability
import ModularRep.StrictQuasiIsolation
import ModularRep.OddQuasiIsolation

/-!
# Principal two-series and strict blocks in odd-field Spin groups

This is the rank-at-least-two provider for `lem:type-b-principal-series`.
Ordinary blocks are the specified primitive idempotents selected by the
existing stable-lattice decomposition source on the literal Spin group.
Rational semisimple labels live in the literal finite PCSp group.

Cabanes--Enguehard Theorem 21.14 supplies the full ordinary principal-series
equality. Bonnafe Proposition 5.3(a) supplies its fourth-power consequence
for semisimple quasi-isolated adjoint labels, through an algebraically
closed symplectic lift. No rational Sp-to-PCSp surjectivity is asserted.
The ordinary series and odd block-label dictionary remain E2/U inputs.

The strict predicate is the centralizer/proper-Levi formula on the same
label, not a freely supplied predicate on blocks. Connected centralizers,
proper Levis and the rational inclusion have their explicit E1/U algebraic
interpretation. Lean proves the identity is strict, strict implies quasi,
the odd-label order argument, both block implications and their joins.
Neither the final three-clause lemma nor a principal-is-strict assertion
is a field of a source record. The older GGGR certificate is preserved;
`toLegacyCertificate` derives its narrower fields when rank is at least three.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBCurrentPrincipalSeries

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBCentralKernelBlockSource TypeBSpinPrincipalDecompositionBinding
open ModularRep.ManuscriptVerification.StrictQuasiIsolation

variable {n r f : ℕ} {F k K O : Type}
  [Field F] [Finite F] [CharP F r]
  [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [CommRing O] [IsDomain O] [Algebra O K]
  {N : NormSource n F} [Finite (Spin n F N)]

/-- A power-of-two order condition on the actual rational dual label. -/
abbrev IsTwoElement (s : PCSp F n) : Prop :=
  TypeBSpinGGGRPrincipalSeriesBinding.IsTwoElement s

/-- The identity two-series is the union of rational Lusztig series over
the two-elements in the same finite dual group. -/
def IdentityTwoSeries (rationalSeries : PCSp F n → Irr K (Spin n F N) → Prop)
    (chi : Irr K (Spin n F N)) : Prop :=
  ∃ t : PCSp F n, IsTwoElement t ∧ rationalSeries t chi

/-- The ordinary two-series at a rational odd semisimple label. -/
def TwoSeries (rationalSeries : PCSp F n → Irr K (Spin n F N) → Prop)
    (s : PCSp F n) (chi : Irr K (Spin n F N)) : Prop :=
  ∃ t : PCSp F n, IsTwoElement t ∧ Commute s t ∧ rationalSeries (s * t) chi

theorem twoSeries_one (rationalSeries : PCSp F n → Irr K (Spin n F N) → Prop)
    (chi : Irr K (Spin n F N)) :
    TwoSeries rationalSeries 1 chi ↔ IdentityTwoSeries rationalSeries chi := by
  constructor
  · rintro ⟨t, ht, _, hchi⟩
    exact ⟨t, ht, by simpa only [one_mul] using hchi⟩
  · rintro ⟨t, ht, hchi⟩
    exact ⟨t, ht, by change 1 * t = t * 1; simp,
      by simpa only [one_mul] using hchi⟩

/-- Coordinatewise scalar inclusion on the fixed alternating spaces. -/
def vectorMap {A : Type} [Field A] (embedding : F →+* A)
    (v : SymplecticSpace F n) : SymplecticSpace A n :=
  (fun i => embedding (v.1 i), fun i => embedding (v.2 i))

/-- E1/U algebraic interpretation on fixed finite and algebraic PCSp
carriers. `rationalMap` is the inclusion induced by `embedding`, identified
with the full rational point group of the split Frobenius. The connected
centralizer and proper-Levi predicates have their algebraic meanings.
No choice of an ordinary character or block is made by these fields. -/
structure DualGeometry (parameters : OddFieldParameters F r f) (rank : 2 ≤ n) where
  Closure : Type
  [fieldClosure : Field Closure]
  [algClosedClosure : IsAlgClosed Closure]
  [charClosure : CharP Closure r]
  embedding : F →+* Closure
  conformalMap : CSp F n →* CSp Closure n
  conformalMap_vector : ∀ (g : CSp F n) (v : SymplecticSpace F n),
    linearPart Closure n (conformalMap g) (vectorMap embedding v) =
      vectorMap embedding (linearPart F n g v)
  conformalMap_multiplier : ∀ g : CSp F n,
    (multiplier Closure n (conformalMap g) : Closure) =
      embedding (multiplier F n g : F)
  rationalMap : PCSp F n →* PCSp Closure n
  rationalMap_quotient : ∀ g : CSp F n,
    rationalMap (QuotientGroup.mk' (scalarSubgroup F n) g) =
      QuotientGroup.mk' (scalarSubgroup Closure n) (conformalMap g)
  rationalMap_injective : Function.Injective rationalMap
  connectedCentralizer : PCSp F n → Subgroup (PCSp Closure n)
  connected_le : ∀ s, connectedCentralizer s ≤ Subgroup.centralizer {rationalMap s}
  connected_one : connectedCentralizer 1 = ⊤
  IsProperLevi : Set (PCSp Closure n) → Prop
  proper : ∀ L, IsProperLevi L → ¬ Set.univ ⊆ L

attribute [instance] DualGeometry.fieldClosure DualGeometry.algClosedClosure
  DualGeometry.charClosure

variable {parameters : OddFieldParameters F r f} {rank : 2 ≤ n}

namespace DualGeometry

variable (D : DualGeometry parameters rank)

/-- The finite centralizer as a subgroup of the same algebraic dual. -/
def finiteCentralizer (s : PCSp F n) : Subgroup (PCSp D.Closure n) :=
  Subgroup.centralizer {D.rationalMap s} ⊓ D.rationalMap.range

theorem finiteCentralizer_le (s : PCSp F n) :
    D.finiteCentralizer s ≤ Subgroup.centralizer {D.rationalMap s} := inf_le_left

/-- Semisimplicity and geometric quasi-isolation for a rational label. -/
def QuasiIsolated (s : PCSp F n) : Prop :=
  IsPrimeRegular r s ∧
    NotContainedInProperLevi
      (Subgroup.centralizer {D.rationalMap s} : Set (PCSp D.Closure n)) D.IsProperLevi

/-- The strict centralizer formula, retaining the same semisimple label. -/
def StrictlyQuasiIsolatedLabel (s : PCSp F n) : Prop :=
  IsPrimeRegular r s ∧
    NotContainedInProperLevi
      ((D.finiteCentralizer s : Set (PCSp D.Closure n)) *
        (D.connectedCentralizer s : Set (PCSp D.Closure n))) D.IsProperLevi

theorem quasiIsolated_of_strict (s : PCSp F n)
    (hs : D.StrictlyQuasiIsolatedLabel s) : D.QuasiIsolated s :=
  ⟨hs.1, quasiIsolated_of_strictlyQuasiIsolated
    (D.finiteCentralizer_le s) (D.connected_le s) hs.2⟩

/-- The identity is strict because its connected centralizer is the whole
algebraic group and a proper Levi cannot contain that group. -/
theorem identity_strict : D.StrictlyQuasiIsolatedLabel 1 := by
  refine ⟨isPrimeRegular_one, ?_⟩
  intro L hL hsub
  apply D.proper L hL
  intro x _
  apply hsub
  refine ⟨1, (D.finiteCentralizer 1).one_mem, x, ?_, one_mul x⟩
  rw [D.connected_one]
  trivial

end DualGeometry

/-- Bonnafe Proposition 5.3(a), specialized to the same rank-at-least-two
odd-field adjoint label. The fourth-power conclusion is the image of the
algebraically closed symplectic lift's fourth-power identity. Its rational
point/closure interpretation remains U; no rational symplectic lift is used. -/
structure BonnafeSource (D : DualGeometry parameters rank) : Prop where
  fourth_power : ∀ s : PCSp F n, D.QuasiIsolated s → s ^ 4 = 1

theorem twoElement_of_quasiIsolated (D : DualGeometry parameters rank)
    (bonnafe : BonnafeSource D) (s : PCSp F n) (hs : D.QuasiIsolated s) :
    IsTwoElement s := by
  refine ⟨2, ?_⟩
  simpa using bonnafe.fourth_power s hs

/-- The checked odd-order/fourth-power argument applies to the actual
rational block label, without a change of dual carrier. -/
theorem strict_odd_label_eq_one (D : DualGeometry parameters rank)
    (bonnafe : BonnafeSource D) (s : PCSp F n)
    (oddLabel : IsPrimeRegular 2 s) (strict : D.StrictlyQuasiIsolatedLabel s) :
    s = 1 := by
  have fourth := bonnafe.fourth_power s (D.quasiIsolated_of_strict s strict)
  have coprime : (orderOf s).Coprime 4 := by
    simpa only [show 4 = 2 ^ 2 by decide] using oddLabel.pow_right 2
  exact (show IsPrimeRegular 4 s from coprime).eq_one_of_pow_eq_one fourth

variable (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin n F N) => b.val))

/-- The same specified ordinary block selector and literal principal block
throughout the lemma. Ordinary splitting is explicit; stable reductions
and the rational-series interpretation retain the existing E1/U source scope.
The principal test is the action on the actual trivial representation. -/
structure Context (parameters : OddFieldParameters F r f) (rank : 2 ≤ n) where
  ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card (Spin n F N))
  ordinary : OrdinaryBlockSource Msys iota blocks
  principalBlock : LiteralPrimitiveBlock k (Spin n F N)
  principal : IsPrincipal principalBlock
  rationalSeries : PCSp F n → Irr K (Spin n F N) → Prop
  series_semisimple : ∀ s chi, rationalSeries s chi → IsPrimeRegular r s

variable {Msys iota blocks}

/-- Exactly Cabanes--Enguehard Theorem 21.14, p. 341, for odd q and the
literal type-B group (including rank two). The equivalence records both
ordinary-series inclusions, on the context's one specified block selector. -/
structure CE2114Source (C : Context Msys iota blocks parameters rank) : Prop where
  membership_iff : ∀ chi : Irr K (Spin n F N),
    C.ordinary.ordinaryBlock chi = C.principalBlock ↔
      IdentityTwoSeries C.rationalSeries chi

/-- The E2/U odd semisimple block-label dictionary from the ordinary
two-series partition (Cabanes--Enguehard Theorem 9.12). `label` is a
rational representative of the block's parameter. The last field is only
the disjointness of an odd nonidentity series from the identity two-series;
it neither identifies any block as principal nor asserts strictness.
The definition below supplies the FLZ strict-block label criterion. -/
structure BlockLabelSource (C : Context Msys iota blocks parameters rank) where
  label : LiteralPrimitiveBlock k (Spin n F N) → PCSp F n
  semisimple : ∀ b, IsPrimeRegular r (label b)
  twoRegular : ∀ b, IsPrimeRegular 2 (label b)
  ordinary_series : ∀ chi : Irr K (Spin n F N),
    TwoSeries C.rationalSeries (label (C.ordinary.ordinaryBlock chi)) chi
  identity_disjoint : ∀ (s : PCSp F n) (chi : Irr K (Spin n F N)),
    IsPrimeRegular 2 s → TwoSeries C.rationalSeries s chi →
      IdentityTwoSeries C.rationalSeries chi → s = 1

/-- Strictness is the standard label formula on this same specified block.
Its interpretation as the published strict block notion is the stated
E2/U block-label dictionary, not a supplied conclusion about principal blocks. -/
def StrictlyQuasiIsolatedBlock (C : Context Msys iota blocks parameters rank)
    (D : DualGeometry parameters rank) (labels : BlockLabelSource C)
    (b : LiteralPrimitiveBlock k (Spin n F N)) : Prop :=
  D.StrictlyQuasiIsolatedLabel (labels.label b)

/-- Equality of the actual ordinary principal fibre and identity two-series. -/
theorem principal_series_eq (C : Context Msys iota blocks parameters rank)
    (ce : CE2114Source C) :
    {chi : Irr K (Spin n F N) | C.ordinary.ordinaryBlock chi = C.principalBlock} =
      {chi : Irr K (Spin n F N) | IdentityTwoSeries C.rationalSeries chi} := by
  ext chi
  exact ce.membership_iff chi

/-- Every ordinary character in a quasi-isolated rational series belongs
to the same specified principal block. -/
theorem quasiIsolated_character_principal (C : Context Msys iota blocks parameters rank)
    (ce : CE2114Source C) (D : DualGeometry parameters rank) (bonnafe : BonnafeSource D)
    (s : PCSp F n) (chi : Irr K (Spin n F N))
    (quasi : D.QuasiIsolated s) (series : C.rationalSeries s chi) :
    C.ordinary.ordinaryBlock chi = C.principalBlock :=
  (ce.membership_iff chi).mpr
    ⟨s, twoElement_of_quasiIsolated D bonnafe s quasi, series⟩

/-- Nonempty specified ordinary block fibres join the full series equality
to the identity-label test. No identity/principal block equivalence is a source. -/
theorem label_eq_one_iff (C : Context Msys iota blocks parameters rank)
    (ce : CE2114Source C) (labels : BlockLabelSource C)
    (b : LiteralPrimitiveBlock k (Spin n F N)) :
    labels.label b = 1 ↔ b = C.principalBlock := by
  obtain ⟨chi, hchi⟩ := C.ordinary.ordinaryBlock_surjective b
  have hseries : TwoSeries C.rationalSeries (labels.label b) chi := by
    simpa only [hchi] using labels.ordinary_series chi
  constructor
  · intro hlabel
    rw [hlabel] at hseries
    have principal := (ce.membership_iff chi).mpr
      ((twoSeries_one C.rationalSeries chi).mp hseries)
    exact hchi.symm.trans principal
  · intro hb
    exact labels.identity_disjoint (labels.label b) chi (labels.twoRegular b) hseries
      ((ce.membership_iff chi).mp (hchi.trans hb))

/-- The principal block is exactly the block with a strictly quasi-isolated
label. Both implications are deductions on the same primitive idempotents. -/
theorem strictlyQuasiIsolated_iff_eq_principal
    (C : Context Msys iota blocks parameters rank) (ce : CE2114Source C)
    (D : DualGeometry parameters rank) (bonnafe : BonnafeSource D)
    (labels : BlockLabelSource C) (b : LiteralPrimitiveBlock k (Spin n F N)) :
    StrictlyQuasiIsolatedBlock C D labels b ↔ b = C.principalBlock := by
  constructor
  · intro strict
    exact (label_eq_one_iff C ce labels b).mp
      (strict_odd_label_eq_one D bonnafe (labels.label b) (labels.twoRegular b) strict)
  · intro hb
    change D.StrictlyQuasiIsolatedLabel (labels.label b)
    rw [(label_eq_one_iff C ce labels b).mpr hb]
    exact D.identity_strict

/-- The same classification with the literal trivial-module principal test. -/
theorem strictlyQuasiIsolated_iff_principal
    (C : Context Msys iota blocks parameters rank) (ce : CE2114Source C)
    (D : DualGeometry parameters rank) (bonnafe : BonnafeSource D)
    (labels : BlockLabelSource C) (b : LiteralPrimitiveBlock k (Spin n F N)) :
    StrictlyQuasiIsolatedBlock C D labels b ↔ IsPrincipal b := by
  constructor
  · intro strict
    have hb := (strictlyQuasiIsolated_iff_eq_principal C ce D bonnafe labels b).mp strict
    exact hb.symm ▸ C.principal
  · intro principal
    apply (strictlyQuasiIsolated_iff_eq_principal C ce D bonnafe labels b).mpr
    exact TypeBCentralKernelPrincipalStability.principal_unique blocks
      b C.principalBlock principal C.principal

/-- All three clauses of current Lemma 4.8, for every rank at least two. -/
theorem lemma_4_8 (C : Context Msys iota blocks parameters rank) (ce : CE2114Source C)
    (D : DualGeometry parameters rank) (bonnafe : BonnafeSource D)
    (labels : BlockLabelSource C) :
    ({chi : Irr K (Spin n F N) | C.ordinary.ordinaryBlock chi = C.principalBlock} =
      {chi : Irr K (Spin n F N) | IdentityTwoSeries C.rationalSeries chi}) ∧
    (∀ (s : PCSp F n) (chi : Irr K (Spin n F N)),
      D.QuasiIsolated s → C.rationalSeries s chi →
        C.ordinary.ordinaryBlock chi = C.principalBlock) ∧
    (∀ b : LiteralPrimitiveBlock k (Spin n F N),
      StrictlyQuasiIsolatedBlock C D labels b ↔ IsPrincipal b) :=
  ⟨principal_series_eq C ce,
    quasiIsolated_character_principal C ce D bonnafe,
    strictlyQuasiIsolated_iff_principal C ce D bonnafe labels⟩

/-- Compatibility with the retained rank-at-least-three GGGR source.
Normalized Alvis--Curtis series preservation remains its separate
Cabanes--Enguehard Proposition 9.8(iv) input. -/
def toLegacyCertificate (C : Context Msys iota blocks parameters rank)
    (ce : CE2114Source C) (D : DualGeometry parameters rank) (bonnafe : BonnafeSource D)
    (higher : 3 ≤ n) (normalizedDual : Irr K (Spin n F N) → Irr K (Spin n F N))
    (dual_series : ∀ s chi, C.rationalSeries s chi →
      C.rationalSeries s (normalizedDual chi)) :
    TypeBSpinGGGRPrincipalSeriesBinding.PrincipalSeriesCertificate parameters higher
      C.ordinary.ordinaryBlock C.principalBlock C.principal C.rationalSeries
      D.QuasiIsolated normalizedDual where
  quasiIsolated_fourth_power := bonnafe.fourth_power
  two_series_principal s chi ht hchi := (ce.membership_iff chi).mpr ⟨s, ht, hchi⟩
  normalizedDual_series := dual_series

end ModularRep.PaperProofs.TypeBCurrentPrincipalSeries


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
