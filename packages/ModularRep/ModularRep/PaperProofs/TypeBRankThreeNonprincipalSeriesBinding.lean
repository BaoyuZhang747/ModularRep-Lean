import ModularRep.PaperProofs.TypeBSpinBroueMichelSourceBinding
import ModularRep.PaperProofs.TypeBSpinGGGRPrincipalSeriesBinding
import ModularRep.OddQuasiIsolation

/-!
The full rational Lusztig family on the actual Spin group and literal PCSp
classes is an explicit E1/U source boundary. FLZ Sections 2.3, 2.4.2 and 3.1
fix that family, its ordinary block unions and the dual finite-point model.
The specified ordinary selector is tied to the same modular system, root and
stable-lattice decomposition numbers before the block label is constructed.

The additional one-way source is Cabanes--Enguehard Theorem 21.14: an actual
ordinary character in a rational two-element series belongs to the specified
principal block. Its coefficient and finite-point interpretation remain
explicit. No odd modular prime, integral series map or block matching is
required. The identity-label implication is proved from this source.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalSeriesBinding

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBRationalSeriesSource TypeBSpinBroueMichelCarriers
open TypeBSpinConlonBlockSourceInstantiation (RationalIndex)
open TypeBOrdinaryBlockSplitting
open TypeBSpinGGGRPrincipalSeriesBinding (IsTwoElement)
open TypeBCentralKernelBlockSource

variable {p f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  {N : NormSource 3 F} [Finite (Spin 3 F N)]

/-- Odd defining characteristic supplies the nondefining-prime guard. -/
theorem two_ne_defining (parameters : OddFieldParameters F p f) : 2 ≠ p := by
  intro h
  exact (by decide : ¬ Odd 2) (h.symm ▸ parameters.odd)

/-- Membership in the same full rational family at an actual dual element. -/
def RationalSeriesAt
    (S : RationalSeriesSource K (Spin 3 F N) (FullRationalIndex p 3 F))
    (s : PCSp F 3) (chi : Irr K (Spin 3 F N)) : Prop :=
  ∃ regular : p.Coprime (orderOf s),
    chi ∈ S.rationalSeries ⟨ConjClasses.mk s, s, rfl, regular⟩

variable (parameters : OddFieldParameters F p f)
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  (hinj : IrreducibleBrauerCharacterInjectivity iota)
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 3 F N) => b.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : OrdinaryBlockSource Msys iota hinj blocks)

/-- Source facts about the full specified ordinary family, before selecting
any block label. The family must be the prescribed rational Lusztig family. -/
structure Sources where
  family : RationalSeriesSource K (Spin 3 F N) (FullRationalIndex p 3 F)
  unions : TypeBSpinBroueMichelSourceBinding.BlockUnionCertificate
    family parameters.prime Nat.prime_two (two_ne_defining parameters)
    Msys iota hinj blocks ordinary
  two_series_principal : ∀ (s : PCSp F 3) (chi : Irr K (Spin 3 F N)),
    IsTwoElement s → RationalSeriesAt family s chi →
      IsPrincipal (ordinary.physical.ordinaryBlock chi)

variable (source : Sources parameters Msys iota hinj blocks ordinary)

/-- The specified block index is derived by the existing ordinary union API. -/
def blockSeries (b : LiteralPrimitiveBlock k (Spin 3 F N)) : RationalIndex p 2 3 F :=
  (TypeBSpinBroueMichelSourceBinding.rationalSource source.family parameters.prime
    Nat.prime_two (two_ne_defining parameters) Msys iota hinj blocks ordinary
    source.unions).blockSeries b

/-- Choose only an actual representative of that constructed rational class. -/
def labelParameter (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F) :=
  Classical.choose (parameterIndex_surjective
    (blockSeries parameters Msys iota hinj blocks ordinary source b))

theorem labelParameter_index (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    parameterIndex (labelParameter parameters Msys iota hinj blocks ordinary source b) =
      blockSeries parameters Msys iota hinj blocks ordinary source b :=
  Classical.choose_spec (parameterIndex_surjective
    (blockSeries parameters Msys iota hinj blocks ordinary source b))

/-- The label is an element of the literal quotient by all nonzero scalars. -/
def label (b : LiteralPrimitiveBlock k (Spin 3 F N)) : PCSp F 3 :=
  (labelParameter parameters Msys iota hinj blocks ordinary source b).val

theorem label_defining_regular (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    p.Coprime (orderOf (label parameters Msys iota hinj blocks ordinary source b)) :=
  (labelParameter parameters Msys iota hinj blocks ordinary source b).property.1

theorem label_two_prime (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    IsPrimeRegular 2 (label parameters Msys iota hinj blocks ordinary source b) :=
  (labelParameter parameters Msys iota hinj blocks ordinary source b).property.2.symm

/-- Every ordinary character of the same specified block lies in its full
Broue--Michel union, including the commuting two-element part. -/
theorem blockSeries_support (b : LiteralPrimitiveBlock k (Spin 3 F N))
    (chi : Irr K (Spin 3 F N)) (hchi : ordinary.physical.ordinaryBlock chi = b) :
    indexedOrdinaryUnion source.family parameters.prime Nat.prime_two
      (two_ne_defining parameters)
      (blockSeries parameters Msys iota hinj blocks ordinary source b) chi := by
  apply (TypeBSpinBroueMichelSourceBinding.ordinaryUnion_iff_blockSeries source.family
    parameters.prime Nat.prime_two (two_ne_defining parameters)
    Msys iota hinj blocks ordinary source.unions _ chi).mpr
  change blockSeries parameters Msys iota hinj blocks ordinary source
    (ordinary.physical.ordinaryBlock chi) = _
  rw [hchi]

/-- Literal association means full ordinary union support at this actual
semisimple two-regular class, rather than a caller-supplied relation. -/
def Associated (b : LiteralPrimitiveBlock k (Spin 3 F N)) (s : PCSp F 3) : Prop :=
  ∃ regular : p.Coprime (orderOf s) ∧ Nat.Coprime 2 (orderOf s),
    ∀ chi : Irr K (Spin 3 F N), ordinary.physical.ordinaryBlock chi = b →
      indexedOrdinaryUnion source.family parameters.prime Nat.prime_two
        (two_ne_defining parameters) (parameterIndex ⟨s, regular⟩) chi

theorem label_associated (b : LiteralPrimitiveBlock k (Spin 3 F N)) :
    Associated parameters Msys iota hinj blocks ordinary source b
      (label parameters Msys iota hinj blocks ordinary source b) := by
  refine ⟨(labelParameter parameters Msys iota hinj blocks ordinary source b).property, ?_⟩
  intro chi hchi
  have h := blockSeries_support parameters Msys iota hinj blocks ordinary source b chi hchi
  rw [← labelParameter_index parameters Msys iota hinj blocks ordinary source b] at h
  exact h

/-- Expose the ordinary representative and actual commuting product behind
the indexed support, retaining the same selected rational class. -/
theorem label_representative_support
    (b : LiteralPrimitiveBlock k (Spin 3 F N)) (chi : Irr K (Spin 3 F N))
    (hchi : ordinary.physical.ordinaryBlock chi = b) :
    ∃ s : AdmissibleParameter (p := p) (ell := 2) (n := 3) (F := F),
      parameterIndex s = parameterIndex
        (labelParameter parameters Msys iota hinj blocks ordinary source b) ∧
      ∃ t : CentralizerEllElement s,
        chi ∈ source.family.rationalSeries
          (productIndex parameters.prime Nat.prime_two (two_ne_defining parameters) s t) := by
  have h := blockSeries_support parameters Msys iota hinj blocks ordinary source b chi hchi
  rw [← labelParameter_index parameters Msys iota hinj blocks ordinary source b] at h
  exact h

/-- Identity-class union support forces the same literal block to be principal. -/
theorem identity_label_principal :
    ModularRep.TypeBQuasiIsolation.IdentityLabelPrincipalBlockInterface
      (Associated parameters Msys iota hinj blocks ordinary source) IsPrincipal := by
  intro b associated
  obtain ⟨chi, hchi⟩ := ordinary.physical.ordinaryBlock_surjective b
  obtain ⟨regular, support⟩ := associated
  obtain ⟨s, hs, t, ht⟩ := support chi hchi
  have classes : ConjClasses.mk s.val = ConjClasses.mk (1 : PCSp F 3) :=
    congrArg Subtype.val hs
  have s_one : s.val = 1 :=
    isConj_one_left.mp (ConjClasses.mk_eq_mk_iff_isConj.mp classes)
  have twoElement : IsTwoElement (s.val * (t.val : PCSp F 3)) := by
    obtain ⟨a, ha⟩ := t.property
    refine ⟨a, ?_⟩
    have product_eq : s.val * (t.val : PCSp F 3) = (t.val : PCSp F 3) :=
      (congrArg (fun x : PCSp F 3 => x * (t.val : PCSp F 3)) s_one).trans
        (one_mul (t.val : PCSp F 3))
    have power : (t.val : PCSp F 3) ^ (2 ^ a) = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one _
    exact (congrArg (fun x : PCSp F 3 => x ^ (2 ^ a)) product_eq).trans power
  have principal := source.two_series_principal (s.val * (t.val : PCSp F 3)) chi
    twoElement ⟨product_order_coprime parameters.prime Nat.prime_two
      (two_ne_defining parameters) s t, ht⟩
  exact hchi ▸ principal

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalSeriesBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
