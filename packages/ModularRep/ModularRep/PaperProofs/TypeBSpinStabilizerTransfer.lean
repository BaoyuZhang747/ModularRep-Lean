import ModularRep.PaperProofs.TypeBSpinConlonBlockSourceInstantiation
import ModularRep.StabilizerFactorizationTransport

/-!
# The Spin stabilizer-transfer join in Type B Proposition 4.3

FLZ Theorem 3.10, p. 546, separates a nontrivial regular diagonal transform
from a field transform of an ordinary Spin character. That exact ordinary
statement remains an E2 input on the same actual set of characters and
effective action as the accepted Lemma 4.2 endpoint. The trivial diagonal
case follows from the literal kernel identification.

We invoke that accepted endpoint on block-orbit representatives, use the
existing `OddConlonOrbitAssembly` construction to combine the resulting
equivalence, and apply the existing `StabilizerFactorizationTransport`
theorem. There is no Brauer stabilizer-factorization or Brauer-to-ordinary
bijection premise. Source authentication of the ordinary theorem and of
the inherited Lemma 4.2 inputs retains its existing E1/E2/U boundary.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinStabilizerTransfer

open ModularRep
open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport
open TypeBCliffordCarriers TypeBSpinStabilizer
open TypeBSpinConlonBlockSourceInstantiation
open TypeBIntegralSeriesCertificate
open TypeBSpecialCliffordActionAdapter
open ConlonBasicSet OddConlonOrbitAssembly

variable {n p f ell : ℕ} [NeZero f]
variable {F K O k : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable {N : NormSource n F}
variable [Finite (Spin n F N)]

section OrdinarySource

variable (series : Irr K (Spin n F N) → Prop)
variable [MulAction (OuterGroup f) (OrdinarySeriesCarrier series)]
variable (diagonal : SpecialClifford n F →* DiagonalGroup)

/-- FLZ Theorem 3.10 on the actual selected ordinary characters. The
effective diagonal and field actions are the inverse-pullback conventions
bound to actual automorphisms by `EffectiveActionSource`. Applying the
published statement to inverse generators gives this identical clause.
The nontrivial-diagonal hypothesis is kept literally. -/
structure Theorem310Source : Prop where
  separate : ∀ (x : OrdinarySeriesCarrier series)
      (g : SpecialClifford n F) (e : FieldGroup f),
    g ∉ SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) →
    ((1, e) : OuterGroup f) • x = ((diagonal g, 1) : OuterGroup f) • x →
      ((1, e) : OuterGroup f) • x = x ∧
        ((diagonal g, 1) : OuterGroup f) • x = x

/-- The omitted trivial-diagonal case and inverse-generator conversion are
routine deductions from the precise source separation statement. -/
theorem ordinary_product_factorization
    (kernel : diagonal.ker =
      SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F))
    (source : Theorem310Source (N := N) (f := f) series diagonal)
    (x : OrdinarySeriesCarrier series) (g : SpecialClifford n F)
    (e : FieldGroup f) :
    ((diagonal g, 1) : OuterGroup f) • (((1, e) : OuterGroup f) • x) = x ↔
      ((diagonal g, 1) : OuterGroup f) • x = x ∧
        ((1, e) : OuterGroup f) • x = x := by
  constructor
  · intro h
    by_cases hg : g ∈ SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F)
    · have hd : diagonal g = 1 := by
        change g ∈ diagonal.ker
        rwa [kernel]
      have hpair : ((diagonal g, 1) : OuterGroup f) = 1 := by
        exact Prod.ext hd rfl
      rw [hpair, one_smul] at h ⊢
      exact ⟨rfl, h⟩
    · have hginv : g⁻¹ ∉
          SpinSubgroup n F N ⊔ Subgroup.center (SpecialClifford n F) := by
        intro hi
        apply hg
        simpa using (SpinSubgroup n F N ⊔
          Subgroup.center (SpecialClifford n F)).inv_mem hi
      have heq : ((1, e) : OuterGroup f) • x =
          ((diagonal g⁻¹, 1) : OuterGroup f) • x := by
        simpa only [map_inv, Prod.inv_mk, inv_one] using
          (eq_inv_smul_iff.mpr h)
      have he := (source.separate x g⁻¹ e hginv heq).1
      exact ⟨by simpa only [he] using h, he⟩
  · rintro ⟨hg, he⟩
    rw [he, hg]

end OrdinarySource

set_option maxHeartbeats 1200000 in
/-- The source-bound Spin stabilizer conclusion needed in Proposition 4.3.
All block equivalences used in the proof are obtained by the accepted
Lemma 4.2 theorem; none occurs among the inputs. -/
theorem brauer_product_factorization_of_lemma43_and_theorem310
    (rank_at_least_three : 3 ≤ n)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    {parameters : OddFieldParameters F p f}
    (fieldSource : FieldActionSource n F p f parameters N)
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
    (hinj : IrreducibleBrauerCharacterInjectivity iota)
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Finite source.family.Basic]
    [MulAction (OuterGroup f) source.family.Basic]
    [MulAction (OuterGroup f) (IBr iota)]
    [MulAction (OuterGroup f) (SpinBlock (k := k) (N := N))]
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (certificate : Theorem23Certificate Msys iota hcompat hinj source.family
      blocks source.blockSeries p 2)
    (ordinaryBlock : source.family.Basic → SpinBlock (k := k) (N := N))
    (forwardGenerator : ∀ x : source.family.Basic,
      (spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
        certificate hEll hOdd hNondef).linearEquiv (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet (irreducibleBrauerCharacterBlock iota hinj blocks) (ordinaryBlock x)))
    (ordinaryBlockEquivariant : ∀ (a : OuterGroup f)
        (x : source.family.Basic), ordinaryBlock (a • x) = a • ordinaryBlock x)
    (brauerBlockEquivariant : ∀ (a : OuterGroup f) (phi : IBr iota),
      irreducibleBrauerCharacterBlock iota hinj blocks (a • phi) =
        a • irreducibleBrauerCharacterBlock iota hinj blocks phi)
    (actions : EffectiveActionSource fieldSource iota hinj source.family.selectedSeries
      (spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
        certificate hEll hOdd hNondef))
    (ordinarySeparation : Theorem310Source (N := N) (f := f)
      source.family.selectedSeries actions.diagonal)
    (conlon : ∀ b : SpinBlock (k := k) (N := N),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (OuterGroup f) b))
    (burnside : ∀ b : SpinBlock (k := k) (N := N),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (OuterGroup f) b)) :
    ∀ (phi : IBr iota) (g : SpecialClifford n F) (e : FieldGroup f),
      ((actions.diagonal g, 1) : OuterGroup f) •
          (((1, e) : OuterGroup f) • phi) = phi ↔
        ((actions.diagonal g, 1) : OuterGroup f) • phi = phi ∧
          ((1, e) : OuterGroup f) • phi = phi := by
  classical
  let brauerBlock := irreducibleBrauerCharacterBlock iota hinj blocks
  have locals : RepresentativeEquivExists
      brauerBlock ordinaryBlock brauerBlockEquivariant := by
    intro omega
    let b : SpinBlock (k := k) (N := N) := orbitRepresentative omega
    let J := MulAction.stabilizer (OuterGroup f) b
    letI : MulAction J (BlockFibre ordinaryBlock b) :=
      stabilizerFibreAction ordinaryBlock ordinaryBlockEquivariant b
    letI : MulAction J (BlockFibre brauerBlock b) :=
      stabilizerFibreAction brauerBlock brauerBlockEquivariant b
    have accepted := lemma_4_3_spin_source_instantiated
      rank_at_least_three hEll hOdd hNondef fieldSource Msys iota hcompat hinj
      source blocks certificate ordinaryBlock forwardGenerator
      ordinaryBlockEquivariant brauerBlockEquivariant actions b (conlon b) (burnside b)
    obtain ⟨beta, hbeta⟩ := accepted.2.2
    refine ⟨beta, ?_⟩
    intro a ha x
    exact congrArg Subtype.val (hbeta (⟨a, ha⟩ : J) x)
  let family := RepresentativeEquivFamily.ofExists
    brauerBlock ordinaryBlock brauerBlockEquivariant locals
  let beta := RepresentativeEquivFamily.globalEquiv
    brauerBlock ordinaryBlock brauerBlockEquivariant ordinaryBlockEquivariant family
  have hbeta : ∀ (a : OuterGroup f) (phi : IBr iota),
      beta (a • phi) = a • beta phi :=
    RepresentativeEquivFamily.globalEquiv_equivariant
      brauerBlock ordinaryBlock brauerBlockEquivariant ordinaryBlockEquivariant family
  let diagonalHom : SpecialClifford n F →* OuterGroup f :=
    (MonoidHom.inl DiagonalGroup (FieldGroup f)).comp actions.diagonal
  let fieldHom : FieldGroup f →* OuterGroup f :=
    MonoidHom.inr DiagonalGroup (FieldGroup f)
  letI : MulAction (SpecialClifford n F) (IBr iota) :=
    MulAction.compHom (IBr iota) diagonalHom
  letI : MulAction (FieldGroup f) (IBr iota) :=
    MulAction.compHom (IBr iota) fieldHom
  letI : MulAction (SpecialClifford n F) source.family.Basic :=
    MulAction.compHom source.family.Basic diagonalHom
  letI : MulAction (FieldGroup f) source.family.Basic :=
    MulAction.compHom source.family.Basic fieldHom
  intro phi g e
  have ordinaryFactorization :
      ProductStabilizerFactorization
        (D := SpecialClifford n F) (E := FieldGroup f) (beta phi) := by
    intro d sigma
    exact ordinary_product_factorization (f := f) source.family.selectedSeries actions.diagonal
      actions.diagonal_kernel ordinarySeparation (beta phi) d sigma
  have transferred := brauerFactorization_of_ordinaryFactorization
    beta (fun d x => hbeta (diagonalHom d) x)
      (fun sigma x => hbeta (fieldHom sigma) x) phi ordinaryFactorization
  exact transferred g e

end ModularRep.PaperProofs.TypeBSpinStabilizerTransfer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
