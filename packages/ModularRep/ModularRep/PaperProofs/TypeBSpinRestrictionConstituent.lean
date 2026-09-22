import ModularRep.PaperProofs.TypeBSpinStabilizerTransfer
import ModularRep.BrauerCharacterCommonRootCompatibility
import ModularRep.NavarroCoveringBrauerExtension

/-!
# A literal Spin constituent with the derived stabilizer factorization

The subgroup root convention is the restriction of the prescribed special
Clifford root convention. The ambient character is therefore unchanged.
The E1 restriction input is a nonzero nonnegative expansion of the actual
restricted class function: Navarro (2.2)(d), pp. 18--19, and (2.3), p. 19,
with the characteristic-zero realization made on the displayed fields.

Lean selects a nonzero coefficient, interprets it through the existing
literal `BrauerOccursInRestriction` definition, and invokes the accepted
Spin Lemma-4.3/Theorem-3.10 transfer. No arbitrary lies-over relation or
constituent-with-stabilizer-factorization assertion is supplied.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBSpinRestrictionConstituent

open ModularRep
open BlockFibreRestriction DecompositionBasicSetBridge ExactGrothendieckGroup
open FDRepSimpleClassKZero OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBSpinStabilizer TypeBSpinConlonBlockSourceInstantiation
open TypeBSpinStabilizerTransfer TypeBIntegralSeriesCertificate
open TypeBSpecialCliffordActionAdapter ConlonBasicSet
open NavarroCoveringBrauerExtension

variable {n p f ell : ℕ} [NeZero f]
variable {F K O k : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable (N : NormSource n F)
variable [Finite (SpecialClifford n F)]

/-- The actual subgroup order gives the divisibility needed for restricting
the single ambient prime regular root convention. -/
theorem spin_exponent_dvd :
    primeRegularExponent ell (Spin n F N) ∣
      primeRegularExponent ell (SpecialClifford n F) := by
  simpa only [primeRegularExponent] using
    Nat.ordCompl_dvd_ordCompl_of_dvd
      (Subgroup.card_subgroup_dvd_card (SpinSubgroup n F N)) ell

/-- The Spin root lift is constructed by restriction of the fixed ambient
root equivalence. It is not an independent convention to be matched later. -/
def spinRoot (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F)) :
    PrimeRegularRootEmbedding ell k K (Spin n F N) :=
  PrimeRegularRootEmbedding.ofCommonRoot iotaA.prime iotaA.toMulEquiv
    (spin_exponent_dvd (ell := ell) N)

/-- The derived Spin and prescribed special Clifford lifts agree on every
root used by Spin. The proof concerns those roots, not the zero extension
of each lift to the entire modular coefficient field. -/
theorem spinRoot_agrees
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (z : rootsOfUnity (primeRegularExponent ell (Spin n F N)) k) :
    (spinRoot N iotaA).lift (((z : kˣ) : k)) = iotaA.lift (((z : kˣ) : k)) := by
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion
    (spin_exponent_dvd (ell := ell) N) z
  calc
    (spinRoot N iotaA).lift (((z : kˣ) : k)) =
        (spinRoot N iotaA).liftRoot z := (spinRoot N iotaA).lift_coe z
    _ = iotaA.liftRoot included := rfl
    _ = iotaA.lift (((included : kˣ) : k)) := (iotaA.lift_coe included).symm
    _ = iotaA.lift (((z : kˣ) : k)) := rfl

/-- Existing representation pullback compatibility specializes to this
literal subgroup and to the derived root convention. -/
theorem spin_brauer_pullback
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (V : FDRep k (SpecialClifford n F)) :
    Representation.brauerCharacterOfRootEmbedding
        (Representation.pullback V.ρ (SpinSubgroup n F N).subtype) (spinRoot N iotaA) =
      PrimeRegularClassFunction.pullback (SpinSubgroup n F N).subtype
        (Representation.brauerCharacterOfRootEmbedding V.ρ iotaA) :=
  Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
    V.ρ iotaA (spinRoot N iotaA) (SpinSubgroup n F N).subtype
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      V.ρ iotaA (spinRoot N iotaA) (SpinSubgroup n F N).subtype
      (spinRoot_agrees N iotaA))

/-- Narrow E1/U positive restriction expansion, on exactly the actual
character functions and the derived subgroup root. Navarro (2.2)(d) and
(2.3), pp. 18--19, give the expansion; restriction preserves the positive
dimension of an irreducible representation, so its multiplicity vector is
nonzero. The realization in an arbitrary characteristic-zero `K` remains
part of this exact source binding. No constituent or factorization target
is chosen by the source packet. -/
structure RestrictionExpansionSource
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F)) where
  multiplicity : IBr iotaA → IBr (spinRoot N iotaA) →₀ ℕ
  nonzero : ∀ Phi : IBr iotaA, multiplicity Phi ≠ 0
  value : ∀ (Phi : IBr iotaA) (x : PrimeRegularElement (G := Spin n F N) ell),
    Phi.1 (PrimeRegularElement.map (SpinSubgroup n F N).subtype x) =
      (multiplicity Phi).sum (fun phi m => (m : K) * phi.1 x)

/-- A nonzero source coefficient yields an actual constituent according
to the already defined finite nonnegative expansion predicate. -/
theorem exists_spin_constituent
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (restriction : RestrictionExpansionSource N iotaA) (Phi : IBr iotaA) :
    ∃ phi : IBr (spinRoot N iotaA),
      BrauerOccursInRestriction (SpinSubgroup n F N) iotaA (spinRoot N iotaA) Phi phi := by
  classical
  have hexists : ∃ phi, restriction.multiplicity Phi phi ≠ 0 := by
    by_contra h
    apply restriction.nonzero Phi
    ext phi
    exact not_not.mp (fun hphi => h ⟨phi, hphi⟩)
  obtain ⟨phi, hphi⟩ := hexists
  exact ⟨phi, restriction.multiplicity Phi, hphi, restriction.value Phi⟩

set_option maxHeartbeats 1400000 in
/-- Each actual special Clifford Brauer character has a literal Spin
constituent satisfying the stabilizer separation already deduced from the
accepted Spin window. The E1 source input contains only the positive
restriction expansion; factorization is obtained by invoking that window.
-/
theorem exists_spin_constituent_with_factorization
    (rank_at_least_three : 3 ≤ n)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    {parameters : OddFieldParameters F p f}
    (fieldSource : FieldActionSource n F p f parameters N)
    (Msys : ModularSystem ell K O k)
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (restriction : RestrictionExpansionSource N iotaA)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys (spinRoot N iotaA))
    (hinj : IrreducibleBrauerCharacterInjectivity (spinRoot N iotaA))
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Finite source.family.Basic]
    [MulAction (OuterGroup f) source.family.Basic]
    [MulAction (OuterGroup f) (IBr (spinRoot N iotaA))]
    [MulAction (OuterGroup f) (SpinBlock (k := k) (N := N))]
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (certificate : Theorem23Certificate Msys (spinRoot N iotaA) hcompat hinj source.family
      blocks source.blockSeries p 2)
    (ordinaryBlock : source.family.Basic → SpinBlock (k := k) (N := N))
    (forwardGenerator : ∀ x : source.family.Basic,
      (spinBasicSetFromTheorem23 Msys (spinRoot N iotaA) hcompat hinj source blocks
        certificate hEll hOdd hNondef).linearEquiv (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet (irreducibleBrauerCharacterBlock (spinRoot N iotaA) hinj blocks)
            (ordinaryBlock x)))
    (ordinaryBlockEquivariant : ∀ (a : OuterGroup f)
        (x : source.family.Basic), ordinaryBlock (a • x) = a • ordinaryBlock x)
    (brauerBlockEquivariant : ∀ (a : OuterGroup f) (phi : IBr (spinRoot N iotaA)),
      irreducibleBrauerCharacterBlock (spinRoot N iotaA) hinj blocks (a • phi) =
        a • irreducibleBrauerCharacterBlock (spinRoot N iotaA) hinj blocks phi)
    (actions : EffectiveActionSource fieldSource (spinRoot N iotaA) hinj
      source.family.selectedSeries
      (spinBasicSetFromTheorem23 Msys (spinRoot N iotaA) hcompat hinj source blocks
        certificate hEll hOdd hNondef))
    (ordinarySeparation : Theorem310Source (N := N) (f := f)
      source.family.selectedSeries actions.diagonal)
    (conlon : ∀ b : SpinBlock (k := k) (N := N),
      PadicConlonMarkDetection.{0, 0} (p := 2)
        (A := MulAction.stabilizer (OuterGroup f) b))
    (burnside : ∀ b : SpinBlock (k := k) (N := N),
      PublishedBurnsideMarkInjectivity.{0, 0}
        (A := MulAction.stabilizer (OuterGroup f) b))
    (Phi : IBr iotaA) :
    ∃ phi : IBr (spinRoot N iotaA),
      BrauerOccursInRestriction (SpinSubgroup n F N) iotaA (spinRoot N iotaA) Phi phi ∧
      ∀ (g : SpecialClifford n F) (e : FieldGroup f),
        ((actions.diagonal g, 1) : OuterGroup f) •
            (((1, e) : OuterGroup f) • phi) = phi ↔
          ((actions.diagonal g, 1) : OuterGroup f) • phi = phi ∧
            ((1, e) : OuterGroup f) • phi = phi := by
  obtain ⟨phi, hphi⟩ := exists_spin_constituent N iotaA restriction Phi
  refine ⟨phi, hphi, ?_⟩
  exact brauer_product_factorization_of_lemma43_and_theorem310
    rank_at_least_three hEll hOdd hNondef fieldSource Msys (spinRoot N iotaA) hcompat hinj
    source blocks certificate ordinaryBlock forwardGenerator ordinaryBlockEquivariant
    brauerBlockEquivariant actions ordinarySeparation conlon burnside phi

end ModularRep.PaperProofs.TypeBSpinRestrictionConstituent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
