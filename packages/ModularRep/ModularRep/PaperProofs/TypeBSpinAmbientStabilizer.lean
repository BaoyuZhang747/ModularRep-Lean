import ModularRep.PaperProofs.TypeBAutomorphismSource
import ModularRep.PaperProofs.TypeBSpinStabilizerTransfer
import ModularRep.PaperProofs.TypeBSpinRestrictionConstituent
import ModularRep.CyclicOuterBrauerExtension

/-!
# From the effective Spin action to the actual ambient inertia

The ambient carrier is the literal special Clifford / field semidirect
product of `TypeBWeightStabilizerSource`. Its natural homomorphism to Spin
automorphisms is `TypeBAutomorphismSource.ambientAutomorphism`.

The existing effective-action certificate gives exact K_0 formulas, with
labelled generators. Applying the checked Brauer-character homomorphism
and its twist naturality derives those same formulas on literal IBr.
No further character-action compatibility input is needed.

The final endpoint invokes the accepted Spin Lemma 4.2 / FLZ Theorem 3.10
deduction and converts its factorization to a literal product of inertia
subgroup images in the actual ambient semidirect product. It assumes no
factorizing Brauer character or constituent, and no criterion target.
-/

noncomputable section

open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBSpinAmbientStabilizer

open ModularRep
open ModularRep.BlockFibreRestriction
open ModularRep.DecompositionBasicSetBridge
open ModularRep.ExactGrothendieckGroup
open ModularRep.FDRepSimpleClassKZero
open ModularRep.OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBSpinStabilizer
open TypeBSpinConlonBlockSourceInstantiation TypeBSpinStabilizerTransfer
open TypeBIntegralSeriesCertificate TypeBSpecialCliffordActionAdapter
open TypeBWeightStabilizerSource TypeBAutomorphismSource
open CyclicOuterLemma37Concrete ConlonBasicSet OddConformalProposition311Relative
open TypeBSpinRestrictionConstituent NavarroCoveringBrauerExtension

variable {n p f ell : ℕ} [NeZero f]
variable {F K O k : Type}
variable [Field F] [Finite F] [CharP F p]
variable [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
variable [CharZero K] [IsAlgClosed K] [CharP k ell] [IsAlgClosed k]
variable {N : NormSource n F} [Finite (Spin n F N)]
variable {parameters : OddFieldParameters F p f}
variable (fieldSource : FieldActionSource n F p f parameters N)
variable (iota : PrimeRegularRootEmbedding ell k K (Spin n F N))
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)

/-- The actual modular generator evaluates to the very same Brauer
character. This also fixes the root realization in the comparison. -/
theorem brauer_generator_value (phi : IBr iota) :
    brauerCharacterKZeroHom iota
        (labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
          (MonoidAlgebra.single phi 1)) = phi.1 := by
  rw [labelledSimpleClassKZero_single, simpleClassToFDRepKZeroGenerator,
    brauerCharacterKZeroHom_classOf]
  exact congrArg Subtype.val ((simpleModuleClassEquivIBr iota hinj).apply_symm_apply phi)

section EffectiveActionComparison

variable (series : Irr K (Spin n F N) → Prop)
variable [MulAction (OuterGroup f) (OrdinarySeriesCarrier series)]
variable [MulAction (OuterGroup f) (IBr iota)]
variable [MulAction (OuterGroup f) (SpinBlock (k := k) (N := N))]
variable {decomposition : FDRepKZero K (Spin n F N) →+ FDRepKZero k (Spin n F N)}
variable (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
  (OrdinarySeriesCarrier series) decomposition)
variable (actions : EffectiveActionSource fieldSource iota hinj series basicSet)

include hinj series basicSet actions

/-- Exact K_0 generator compatibility forces literal Brauer-character
compatibility. The final applications use the two existing action fields. -/
theorem effective_smul_eq_twist
    (a : OuterGroup f) (alpha : MulAut (Spin n F N))
    (htwist : ∀ z : FDRepKZero k (Spin n F N),
      actions.labelled.modularAction a z = twistKZero (k := k) alpha z)
    (phi : IBr iota) :
    a • phi = IrreducibleBrauerCharacter.twist iota phi alpha := by
  let generator (psi : IBr iota) :=
    labelledSimpleClassKZero (simpleModuleClassEquivIBr iota hinj).symm
      (MonoidAlgebra.single psi 1)
  have h := actions.labelled.modular_single a phi
  change generator (a • phi) = actions.labelled.modularAction a (generator phi) at h
  rw [htwist] at h
  apply Subtype.ext
  change (a • phi).1 = phi.1.twist alpha
  calc
    (a • phi).1 = brauerCharacterKZeroHom iota (generator (a • phi)) :=
      (brauer_generator_value iota hinj (a • phi)).symm
    _ = brauerCharacterKZeroHom iota (twistKZero (k := k) alpha (generator phi)) :=
      congrArg (brauerCharacterKZeroHom iota) h
    _ = phi.1.twist alpha := by
      have ht := DFunLike.congr_fun (brauerCharacterKZeroHom_twist iota alpha) (generator phi)
      change brauerCharacterKZeroHom iota (twistKZero (k := k) alpha (generator phi)) =
        (brauerCharacterKZeroHom iota (generator phi)).twist alpha at ht
      have hv : brauerCharacterKZeroHom iota (generator phi) = phi.1 :=
        brauer_generator_value iota hinj phi
      rw [hv] at ht
      exact ht

theorem diagonal_smul_eq_twist (g : SpecialClifford n F) (phi : IBr iota) :
    ((actions.diagonal g, 1) : OuterGroup f) • phi =
      IrreducibleBrauerCharacter.twist iota phi
        (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹) :=
  effective_smul_eq_twist fieldSource iota hinj series basicSet actions
    (actions.diagonal g, 1) (MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹)
    (actions.modular_diagonal g) phi

theorem field_smul_eq_twist (e : FieldGroup f) (phi : IBr iota) :
    ((1, e) : OuterGroup f) • phi =
      IrreducibleBrauerCharacter.twist iota phi (spinFieldAction n F fieldSource e⁻¹) :=
  effective_smul_eq_twist fieldSource iota hinj series basicSet actions
    (1, e) (spinFieldAction n F fieldSource e⁻¹) (actions.modular_field e) phi

end EffectiveActionComparison

/-- The canonical actual ambient action; it is constructed from the
natural automorphism homomorphism, not supplied as an instance. -/
@[instance_reducible]
def ambientBrauerAction : MulAction (Ambient fieldSource) (IBr iota) :=
  rightAutomorphismAction (X := IBr iota) (ambientAutomorphism fieldSource)

/-- The literal ambient Brauer inertia under that canonical action. -/
def ambientBrauerInertia (phi : IBr iota) : Subgroup (Ambient fieldSource) :=
  (MulAction.stabilizer (MulAut (Spin n F N))ᵐᵒᵖ phi).comap
    (inverseOpHom (ambientAutomorphism fieldSource))

/-- The actual special Clifford inertia embedded by the semidirect left
inclusion. -/
def specialCliffordInertiaImage (phi : IBr iota) : Subgroup (Ambient fieldSource) :=
  ((ambientBrauerInertia fieldSource iota phi).comap
    (SemidirectProduct.inl : SpecialClifford n F →* Ambient fieldSource)).map
      SemidirectProduct.inl

/-- The actual field inertia embedded by the semidirect right inclusion. -/
def fieldInertiaImage (phi : IBr iota) : Subgroup (Ambient fieldSource) :=
  ((ambientBrauerInertia fieldSource iota phi).comap
    (SemidirectProduct.inr : FieldGroup f →* Ambient fieldSource)).map
      SemidirectProduct.inr

section AmbientComparison

variable (series : Irr K (Spin n F N) → Prop)
variable [MulAction (OuterGroup f) (OrdinarySeriesCarrier series)]
variable [MulAction (OuterGroup f) (IBr iota)]
variable [MulAction (OuterGroup f) (SpinBlock (k := k) (N := N))]
variable {decomposition : FDRepKZero K (Spin n F N) →+ FDRepKZero k (Spin n F N)}
variable (basicSet : RestrictedIntegralBasicSetOnIBr iota hinj
  (OrdinarySeriesCarrier series) decomposition)
variable (actions : EffectiveActionSource fieldSource iota hinj series basicSet)

include hinj series basicSet actions

theorem ambient_inl_smul (g : SpecialClifford n F) (phi : IBr iota) :
    let _ : MulAction (Ambient fieldSource) (IBr iota) :=
      ambientBrauerAction fieldSource iota
    (SemidirectProduct.inl g : Ambient fieldSource) • phi =
      ((actions.diagonal g, 1) : OuterGroup f) • phi := by
  change IrreducibleBrauerCharacter.twist iota phi
    (ambientAutomorphism fieldSource (SemidirectProduct.inl g : Ambient fieldSource)⁻¹) = _
  have h : ambientAutomorphism fieldSource
      (SemidirectProduct.inl g : Ambient fieldSource)⁻¹ =
      MulAut.conjNormal (H := SpinSubgroup n F N) g⁻¹ := by
    simp only [map_inv, ambientAutomorphism_inl]
  rw [h]
  exact (diagonal_smul_eq_twist fieldSource iota hinj series basicSet actions g phi).symm

theorem ambient_inr_smul (e : FieldGroup f) (phi : IBr iota) :
    let _ : MulAction (Ambient fieldSource) (IBr iota) :=
      ambientBrauerAction fieldSource iota
    (SemidirectProduct.inr e : Ambient fieldSource) • phi =
      ((1, e) : OuterGroup f) • phi := by
  change IrreducibleBrauerCharacter.twist iota phi
    (ambientAutomorphism fieldSource (SemidirectProduct.inr e : Ambient fieldSource)⁻¹) = _
  have h : ambientAutomorphism fieldSource
      (SemidirectProduct.inr e : Ambient fieldSource)⁻¹ =
      spinFieldAction n F fieldSource e⁻¹ := by
    simp only [map_inv, ambientAutomorphism_inr]
  rw [h]
  exact (field_smul_eq_twist fieldSource iota hinj series basicSet actions e phi).symm

/-- A deduction helper, consumed below with the already proved effective
factorization. Its hypothesis is not a source certificate. -/
theorem ambient_inertia_product_of_effective
    (phi : IBr iota)
    (factorization : ∀ (g : SpecialClifford n F) (e : FieldGroup f),
      ((actions.diagonal g, 1) : OuterGroup f) •
          (((1, e) : OuterGroup f) • phi) = phi ↔
        ((actions.diagonal g, 1) : OuterGroup f) • phi = phi ∧
          ((1, e) : OuterGroup f) • phi = phi) :
    (ambientBrauerInertia fieldSource iota phi : Set (Ambient fieldSource)) =
      (specialCliffordInertiaImage fieldSource iota phi : Set (Ambient fieldSource)) *
        (fieldInertiaImage fieldSource iota phi : Set (Ambient fieldSource)) := by
  letI : MulAction (Ambient fieldSource) (IBr iota) := ambientBrauerAction fieldSource iota
  have hm : ∀ (g : SpecialClifford n F) (psi : IBr iota),
      (SemidirectProduct.inl g : Ambient fieldSource) • psi =
        ((actions.diagonal g, 1) : OuterGroup f) • psi :=
    ambient_inl_smul fieldSource iota hinj series basicSet actions
  have he : ∀ (e : FieldGroup f) (psi : IBr iota),
      (SemidirectProduct.inr e : Ambient fieldSource) • psi =
        ((1, e) : OuterGroup f) • psi :=
    ambient_inr_smul fieldSource iota hinj series basicSet actions
  have hc : ∀ (g : SpecialClifford n F) (e : FieldGroup f),
      (SemidirectProduct.inl g : Ambient fieldSource) •
          ((SemidirectProduct.inr e : Ambient fieldSource) • phi) = phi ↔
        (SemidirectProduct.inl g : Ambient fieldSource) • phi = phi ∧
          (SemidirectProduct.inr e : Ambient fieldSource) • phi = phi := by
    intro g e
    simpa only [hm, he] using factorization g e
  ext a
  constructor
  · intro ha
    have ha' : a • phi = phi := ha
    have hcombined : (SemidirectProduct.inl a.left : Ambient fieldSource) •
        ((SemidirectProduct.inr a.right : Ambient fieldSource) • phi) = phi := by
      rw [← mul_smul, SemidirectProduct.inl_left_mul_inr_right]
      exact ha'
    obtain ⟨hl, hr⟩ := (hc a.left a.right).mp hcombined
    exact Set.mem_mul.mpr ⟨SemidirectProduct.inl a.left,
      ⟨a.left, hl, rfl⟩, SemidirectProduct.inr a.right,
      ⟨a.right, hr, rfl⟩, SemidirectProduct.inl_left_mul_inr_right a⟩
  · intro ha
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp ha
    obtain ⟨g, hg, rfl⟩ := hx
    obtain ⟨e, he', rfl⟩ := hy
    exact (ambientBrauerInertia fieldSource iota phi).mul_mem hg he'

end AmbientComparison

set_option maxHeartbeats 1200000 in
/-- The actual ambient Brauer inertia factorization, derived by invoking
the accepted Spin window with the same non-conclusion source inputs. -/
theorem ambient_inertia_product_of_lemma43_and_theorem310
    (rank_at_least_three : 3 ≤ n)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    (Msys : ModularSystem ell K O k)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys iota)
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
        (A := MulAction.stabilizer (OuterGroup f) b))
    (phi : IBr iota) :
    (ambientBrauerInertia fieldSource iota phi : Set (Ambient fieldSource)) =
      (specialCliffordInertiaImage fieldSource iota phi : Set (Ambient fieldSource)) *
        (fieldInertiaImage fieldSource iota phi : Set (Ambient fieldSource)) := by
  have factorization := brauer_product_factorization_of_lemma43_and_theorem310
    rank_at_least_three hEll hOdd hNondef fieldSource Msys iota hcompat hinj
    source blocks certificate ordinaryBlock forwardGenerator ordinaryBlockEquivariant
    brauerBlockEquivariant actions ordinarySeparation conlon burnside phi
  exact ambient_inertia_product_of_effective fieldSource iota hinj source.family.selectedSeries
    (spinBasicSetFromTheorem23 Msys iota hcompat hinj source blocks
      certificate hEll hOdd hNondef) actions phi factorization

set_option maxHeartbeats 1400000 in
/-- The prescribed special Clifford Brauer character has an actual Spin
restriction constituent whose canonical ambient inertia factors. The Spin
root is derived from the prescribed ambient root. The positive restriction
source supplies no constituent or factorization; both are deductions. -/
theorem exists_spin_constituent_with_ambient_factorization
    [Finite (SpecialClifford n F)]
    (rank_at_least_three : 3 ≤ n)
    (hEll : Nat.Prime ell) (hOdd : Odd ell) (hNondef : ell ≠ p)
    (Msys : ModularSystem ell K O k)
    (iotaA : PrimeRegularRootEmbedding ell k K (SpecialClifford n F))
    (restriction : RestrictionExpansionSource N iotaA)
    (hcompat : StableReductionBrauerCharacterCompatibility Msys (spinRoot N iotaA))
    (hinjSpin : IrreducibleBrauerCharacterInjectivity (spinRoot N iotaA))
    (source : SpinRationalSeriesSource (p := p) (ell := ell) (K := K) (k := k) (N := N))
    [Finite source.family.Basic]
    [MulAction (OuterGroup f) source.family.Basic]
    [MulAction (OuterGroup f) (IBr (spinRoot N iotaA))]
    [MulAction (OuterGroup f) (SpinBlock (k := k) (N := N))]
    [Fintype (SpinBlock (k := k) (N := N))]
    (blocks : BlockIdempotentDecomposition (blockIdempotent (k := k) (N := N)))
    (certificate : Theorem23Certificate Msys (spinRoot N iotaA) hcompat hinjSpin source.family
      blocks source.blockSeries p 2)
    (ordinaryBlock : source.family.Basic → SpinBlock (k := k) (N := N))
    (forwardGenerator : ∀ x : source.family.Basic,
      (spinBasicSetFromTheorem23 Msys (spinRoot N iotaA) hcompat hinjSpin source blocks
        certificate hEll hOdd hNondef).linearEquiv (MonoidAlgebra.single x 1) ∈
        MonoidAlgebra.supported ℤ ℤ
          (blockFibreSet (irreducibleBrauerCharacterBlock (spinRoot N iotaA) hinjSpin blocks)
            (ordinaryBlock x)))
    (ordinaryBlockEquivariant : ∀ (a : OuterGroup f)
        (x : source.family.Basic), ordinaryBlock (a • x) = a • ordinaryBlock x)
    (brauerBlockEquivariant : ∀ (a : OuterGroup f) (phi : IBr (spinRoot N iotaA)),
      irreducibleBrauerCharacterBlock (spinRoot N iotaA) hinjSpin blocks (a • phi) =
        a • irreducibleBrauerCharacterBlock (spinRoot N iotaA) hinjSpin blocks phi)
    (actions : EffectiveActionSource fieldSource (spinRoot N iotaA) hinjSpin
      source.family.selectedSeries
      (spinBasicSetFromTheorem23 Msys (spinRoot N iotaA) hcompat hinjSpin source blocks
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
      (ambientBrauerInertia fieldSource (spinRoot N iotaA) phi : Set (Ambient fieldSource)) =
        (specialCliffordInertiaImage fieldSource (spinRoot N iotaA) phi :
            Set (Ambient fieldSource)) *
          (fieldInertiaImage fieldSource (spinRoot N iotaA) phi : Set (Ambient fieldSource)) := by
  obtain ⟨phi, hphi⟩ := exists_spin_constituent N iotaA restriction Phi
  refine ⟨phi, hphi, ?_⟩
  exact ambient_inertia_product_of_lemma43_and_theorem310 fieldSource (spinRoot N iotaA) hinjSpin
    rank_at_least_three hEll hOdd hNondef Msys hcompat source blocks certificate
    ordinaryBlock forwardGenerator ordinaryBlockEquivariant brauerBlockEquivariant
    actions ordinarySeparation conlon burnside phi

end ModularRep.PaperProofs.TypeBSpinAmbientStabilizer


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
