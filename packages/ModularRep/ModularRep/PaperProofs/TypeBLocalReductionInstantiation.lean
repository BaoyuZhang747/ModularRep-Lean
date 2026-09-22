import ModularRep.PaperProofs.TypeBFixedRootCriterionFamilySplitting
import ModularRep.PaperProofs.TypeBFLZModularRootBinding
import ModularRep.BrauerCharacterCommonRootCompatibility
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# Local defect-zero reductions on the same modular-system roots

Navarro (3.18), p. 61, supplies the irreducible Brauer reduction of a
defect-zero ordinary character of one fixed finite group. The source below
retains that group, sufficient ordinary roots and the actual residue map
of the SAME modular system. Serre, Sections 12.1 and 12.3, especially
Theorem 24, p. 94, gives the ordinary interpretation over the displayed
splitting field. No ordinary algebraic closure is assumed.

The normalizer-quotient root is a restriction of the prescribed ambient
root. Its residue equation and agreement with the ambient convention are
proved. Reduction uniqueness follows from equality of the actual Brauer
functions. The selected representative is exactly the one used by the
existing literal local-extension construction.

The downstairs specified block compatibility remains a separate input.
Navarro (4.8), p. 84, and (4.18), p. 90, explain radicality of the usual
set of weights; they do not identify a freely supplied local block selector.
Matching that selector and its normalizer inflation to specified blocks
uses the separate guarded decomposition-support interpretation. No whole
LocalReductionData, matching, extension or block-condition source is used.
-/

noncomputable section
set_option autoImplicit false

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBLocalReductionInstantiation

open ModularRep OrdinaryIrreducibleCharacter CharacterWeight
open CyclicOuterLemma37LiteralLocalExtension TypeBCriterionHypotheses
open TypeBFixedRootDefinitionFamily

/-- Calibration on the actual integral roots required by this finite group.
The equality concerns the residue map of the prescribed modular system. -/
def RootResidueCompatible {ell : ℕ} {K O k H : Type}
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [Group H] [Finite H] (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K H) : Prop :=
  ∀ z : O, z ^ primeRegularExponent ell H = 1 →
    iota.lift (Msys.residue z) = algebraMap O K z

/-- The fixed-group Navarro (3.18) statement with its splitting and literal
modular-system calibration retained as constructor indices. -/
structure ScopedDefectZeroReductionSource {ell : ℕ} {K O k H : Type}
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [Group H] [finiteGroup : Finite H]
    [residueCharacteristic : CharP k ell] [residueClosure : IsAlgClosed k]
    [ordinaryCharacteristic : CharZero K]
    (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K H)
    (calibration : RootResidueCompatible Msys iota)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card H)] : Prop where
  reduction : ∀ chi : Irr K H,
    ModularRep.IsDefectZeroOrdinaryCharacter ell chi →
    ∃ phi : IBr iota, ∀ x : PrimeRegularElement (G := H) ell,
      chi x.val = phi.val x

section Roots

variable {ell : ℕ} {K O k G : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [Group G] [Finite G]

/-- Two literal order divisibilities, with no radicality assumption. -/
theorem local_order_dvd (Q : Subgroup G) :
    Nat.card (NormalizerQuotient Q) ∣ Nat.card G :=
  (Subgroup.card_quotient_dvd_card
    (Q.subgroupOf (Subgroup.normalizer (Q : Set G)))).trans
    (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (Q : Set G)))

theorem local_exponent_dvd (Q : Subgroup G) :
    primeRegularExponent ell (NormalizerQuotient Q) ∣
      primeRegularExponent ell G := by
  simpa only [primeRegularExponent] using
    Nat.ordCompl_dvd_ordCompl_of_dvd (local_order_dvd Q) ell

/-- The exact normalizer quotient uses the restriction of the SAME root. -/
def localRoot (iotaG : PrimeRegularRootEmbedding ell k K G) (Q : Subgroup G) :
    PrimeRegularRootEmbedding ell k K (NormalizerQuotient Q) :=
  PrimeRegularRootEmbedding.ofCommonRoot iotaG.prime iotaG.toMulEquiv
    (local_exponent_dvd (ell := ell) Q)

theorem localRoot_agrees (iotaG : PrimeRegularRootEmbedding ell k K G)
    (Q : Subgroup G)
    (z : rootsOfUnity (primeRegularExponent ell (NormalizerQuotient Q)) k) :
    (localRoot iotaG Q).lift ((z : kˣ) : k) = iotaG.lift ((z : kˣ) : k) := by
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion
    (local_exponent_dvd (ell := ell) Q) z
  calc
    (localRoot iotaG Q).lift ((z : kˣ) : k) =
        (localRoot iotaG Q).liftRoot z := (localRoot iotaG Q).lift_coe z
    _ = iotaG.liftRoot included := rfl
    _ = iotaG.lift ((included : kˣ) : k) := (iotaG.lift_coe included).symm
    _ = iotaG.lift ((z : kˣ) : k) := rfl

/-- Restriction preserves the actual residue calibration. -/
theorem localRoot_residue (Msys : ModularSystem ell K O k)
    (iotaG : PrimeRegularRootEmbedding ell k K G)
    (calibration : RootResidueCompatible Msys iotaG) (Q : Subgroup G) :
    RootResidueCompatible Msys (localRoot iotaG Q) := by
  intro z hz
  letI : NeZero (primeRegularExponent ell (NormalizerQuotient Q)) :=
    ⟨(primeRegularExponent_pos ell (NormalizerQuotient Q)).ne'⟩
  let zbar : rootsOfUnity (primeRegularExponent ell (NormalizerQuotient Q)) k :=
    rootsOfUnity.mkOfPowEq (Msys.residue z) (by rw [← map_pow, hz, map_one])
  have hval : ((zbar : kˣ) : k) = Msys.residue z := rfl
  rw [← hval, localRoot_agrees, hval]
  apply calibration
  obtain ⟨d, hd⟩ := local_exponent_dvd (ell := ell) Q
  rw [hd, pow_mul, hz, one_pow]

/-- Sufficient roots for the ambient group supply this exact local guard. -/
def localOrdinaryRoots [HasEnoughRootsOfUnity K (Nat.card G)] (Q : Subgroup G) :
    HasEnoughRootsOfUnity K (Nat.card (NormalizerQuotient Q)) :=
  HasEnoughRootsOfUnity.of_dvd K (local_order_dvd Q)

end Roots

section Reduction

variable {ell : ℕ} {K O k H : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [Group H] [Finite H] [CharP k ell] [IsAlgClosed k] [CharZero K]

/-- Uniqueness requires no extra character-theoretic source. -/
theorem reduction_unique (iota : PrimeRegularRootEmbedding ell k K H)
    (chi : Irr K H) (phi psi : IBr iota)
    (hphi : ∀ x : PrimeRegularElement (G := H) ell, chi x.val = phi.val x)
    (hpsi : ∀ x : PrimeRegularElement (G := H) ell, chi x.val = psi.val x) :
    phi = psi := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  exact (hphi x).symm.trans (hpsi x)

theorem existsUnique_reduction (Msys : ModularSystem ell K O k)
    (iota : PrimeRegularRootEmbedding ell k K H)
    (calibration : RootResidueCompatible Msys iota)
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (source : ScopedDefectZeroReductionSource Msys iota calibration)
    (chi : Irr K H) (hchi : ModularRep.IsDefectZeroOrdinaryCharacter ell chi) :
    ∃! phi : IBr iota, ∀ x : PrimeRegularElement (G := H) ell,
      chi x.val = phi.val x := by
  obtain ⟨phi, hphi⟩ := source.reduction chi hchi
  exact ⟨phi, hphi, fun psi hpsi => reduction_unique iota chi psi phi hpsi hphi⟩

end Reduction

section Selected

variable {ell : ℕ} {K O k G B : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  [Group G] [Fintype G] [Fintype B] [MulAction (MulAut G)ᵐᵒᵖ B]
  [HasEnoughRootsOfUnity K (Nat.card G)]
  (Msys : ModularSystem ell K O k)
  (iotaG : PrimeRegularRootEmbedding ell k K G)
  (calibration : RootResidueCompatible Msys iotaG)
  (navarro : ∀ (H : Type) [Group H] [Finite H]
    [HasEnoughRootsOfUnity K (Nat.card H)]
    (iota : PrimeRegularRootEmbedding ell k K H)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (blockSource : LocalBlockInductionSource
    (p := ell) (k := k) (K := K) (G := G) (Block := B))

/-- Select the actual reduction of the existing selected raw representative.
The uniform E1 input is guarded separately for each finite local group. -/
def selectedReduction (b : B) (w : LiteralWeightFibre blockSource b) :
    SelectedLocalReductionSource blockSource b w := by
  let W := selectedCharacterWeight blockSource b w
  letI := localOrdinaryRoots (K := K) W.subgroup
  let root := localRoot iotaG W.subgroup
  let source := navarro (NormalizerQuotient W.subgroup) root
    (localRoot_residue Msys iotaG calibration W.subgroup)
  let result := source.reduction W.localCharacter W.defectZero
  exact {
    iota := root
    brauer := Classical.choose result
    reduction := Classical.choose_spec result }

@[simp]
theorem selectedReduction_iota (b : B) (w : LiteralWeightFibre blockSource b) :
    (selectedReduction Msys iotaG calibration navarro blockSource b w).iota =
      localRoot iotaG (SelectedRadical blockSource b w) := rfl

theorem selectedReduction_value (b : B) (w : LiteralWeightFibre blockSource b)
    (x : PrimeRegularElement (G := NormalizerQuotient
      (SelectedRadical blockSource b w)) ell) :
    (selectedCharacterWeight blockSource b w).localCharacter x.val =
      (selectedReduction Msys iotaG calibration navarro blockSource b w).brauer.val x :=
  (selectedReduction Msys iotaG calibration navarro blockSource b w).reduction x

theorem selectedReduction_rootAgreement (b : B)
    (w : LiteralWeightFibre blockSource b) :
    QuotientRootAgreement iotaG (SelectedRadical blockSource b w)
      (selectedReduction Msys iotaG calibration navarro blockSource b w).iota :=
  localRoot_agrees iotaG (SelectedRadical blockSource b w)

end Selected

section Criterion

variable {ell : ℕ} {K O k M : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K] [Group M] [Finite M]
  (G : Subgroup M) [G.Normal]

local instance ambientFintype : Fintype M := Fintype.ofFinite _
local instance subgroupFintype : Fintype G := Fintype.ofFinite _

variable [Fintype (LiteralPrimitiveBlock k M)] [Fintype (LiteralPrimitiveBlock k G)]

/-- The entire local-reduction domain is derived. Specified block compatibility
is explicit and concerns the SAME downstairs operations, independently of E1
defect-zero reduction existence. -/
def localReductionData (Msys : ModularSystem ell K O k)
    (iotaG : PrimeRegularRootEmbedding ell k K G)
    (calibration : RootResidueCompatible Msys iotaG)
    [HasEnoughRootsOfUnity K (Nat.card G)]
    (navarro : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)]
      (iota : PrimeRegularRootEmbedding ell k K H)
      (compatible : RootResidueCompatible Msys iota),
        ScopedDefectZeroReductionSource Msys iota compatible)
    (blocks : BlockData (ell := ell) (k := k) (K := K) G)
    (physical : GuardedBlockCompatibility iotaG blocks.weightDownstairs.operations) :
    LocalReductionData G iotaG blocks where
  blockCompatibility := physical
  reduction := selectedReduction Msys iotaG calibration navarro blocks.weightDownstairs
  rootAgreement := selectedReduction_rootAgreement Msys iotaG calibration navarro
    blocks.weightDownstairs

end Criterion

section Spin

open TypeBCliffordCarriers

variable {n ell : ℕ} {F K O k : Type}
  [Field F] [Finite F] [Finite (Clifford n F)]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (N : NormSource n F)
  [Fintype (LiteralPrimitiveBlock k (SpecialClifford n F))]
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]

local instance cliffordFintype : Fintype (SpecialClifford n F) := Fintype.ofFinite _
local instance spinFintype : Fintype (Spin n F N) := Fintype.ofFinite _

/-- The actual Spin instance has no separate root, calibration, splitting or
whole-local-reduction input: these use the SAME Msys and cyclotomic choice. -/
def localReductionData_modular_instantiated (Msys : ModularSystem ell K O k)
    (choice : TypeBFLZCyclotomicModel.Choice (F := F) (n := n) K)
    (navarro : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)]
      (iota : PrimeRegularRootEmbedding ell k K H)
      (compatible : RootResidueCompatible Msys iota),
        ScopedDefectZeroReductionSource Msys iota compatible)
    (blocks : BlockData (ell := ell) (k := k) (K := K) (SpinSubgroup n F N))
    (physical : GuardedBlockCompatibility
      (TypeBFLZModularRootBinding.spinRoot Msys choice N)
      blocks.weightDownstairs.operations) :
    LocalReductionData (SpinSubgroup n F N)
      (TypeBFLZModularRootBinding.spinRoot Msys choice N) blocks := by
  letI := choice.ordinaryRoots
  letI : HasEnoughRootsOfUnity K (Nat.card (Spin n F N)) :=
    HasEnoughRootsOfUnity.of_dvd K
      (Subgroup.card_subgroup_dvd_card (SpinSubgroup n F N))
  exact localReductionData (SpinSubgroup n F N) Msys
    (TypeBFLZModularRootBinding.spinRoot Msys choice N)
    (TypeBFLZModularRootBinding.spinRoot_residue Msys choice N)
    navarro blocks physical

end Spin

end ModularRep.PaperProofs.TypeBLocalReductionInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
