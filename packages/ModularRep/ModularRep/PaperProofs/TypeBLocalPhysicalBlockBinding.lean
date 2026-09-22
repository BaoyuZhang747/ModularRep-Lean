import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.PaperProofs.TypeBModularGroupRootBinding
import ModularRep.PaperProofs.TypeBOrdinaryBlockSplitting
import ModularRep.OrdinaryBlockFibre

/-!
# Specified blocks of the actual inflated local characters

The finite group decomposition input reconstructs an ordinary character
from its actual stable-lattice simple-factor coordinates, using the SAME
modular system and its constructed root convention. Navarro (2.9), p. 23,
supplies this routine statement in the displayed splitting scope. Linear
independence proves that an irreducible reduction has row single phi 1.

The existing ordinary-block source binds nonzero specified decomposition
numbers to actual primitive idempotents, as in Navarro (3.3), (3.11) and
(3.13)(b). The operations-specific input concerns ONLY ordinary inflation:
the block of the literal inflated quotient character is the block supplied
by the local quotient-block and inflation operations. The weight convention
on p. 90 and quotient-block containment preceding (9.9), p. 199, give its
source meaning.

No Brauer reduction or desired normalizer-block equality is a field of
that ordinary membership input. The guarded compatibility is derived,
including equality of every admissible normalizer root with the SAME
modular-system root. Neither an ordinary algebraic closure nor a complete
local-reduction domain is supplied.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding

open ModularRep OrdinaryIrreducibleCharacter CharacterWeight FDRepSimpleClassKZero
open TypeBLocalReductionInstantiation TypeBModularGroupRootBinding
open TypeBFixedRootDefinitionFamily

/-- The character expansion of the already constructed specified row, at one
fixed finite group and with sufficient ordinary roots inside its scope. -/
structure ScopedDecompositionExpansionSource {ell : ℕ} {K O k H : Type}
    [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
    [Group H] [finiteGroup : Finite H]
    [residueCharacteristic : CharP k ell] [residueClosure : IsAlgClosed k]
    [ordinaryCharacteristic : CharZero K]
    (Msys : ModularSystem ell K O k)
    [ordinaryRoots : HasEnoughRootsOfUnity K (Nat.card H)] : Prop where
  expansion : ∀ chi : Irr K H,
    Finsupp.linearCombination ℤ
      (fun phi : IBr (groupRoot Msys H) => phi.val.toFun)
      (TypeBOrdinaryBlockSplitting.decompositionRow Msys (groupRoot Msys H) chi) =
        fun x : PrimeRegularElement (G := H) ell => chi x.val

section Decomposition

variable {ell : ℕ} {K O k H : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k] [Group H] [Finite H]
  (Msys : ModularSystem ell K O k)
  [HasEnoughRootsOfUnity K (Nat.card H)]

/-- Existing stable-reduction compatibility supplies the narrower expansion
statement; no new coefficient matrix is introduced. -/
theorem expansionSource_of_stableReduction
    (compatible : StableReductionBrauerCharacterCompatibility Msys (groupRoot Msys H)) :
    ScopedDecompositionExpansionSource (H := H) Msys where
  expansion := TypeBOrdinaryBlockSplitting.decompositionRow_character
    Msys (groupRoot Msys H) compatible

/-- An irreducible prime regular restriction forces its specified row. -/
theorem decompositionRow_eq_single
    (source : ScopedDecompositionExpansionSource (H := H) Msys)
    (chi : Irr K H) (phi : IBr (groupRoot Msys H))
    (reduction : ∀ x : PrimeRegularElement (G := H) ell, chi x.val = phi.val x) :
    TypeBOrdinaryBlockSplitting.decompositionRow Msys (groupRoot Msys H) chi =
      Finsupp.single phi 1 := by
  apply (((irreducibleBrauerCharacters_linearIndependent (groupRoot Msys H)).restrict_scalars' ℤ).finsuppLinearCombination_injective)
  rw [source.expansion, Finsupp.linearCombination_single, one_smul]
  funext x
  exact reduction x

theorem decompositionRow_self_ne_zero
    (source : ScopedDecompositionExpansionSource (H := H) Msys)
    (chi : Irr K H) (phi : IBr (groupRoot Msys H))
    (reduction : ∀ x : PrimeRegularElement (G := H) ell, chi x.val = phi.val x) :
    TypeBOrdinaryBlockSplitting.decompositionRow Msys (groupRoot Msys H) chi phi ≠ 0 := by
  rw [decompositionRow_eq_single Msys source chi phi reduction]
  simp only [Finsupp.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true]

end Decomposition

section Local

variable {ell : ℕ} {K O k G B : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k ell] [IsAlgClosed k]
  [Group G] [Fintype G] [MulAction (MulAut G)ᵐᵒᵖ B]
  (Msys : ModularSystem ell K O k)
  (operations : LocalBlockInductionOperations
    (p := ell) (k := k) (K := K) (G := G) (Block := B))

/-- Ordinary inflation along the literal normalizer quotient map. -/
def inflatedOrdinary (Q : Subgroup G) (chi : Irr K (NormalizerQuotient Q)) :
    Irr K (Subgroup.normalizer (Q : Set G)) :=
  inflateAlong (QuotientGroup.mk' (Q.subgroupOf (Subgroup.normalizer (Q : Set G))))
    (QuotientGroup.mk'_surjective _) chi

@[simp]
theorem inflatedOrdinary_value (Q : Subgroup G) (chi : Irr K (NormalizerQuotient Q))
    (x : Subgroup.normalizer (Q : Set G)) :
    inflatedOrdinary Q chi x =
      chi (QuotientGroup.mk' (Q.subgroupOf (Subgroup.normalizer (Q : Set G))) x) := rfl

/-- Ambient sufficient roots restrict to the actual normalizer. -/
def normalizerOrdinaryRoots [HasEnoughRootsOfUnity K (Nat.card G)] (Q : Subgroup G) :
    HasEnoughRootsOfUnity K (Nat.card (Subgroup.normalizer (Q : Set G))) :=
  HasEnoughRootsOfUnity.of_dvd K
    (Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (Q : Set G)))

/-- The existing specified ordinary-block source on the very decomposition
stored by the local operations, with its actual stable-reduction support. -/
def NormalizerOrdinarySource [HasEnoughRootsOfUnity K (Nat.card G)]
    (Q : Subgroup G) : Type := by
  letI := normalizerOrdinaryRoots (K := K) Q
  letI := (operations.inflatedNormalizerBlockData Q).fintypeBlock
  exact TypeBOrdinaryBlockSplitting.OrdinaryBlockSource Msys
    (groupRoot Msys (Subgroup.normalizer (Q : Set G)))
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    (operations.inflatedNormalizerBlockData Q).blocks

/-- The actual ordinary primitive block selected by that specified source. -/
def ordinaryNormalizerBlock [HasEnoughRootsOfUnity K (Nat.card G)]
    (Q : Subgroup G) (ordinary : NormalizerOrdinarySource Msys operations Q)
    (chi : Irr K (Subgroup.normalizer (Q : Set G))) :
    InflatedNormalizerBlock (k := k) Q := by
  letI := (operations.inflatedNormalizerBlockData Q).fintypeBlock
  exact (ordinary.physical
    (ordinaryRoots := normalizerOrdinaryRoots (K := K) Q)).ordinaryBlock chi

/-- The sole operations-specific input is ordinary block membership of
inflation from the actual quotient. It has no Brauer-character variable. -/
structure OrdinaryInflationMembership [HasEnoughRootsOfUnity K (Nat.card G)]
    (ordinary : ∀ Q : Subgroup G, NormalizerOrdinarySource Msys operations Q) : Prop where
  membership : ∀ (Q : Subgroup G) (radical : IsRadicalSubgroup ell Q)
    (chi : Irr K (NormalizerQuotient Q))
    (defectZero : ModularRep.IsDefectZeroOrdinaryCharacter ell chi),
    ordinaryNormalizerBlock Msys operations Q (ordinary Q) (inflatedOrdinary Q chi) =
      operations.inflateToNormalizer Q (operations.localCharacterBlock Q chi defectZero)

/-- Nonzero specified support identifies the exact normalizer block. -/
theorem normalizerBrauerBlock_eq_ordinary
    [HasEnoughRootsOfUnity K (Nat.card G)]
    (Q : Subgroup G) (ordinary : NormalizerOrdinarySource Msys operations Q)
    (chi : Irr K (Subgroup.normalizer (Q : Set G)))
    (phi : IBr (groupRoot Msys (Subgroup.normalizer (Q : Set G))))
    (support : TypeBOrdinaryBlockSplitting.decompositionRow Msys
      (groupRoot Msys (Subgroup.normalizer (Q : Set G))) chi phi ≠ 0) :
    NavarroLocalReductionInflationBlockCompatibility.normalizerBrauerBlock operations Q
      (groupRoot Msys (Subgroup.normalizer (Q : Set G))) phi =
        ordinaryNormalizerBlock Msys operations Q ordinary chi := by
  letI := normalizerOrdinaryRoots (K := K) Q
  letI := (operations.inflatedNormalizerBlockData Q).fintypeBlock
  exact TypeBOrdinaryBlockSplitting.block_of_nonzero_row Msys
    (groupRoot Msys (Subgroup.normalizer (Q : Set G)))
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding _)
    (operations.inflatedNormalizerBlockData Q).blocks ordinary chi phi support

/-- Agreement with the calibrated ambient roots fixes every permitted
normalizer convention, rather than varying the specified block source. -/
theorem normalizerRoot_eq_groupRoot
    (iotaG : PrimeRegularRootEmbedding ell k K G)
    (calibration : RootResidueCompatible Msys iotaG) (Q : Subgroup G)
    (iotaN : PrimeRegularRootEmbedding ell k K (Subgroup.normalizer (Q : Set G)))
    (agreement : NormalizerRootAgreement iotaG Q iotaN) :
    iotaN = groupRoot Msys (Subgroup.normalizer (Q : Set G)) := by
  apply eq_groupRoot_of_residue Msys _ iotaN
  intro z hz
  let H := Subgroup.normalizer (Q : Set G)
  letI : NeZero (primeRegularExponent ell H) := ⟨(primeRegularExponent_pos ell H).ne'⟩
  let zbar : rootsOfUnity (primeRegularExponent ell H) k :=
    rootsOfUnity.mkOfPowEq (Msys.residue z) (by rw [← map_pow, hz, map_one])
  have hval : ((zbar : kˣ) : k) = Msys.residue z := rfl
  rw [← hval, agreement, hval]
  apply calibration
  have hdiv : primeRegularExponent ell H ∣ primeRegularExponent ell G := by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card H) ell
  obtain ⟨d, hd⟩ := hdiv
  rw [hd, pow_mul, hz, one_pow]

/-- The fixed-root local specified law follows from ordinary inflation
membership and actual decomposition support. -/
def guardedBlockCompatibility
    [HasEnoughRootsOfUnity K (Nat.card G)]
    (iotaG : PrimeRegularRootEmbedding ell k K G)
    (calibration : RootResidueCompatible Msys iotaG)
    (expansion : ∀ (H : Type) [Group H] [Finite H]
      [HasEnoughRootsOfUnity K (Nat.card H)],
        ScopedDecompositionExpansionSource (H := H) Msys)
    (ordinary : ∀ Q : Subgroup G, NormalizerOrdinarySource Msys operations Q)
    (membership : OrdinaryInflationMembership Msys operations ordinary) :
    GuardedBlockCompatibility iotaG operations := by
  refine ⟨?_⟩
  intro W iotaN phiN agreement reduction
  have heq := normalizerRoot_eq_groupRoot Msys iotaG calibration W.subgroup iotaN agreement
  subst iotaN
  letI := normalizerOrdinaryRoots (K := K) W.subgroup
  have support := decompositionRow_self_ne_zero Msys
    (expansion (Subgroup.normalizer (W.subgroup : Set G)))
    (inflatedOrdinary W.subgroup W.localCharacter) phiN reduction
  exact (normalizerBrauerBlock_eq_ordinary Msys operations W.subgroup
    (ordinary W.subgroup) (inflatedOrdinary W.subgroup W.localCharacter) phiN support).trans
      (membership.membership W.subgroup W.radical W.localCharacter W.defectZero)

end Local

end ModularRep.PaperProofs.TypeBLocalPhysicalBlockBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
