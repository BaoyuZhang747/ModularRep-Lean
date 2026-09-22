import ModularRep.PaperProofs.SporadicFi24ThreeBlockCarrierActual

/-!
# Literal block cancellation for the Fischer group at three

This file gives the first literal-carrier form of the cancellation used for
`Fi'_{24}` at the coefficient prime three.  The two total spaces are the
library's function-valued irreducible Brauer characters and conjugacy classes
of actual character weights.  Their block fibres are fibres of the literal
primitive-central-idempotent assignments.

The input `RawSectorFamily` is deliberately only a family of equivariant
equivalences on central character-sector fibres.  Its construction gives a total
equivariant equivalence, but no block preservation is assumed.  A complete
census of the three literal blocks is a separate source input.  Lean uses that
census and the pairwise distinction of the blocks to construct the two
decompositions into block fibres. The cancellation interface receives
equivariant equivalences on the known nonprincipal and defect-zero fibres. In
the live factory route the defect-zero field is kernel-constructed upstream
from D/T/C/B/Z/F, while the nonprincipal field is kernel-constructed from a
literal cardinality and fixed-point census.
In particular, the defect-zero equivalence is independent of the
normalisation at `Q = 1`; fixing one selected image would not establish an
equivalence of the whole defect-zero fibre.

Lean then applies the finite `C₂`-set cancellation theorem to construct an
equivariant equivalence on the remaining, principal block fibre.  No
principal-block equivalence, cardinality, fixed-point count, or signature is
an input here.  It combines that map with the two known fibre equivalences,
proves equivariance for the selected outer involution and literal block
preservation, and retains literal agreement with both known maps.  This
module does not identify the printed An--Dietrich rows with these literal
fibres or provide the full automorphism and extension clauses of the
inductive condition.  Those source-shaped identifications and deductions
remain later obligations.

Trust grading used below:

* `K`: deductions checked by the Lean kernel, including literal Brauer-block
  and block-sector transport and the quotient descent built from raw
  weight-block naturality;
* `E1`: source facts behind concrete local-block, inflation, induction, and
  raw automorphism-naturality operations;
* `E2`: the An--Dietrich raw sector family and the deep cited inputs entering
  the remaining source records;
* `E3`: the character-table calculation that cross-checks the three-block
  census and selected orbit data, including the nonprincipal census;
* `U`: the concrete carrier, operation, and source matches identifying the
  abstract data with the intended Fischer group.

`RoutineTransportInput` is empty and contributes no E1 premise. The K
weight-block transport theorem remains conditional on the raw local-block
naturality recorded by `LocalBlockInductionSource.automorphism_transport`;
that concrete operation/naturality match remains E1/U. The nonprincipal
literal census remains an external E2/E3/U boundary.

The exhaustive field `all_blocks` has composite grade `E1/E2/U`: it uses the
published block classification, the standard correspondence between blocks
and primitive central idempotents, and their transport to the literal carrier
below.  The present transcript calculation is only an `E3` cross-check and
does not itself establish that literal identification.
-/

noncomputable section

open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual

open Formalisation
open Formalisation.BlockCancellation
open ModularRep.PaperProofs.SporadicFi24CentralSectorAssemblyLemma56Actual

universe u

variable {k K X BlockIndex : Type u}
variable [Field k] [Field K] [CharP k 3] [IsAlgClosed k] [CharZero K]
variable [Group X] [Fintype X] [Fintype BlockIndex]
variable {blockIdempotent : BlockIndex → k[X]}

noncomputable local instance centerFintype :
    Fintype (Subgroup.center X) :=
  Fintype.ofFinite _

variable (iota : PrimeRegularRootEmbedding 3 k K X)
variable (hinj :
  FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [Invertible (Fintype.card (Subgroup.center X) : k)]
variable {R :
  LiteralCarrierAdapter (p := 3) (k := k) (K := K) (X := X)}
variable (E1 : RoutineTransportInput iota hinj blocks R)

/-! ## Raw sector input and literal block fibres -/

/-- The An--Dietrich sector maps before any block-induction or block-fibre
conclusion is added.  Supplying this family is an `E2` source input. -/
abbrev RawSectorFamily :=
  EquivariantFibreEquiv
    (brauerSector iota hinj blocks)
    (weightSector (R := R))
    (brauerSector_equivariant iota hinj blocks E1)
    (weightSector_equivariant_actual
      (iota := iota) (hinj := hinj) (blocks := blocks) (R := R) E1)

omit [Fintype X] [CharP k 3] [IsAlgClosed k] in
/-- If the chosen covering group is centreless, its central set of characters
has at most one element. -/
theorem centralSector_subsingleton
    (hcenter : ∀ z : Subgroup.center X, z = 1) :
    Subsingleton (CentralSector (k := k) (X := X)) := by
  let _ : Subsingleton (Subgroup.center X) :=
    ⟨fun z w ↦ (hcenter z).trans (hcenter w).symm⟩
  infer_instance

/-- On a centreless carrier, a globally equivariant equivalence restricts to
the raw family on central character sectors. No block preservation is used. -/
def rawSectorFamilyOfEquivariantEquiv
    (hcenter : ∀ z : Subgroup.center X, z = 1)
    (rawEquiv : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (rawEquivariant : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      rawEquiv (a • phi) = a • rawEquiv phi) :
    RawSectorFamily iota hinj blocks E1 := by
  let _ : Subsingleton (CentralSector (k := k) (X := X)) :=
    centralSector_subsingleton hcenter
  exact EquivariantFibreEquiv.ofEquiv_of_subsingleton rawEquiv rawEquivariant

/-- The canonical permutation of all literal Brauer characters induced by
the selected outer automorphism. -/
def totalBrauerPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (IBr iota) :=
  MulAction.toPermHom (MulAut X)ᵐᵒᵖ (IBr iota) S.outer

/-- The canonical permutation of all literal character weights induced by
the selected outer automorphism. -/
def totalWeightPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm (WeightClass (p := 3) (K := K) (X := X)) :=
  MulAction.toPermHom (MulAut X)ᵐᵒᵖ
    (WeightClass (p := 3) (K := K) (X := X)) S.outer

private theorem sumPerm_involutive
    {A B : Type*} (sigma : Equiv.Perm A) (tau : Equiv.Perm B)
    (hsigma : Function.Involutive sigma)
    (htau : Function.Involutive tau) :
    Function.Involutive (sumPerm sigma tau) := by
  intro x
  cases x with
  | inl a =>
      change Sum.inl (sigma (sigma a)) = Sum.inl a
      rw [hsigma a]
  | inr b =>
      change Sum.inr (tau (tau b)) = Sum.inr b
      rw [htau b]

/-! ## Complete literal decompositions -/

/-- The three Brauer block fibres, with the principal fibre distinguished as
the part that remains after cancellation. -/
abbrev BrauerThreeParts
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :=
  Sum (BrauerFibre iota hinj blocks S.principalBlock)
    (Sum (BrauerFibre iota hinj blocks S.nonprincipalBlock)
      (BrauerFibre iota hinj blocks S.defectZeroBlock))

/-- The corresponding three literal weight block fibres. -/
abbrev WeightThreeParts
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :=
  Sum (WeightFibre (R := R) S.principalBlock)
    (Sum (WeightFibre (R := R) S.nonprincipalBlock)
      (WeightFibre (R := R) S.defectZeroBlock))

/-- Forget the summand tag of the Brauer decomposition. -/
def brauerPartValue
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    BrauerThreeParts iota hinj blocks S → IBr iota
  | .inl phi => phi.1
  | .inr (.inl phi) => phi.1
  | .inr (.inr phi) => phi.1

/-- Forget the summand tag of the weight decomposition. -/
def weightPartValue
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    WeightThreeParts (R := R) S →
      WeightClass (p := 3) (K := K) (X := X)
  | .inl w => w.1
  | .inr (.inl w) => w.1
  | .inr (.inr w) => w.1

/-- The outer action on the two already known Brauer fibres. -/
def knownBrauerPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm
      (Sum (BrauerFibre iota hinj blocks S.nonprincipalBlock)
        (BrauerFibre iota hinj blocks S.defectZeroBlock)) :=
  sumPerm (nonprincipalBrauerPerm iota hinj blocks E1 S)
    (defectZeroBrauerPerm iota hinj blocks E1 S)

/-- The outer action on the two already known weight fibres. -/
def knownWeightPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Equiv.Perm
      (Sum (WeightFibre (R := R) S.nonprincipalBlock)
        (WeightFibre (R := R) S.defectZeroBlock)) :=
  sumPerm (nonprincipalWeightPerm (R := R) S)
    (defectZeroWeightPerm (R := R) S)

/-- Two elements in literal fibres over the same value have the same block
label. -/
private theorem block_eq_of_fibre_value_eq
    {A B : Type*} {f : A → B} {b c : B}
    (x : Fibre f b) (y : Fibre f c) (h : x.1 = y.1) :
    b = c :=
  x.2.symm.trans ((congrArg f h).trans y.2)

/-- The forgetful map from the three Brauer fibres is injective because the
three literal blocks are pairwise distinct. -/
theorem brauerPartValue_injective
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Function.Injective (brauerPartValue iota hinj blocks S) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
          cases y with
          | inl y =>
              exact (S.principal_ne_nonprincipal
                (block_eq_of_fibre_value_eq x y h)).elim
          | inr y =>
              exact (S.principal_ne_defectZero
                (block_eq_of_fibre_value_eq x y h)).elim
  | inr x =>
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              exact (S.principal_ne_nonprincipal
                (block_eq_of_fibre_value_eq y x h.symm)).elim
          | inr y =>
              cases y with
              | inl y =>
                  exact congrArg Sum.inr
                    (congrArg Sum.inl (Subtype.ext h))
              | inr y =>
                  exact (S.nonprincipal_ne_defectZero
                    (block_eq_of_fibre_value_eq x y h)).elim
      | inr x =>
          cases y with
          | inl y =>
              exact (S.principal_ne_defectZero
                (block_eq_of_fibre_value_eq y x h.symm)).elim
          | inr y =>
              cases y with
              | inl y =>
                  exact (S.nonprincipal_ne_defectZero
                    (block_eq_of_fibre_value_eq y x h.symm)).elim
              | inr y =>
                  exact congrArg Sum.inr
                    (congrArg Sum.inr (Subtype.ext h))

/-- The exhaustive block census makes the forgetful map from the three
Brauer fibres surjective. -/
theorem brauerPartValue_surjective
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Function.Surjective (brauerPartValue iota hinj blocks S) := by
  intro phi
  rcases S.all_blocks (brauerBlock iota hinj blocks phi) with h | h | h
  · exact ⟨Sum.inl ⟨phi, h⟩, rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨phi, h⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨phi, h⟩), rfl⟩

/-- The forgetful map from the three weight fibres is injective because the
three literal blocks are pairwise distinct. -/
theorem weightPartValue_injective
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Function.Injective (weightPartValue (R := R) S) := by
  intro x y h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
          cases y with
          | inl y =>
              exact (S.principal_ne_nonprincipal
                (block_eq_of_fibre_value_eq x y h)).elim
          | inr y =>
              exact (S.principal_ne_defectZero
                (block_eq_of_fibre_value_eq x y h)).elim
  | inr x =>
      cases x with
      | inl x =>
          cases y with
          | inl y =>
              exact (S.principal_ne_nonprincipal
                (block_eq_of_fibre_value_eq y x h.symm)).elim
          | inr y =>
              cases y with
              | inl y =>
                  exact congrArg Sum.inr
                    (congrArg Sum.inl (Subtype.ext h))
              | inr y =>
                  exact (S.nonprincipal_ne_defectZero
                    (block_eq_of_fibre_value_eq x y h)).elim
      | inr x =>
          cases y with
          | inl y =>
              exact (S.principal_ne_defectZero
                (block_eq_of_fibre_value_eq y x h.symm)).elim
          | inr y =>
              cases y with
              | inl y =>
                  exact (S.nonprincipal_ne_defectZero
                    (block_eq_of_fibre_value_eq y x h.symm)).elim
              | inr y =>
                  exact congrArg Sum.inr
                    (congrArg Sum.inr (Subtype.ext h))

/-- The exhaustive block census makes the forgetful map from the three
weight fibres surjective. -/
theorem weightPartValue_surjective
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Function.Surjective (weightPartValue (R := R) S) := by
  intro w
  rcases S.all_blocks (R.1.weightBlock w) with h | h | h
  · exact ⟨Sum.inl ⟨w, h⟩, rfl⟩
  · exact ⟨Sum.inr (Sum.inl ⟨w, h⟩), rfl⟩
  · exact ⟨Sum.inr (Sum.inr ⟨w, h⟩), rfl⟩

/-- The bijection that forgets the block-fibre tag on a literal Brauer
character. -/
def brauerPartsEquiv
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    BrauerThreeParts iota hinj blocks S ≃ IBr iota :=
  Equiv.ofBijective (brauerPartValue iota hinj blocks S)
    ⟨brauerPartValue_injective iota hinj blocks S,
      brauerPartValue_surjective iota hinj blocks S⟩

/-- The bijection that forgets the block-fibre tag on a literal weight. -/
def weightPartsEquiv
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    WeightThreeParts (R := R) S ≃
      WeightClass (p := 3) (K := K) (X := X) :=
  Equiv.ofBijective (weightPartValue (R := R) S)
    ⟨weightPartValue_injective (R := R) S,
      weightPartValue_surjective (R := R) S⟩

/-- The canonical decomposition of all literal Brauer characters into the
three block fibres. -/
def brauerDecomposition
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    IBr iota ≃ BrauerThreeParts iota hinj blocks S :=
  (brauerPartsEquiv iota hinj blocks S).symm

/-- The canonical decomposition of all literal weights into the three block
fibres. -/
def weightDecomposition
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    WeightClass (p := 3) (K := K) (X := X) ≃
      WeightThreeParts (R := R) S :=
  (weightPartsEquiv (R := R) S).symm

@[simp]
theorem brauerPartValue_decomposition
    (S : Fi24ThreeBlockSource (k := k) (X := X)) (phi : IBr iota) :
    brauerPartValue iota hinj blocks S (brauerDecomposition iota hinj blocks S phi) =
      phi :=
  (brauerPartsEquiv iota hinj blocks S).apply_symm_apply phi

@[simp]
theorem weightPartValue_decomposition
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (w : WeightClass (p := 3) (K := K) (X := X)) :
    weightPartValue (R := R) S (weightDecomposition (R := R) S w) = w :=
  (weightPartsEquiv (R := R) S).apply_symm_apply w

theorem brauerPartValue_sumPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (x : BrauerThreeParts iota hinj blocks S) :
    brauerPartValue iota hinj blocks S
        (sumPerm (principalBrauerPerm iota hinj blocks E1 S)
          (knownBrauerPerm iota hinj blocks E1 S) x) =
      totalBrauerPerm iota S (brauerPartValue iota hinj blocks S x) := by
  rcases x with x | x
  · rfl
  · rcases x with x | x <;> rfl

theorem weightPartValue_sumPerm
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (x : WeightThreeParts (R := R) S) :
    weightPartValue (R := R) S
        (sumPerm (principalWeightPerm (R := R) S)
          (knownWeightPerm (R := R) S) x) =
      totalWeightPerm (K := K) S (weightPartValue (R := R) S x) := by
  rcases x with x | x
  · rfl
  · rcases x with x | x <;> rfl

theorem brauerDecomposition_intertwines
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Intertwines (brauerDecomposition iota hinj blocks S)
      (totalBrauerPerm iota S)
      (sumPerm (principalBrauerPerm iota hinj blocks E1 S)
        (knownBrauerPerm iota hinj blocks E1 S)) := by
  intro phi
  apply brauerPartValue_injective iota hinj blocks S
  rw [brauerPartValue_decomposition,
    brauerPartValue_sumPerm,
    brauerPartValue_decomposition]

theorem weightDecomposition_intertwines
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Intertwines (weightDecomposition (R := R) S)
      (totalWeightPerm (K := K) S)
      (sumPerm (principalWeightPerm (R := R) S)
        (knownWeightPerm (R := R) S)) := by
  intro w
  apply weightPartValue_injective (R := R) S
  rw [weightPartValue_decomposition,
    weightPartValue_sumPerm,
    weightPartValue_decomposition]

/-! ## The independently known block fibres -/

def knownEquiv
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    Sum (BrauerFibre iota hinj blocks S.nonprincipalBlock)
        (BrauerFibre iota hinj blocks S.defectZeroBlock) ≃
      Sum (WeightFibre (R := R) S.nonprincipalBlock)
        (WeightFibre (R := R) S.defectZeroBlock) :=
  Equiv.sumCongr Known.nonprincipal Known.defectZero

theorem knownEquiv_intertwines
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    Intertwines (knownEquiv iota hinj blocks E1 S Known)
      (knownBrauerPerm iota hinj blocks E1 S)
      (knownWeightPerm (R := R) S) := by
  intro x
  cases x with
  | inl phi =>
      exact congrArg Sum.inl (Known.nonprincipal_intertwines phi)
  | inr phi =>
      exact congrArg Sum.inr (Known.defectZero_intertwines phi)

/-! ## Kernel cancellation -/

private theorem intertwines_symm
    {A B : Type*} (e : A ≃ B)
    {sigma : Equiv.Perm A} {tau : Equiv.Perm B}
    (h : Intertwines e sigma tau) :
    Intertwines e.symm tau sigma := by
  intro y
  apply e.injective
  rw [e.apply_symm_apply, h, e.apply_symm_apply]

private theorem intertwines_trans
    {A B C : Type*} (e : A ≃ B) (f : B ≃ C)
    {sigma : Equiv.Perm A} {tau : Equiv.Perm B}
    {upsilon : Equiv.Perm C}
    (he : Intertwines e sigma tau)
    (hf : Intertwines f tau upsilon) :
    Intertwines (e.trans f) sigma upsilon := by
  intro x
  change f (e (sigma x)) = upsilon (f (e x))
  rw [he x, hf (e x)]

/-- The raw sector family supplies the required equivariant equivalence only
on the two complete literal carriers.  This is `K` from its `E2` family
input. -/
theorem rawSectorFamily_intertwines
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Intertwines F.assemble (totalBrauerPerm iota S)
      (totalWeightPerm (K := K) S) := by
  intro phi
  change F.assemble (S.outer • phi) = S.outer • F.assemble phi
  exact F.assemble_equivariant S.outer phi

/-- Transport the raw total equivalence across the two complete literal
decompositions. -/
def decomposedGlobalEquiv
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    BrauerThreeParts iota hinj blocks S ≃
      WeightThreeParts (R := R) S :=
  (brauerDecomposition iota hinj blocks S).symm.trans
    (F.assemble.trans (weightDecomposition (R := R) S))

theorem decomposedGlobalEquiv_intertwines
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X)) :
    Intertwines (decomposedGlobalEquiv iota hinj blocks E1 F S)
      (sumPerm (principalBrauerPerm iota hinj blocks E1 S)
        (knownBrauerPerm iota hinj blocks E1 S))
      (sumPerm (principalWeightPerm (R := R) S)
        (knownWeightPerm (R := R) S)) :=
  intertwines_trans (brauerDecomposition iota hinj blocks S).symm
    (F.assemble.trans (weightDecomposition (R := R) S))
    (intertwines_symm (brauerDecomposition iota hinj blocks S)
      (brauerDecomposition_intertwines iota hinj blocks E1 S))
    (intertwines_trans F.assemble (weightDecomposition (R := R) S)
      (rawSectorFamily_intertwines iota hinj blocks E1 F S)
      (weightDecomposition_intertwines (R := R) S))

/-- `K`: finite `C₂`-set cancellation constructs the equivariant
equivalence on the remaining literal principal block fibre.  The conclusion
is existential because cancellation does not choose a canonical labelling. -/
theorem exists_principalFibreEquiv
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    ∃ principal :
        BrauerFibre iota hinj blocks S.principalBlock ≃
          WeightFibre (R := R) S.principalBlock,
      Intertwines principal
        (principalBrauerPerm iota hinj blocks E1 S)
        (principalWeightPerm (R := R) S) := by
  letI : Finite (WeightClass (p := 3) (K := K) (X := X)) :=
    Finite.of_injective F.assemble.symm F.assemble.symm.injective
  exact Formalisation.BlockCancellation.cancel_equivariant_equiv
    (principalBrauerPerm iota hinj blocks E1 S)
    (knownBrauerPerm iota hinj blocks E1 S)
    (principalWeightPerm (R := R) S)
    (knownWeightPerm (R := R) S)
    (brauerFibrePerm_involutive iota hinj blocks E1 S
      S.principalBlock S.principal_fixed)
    (sumPerm_involutive
      (nonprincipalBrauerPerm iota hinj blocks E1 S)
      (defectZeroBrauerPerm iota hinj blocks E1 S)
      (brauerFibrePerm_involutive iota hinj blocks E1 S
        S.nonprincipalBlock S.nonprincipal_fixed)
      (brauerFibrePerm_involutive iota hinj blocks E1 S
        S.defectZeroBlock S.defectZero_fixed))
    (weightFibrePerm_involutive (R := R) S
      S.principalBlock S.principal_fixed)
    (sumPerm_involutive
      (nonprincipalWeightPerm (R := R) S)
      (defectZeroWeightPerm (R := R) S)
      (weightFibrePerm_involutive (R := R) S
        S.nonprincipalBlock S.nonprincipal_fixed)
      (weightFibrePerm_involutive (R := R) S
        S.defectZeroBlock S.defectZero_fixed))
    (decomposedGlobalEquiv iota hinj blocks E1 F S)
    (decomposedGlobalEquiv_intertwines iota hinj blocks E1 F S)
    (knownEquiv iota hinj blocks E1 S Known)
    (knownEquiv_intertwines iota hinj blocks E1 S Known)

/-- For a centreless carrier, the total equivariant correspondence supplied
by the literature is enough for the principal block cancellation. It is not
assumed to preserve blocks. -/
theorem exists_principalFibreEquiv_of_equivariantEquiv
    (hcenter : ∀ z : Subgroup.center X, z = 1)
    (rawEquiv : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X))
    (rawEquivariant : ∀ (a : (MulAut X)ᵐᵒᵖ) (phi : IBr iota),
      rawEquiv (a • phi) = a • rawEquiv phi)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    ∃ principal :
        BrauerFibre iota hinj blocks S.principalBlock ≃
          WeightFibre (R := R) S.principalBlock,
      Intertwines principal
        (principalBrauerPerm iota hinj blocks E1 S)
        (principalWeightPerm (R := R) S) :=
  exists_principalFibreEquiv iota hinj blocks E1
    (rawSectorFamilyOfEquivariantEquiv iota hinj blocks E1
      hcenter rawEquiv rawEquivariant)
    S Known

/-! ## Construction of the three block maps -/

/-- Combine the principal equivalence constructed by cancellation with the
two independently known block equivalences. -/
def assembledThreeBlockEquiv
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (principal :
      BrauerFibre iota hinj blocks S.principalBlock ≃
        WeightFibre (R := R) S.principalBlock)
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    IBr iota ≃ WeightClass (p := 3) (K := K) (X := X) :=
  (brauerDecomposition iota hinj blocks S).trans
    ((Equiv.sumCongr principal
      (knownEquiv iota hinj blocks E1 S Known)).trans
      (weightDecomposition (R := R) S).symm)

/-- The resulting equivalence commutes with the selected outer involution. -/
theorem assembledThreeBlockEquiv_intertwines
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (principal :
      BrauerFibre iota hinj blocks S.principalBlock ≃
        WeightFibre (R := R) S.principalBlock)
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (hprincipal :
      Intertwines principal
        (principalBrauerPerm iota hinj blocks E1 S)
        (principalWeightPerm (R := R) S)) :
    Intertwines
      (assembledThreeBlockEquiv iota hinj blocks E1 S principal Known)
      (totalBrauerPerm iota S)
      (totalWeightPerm (K := K) S) := by
  unfold assembledThreeBlockEquiv
  refine intertwines_trans
    (brauerDecomposition iota hinj blocks S)
    ((Equiv.sumCongr principal
      (knownEquiv iota hinj blocks E1 S Known)).trans
      (weightDecomposition (R := R) S).symm)
    (brauerDecomposition_intertwines iota hinj blocks E1 S) ?_
  have hsum :
      Intertwines
        (Equiv.sumCongr principal
          (knownEquiv iota hinj blocks E1 S Known))
        (sumPerm (principalBrauerPerm iota hinj blocks E1 S)
          (knownBrauerPerm iota hinj blocks E1 S))
        (sumPerm (principalWeightPerm (R := R) S)
          (knownWeightPerm (R := R) S)) := by
    intro x
    rcases x with phi | x
    · exact congrArg Sum.inl (hprincipal phi)
    · exact congrArg Sum.inr
        (knownEquiv_intertwines iota hinj blocks E1 S Known x)
  have hweight :
      Intertwines (weightDecomposition (R := R) S).symm
        (sumPerm (principalWeightPerm (R := R) S)
          (knownWeightPerm (R := R) S))
        (totalWeightPerm (K := K) S) :=
    intertwines_symm
      (weightDecomposition (R := R) S)
      (weightDecomposition_intertwines (R := R) S)
  exact intertwines_trans
    (Equiv.sumCongr principal
      (knownEquiv iota hinj blocks E1 S Known))
    (weightDecomposition (R := R) S).symm hsum hweight

@[simp]
theorem assembledThreeBlockEquiv_principal
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (principal :
      BrauerFibre iota hinj blocks S.principalBlock ≃
        WeightFibre (R := R) S.principalBlock)
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (phi : BrauerFibre iota hinj blocks S.principalBlock) :
    assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi.1 =
      (principal phi).1 := by
  have hsource :
      brauerDecomposition iota hinj blocks S phi.1 = Sum.inl phi := by
    apply brauerPartValue_injective iota hinj blocks S
    rw [brauerPartValue_decomposition]
    rfl
  have htarget :
      weightDecomposition (R := R) S (principal phi).1 =
        Sum.inl (principal phi) := by
    apply weightPartValue_injective (R := R) S
    rw [weightPartValue_decomposition]
    rfl
  apply (weightDecomposition (R := R) S).injective
  simp only [assembledThreeBlockEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [hsource, htarget]
  rfl

@[simp]
theorem assembledThreeBlockEquiv_nonprincipal
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (principal :
      BrauerFibre iota hinj blocks S.principalBlock ≃
        WeightFibre (R := R) S.principalBlock)
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (phi : BrauerFibre iota hinj blocks S.nonprincipalBlock) :
    assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi.1 =
      (Known.nonprincipal phi).1 := by
  have hsource :
      brauerDecomposition iota hinj blocks S phi.1 =
        Sum.inr (Sum.inl phi) := by
    apply brauerPartValue_injective iota hinj blocks S
    rw [brauerPartValue_decomposition]
    rfl
  have htarget :
      weightDecomposition (R := R) S (Known.nonprincipal phi).1 =
        Sum.inr (Sum.inl (Known.nonprincipal phi)) := by
    apply weightPartValue_injective (R := R) S
    rw [weightPartValue_decomposition]
    rfl
  apply (weightDecomposition (R := R) S).injective
  simp only [assembledThreeBlockEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [hsource, htarget]
  rfl

@[simp]
theorem assembledThreeBlockEquiv_defectZero
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (principal :
      BrauerFibre iota hinj blocks S.principalBlock ≃
        WeightFibre (R := R) S.principalBlock)
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (phi : BrauerFibre iota hinj blocks S.defectZeroBlock) :
    assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi.1 =
      (Known.defectZero phi).1 := by
  have hsource :
      brauerDecomposition iota hinj blocks S phi.1 =
        Sum.inr (Sum.inr phi) := by
    apply brauerPartValue_injective iota hinj blocks S
    rw [brauerPartValue_decomposition]
    rfl
  have htarget :
      weightDecomposition (R := R) S (Known.defectZero phi).1 =
        Sum.inr (Sum.inr (Known.defectZero phi)) := by
    apply weightPartValue_injective (R := R) S
    rw [weightPartValue_decomposition]
    rfl
  apply (weightDecomposition (R := R) S).injective
  simp only [assembledThreeBlockEquiv, Equiv.trans_apply,
    Equiv.apply_symm_apply]
  rw [hsource, htarget]
  rfl

/-- The resulting equivalence preserves the literal primitive block attached
to every Brauer character. -/
theorem assembledThreeBlockEquiv_preserves_block
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (principal :
      BrauerFibre iota hinj blocks S.principalBlock ≃
        WeightFibre (R := R) S.principalBlock)
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (phi : IBr iota) :
    R.1.weightBlock
        (assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi) =
      brauerBlock iota hinj blocks phi := by
  rcases S.all_blocks (brauerBlock iota hinj blocks phi) with h | h | h
  · let phi' : BrauerFibre iota hinj blocks S.principalBlock := ⟨phi, h⟩
    change R.1.weightBlock
        (assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi'.1) =
      brauerBlock iota hinj blocks phi'.1
    rw [assembledThreeBlockEquiv_principal]
    exact (principal phi').property.trans phi'.property.symm
  · let phi' : BrauerFibre iota hinj blocks S.nonprincipalBlock := ⟨phi, h⟩
    change R.1.weightBlock
        (assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi'.1) =
      brauerBlock iota hinj blocks phi'.1
    rw [assembledThreeBlockEquiv_nonprincipal]
    exact (Known.nonprincipal phi').property.trans phi'.property.symm
  · let phi' : BrauerFibre iota hinj blocks S.defectZeroBlock := ⟨phi, h⟩
    change R.1.weightBlock
        (assembledThreeBlockEquiv iota hinj blocks E1 S principal Known phi'.1) =
      brauerBlock iota hinj blocks phi'.1
    rw [assembledThreeBlockEquiv_defectZero]
    exact (Known.defectZero phi').property.trans phi'.property.symm

/-- The cancellation map and the two known fibre maps combine to a total
block-preserving equivalence for the selected outer involution.  The result
does not assert full automorphism equivariance or the extension clauses of
the inductive condition. -/
theorem exists_threeBlockBlockwiseEquiv
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    ∃ Omega : IBr iota ≃ WeightClass (p := 3) (K := K) (X := X),
      Intertwines Omega
        (totalBrauerPerm iota S)
        (totalWeightPerm (K := K) S) ∧
      (∀ phi,
        R.1.weightBlock (Omega phi) =
          brauerBlock iota hinj blocks phi) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.nonprincipalBlock,
        Omega phi.1 = (Known.nonprincipal phi).1) ∧
      (∀ phi : BrauerFibre iota hinj blocks S.defectZeroBlock,
        Omega phi.1 = (Known.defectZero phi).1) := by
  obtain ⟨principal, hprincipal⟩ :=
    exists_principalFibreEquiv iota hinj blocks E1 F S Known
  refine ⟨assembledThreeBlockEquiv iota hinj blocks E1 S principal Known,
    ?_, ?_, ?_, ?_⟩
  · exact assembledThreeBlockEquiv_intertwines
      iota hinj blocks E1 S principal Known hprincipal
  · exact assembledThreeBlockEquiv_preserves_block
      iota hinj blocks E1 S principal Known
  · exact assembledThreeBlockEquiv_nonprincipal
      iota hinj blocks E1 S principal Known
  · exact assembledThreeBlockEquiv_defectZero
      iota hinj blocks E1 S principal Known

/-- The equivariant equivalence constructed by cancellation identifies the
literal principal Brauer and weight signatures for the selected outer
involution.  In particular, neither cardinality nor fixed point equality is a
new source input. -/
theorem principalFibre_signatures_eq
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S) :
    (Nat.card (BrauerFibre iota hinj blocks S.principalBlock),
      Nat.card (Function.fixedPoints
        (principalBrauerPerm iota hinj blocks E1 S))) =
    (Nat.card (WeightFibre (R := R) S.principalBlock),
      Nat.card (Function.fixedPoints
        (principalWeightPerm (R := R) S))) := by
  obtain ⟨principal, hprincipal⟩ :=
    exists_principalFibreEquiv iota hinj blocks E1 F S Known
  apply Prod.ext
  · exact Nat.card_congr principal
  · exact Nat.card_congr
      (fixedPointsEquivOfIntertwines principal _ _ hprincipal)

/-- Exact numerical consequence used in the manuscript.  Once the external
table calculation has been matched to the literal principal Brauer fibre,
Lean transports its signature `(25, 25)` to the literal principal weight
fibre. -/
theorem principalWeight_signature_of_brauer_signature
    (F : RawSectorFamily iota hinj blocks E1)
    (S : Fi24ThreeBlockSource (k := k) (X := X))
    (Known : Fi24ThreeKnownEquivalences iota hinj blocks E1 S)
    (hBrauer :
      (Nat.card (BrauerFibre iota hinj blocks S.principalBlock),
        Nat.card (Function.fixedPoints
          (principalBrauerPerm iota hinj blocks E1 S))) = (25, 25)) :
    (Nat.card (WeightFibre (R := R) S.principalBlock),
      Nat.card (Function.fixedPoints
        (principalWeightPerm (R := R) S))) = (25, 25) :=
  (principalFibre_signatures_eq iota hinj blocks E1 F S Known).symm.trans
    hBrauer

end ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
