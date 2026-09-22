import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit
import Formalisation.FibreTransport
import Formalisation.EquivariantActions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulCenterEquivariantReplacement

/-! Transport the original faithful-sector bijection between Brauer
characters and weights defined by ordinary characters. The full equivariance, radical partition and
underlying stabilizer equality are conclusions of the construction.
No character-triple predicate or full-family source is used. -/

noncomputable section
set_option maxHeartbeats 2000000
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily

open ModularRep Formalisation
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicFi24P3Definition44NamedCarrierFaithfulSectorCarriers

universe u

variable {p : ℕ} {k K G Block : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Fintype G] [Fintype Block]
variable {blockIdempotent : Block → k[G]}
local instance centerFintype : Fintype (Subgroup.center G) := Fintype.ofFinite _
variable [Invertible (Fintype.card (Subgroup.center G) : k)]
variable (iota : PrimeRegularRootEmbedding p k K G)
variable (hinj : FDRepSimpleClassKZero.IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable (R : LiteralCarrierAdapter (p := p) (k := k) (K := K) (X := G))
variable (E1 : RoutineTransportInput iota hinj blocks R)

local notation "A" => (MulAut G)ᵐᵒᵖ
local notation "S" => FaithfulSector (k := k) (X := G)
local notation "FB" => FaithfulIBr iota hinj blocks R E1
local notation "FW" => FaithfulWeight iota hinj blocks R E1
local notation "pX" => faithfulBrauerSector iota hinj blocks R E1
local notation "pY" => faithfulWeightSector iota hinj blocks R E1
local notation "rY" => faithfulWeightRadical iota hinj blocks R E1

theorem brauerProjection_equivariant (a : A) (x : FB) :
    pX (a • x) = a • pX x := by
  apply Subtype.ext
  exact brauerSector_equivariant iota hinj blocks E1 a x.val

theorem weightProjection_equivariant (a : A) (y : FW) :
    pY (a • y) = a • pY y := by
  apply Subtype.ext
  exact weightSector_equivariant_actual iota hinj blocks E1 a y.val

local notation "hpX" => brauerProjection_equivariant iota hinj blocks R E1
local notation "hpY" => weightProjection_equivariant iota hinj blocks R E1

def transportedEquivalence (nu0 : S) (t : S → A) (ht : ∀ nu, t nu • nu0 = nu)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0) : FB ≃ FW :=
  Formalisation.transportedEquiv pX pY hpX hpY nu0 t ht e0

def radicalPart (e : FB ≃ FW) (x : FB) : RadicalClass (p := p) (X := G) := rY (e x)

/- This fixed predicate records only constructed output properties. It is
never a source premise. The local equivalences retain the same global map. -/
def FamilyProperties (e : FB ≃ FW) : Prop :=
  (∀ (a : A) (x : FB), e (a • x) = a • e x) ∧
  (∀ x : FB, pY (e x) = pX x) ∧
  (∀ x : FB, MulAction.stabilizer A x.val = MulAction.stabilizer A (e x).val) ∧
  (∀ (a : A) (x : FB), a • x.val = x.val ↔ a • (e x).val = (e x).val) ∧
  (∀ (a : A) (x : FB), radicalPart iota hinj blocks R E1 e (a • x) =
    a • radicalPart iota hinj blocks R E1 e x) ∧
  (∃ P : FB ≃ (Σ q : RadicalClass (p := p) (X := G),
      {x : FB // radicalPart iota hinj blocks R E1 e x = q}),
    ∀ x : FB, (P x).1 = radicalPart iota hinj blocks R E1 e x) ∧
  ∀ (nu : S) (q : RadicalClass (p := p) (X := G)),
    ∃ L : {x : FB // pX x = nu ∧ radicalPart iota hinj blocks R E1 e x = q} ≃
        {y : FW // pY y = nu ∧ rY y = q},
      ∀ x, (L x).1 = e x.1

/-- The faithful-family and fixed-iff deduction from the original base
sector bijection and orbit coverage. The specified specialization below
derives the catalogue, injectivity and empty compatibility shell internally. -/
theorem family_from_sector_orbit
    (nu0 : S) (hOrbit : ∀ nu : S, ∃ a : A, a • nu0 = nu)
    (e0 : Fibre pX nu0 ≃ Fibre pY nu0)
    (he0 : ∀ (a : A) (ha : a • nu0 = nu0) (x : Fibre pX nu0),
      e0 (stabilizerFibreEquiv pX hpX nu0 a ha x) =
        stabilizerFibreEquiv pY hpY nu0 a ha (e0 x)) :
    ∃ e : FB ≃ FW, FamilyProperties iota hinj blocks R E1 e ∧
      ∀ (t : S → A) (ht : ∀ nu, t nu • nu0 = nu),
        e = transportedEquivalence iota hinj blocks R E1 nu0 t ht e0 := by
  let t : S → A := fun nu => Classical.choose (hOrbit nu)
  have ht : ∀ nu, t nu • nu0 = nu := fun nu => Classical.choose_spec (hOrbit nu)
  let e : FB ≃ FW := transportedEquivalence iota hinj blocks R E1 nu0 t ht e0
  have he : ∀ (a : A) (x : FB), e (a • x) = a • e x :=
    Formalisation.transportedEquiv_equivariant pX pY hpX hpY nu0 t ht e0 he0
  have hs : ∀ x : FB, pY (e x) = pX x :=
    Formalisation.transportedEquiv_preserves_base pX pY hpX hpY nu0 t ht e0
  have hfixed : ∀ (a : A) (x : FB), a • x.val = x.val ↔
      a • (e x).val = (e x).val := by
    intro a x
    rw [← faithfulIBr_smul_eq_iff iota hinj blocks R E1 a x,
      ← faithfulWeight_smul_eq_iff iota hinj blocks R E1 a (e x)]
    exact Formalisation.fixed_iff_of_injective_equivariant e.injective he a x
  refine ⟨e, ⟨he, hs, ?_, hfixed, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    apply Subgroup.ext
    intro a
    exact hfixed a x
  · intro a x
    change rY (e (a • x)) = a • rY (e x)
    rw [he]
    exact weightRadical_equivariant a (e x).val
  · exact ⟨(Equiv.sigmaFiberEquiv (radicalPart iota hinj blocks R E1 e)).symm,
      fun _ => rfl⟩
  · intro nu q
    let L : {x : FB // pX x = nu ∧ radicalPart iota hinj blocks R E1 e x = q} ≃
        {y : FW // pY y = nu ∧ rY y = q} := e.subtypeEquiv (by
      intro x
      change (pX x = nu ∧ rY (e x) = q) ↔ (pY (e x) = nu ∧ rY (e x) = q)
      rw [hs])
    exact ⟨L, fun _ => rfl⟩
  · intro t' ht'
    exact Formalisation.transportedEquiv_independent_of_transporter
      pX pY hpX hpY nu0 t t' ht ht' e0 he0

/-- The manuscript transport and fixed-iff deduction on specified carriers.
The only specified operations input is R. Its catalogue, the root-derived
Brauer injectivity and the empty routine compatibility shell are internal.
Faithful-sector coverage is derived from the centre/inversion cases. -/
theorem faithful_sector_replacement_transport
    (nu0 : FaithfulSector (k := k) (X := G))
    (hcase : SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit.FaithfulSectorOrbitCases
      (G := G)) :
    letI : Fintype (ActualBlock (k := k) (X := G)) :=
      R.1.operations.ambientBlockData.fintypeBlock
    let inj := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
    let bs := R.1.operations.ambientBlockData.blocks
    let routine : RoutineTransportInput iota inj bs R := ⟨⟩
    let bP := faithfulBrauerSector iota inj bs R routine
    let wP := faithfulWeightSector iota inj bs R routine
    ∀ (e0 : Fibre bP nu0 ≃ Fibre wP nu0),
      (∀ (a : (MulAut G)ᵐᵒᵖ) (ha : a • nu0 = nu0) (x : Fibre bP nu0),
        e0 (stabilizerFibreEquiv bP
          (brauerProjection_equivariant iota inj bs R routine) nu0 a ha x) =
          stabilizerFibreEquiv wP
            (weightProjection_equivariant iota inj bs R routine) nu0 a ha (e0 x)) →
      ∃ e : FaithfulIBr iota inj bs R routine ≃ FaithfulWeight iota inj bs R routine,
        FamilyProperties iota inj bs R routine e ∧
        ∀ (t : FaithfulSector (k := k) (X := G) → (MulAut G)ᵐᵒᵖ)
          (ht : ∀ nu, t nu • nu0 = nu),
          e = transportedEquivalence iota inj bs R routine nu0 t ht e0 := by
  let : Fintype (ActualBlock (k := k) (X := G)) :=
    R.1.operations.ambientBlockData.fintypeBlock
  exact family_from_sector_orbit iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    R.1.operations.ambientBlockData.blocks R ⟨⟩ nu0
    (SporadicFi24P3Definition44NamedCarrierFaithfulSectorOrbit.faithfulSector_orbit nu0 hcase)

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierFaithfulSectorFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
