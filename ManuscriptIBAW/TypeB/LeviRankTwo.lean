import ModularRep.PaperProofs.TypeBCurrentLeviFactorSelection

/-!
# Principal characters on rank two Levi factors

The rank two step of manuscript Proposition 4.13 concerns the principal
2-block of Sp4. Trivial field action is treated directly. For an odd field
of order at least nine, the character source is restricted to the principal
block. It is the principal stabiliser
assertion obtained from the verification following Brough--Schaeffer Fry,
Lemma 4.5, and their Lemma 4.6, with diagonal conjugation as in the manuscript.
Its interpretation on the specified matrix group and root embedding is an
explicit assumption.

The matrix calculation separates the diagonal and field actions at the
chosen character. The geometric identification then transports this
factorisation to the original rational Levi factor. No assertion about
Brauer characters outside the principal block is required.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

namespace ManuscriptIBAW.TypeB.LeviRankTwo

open Formalisation ModularRep ModularRep.PaperProofs
open TypeBRegularLeviRationalCarriers TypeBComponentCycleNormalization
open TypeBLeviRepresentativeCarriers TypeBLeviRepresentativeSelection
open TypeBLeviReturnB2Coefficient TypeBLeviReturnB2Application
open TypeBLeviReturnB2Diagonal TypeBLeviReturnB2MatrixAction
open TypeBRegularLeviCharacterActionAdapter TypeBComponentReturnCarrierTransport
open TypeBLeviReturnPowerSelection TypeBLeviReturnPowerAutomorphism
open TypeBCurrentLeviFactorSelection TypeBCentralKernelBlockSource
open TypeBCentralKernelSpinFibreIdentification
open EvenFieldAssumption53Relative
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section Standard

variable {F : Type} [Field F] [Finite F]
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  (coordinates : MatrixKernelSource F) (odd : Odd (Nat.card F))
  (iota : PrimeRegularRootEmbedding 2 k K (Sp4 F))
  (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Separation is needed only at the character whose stabiliser is computed. -/
theorem standard_factorization_at (chi : IBr iota)
    (separation : ∀ sigma : StandardField (F := F) p,
      IrreducibleBrauerCharacter.twist iota chi (diagonalAut coordinates odd) =
          IrreducibleBrauerCharacter.twist iota chi (sigma : MulAut (Sp4 F)) →
        IrreducibleBrauerCharacter.twist iota chi (diagonalAut coordinates odd) = chi ∧
          IrreducibleBrauerCharacter.twist iota chi (sigma : MulAut (Sp4 F)) = chi) :
    letI := rightAutomorphismAction iota (pcspAction coordinates)
    letI := rightAutomorphismAction iota (StandardField (F := F) p).subtype
    ProductStabilizerFactorization (D := TypeBConformalDualCarriers.PCSp F 2)
      (E := StandardField (F := F) p) chi := by
  let := rightAutomorphismAction iota (pcspAction coordinates)
  let := rightAutomorphismAction iota (StandardField (F := F) p).subtype
  intro d sigma
  constructor
  · intro hcombined
    have hrel : d⁻¹ • chi = sigma • chi := by
      have h := congrArg (fun z : IBr iota => d⁻¹ • z) hcombined
      simpa only [inv_smul_smul] using h.symm
    change IrreducibleBrauerCharacter.twist iota chi
      (pcspAction coordinates ((d⁻¹)⁻¹)) =
        IrreducibleBrauerCharacter.twist iota chi
          ((StandardField (F := F) p).subtype sigma⁻¹) at hrel
    rw [inv_inv] at hrel
    have hfield : sigma • chi = chi := by
      change IrreducibleBrauerCharacter.twist iota chi
        ((StandardField (F := F) p).subtype sigma⁻¹) = chi
      rcases pcsp_twist_cases coordinates odd iota d chi with hinner | hdiagonal
      · exact hrel.symm.trans hinner
      · exact (separation sigma⁻¹ (hdiagonal.symm.trans hrel)).2
    exact ⟨by simpa only [hfield] using hcombined, hfield⟩
  · rintro ⟨hdiagonal, hfield⟩
    rw [hfield, hdiagonal]

end Standard

section Factors

variable {A : Type} [Group A] {Frob : MulAut A} {Lbar : Subgroup A}
  [Finite (fixedPoints Frob.toMonoidHom)]
  {E : Type} [Group E] [Finite E] [IsCyclic E]
  {C : Type} [Fintype C] {m : C → ℕ}
  {leviStable : Lbar.map Frob.toMonoidHom = Lbar}
  {k K : Type} [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  {geometry : PrimalData Frob Lbar leviStable m}
  {field : FieldData Frob Lbar E}
  {root : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom Lbar)}
  {theta0 : IBr (rootN Frob Lbar root)}
  {presentation : Presentation geometry field root theta0} {c : C}

/-- Geometric coordinates and the character assertion for the principal block.
The block and its supported character belong to the original Levi factor.
The source on the standard group uses their transported block and roots. -/
structure Sources (presentation : Presentation geometry field root theta0) (c : C) where
  p : ℕ
  f : ℕ
  FQ : Type
  Astd : Type
  [fieldFQ : Field FQ]
  [finiteFQ : Finite FQ]
  [fieldAstd : Field Astd]
  [algebra : Algebra FQ Astd]
  [prime : Fact p.Prime]
  [charFQ : CharP FQ p]
  [charAstd : CharP Astd p]
  real : B2Realization presentation c p f FQ Astd
  coordinates : MatrixKernelSource FQ
  diagonal : real.DiagonalSource coordinates
  odd : Odd (Nat.card FQ)
  block : LiteralPrimitiveBlock k (Base m geometry.factor c)
  principal : IsPrincipal block
  supported : Supported (presentation.factorRoot c) block (presentation.localBase c)
  characterSource :
    (∀ sigma : StandardField (F := FQ) p, (sigma : MulAut (Sp4 FQ)) = 1) ∨
    (9 ≤ Nat.card FQ ∧ ∀ chi : IBr real.standardRoot,
      Supported real.standardRoot (primitiveBlockEquiv real.identification block) chi →
      ∀ sigma : StandardField (F := FQ) p,
        IrreducibleBrauerCharacter.twist real.standardRoot chi (diagonalAut coordinates odd) =
            IrreducibleBrauerCharacter.twist real.standardRoot chi (sigma : MulAut (Sp4 FQ)) →
          IrreducibleBrauerCharacter.twist real.standardRoot chi (diagonalAut coordinates odd) = chi ∧
            IrreducibleBrauerCharacter.twist real.standardRoot chi (sigma : MulAut (Sp4 FQ)) = chi)

attribute [instance] Sources.fieldFQ Sources.finiteFQ Sources.fieldAstd
  Sources.algebra Sources.prime Sources.charFQ Sources.charAstd

variable {p f : ℕ} {FQ Astd : Type} [Field FQ] [Finite FQ] [Field Astd]
  [Algebra FQ Astd] [Fact p.Prime] [CharP FQ p] [CharP Astd p]
  (real : B2Realization presentation c p f FQ Astd)
  {coordinates : MatrixKernelSource FQ} (diagonal : real.DiagonalSource coordinates)

include diagonal in
/-- Transport a factorisation at this character through the original component
and conjugation maps. No surjective lift to the conformal group is needed. -/
theorem factorization_on_original
    (standard :
      letI := rightAutomorphismAction real.standardRoot (pcspAction coordinates)
      letI := rightAutomorphismAction real.standardRoot
        (Subgroup.zpowers (fieldGenerator FQ p)).subtype
      ProductStabilizerFactorization (D := TypeBConformalDualCarriers.PCSp FQ 2)
        (E := Subgroup.zpowers (fieldGenerator FQ p)) real.standardBase) :
    letI := rightAutomorphismAction (presentation.factorRoot c)
      (geometry.diagonalAction (first m c))
    letI := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
    ProductStabilizerFactorization (D := geometry.diagonalGroup (first m c))
      (E := presentation.ReturnGroup c) (presentation.localBase c) ∧
    SemidirectStabilizerFactors (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c) := by
  let := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  let := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  let := rightAutomorphismAction real.standardRoot (pcspAction coordinates)
  let := rightAutomorphismAction real.standardRoot
    (Subgroup.zpowers (fieldGenerator FQ p)).subtype
  let := rightAutomorphismAction real.standardRoot
    (canonicalReturn real.identification (geometry.diagonalAction (first m c)))
  let := rightAutomorphismAction real.standardRoot
    (canonicalReturn real.identification (presentation.localH c))
  let beta := IrreducibleBrauerCharacter.equivAlongMulEquiv
    (presentation.factorRoot c) real.identification
  have return_transport (r0 : presentation.ReturnGroup c)
      (chi : IBr (presentation.factorRoot c)) :
      beta (r0 • chi) = real.returnToField r0 • beta chi := by
    rw [brauerAction_transport (presentation.factorRoot c) real.identification
      (presentation.localH c)]
    change IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
      (canonicalReturn real.identification (presentation.localH c) r0⁻¹) =
        IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
          (canonicalReturn real.identification (presentation.localH c) r0)⁻¹
    rw [map_inv]
  have factor : ProductStabilizerFactorization
      (D := geometry.diagonalGroup (first m c)) (E := presentation.ReturnGroup c)
      (presentation.localBase c) := by
    intro d r0
    obtain ⟨x, hx⟩ := real.diagonal_image_lift diagonal d
    have diagonal_transport (chi : IBr (presentation.factorRoot c)) :
        beta (d • chi) = x • beta chi := by
      rw [brauerAction_transport (presentation.factorRoot c) real.identification
        (geometry.diagonalAction (first m c))]
      change IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
        (canonicalReturn real.identification (geometry.diagonalAction (first m c)) d⁻¹) =
          IrreducibleBrauerCharacter.twist real.standardRoot (beta chi)
            (pcspAction coordinates x⁻¹)
      rw [map_inv, hx, map_inv]
    constructor
    · intro equality
      have equalityS : x • (real.returnToField r0 • real.standardBase) = real.standardBase := by
        change x • (real.returnToField r0 • beta (presentation.localBase c)) =
          beta (presentation.localBase c)
        rw [← return_transport r0 (presentation.localBase c),
          ← diagonal_transport (r0 • presentation.localBase c)]
        exact congrArg beta equality
      obtain ⟨hd, hr⟩ := (standard x (real.returnToField r0)).mp equalityS
      exact ⟨beta.injective ((diagonal_transport (presentation.localBase c)).trans hd),
        beta.injective ((return_transport r0 (presentation.localBase c)).trans hr)⟩
    · rintro ⟨hd, hr⟩
      rw [hr, hd]
  exact ⟨factor,
    (semidirectStabilizerFactors_iff_productStabilizerFactorization
      (presentation.localD c) (presentation.localCompatible c)
      (presentation.localBase c)).mpr factor⟩

/-- The chosen principal constituent itself has the two required factorisations. -/
theorem Sources.representative (source : Sources presentation c) :
    FactorRepresentative presentation c := by
  let := rightAutomorphismAction (presentation.factorRoot c)
    (geometry.diagonalAction (first m c))
  let := rightAutomorphismAction (presentation.factorRoot c) (presentation.localH c)
  have support : Supported source.real.standardRoot
      (primitiveBlockEquiv source.real.identification source.block) source.real.standardBase := by
    exact TypeBCentralKernelButterflyCharacterIdentification.supported_along_of_lift_eq
      source.real.identification (presentation.factorRoot c) source.real.standardRoot source.block
      (presentation.localBase c) source.real.standardBase
      (funext fun z ↦ (presentation.factorRoot c).alongMulEquiv_lift source.real.identification z)
      rfl source.supported
  have separation : ∀ sigma : StandardField (F := source.FQ) source.p,
      IrreducibleBrauerCharacter.twist source.real.standardRoot source.real.standardBase
          (diagonalAut source.coordinates source.odd) =
        IrreducibleBrauerCharacter.twist source.real.standardRoot source.real.standardBase
          (sigma : MulAut (Sp4 source.FQ)) →
      IrreducibleBrauerCharacter.twist source.real.standardRoot source.real.standardBase
          (diagonalAut source.coordinates source.odd) = source.real.standardBase ∧
        IrreducibleBrauerCharacter.twist source.real.standardRoot source.real.standardBase
          (sigma : MulAut (Sp4 source.FQ)) = source.real.standardBase := by
    rcases source.characterSource with trivial | published
    · intro sigma equality
      have fixed : IrreducibleBrauerCharacter.twist source.real.standardRoot
          source.real.standardBase (sigma : MulAut (Sp4 source.FQ)) =
          source.real.standardBase := by
        rw [trivial sigma]
        exact IrreducibleBrauerCharacter.twist_refl _ _
      exact ⟨equality.trans fixed, fixed⟩
    · exact published.2 source.real.standardBase support
  have standard := standard_factorization_at source.coordinates source.odd
    source.real.standardRoot source.p source.real.standardBase separation
  obtain ⟨factor, semidirect⟩ := factorization_on_original source.real source.diagonal standard
  exact ⟨presentation.localBase c,
    ⟨1, one_smul (geometry.diagonalGroup (first m c)) (presentation.localBase c)⟩,
    factor, semidirect⟩

end Factors
end ManuscriptIBAW.TypeB.LeviRankTwo

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
this package's formalisation report and source records.
-/
