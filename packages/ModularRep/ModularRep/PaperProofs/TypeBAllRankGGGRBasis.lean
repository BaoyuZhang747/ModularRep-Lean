import ModularRep.PaperProofs.TypeBSpinGGGRRationalSpanBinding

/-!
# The rational-basis consumer for the actual all-rank Spin GGGRs

This supporting consumer takes the specified source built by the all-rank
application.  It does not construct the missing nonabelian source.  At the
application endpoint that source and the two literal identifications below
must be constructed internally from the selected actual-character data.

The carrier is exactly the rational span of the same K-valued principal
PIM functions.  Membership comes from natural PIM expansions, independence
from the checked specified K-basis, and dimension from the two checked PIM
dimension formulas.  No rational-valued character space is introduced.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBAllRankGGGR.Basis

open ModularRep OrdinaryIrreducibleCharacter TypeBCliffordCarriers
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBCentralKernelBlockSource
open TypeBSpinRationalUnipotentClassBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinGGGRRationalSpanBinding
open TypeBGGGRRankProposition412SourceInstantiation
open scoped MonoidAlgebra

local instance finiteTypeFintype (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  {N : NormSource n F} [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {parameters : OddFieldParameters F r f} {rank : 4 ≤ n}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {hcompat : StableReductionBrauerCharacterCompatibility Msys iota}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]
  {blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val)}
  {ordinary : OrdinaryBlockSource Msys iota blocks}
  {orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)}
  {columns : DecompositionColumnIndependenceSource Msys iota}
  {gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K}
  {m : ℕ} {classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)}
  {induction : GGGRInductionSource parameters
    (Nat.le_trans (show 3 ≤ 4 by decide) rank) gamma}
  {expansion : OddInductionExpansionCertificate Msys iota hcompat}

/-- The actual projected GGGR at the same exhaustive rational-class index,
as an element of the Q-span of the actual K-valued principal PIMs. -/
def principalGGGRQComponent (j : Fin m) : projectiveQSpan Msys iota b :=
  ⟨principalProjection Msys iota b blocks ordinary (gamma (classIndex j)),
    principalGGGR_mem_projectiveQ Msys iota b orthogonality blocks ordinary
      parameters (Nat.le_trans (show 3 ≤ 4 by decide) rank) gamma induction
      hcompat expansion (classIndex j)⟩

@[simp] theorem principalGGGRQComponent_val (j : Fin m) :
    (principalGGGRQComponent (parameters := parameters) (rank := rank)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (b := b) (blocks := blocks) (ordinary := ordinary)
      (gamma := gamma) (classIndex := classIndex) (induction := induction)
      (expansion := expansion) j).val =
      principalProjection Msys iota b blocks ordinary (gamma (classIndex j)) := rfl

variable (D : GGGRBasisSource m (physicalProjectiveSpace Msys iota b))
  (gggr_eq : ∀ j, D.gggr j = gamma (classIndex j))
  (projection_eq : D.principalProjection = principalProjection Msys iota b blocks ordinary)

include gggr_eq projection_eq in
/-- Supporting transfer from the internally constructed specified source.
The identities keep the same actual GGGRs and specified projector. -/
theorem principalGGGR_K_linearIndependent :
    LinearIndependent K (fun j : Fin m =>
      principalProjection Msys iota b blocks ordinary (gamma (classIndex j))) := by
  have h := D.gggrProjectiveBasis.linearIndependent.map'
    (physicalProjectiveSpace Msys iota b).subtype (Submodule.ker_subtype _)
  have h' : LinearIndependent K (fun j : Fin m => (D.principalGGGRComponent j).val) := by
    simpa only [D.coe_gggrProjectiveBasis, Function.comp_def,
      Submodule.subtype_apply] using h
  simpa only [GGGRBasisSource.principalGGGRComponent, projection_eq, gggr_eq] using h'

include D gggr_eq projection_eq in
/-- K-independence restricts to Q-independence of these exact vectors;
the ambient K-span is never restricted to obtain the rational carrier. -/
theorem principalGGGR_Q_linearIndependent :
    LinearIndependent ℚ
      (principalGGGRQComponent (parameters := parameters) (rank := rank)
        (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
        (hcompat := hcompat) (b := b) (blocks := blocks) (ordinary := ordinary)
        (gamma := gamma) (classIndex := classIndex) (induction := induction)
        (expansion := expansion)) := by
  apply LinearIndependent.of_comp (projectiveQSpan Msys iota b).subtype
  exact (principalGGGR_K_linearIndependent D gggr_eq projection_eq).restrict_scalars' ℚ

include D orthogonality columns in
/-- The specified source's class count gives the Q-dimension through the
same supported Brauer cardinal; no additional dimension input is needed. -/
theorem source_card_eq_Q_finrank :
    Fintype.card (Fin m) = Module.finrank ℚ (projectiveQSpan Msys iota b) := by
  calc
    Fintype.card (Fin m) = Module.finrank K (physicalProjectiveSpace Msys iota b) :=
      D.card_eq_finrank
    _ = Nat.card {phi : IBr iota // Supported iota b phi} :=
      physicalProjectiveSpace_finrank orthogonality Msys iota columns b
    _ = Module.finrank ℚ (projectiveQSpan Msys iota b) :=
      (projectiveQSpan_finrank Msys iota b orthogonality columns).symm

/-- A supporting all-rank rational-basis consumer.  The final specified
application must build D internally; this declaration alone is not the
nonabelian all-rank construction. -/
def rationalGGGRBasisOfPhysicalSource :
    Module.Basis (Fin m) ℚ (projectiveQSpan Msys iota b) :=
  basisOfLinearIndependentOfCardEqFinrank'
    (principalGGGRQComponent (parameters := parameters) (rank := rank)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (b := b) (blocks := blocks) (ordinary := ordinary)
      (gamma := gamma) (classIndex := classIndex) (induction := induction)
      (expansion := expansion))
    (principalGGGR_Q_linearIndependent (parameters := parameters) (rank := rank)
      (orthogonality := orthogonality) (Msys := Msys) (iota := iota)
      (hcompat := hcompat) (b := b) (blocks := blocks) (ordinary := ordinary)
      (gamma := gamma) (classIndex := classIndex) (induction := induction)
      (expansion := expansion) D gggr_eq projection_eq)
    (source_card_eq_Q_finrank (orthogonality := orthogonality) (columns := columns) D)

/-- The displayed basis vectors are exactly the actual principal GGGR
projections under the same exhaustive classIndex. -/
theorem rationalGGGRBasisOfPhysicalSource_apply (j : Fin m) :
    ((rationalGGGRBasisOfPhysicalSource (parameters := parameters) (rank := rank)
      (orthogonality := orthogonality) (columns := columns)
      (Msys := Msys) (iota := iota) (hcompat := hcompat) (b := b)
      (blocks := blocks) (ordinary := ordinary) (gamma := gamma)
      (classIndex := classIndex) (induction := induction) (expansion := expansion)
      D gggr_eq projection_eq) j).val =
      principalProjection Msys iota b blocks ordinary (gamma (classIndex j)) := by
  simp only [rationalGGGRBasisOfPhysicalSource,
    coe_basisOfLinearIndependentOfCardEqFinrank', principalGGGRQComponent]

end ModularRep.PaperProofs.TypeBAllRankGGGR.Basis


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
