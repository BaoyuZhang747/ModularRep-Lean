import ModularRep.PaperProofs.TypeBRankThreePrincipalFixedRootFamilyBinding
import ModularRep.PaperProofs.TypeBMatrixOmegaPrimeToTwoCover
import ModularRep.PaperProofs.TypeBBSCentralCharacterQuotient
import ModularRep.PaperProofs.EvenFieldFLZCentrelessCentralKernel

/-!
# The principal family's computed common reference quotient

The reference is the trivial character in the prescribed specified principal
block. The actual identity prime-to-two cover forces centrelessness, so the
family's common central kernel and all same-reference quotient characters
are constructed. Their calibrated roots and original character values agree
with the existing computed character-central quotient. No matched ambient,
weight descent or extension is supplied by this construction.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalReferenceBinding

open ModularRep CharacterWeight FDRepSimpleClassKZero
open TypeBRankThreePrincipalCountBinding TypeBLocalReductionInstantiation
open TypeBCentralKernelBlockSource TypeBFixedRootDefinitionFamily
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZ318FixedTheoremGate
open EvenFieldFLZBAWGoodFamily EvenFieldFLZCentrelessCentralKernel
open TypeBCliffordCarriers

section Trivial

variable {k X : Type} [Field k] [Group X]

/-- A subrepresentation of the residue field is either zero or the field. -/
theorem trivialRepresentation_irreducible :
    Representation.IsIrreducible (1 : Representation k X k) := by
  letI : Nontrivial (Subrepresentation (1 : Representation k X k)) :=
    ⟨⟨⊥, ⊤, by
      intro h
      exact (bot_ne_top : (⊥ : Submodule k k) ≠ ⊤)
        (congrArg Subrepresentation.toSubmodule h)⟩⟩
  letI : IsSimpleOrder (Submodule k k) :=
    is_simple_module_of_finrank_eq_one (Module.finrank_self k)
  refine IsSimpleOrder.mk ?_
  intro W
  rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.ext h)
  · exact Or.inr (Subrepresentation.ext h)

variable {K : Type} [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
  [Finite X] (root : PrimeRegularRootEmbedding 2 k K X)

/-- The affording representation is the actual one-dimensional trivial module. -/
def trivialBrauer : IBr root :=
  ⟨Representation.brauerCharacterOfRootEmbedding (1 : Representation k X k) root,
    ⟨FDRep.of (1 : Representation k X k), trivialRepresentation_irreducible, rfl⟩⟩

/-- The same principal-idempotent test supplies its actual module support. -/
theorem trivialBrauer_supported (b : LiteralPrimitiveBlock k X) (hb : IsPrincipal b) :
    Supported root b (trivialBrauer root) :=
  ⟨FDRep.of (1 : Representation k X k), trivialRepresentation_irreducible, rfl, hb⟩

end Trivial

local instance groupFintype (X : Type) [Group X] [Finite X] : Fintype X :=
  Fintype.ofFinite X

variable {F K O k : Type} [Field F] [Finite F]
  [Field K] [CharZero K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  (S : OmegaWeightSource (k := k) (K := K) F)
  (SH : SOWeightSource (k := k) (K := K) F)
  (literal : ∀ c, S.operations.ambientBlockData.blockIdempotent c = c.val)
  (literalH : ∀ c, SH.operations.ambientBlockData.blockIdempotent c = c.val)
  (Msys : ModularSystem 2 K O k)
  (root : PrimeRegularRootEmbedding 2 k K (G F))
  (calibration : RootResidueCompatible Msys root)
  [HasEnoughRootsOfUnity K (Nat.card (G F))]
  (navarro : ∀ (X : Type) [Group X] [Finite X]
    [HasEnoughRootsOfUnity K (Nat.card X)]
    (iota : PrimeRegularRootEmbedding 2 k K X)
    (compatible : RootResidueCompatible Msys iota),
      ScopedDefectZeroReductionSource Msys iota compatible)
  (guard : GuardedBlockCompatibility root S.operations)
  (b : LiteralPrimitiveBlock k (G F))

/-- The already constructed family problem, with no altered carrier or reduction. -/
abbrev problem : Definition35Problem :=
  (TypeBRankThreePrincipalFixedRootFamilyBinding.family
    S SH literal literalH Msys root calibration navarro guard).problem b

/-- The common reference is an output, chosen concretely in the principal block. -/
def reference (hb : IsPrincipal b) :
    Definition35Brauer (problem S SH literal literalH Msys root calibration navarro guard b) :=
  TypeBRankThreePrincipalFixedRootFamilyBinding.brauerFibreEquiv
    S SH literal literalH Msys root calibration navarro guard b
    ⟨trivialBrauer root, trivialBrauer_supported root b hb⟩

@[simp] theorem reference_val (hb : IsPrincipal b) :
    (reference S SH literal literalH Msys root calibration navarro guard b hb).val =
      trivialBrauer root := rfl

/-- Both APIs use the same chosen affording representation of the same character. -/
theorem centralKernel_eq
    (psi : Definition35Brauer
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    centralCharacterKernel
        (problem S SH literal literalH Msys root calibration navarro guard b) psi =
      TypeBBSCentralCharacterQuotient.centralKernel root psi.val := rfl

variable {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))

/-- The cover is the existing actual identity cover, on the unchanged family group. -/
def cover : EllPrimeCoverSource 2
    (TypeBRankThreePrincipalFixedRootFamilyBinding.family
      S SH literal literalH Msys root calibration navarro guard).H :=
  TypeBMatrixOmegaPrimeToTwoCover.identityEllPrimeCover
    3 F parameters le_rfl N C centreSpin fullCover simple nonabelian

/-- Its projection is literally the identity on matrix Omega. -/
@[simp] theorem cover_quotient :
    (cover S SH literal literalH Msys root calibration navarro guard
      parameters N C centreSpin fullCover simple nonabelian).quotient =
      MonoidHom.id (G F) := rfl

include parameters N C centreSpin fullCover simple nonabelian in
/-- The identity cover's exact kernel equation proves centrelessness. -/
theorem centreless : Subgroup.center (G F) = ⊥ := by
  have h := (TypeBMatrixOmegaPrimeToTwoCover.identityEllPrimeCover
    3 F parameters le_rfl N C centreSpin fullCover simple nonabelian).quotient_kernel.symm
  exact h.trans ((MonoidHom.ker_eq_bot_iff _).mpr (fun _ _ hxy => hxy))

include parameters N C centreSpin fullCover simple nonabelian in
/-- Every original character uses the reference's computed central kernel. -/
theorem commonKernel (hb : IsPrincipal b)
    (psi : Definition35Brauer
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    centralCharacterKernel
        (problem S SH literal literalH Msys root calibration navarro guard b) psi =
      centralCharacterKernel
        (problem S SH literal literalH Msys root calibration navarro guard b)
        (reference S SH literal literalH Msys root calibration navarro guard b hb) :=
  centralCharacterKernel_eq_of_centerless
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian) psi
    (reference S SH literal literalH Msys root calibration navarro guard b hb)

/-- Every character descends to the one concrete reference quotient. -/
def quotientBrauer (hb : IsPrincipal b)
    (psi : Definition35Brauer
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    CentralQuotientBrauerSource
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) psi :=
  centerlessCentralQuotientBrauerSourceFromReference
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) psi

/-- The quotient lift is the prescribed original lift for every character. -/
theorem quotientBrauer_root_lift (hb : IsPrincipal b)
    (psi : Definition35Brauer
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).iota.lift = root.lift :=
  centerlessCentralQuotientBrauerSourceFromReference_iota_lift
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (centreless parameters N C centreSpin fullCover simple nonabelian)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) psi

/-- The quotient uses the same modular-system calibration. -/
theorem quotientBrauer_residue (hb : IsPrincipal b)
    (psi : Definition35Brauer
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    RootResidueCompatible Msys
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi).iota :=
  TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue Msys root calibration
    (centerlessCentralCharacterQuotientEquiv
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (centreless parameters N C centreSpin fullCover simple nonabelian)
      (reference S SH literal literalH Msys root calibration navarro guard b hb)).symm

/-- The descended function is the existing computed quotient's Brauer transport. -/
theorem quotientBrauer_val (hb : IsPrincipal b)
    (psi : Definition35Brauer
      (problem S SH literal literalH Msys root calibration navarro guard b)) :
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val =
      (TypeBBSCentralCharacterQuotient.brauerEquiv root
        (reference S SH literal literalH Msys root calibration navarro guard b hb).val
        (centreless parameters N C centreSpin fullCover simple nonabelian) psi.val).val := by
  ext x
  rfl

/-- The same reference quotient also carries the derived quotient-cover data. -/
def quotientCover (hb : IsPrincipal b) :
    CentralQuotientCoverSource
      (TypeBRankThreePrincipalFixedRootFamilyBinding.family
        S SH literal literalH Msys root calibration navarro guard)
      (cover S SH literal literalH Msys root calibration navarro guard
        parameters N C centreSpin fullCover simple nonabelian) b
      (reference S SH literal literalH Msys root calibration navarro guard b hb) :=
  centerlessCentralQuotientCoverSource
    (TypeBRankThreePrincipalFixedRootFamilyBinding.family
      S SH literal literalH Msys root calibration navarro guard)
    (cover S SH literal literalH Msys root calibration navarro guard
      parameters N C centreSpin fullCover simple nonabelian)
    (centreless parameters N C centreSpin fullCover simple nonabelian) b
    (reference S SH literal literalH Msys root calibration navarro guard b hb)

end ModularRep.PaperProofs.TypeBRankThreePrincipalReferenceBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
