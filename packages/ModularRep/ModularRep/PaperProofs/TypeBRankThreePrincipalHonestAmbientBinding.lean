import ModularRep.PaperProofs.TypeBRankThreePrincipalReferenceBinding
import ModularRep.PaperProofs.TypeBKoshitaniSpathHonestAmbientSource

/-!
# The honest ambient for the actual principal reference quotient

The existing modular existence certificate is applied to the constructed
principal reference, its computed quotient cover and the prescribed descended
character. The ambient root is constructed from the same modular system.
Restriction and root agreement retain the literal quotient embedding.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreePrincipalHonestAmbientBinding

open ModularRep CharacterWeight
open TypeBRankThreePrincipalCountBinding TypeBLocalReductionInstantiation
open TypeBCentralKernelBlockSource TypeBFixedRootDefinitionFamily
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZ318FixedTheoremGate EvenFieldFLZBAWGoodFamily
open TypeBCliffordCarriers TypeBModularGroupRootBinding
open SpathPositiveQTopBlockChoice
open TypeBRankThreePrincipalReferenceBinding

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
  {r f : ℕ} [CharP F r]
  (parameters : OddFieldParameters F r f) (N : NormSource 3 F)
  (C : TypeBCliffordOrthogonalSourceBinding.Source 3 F r f parameters le_rfl N)
  (centreSpin : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 r f F N)
  (fullCover : IsUniversalCentralExtension
    (TypeBCliffordOrthogonalSourceBinding.spinProjection 3 F parameters le_rfl N C))
  (simple : IsSimpleGroup (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (nonabelian : ¬ IsMulCommutative (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (hb : IsPrincipal b)
  (psi : Definition35Brauer
    (problem S SH literal literalH Msys root calibration navarro guard b))

/-- Every global output on this actual ambient restricts to this quotient character. -/
theorem global_restricts
    (ambient : SpathAmbientGroup
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi))
    (global : ChosenGlobalExtensionData ambient) :
    PrimeRegularClassFunction.pullback
        (quotientToAmbient
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
          (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
            parameters N C centreSpin fullCover simple nonabelian hb psi) ambient)
        global.globalExtension.1.val =
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val := by
  apply PrimeRegularClassFunction.ext
  intro x
  have h := congrArg
    (fun value : PrimeRegularClassFunction K ambient.base 2 =>
      value (PrimeRegularElement.map ambient.baseEquiv.toMonoidHom x))
    global.globalExtension.2
  change global.globalExtension.1.val
      (PrimeRegularElement.map
        (quotientToAmbient
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
          (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
            parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) x) = _
  change global.globalExtension.1.val
      (PrimeRegularElement.map
        (quotientToAmbient
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
          (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
            parameters N C centreSpin fullCover simple nonabelian hb psi) ambient) x) =
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val
      (PrimeRegularElement.map ambient.baseEquiv.symm.toMonoidHom
        (PrimeRegularElement.map ambient.baseEquiv.toMonoidHom x)) at h
  have hx : PrimeRegularElement.map ambient.baseEquiv.symm.toMonoidHom
      (PrimeRegularElement.map ambient.baseEquiv.toMonoidHom x) = x := by
    apply Subtype.ext
    exact ambient.baseEquiv.symm_apply_apply x.val
  exact h.trans (congrArg
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val hx)

/-- The constructed ambient lift agrees on the actual reference quotient's domain. -/
theorem quotientRoot_agrees
    (ambient : SpathAmbientGroup
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi))
    (zeta : rootsOfUnity
      (primeRegularExponent 2
        (CentralCharacterQuotient
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb))) k) :
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).iota.lift
        ((zeta : kˣ) : k) =
      (groupRoot Msys ambient.A).lift ((zeta : kˣ) : k) := by
  letI : Algebra O
      (problem S SH literal literalH Msys root calibration navarro guard b).K :=
    (inferInstance : Algebra O K)
  exact TypeBKoshitaniSpathHonestAmbientSource.quotientRoot_agrees
    (problem S SH literal literalH Msys root calibration navarro guard b)
    (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi) Msys
    (quotientBrauer_residue S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi) ambient zeta

/-- The same comparison retains the original prescribed root lift. -/
theorem originalRoot_agrees
    (ambient : SpathAmbientGroup
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi))
    (zeta : rootsOfUnity
      (primeRegularExponent 2
        (CentralCharacterQuotient
          (problem S SH literal literalH Msys root calibration navarro guard b)
          (reference S SH literal literalH Msys root calibration navarro guard b hb))) k) :
    root.lift ((zeta : kˣ) : k) =
      (groupRoot Msys ambient.A).lift ((zeta : kˣ) : k) :=
  (congrFun
    (quotientBrauer_root_lift S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi).symm
    ((zeta : kˣ) : k)).trans
    (quotientRoot_agrees S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi ambient zeta)

/-- The actual common quotient supplies all covering and central-faithfulness data. -/
theorem exists_ambient_global
    (fieldScope : SpathCoefficientField 2 k Msys.prime)
    (certificate : TypeBKoshitaniSpathHonestAmbientSource.ModularExistenceCertificate) :
    ∃ ambient : SpathAmbientGroup
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi),
      ∃ global : ChosenGlobalExtensionData ambient,
        global.ambientRoot = groupRoot Msys ambient.A := by
  letI : Algebra O
      (TypeBRankThreePrincipalFixedRootFamilyBinding.family
        S SH literal literalH Msys root calibration navarro guard).K :=
    (inferInstance : Algebra O K)
  exact TypeBKoshitaniSpathHonestAmbientSource.exists_ambient_global_of_quotientCover
    (TypeBRankThreePrincipalFixedRootFamilyBinding.family
      S SH literal literalH Msys root calibration navarro guard)
    (cover S SH literal literalH Msys root calibration navarro guard
      parameters N C centreSpin fullCover simple nonabelian) b
    (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
    (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi)
    (quotientCover S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb) Msys
    (quotientBrauer_residue S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi) fieldScope certificate

/-- One returned global extension has all the literal restriction and root anchors. -/
theorem exists_ambient_global_anchored
    (fieldScope : SpathCoefficientField 2 k Msys.prime)
    (certificate : TypeBKoshitaniSpathHonestAmbientSource.ModularExistenceCertificate) :
    ∃ ambient : SpathAmbientGroup
      (problem S SH literal literalH Msys root calibration navarro guard b)
      (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
      (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
        parameters N C centreSpin fullCover simple nonabelian hb psi),
      ∃ global : ChosenGlobalExtensionData ambient,
        global.ambientRoot = groupRoot Msys ambient.A ∧
        PrimeRegularClassFunction.pullback
            (quotientToAmbient
              (problem S SH literal literalH Msys root calibration navarro guard b)
              (reference S SH literal literalH Msys root calibration navarro guard b hb) psi
              (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
                parameters N C centreSpin fullCover simple nonabelian hb psi) ambient)
            global.globalExtension.1.val =
          (quotientBrauer S SH literal literalH Msys root calibration navarro guard b
            parameters N C centreSpin fullCover simple nonabelian hb psi).brauer.val ∧
        ∀ zeta : rootsOfUnity
          (primeRegularExponent 2
            (CentralCharacterQuotient
              (problem S SH literal literalH Msys root calibration navarro guard b)
              (reference S SH literal literalH Msys root calibration navarro guard b hb))) k,
          root.lift ((zeta : kˣ) : k) = global.ambientRoot.lift ((zeta : kˣ) : k) := by
  obtain ⟨ambient, global, hroot⟩ :=
    exists_ambient_global S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi fieldScope certificate
  refine ⟨ambient, global, hroot,
    global_restricts S SH literal literalH Msys root calibration navarro guard b
      parameters N C centreSpin fullCover simple nonabelian hb psi ambient global, ?_⟩
  intro zeta
  exact (originalRoot_agrees S SH literal literalH Msys root calibration navarro guard b
    parameters N C centreSpin fullCover simple nonabelian hb psi ambient zeta).trans
    (congrArg
      (fun iota : PrimeRegularRootEmbedding 2 k K ambient.A =>
        iota.lift ((zeta : kˣ) : k)) hroot.symm)

end ModularRep.PaperProofs.TypeBRankThreePrincipalHonestAmbientBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
