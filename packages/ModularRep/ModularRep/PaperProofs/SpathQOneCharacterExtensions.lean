import ModularRep.BrauerCharacterExtensionBridge
import ModularRep.BrauerCharacterExtensionWitnessTransport
import ModularRep.PaperProofs.CanonicalLocalBaseTransport

/-!
# Character extensions in the trivial-radical branch

For a matched weight whose quotient radical is trivial, the ambient local
normaliser is canonically the whole ambient group.  One Brauer-character
extension can therefore supply both the global and local extension fields,
after transport across the canonical subgroup equivalences.

The cyclic-extension principle remains an explicit standard source.  The
carrier transports and the construction of the two extension fields are
kernel deductions.
-/

noncomputable section

namespace ModularRep.PaperProofs.SpathQOneCharacterExtensions

open ModularRep
open ModularRep.PaperProofs.EvenFieldFLZBAWGoodFamily
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions

universe u

section CommonExtension

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A]

/-- A realised irreducible Brauer character of a normal base subgroup,
together with one representation extension to the ambient group. -/
structure QOneCommonExtensionData
    (N : Subgroup A) [N.Normal]
    (baseRoot : PrimeRegularRootEmbedding p k K N)
    (baseBrauer : IBr baseRoot) where
  realisation : FDRep k N
  irreducible : Representation.IsIrreducible realisation.ρ
  affords : Representation.brauerCharacterOfRootEmbedding
    realisation.ρ baseRoot = baseBrauer.1
  extension : Representation.Extension N realisation.ρ

/-- The common representation extension supplies an ambient irreducible
Brauer character extending the prescribed base character. -/
noncomputable def QOneCommonExtensionData.ambientWitness
    {N : Subgroup A} [N.Normal]
    {baseRoot : PrimeRegularRootEmbedding p k K N}
    {baseBrauer : IBr baseRoot}
    (E : QOneCommonExtensionData N baseRoot baseBrauer)
    (ambientRoot : PrimeRegularRootEmbedding p k K A)
    (hlift : baseRoot.lift = ambientRoot.lift) :
    Representation.Extension.BrauerCharacterExtensionWitness
      ambientRoot baseRoot baseBrauer :=
  Representation.Extension.brauerCharacterExtensionWitnessOfLiftEq
    E.extension E.irreducible ambientRoot baseRoot baseBrauer
      E.affords hlift

/-- Construct the common extension packet from the standard cyclic-extension
principle and fixedness of the base Brauer character. -/
theorem exists_qOneCommonExtensionData
    {N : Subgroup A} [N.Normal]
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (baseRoot : PrimeRegularRootEmbedding p k K N)
    (baseBrauer : IBr baseRoot)
    (hcyclic : IsCyclic (A ⧸ N))
    (hfixed : ∀ a : A,
      IrreducibleBrauerCharacter.twist baseRoot baseBrauer
        (MulAut.conjNormal a) = baseBrauer) :
    Nonempty (QOneCommonExtensionData N baseRoot baseBrauer) := by
  rcases
      Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
        principle baseRoot baseBrauer hcyclic hfixed with
    ⟨W, hW, hcharacter, ⟨E⟩⟩
  exact ⟨⟨W, hW, hcharacter.symm, E⟩⟩

end CommonExtension

section SpathCarriers

/-- A trivial quotient radical has trivial image in the ambient group. -/
theorem ambientRadical_eq_bot_of_quotientRadical_eq_bot
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥) :
    ambientRadical P reference psi w quotient ambient = ⊥ := by
  unfold ambientRadical
  rw [hQ, Subgroup.map_bot]

/-- When the quotient radical is trivial, its ambient normaliser is
canonically the whole ambient group. -/
def qOneAmbientLocalEquiv
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥) :
    AmbientLocalGroup P reference psi w quotient ambient ≃* ambient.A :=
  (MulEquiv.subgroupCongr (by
    change Subgroup.normalizer
      (ambientRadical P reference psi w quotient ambient : Set ambient.A) = ⊤
    rw [ambientRadical_eq_bot_of_quotientRadical_eq_bot ambient hQ]
    exact Subgroup.normalizer_eq_top (H := (⊥ : Subgroup ambient.A)))).trans
      Subgroup.topEquiv

/-- The base inside the trivial-radical local normaliser is canonically the
ambient base itself. -/
def qOneAmbientBaseEquiv
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥) :
    ambient.base ≃*
      AmbientLocalBase P reference psi w quotient ambient where
  toFun x := ⟨⟨x.1, by
    change x.1 ∈ Subgroup.normalizer
      (ambientRadical P reference psi w quotient ambient : Set ambient.A)
    rw [ambientRadical_eq_bot_of_quotientRadical_eq_bot ambient hQ]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The ambient and base equivalences form the literal subgroup square used
to transport an extension witness. -/
@[simp]
theorem qOneAmbientBase_square
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥) :
    (qOneAmbientLocalEquiv ambient hQ).toMonoidHom.comp
        (AmbientLocalBase P reference psi w quotient ambient).subtype =
      ambient.base.subtype.comp
        (qOneAmbientBaseEquiv ambient hQ).symm.toMonoidHom := by
  ext x
  rfl

/-- At the trivial radical, the intermediate local normaliser is canonically
the intermediate group itself. -/
def qOneIntermediateLocalEquiv
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥)
    (J : Subgroup ambient.A) :
    IntermediateLocalNormalizer (w := w) ambient J ≃* J where
  toFun x := x.1
  invFun x := ⟨x, by
    change (x.1 : ambient.A) ∈ Subgroup.normalizer
      (ambientRadical P reference psi w quotient ambient : Set ambient.A)
    rw [ambientRadical_eq_bot_of_quotientRadical_eq_bot ambient hQ]
    simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Equivalent subgroup formulation of the preceding carrier collapse. -/
theorem qOneIntermediateLocalNormalizer_eq_top
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient)
    (hQ : quotientRadical P reference w = ⊥)
    (J : Subgroup ambient.A) :
    IntermediateLocalNormalizer (w := w) ambient J = ⊤ := by
  unfold IntermediateLocalNormalizer
  change (Subgroup.normalizer
    (ambientRadical P reference psi w quotient ambient : Set ambient.A)).comap
      J.subtype = ⊤
  rw [ambientRadical_eq_bot_of_quotientRadical_eq_bot ambient hQ]
  rw [Subgroup.normalizer_eq_top (H := (⊥ : Subgroup ambient.A))]
  ext x
  simp

end SpathCarriers

section LiveExtensionPacket

/-- The only local coherence data needed after the local-base equivalence is
fixed canonically.  The remaining field identifies the supplied local Brauer
character with the transported global base character. -/
structure QOneLocalTransportData
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    (localInflation : QuotientLocalInflationSource P reference w weight)
    (ambient : SpathAmbientGroup P reference psi quotient) where
  quotientRadical_eq_bot : quotientRadical P reference w = ⊥
  localBrauerCompatibility :
    PrimeRegularClassFunction.pullback
        (qOneAmbientBaseEquiv ambient quotientRadical_eq_bot).symm.toMonoidHom
        (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
          ambient.baseEquiv quotient.brauer).1 =
      (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
        (canonicalLocalBaseEquiv ambient) localInflation.brauer).1

/-- Common extension data specialised to the exact global base character in
the live Spath carrier. -/
abbrev LiveQOneCommonExtensionData
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    (ambient : SpathAmbientGroup P reference psi quotient) :=
  QOneCommonExtensionData ambient.base
    (quotient.iota.alongMulEquiv ambient.baseEquiv)
    (IrreducibleBrauerCharacter.alongMulEquiv quotient.iota
      ambient.baseEquiv quotient.brauer)

/-- Fill the live global and local Spath extension fields from one common
extension, transporting the local witness across the canonical
trivial-radical carrier square. -/
noncomputable def spathCharacterExtensionsOfQOneCommon
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (common : LiveQOneCommonExtensionData ambient)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localData : QOneLocalTransportData localInflation ambient) :
    SpathCharacterExtensions P reference psi w quotient weight
      localInflation ambient := by
  let global := common.ambientWitness ambientRoot hlift
  let eA := (qOneAmbientLocalEquiv ambient
    localData.quotientRadical_eq_bot).symm
  let eBase := qOneAmbientBaseEquiv ambient
    localData.quotientRadical_eq_bot
  let localWitness := global.alongMulEquivOfBase eA eBase
    (qOneAmbientBase_square ambient localData.quotientRadical_eq_bot)
    (localInflation.iota.alongMulEquiv
      (canonicalLocalBaseEquiv ambient))
    (IrreducibleBrauerCharacter.alongMulEquiv localInflation.iota
      (canonicalLocalBaseEquiv ambient) localInflation.brauer)
    localData.localBrauerCompatibility
  exact {
    ambientRoot := ambientRoot
    globalExtension := global
    localBaseEquiv := canonicalLocalBaseEquiv ambient
    localBaseEquiv_natural := canonicalLocalBaseEquiv_natural ambient
    localAmbientRoot := ambientRoot.alongMulEquiv eA
    localExtension := localWitness }

/-- The local ambient character is exactly the canonical transport of the
global ambient extension character. -/
@[simp]
theorem spathCharacterExtensionsOfQOneCommon_localExtension
    {P : Definition35Problem.{u}}
    {reference psi : Definition35Brauer P}
    {w : Definition35Weight P}
    {quotient : CentralQuotientBrauerSource P reference psi}
    {weight : QuotientWeightBrauerSource P reference w}
    {localInflation : QuotientLocalInflationSource P reference w weight}
    {ambient : SpathAmbientGroup P reference psi quotient}
    (common : LiveQOneCommonExtensionData ambient)
    (ambientRoot : PrimeRegularRootEmbedding P.p P.k P.K ambient.A)
    (hlift : (quotient.iota.alongMulEquiv ambient.baseEquiv).lift =
      ambientRoot.lift)
    (localData : QOneLocalTransportData localInflation ambient) :
    (spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
      localData).localExtension.1 =
      IrreducibleBrauerCharacter.alongMulEquiv ambientRoot
        (qOneAmbientLocalEquiv ambient
          localData.quotientRadical_eq_bot).symm
        ((spathCharacterExtensionsOfQOneCommon common ambientRoot hlift
          localData).globalExtension.1) :=
  rfl

end LiveExtensionPacket

end ModularRep.PaperProofs.SpathQOneCharacterExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
