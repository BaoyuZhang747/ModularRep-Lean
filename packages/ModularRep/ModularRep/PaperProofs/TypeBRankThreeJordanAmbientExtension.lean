import ModularRep.PaperProofs.TypeBRankThreeJordanRepresentativeApplication

/-!
# Extension of the retained ambient Jordan character

The accepted representative/Jordan endpoint is invoked once with its same
specified sources. Its four witnesses, original Levi extension and all packet,
block and stabilizer equations are retained. The already supplied cyclic
extension principle gives an extension of the same ambient character.
The proved field-fixer equality identifies the right semidirect factor with
the original Levi character's actual stabilizer in the chosen field group.

This is the ambient extension consequence. It does not construct a Morita
functor or identify a cohomology bimodule; the inherited specified source
interpretations remain explicit in the unchanged telescope.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeJordanAmbientExtension

open ModularRep FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBRankThreeNonprincipalApplication TypeBRankThreeNonprincipalGeometry
open TypeBRegularLeviRationalCarriers TypeBRankThreeFactorsPointSource
open TypeBRankThreeJordanDualLabel TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBLeviRepresentativeAssembly
open TypeBLeviRepresentativeTransport TypeBLeviRepresentativeClifford
open TypeBLeviRepresentativeField TypeBLemma47LeviApplication
open TypeBCharacteristicTwoConstituentSource TypeBCharacteristicTwoCorrespondenceSource
open TypeBCharacteristicTwoExtensionCarriers TypeBCharacteristicTwoCliffordKernel
open TypeBCharacteristicTwoCliffordApplication TypeBCharacteristicTwoGallagherSource
open TypeBCharacteristicTwoGallagherProduct
open TypeBRankThreeJordanSource TypeBRankThreeJordanPacketCarriers
open TypeBRankThreeJordanOriginalTransport TypeBRankThreeJordanPacketCopies
open TypeBRankThreeJordanActions TypeBRankThreeJordanCliffordCarriers
open TypeBRankThreeJordanMap TypeBRankThreeJordanTransfer
open TypeBRationalSeriesSource

/-- Equality of the actual field subgroups transports the complete honest
extension proposition, including its literal restriction map. -/
private theorem honest_field_extension_at_equal_stabilizer
    {G E k K : Type} [Group G] [Finite G] [Group E] [Finite E] [IsCyclic E]
    [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
    (iota : PrimeRegularRootEmbedding 2 k K G) (action : E →* MulAut G)
    (source812 : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (psi : IBr iota) (S : Subgroup E)
    (equal : fieldStabilizer iota action psi = S) :
    ∃ V : FDRep k G,
      Representation.IsIrreducible V.ρ ∧
      psi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
      ∃ rho : Representation k (G ⋊[action.comp S.subtype] S) V,
        Representation.IsIrreducible rho ∧
        Nonempty (Representation.Equiv
          (rho.pullback
            (SemidirectProduct.inl : G →* G ⋊[action.comp S.subtype] S)) V.ρ) := by
  cases equal
  exact honest_field_extension iota action source812 psi

variable {p f : ℕ} {F A E K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  [Group E] [Finite E] [IsCyclic E]
  (parameters : OddFieldParameters F p f) (normF : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) normF)
  [Finite (Spin 3 F normF)] [Finite (SpecialClifford 3 F)]
  (Msys : ModularSystem 2 K O k)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F normF))
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F normF))]
  (blocksG : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F normF) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F normF))]
  (ordinaryG : OrdinaryBlockSource Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG)
  (seriesG : Sources parameters Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG ordinaryG)
  (dualFrobenius : FrobeniusSource p f A)
  (dualPoints : RationalPointSource F A p f dualFrobenius)
  (dualGeometry : GeometrySource F A p f dualFrobenius dualPoints)
  (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (r : ManuscriptReduction parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b)
  (normA : NormSource 3 A) (chart : PairedChart normA r.levi)
  (Frob : MulAut (SpecialClifford 3 A))
  [Finite (fixedPoints Frob.toMonoidHom)]
  (iotaL : PrimeRegularRootEmbedding 2 k K (L Frob.toMonoidHom chart.primalLevi))
  [Fintype (LiteralPrimitiveBlock k (L Frob.toMonoidHom chart.primalLevi))]
  (blocksL : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (L Frob.toMonoidHom chart.primalLevi) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (L Frob.toMonoidHom chart.primalLevi))]
  (ordinaryL : OrdinaryBlockSource Msys iotaL
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaL) blocksL)
  (familyL : RationalSeriesSource K (L Frob.toMonoidHom chart.primalLevi)
    (TypeBRankThreeJordanLeviPacket.FullRationalIndex p (rationalLevi r)))
  (points : CliffordFixedPointSource 3 p f F A normF normA Frob)
  (field : FieldData Frob chart.primalLevi E)
  (perfect : commutator (Spin 3 F normF) = ⊤)
  (source : Certificate parameters normF orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
    iotaL blocksL ordinaryL familyL points field perfect)

variable {C : Type} [Fintype C] {m : C → ℕ}
  (geometry : PrimalData Frob chart.primalLevi source.primal_frobenius m)
  (iotaN : PrimeRegularRootEmbedding 2 k K (L0 Frob.toMonoidHom chart.primalLevi))
  (iotaGamma : PrimeRegularRootEmbedding 2 k K (Gamma Frob chart.primalLevi))

noncomputable local instance finiteH {T : Type} [Group T]
    (sigma : MulAut T) (U : Subgroup T) [Finite (fixedPoints sigma.toMonoidHom)] :
    Fintype (H sigma U) := Fintype.ofFinite (H sigma U)
noncomputable local instance finiteNInH {T : Type} [Group T]
    (sigma : MulAut T) (U : Subgroup T) [Finite (fixedPoints sigma.toMonoidHom)] :
    Fintype ((N sigma U).subgroupOf (H sigma U)) :=
  Fintype.ofFinite ((N sigma U).subgroupOf (H sigma U))
local instance quotientCommutative {T : Type} [Group T]
    (sigma : MulAut T) (U : Subgroup T) :
    IsMulCommutative (Gamma sigma U ⧸ N sigma U) :=
  quotientN_abelian sigma U

variable {BlockN : Type} [Fintype BlockN]
  {idempotentN : BlockN → k[(N Frob chart.primalLevi).subgroupOf (H Frob chart.primalLevi)]}
  (blocksN : BlockIdempotentDecomposition idempotentN)
  (catalogueH : BlockCentralCharacterCatalogue
    (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)))
  (catalogueN : BlockCentralCharacterCatalogue blocksN)

/-- The same selected representative and Jordan image, with both original
Levi and ambient Spin honest extensions over the original Levi field fixer. -/
theorem actual_representative_jordan_ambient_extension
    (decomposition : ∀ x : SpecialClifford 3 A,
      ∃ g ∈ SpinSubgroup 3 A normA, ∃ z ∈ Subgroup.center (SpecialClifford 3 A),
        x = g * z)
    (intersection : pairedLevi chart.primalLevi ⊓ SpinSubgroup 3 A normA ≤ chart.primalLevi)
    (lang : TypeBRankThreeJordanDiagonalProduct.LeviLangSource Frob chart.primalLevi)
    (roots_N_H : RootAgreement (H Frob chart.primalLevi) (N Frob chart.primalLevi)
      (rootH Frob chart.primalLevi iotaL) (rootN Frob chart.primalLevi iotaN))
    (fieldScope : SpathCoefficientField 2 k (rootH Frob chart.primalLevi iotaL).prime)
    (covering : FixedRestrictionCovering
      (H Frob chart.primalLevi) (N Frob chart.primalLevi) (N_le_H Frob chart.primalLevi)
      (rootH Frob chart.primalLevi iotaL) (rootN Frob chart.primalLevi iotaN)
      (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)) blocksN
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding (rootH Frob chart.primalLevi iotaL))
      (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
        (embeddedRoot (H Frob chart.primalLevi) (N Frob chart.primalLevi)
          (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN)))
      catalogueH catalogueN roots_N_H fieldScope)
    (P : Set (IBr (rootH Frob chart.primalLevi iotaL)))
    (psi0 : IBr (rootH Frob chart.primalLevi iotaL))
    (prescribedOrbit :
      letI := ambientBrauerAction (H Frob chart.primalLevi)
        (rootH Frob chart.primalLevi iotaL)
      P = MulAction.orbit (Gamma Frob chart.primalLevi) psi0)
    (initialPacket : InPacket iotaL blocksL
      (leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
        seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
        iotaL blocksL ordinaryL familyL)
      (TypeBLeviRepresentativeOriginalExtension.originalCharacter
        Frob chart.primalLevi iotaL psi0))
    (theta0 : IBr (rootN Frob chart.primalLevi iotaN))
    (occurs0 : Occurs (H Frob chart.primalLevi) (N Frob chart.primalLevi)
      (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
      (rootN Frob chart.primalLevi iotaN) psi0 theta0)
    (presentation : Presentation geometry field iotaN theta0)
    (S Q J : C → Type) [∀ c, Group (S c)] [∀ c, Finite (S c)]
    [∀ c, Group (Q c)] [∀ c, Group (J c)]
    (standard : StandardData presentation S Q J)
    (iotaI : ∀ theta : IBr (rootN Frob chart.primalLevi iotaN),
      PrimeRegularRootEmbedding 2 k K
        (BrauerInertia (H Frob chart.primalLevi) (N Frob chart.primalLevi)
          (rootN Frob chart.primalLevi iotaN) theta))
    (iotaA : ∀ theta : IBr (rootN Frob chart.primalLevi iotaN),
      PrimeRegularRootEmbedding 2 k K
        (AmbientInertia (N Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN) theta))
    (roots_N_G : RootsAgree iotaGamma (rootN Frob chart.primalLevi iotaN))
    (roots_A_G : ∀ theta, RootsAgree iotaGamma (iotaA theta))
    (roots_N_A : ∀ theta, RootsAgree (iotaA theta) (rootN Frob chart.primalLevi iotaN))
    (roots_I_A : ∀ theta, RootsAgree (iotaA theta) (iotaI theta))
    (multiplicityFree : MultiplicityFreeRestriction (N Frob chart.primalLevi)
      iotaGamma (rootN Frob chart.primalLevi iotaN))
    (above : ExistsAbovePrinciple k K)
    (homogeneousClifford : HomogeneousCliffordPrinciple k K)
    (source87 : Navarro87Principle k K)
    (source89 : ∀ theta, Navarro89Source (H Frob chart.primalLevi) (N Frob chart.primalLevi)
      (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
      (rootN Frob chart.primalLevi iotaN) theta (iotaI theta))
    (source820 : Navarro820AbelianProductPrinciple k K)
    (source812 : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k) :
    letI := ambientBrauerAction (H Frob chart.primalLevi)
      (rootH Frob chart.primalLevi iotaL)
    letI := ambientBrauerAction (N Frob chart.primalLevi)
      (rootN Frob chart.primalLevi iotaN)
    letI := originalAmbientAction Frob chart.primalLevi iotaL
    letI := originalFieldAction Frob chart.primalLevi iotaL field
    letI := cliffordBrauerAction iotaG
    letI := spinBrauerFieldAction points field.fieldPoints perfect iotaG
    let eL := leviIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r normA chart Frob
      iotaL blocksL ordinaryL familyL
    let eG := ambientIdempotent parameters normF orthogonal Msys iotaG blocksG ordinaryG
      seriesG dualFrobenius dualPoints dualGeometry b r
    ∃ (theta : IBr (rootN Frob chart.primalLevi iotaN))
      (y : Gamma Frob chart.primalLevi) (psiH : IBr (rootH Frob chart.primalLevi iotaL))
      (psi : Packet iotaL blocksL eL),
      psiH = y • psi0 ∧ theta = y • theta0 ∧ psiH ∈ P ∧
      Occurs (H Frob chart.primalLevi) (N Frob chart.primalLevi)
        (N_le_H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
        (rootN Frob chart.primalLevi iotaN) psiH theta ∧
      CentralCharacterCovers ((N Frob chart.primalLevi).subgroupOf (H Frob chart.primalLevi))
        (catalogueH.centralCharacter
          (blockIndex (rootH Frob chart.primalLevi iotaL)
            (blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)) psiH))
        (catalogueN.centralCharacter
          (irreducibleBrauerCharacterBlock
            (embeddedRoot (H Frob chart.primalLevi) (N Frob chart.primalLevi)
              (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN))
            (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
              (embeddedRoot (H Frob chart.primalLevi) (N Frob chart.primalLevi)
                (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN)))
            blocksN (embeddedCharacter (H Frob chart.primalLevi) (N Frob chart.primalLevi)
              (N_le_H Frob chart.primalLevi) (rootN Frob chart.primalLevi iotaN) theta))) ∧
      characterEquiv Frob chart.primalLevi iotaL psi.val = psiH ∧
      psi.val = TypeBLeviRepresentativeOriginalExtension.originalCharacter
        Frob chart.primalLevi iotaL psiH ∧
      Formalisation.SemidirectStabilizerFactors
        (cliffordFieldAction points field.fieldPoints)
        (clifford_semidirect_compatible points field.fieldPoints perfect iotaG)
        (source.jordan.character psi) ∧
      MulAction.stabilizer E (source.jordan.character psi) = MulAction.stabilizer E psi.val ∧
      InPacket iotaG blocksG eG (source.jordan.character psi) ∧
      supportingBlock iotaG blocksG (source.jordan.character psi) =
        (source.jordan.block ⟨supportingBlock iotaL blocksL psi.val, psi.property⟩).val ∧
      (∃ W : FDRep k (L Frob.toMonoidHom chart.primalLevi),
        Representation.IsIrreducible W.ρ ∧
        psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL ∧
        ∃ rho : Representation k
          (FieldSemidirect iotaL (originalField Frob chart.primalLevi field) psi.val) W,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (rho.pullback (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
              FieldSemidirect iotaL (originalField Frob chart.primalLevi field) psi.val)) W.ρ)) ∧
      let stabilizer := fieldStabilizer iotaL
        (originalField Frob chart.primalLevi field) psi.val
      let action := spinFieldAction points field.fieldPoints perfect
      ∃ V : FDRep k (Spin 3 F normF),
        Representation.IsIrreducible V.ρ ∧
        (source.jordan.character psi).val =
          Representation.brauerCharacterOfRootEmbedding V.ρ iotaG ∧
        ∃ rho : Representation k
          ((Spin 3 F normF) ⋊[action.comp stabilizer.subtype] stabilizer) V,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (rho.pullback (SemidirectProduct.inl : Spin 3 F normF →*
              (Spin 3 F normF) ⋊[action.comp stabilizer.subtype] stabilizer)) V.ρ) := by
  letI := ambientBrauerAction (H Frob chart.primalLevi)
    (rootH Frob chart.primalLevi iotaL)
  letI := ambientBrauerAction (N Frob chart.primalLevi)
    (rootN Frob chart.primalLevi iotaN)
  letI := originalAmbientAction Frob chart.primalLevi iotaL
  letI := originalFieldAction Frob chart.primalLevi iotaL field
  letI := cliffordBrauerAction iotaG
  letI := spinBrauerFieldAction points field.fieldPoints perfect iotaG
  have selected :=
    TypeBRankThreeJordanRepresentativeApplication.actual_representative_jordan
      parameters normF orthogonal Msys iotaG blocksG ordinaryG seriesG
      dualFrobenius dualPoints dualGeometry b r normA chart Frob iotaL blocksL
      ordinaryL familyL points field perfect source geometry iotaN iotaGamma
      blocksN catalogueH catalogueN decomposition intersection lang roots_N_H
      fieldScope covering P psi0 prescribedOrbit initialPacket theta0 occurs0
      presentation S Q J standard iotaI iotaA roots_N_G roots_A_G roots_N_A roots_I_A
      multiplicityFree above homogeneousClifford source87 source89 source820 source812
  let theta := Classical.choose selected
  have selectedTheta := Classical.choose_spec selected
  let y := Classical.choose selectedTheta
  have selectedY := Classical.choose_spec selectedTheta
  let psiH := Classical.choose selectedY
  have selectedPsiH := Classical.choose_spec selectedY
  let psi := Classical.choose selectedPsiH
  have data := Classical.choose_spec selectedPsiH
  have hpsi := data.1
  have htheta := data.2.1
  have hinP := data.2.2.1
  have hoccurs := data.2.2.2.1
  have hcovers := data.2.2.2.2.1
  have hOriginal := data.2.2.2.2.2.1
  have canonical := data.2.2.2.2.2.2.1
  have factorization := data.2.2.2.2.2.2.2.1
  have hfixers := data.2.2.2.2.2.2.2.2.1
  have packet := data.2.2.2.2.2.2.2.2.2.1
  have block := data.2.2.2.2.2.2.2.2.2.2.1
  have leviExtension := data.2.2.2.2.2.2.2.2.2.2.2
  have sameStabilizer :
      fieldStabilizer iotaG (spinFieldAction points field.fieldPoints perfect)
          (source.jordan.character psi) =
        fieldStabilizer iotaL (originalField Frob chart.primalLevi field) psi.val := by
    change MulAction.stabilizer E (source.jordan.character psi) =
      MulAction.stabilizer E psi.val
    exact hfixers
  have ambientExtension := honest_field_extension_at_equal_stabilizer
    iotaG (spinFieldAction points field.fieldPoints perfect) source812
    (source.jordan.character psi)
    (fieldStabilizer iotaL (originalField Frob chart.primalLevi field) psi.val)
    sameStabilizer
  exact ⟨theta, y, psiH, psi, hpsi, htheta, hinP, hoccurs, hcovers, hOriginal,
    canonical, factorization, hfixers, packet, block, leviExtension, ambientExtension⟩

end ModularRep.PaperProofs.TypeBRankThreeJordanAmbientExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
