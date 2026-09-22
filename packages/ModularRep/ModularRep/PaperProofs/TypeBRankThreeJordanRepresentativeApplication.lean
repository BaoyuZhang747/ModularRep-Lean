import ModularRep.PaperProofs.TypeBRankThreeJordanSource
import ModularRep.PaperProofs.TypeBRankThreeJordanTransfer
import ModularRep.PaperProofs.TypeBRankThreeJordanPacketCopies
import ModularRep.PaperProofs.TypeBLeviRepresentativeApplication

/-!
# The selected original Levi representative and its modular Jordan image

The accepted representative theorem is invoked internally on the canonical
copy of the same original Levi. Its supported block indices are computed
from the actual original packet element. The initial character's packet
membership and invariance derive support of the whole prescribed orbit.

The returned original character and its extension are retained.
Canonical copy transport supplies its packet membership and the preceding
Levi factorization, then the same source Jordan map supplies the ambient
character. The actual ambient factorization and field-fixer equality are
deductions. All specified and published source scopes remain explicit.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeJordanRepresentativeApplication

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

/-- The actual selected representative and its same-label Jordan image.
The preceding representative and factorization are constructed internally. -/
theorem actual_representative_jordan
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
      ∃ W : FDRep k (L Frob.toMonoidHom chart.primalLevi),
        Representation.IsIrreducible W.ρ ∧
        psi.val.val = Representation.brauerCharacterOfRootEmbedding W.ρ iotaL ∧
        ∃ rho : Representation k
          (FieldSemidirect iotaL (originalField Frob chart.primalLevi field) psi.val) W,
          Representation.IsIrreducible rho ∧
          Nonempty (Representation.Equiv
            (rho.pullback (SemidirectProduct.inl : L Frob.toMonoidHom chart.primalLevi →*
              FieldSemidirect iotaL (originalField Frob chart.primalLevi field) psi.val)) W.ρ) := by
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
  let copiedBlocks := blocksL.alongMulEquiv (originalLEquiv Frob chart.primalLevi)
  let seriesBlocks : Set (LiteralPrimitiveBlock k (L Frob.toMonoidHom chart.primalLevi)) :=
    {i | (blocksL.primitiveBlockOfIndex i).val * eL = (blocksL.primitiveBlockOfIndex i).val}
  let beta := characterEquiv Frob chart.primalLevi iotaL
  let original := TypeBLeviRepresentativeOriginalExtension.originalCharacter Frob chart.primalLevi iotaL
  have transport (phi : IBr (rootH Frob chart.primalLevi iotaL)) : beta (original phi) = phi :=
    TypeBLeviRepresentativeOriginalExtension.originalCharacter_transport
      Frob chart.primalLevi iotaL phi
  have support_iff (phi : IBr (rootH Frob chart.primalLevi iotaL)) :
      blockIndex (rootH Frob chart.primalLevi iotaL) copiedBlocks phi ∈ seriesBlocks ↔
        InPacket iotaL blocksL eL (original phi) := by
    have index : blockIndex (rootH Frob chart.primalLevi iotaL) copiedBlocks phi =
        blockIndex iotaL blocksL (original phi) := by
      have h := blockIndex_alongMulEquiv iotaL blocksL
        (originalLEquiv Frob chart.primalLevi) (original phi)
      change blockIndex (rootH Frob chart.primalLevi iotaL) copiedBlocks
        (beta (original phi)) = blockIndex iotaL blocksL (original phi) at h
      exact (congrArg
        (fun x : IBr (rootH Frob chart.primalLevi iotaL) =>
          blockIndex (rootH Frob chart.primalLevi iotaL) copiedBlocks x)
        (transport phi)).symm.trans h
    change (blocksL.primitiveBlockOfIndex
        (blockIndex (rootH Frob chart.primalLevi iotaL) copiedBlocks phi)).val * eL =
      (blocksL.primitiveBlockOfIndex
        (blockIndex (rootH Frob chart.primalLevi iotaL) copiedBlocks phi)).val ↔ _
    have hprop := congrArg
      (fun i : LiteralPrimitiveBlock k (L Frob.toMonoidHom chart.primalLevi) =>
        (blocksL.primitiveBlockOfIndex i).val * eL =
          (blocksL.primitiveBlockOfIndex i).val) index
    exact ⟨fun h => Eq.mp hprop h, fun h => Eq.mpr hprop h⟩
  have orbitInSeries : ∀ phi ∈ P,
      irreducibleBrauerCharacterBlock (rootH Frob chart.primalLevi iotaL)
        (irreducibleBrauerCharacterInjectivity_of_rootEmbedding
          (rootH Frob chart.primalLevi iotaL)) copiedBlocks phi ∈ seriesBlocks := by
    intro phi hphi
    apply (support_iff phi).mpr
    rw [prescribedOrbit] at hphi
    obtain ⟨y, hy⟩ := MulAction.mem_orbit_iff.mp hphi
    have original_eq : original phi = y • original psi0 := by
      apply beta.injective
      calc
        beta (original phi) = phi := transport phi
        _ = y • psi0 := hy.symm
        _ = y • beta (original psi0) := congrArg (fun x => y • x) (transport psi0).symm
        _ = beta (y • original psi0) := (characterEquiv_ambient
          Frob chart.primalLevi iotaL y (original psi0)).symm
    rw [original_eq]
    exact inPacket_smul iotaL blocksL eL (originalConjugation Frob chart.primalLevi)
      source.gamma_invariant y (original psi0) initialPacket
  letI := fieldBrauerAction (H Frob chart.primalLevi) (rootH Frob chart.primalLevi iotaL)
    field.fieldOnGamma field.H_stable
  have selected :=
    TypeBLeviRepresentativeApplication.actual_levi_representative
      Frob chart.primalLevi source.primal_frobenius geometry field iotaL iotaN iotaGamma
      copiedBlocks blocksN catalogueH catalogueN roots_N_H fieldScope covering
      seriesBlocks P psi0 prescribedOrbit orbitInSeries theta0 occurs0 presentation
      S Q J standard iotaI iotaA roots_N_G roots_A_G roots_N_A roots_I_A
      multiplicityFree above homogeneousClifford source87 source89 source820 source812
  -- Select each witness once, without an eliminator over the full physical goal.
  let theta := Classical.choose selected
  have selectedTheta := Classical.choose_spec selected
  let y := Classical.choose selectedTheta
  have selectedY := Classical.choose_spec selectedTheta
  let psiH := Classical.choose selectedY
  have selectedPsi := Classical.choose_spec selectedY
  have hpsi := selectedPsi.1
  have htheta := selectedPsi.2.1
  have hinP := selectedPsi.2.2.1
  have hinSeries := selectedPsi.2.2.2.1
  have hoccurs := selectedPsi.2.2.2.2.1
  have hcovers := selectedPsi.2.2.2.2.2.1
  have hfull := selectedPsi.2.2.2.2.2.2.1
  have selectedOriginal := selectedPsi.2.2.2.2.2.2.2.2
  let originalPsi := Classical.choose selectedOriginal
  have originalData := Classical.choose_spec selectedOriginal
  have hOriginal := originalData.1
  have extension := originalData.2.2
  have canonical : originalPsi = original psiH :=
    beta.injective (hOriginal.trans (transport psiH).symm)
  have originalPacket : InPacket iotaL blocksL eL originalPsi := by
    rw [canonical]
    exact (support_iff psiH).mp hinSeries
  let psi : Packet iotaL blocksL eL := ⟨originalPsi, originalPacket⟩
  have levi : ModularRep.ManuscriptVerification.StabilizerFactorizationTransport.ProductStabilizerFactorization
      (D := Gamma Frob chart.primalLevi) (E := E) psi.val := by
    change ModularRep.ManuscriptVerification.StabilizerFactorizationTransport.ProductStabilizerFactorization
      (D := Gamma Frob chart.primalLevi) (E := E) originalPsi
    rw [canonical]
    exact original_product_factorization Frob chart.primalLevi iotaL field psiH hfull
  have transferred := stabilizer_transfer points chart.primalLevi field perfect iotaL iotaG
    blocksL blocksG eL eG source.gamma_invariant source.field_invariant source.jordan
    chart.primalLevi_le_spin decomposition intersection lang psi levi
  exact ⟨theta, y, psiH, psi, hpsi, htheta, hinP, hoccurs, hcovers, hOriginal,
    canonical, transferred.1, transferred.2.1, transferred.2.2,
    source.jordan.supporting_block psi, extension⟩

end ModularRep.PaperProofs.TypeBRankThreeJordanRepresentativeApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
