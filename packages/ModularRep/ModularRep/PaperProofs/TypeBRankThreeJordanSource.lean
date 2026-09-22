import ModularRep.PaperProofs.TypeBRankThreeJordanMap
import ModularRep.PaperProofs.TypeBRankThreeJordanAmbientPacket
import ModularRep.PaperProofs.TypeBRankThreeJordanLeviPacket
import ModularRep.PaperProofs.TypeBRankThreeJordanDualLabel
import ModularRep.PaperProofs.TypeBRankThreeFactorsPointSource
import ModularRep.PaperProofs.TypeBCharacteristicTwoGallagherSource

/-!
# Fixed-label source binding for the rank-three modular Jordan deduction

Both modular idempotents are constructed from the SAME specified ordinary
block selectors and full rational Lusztig unions. The dual Levi and its
rational semisimple label are the preceding nonprincipal reduction's
actual Levi and actual label; their membership, order and Frobenius
equations are derived in DualLabel. The primal group is the paired
chart's literal original Levi inside the same Clifford point model.

FLZ Jordan 2022 Theorem 4.2 and the proof of Proposition 5.2 provide the
one-way character/block correspondence at the retained
C°(s) C(s)^F containment. The companion's ordinary block-closure source
and chosen-field/idempotent normalization are separate exact inputs.
A certificate inhabitant must mean the SAME reduced cohomology map,
not an arbitrary map satisfying a subsequently desired stabilizer.
Its algebraic model, paired Frobenius, source coefficient realization
and actual chosen F0 authentication remain explicit E1/E2/U obligations.
No claim is made that merely inhabiting a Lean record proves those
external source interpretations.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBRankThreeJordanSource

open ModularRep OrdinaryIrreducibleCharacter FDRepSimpleClassKZero
open TypeBCliffordCarriers TypeBConformalDualCarriers
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBRankThreeNonprincipalApplication TypeBRankThreeNonprincipalGeometry
open TypeBRegularLeviRationalCarriers TypeBRankThreeFactorsPointSource
open TypeBRankThreeJordanDualLabel TypeBLeviRepresentativeCarriers
open TypeBLeviRepresentativeSelection TypeBRankThreeJordanOriginalTransport
open TypeBRankThreeJordanMap TypeBCharacteristicTwoGallagherSource
open TypeBRationalSeriesSource

/-- The same six source fields, with the map indexed by the retained invariance proofs. -/
structure CertificateCore
    (primalCondition rootsCondition closureCondition gammaCondition fieldCondition : Prop)
    (Jordan : gammaCondition → fieldCondition → Type) where
  primal_frobenius : primalCondition
  roots_agree : rootsCondition
  levi_union_closed : closureCondition
  gamma_invariant : gammaCondition
  field_invariant : fieldCondition
  jordan : Jordan gamma_invariant field_invariant

variable {p f : ℕ} {F A E K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F p f) (N : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) N)
  [Finite (Spin 3 F N)] [Finite (SpecialClifford 3 F)]
  (Msys : ModularSystem 2 K O k)
  (iotaG : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocksG : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin 3 F N) => c.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinaryG : OrdinaryBlockSource Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG)
  (seriesG : Sources parameters Msys iotaG
    (irreducibleBrauerCharacterInjectivity_of_rootEmbedding iotaG) blocksG ordinaryG)
  (dualFrobenius : FrobeniusSource p f A)
  (dualPoints : RationalPointSource F A p f dualFrobenius)
  (dualGeometry : GeometrySource F A p f dualFrobenius dualPoints)
  (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
  (r : ManuscriptReduction parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b)

/-- The ambient admissible parameter keeps exactly the retained label. -/
def ambientParameter :
    TypeBSpinBroueMichelCarriers.AdmissibleParameter
      (p := p) (ell := 2) (n := 3) (F := F) :=
  ⟨r.label, r.defining_regular, Nat.coprime_two_left.mpr r.odd_order⟩

/-- The actual ambient idempotent, constructed from its full ordinary family. -/
def ambientIdempotent : k[Spin 3 F N] :=
  TypeBRankThreeJordanAmbientPacket.idempotent parameters Msys iotaG blocksG
    ordinaryG seriesG (ambientParameter parameters N orthogonal Msys iotaG blocksG
      ordinaryG seriesG dualFrobenius dualPoints dualGeometry b r)

variable (Nbar : NormSource 3 A) (chart : PairedChart Nbar r.levi)
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

/-- The Levi union uses the same rational label inside the retained dual Levi. -/
def leviIdempotent : k[L Frob.toMonoidHom chart.primalLevi] :=
  TypeBRankThreeJordanLeviPacket.idempotent Msys iotaL blocksL ordinaryL familyL
    parameters.prime (two_ne_defining parameters) (rationalLabel r)
    (rationalLabel_defining_regular r)

variable [Group E]
  (points : CliffordFixedPointSource 3 p f F A N Nbar Frob)
  (field : FieldData Frob chart.primalLevi E)
  (perfect : commutator (Spin 3 F N) = ⊤)

/-- Exact fixed-label inputs for the source-instantiated consumer.

The first fields authenticate the ordinary union, necessary root
agreement and invariance under the ACTUAL chosen actors. The final
one-way map uses those same computed packet idempotents throughout.
No representative, stabilizer, extension or numbered target is supplied. -/
abbrev Certificate :=
  let eL := leviIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r Nbar chart Frob
    iotaL blocksL ordinaryL familyL
  let eG := ambientIdempotent parameters N orthogonal Msys iotaG blocksG ordinaryG
    seriesG dualFrobenius dualPoints dualGeometry b r
  CertificateCore
    (chart.primalLevi.map Frob.toMonoidHom = chart.primalLevi)
    (RootsAgree iotaG iotaL)
    (TypeBRankThreeJordanLeviPacket.BlockClosureCertificate
      Msys iotaL blocksL ordinaryL familyL parameters.prime
      (two_ne_defining parameters) (rationalLabel r) (rationalLabel_defining_regular r))
    (∀ m : Gamma Frob chart.primalLevi,
      MonoidAlgebra.mapDomainRingEquiv k
        (originalConjugation Frob chart.primalLevi m) eL = eL)
    (∀ a : E,
      MonoidAlgebra.mapDomainRingEquiv k
        (originalField Frob chart.primalLevi field a) eL = eL)
    (fun gamma_invariant field_invariant =>
      ModularJordanMap points chart.primalLevi field perfect iotaL iotaG
        blocksL blocksG eL eG gamma_invariant field_invariant)

end ModularRep.PaperProofs.TypeBRankThreeJordanSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
