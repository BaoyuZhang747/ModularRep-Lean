import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily
import ModularRep.PaperProofs.TypeBLocalReductionInstantiation
import ModularRep.BrauerCharacterHomPullback
import ModularRep.SpathNavarroSourceAdapter

/-!
# The forward honest-extension implication of Spath Proposition 3.6(b)

The primary source is Spath (2017), Proposition 3.6(b), p. 670,
local extraction lines 305--340. The given global extension is fixed
before ONE local extension is selected for EVERY intermediate subgroup.
Equal constituent support on the literal centralizer is retained separately
from the literal restrictions and specified block-induction equations.

`HonestLocalExtensionCertificate` declares one narrow E2 source field and
no inhabitant. Its input is the existing full modular block-triple witness,
not an application-specific matching or final condition. The same-system
ambient calibration and `SpathCoefficientField` delimit the E1 interpretation
of the paper's coefficient convention (Notation 2.1, lines 137--164).
The given TripleData retains all finite-domain root guards and actual
primitive block catalogues. No ordinary algebraic closure, independently
supplied ambient splitting, or unrestricted cross-group lift equality is used.

The elementary helpers below retain the literal inclusions and root guards.
The last two declarations only select the local extension supplied by the
certificate and retain all its clauses for that same selected character.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBSpathHonestLocalExtensionSource

open ModularRep
open TypeBCentralKernelTripleCertificate TypeBCentralKernelLocalBlockBinding
open TypeBLocalReductionInstantiation
open Representation.Extension

variable {p : ℕ} {k K : Type}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

local instance finiteGroupFintype (H : Type) [Group H] [Finite H] :
    Fintype H := Fintype.ofFinite H

variable {T : Type} [Group T] [Finite T] {N U : Subgroup T}
  (D : TripleData (p := p) (k := k) (K := K) N U)

/-- The local ambient uses the restriction of the specified ambient root. -/
def localAmbientRoot : PrimeRegularRootEmbedding p k K U :=
  subgroupRoot D.ambientRoot U

/-- Both constituent supports are measured at this one centralizer root. -/
def centralizerRoot : PrimeRegularRootEmbedding p k K
    (Subgroup.centralizer (N : Set T)) :=
  subgroupRoot D.ambientRoot (Subgroup.centralizer (N : Set T))

theorem localAmbientRoot_agrees
    (z : rootsOfUnity (primeRegularExponent p U) k) :
    (localAmbientRoot D).lift ((z : kˣ) : k) =
      D.ambientRoot.lift ((z : kˣ) : k) :=
  subgroupRoot_agrees D.ambientRoot U z

theorem centralizerRoot_agrees
    (z : rootsOfUnity
      (primeRegularExponent p (Subgroup.centralizer (N : Set T))) k) :
    (centralizerRoot D).lift ((z : kˣ) : k) =
      D.ambientRoot.lift ((z : kˣ) : k) :=
  subgroupRoot_agrees D.ambientRoot (Subgroup.centralizer (N : Set T)) z

/-- The local base root also agrees with the prescribed local ambient root. -/
theorem localBaseRoot_agrees
    (z : rootsOfUnity (primeRegularExponent p (localBase N U)) k) :
    D.localData.iota.lift ((z : kˣ) : k) =
      (localAmbientRoot D).lift ((z : kˣ) : k) := by
  let included := PrimeRegularRootEmbedding.rootsOfUnityInclusion
    (Nat.ordCompl_dvd_ordCompl_of_dvd
      (Subgroup.card_subgroup_dvd_card (localBase N U)) p) z
  exact (D.localRoots z).trans (localAmbientRoot_agrees D included).symm

variable [N.Normal] {theta : IBr D.base.iota} {phi : IBr D.localData.iota}
  (witness : BlockTripleWitness D theta phi)

/-- The witness gives exactly this inclusion of the actual centralizer. -/
def centralizerToLocal : Subgroup.centralizer (N : Set T) →* U :=
  Subgroup.inclusion witness.centralizer_le

@[simp] theorem centralizerToLocal_coe
    (x : Subgroup.centralizer (N : Set T)) :
    ((centralizerToLocal D witness x : U) : T) = (x : T) := rfl

@[simp] theorem centralizerToLocal_subtype :
    U.subtype.comp (centralizerToLocal D witness) =
      (Subgroup.centralizer (N : Set T)).subtype := rfl

/-- Exact forward Proposition 3.6(b), with the modular field and finite-root
interpretation retained explicitly. This structure has no supplied inhabitant.
Neither an intermediate subgroup nor the local extension may be chosen before
the given global extension; the same local extension serves every subgroup. -/
structure HonestLocalExtensionCertificate
    (p : ℕ) (k K : Type)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] : Prop where
  exists_local : ∀ (T : Type) [Group T] [Finite T]
      (N U : Subgroup T) [N.Normal]
      (D : TripleData (p := p) (k := k) (K := K) N U)
      (theta : IBr D.base.iota) (phi : IBr D.localData.iota)
      (witness : BlockTripleWitness D theta phi)
      (fieldScope : SpathCoefficientField p k D.ambientRoot.prime)
      (O : Type) [CommRing O] [IsDomain O] [Algebra O K]
      (Msys : ModularSystem p K O k)
      (calibration : RootResidueCompatible Msys D.ambientRoot)
      (chi : BrauerCharacterExtensionWitness D.ambientRoot D.base.iota theta),
    ∃ eta : BrauerCharacterExtensionWitness
        (localAmbientRoot D) D.localData.iota phi,
      (∀ nu : IBr (centralizerRoot D),
        OccursAlong (Subgroup.centralizer (N : Set T)).subtype
            D.ambientRoot (centralizerRoot D) chi.val nu ↔
          OccursAlong (centralizerToLocal D witness)
            (localAmbientRoot D) (centralizerRoot D) eta.val nu) ∧
      ∀ (J : Subgroup T) (hNJ : N ≤ J),
        ∃ chiJ : IBr (D.intermediate J hNJ).iota,
        ∃ etaJ : IBr (D.localIntermediateData J hNJ).iota,
          PrimeRegularClassFunction.pullback J.subtype chi.val.val = chiJ.val ∧
          PrimeRegularClassFunction.pullback (localToU U J) eta.val.val = etaJ.val ∧
          IntermediateBlockInduces D J hNJ chiJ etaJ

variable (certificate : HonestLocalExtensionCertificate p k K)
  (fieldScope : SpathCoefficientField p k D.ambientRoot.prime)
  {O : Type} [CommRing O] [IsDomain O] [Algebra O K]
  (Msys : ModularSystem p K O k)
  (calibration : RootResidueCompatible Msys D.ambientRoot)
  (chi : BrauerCharacterExtensionWitness D.ambientRoot D.base.iota theta)

/-- Choose once after the specified global character, retaining the original
literal local base and its root. No source inhabitant is constructed here. -/
def localExtension : BrauerCharacterExtensionWitness
    (localAmbientRoot D) D.localData.iota phi :=
  Classical.choose (certificate.exists_local T N U D theta phi witness
    fieldScope O Msys calibration chi)

/-- Both source conclusions hold for that same chosen local character,
including all intermediate restrictions and the separate central support. -/
theorem localExtension_spec :
    (∀ nu : IBr (centralizerRoot D),
      OccursAlong (Subgroup.centralizer (N : Set T)).subtype
          D.ambientRoot (centralizerRoot D) chi.val nu ↔
        OccursAlong (centralizerToLocal D witness)
          (localAmbientRoot D) (centralizerRoot D)
          (localExtension D witness certificate fieldScope Msys calibration chi).val nu) ∧
    ∀ (J : Subgroup T) (hNJ : N ≤ J),
      ∃ chiJ : IBr (D.intermediate J hNJ).iota,
      ∃ etaJ : IBr (D.localIntermediateData J hNJ).iota,
        PrimeRegularClassFunction.pullback J.subtype chi.val.val = chiJ.val ∧
        PrimeRegularClassFunction.pullback (localToU U J)
            (localExtension D witness certificate fieldScope Msys calibration chi).val.val =
          etaJ.val ∧
        IntermediateBlockInduces D J hNJ chiJ etaJ :=
  Classical.choose_spec (certificate.exists_local T N U D theta phi witness
    fieldScope O Msys calibration chi)

end ModularRep.PaperProofs.TypeBSpathHonestLocalExtensionSource


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
