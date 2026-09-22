import ModularRep.PaperProofs.TypeBCentralKernelButterflyCertificate
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily
import ModularRep.PaperProofs.TypeBCentralKernelPairSplittingBinding
import ModularRep.PaperProofs.CanonicalLocalBaseTransport

/-!
# Prescribed Butterfly target roots in the fixed honest ambient

The ambient is the already chosen `SpathAmbientGroup`. Its local group is
the full normalizer of the actual embedded quotient radical. The base root
is transported from the prescribed quotient character, and the local root
from its prescribed normalizer inflation through the canonical local-base
equivalence. One modular system supplies their ambient-root guards and all
intermediate roots; the literal specified block family remains explicit.

The two ambient root conventions are compared only on their common finite
root domain. No equality of whole lift functions across unrelated ambient
orders, ordinary splitting input, source certificate or triple witness is
introduced here.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBButterflyHonestTargetRoots

open ModularRep TypeBLocalReductionInstantiation
open TypeBModularGroupRootBinding TypeBModularCommonRootBinding
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleRootFamily
open TypeBCentralKernelButterflyCertificate
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Family
open EvenFieldFLZBAWGoodFamily

section CommonDomain

variable {p : ℕ} {K O k X Y : Type}
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [Group X] [Finite X] [Group Y] [Finite Y]
  (Msys : ModularSystem p K O k)

/-- The same residue convention agrees at every unit in both actual root
domains. The comparison takes place inside their common product order. -/
theorem calibrated_roots_common_domain
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (calibrationX : RootResidueCompatible Msys iotaX)
    (calibrationY : RootResidueCompatible Msys iotaY)
    (z : kˣ)
    (hzX : z ^ primeRegularExponent p X = 1)
    (hzY : z ^ primeRegularExponent p Y = 1) :
    iotaX.lift (z : k) = iotaY.lift (z : k) := by
  rw [eq_groupRoot_of_residue Msys X iotaX calibrationX,
    eq_groupRoot_of_residue Msys Y iotaY calibrationY]
  let zX : rootsOfUnity (primeRegularExponent p X) k := ⟨z, hzX⟩
  let zY : rootsOfUnity (primeRegularExponent p Y) k := ⟨z, hzY⟩
  let m := primeRegularExponent p X * primeRegularExponent p Y
  have hm : 0 < m :=
    Nat.mul_pos (primeRegularExponent_pos p X) (primeRegularExponent_pos p Y)
  have hc : m.Coprime p :=
    (exponent_coprime Msys X).mul_left (exponent_coprime Msys Y)
  have hX : primeRegularExponent p X ∣ m := Nat.dvd_mul_right _ _
  have hY : primeRegularExponent p Y ∣ m := Nat.dvd_mul_left _ _
  have first := rootEquiv_coherent_value Msys
    (primeRegularExponent_pos p X) hm (exponent_coprime Msys X) hc hX zX
  have second := rootEquiv_coherent_value Msys
    (primeRegularExponent_pos p Y) hm (exponent_coprime Msys Y) hc hY zY
  have same :
      (Subgroup.inclusion (rootsOfUnity_le_of_dvd hX) zX : rootsOfUnity m k) =
        Subgroup.inclusion (rootsOfUnity_le_of_dvd hY) zY := by
    apply Subtype.ext
    rfl
  change (groupRoot Msys X).lift ((zX : kˣ) : k) =
    (groupRoot Msys Y).lift ((zY : kˣ) : k)
  rw [(groupRoot Msys X).lift_coe zX, (groupRoot Msys Y).lift_coe zY]
  change (((rootEquiv Msys (primeRegularExponent_pos p X)
      (exponent_coprime Msys X) zX) : Kˣ) : K) =
    (((rootEquiv Msys (primeRegularExponent_pos p Y)
      (exponent_coprime Msys Y) zY) : Kˣ) : K)
  exact first.trans ((congrArg
    (fun t : rootsOfUnity m k => ((rootEquiv Msys hm hc t : Kˣ) : K))
    same).trans second.symm)

end CommonDomain

section HonestTarget

variable (P : Definition35Problem.{0})
  (reference psi : Definition35Brauer P) (w : Definition35Weight P)
  (quotient : CentralQuotientBrauerSource P reference psi)
  (weight : QuotientWeightBrauerSource P reference w)
  (localInflation : QuotientLocalInflationSource P reference w weight)
  (ambient : SpathAmbientGroup P reference psi quotient)
  {O : Type} [CommRing O] [IsDomain O] [Algebra O P.K]
  (Msys : ModularSystem P.p P.K O P.k)
  (quotientCalibration : RootResidueCompatible Msys quotient.iota)
  (localCalibration : RootResidueCompatible Msys localInflation.iota)

include quotientCalibration in
/-- The prescribed quotient root has exactly the ambient convention on
the literal normal base's finite root domain. -/
theorem baseRoot_agrees
    (z : rootsOfUnity (primeRegularExponent P.p ambient.base) P.k) :
    (quotient.iota.alongMulEquiv ambient.baseEquiv).lift ((z : P.kˣ) : P.k) =
      (groupRoot Msys ambient.A).lift ((z : P.kˣ) : P.k) := by
  rw [eq_groupRoot_of_residue Msys ambient.base
    (quotient.iota.alongMulEquiv ambient.baseEquiv)
    (TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
      Msys quotient.iota quotientCalibration ambient.baseEquiv)]
  exact groupRoot_agrees_of_dvd Msys ambient.A ambient.base
    (Nat.ordCompl_dvd_ordCompl_of_dvd
      (Subgroup.card_subgroup_dvd_card ambient.base) P.p) z

include localCalibration in
/-- The actual normalizer inflation is transported through the canonical
local-base map. Nested subgroup divisibility gives its ambient-root guard. -/
theorem localRoot_agrees
    (z : rootsOfUnity
      (primeRegularExponent P.p (AmbientLocalBase P reference psi w quotient ambient))
      P.k) :
    (localInflation.iota.alongMulEquiv
        (canonicalLocalBaseEquiv (w := w) ambient)).lift ((z : P.kˣ) : P.k) =
      (groupRoot Msys ambient.A).lift ((z : P.kˣ) : P.k) := by
  rw [eq_groupRoot_of_residue Msys
    (AmbientLocalBase P reference psi w quotient ambient)
    (localInflation.iota.alongMulEquiv (canonicalLocalBaseEquiv (w := w) ambient))
    (TypeBCentralKernelPairSplittingBinding.alongMulEquiv_residue
      Msys localInflation.iota localCalibration (canonicalLocalBaseEquiv (w := w) ambient))]
  have hcard :
      Nat.card (AmbientLocalBase P reference psi w quotient ambient) ∣
        Nat.card ambient.A :=
    (Subgroup.card_subgroup_dvd_card
      (AmbientLocalBase P reference psi w quotient ambient)).trans
      (Subgroup.card_subgroup_dvd_card
        (AmbientLocalGroup P reference psi w quotient ambient))
  exact groupRoot_agrees_of_dvd Msys ambient.A
    (AmbientLocalBase P reference psi w quotient ambient)
    (Nat.ordCompl_dvd_ordCompl_of_dvd hcard P.p) z

variable (blocks : PhysicalBlockFamily (k := P.k) ambient.base
  (AmbientLocalGroup P reference psi w quotient ambient))

/-- Literal target data on the fixed ambient and its full radical normalizer.
Only the specified family is supplied; every root guard is constructed. -/
def targetData : TripleData (p := P.p) (k := P.k) (K := P.K)
    ambient.base (AmbientLocalGroup P reference psi w quotient ambient) :=
  withPrescribedRoots ambient.base (AmbientLocalGroup P reference psi w quotient ambient)
    (groupRoot Msys ambient.A)
    (quotient.iota.alongMulEquiv ambient.baseEquiv)
    (localInflation.iota.alongMulEquiv (canonicalLocalBaseEquiv (w := w) ambient))
    (baseRoot_agrees P reference psi quotient ambient Msys quotientCalibration)
    (localRoot_agrees P reference psi w quotient weight localInflation ambient Msys
      localCalibration)
    blocks

/-- The target base character is the prescribed quotient character under
the same ambient base equivalence. -/
def baseTheta : IBr
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).base.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv
    quotient.iota ambient.baseEquiv quotient.brauer

/-- The target local character is the actual selected normalizer inflation
under the canonical local-base equivalence. -/
def localPhi : IBr
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).localData.iota :=
  IrreducibleBrauerCharacter.equivAlongMulEquiv localInflation.iota
    (canonicalLocalBaseEquiv (w := w) ambient) localInflation.brauer

@[simp] theorem baseTheta_val :
    (baseTheta P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).val =
        PrimeRegularClassFunction.pullback ambient.baseEquiv.symm.toMonoidHom
          quotient.brauer.val := rfl

@[simp] theorem localPhi_val :
    (localPhi P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).val =
        PrimeRegularClassFunction.pullback
          (canonicalLocalBaseEquiv (w := w) ambient).symm.toMonoidHom
          localInflation.brauer.val := rfl

@[simp] theorem targetData_ambientRoot :
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).ambientRoot =
        groupRoot Msys ambient.A := rfl

@[simp] theorem targetData_base_iota :
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).base.iota =
        quotient.iota.alongMulEquiv ambient.baseEquiv := rfl

@[simp] theorem targetData_local_iota :
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).localData.iota =
        localInflation.iota.alongMulEquiv
          (canonicalLocalBaseEquiv (w := w) ambient) := rfl

@[simp] theorem targetData_intermediate_iota
    (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J) :
    ((targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).intermediate J hNJ).iota =
        TypeBCentralKernelLocalBlockBinding.subgroupRoot (groupRoot Msys ambient.A) J := rfl

@[simp] theorem targetData_localIntermediate_iota
    (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J) :
    ((targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).localIntermediateData J hNJ).iota =
        nestedRoot (groupRoot Msys ambient.A) J
          (localIntermediate (AmbientLocalGroup P reference psi w quotient ambient) J) := rfl

/-- The same specified catalogue is retained at each literal carrier. -/
theorem targetData_blocks :
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).base.blocks = blocks.base ∧
    (targetData P reference psi w quotient weight localInflation ambient Msys
      quotientCalibration localCalibration blocks).localData.blocks = blocks.localData ∧
    (∀ (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J),
      ((targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).intermediate J hNJ).blocks =
          blocks.intermediate J hNJ) ∧
    (∀ (J : Subgroup ambient.A) (hNJ : ambient.base ≤ J),
      ((targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).localIntermediateData J hNJ).blocks =
          blocks.localIntermediateData J hNJ) :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The constructed ambient root remains calibrated to this same system. -/
theorem targetData_ambient_residue :
    RootResidueCompatible Msys
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks).ambientRoot :=
  groupRoot_residue Msys ambient.A

/-- A calibrated source ambient gives the exact Butterfly common-domain
guard against the prescribed target, regardless of their different orders. -/
theorem ambientRootsCompatible
    {T1 : Type} [Group T1] [Finite T1] {N1 U1 : Subgroup T1}
    (D1 : TripleData (p := P.p) (k := P.k) (K := P.K) N1 U1)
    (sourceCalibration : RootResidueCompatible Msys D1.ambientRoot) :
    AmbientRootsCompatible D1
      (targetData P reference psi w quotient weight localInflation ambient Msys
        quotientCalibration localCalibration blocks) := by
  intro z hz1 hz2
  exact calibrated_roots_common_domain Msys D1.ambientRoot
    (groupRoot Msys ambient.A) sourceCalibration
    (groupRoot_residue Msys ambient.A) z hz1 hz2

end HonestTarget

end ModularRep.PaperProofs.TypeBButterflyHonestTargetRoots


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
