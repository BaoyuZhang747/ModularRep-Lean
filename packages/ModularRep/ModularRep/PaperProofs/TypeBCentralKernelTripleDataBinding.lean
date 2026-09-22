import ModularRep.PaperProofs.TypeBCentralKernelTripleInflation
import ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily

/-!
# The literal per-pair application of MRR Lemma 3.14

The pair is the actual inflated Brauer character and an actual raw ordinary
weight whose inertia lies in that character's inertia. The quotient data
use the canonical image subgroups in the quotient of this inertia group.
Both base and local characters and their inflation equations are the
previously checked constructions on these exact carriers.

Only the quotient ambient root, literal block catalogues, and two
downstairs root guards are new data. All upstairs guards and kernel
inclusions are deductions. The one-way MRR certificate is applied to an
existing literal quotient witness; no upstairs witness or target predicate
is included in the data record and no certificate inhabitant is declared.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleDataBinding

open ModularRep CharacterWeight TypeBCentralKernelCarriers
open TypeBCentralKernelInertia TypeBCentralKernelBrauerInflation
open TypeBCentralKernelTripleCarriers TypeBCentralKernelTripleCertificate
open TypeBCentralKernelTripleProjection TypeBCentralKernelTripleInflation
open TypeBCentralKernelTripleRootFamily TypeBCentralKernelLocalReduction

universe u

variable {p : ℕ} {k K A : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
variable [Group A] [Finite A]

variable (P G : Subgroup A) [P.Normal] [G.Normal]

/-- The actual kernel inside G inherits its p-group property from P. -/
theorem baseKernelIsPGroup (hPambient : IsPGroup p P) :
    IsPGroup p (kernelInG G P) := hPambient.comap_subtype

variable (hPG : P ≤ G) (hPambient : IsPGroup p P)
variable (iotaDown : PrimeRegularRootEmbedding p k K (QuotientG G P))
variable (kernel : Navarro232Principle p k)
variable (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
variable (thetaBar : IBr iotaDown)

abbrev inertia := originalInertia P G (baseKernelIsPGroup P G hPambient)
  iotaDown kernel regular thetaBar

local notation "hP" => baseKernelIsPGroup P G hPambient
local notation "TI" => originalInertia (p := p) (k := k) (K := K) (A := A)
  P G hP iotaDown kernel regular thetaBar

variable (W : CharacterWeight p K G) (hUT : U G W ≤ TI)

/-- The actual quotient kernel inside the possibly nonnormal inertia group. -/
theorem inertiaKernelIsPGroup : IsPGroup p (Z P TI) := hPambient.comap_subtype

include hPG in
/-- The kernel is contained in the literal base by P ≤ G. -/
theorem kernel_le_base : Z P TI ≤ N G TI := Subgroup.comap_mono hPG

/-- Raw-weight inertia contains P by the checked quotient-stabilizer
preimage theorem. No inertia inclusion is sourced. -/
theorem kernel_le_local : Z P TI ≤ H G TI W :=
  Subgroup.comap_mono (kernel_le_rawInertia P G hP W)

/-- Exactly the lower root-coherence and specified catalogue data. In
particular this record contains no character correspondence, inertia
identity, projective representation or block-triple witness. -/
structure PerPairData (raw_le : U G W ≤ TI) where
  quotientAmbientRoot : PrimeRegularRootEmbedding p k K (TI ⧸ Z P TI)
  upBlocks : PhysicalBlockFamily (k := k) (N G TI) (H G TI W)
  downBlocks : PhysicalBlockFamily (k := k) (Nbar P G TI) (Hbar P G TI W)
  downBaseAgree : ∀ z : rootsOfUnity (primeRegularExponent p (Nbar P G TI)) k,
    (downBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar).lift ((z : kˣ) : k) =
      quotientAmbientRoot.lift ((z : kˣ) : k)
  downLocalAgree : ∀ z : rootsOfUnity (primeRegularExponent p (Mbar P G TI W)) k,
    (downLocalRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hPG raw_le).lift ((z : kˣ) : k) =
      quotientAmbientRoot.lift ((z : kˣ) : k)

def upAmbientRoot (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) : PrimeRegularRootEmbedding p k K TI :=
  upRoot (Z P TI) (inertiaKernelIsPGroup P G hPambient iotaDown kernel regular thetaBar)
    D.quotientAmbientRoot

/-- The original base root agrees with the constructed ambient root. Its
guard is transferred through the actual base projection and its p-kernel. -/
theorem upBaseAgree (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) (z : rootsOfUnity (primeRegularExponent p (N G TI)) k) :
    (upBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar).lift ((z : kˣ) : k) =
      (upAmbientRoot P G hPG hPambient iotaDown kernel regular thetaBar W hUT D).lift
        ((z : kˣ) : k) := by
  have agree := surjection_agrees D.quotientAmbientRoot
    (quotientSubgroupMap (Z P TI) (N G TI))
    (quotientSubgroupMap_surjective (Z P TI) (N G TI))
    (quotientSubgroupMap_kernel_isPGroup (Z P TI) (N G TI)
      (inertiaKernelIsPGroup P G hPambient iotaDown kernel regular thetaBar))
    (upBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar)
    (downBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar)
    (baseLifts (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar) D.downBaseAgree z
  exact agree.trans (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
    (Z P TI) (inertiaKernelIsPGroup P G hPambient iotaDown kernel regular thetaBar)
    D.quotientAmbientRoot _).symm

/-- The local guard uses the literal intersection projection, whose
surjectivity follows from P ≤ G, and its actual p-group kernel. -/
theorem upLocalAgree (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) (z : rootsOfUnity (primeRegularExponent p (M G TI W)) k) :
    (upLocalRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hUT).lift ((z : kˣ) : k) =
      (upAmbientRoot P G hPG hPambient iotaDown kernel regular thetaBar W hUT D).lift
        ((z : kˣ) : k) := by
  have agree := surjection_agrees D.quotientAmbientRoot
    (quotientLocalMap (Z P TI) (N G TI) (H G TI W))
    (quotientLocalMap_surjective (Z P TI) (N G TI) (H G TI W)
      (kernel_le_base P G hPG hPambient iotaDown kernel regular thetaBar))
    (quotientLocalMap_kernel_isPGroup (Z P TI) (N G TI) (H G TI W)
      (inertiaKernelIsPGroup P G hPambient iotaDown kernel regular thetaBar))
    (upLocalRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hUT)
    (downLocalRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hPG hUT)
    (localLifts (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hPG hUT) D.downLocalAgree z
  exact agree.trans (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
    (Z P TI) (inertiaKernelIsPGroup P G hPambient iotaDown kernel regular thetaBar)
    D.quotientAmbientRoot _).symm

/-- The original literal triple family, with the already fixed base/local
roots and canonical roots on every intermediate and nested intermediate. -/
def upData (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) : TripleData (p := p) (k := k) (K := K) (N G TI) (H G TI W) :=
  withPrescribedRoots (N G TI) (H G TI W)
    (upAmbientRoot P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
    (upBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar)
    (upLocalRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hUT)
    (upBaseAgree P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
    (upLocalAgree P G hPG hPambient iotaDown kernel regular thetaBar W hUT D) D.upBlocks

/-- The quotient family is on the actual image subgroups in TI/Z. -/
def downData (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) : TripleData (p := p) (k := k) (K := K) (Nbar P G TI) (Hbar P G TI W) :=
  withPrescribedRoots (Nbar P G TI) (Hbar P G TI W) D.quotientAmbientRoot
    (downBaseRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar)
    (downLocalRoot (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W hPG hUT)
    D.downBaseAgree D.downLocalAgree D.downBlocks

def upTheta (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) : IBr (upData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D).base.iota :=
  upBaseCharacter (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar

def downTheta (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) : IBr (downData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D).base.iota :=
  downBaseCharacter (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar

def upPhi (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) (navarro : Navarro318Certificate p k K) :
    IBr (upData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D).localData.iota :=
  upLocalCharacter (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W navarro hUT

def downPhi (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) (navarro : Navarro318Certificate p k K) :
    IBr (downData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D).localData.iota :=
  downLocalCharacter (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W navarro hPG hUT

/-- Literal per-pair application of the exact one-way MRR certificate.
The only witness premise is downstairs, on the canonical image carriers
and the actual constructed Brauer characters. -/
theorem perPairInflate (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient iotaDown kernel regular thetaBar W hUT) (navarro : Navarro318Certificate p k K)
    (certificate : Lemma314Certificate p k K)
    (quotientWitness : Nonempty (BlockTripleWitness
      (downData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
      (downTheta P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
      (downPhi P G hPG hPambient iotaDown kernel regular thetaBar W hUT D navarro))) :
    Nonempty (BlockTripleWitness
      (upData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
      (upTheta P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
      (upPhi P G hPG hPambient iotaDown kernel regular thetaBar W hUT D navarro)) := by
  apply certificate.inflate TI (N G TI) (H G TI W) (Z P TI)
    (kernel_le_base P G hPG hPambient iotaDown kernel regular thetaBar)
    (kernel_le_local P G hPambient iotaDown kernel regular thetaBar W)
    (upData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
    (downData P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
    (upTheta P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
    (upPhi P G hPG hPambient iotaDown kernel regular thetaBar W hUT D navarro)
    (downTheta P G hPG hPambient iotaDown kernel regular thetaBar W hUT D)
    (downPhi P G hPG hPambient iotaDown kernel regular thetaBar W hUT D navarro)
  · intro z
    exact (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift
      (Z P TI) (inertiaKernelIsPGroup P G hPambient iotaDown kernel regular thetaBar)
      D.quotientAmbientRoot _).symm
  · intro x
    exact congrArg (fun f : PrimeRegularClassFunction K (N G TI) p => f x)
      (baseInflation (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar)
  · intro x
    exact congrArg (fun f : PrimeRegularClassFunction K (M G TI W) p => f x)
      (localInflation (p := p) (k := k) (K := K) (A := A) P G hP iotaDown kernel regular thetaBar W navarro hPG hUT)
  · exact quotientWitness

end ModularRep.PaperProofs.TypeBCentralKernelTripleDataBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
