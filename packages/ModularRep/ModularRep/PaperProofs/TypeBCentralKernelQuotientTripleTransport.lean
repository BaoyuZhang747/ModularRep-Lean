import ModularRep.PaperProofs.TypeBCentralKernelQuotientTripleCharacters
import ModularRep.PaperProofs.TypeBCentralKernelButterflyWitnessTransport
import ModularRep.PaperProofs.TypeBCentralKernelTripleDataBinding

/-!
# From the native quotient-inertia triple to its literal quotient images

The old ambient group is the actual quotient Brauer inertia. The target
ambient is the quotient of the actual upstairs Brauer inertia. Every map
is the previously anchored quotient-inertia equivalence or its restriction.
The source roots and characters retain the actual quotient character and
descended ordinary weight. The independently prescribed target data are
exactly those consumed by the checked per-pair MRR inflation application.

Only an existing native quotient block-triple witness is a witness input.
Its centralizer inclusion proves the Butterfly local subgroup equality;
the local equivalence is identified by its literal inclusion into the base.
All root and character guards are constructed, and specified block matching
is derived by the checked Butterfly character-identification theorem.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelQuotientTripleTransport

open ModularRep TypeBCentralKernelTripleCertificate
open TypeBCentralKernelButterflyCertificate TypeBCentralKernelTripleRootFamily

universe u

section PrescribedLocalImage

variable {p : ℕ} {k K T1 T2 : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group T1] [Group T2] [Finite T1] [Finite T2]
  (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
  (H1 : Subgroup T1) (H2 : Subgroup T2)
  (eT : T1 ≃* T2) (eN : N1 ≃* N2)

/-- Equality elimination for an independently prescribed target local
subgroup. The actual local equivalence is forced by its base anchor, so
the Butterfly construction introduces no additional local-carrier choice. -/
theorem transfer_with_local_image
    (anchor : ∀ n : N1, eT (n : T1) = (eN n : T2))
    (localImage : H1.map eT.toMonoidHom = H2)
    (eL : localBase N1 H1 ≃* localBase N2 H2)
    (localAnchor : ∀ x : localBase N1 H1,
      localToBase N2 H2 (eL x) = eN (localToBase N1 H1 x))
    (D1 : TripleData (p := p) (k := k) (K := K) N1 H1)
    (D2 : TripleData (p := p) (k := k) (K := K) N2 H2)
    (theta1 : IBr D1.base.iota) (phi1 : IBr D1.localData.iota)
    (witness : BlockTripleWitness D1 theta1 phi1)
    (theta2 : IBr D2.base.iota) (phi2 : IBr D2.localData.iota)
    (ambientRoots : AmbientRootsCompatible D1 D2)
    (baseLifts : D2.base.iota.lift = D1.base.iota.lift)
    (localLifts : D2.localData.iota.lift = D1.localData.iota.lift)
    (baseValues : theta2.val =
      PrimeRegularClassFunction.pullback eN.symm.toMonoidHom theta1.val)
    (localValues : phi2.val =
      PrimeRegularClassFunction.pullback eL.symm.toMonoidHom phi1.val)
    (certificate : ButterflyCertificate p k K) :
    Nonempty (BlockTripleWitness D2 theta2 phi2) := by
  have subgroup_eq : H2 =
      TypeBCentralKernelButterflyWitnessTransport.targetLocalAmbient N1 N2 H1 eN :=
    localImage.symm.trans
      (TypeBCentralKernelButterflyAmbientIsomorphism.secondLocalAmbient_eq_map
        N1 N2 eT eN anchor H1 witness.centralizer_le).symm
  clear localImage
  subst H2
  have equiv_eq : eL =
      (TypeBCentralKernelButterflyWitnessTransport.localId
        N1 N2 H1 eN witness.centralizer_le).equiv := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun n : N2 => (n : T2)) ((localAnchor x).trans
      ((TypeBCentralKernelButterflyWitnessTransport.localId
        N1 N2 H1 eN witness.centralizer_le).base_value x).symm)
  apply TypeBCentralKernelButterflyWitnessTransport.transfer_to_prescribed
    N1 N2 H1 eT eN D1 anchor D2 theta1 phi1 witness theta2 phi2
    ambientRoots baseLifts localLifts baseValues
  · rw [← equiv_eq]
    exact localValues
  · exact certificate

end PrescribedLocalImage

section ActualQuotient

open TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelBrauerInflation TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleProjection TypeBCentralKernelTripleInflation
open TypeBCentralKernelTripleDataBinding TypeBCentralKernelLocalReduction

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] [IsAlgClosed K]
  [Group A] [Finite A]
  (P G : Subgroup A) [P.Normal] [G.Normal]
  (hPG : P ≤ G) (hPambient : IsPGroup p P)
  (root : PrimeRegularRootEmbedding p k K (QuotientG G P))
  (kernel : Navarro232Principle p k)
  (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
  (thetaBar : IBr root)

local notation "hP" => baseKernelIsPGroup P G hPambient
local notation "TI" => originalInertia (p := p) (k := k) (K := K) (A := A)
  P G hP root kernel regular thetaBar
local notation "QI" => TypeBCentralKernelQuotientInertiaImages.quotientInertia P G root thetaBar
local notation "NQ" => inside (embeddedQuotientG G P) QI
local notation "eT" => TypeBCentralKernelQuotientInertiaImages.inertiaQuotientEquiv
  P G hP root kernel regular thetaBar
local notation "eN" => TypeBCentralKernelQuotientInertiaImages.baseImageEquiv
  P G hP root kernel regular thetaBar hPG

/-- The inverse quotient-inertia equivalence is anchored to the inverse
of the actual restricted base equivalence. -/
theorem inverse_base_anchor (n : NQ) :
    (eT).symm n.val = ((eN).symm n).val := by
  obtain ⟨x, rfl⟩ := (eN).surjective n
  exact (congrArg (eT).symm
    (TypeBCentralKernelQuotientInertiaImages.baseImageEquiv_val
      P G hP root kernel regular thetaBar hPG x)).trans
    (((eT).symm_apply_apply x.val).trans
      (congrArg Subtype.val ((eN).symm_apply_apply x)).symm)

variable (W : CharacterWeight p K G)

local notation "HQ" => inside
  (TypeBCentralKernelQuotientInertiaImages.quotientRawInertia P G hP W) QI
local notation "eL" => TypeBCentralKernelQuotientInertiaImages.localImageEquiv
  P G hP root kernel regular thetaBar hPG W

/-- The source local subgroup is the actual quotient raw-weight inertia
inside QI, and its inverse image is precisely the prescribed Hbar. -/
theorem inverse_local_image :
    (HQ).map (eT).symm.toMonoidHom = Hbar P G TI W :=
  (Subgroup.map_symm_eq_iff_map_eq (Hbar P G TI W)
    (H := (HQ)) (e := (eT))).mpr
    (TypeBCentralKernelQuotientInertiaImages.local_image
      P G hP root kernel regular thetaBar W)

/-- The inverse local-intersection map has the same base anchor as the
constructed Butterfly local identification. -/
theorem inverse_local_anchor (x : localBase NQ HQ) :
    localToBase (Nbar P G TI) (Hbar P G TI W) ((eL).symm x) =
      (eN).symm (localToBase NQ HQ x) := by
  apply (eN).injective
  have triangle : localToBase NQ HQ ((eL) ((eL).symm x)) =
      (eN) (localToBase (Nbar P G TI) (Hbar P G TI W) ((eL).symm x)) :=
    TypeBCentralKernelQuotientInertiaImages.local_base_triangle
      P G hP root kernel regular thetaBar hPG W ((eL).symm x)
  exact triangle.symm.trans
    ((congrArg (localToBase NQ HQ) ((eL).apply_symm_apply x)).trans
      ((eN).apply_symm_apply (localToBase NQ HQ x)).symm)

/-- The native ambient root shares the complete prescribed field lift of
the canonical target ambient root. -/
def nativeAmbientRoot (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT) :
    PrimeRegularRootEmbedding p k K QI :=
  D.quotientAmbientRoot.alongMulEquiv (eT)

theorem nativeBaseAgree (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (z : rootsOfUnity (primeRegularExponent p NQ) k) :
    (TypeBCentralKernelQuotientTripleCharacters.nativeBaseRoot
      P G hP root kernel regular thetaBar).lift ((z : kˣ) : k) =
      (nativeAmbientRoot P G hPG hPambient root kernel regular thetaBar W hUT D).lift
        ((z : kˣ) : k) := by
  calc
    _ = (downBaseRoot (p := p) (k := k) (K := K) (A := A)
        P G hP root kernel regular thetaBar).lift ((z : kˣ) : k) :=
      (congrFun (TypeBCentralKernelQuotientTripleCharacters.baseLifts
        P G hP root kernel regular thetaBar) _).symm
    _ = ((downBaseRoot (p := p) (k := k) (K := K) (A := A)
        P G hP root kernel regular thetaBar).alongMulEquiv (eN)).lift ((z : kˣ) : k) :=
      ((downBaseRoot (p := p) (k := k) (K := K) (A := A)
        P G hP root kernel regular thetaBar).alongMulEquiv_lift (eN) _).symm
    _ = D.quotientAmbientRoot.lift ((z : kˣ) : k) :=
      alongMulEquiv_agrees D.quotientAmbientRoot
        (downBaseRoot (p := p) (k := k) (K := K) (A := A)
          P G hP root kernel regular thetaBar) (eN) D.downBaseAgree z
    _ = _ := (D.quotientAmbientRoot.alongMulEquiv_lift (eT) _).symm

theorem nativeLocalAgree (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (z : rootsOfUnity (primeRegularExponent p (localBase NQ HQ)) k) :
    (TypeBCentralKernelQuotientTripleCharacters.nativeLocalRoot
      P G hP root kernel regular thetaBar W hPG hUT).lift ((z : kˣ) : k) =
      (nativeAmbientRoot P G hPG hPambient root kernel regular thetaBar W hUT D).lift
        ((z : kˣ) : k) := by
  calc
    _ = (downLocalRoot (p := p) (k := k) (K := K) (A := A)
        P G hP root kernel regular thetaBar W hPG hUT).lift ((z : kˣ) : k) :=
      (congrFun (TypeBCentralKernelQuotientTripleCharacters.localLifts
        P G hP root kernel regular thetaBar W hPG hUT) _).symm
    _ = ((downLocalRoot (p := p) (k := k) (K := K) (A := A)
        P G hP root kernel regular thetaBar W hPG hUT).alongMulEquiv (eL)).lift ((z : kˣ) : k) :=
      ((downLocalRoot (p := p) (k := k) (K := K) (A := A)
        P G hP root kernel regular thetaBar W hPG hUT).alongMulEquiv_lift (eL) _).symm
    _ = D.quotientAmbientRoot.lift ((z : kˣ) : k) :=
      alongMulEquiv_agrees D.quotientAmbientRoot
        (downLocalRoot (p := p) (k := k) (K := K) (A := A)
          P G hP root kernel regular thetaBar W hPG hUT) (eL) D.downLocalAgree z
    _ = _ := (D.quotientAmbientRoot.alongMulEquiv_lift (eT) _).symm

/-- Native quotient data have actual base/local roots and literal native
block catalogues. Their root guards are derived from the prescribed target
ambient root and the checked complete lift-function equalities. -/
def nativeData (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (blocks : PhysicalBlockFamily (k := k) NQ HQ) :
    TripleData (p := p) (k := k) (K := K) NQ HQ :=
  withPrescribedRoots NQ HQ
    (nativeAmbientRoot P G hPG hPambient root kernel regular thetaBar W hUT D)
    (TypeBCentralKernelQuotientTripleCharacters.nativeBaseRoot
      P G hP root kernel regular thetaBar)
    (TypeBCentralKernelQuotientTripleCharacters.nativeLocalRoot
      P G hP root kernel regular thetaBar W hPG hUT)
    (nativeBaseAgree P G hPG hPambient root kernel regular thetaBar W hUT D)
    (nativeLocalAgree P G hPG hPambient root kernel regular thetaBar W hUT D) blocks

def nativeTheta (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (blocks : PhysicalBlockFamily (k := k) NQ HQ) :
    IBr (nativeData P G hPG hPambient root kernel regular thetaBar W hUT D blocks).base.iota :=
  TypeBCentralKernelQuotientTripleCharacters.nativeBaseCharacter
    P G hP root kernel regular thetaBar

def nativePhi (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (blocks : PhysicalBlockFamily (k := k) NQ HQ)
    (navarro : Navarro318Certificate p k K) :
    IBr (nativeData P G hPG hPambient root kernel regular thetaBar W hUT D blocks).localData.iota :=
  TypeBCentralKernelQuotientTripleCharacters.nativeLocalCharacter
    P G hP root kernel regular thetaBar W hPG hUT navarro

theorem nativeAmbientRootsCompatible (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (blocks : PhysicalBlockFamily (k := k) NQ HQ) :
    AmbientRootsCompatible
      (nativeData P G hPG hPambient root kernel regular thetaBar W hUT D blocks)
      (downData P G hPG hPambient root kernel regular thetaBar W hUT D) := by
  intro z _ _
  exact D.quotientAmbientRoot.alongMulEquiv_lift (eT) (z : k)

/-- Apply the exact Butterfly certificate to the existing native quotient
witness. The output is literally the quotient-image witness required by
`TypeBCentralKernelTripleDataBinding.perPairInflate`. -/
theorem transport (hUT : U G W ≤ TI)
    (D : PerPairData P G hPG hPambient root kernel regular thetaBar W hUT)
    (blocks : PhysicalBlockFamily (k := k) NQ HQ)
    (navarro : Navarro318Certificate p k K)
    (certificate : ButterflyCertificate p k K)
    (sourceWitness : Nonempty (BlockTripleWitness
      (nativeData P G hPG hPambient root kernel regular thetaBar W hUT D blocks)
      (nativeTheta P G hPG hPambient root kernel regular thetaBar W hUT D blocks)
      (nativePhi P G hPG hPambient root kernel regular thetaBar W hUT D blocks navarro))) :
    Nonempty (BlockTripleWitness
      (downData P G hPG hPambient root kernel regular thetaBar W hUT D)
      (downTheta P G hPG hPambient root kernel regular thetaBar W hUT D)
      (downPhi P G hPG hPambient root kernel regular thetaBar W hUT D navarro)) := by
  obtain ⟨witness⟩ := sourceWitness
  exact transfer_with_local_image NQ (Nbar P G TI) HQ (Hbar P G TI W)
    (eT).symm (eN).symm
    (inverse_base_anchor P G hPG hPambient root kernel regular thetaBar)
    (inverse_local_image P G hPambient root kernel regular thetaBar W)
    (eL).symm
    (inverse_local_anchor P G hPG hPambient root kernel regular thetaBar W)
    (nativeData P G hPG hPambient root kernel regular thetaBar W hUT D blocks)
    (downData P G hPG hPambient root kernel regular thetaBar W hUT D)
    (nativeTheta P G hPG hPambient root kernel regular thetaBar W hUT D blocks)
    (nativePhi P G hPG hPambient root kernel regular thetaBar W hUT D blocks navarro)
    witness
    (downTheta P G hPG hPambient root kernel regular thetaBar W hUT D)
    (downPhi P G hPG hPambient root kernel regular thetaBar W hUT D navarro)
    (nativeAmbientRootsCompatible P G hPG hPambient root kernel regular thetaBar W hUT D blocks)
    (TypeBCentralKernelQuotientTripleCharacters.baseLifts P G hP root kernel regular thetaBar)
    (TypeBCentralKernelQuotientTripleCharacters.localLifts P G hP root kernel regular thetaBar W hPG hUT)
    (TypeBCentralKernelQuotientTripleCharacters.basePullback P G hP root kernel regular thetaBar hPG)
    (TypeBCentralKernelQuotientTripleCharacters.localPullback P G hP root kernel regular thetaBar W hPG hUT navarro)
    certificate

end ActualQuotient

end ModularRep.PaperProofs.TypeBCentralKernelQuotientTripleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
