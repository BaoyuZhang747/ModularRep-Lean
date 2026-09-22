import ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate

/-!
# The one-way Butterfly theorem on literal block-triple carriers

This is the source interface for Feng--Li--Zhang, Jordan decomposition for
weights, Theorem 3.2, pp. 9--10, equivalently the Butterfly lemma in
Martinez--Rizo--Rossi (author TeX lines 673--681). It is a certificate TYPE;
no axiom, inhabitant or application is declared here.

The two normal base groups are identified by a displayed group equivalence.
Both ambient conjugation maps consequently have the SAME actual target
`MulAut N1`. The second local ambient group is defined as the full preimage
of the first local group's actual image. It is not a freely chosen subgroup.
The local-base identification has a pointwise equation over the base
equivalence. Character values, roots and specified primitive-block transport
are explicit source-to-carrier guards. The output is the independently fixed
`BlockTripleWitness`, not an iBAW predicate or a chosen conversion relation.

The source uses one fixed modular system. Its identification with the fields,
root conventions and specified catalogues below remains E2/U. The displayed
root/character/block guards are carrier identifications to be proved in an
application, not additional published representation theoretic conclusions.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBCentralKernelButterflyCertificate

open ModularRep TypeBCentralKernelTripleCertificate

universe u

section Groups

variable {T1 T2 : Type u} [Group T1] [Group T2]
  (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]

/-- Actual conjugation on the first literal normal subgroup. -/
def firstAction : T1 →* MulAut N1 := MulAut.conjNormal (H := N1)

/-- Actual conjugation on the second normal subgroup, transported back
through the specified base identification. -/
def secondAction (e : N1 ≃* N2) : T2 →* MulAut N1 :=
  (MulAut.congr e).symm.toMonoidHom.comp (MulAut.conjNormal (H := N2))

theorem firstAction_value (t : T1) (n : N1) :
    (firstAction N1 t n : T1) = t * (n : T1) * t⁻¹ := rfl

theorem secondAction_value (e : N1 ≃* N2) (t : T2) (n : N1) :
    e (secondAction N1 N2 e t n) = MulAut.conjNormal (H := N2) t (e n) := by
  change e (e.symm _) = _
  exact e.apply_symm_apply _

/-- The source hypothesis is equality of literal conjugation images in
one actual automorphism group, not an abstract isomorphism of outer groups. -/
def SameConjugationImage (e : N1 ≃* N2) : Prop :=
  (firstAction N1).range = (secondAction N1 N2 e).range

/-- The new local ambient is precisely the preimage prescribed by the
Butterfly theorem. No normality of either local ambient is imposed. -/
def secondLocalAmbient (e : N1 ≃* N2) (H1 : Subgroup T1) : Subgroup T2 :=
  (H1.map (firstAction N1)).comap (secondAction N1 N2 e)

theorem mem_secondLocalAmbient (e : N1 ≃* N2) (H1 : Subgroup T1) (t : T2) :
    t ∈ secondLocalAmbient N1 N2 e H1 ↔
      ∃ h : T1, h ∈ H1 ∧ firstAction N1 h = secondAction N1 N2 e t := Iff.rfl

end Groups

section Identifications

variable {T1 T2 : Type u} [Group T1] [Group T2]

/-- The canonical local intersection mapped into its literal normal base. -/
def localToBase (N H : Subgroup T1) : localBase N H →* N where
  toFun x := ⟨x.val.val, x.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- This local equivalence must cover the SAME base equivalence pointwise.
In particular it cannot independently identify unrelated local characters. -/
structure LocalIdentification (N1 : Subgroup T1) (N2 : Subgroup T2)
    (e : N1 ≃* N2) (H1 : Subgroup T1) (H2 : Subgroup T2) where
  equiv : localBase N1 H1 ≃* localBase N2 H2
  base_value : ∀ x : localBase N1 H1,
    localToBase N2 H2 (equiv x) = e (localToBase N1 H1 x)

variable {k K X Y : Type u} [Field k] [Field K]
  [Group X] [Finite X] [Group Y] [Finite Y]

/-- The actual group-basis transport of a primitive block. -/
def blockAlong (e : X ≃* Y) (b : LiteralPrimitiveBlock k X) :
    LiteralPrimitiveBlock k Y :=
  ⟨MonoidAlgebra.mapDomainRingEquiv k e b.val,
    b.property.mapRingEquiv (MonoidAlgebra.mapDomainRingEquiv k e)⟩

theorem blockAlong_value (e : X ≃* Y) (b : LiteralPrimitiveBlock k X) :
    (blockAlong e b).val = MonoidAlgebra.mapDomainRingEquiv k e b.val := rfl

variable {p : ℕ} [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Literal identification of one character on isomorphic carriers, with
its root convention and specified supporting block. These are application
guards; no free character or block matching is permitted. -/
structure CharacterIdentification (e : X ≃* Y)
    (DX : CharacterData p k K X) (DY : CharacterData p k K Y)
    (thetaX : IBr DX.iota) (thetaY : IBr DY.iota) : Prop where
  roots : ∀ z : rootsOfUnity (primeRegularExponent p X) k,
    DX.iota.lift ((z : kˣ) : k) = DY.iota.lift ((z : kˣ) : k)
  values : ∀ x : PrimeRegularElement (G := X) p,
    thetaX.val x = thetaY.val (PrimeRegularElement.map e.toMonoidHom x)
  physical_block : blockAlong e (DX.block thetaX) = DY.block thetaY

end Identifications

section Certificate

variable {p : ℕ} {k K : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  {T1 T2 : Type u} [Group T1] [Group T2] [Finite T1] [Finite T2]
  {N1 H1 : Subgroup T1} {N2 H2 : Subgroup T2}

/-- The two ambient root choices agree wherever both are defined on roots.
No equality of arbitrary extensions away from these root domains is used.
The source-to-modular-system realization remains explicit U. -/
def AmbientRootsCompatible
    (D1 : TripleData (p := p) (k := k) (K := K) N1 H1)
    (D2 : TripleData (p := p) (k := k) (K := K) N2 H2) : Prop :=
  ∀ z : kˣ,
    z ^ primeRegularExponent p T1 = 1 →
    z ^ primeRegularExponent p T2 = 1 →
      D1.ambientRoot.lift (z : k) = D2.ambientRoot.lift (z : k)

/-- Exact one-way Butterfly source, with explicit common-base/local
identifications. An existing literal block triple is transported to a new
actual ambient inducing the same automorphisms. The new local ambient is
the prescribed full preimage, and every character and block in the output
is bound by the displayed value and group algebra transport equations.

This structure has no declared inhabitant. In particular it is not a
source asserting a Type B bijection, an inductive condition, or an upstairs
triple without an existing source-side triple. -/
structure ButterflyCertificate (p : ℕ) (k K : Type u)
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K] where
  transfer : ∀ (T1 T2 : Type u) [Group T1] [Group T2] [Finite T1] [Finite T2]
      (N1 : Subgroup T1) (N2 : Subgroup T2) [N1.Normal] [N2.Normal]
      (e : N1 ≃* N2) (H1 : Subgroup T1)
      (D1 : TripleData (p := p) (k := k) (K := K) N1 H1)
      (D2 : TripleData (p := p) (k := k) (K := K)
        N2 (secondLocalAmbient N1 N2 e H1))
      (localId : LocalIdentification N1 N2 e H1 (secondLocalAmbient N1 N2 e H1))
      (theta1 : IBr D1.base.iota) (phi1 : IBr D1.localData.iota)
      (theta2 : IBr D2.base.iota) (phi2 : IBr D2.localData.iota),
    SameConjugationImage N1 N2 e →
    AmbientRootsCompatible D1 D2 →
    CharacterIdentification e D1.base D2.base theta1 theta2 →
    CharacterIdentification localId.equiv D1.localData D2.localData phi1 phi2 →
    Nonempty (BlockTripleWitness D1 theta1 phi1) →
    Nonempty (BlockTripleWitness D2 theta2 phi2)

end Certificate

end ModularRep.PaperProofs.TypeBCentralKernelButterflyCertificate


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
