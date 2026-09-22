import ModularRep.IrreducibleBrauerCharacter
import ModularRep.NormalCoreIBAWTransport
import ModularRep.WeightRightActionCoherence

/-!
# Source-shaped normal-core transport for manuscript Lemma 2.6

This file replaces two abstract carriers in `NormalCoreIBAWTransport` by the
actual function-valued irreducible Brauer characters and the actual
conjugacy classes of representation weights.  Routine facts about a normal
`p`-core are kept as exact source inputs.  In particular, the file does not
reprove that irreducible Brauer characters have the `p`-core in their kernel,
or that quotienting by the `p`-core identifies weights.

The kernel-checked work here is the manuscript-specific transport: literal
inflation of class functions is shown to commute with every automorphism
preserving the core, the source-supplied weight identification is descended
to actual conjugacy classes, and both maps are combined with a downstairs
iBAW candidate.  No upstairs bijection or iBAW conclusion is an input.
-/

noncomputable section

namespace ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation

universe u

section ClassFunctionInflation

variable {p : ℕ} {K G H : Type u}
  [Field K] [Group G] [Group H]

/-- Literal pullback of a prime regular class function.  For a quotient map
this is inflation. -/
def pullbackPrimeRegularClassFunction
    (f : G →* H) (phi : PrimeRegularClassFunction K H p) :
    PrimeRegularClassFunction K G p where
  toFun := phi.toFun.pullback f
  map_conj x g := by
    change phi (PrimeRegularElement.map f
      ⟨x * g.1 * x⁻¹, g.2.conj x⟩) =
        phi (PrimeRegularElement.map f g)
    have hmap :
        PrimeRegularElement.map f ⟨x * g.1 * x⁻¹, g.2.conj x⟩ =
          ⟨f x * (PrimeRegularElement.map f g).1 * (f x)⁻¹,
            (PrimeRegularElement.map f g).2.conj (f x)⟩ := by
      apply Subtype.ext
      change f (x * g.1 * x⁻¹) = f x * f g.1 * (f x)⁻¹
      simp
    rw [hmap]
    exact phi.map_conj (f x) (PrimeRegularElement.map f g)

@[simp]
theorem pullbackPrimeRegularClassFunction_apply
    (f : G →* H) (phi : PrimeRegularClassFunction K H p)
    (g : PrimeRegularElement (G := G) p) :
    pullbackPrimeRegularClassFunction f phi g =
      phi (PrimeRegularElement.map f g) :=
  rfl

/-- Pullback commutes with compatible automorphisms of the source and
target groups. -/
theorem pullback_twist
    (f : G →* H) (alpha : MulAut G) (beta : MulAut H)
    (hcomm : ∀ g : G, f (alpha g) = beta (f g))
    (phi : PrimeRegularClassFunction K H p) :
    pullbackPrimeRegularClassFunction f (phi.twist beta) =
      (pullbackPrimeRegularClassFunction f phi).twist alpha := by
  ext g
  exact congrArg phi (Subtype.ext (hcomm g.1).symm)

end ClassFunctionInflation

section QuotientAutomorphisms

variable {G : Type u} [Group G]
variable (P : Subgroup G) [P.Normal]

/-- An automorphism preserving `P` induces an automorphism of `G / P`. -/
def quotientMulAut (alpha : MulAut G)
    (hP : P.map alpha.toMonoidHom = P) : MulAut (G ⧸ P) where
  toFun := QuotientGroup.map P P alpha.toMonoidHom (by
    intro g hg
    rw [← hP]
    exact ⟨g, hg, rfl⟩)
  invFun := QuotientGroup.map P P alpha.symm.toMonoidHom (by
    intro g hg
    have hPinv : P.map alpha.symm.toMonoidHom = P := by
      apply le_antisymm
      · intro x hx
        rcases hx with ⟨y, hy, rfl⟩
        have hyMap : y ∈ P.map alpha.toMonoidHom := by
          rw [hP]
          exact hy
        rcases hyMap with ⟨z, hz, hzy⟩
        have heq : alpha.symm y = z := by
          rw [← hzy]
          simp
        simpa [heq] using hz
      · intro x hx
        have hax : alpha x ∈ P := by
          rw [← hP]
          exact ⟨x, hx, rfl⟩
        exact ⟨alpha x, hax, by simp⟩
    rw [← hPinv]
    exact ⟨g, hg, rfl⟩)
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro g
    change QuotientGroup.mk' P (alpha.symm (alpha g)) =
      QuotientGroup.mk' P g
    simp
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro g
    change QuotientGroup.mk' P (alpha (alpha.symm g)) =
      QuotientGroup.mk' P g
    simp
  map_mul' q r := map_mul _ q r

@[simp]
theorem quotientMulAut_mk (alpha : MulAut G)
    (hP : P.map alpha.toMonoidHom = P) (g : G) :
    quotientMulAut P alpha hP (QuotientGroup.mk' P g) =
      QuotientGroup.mk' P (alpha g) :=
  rfl

end QuotientAutomorphisms

section ActualBrauerInflation

variable {p : ℕ} {k K G : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]
variable (P : Subgroup G) [P.Normal]
variable (iotaDown : PrimeRegularRootEmbedding p k K (G ⧸ P))
variable (iotaUp : PrimeRegularRootEmbedding p k K G)

/-- Exact E1 input for Brauer inflation through a normal `p`-subgroup.

The first field is irreducibility of literal inflation.  The second is the
kernel theorem in its exact function-valued descent form.  The third is the
routine fact that a `p`-regular element of the quotient has a `p`-regular
lift.  None of these fields asserts a character-to-weight bijection. -/
structure BrauerInflationInput where
  inflatedIrreducible : ∀ phi : IBr iotaDown,
    IsIrreducibleBrauerCharacter iotaUp
      (pullbackPrimeRegularClassFunction (QuotientGroup.mk' P) phi.1)
  descends : ∀ psi : IBr iotaUp,
    ∃ phi : IBr iotaDown,
      pullbackPrimeRegularClassFunction (QuotientGroup.mk' P) phi.1 = psi.1
  regularLift : ∀ h : PrimeRegularElement (G := G ⧸ P) p,
    ∃ g : PrimeRegularElement (G := G) p,
      PrimeRegularElement.map (QuotientGroup.mk' P) g = h

namespace BrauerInflationInput

/-- Actual function-valued inflation on `IBr`. -/
def inflate
    (D : BrauerInflationInput P iotaDown iotaUp) :
    IBr iotaDown → IBr iotaUp := fun phi ↦
  ⟨pullbackPrimeRegularClassFunction (QuotientGroup.mk' P) phi.1,
    D.inflatedIrreducible phi⟩

@[simp]
theorem inflate_val
    (D : BrauerInflationInput P iotaDown iotaUp) (phi : IBr iotaDown) :
    (inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D phi).1 =
      pullbackPrimeRegularClassFunction (QuotientGroup.mk' P) phi.1 :=
  rfl

theorem inflate_injective
    (D : BrauerInflationInput P iotaDown iotaUp) :
    Function.Injective
      (inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D) := by
  intro phi psi h
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro x
  rcases D.regularLift x with ⟨g, hg⟩
  have hv := congrArg
    (fun z : IBr iotaUp ↦ z.1 g) h
  change phi.1 (PrimeRegularElement.map (QuotientGroup.mk' P) g) =
    psi.1 (PrimeRegularElement.map (QuotientGroup.mk' P) g) at hv
  simpa [hg] using hv

theorem inflate_surjective
    (D : BrauerInflationInput P iotaDown iotaUp) :
    Function.Surjective
      (inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D) := by
  intro psi
  rcases D.descends psi with ⟨phi, hphi⟩
  refine ⟨phi, ?_⟩
  exact Subtype.ext hphi

/-- The canonical function-valued Brauer inflation equivalence. -/
def equiv
    (D : BrauerInflationInput P iotaDown iotaUp) :
    IBr iotaDown ≃ IBr iotaUp :=
  Equiv.ofBijective
    (inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D)
    ⟨inflate_injective (P := P) (iotaDown := iotaDown)
        (iotaUp := iotaUp) D,
      inflate_surjective (P := P) (iotaDown := iotaDown)
        (iotaUp := iotaUp) D⟩

@[simp]
theorem equiv_apply
    (D : BrauerInflationInput P iotaDown iotaUp) (phi : IBr iotaDown) :
    equiv (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D phi =
      inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D phi :=
  rfl

/-- Literal Brauer inflation intertwines an automorphism of `G` preserving
`P` with its induced quotient automorphism. -/
theorem inflate_twist
    (D : BrauerInflationInput P iotaDown iotaUp)
    (alpha : MulAut G) (hP : P.map alpha.toMonoidHom = P)
    (phi : IBr iotaDown) :
    inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D
        (IrreducibleBrauerCharacter.twist iotaDown phi
          (quotientMulAut P alpha hP)) =
      IrreducibleBrauerCharacter.twist iotaUp
        (inflate (P := P) (iotaDown := iotaDown) (iotaUp := iotaUp) D phi)
        alpha := by
  apply Subtype.ext
  exact pullback_twist (QuotientGroup.mk' P) alpha
    (quotientMulAut P alpha hP)
    (fun g ↦ rfl) phi.1

end BrauerInflationInput

end ActualBrauerInflation

section ActualWeightTransport

open CategoryTheory

variable {p : ℕ} {K G : Type u}
  [Field K] [CharZero K] [Group G] [Finite G]

/-- Exact E1 input identifying representation weights through the normal
`p`-core.  The maps in every field are the literal constructions from
`NormalCoreTransport`; only their routine functoriality on isomorphism
classes, their inverse laws, and their compatibility with automorphisms are
supplied.  No character-to-weight correspondence occurs here. -/
structure WeightTransportInput where
  liftIsomorphic :
    ∀ {W W' : RepresentationWeight p K (G ⧸ pCore p G)},
      RepresentationWeight.Isomorphic W W' →
        RepresentationWeight.Isomorphic W.liftFromQuotientPCore
          W'.liftFromQuotientPCore
  quotientIsomorphic :
    ∀ {W W' : RepresentationWeight p K G},
      RepresentationWeight.Isomorphic W W' →
        RepresentationWeight.Isomorphic W.quotientPCore W'.quotientPCore
  quotientLift : ∀ W : RepresentationWeight p K (G ⧸ pCore p G),
    RepresentationWeight.Isomorphic
      W.liftFromQuotientPCore.quotientPCore W
  liftQuotient : ∀ W : RepresentationWeight p K G,
    RepresentationWeight.Isomorphic
      W.quotientPCore.liftFromQuotientPCore W
  automorphismNatural :
    ∀ (W : RepresentationWeight p K (G ⧸ pCore p G))
      (alpha : MulAut G),
      RepresentationWeight.Isomorphic
        ((W.rightTwist
          (quotientMulAut (pCore p G) alpha
            (pCore_map_equiv p alpha))).liftFromQuotientPCore)
        (W.liftFromQuotientPCore.rightTwist alpha)

namespace WeightTransportInput

/-- Lifting on actual representation-weight isomorphism classes. -/
def liftIsoClass (D : WeightTransportInput (p := p) (K := K) (G := G)) :
    RepresentationWeight.IsoClass
        (p := p) (K := K) (G := G ⧸ pCore p G) →
      RepresentationWeight.IsoClass (p := p) (K := K) (G := G) :=
  Quotient.map RepresentationWeight.liftFromQuotientPCore
    (fun _ _ h ↦ D.liftIsomorphic h)

/-- Quotienting on actual representation-weight isomorphism classes. -/
def quotientIsoClass
    (D : WeightTransportInput (p := p) (K := K) (G := G)) :
    RepresentationWeight.IsoClass (p := p) (K := K) (G := G) →
      RepresentationWeight.IsoClass
        (p := p) (K := K) (G := G ⧸ pCore p G) :=
  Quotient.map RepresentationWeight.quotientPCore
    (fun _ _ h ↦ D.quotientIsomorphic h)

@[simp]
theorem quotientIsoClass_liftIsoClass
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (x : RepresentationWeight.IsoClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    D.quotientIsoClass (D.liftIsoClass x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (D.quotientLift W)

@[simp]
theorem liftIsoClass_quotientIsoClass
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (x : RepresentationWeight.IsoClass (p := p) (K := K) (G := G)) :
    D.liftIsoClass (D.quotientIsoClass x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (D.liftQuotient W)

/-- The source-supplied normal-core identification gives an equivalence on
the actual isomorphism classes of representation weights. -/
def isoClassEquiv
    (D : WeightTransportInput (p := p) (K := K) (G := G)) :
    RepresentationWeight.IsoClass
        (p := p) (K := K) (G := G ⧸ pCore p G) ≃
      RepresentationWeight.IsoClass (p := p) (K := K) (G := G) where
  toFun := D.liftIsoClass
  invFun := D.quotientIsoClass
  left_inv := D.quotientIsoClass_liftIsoClass
  right_inv := D.liftIsoClass_quotientIsoClass

/-- The lift on isomorphism classes commutes with any automorphism of `G`
and its induced quotient automorphism. -/
theorem liftIsoClass_rightTwist
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (alpha : MulAut G)
    (x : RepresentationWeight.IsoClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    D.liftIsoClass
        (RepresentationWeight.rightTwistIsoClass
          (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)) x) =
      RepresentationWeight.rightTwistIsoClass alpha (D.liftIsoClass x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact Quotient.sound (D.automorphismNatural W alpha)

/-- The induced quotient automorphism of an inner automorphism is the inner
automorphism induced by the quotient element. -/
theorem quotientMulAut_conj (g : G) :
    quotientMulAut (pCore p G) (MulAut.conj g)
        (pCore_map_equiv p (MulAut.conj g)) =
      MulAut.conj (QuotientGroup.mk' (pCore p G) g) := by
  apply DFunLike.ext
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  change QuotientGroup.mk' (pCore p G) (g * y * g⁻¹) =
    QuotientGroup.mk' (pCore p G) g *
      QuotientGroup.mk' (pCore p G) y *
        (QuotientGroup.mk' (pCore p G) g)⁻¹
  simp

/-- Quotienting is equivariant on weight isomorphism classes.  This is
derived from equivariance of the inverse lift, rather than supplied as a
second naturality assumption. -/
theorem quotientIsoClass_rightTwist
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (alpha : MulAut G)
    (x : RepresentationWeight.IsoClass (p := p) (K := K) (G := G)) :
    D.quotientIsoClass
        (RepresentationWeight.rightTwistIsoClass alpha x) =
      RepresentationWeight.rightTwistIsoClass
        (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha))
        (D.quotientIsoClass x) := by
  apply D.isoClassEquiv.injective
  exact
    calc
      D.liftIsoClass
          (D.quotientIsoClass
            (RepresentationWeight.rightTwistIsoClass alpha x)) =
          RepresentationWeight.rightTwistIsoClass alpha x :=
        D.liftIsoClass_quotientIsoClass _
      _ = RepresentationWeight.rightTwistIsoClass alpha
            (D.liftIsoClass (D.quotientIsoClass x)) := by
        rw [D.liftIsoClass_quotientIsoClass]
      _ = D.liftIsoClass
            (RepresentationWeight.rightTwistIsoClass
              (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha))
              (D.quotientIsoClass x)) :=
        (D.liftIsoClass_rightTwist alpha _).symm

/-- Lifting descends to the actual ambient conjugacy classes of
representation weights. -/
def liftConjugacyClass
    (D : WeightTransportInput (p := p) (K := K) (G := G)) :
    RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G) →
      RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G) :=
  Quotient.map D.liftIsoClass (by
    intro x y hxy
    rcases hxy with ⟨gbar, rfl⟩
    rcases QuotientGroup.mk'_surjective (pCore p G) gbar with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have hEq : D.liftIsoClass
        (RepresentationWeight.rightTwistIsoClass (MulAut.conj gbar⁻¹) y) =
      RepresentationWeight.rightTwistIsoClass (MulAut.conj g⁻¹)
        (D.liftIsoClass y) := by
      have hauto :
          quotientMulAut (pCore p G) (MulAut.conj g⁻¹)
              (pCore_map_equiv p (MulAut.conj g⁻¹)) =
            MulAut.conj gbar⁻¹ := by
        rw [quotientMulAut_conj]
        congr 1
        simpa using congrArg Inv.inv hg
      rw [← hauto]
      exact D.liftIsoClass_rightTwist (MulAut.conj g⁻¹) y
    exact hEq.symm)

/-- Quotienting descends to the actual ambient conjugacy classes of
representation weights. -/
def quotientConjugacyClass
    (D : WeightTransportInput (p := p) (K := K) (G := G)) :
    RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G) →
      RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G) :=
  Quotient.map D.quotientIsoClass (by
    intro x y hxy
    rcases hxy with ⟨g, rfl⟩
    refine ⟨QuotientGroup.mk' (pCore p G) g, ?_⟩
    have hEq : D.quotientIsoClass
        (RepresentationWeight.rightTwistIsoClass (MulAut.conj g⁻¹) y) =
      RepresentationWeight.rightTwistIsoClass
        (MulAut.conj (QuotientGroup.mk' (pCore p G) g)⁻¹)
        (D.quotientIsoClass y) := by
      rw [D.quotientIsoClass_rightTwist]
      congr 2
      rw [quotientMulAut_conj]
      congr 1
    exact hEq.symm)

@[simp]
theorem quotientConjugacyClass_liftConjugacyClass
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (x : RepresentationWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    D.quotientConjugacyClass (D.liftConjugacyClass x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : RepresentationWeight.IsoClass
        (p := p) (K := K) (G := G ⧸ pCore p G) ↦
      (Quotient.mk'' z : RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G)))
    (D.quotientIsoClass_liftIsoClass W)

@[simp]
theorem liftConjugacyClass_quotientConjugacyClass
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (x : RepresentationWeight.ConjugacyClass
      (p := p) (K := K) (G := G)) :
    D.liftConjugacyClass (D.quotientConjugacyClass x) = x := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : RepresentationWeight.IsoClass (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G)))
    (D.liftIsoClass_quotientIsoClass W)

/-- The actual conjugacy classes of representation weights are equivalent
across the normal `p`-core. -/
def conjugacyClassEquiv
    (D : WeightTransportInput (p := p) (K := K) (G := G)) :
    RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G ⧸ pCore p G) ≃
      RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G) where
  toFun := D.liftConjugacyClass
  invFun := D.quotientConjugacyClass
  left_inv := D.quotientConjugacyClass_liftConjugacyClass
  right_inv := D.liftConjugacyClass_quotientConjugacyClass

/-- The actual conjugacy class equivalence commutes with automorphism
transport. -/
theorem liftConjugacyClass_rightTwist
    (D : WeightTransportInput (p := p) (K := K) (G := G))
    (alpha : MulAut G)
    (x : RepresentationWeight.ConjugacyClass
      (p := p) (K := K) (G := G ⧸ pCore p G)) :
    D.liftConjugacyClass
        (RepresentationWeight.rightTwistConjugacyClass
          (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)) x) =
      RepresentationWeight.rightTwistConjugacyClass alpha
        (D.liftConjugacyClass x) := by
  refine Quotient.inductionOn x ?_
  intro W
  exact congrArg
    (fun z : RepresentationWeight.IsoClass (p := p) (K := K) (G := G) ↦
      (Quotient.mk'' z : RepresentationWeight.ConjugacyClass
        (p := p) (K := K) (G := G)))
    (D.liftIsoClass_rightTwist alpha W)

end WeightTransportInput

end ActualWeightTransport

section ActualCandidateTransport

variable {p : ℕ} {k K G BlockDown BlockUp : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group G] [Finite G]
variable (iotaDown :
  PrimeRegularRootEmbedding p k K (G ⧸ pCore p G))
variable (iotaUp : PrimeRegularRootEmbedding p k K G)

abbrev DownWeights := RepresentationWeight.ConjugacyClass
  (p := p) (K := K) (G := G ⧸ pCore p G)

abbrev UpWeights := RepresentationWeight.ConjugacyClass
  (p := p) (K := K) (G := G)

/-- The actual upstairs equivalence obtained by deflating a function-valued
Brauer character, applying the downstairs correspondence, and lifting the
actual conjugacy class of representation weights. -/
def transportedEquiv
    (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
    (W : WeightTransportInput (p := p) (K := K) (G := G))
    (downstairs : IBr iotaDown ≃ DownWeights (p := p) (K := K) (G := G)) :
    IBr iotaUp ≃ UpWeights (p := p) (K := K) (G := G) :=
  (B.equiv (P := pCore p G) (iotaDown := iotaDown)
    (iotaUp := iotaUp)).symm.trans
    (downstairs.trans W.conjugacyClassEquiv)

@[simp]
theorem transportedEquiv_inflate
    (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
    (W : WeightTransportInput (p := p) (K := K) (G := G))
    (downstairs : IBr iotaDown ≃ DownWeights (p := p) (K := K) (G := G))
    (phi : IBr iotaDown) :
  transportedEquiv iotaDown iotaUp B W downstairs
        (B.inflate (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp) phi) =
      W.liftConjugacyClass (downstairs phi) := by
  change W.liftConjugacyClass
      (downstairs ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)).symm
          (B.inflate (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp) phi))) =
    W.liftConjugacyClass (downstairs phi)
  have hinflate := B.equiv_apply (P := pCore p G)
    (iotaDown := iotaDown) (iotaUp := iotaUp) phi
  have hsymm :
      (B.equiv (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)).symm
          (B.inflate (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp) phi) = phi := by
    calc
      (B.equiv (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp)).symm
            (B.inflate (P := pCore p G) (iotaDown := iotaDown)
              (iotaUp := iotaUp) phi) =
          (B.equiv (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp)).symm
              (B.equiv (P := pCore p G) (iotaDown := iotaDown)
                (iotaUp := iotaUp) phi) :=
        congrArg
          (B.equiv (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp)).symm hinflate.symm
      _ = phi := (B.equiv (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)).symm_apply_apply phi
  exact congrArg (fun z ↦ W.liftConjugacyClass (downstairs z)) hsymm

/-- Inverse Brauer inflation commutes with an automorphism preserving the
`p`-core. -/
theorem equiv_symm_twist
    (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
    (alpha : MulAut G) (phi : IBr iotaUp) :
    (B.equiv (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp)).symm
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha) =
      IrreducibleBrauerCharacter.twist iotaDown
        ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp)).symm phi)
        (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha)) := by
  apply (B.equiv (P := pCore p G) (iotaDown := iotaDown)
    (iotaUp := iotaUp)).injective
  calc
    B.equiv (P := pCore p G) (iotaDown := iotaDown) (iotaUp := iotaUp)
        ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp)).symm
          (IrreducibleBrauerCharacter.twist iotaUp phi alpha)) =
        IrreducibleBrauerCharacter.twist iotaUp phi alpha :=
      (B.equiv (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)).apply_symm_apply _
    _ = IrreducibleBrauerCharacter.twist iotaUp
          (B.inflate (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp)
              ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
                (iotaUp := iotaUp)).symm phi))
          alpha := by
      rw [← B.equiv_apply (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)]
      simp
    _ = B.equiv (P := pCore p G) (iotaDown := iotaDown) (iotaUp := iotaUp)
          (IrreducibleBrauerCharacter.twist iotaDown
            ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
              (iotaUp := iotaUp)).symm phi)
            (quotientMulAut (pCore p G) alpha
              (pCore_map_equiv p alpha))) := by
      rw [B.equiv_apply (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)]
      exact (B.inflate_twist (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp) alpha (pCore_map_equiv p alpha)
        ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp)).symm phi)).symm

/-- Manuscript-specific equivariance of the transported correspondence on
the sets of characters and weights.  The only correspondence premise
is the downstairs equivariance equation. -/
theorem transportedEquiv_equivariant
    (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
    (W : WeightTransportInput (p := p) (K := K) (G := G))
    (downstairs : IBr iotaDown ≃ DownWeights (p := p) (K := K) (G := G))
    (hDown : ∀ (alpha : MulAut G) (phi : IBr iotaDown),
      downstairs
          (IrreducibleBrauerCharacter.twist iotaDown phi
            (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha))) =
        RepresentationWeight.rightTwistConjugacyClass
          (quotientMulAut (pCore p G) alpha (pCore_map_equiv p alpha))
          (downstairs phi))
    (alpha : MulAut G) (phi : IBr iotaUp) :
    transportedEquiv iotaDown iotaUp B W downstairs
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha) =
      RepresentationWeight.rightTwistConjugacyClass alpha
        (transportedEquiv iotaDown iotaUp B W downstairs phi) := by
  change W.liftConjugacyClass
      (downstairs ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
        (iotaUp := iotaUp)).symm
        (IrreducibleBrauerCharacter.twist iotaUp phi alpha))) =
    RepresentationWeight.rightTwistConjugacyClass alpha
      (W.liftConjugacyClass
        (downstairs ((B.equiv (P := pCore p G) (iotaDown := iotaDown)
          (iotaUp := iotaUp)).symm phi)))
  rw [equiv_symm_twist, hDown, W.liftConjugacyClass_rightTwist]

/-- Source-shaped block data needed by the actual candidate transport.
These are block labels and compatibility equations, not an upstairs
character-to-weight bijection. -/
structure BlockTransportInput
    (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
    (W : WeightTransportInput (p := p) (K := K) (G := G)) where
  blockEquiv : BlockDown ≃ BlockUp
  brauerBlockDown : IBr iotaDown → BlockDown
  brauerBlockUp : IBr iotaUp → BlockUp
  weightBlockDown : DownWeights (p := p) (K := K) (G := G) → BlockDown
  weightBlockUp : UpWeights (p := p) (K := K) (G := G) → BlockUp
  brauerCompatible : ∀ phi : IBr iotaDown,
    brauerBlockUp (B.inflate (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp) phi) =
      blockEquiv (brauerBlockDown phi)
  weightCompatible : ∀ omega : DownWeights (p := p) (K := K) (G := G),
    weightBlockUp (W.liftConjugacyClass omega) =
      blockEquiv (weightBlockDown omega)

namespace BlockTransportInput

/-- The transported equivalence preserves the block induced from the local
weight, assuming only downstairs block preservation and the two canonical
block-transport equations. -/
theorem transportedEquiv_block_preserving
    (B : BrauerInflationInput (pCore p G) iotaDown iotaUp)
    (W : WeightTransportInput (p := p) (K := K) (G := G))
    (T : BlockTransportInput (BlockDown := BlockDown) (BlockUp := BlockUp)
      iotaDown iotaUp B W)
    (downstairs : IBr iotaDown ≃ DownWeights (p := p) (K := K) (G := G))
    (hDown : ∀ phi : IBr iotaDown,
      T.weightBlockDown (downstairs phi) = T.brauerBlockDown phi)
    (phi : IBr iotaUp) :
    T.weightBlockUp
        (transportedEquiv iotaDown iotaUp B W downstairs phi) =
      T.brauerBlockUp phi := by
  let phiDown := (B.equiv (P := pCore p G) (iotaDown := iotaDown)
    (iotaUp := iotaUp)).symm phi
  have hphi : B.inflate (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp) phiDown = phi := by
    exact (B.equiv (P := pCore p G) (iotaDown := iotaDown)
      (iotaUp := iotaUp)).apply_symm_apply phi
  calc
    T.weightBlockUp
        (transportedEquiv iotaDown iotaUp B W downstairs phi) =
        T.weightBlockUp (W.liftConjugacyClass (downstairs phiDown)) := by
      rw [← hphi, transportedEquiv_inflate]
    _ = T.blockEquiv (T.weightBlockDown (downstairs phiDown)) :=
      T.weightCompatible _
    _ = T.blockEquiv (T.brauerBlockDown phiDown) :=
      congrArg T.blockEquiv (hDown phiDown)
    _ = T.brauerBlockUp
          (B.inflate (P := pCore p G) (iotaDown := iotaDown)
            (iotaUp := iotaUp) phiDown) :=
      (T.brauerCompatible phiDown).symm
    _ = T.brauerBlockUp phi := congrArg T.brauerBlockUp hphi

end BlockTransportInput

end ActualCandidateTransport

end ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
