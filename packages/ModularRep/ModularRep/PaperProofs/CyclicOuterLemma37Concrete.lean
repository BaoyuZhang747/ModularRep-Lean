import ModularRep.CyclicOuterBrauerExtension
import ModularRep.PaperProofs.CyclicOuterLemma37Relative
import ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal
import ModularRep.WeightCharacterBridge

/-!
# Characters and weights for manuscript Lemma 2.10

This file instantiates the manuscript-specific deductions in Lemma 2.10 on
the library's function-valued irreducible Brauer characters and on actual
character weights.  The routine structure of the finite simple group and
its automorphism group is an E1 source input.  The remaining clauses of
Feng--Li--Zhang, Theorem 3.18, are separate E2 inputs and are not encoded as
a BAW-good or iBAW premise.
-/

noncomputable section

namespace ModularRep.PaperProofs.CyclicOuterLemma37Concrete

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Relative

universe u

section ActualGlobalCarriers

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]

abbrev WeightClass :=
  CharacterWeight.ConjugacyClass (p := p) (K := K) (G := H)

/-- Inner automorphisms fix an ambient conjugacy class of actual character
weights. -/
theorem inner_fixes_weightClass (h : H)
    (w : WeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction H (WeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := WeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    h • w = w := by
  dsimp only [rightAutomorphismAction, inverseOpHom]
  refine Quotient.inductionOn w ?_
  intro x
  apply Quotient.sound
  exact ⟨h, rfl⟩

/-- The action data of Lemma 2.10 on the literal global carriers.  The only
character-theoretic datum is the cited blockwise equivalence `omega` and its
outer equivariance. -/
def actualActionData
    (iota : PrimeRegularRootEmbedding p k K H)
    (phi : E →* MulAut H)
    (omega : IBr iota ≃ WeightClass (p := p) (K := K) (H := H))
    (omegaE : ∀ (e : E) (psi : IBr iota),
      let _ : MulAction E (IBr iota) :=
        rightAutomorphismAction (X := IBr iota) phi
      let _ : MulAction E (WeightClass (p := p) (K := K) (H := H)) :=
        rightAutomorphismAction
          (X := WeightClass (p := p) (K := K) (H := H)) phi
      omega (e • psi) = e • omega psi) :
    let _ : MulAction H (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let _ : MulAction H (WeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := WeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (WeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := WeightClass (p := p) (K := K) (H := H)) phi
    ActionData phi (Brauer := IBr iota)
      (Weight := WeightClass (p := p) (K := K) (H := H)) := by
  dsimp only
  letI : MulAction H (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) phi
  letI : MulAction H (WeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := WeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (WeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := WeightClass (p := p) (K := K) (H := H)) phi
  exact
    { brauerCompatible :=
        rightAutomorphismSemidirectCompatible (X := IBr iota) phi
      weightCompatible :=
        rightAutomorphismSemidirectCompatible
          (X := WeightClass (p := p) (K := K) (H := H)) phi
      omega := omega
      omegaE := by
        intro e psi
        exact omegaE e psi
      brauerInnerTrivial := inner_fixes_ibr iota
      weightInnerTrivial := inner_fixes_weightClass }

end ActualGlobalCarriers

section ActualRawWeights

variable {p : ℕ} {K H E : Type u}
variable [Field K] [CharZero K] [Group H] [Finite H]
variable [Group E] [Finite E] [IsCyclic E]

abbrev RawWeightClass :=
  CharacterWeight.IsoClass (p := p) (K := K) (G := H)

/-- The radical subgroup belonging to an isomorphism class of actual
character weights.  This is well defined because weight isomorphism retains
the subgroup literally. -/
def rawSubgroup : RawWeightClass (p := p) (K := K) (H := H) → Subgroup H :=
  Quotient.lift (fun W : CharacterWeight p K H ↦ W.subgroup) (by
    intro W W' h
    exact h.choose)

@[simp]
theorem rawSubgroup_mk (W : CharacterWeight p K H) :
    rawSubgroup (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := H)) =
      W.subgroup :=
  rfl

/-- The first component of an actual raw weight transforms by conjugation
under the ambient group action. -/
theorem rawSubgroup_conjugate
    (h : H) (w : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    rawSubgroup (h • w) =
      (rawSubgroup w).map (MulAut.conj h).toMonoidHom := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  refine Quotient.inductionOn w ?_
  intro W
  change W.subgroup.comap (MulAut.conj h⁻¹).toMonoidHom =
    W.subgroup.map (MulAut.conj h).toMonoidHom
  have hconj : (MulAut.conj h).symm = MulAut.conj h⁻¹ := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  calc
    W.subgroup.comap (MulAut.conj h⁻¹).toMonoidHom =
        W.subgroup.comap (MulAut.conj h).symm.toMonoidHom := by rw [hconj]
    _ = W.subgroup.map (MulAut.conj h).toMonoidHom :=
      (Subgroup.map_equiv_eq_comap_symm
        (MulAut.conj h) W.subgroup).symm

/-- The radical subgroup transforms by the supplied automorphism under the
encoded right action. -/
theorem rawSubgroup_outer
    (phi : E →* MulAut H) (e : E)
    (w : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    rawSubgroup (e • w) =
      (rawSubgroup w).map (phi e).toMonoidHom := by
  dsimp only
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  refine Quotient.inductionOn w ?_
  intro W
  change W.subgroup.comap (phi e⁻¹).toMonoidHom =
    W.subgroup.map (phi e).toMonoidHom
  have hinv : (phi e).symm = phi e⁻¹ := by
    rw [map_inv]
    rfl
  calc
    W.subgroup.comap (phi e⁻¹).toMonoidHom =
        W.subgroup.comap (phi e).symm.toMonoidHom := by rw [hinv]
    _ = W.subgroup.map (phi e).toMonoidHom :=
      (Subgroup.map_equiv_eq_comap_symm (phi e) W.subgroup).symm

/-- The subgroup component of a raw weight under the full semidirect
action is the image under the corresponding automorphism of `H`. -/
theorem rawSubgroup_semidirect
    (phi : E →* MulAut H)
    (g : H ⋊[phi] E)
    (w : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      semidirectMulAction phi hcompat
    rawSubgroup (g • w) =
      (rawSubgroup w).map (semidirectToMulAut phi g).toMonoidHom := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  let hcompat := rightAutomorphismSemidirectCompatible
    (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    semidirectMulAction phi hcompat
  change rawSubgroup (g.left • (g.right • w)) = _
  rw [rawSubgroup_conjugate, rawSubgroup_outer]
  rw [Subgroup.map_map]
  rfl

/-- Stabilisation of a literal raw character-weight class supplies the exact
isomorphism of its local ordinary character after transport by the associated
automorphism.  This is the character-level information contained in the raw
pair stabiliser; no local Brauer fixedness is assumed. -/
theorem stabilizer_supplies_rawWeight_isomorphic
    (phi : E →* MulAut H) (W : CharacterWeight p K H) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      semidirectMulAction phi hcompat
    ∀ g : semidirectStabilizer (phi := phi)
        (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := H)),
      CharacterWeight.Isomorphic
        (W.rightTwist (semidirectToMulAut phi (g : H ⋊[phi] E)⁻¹)) W := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  let hcompat := rightAutomorphismSemidirectCompatible
    (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    semidirectMulAction phi hcompat
  intro g
  have hg := g.property
  change (g : H ⋊[phi] E) •
      (Quotient.mk'' W : RawWeightClass (p := p) (K := K) (H := H)) =
    Quotient.mk'' W at hg
  change Quotient.mk''
      ((W.rightTwist (phi g.1.right⁻¹)).rightTwist
        (MulAut.conj g.1.left⁻¹)) = Quotient.mk'' W at hg
  have hseq : CharacterWeight.Isomorphic
      ((W.rightTwist (phi g.1.right⁻¹)).rightTwist
        (MulAut.conj g.1.left⁻¹)) W := Quotient.exact hg
  have hproduct := CharacterWeight.rightTwist_mul_isomorphic W
    (phi g.1.right⁻¹) (MulAut.conj g.1.left⁻¹)
  have hprodToW := CharacterWeight.isomorphic_trans
    (CharacterWeight.isomorphic_symm hproduct) hseq
  have hauto : phi g.1.right⁻¹ * MulAut.conj g.1.left⁻¹ =
      semidirectToMulAut phi (g : H ⋊[phi] E)⁻¹ := by
    have hgMap : semidirectToMulAut phi (g : H ⋊[phi] E) =
        MulAut.conj g.1.left * phi g.1.right := by
      calc
        semidirectToMulAut phi (g : H ⋊[phi] E) =
            semidirectToMulAut phi
              (SemidirectProduct.inl g.1.left *
                SemidirectProduct.inr g.1.right) :=
          congrArg (semidirectToMulAut phi)
            (SemidirectProduct.inl_left_mul_inr_right g.1).symm
        _ = MulAut.conj g.1.left * phi g.1.right := by
          rw [map_mul, semidirectToMulAut_inl, semidirectToMulAut_inr]
    calc
      phi g.1.right⁻¹ * MulAut.conj g.1.left⁻¹ =
          (phi g.1.right)⁻¹ * (MulAut.conj g.1.left)⁻¹ := by
        congr 1
        · rw [map_inv]
        · change innerAutomorphismHom g.1.left⁻¹ =
            (innerAutomorphismHom g.1.left)⁻¹
          rw [map_inv]
      _ = (MulAut.conj g.1.left * phi g.1.right)⁻¹ := by
        rw [mul_inv_rev]
      _ = (semidirectToMulAut phi (g : H ⋊[phi] E))⁻¹ :=
        congrArg Inv.inv hgMap.symm
      _ = semidirectToMulAut phi (g : H ⋊[phi] E)⁻¹ :=
        (map_inv _ (g : H ⋊[phi] E)).symm
  rw [← hauto]
  exact hprodToW

/-- Evaluation of a local character after dependent transport along an
equality of radical subgroups. -/
theorem castLocalCharacter_apply
    {Q R : Subgroup H} (hQR : Q = R)
    (chi : OrdinaryIrreducibleCharacter.Irr K (NormalizerQuotient Q))
    (x : NormalizerQuotient R) :
    (CharacterWeight.castLocalCharacter hQR chi) x =
      chi ((MulEquiv.cast
        (M := fun S : Subgroup H ↦ NormalizerQuotient S) hQR).symm x) := by
  subst R
  rfl

/-- The subgroup equality attached to an element of the normaliser. -/
def normalizerConjugateSubgroupEq
    (W : CharacterWeight p K H) (h : H)
    (hh : h ∈ Subgroup.normalizer (W.subgroup : Set H)) :
    (W.rightTwist (MulAut.conj h⁻¹)).subgroup = W.subgroup := by
  have hmap : W.subgroup.map (MulAut.conj h).toMonoidHom = W.subgroup :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hh
  have hconj : (MulAut.conj h).symm = MulAut.conj h⁻¹ := by
    ext x
    simp [mul_assoc]
  change W.subgroup.comap (MulAut.conj h⁻¹).toMonoidHom = W.subgroup
  calc
    W.subgroup.comap (MulAut.conj h⁻¹).toMonoidHom =
        W.subgroup.comap (MulAut.conj h).symm.toMonoidHom := by rw [hconj]
    _ = W.subgroup.map (MulAut.conj h).toMonoidHom :=
      (Subgroup.map_equiv_eq_comap_symm
        (MulAut.conj h) W.subgroup).symm
    _ = W.subgroup := hmap

/-- Casting a normaliser quotient along an equality of subgroups does not
change the underlying normaliser element. -/
@[simp]
theorem normalizerQuotientCast_symm_mk
    {Q R : Subgroup H} (hQR : Q = R)
    (n : Subgroup.normalizer (R : Set H)) :
    (MulEquiv.cast
      (M := fun S : Subgroup H ↦ NormalizerQuotient S) hQR).symm
        (QuotientGroup.mk n) =
      QuotientGroup.mk
        (MulEquiv.cast
          (M := fun S : Subgroup H ↦
            Subgroup.normalizer (S : Set H)) hQR.symm n) := by
  subst R
  rfl

/-- Transport of a normaliser element along equality of its subgroup leaves
its underlying group element unchanged. -/
@[simp]
theorem normalizerCast_coe
    {Q R : Subgroup H} (hQR : Q = R)
    (n : Subgroup.normalizer (Q : Set H)) :
    ((MulEquiv.cast
      (M := fun S : Subgroup H ↦ Subgroup.normalizer (S : Set H))
      hQR n : Subgroup.normalizer (R : Set H)) : H) = n := by
  subst R
  rfl

/-- Direct transport by the inner automorphism induced by a normaliser
element is conjugation in the normaliser quotient. -/
theorem rightNormalizerQuotientEquiv_inner_apply
    (W : CharacterWeight p K H) (h : H)
    (hh : h ∈ Subgroup.normalizer (W.subgroup : Set H))
    (x : NormalizerQuotient W.subgroup) :
    rightNormalizerQuotientEquiv (MulAut.conj h⁻¹) W.subgroup
        ((MulEquiv.cast
          (M := fun S : Subgroup H ↦ NormalizerQuotient S)
          (normalizerConjugateSubgroupEq W h hh)).symm x) =
      (QuotientGroup.mk
          (⟨h, hh⟩ : Subgroup.normalizer (W.subgroup : Set H)))⁻¹ *
        x *
      QuotientGroup.mk
          (⟨h, hh⟩ : Subgroup.normalizer (W.subgroup : Set H)) := by
  let hQ : W.subgroup.comap (MulAut.conj h⁻¹).toMonoidHom =
      W.subgroup := normalizerConjugateSubgroupEq W h hh
  change rightNormalizerQuotientEquiv (MulAut.conj h⁻¹) W.subgroup
      ((MulEquiv.cast
        (M := fun S : Subgroup H ↦ NormalizerQuotient S) hQ).symm x) = _
  refine QuotientGroup.induction_on x ?_
  intro n
  rw [normalizerQuotientCast_symm_mk]
  rw [rightNormalizerQuotientEquiv_mk]
  change QuotientGroup.mk' _ _ =
    QuotientGroup.mk' _ (⟨h, hh⟩⁻¹ * n * ⟨h, hh⟩)
  apply congrArg
  apply Subtype.ext
  rw [rightNormalizerEquiv_coe, normalizerCast_coe]
  simp [mul_assoc]

/-- The quotient identity used when an element of `N_H(Q)` acts on
`N_H(Q)/Q`.  The structure is retained as an interface for downstream files,
and `canonicalRawNormalizerQuotientInput` constructs it without an additional
application hypothesis. -/
structure RawNormalizerQuotientInput where
  quotientConjugation :
    ∀ (W : CharacterWeight p K H) (h : H)
      (hh : h ∈ Subgroup.normalizer (W.subgroup : Set H))
      (x : NormalizerQuotient W.subgroup),
      rightNormalizerQuotientEquiv (MulAut.conj h⁻¹) W.subgroup
          ((MulEquiv.cast
            (M := fun S : Subgroup H ↦ NormalizerQuotient S)
            (normalizerConjugateSubgroupEq W h hh)).symm x) =
        (QuotientGroup.mk
            (⟨h, hh⟩ : Subgroup.normalizer (W.subgroup : Set H)))⁻¹ *
          x *
        QuotientGroup.mk
            (⟨h, hh⟩ : Subgroup.normalizer (W.subgroup : Set H))

/-- The quotient-conjugation input is canonical; no application-specific
group-theoretic hypothesis is needed. -/
theorem canonicalRawNormalizerQuotientInput :
    RawNormalizerQuotientInput (p := p) (K := K) (H := H) :=
  ⟨rightNormalizerQuotientEquiv_inner_apply⟩

/-- Ordinary irreducible character functions are constant on conjugacy
classes. -/
theorem ordinaryCharacter_conj
    {A : Type u} [Group A]
    (chi : OrdinaryIrreducibleCharacter.Irr K A) (a x : A) :
    chi (a * x * a⁻¹) = chi x := by
  rcases chi.2 with ⟨R⟩
  calc
    chi (a * x * a⁻¹) = R.representation.character (a * x * a⁻¹) :=
      (congrFun R.character_eq (a * x * a⁻¹)).symm
    _ = R.representation.character x := R.representation.char_conj x a
    _ = chi x := congrFun R.character_eq x

/-- Conjugation by an element of the subgroup normaliser fixes the actual
raw character-weight pair up to the equality built into `RawWeightClass`.
The character invariance is derived from the literal quotient action. -/
theorem normalizer_fixes_rawWeight
    (D : RawNormalizerQuotientInput (p := p) (K := K) (H := H))
    (h : H) (w : RawWeightClass (p := p) (K := K) (H := H))
    (hh : h ∈ Subgroup.normalizer (rawSubgroup w : Set H)) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    h • w = w := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  refine Quotient.inductionOn w ?_ hh
  intro W hnormal
  let hQ := normalizerConjugateSubgroupEq W h hnormal
  apply Quotient.sound
  refine ⟨hQ, ?_⟩
  apply OrdinaryIrreducibleCharacter.ext
  intro x
  change (CharacterWeight.castLocalCharacter hQ
      (OrdinaryIrreducibleCharacter.mapEquiv W.localCharacter
        (rightNormalizerQuotientEquiv
          (MulAut.conj h⁻¹) W.subgroup).symm)) x = W.localCharacter x
  rw [castLocalCharacter_apply]
  change W.localCharacter
      (rightNormalizerQuotientEquiv (MulAut.conj h⁻¹) W.subgroup
        ((MulEquiv.cast
          (M := fun S : Subgroup H ↦ NormalizerQuotient S) hQ).symm x)) =
    W.localCharacter x
  rw [D.quotientConjugation W h hnormal x]
  simpa only [inv_inv] using
    ordinaryCharacter_conj W.localCharacter
      (QuotientGroup.mk
        (⟨h, hnormal⟩ : Subgroup.normalizer (W.subgroup : Set H)))⁻¹ x

/-- The raw-weight data of Lemma 2.10 on the literal character-weight
isomorphism classes. -/
def actualRawWeightData
    (D : RawNormalizerQuotientInput (p := p) (K := K) (H := H))
    (phi : E →* MulAut H) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    RawWeightData phi
      (RawWeight := RawWeightClass (p := p) (K := K) (H := H)) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  exact
    { compatible := rightAutomorphismSemidirectCompatible
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
      subgroup := rawSubgroup
      subgroupConjugate := rawSubgroup_conjugate
      normalizerFixes := normalizer_fixes_rawWeight D }

/-- The restricted stabiliser of an actual raw character weight is exactly
the normaliser of its radical subgroup. -/
theorem actual_rawWeight_embeddedStabilizer_eq_normalizer
    (D : RawNormalizerQuotientInput (p := p) (K := K) (H := H))
    (phi : E →* MulAut H)
    (w : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let R := actualRawWeightData D phi
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      semidirectMulAction phi R.compatible
    hStabilizer (phi := phi) w =
      Subgroup.normalizer (rawSubgroup w : Set H) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  let R := actualRawWeightData D phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    semidirectMulAction phi R.compatible
  exact raw_weight_embedded_stabilizer_is_normalizer phi R w

/-- The quotient of the full actual raw-pair stabiliser by the embedded
normaliser is cyclic. -/
theorem actual_rawWeight_stabilizer_quotient_cyclic
    (D : RawNormalizerQuotientInput (p := p) (K := K) (H := H))
    (phi : E →* MulAut H)
    (w : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let R := actualRawWeightData D phi
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      semidirectMulAction phi R.compatible
    IsCyclic (semidirectStabilizer (phi := phi) w ⧸
      embeddedHStabilizer (phi := phi) w) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  let R := actualRawWeightData D phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    semidirectMulAction phi R.compatible
  exact raw_weight_stabilizer_quotient_cyclic phi R w

end ActualRawWeights

section ActualDefectZeroReductionInflation

variable {p : ℕ} {k K L : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group L] [Finite L]
variable (Q : Subgroup L) [Q.Normal]
variable (iotaQuotient : PrimeRegularRootEmbedding p k K (L ⧸ Q))
variable (iotaLocal : PrimeRegularRootEmbedding p k K L)
variable (theta : OrdinaryIrreducibleCharacter.Irr K (L ⧸ Q))

/-- Exact E1 inputs for a defect-zero ordinary character on a quotient.
The Brauer character is the actual function-valued reduction, and its
inflation is the literal pullback along the quotient map. -/
structure ActualDefectZeroReductionInflation where
  defectZero : IsDefectZeroOrdinaryCharacter p theta
  quotientBrauer : IBr iotaQuotient
  quotientReduction :
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      iotaQuotient theta quotientBrauer
  inflatedBrauerIrreducible :
    IsIrreducibleBrauerCharacter iotaLocal
      (ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.pullbackPrimeRegularClassFunction
        (QuotientGroup.mk' Q) quotientBrauer.1)

namespace ActualDefectZeroReductionInflation

/-- The literal inflated irreducible Brauer character. -/
def localBrauer
    (D : ActualDefectZeroReductionInflation Q iotaQuotient iotaLocal theta) :
    IBr iotaLocal :=
  ⟨ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.pullbackPrimeRegularClassFunction
      (QuotientGroup.mk' Q) D.quotientBrauer.1,
    D.inflatedBrauerIrreducible⟩

/-- Reduction and inflation commute on the actual function-valued
characters. -/
theorem localBrauer_isReductionOf_inflateOrdinary
    (D : ActualDefectZeroReductionInflation Q iotaQuotient iotaLocal theta) :
    ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
      iotaLocal
      (ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.inflateOrdinaryCharacter
        Q theta)
      D.localBrauer := by
  intro g
  exact D.quotientReduction
    (PrimeRegularElement.map (QuotientGroup.mk' Q) g)

end ActualDefectZeroReductionInflation

end ActualDefectZeroReductionInflation

/-- Naturality of Brauer reduction turns invariance of the actual ordinary
character into invariance of its actual Brauer reduction. -/
theorem brauerReduction_fixed_of_ordinary_fixed
    {p : ℕ} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Finite A]
    (iota : PrimeRegularRootEmbedding p k K A)
    (theta : OrdinaryIrreducibleCharacter.Irr K A)
    (theta0 : IBr iota)
    (reduction :
      ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
        iota theta theta0)
    (alpha : MulAut A)
    (thetaFixed : OrdinaryIrreducibleCharacter.twist K A theta alpha = theta) :
    IrreducibleBrauerCharacter.twist iota theta0 alpha = theta0 := by
  apply Subtype.ext
  apply PrimeRegularClassFunction.ext
  intro g
  have htheta := congrArg
    (fun chi : OrdinaryIrreducibleCharacter.Irr K A ↦ chi g.1) thetaFixed
  calc
    (IrreducibleBrauerCharacter.twist iota theta0 alpha).1 g =
        theta0.1 (PrimeRegularElement.map alpha.toMonoidHom g) := rfl
    _ = theta (alpha g.1) :=
      (reduction (PrimeRegularElement.map alpha.toMonoidHom g)).symm
    _ = theta g.1 := by simpa using htheta
    _ = theta0.1 g := reduction g

section ActualLocalExtensionApplication

variable {p : ℕ} {k K H E : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]

/-- Apply the local cyclic extension theorem to the literal Brauer reduction
of an actual defect-zero ordinary character.  The set of weights, its
stabiliser and its embedded normaliser are the concrete character-weight
objects constructed above.  Normality of the embedded weight subgroup and
invariance of the transported ordinary local character remain explicit
source inputs.  Lean derives invariance of its Brauer reduction, the cyclic
quotient and the extension. -/
theorem local_extension_actual
    (D : RawNormalizerQuotientInput (p := p) (K := K) (H := H))
    (phi : E →* MulAut H)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (w : RawWeightClass (p := p) (K := K) (H := H)) :
    let _ : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H))
        (MulAut.conj : H →* MulAut H)
    let _ : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
      rightAutomorphismAction
        (X := RawWeightClass (p := p) (K := K) (H := H)) phi
    let R := actualRawWeightData D phi
    let _ : MulAction (H ⋊[phi] E)
        (RawWeightClass (p := p) (K := K) (H := H)) :=
      semidirectMulAction phi R.compatible
    ∀ (Qbar : Subgroup (semidirectStabilizer (phi := phi) w))
      (qnormal : Qbar.Normal)
      (hQ : Qbar ≤ embeddedHStabilizer (phi := phi) w),
      letI : Qbar.Normal := qnormal
      ∀ (iota : PrimeRegularRootEmbedding p k K
          ((embeddedHStabilizer (phi := phi) w).map
            (QuotientGroup.mk' Qbar)))
        (theta : OrdinaryIrreducibleCharacter.Irr K
          ((embeddedHStabilizer (phi := phi) w).map
            (QuotientGroup.mk' Qbar)))
        (_thetaDefectZero : IsDefectZeroOrdinaryCharacter p theta)
        (theta0 : IBr iota)
        (thetaReduction :
          ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
            iota theta theta0),
        (∀ d : (semidirectStabilizer (phi := phi) w) ⧸ Qbar,
          OrdinaryIrreducibleCharacter.twist K _ theta
            (MulAut.conjNormal d) = theta) →
        ∃ W : FDRep k ((embeddedHStabilizer (phi := phi) w).map
              (QuotientGroup.mk' Qbar)),
          Representation.IsIrreducible W.ρ ∧
          theta0.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
          ModularRep.PaperProofs.SporadicCompleteCollapseLemma52ConcreteLocal.IsBrauerReduction
            iota theta theta0 ∧
          Nonempty (Representation.Extension
            ((embeddedHStabilizer (phi := phi) w).map
              (QuotientGroup.mk' Qbar)) W.ρ) := by
  dsimp only
  letI : MulAction H (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H))
      (MulAut.conj : H →* MulAut H)
  letI : MulAction E (RawWeightClass (p := p) (K := K) (H := H)) :=
    rightAutomorphismAction
      (X := RawWeightClass (p := p) (K := K) (H := H)) phi
  let R := actualRawWeightData D phi
  letI : MulAction (H ⋊[phi] E)
      (RawWeightClass (p := p) (K := K) (H := H)) :=
    semidirectMulAction phi R.compatible
  intro Qbar qnormal hQ
  letI : Qbar.Normal := qnormal
  intro iota theta _thetaDefectZero theta0 thetaReduction thetaFixed
  have hfixed : ∀ d : (semidirectStabilizer (phi := phi) w) ⧸ Qbar,
      IrreducibleBrauerCharacter.twist iota theta0
        (MulAut.conjNormal d) = theta0 := by
    intro d
    exact brauerReduction_fixed_of_ordinary_fixed
      iota theta theta0 thetaReduction (MulAut.conjNormal d) (thetaFixed d)
  rcases local_extension_relative phi R principle w Qbar qnormal hQ
      iota theta0 hfixed with ⟨W, hW, hcharacter, hextension⟩
  exact ⟨W, hW, hcharacter, thetaReduction, hextension⟩

end ActualLocalExtensionApplication

end ModularRep.PaperProofs.CyclicOuterLemma37Concrete


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
