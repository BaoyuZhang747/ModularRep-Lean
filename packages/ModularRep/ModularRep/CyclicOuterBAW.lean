import ModularRep.BrauerCharacterExtensionBridge
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic.Group
import Formalisation.SemidirectStabilizer

/-!
# Group-theoretic foundations for cyclic outer automorphisms

The elementary automorphism-centraliser calculation used in manuscript
Lemma 2.10.
-/

namespace ModularRep.ManuscriptVerification.CyclicOuterBAW

universe uR uG uV

variable {H : Type uG} [Group H]

/-- An automorphism of a centreless group that commutes with every inner
automorphism is the identity. -/
theorem mulAut_eq_one_of_commutes_inner
    (hcenter : Subgroup.center H = ⊥)
    (alpha : MulAut H)
    (hcomm : ∀ h : H,
      alpha * MulAut.conj h = MulAut.conj h * alpha) :
    alpha = 1 := by
  ext h
  have hconj : ∀ y : H,
      alpha h * y * (alpha h)⁻¹ = h * y * h⁻¹ := by
    intro y
    obtain ⟨x, rfl⟩ := alpha.surjective y
    have happ := DFunLike.congr_fun (hcomm h) x
    simpa [MulAut.conj_apply, map_mul] using happ
  have hz : h⁻¹ * alpha h ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := hconj y
    calc
      y * (h⁻¹ * alpha h) =
          h⁻¹ * (h * y * h⁻¹) * alpha h := by group
      _ = h⁻¹ * (alpha h * y * (alpha h)⁻¹) * alpha h := by
        rw [hy]
      _ = (h⁻¹ * alpha h) * y := by group
  have hzOne : h⁻¹ * alpha h = 1 := by
    rw [hcenter] at hz
    simpa using hz
  have halpha : alpha h = h := by
    calc
      alpha h = h * (h⁻¹ * alpha h) := by group
      _ = h := by rw [hzOne, mul_one]
  change alpha h = h
  exact halpha

/-- The canonical homomorphism from a group to its inner automorphism group. -/
def innerAutomorphismHom : H →* MulAut H where
  toFun := MulAut.conj
  map_one' := by
    ext x
    simp
  map_mul' a b := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]

/-- The canonical map from `H ⋊ E` to `Aut(H)`, sending `(h,e)` to the
product of conjugation by `h` and the specified automorphism `phi(e)`.  A
bijectivity hypothesis on this particular map expresses the automorphism
decomposition needed in manuscript Lemma 2.10. -/
def semidirectToMulAut {E : Type uG} [Group E]
    (phi : E →* MulAut H) : H ⋊[phi] E →* MulAut H :=
  SemidirectProduct.lift innerAutomorphismHom phi (by
    intro e
    ext h x
    simp [innerAutomorphismHom, MulAut.conj_apply, map_mul, map_inv])

@[simp]
theorem semidirectToMulAut_inl {E : Type uG} [Group E]
    (phi : E →* MulAut H) (h : H) :
    semidirectToMulAut phi (SemidirectProduct.inl h) = MulAut.conj h := by
  simp [semidirectToMulAut, innerAutomorphismHom]

@[simp]
theorem semidirectToMulAut_inr {E : Type uG} [Group E]
    (phi : E →* MulAut H) (e : E) :
    semidirectToMulAut phi (SemidirectProduct.inr e) = phi e := by
  simp [semidirectToMulAut]

/-- The centreless centralizer calculation stated using the canonical
semidirect-product map. -/
theorem mulAut_eq_one_of_commutes_semidirect_inner
    {E : Type uG} [Group E]
    (hcenter : Subgroup.center H = ⊥)
    (phi : E →* MulAut H) (alpha : MulAut H)
    (hcomm : ∀ h : H,
      alpha * semidirectToMulAut phi (SemidirectProduct.inl h) =
        semidirectToMulAut phi (SemidirectProduct.inl h) * alpha) :
    alpha = 1 := by
  apply mulAut_eq_one_of_commutes_inner hcenter alpha
  intro h
  simpa using hcomm h

/-- A pair whose subgroup component transforms by conjugation has stabilizer
equal to the subgroup normalizer once elements of that normalizer are known
to fix the second component.  In the manuscript the second assertion comes
from inner invariance of the character of `N_H(Q)/Q`; it is deliberately an
explicit hypothesis here. -/
theorem stabilizer_eq_normalizer_of_subgroup_equivariant
    {W : Type*} [MulAction H W]
    (subgroup : W → Subgroup H)
    (hsubgroup : ∀ (h : H) (w : W),
      subgroup (h • w) = (subgroup w).map (MulAut.conj h))
    (hnormalizerFixed : ∀ (h : H) (w : W),
      h ∈ Subgroup.normalizer (subgroup w : Set H) → h • w = w)
    (w : W) :
    MulAction.stabilizer H w =
      Subgroup.normalizer (subgroup w : Set H) := by
  ext h
  constructor
  · intro hfix
    have hw : h • w = w := hfix
    have hmap := hsubgroup h w
    rw [hw] at hmap
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hmap.symm
  · intro hnormalizer
    exact hnormalizerFixed h w hnormalizer

section StabilizerProjection

variable {E X : Type*} [Group E]
variable {phi : E →* MulAut H}
variable [MulAction (H ⋊[phi] E) X]

/-- The action of `H` obtained by restricting a semidirect product action
along the canonical inclusion `H → H ⋊ E`. -/
abbrev restrictedHAction : MulAction H X :=
  MulAction.compHom X (SemidirectProduct.inl : H →* H ⋊[phi] E)

/-- The stabilizer of `x` for the restricted `H` action. -/
def hStabilizer (x : X) : Subgroup H :=
  @MulAction.stabilizer H X _
    (restrictedHAction (H := H) (E := E) (phi := phi)) x

/-- The stabilizer of `x` for the whole semidirect product action. -/
def semidirectStabilizer (x : X) : Subgroup (H ⋊[phi] E) :=
  MulAction.stabilizer (H ⋊[phi] E) x

/-- Restriction of the canonical projection `H ⋊ E → E` to the stabilizer
of `x`. -/
def stabilizerRightHom (x : X) :
    semidirectStabilizer (phi := phi) x →* E :=
  SemidirectProduct.rightHom.comp
    (semidirectStabilizer (phi := phi) x).subtype

/-- The embedded restricted-`H` stabilizer, regarded as a subgroup of the
semidirect product stabilizer. -/
def inlStabilizerHom (x : X) :
    hStabilizer (phi := phi) x →* semidirectStabilizer (phi := phi) x where
  toFun h := ⟨SemidirectProduct.inl h.1, by
    change (SemidirectProduct.inl h.1 : H ⋊[phi] E) • x = x
    exact h.2⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

/-- The actual embedded copy of the restricted-`H` stabilizer. -/
def embeddedHStabilizer (x : X) :
    Subgroup (semidirectStabilizer (phi := phi) x) :=
  (inlStabilizerHom (phi := phi) x).range

theorem inlStabilizerHom_injective (x : X) :
    Function.Injective (inlStabilizerHom (phi := phi) x) := by
  intro a b hab
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (φ := phi)
    (congrArg (fun g : semidirectStabilizer (phi := phi) x ↦ g.1) hab)

/-- The restricted `H` stabilizer is all of `H` whenever every element of
the canonical copy of `H` fixes `x`. -/
theorem hStabilizer_eq_top_of_left_fixed (x : X)
    (hfixed : ∀ h : H, (SemidirectProduct.inl h : H ⋊[phi] E) • x = x) :
    hStabilizer (phi := phi) x = ⊤ := by
  apply top_unique
  intro h _
  exact hfixed h

theorem embeddedHStabilizer_eq_ker (x : X) :
    embeddedHStabilizer (phi := phi) x =
      (stabilizerRightHom (phi := phi) x).ker := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    simp [stabilizerRightHom, inlStabilizerHom]
  · intro hg
    have hright : g.1.right = 1 := by
      simpa [stabilizerRightHom, MonoidHom.mem_ker] using hg
    let h : H := g.1.left
    have hinl : (SemidirectProduct.inl h : H ⋊[phi] E) = g.1 := by
      apply SemidirectProduct.ext
      · rfl
      · simpa [h] using hright.symm
    have hh : h ∈ hStabilizer (phi := phi) x := by
      change (SemidirectProduct.inl h : H ⋊[phi] E) • x = x
      rw [hinl]
      exact g.2
    refine ⟨⟨h, hh⟩, ?_⟩
    apply Subtype.ext
    exact hinl

instance embeddedHStabilizer_normal (x : X) :
    (embeddedHStabilizer (phi := phi) x).Normal := by
  rw [embeddedHStabilizer_eq_ker]
  infer_instance

/-- First-isomorphism-theorem identification of the stabilizer quotient with
the range of the restricted right projection. -/
noncomputable def stabilizerQuotientEquivProjectionRange (x : X) :
    (semidirectStabilizer (phi := phi) x ⧸
      embeddedHStabilizer (phi := phi) x) ≃*
      (stabilizerRightHom (phi := phi) x).range :=
  (QuotientGroup.quotientMulEquivOfEq
    (embeddedHStabilizer_eq_ker (phi := phi) x)).trans
    (QuotientGroup.quotientKerEquivRange
      (stabilizerRightHom (phi := phi) x))

/-- The quotient of the full stabilizer by the embedded `H` stabilizer
embeds in the outer factor `E`. -/
noncomputable def stabilizerQuotientEmbedding (x : X) :
    (semidirectStabilizer (phi := phi) x ⧸
      embeddedHStabilizer (phi := phi) x) →* E :=
  (stabilizerRightHom (phi := phi) x).range.subtype.comp
    (stabilizerQuotientEquivProjectionRange (phi := phi) x).toMonoidHom

theorem stabilizerQuotientEmbedding_injective (x : X) :
    Function.Injective (stabilizerQuotientEmbedding (phi := phi) x) :=
  Subtype.val_injective.comp
    (stabilizerQuotientEquivProjectionRange (phi := phi) x).injective

/-- The stabilizer quotient by its embedded `H` stabilizer is cyclic whenever
the outer factor `E` is cyclic. -/
theorem isCyclic_stabilizer_quotient [IsCyclic E] (x : X) :
    IsCyclic (semidirectStabilizer (phi := phi) x ⧸
      embeddedHStabilizer (phi := phi) x) := by
  exact isCyclic_of_injective
    (stabilizerQuotientEmbedding (phi := phi) x)
    (stabilizerQuotientEmbedding_injective (phi := phi) x)

end StabilizerProjection

section CompatibleActions

variable {E X : Type*} [Group E] [MulAction H X] [MulAction E X]
variable {phi : E →* MulAut H} [IsCyclic E]

/-- Specialisation of `isCyclic_stabilizer_quotient` to separately supplied
compatible `H` and `E` actions. -/
theorem isCyclic_stabilizer_quotient_of_compatible
    (hcompat : Formalisation.SemidirectActionCompatible (X := X) phi)
    (x : X) :
    letI : MulAction (H ⋊[phi] E) X :=
      Formalisation.semidirectMulAction phi hcompat
    IsCyclic (semidirectStabilizer (phi := phi) x ⧸
      embeddedHStabilizer (phi := phi) x) := by
  let _ : MulAction (H ⋊[phi] E) X :=
    Formalisation.semidirectMulAction phi hcompat
  exact isCyclic_stabilizer_quotient (phi := phi) x

end CompatibleActions

section QuotientTower

variable {D C : Type*} [Group D] [Group C] [IsCyclic C]

/-- If `Q ≤ N ◁ D` and `D/N` embeds in a cyclic group, then the top quotient
in the tower `Q ≤ N ≤ D` is cyclic. -/
theorem isCyclic_quotient_tower_of_embedding
    (Q N : Subgroup D) [Q.Normal] [N.Normal] (hQN : Q ≤ N)
    (embedding : (D ⧸ N) →* C) (hinjective : Function.Injective embedding) :
    IsCyclic ((D ⧸ Q) ⧸ N.map (QuotientGroup.mk' Q)) := by
  let _ : IsCyclic (D ⧸ N) := isCyclic_of_injective embedding hinjective
  exact isCyclic_of_injective
    (QuotientGroup.quotientQuotientEquivQuotient Q N hQN).toMonoidHom
    (QuotientGroup.quotientQuotientEquivQuotient Q N hQN).injective

end QuotientTower

section RepresentationExtensions

variable {k : Type uR} {E X : Type uG} {V : Type uV}
variable [Field k] [Group E]
variable [Finite H] [Finite E] [IsCyclic E]
variable {phi : E →* MulAut H} [MulAction (H ⋊[phi] E) X]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The supplied Brauer-character extension principle applies to a
representation of the embedded `H` stabilizer because the quotient of the
full stabilizer embeds in the cyclic outer factor.  Identifying the
representation and its trace with a manuscript Brauer character remains a
separate character-theoretic bridge. -/
theorem exists_extension_to_semidirect_stabilizer
    (principle :
      Representation.CyclicExtensionPrinciple.{uR, uG, uV} k)
    (x : X)
    (rho : Representation k (embeddedHStabilizer (phi := phi) x) V)
    (hirr : Representation.IsIrreducible rho)
    (hinvariant : Representation.ConjugationInvariant
      (embeddedHStabilizer (phi := phi) x) rho) :
    Nonempty (Representation.Extension
      (embeddedHStabilizer (phi := phi) x) rho) := by
  let _ : Finite (H ⋊[phi] E) :=
    Finite.of_injective
      (fun g : H ⋊[phi] E => (g.left, g.right)) (by
        intro a b hab
        exact SemidirectProduct.ext
          (congrArg Prod.fst hab) (congrArg Prod.snd hab))
  let _ : Finite (semidirectStabilizer (phi := phi) x) := Subtype.finite
  exact Representation.exists_extension_of_quotient_embedding_cyclic
    principle rho hirr
    (stabilizerQuotientEmbedding (phi := phi) x)
    (stabilizerQuotientEmbedding_injective (phi := phi) x)
    hinvariant

variable {D C : Type uG} [Group D] [Finite D] [Group C] [IsCyclic C]

/-- The supplied Brauer-character extension principle also applies in the
local quotient tower.  If `Q ≤ N ◁ D` and `D/N` embeds in a cyclic group,
an invariant irreducible representation of `N/Q` extends to `D/Q`. -/
theorem exists_extension_over_quotient_tower
    (principle :
      Representation.CyclicExtensionPrinciple.{uR, uG, uV} k)
    (Q N : Subgroup D) [Q.Normal] [N.Normal] (hQN : Q ≤ N)
    (embedding : (D ⧸ N) →* C) (hinjective : Function.Injective embedding)
    (rho : Representation k (N.map (QuotientGroup.mk' Q)) V)
    (hirr : Representation.IsIrreducible rho)
    (hinvariant : Representation.ConjugationInvariant
      (N.map (QuotientGroup.mk' Q)) rho) :
    Nonempty (Representation.Extension
      (N.map (QuotientGroup.mk' Q)) rho) := by
  apply Representation.exists_extension_of_cyclic_quotient
    principle rho hirr
  · exact isCyclic_quotient_tower_of_embedding Q N hQN
      embedding hinjective
  · exact hinvariant

end RepresentationExtensions

section FunctionValuedBrauerExtensions

universe u v

variable {p : ℕ} {k H E X : Type u} {K : Type v}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]
variable {phi : E →* MulAut H} [MulAction (H ⋊[phi] E) X]

private noncomputable instance finiteSemidirectProduct :
    Finite (H ⋊[phi] E) :=
  Finite.of_injective
    (fun g : H ⋊[phi] E ↦ (g.left, g.right)) (by
      intro a b hab
      exact SemidirectProduct.ext
        (congrArg Prod.fst hab) (congrArg Prod.snd hab))

/-- Character-level form of the global extension step in manuscript
Lemma 2.10.  For an actual function-valued irreducible Brauer character of
the embedded stabiliser, fixedness under its ambient stabiliser gives an
affording representation which extends to that stabiliser.  The only
external theorem parameter is Navarro's cyclic-extension principle. -/
theorem exists_extension_to_semidirect_stabilizer_of_ibr_fixed
    (principle :
      Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (x : X)
    (iota : PrimeRegularRootEmbedding p k K
      (embeddedHStabilizer (phi := phi) x))
    (varphi : IBr iota)
    (hfixed : ∀ d : semidirectStabilizer (phi := phi) x,
      IrreducibleBrauerCharacter.twist iota varphi
          (MulAut.conjNormal d) = varphi) :
    ∃ W : FDRep k (embeddedHStabilizer (phi := phi) x),
      Representation.IsIrreducible W.ρ ∧
      varphi.1 =
        Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
      Nonempty (Representation.Extension
        (embeddedHStabilizer (phi := phi) x) W.ρ) := by
  apply Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
    principle iota varphi
  · exact isCyclic_stabilizer_quotient (phi := phi) x
  · exact hfixed

end FunctionValuedBrauerExtensions

end ModularRep.ManuscriptVerification.CyclicOuterBAW


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
