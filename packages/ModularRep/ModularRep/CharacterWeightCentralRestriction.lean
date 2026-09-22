import ModularRep.WeightCharacterBridge

/-!
# Central restrictions do not depend on the weight representative

This module evaluates the actual ordinary local character on the image of a
central element in its normaliser quotient. These values, including the degree,
are invariant under ambient conjugation, so a lies-over formula for one raw
representative transfers to every representative of the same weight class.

It assumes no character-theory source, block-membership assertion,
central character formula, or character-weight correspondence.
-/

noncomputable section

namespace ModularRep.CharacterWeight

universe u

variable {p : ℕ} {K G : Type u}
variable [Field K] [CharZero K] [Group G] [Finite G]

/-- Restriction to the ambient centre after inflation from N_G(Q)/Q. -/
def centralRestriction (W : CharacterWeight p K G)
    (z : Subgroup.center G) : K :=
  W.localCharacter
    (QuotientGroup.mk'
      (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set G)))
      (⟨z.1, Subgroup.center_le_normalizer (W.subgroup : Set G) z.2⟩ :
        Subgroup.normalizer (W.subgroup : Set G)))

@[simp]
theorem centralRestriction_one (W : CharacterWeight p K G) :
    centralRestriction W 1 = W.localCharacter 1 := by
  unfold centralRestriction
  have h :
      (⟨((1 : Subgroup.center G) : G),
        Subgroup.center_le_normalizer (W.subgroup : Set G)
          (1 : Subgroup.center G).2⟩ :
        Subgroup.normalizer (W.subgroup : Set G)) = 1 := rfl
  rw [h, map_one]

/-- Automorphism transport preserves the value at each central element
which the automorphism fixes. There is no fixed-radical assumption. -/
theorem centralRestriction_rightTwist_of_fixed
    (W : CharacterWeight p K G) (alpha : MulAut G)
    (z : Subgroup.center G) (hz : alpha z.1 = z.1) :
    centralRestriction (W.rightTwist alpha) z = centralRestriction W z := by
  change W.localCharacter
      (rightNormalizerQuotientEquiv alpha W.subgroup
        (QuotientGroup.mk
          (⟨z.1, Subgroup.center_le_normalizer
            ((W.subgroup.comap alpha.toMonoidHom : Subgroup G) : Set G) z.2⟩ :
            Subgroup.normalizer
              ((W.subgroup.comap alpha.toMonoidHom : Subgroup G) : Set G)))) =
    W.localCharacter
      (QuotientGroup.mk
        (⟨z.1, Subgroup.center_le_normalizer (W.subgroup : Set G) z.2⟩ :
          Subgroup.normalizer (W.subgroup : Set G)))
  rw [rightNormalizerQuotientEquiv_mk]
  apply congrArg W.localCharacter
  apply congrArg (QuotientGroup.mk'
    (W.subgroup.subgroupOf (Subgroup.normalizer (W.subgroup : Set G))))
  apply Subtype.ext
  exact hz

theorem centralRestriction_inner
    (W : CharacterWeight p K G) (g : G) (z : Subgroup.center G) :
    centralRestriction (W.rightTwist (MulAut.conj g⁻¹)) z =
      centralRestriction W z := by
  apply centralRestriction_rightTwist_of_fixed
  change g⁻¹ * z.1 * (g⁻¹)⁻¹ = z.1
  rw [(Subgroup.mem_center_iff.mp z.2) g⁻¹]
  simp [mul_assoc]

/-- Descend the literal function through equality of raw character weights. -/
def isoCentralRestriction
    (w : IsoClass (p := p) (K := K) (G := G)) : Subgroup.center G → K :=
  Quotient.liftOn w centralRestriction (by
    intro W W' h
    exact congrArg centralRestriction (eq_of_isomorphic h))

theorem isoCentralRestriction_inner
    (w : IsoClass (p := p) (K := K) (G := G))
    (g : G) (z : Subgroup.center G) :
    isoCentralRestriction (g • w) z = isoCentralRestriction w z := by
  refine Quotient.inductionOn w ?_
  intro W
  change centralRestriction (W.rightTwist (MulAut.conj g⁻¹)) z =
    centralRestriction W z
  exact centralRestriction_inner W g z

/-- Descend the same function through ambient conjugation. -/
def classCentralRestriction
    (w : ConjugacyClass (p := p) (K := K) (G := G)) : Subgroup.center G → K :=
  Quotient.liftOn w isoCentralRestriction (by
    intro x y h
    rcases h with ⟨g, rfl⟩
    funext z
    exact isoCentralRestriction_inner y g z)

/-- The actual central values agree whenever the ambient weight classes do. -/
theorem centralRestriction_eq_of_class_eq
    (W W' : CharacterWeight p K G)
    (h : (Quotient.mk'' (Quotient.mk'' W : IsoClass) : ConjugacyClass) =
      Quotient.mk'' (Quotient.mk'' W' : IsoClass))
    (z : Subgroup.center G) :
    centralRestriction W z = centralRestriction W' z :=
  congrArg (fun w => classCentralRestriction w z) h

/-- Transfer a proved ordinary central restriction formula to another raw
representative. The degree is transferred by evaluating the same function at
the identity, not by selecting a new ordinary character. -/
theorem centralRestriction_formula_of_class_eq
    (W W' : CharacterWeight p K G)
    (h : (Quotient.mk'' (Quotient.mk'' W : IsoClass) : ConjugacyClass) =
      Quotient.mk'' (Quotient.mk'' W' : IsoClass))
    (nu : Subgroup.center G → K)
    (hW : ∀ z, centralRestriction W z = W.localCharacter 1 * nu z) :
    ∀ z, centralRestriction W' z = W'.localCharacter 1 * nu z := by
  have hdegree : W.localCharacter 1 = W'.localCharacter 1 := by
    simpa only [centralRestriction_one] using
      centralRestriction_eq_of_class_eq W W' h 1
  intro z
  calc
    centralRestriction W' z = centralRestriction W z :=
      (centralRestriction_eq_of_class_eq W W' h z).symm
    _ = W.localCharacter 1 * nu z := hW z
    _ = W'.localCharacter 1 * nu z := by rw [hdegree]

end ModularRep.CharacterWeight



/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
