import ModularRep.WeightCharacterBridge

/-!
# Radical-subgroup projection on literal character weights

A literal character weight contains a radical subgroup and a defect-zero
local ordinary character.  This file constructs the canonical map which
forgets the local character and retains the ambient conjugacy class of the
radical subgroup.

The construction descends through both honest quotients used by
`CharacterWeight.ConjugacyClass`: first through equality of the transported
local character and then through ambient conjugation.  Automorphisms act on
radical subgroups by inverse image, matching the manuscript's right-action
convention, and this action descends to radical-subgroup conjugacy classes.
Lean proves that the radical projection is equivariant for the canonical
opposite-automorphism actions.

When an application supplies the object-level fact that the trivial subgroup
is `p`-radical, this module also constructs its literal conjugacy class and
proves that every automorphism fixes it.

There are no block assignments, character--weight bijections, finite
enumerations, BAW/iBAW predicates, or representation theoretic source fields
in this module.  Its declarations are group-theoretic constructions and
quotient deductions.
-/

noncomputable section

namespace ModularRep.CharacterWeight

universe u

variable {p : Nat} {G : Type u} [Group G]

/-! ## Literal radical subgroups and their actions -/

/-- Literal radical `p`-subgroups of the ambient group. -/
abbrev RadicalSubgroup :=
  {Q : Subgroup G // IsRadicalSubgroup p Q}

namespace RadicalSubgroup

/-- Manuscript right transport of a literal radical subgroup by an
automorphism: `Q ^ alpha = alpha⁻¹(Q)`. -/
def rightTwist (Q : RadicalSubgroup (p := p) (G := G))
    (alpha : MulAut G) : RadicalSubgroup (p := p) (G := G) :=
  ⟨Q.1.comap alpha.toMonoidHom, Q.2.comap_mulAut alpha⟩

@[simp]
theorem rightTwist_one (Q : RadicalSubgroup (p := p) (G := G)) :
    Q.rightTwist (1 : MulAut G) = Q := by
  apply Subtype.ext
  ext x
  rfl

/-- Successive right transports compose in manuscript order. -/
theorem rightTwist_mul (Q : RadicalSubgroup (p := p) (G := G))
    (alpha beta : MulAut G) :
    (Q.rightTwist alpha).rightTwist beta =
      Q.rightTwist (alpha * beta) := by
  apply Subtype.ext
  ext x
  rfl

/-- The opposite automorphism group acts canonically on literal radical
subgroups. -/
instance automorphismAction :
    MulAction (MulAut G)ᵐᵒᵖ (RadicalSubgroup (p := p) (G := G)) where
  smul alpha Q := Q.rightTwist alpha.unop
  one_smul Q := Q.rightTwist_one
  mul_smul alpha beta Q :=
    (Q.rightTwist_mul beta.unop alpha.unop).symm

/-- Ambient conjugation on radical subgroups, in the convention
`g • Q = gQg⁻¹`. -/
instance conjugationAction :
    MulAction G (RadicalSubgroup (p := p) (G := G)) where
  smul g Q := Q.rightTwist (MulAut.conj g⁻¹)
  one_smul Q := by
    change Q.rightTwist (MulAut.conj (1 : G)⁻¹) = Q
    simp
  mul_smul g h Q := by
    change Q.rightTwist (MulAut.conj (g * h)⁻¹) =
      (Q.rightTwist (MulAut.conj h⁻¹)).rightTwist (MulAut.conj g⁻¹)
    simpa using
      (Q.rightTwist_mul (MulAut.conj h⁻¹) (MulAut.conj g⁻¹)).symm

@[simp]
theorem smul_eq_rightTwist_conj (g : G)
    (Q : RadicalSubgroup (p := p) (G := G)) :
    g • Q = Q.rightTwist (MulAut.conj g⁻¹) :=
  rfl

/-- Automorphism transport carries conjugate subgroups to conjugate
subgroups.  This is the exact well-definedness identity needed for the
automorphism action on conjugacy classes. -/
theorem rightTwist_conjugation (alpha : MulAut G) (g : G)
    (Q : RadicalSubgroup (p := p) (G := G)) :
    (g • Q).rightTwist alpha =
      alpha.symm g • Q.rightTwist alpha := by
  apply Subtype.ext
  ext x
  rw [smul_eq_rightTwist_conj, smul_eq_rightTwist_conj]
  simp only [rightTwist, Subgroup.mem_comap]
  change (MulAut.conj g⁻¹) (alpha x) ∈ Q.1 ↔
    alpha ((MulAut.conj (alpha.symm g)⁻¹) x) ∈ Q.1
  simp only [MulAut.conj_apply]
  simp

end RadicalSubgroup

/-! ## Conjugacy classes of radical subgroups -/

/-- Ambient conjugacy classes of literal radical subgroups. -/
abbrev RadicalConjugacyClass :=
  MulAction.orbitRel.Quotient G (RadicalSubgroup (p := p) (G := G))

namespace RadicalConjugacyClass

/-- Right automorphism transport descends to radical-subgroup conjugacy
classes. -/
def rightTwist (alpha : MulAut G) :
    RadicalConjugacyClass (p := p) (G := G) →
      RadicalConjugacyClass (p := p) (G := G) :=
  Quotient.map (RadicalSubgroup.rightTwist (p := p) (G := G) · alpha) (by
    intro Q R h
    rcases h with ⟨g, rfl⟩
    exact ⟨alpha.symm g,
      (RadicalSubgroup.rightTwist_conjugation alpha g R).symm⟩)

@[simp]
theorem rightTwist_one
    (q : RadicalConjugacyClass (p := p) (G := G)) :
    rightTwist (p := p) (G := G) (1 : MulAut G) q = q := by
  refine Quotient.inductionOn q ?_
  intro Q
  exact congrArg
    (fun R : RadicalSubgroup (p := p) (G := G) =>
      (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := G)))
    Q.rightTwist_one

/-- Successive transport on radical conjugacy classes composes in manuscript
order. -/
theorem rightTwist_mul
    (q : RadicalConjugacyClass (p := p) (G := G))
    (alpha beta : MulAut G) :
    rightTwist (p := p) (G := G) beta
        (rightTwist (p := p) (G := G) alpha q) =
      rightTwist (p := p) (G := G) (alpha * beta) q := by
  refine Quotient.inductionOn q ?_
  intro Q
  exact congrArg
    (fun R : RadicalSubgroup (p := p) (G := G) =>
      (Quotient.mk'' R : RadicalConjugacyClass (p := p) (G := G)))
    (Q.rightTwist_mul alpha beta)

/-- Canonical opposite-automorphism action on radical-subgroup conjugacy
classes. -/
instance automorphismAction :
    MulAction (MulAut G)ᵐᵒᵖ
      (RadicalConjugacyClass (p := p) (G := G)) where
  smul alpha q := rightTwist (p := p) (G := G) alpha.unop q
  one_smul q := rightTwist_one q
  mul_smul alpha beta q :=
    (rightTwist_mul q beta.unop alpha.unop).symm

/-- The literal conjugacy class of the trivial subgroup, when the ambient
group has trivial `p`-core (equivalently, when the trivial subgroup is
`p`-radical). -/
def trivialClass
    (htrivial : IsRadicalSubgroup p (⊥ : Subgroup G)) :
    RadicalConjugacyClass (p := p) (G := G) :=
  Quotient.mk''
    (⟨⊥, htrivial⟩ : RadicalSubgroup (p := p) (G := G))

/-- Canonical automorphism transport fixes the literal class of the trivial
subgroup. -/
@[simp]
theorem smul_trivialClass
    (alpha : (MulAut G)ᵐᵒᵖ)
    (htrivial : IsRadicalSubgroup p (⊥ : Subgroup G)) :
    alpha • trivialClass (p := p) (G := G) htrivial =
      trivialClass (p := p) (G := G) htrivial := by
  change Quotient.mk''
      (RadicalSubgroup.rightTwist
        (⟨⊥, htrivial⟩ : RadicalSubgroup (p := p) (G := G))
        alpha.unop) =
    Quotient.mk''
      (⟨⊥, htrivial⟩ : RadicalSubgroup (p := p) (G := G))
  congr 1
  apply Subtype.ext
  ext x
  simp [RadicalSubgroup.rightTwist]

end RadicalConjugacyClass

/-! ## Projection from literal character weights -/

variable {K : Type u} [Field K] [CharZero K] [Finite G]

/-- Forget the local character of a character-weight isomorphism class.
Weight isomorphism includes literal equality of the radical subgroup, so this
first quotient descent is canonical. -/
def radicalSubgroupOfIsoClass :
    IsoClass (p := p) (K := K) (G := G) →
      RadicalSubgroup (p := p) (G := G) :=
  Quotient.lift (fun W => ⟨W.subgroup, W.radical⟩) (by
    intro W W' h
    apply Subtype.ext
    exact h.choose)

@[simp]
theorem radicalSubgroupOfIsoClass_mk (W : CharacterWeight p K G) :
    radicalSubgroupOfIsoClass (Quotient.mk'' W) =
      (⟨W.subgroup, W.radical⟩ : RadicalSubgroup (p := p) (G := G)) :=
  rfl

/-- Forgetting the local character commutes with ambient conjugation. -/
theorem radicalSubgroupOfIsoClass_conjugation
    (g : G) (W : IsoClass (p := p) (K := K) (G := G)) :
    radicalSubgroupOfIsoClass (g • W) =
      g • radicalSubgroupOfIsoClass W := by
  refine Quotient.inductionOn W ?_
  intro W
  rfl

/-- The radical-class projection from the literal character-weight
conjugacy class quotient. -/
def radicalClass :
    ConjugacyClass (p := p) (K := K) (G := G) →
      RadicalConjugacyClass (p := p) (G := G) :=
  Quotient.map radicalSubgroupOfIsoClass (by
    intro W W' h
    rcases h with ⟨g, rfl⟩
    exact ⟨g, (radicalSubgroupOfIsoClass_conjugation g W').symm⟩)

@[simp]
theorem radicalClass_mkIsoClass
    (W : IsoClass (p := p) (K := K) (G := G)) :
    radicalClass (Quotient.mk'' W) =
      (Quotient.mk'' (radicalSubgroupOfIsoClass W) :
        RadicalConjugacyClass (p := p) (G := G)) :=
  rfl

@[simp]
theorem radicalClass_mk (W : CharacterWeight p K G) :
    radicalClass (Quotient.mk'' (Quotient.mk'' W)) =
      (Quotient.mk''
        (⟨W.subgroup, W.radical⟩ : RadicalSubgroup (p := p) (G := G)) :
          RadicalConjugacyClass (p := p) (G := G)) :=
  rfl

/-- Forgetting the local character commutes with right automorphism transport
on weight isomorphism classes. -/
theorem radicalSubgroupOfIsoClass_rightTwist
    (alpha : MulAut G)
    (W : IsoClass (p := p) (K := K) (G := G)) :
    radicalSubgroupOfIsoClass
        (rightTwistIsoClass (p := p) (K := K) (G := G) alpha W) =
      (radicalSubgroupOfIsoClass W).rightTwist alpha := by
  refine Quotient.inductionOn W ?_
  intro W
  rfl

/-- The two quotient descents commute with right automorphism transport. -/
theorem radicalClass_rightTwist
    (alpha : MulAut G)
    (w : ConjugacyClass (p := p) (K := K) (G := G)) :
    radicalClass
        (rightTwistConjugacyClass
          (p := p) (K := K) (G := G) alpha w) =
      RadicalConjugacyClass.rightTwist alpha (radicalClass w) := by
  refine Quotient.inductionOn w ?_
  intro W
  exact congrArg
    (fun Q : RadicalSubgroup (p := p) (G := G) =>
      (Quotient.mk'' Q : RadicalConjugacyClass (p := p) (G := G)))
    (radicalSubgroupOfIsoClass_rightTwist alpha W)

/-- The canonical radical-class projection is equivariant for every
automorphism of the ambient group. -/
theorem radicalClass_equivariant
    (alpha : (MulAut G)ᵐᵒᵖ)
    (w : ConjugacyClass (p := p) (K := K) (G := G)) :
    radicalClass (alpha • w) = alpha • radicalClass w :=
  radicalClass_rightTwist alpha.unop w

end ModularRep.CharacterWeight


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
