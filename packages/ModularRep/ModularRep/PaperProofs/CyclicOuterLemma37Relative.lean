import ModularRep.CyclicOuterBAW

/-!
# Source-shaped relative form of manuscript Lemma 2.10

Feng--Li--Zhang, *Advances in Mathematics* 408 (2022), Theorem 3.18,
pp. 17--18, recalls the full Brough--Späth criterion.  It is not a theorem
whose sole hypotheses are cyclicity of the outer automorphism group and an
equivariant bijection.  In particular, its clauses (i)(a)--(d),
(ii), (iii)(a)--(c), and (iv)(a)--(b) must be supplied or proved separately.

Navarro, *Characters and Blocks of Finite Groups*, Theorem (3.18),
pp. 61--62, says that a defect-zero block contains one ordinary character
`chi` and that its irreducible Brauer characters consist of `chi^0`.
Navarro, Theorem (8.12), p. 163, says that an invariant irreducible Brauer
character of a normal subgroup extends across a cyclic quotient.

This file proves the deductions made in Lemma 2.10 between those published
inputs.  Concrete identifications of manuscript Brauer characters and
defect-zero reductions with the function-valued `IBr` objects below remain
explicit inputs.  The final application of Feng--Li--Zhang Theorem 3.18 also
remains explicit: no premise below assumes that the block is BAW-good or that
an iBAW bijection exists.
-/

noncomputable section

namespace ModularRep.PaperProofs.CyclicOuterLemma37Relative

open Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW

universe u v

variable {H E Brauer Weight RawWeight : Type u}
variable [Group H] [Finite H] [Group E] [Finite E] [IsCyclic E]
variable (phi : E →* MulAut H)

/-- The action and bijection data which occur before the extension clauses
of the Brough--Späth criterion.  The actions of `H` are trivial because the
manuscript sets are Brauer characters and weights modulo `H`-conjugacy.
Compatibility is stated separately rather than hidden in a supplied action
of `H ⋊ E`. -/
structure ActionData
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight] where
  brauerCompatible : SemidirectActionCompatible (X := Brauer) phi
  weightCompatible : SemidirectActionCompatible (X := Weight) phi
  omega : Brauer ≃ Weight
  omegaE : ∀ (e : E) (x : Brauer), omega (e • x) = e • omega x
  brauerInnerTrivial : ∀ (h : H) (x : Brauer), h • x = x
  weightInnerTrivial : ∀ (h : H) (y : Weight), h • y = y

/-- An outer-equivariant bijection of conjugacy classes is equivariant for
the action of the full semidirect product.  This is clause (ii) of the
criterion in the self-cover specialisation, apart from the concrete
identification of the two sets with the required block fibres. -/
theorem omega_semidirect_equivariant
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight]
    (A : ActionData phi (Brauer := Brauer) (Weight := Weight)) :
    letI : MulAction (H ⋊[phi] E) Brauer :=
      semidirectMulAction phi A.brauerCompatible
    letI : MulAction (H ⋊[phi] E) Weight :=
      semidirectMulAction phi A.weightCompatible
    ∀ g : H ⋊[phi] E, ∀ x : Brauer, A.omega (g • x) = g • A.omega x := by
  let _ : MulAction (H ⋊[phi] E) Brauer :=
    semidirectMulAction phi A.brauerCompatible
  let _ : MulAction (H ⋊[phi] E) Weight :=
    semidirectMulAction phi A.weightCompatible
  exact equivariant_equiv_semidirect_of_left_trivial
    phi A.brauerCompatible A.weightCompatible A.omega A.omegaE
      A.brauerInnerTrivial A.weightInnerTrivial

/-- Exact global stabiliser description.  It proves, rather than assumes,
that the stabiliser is the inverse image of the outer stabiliser. -/
theorem global_stabilizer_eq_outer_comap
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight]
    (A : ActionData phi (Brauer := Brauer) (Weight := Weight))
    (x : Brauer) :
    letI : MulAction (H ⋊[phi] E) Brauer :=
      semidirectMulAction phi A.brauerCompatible
    MulAction.stabilizer (H ⋊[phi] E) x =
      (MulAction.stabilizer E x).comap SemidirectProduct.rightHom := by
  let _ : MulAction (H ⋊[phi] E) Brauer :=
    semidirectMulAction phi A.brauerCompatible
  exact semidirect_stabilizer_eq_comap_right_stabilizer_of_left_trivial
    phi A.brauerCompatible A.brauerInnerTrivial x

/-- Elementwise form of the global stabiliser factorisation in clause
(iv)(a). -/
theorem global_stabilizer_factorization
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight]
    (A : ActionData phi (Brauer := Brauer) (Weight := Weight))
    (x : Brauer) :
    letI : MulAction (H ⋊[phi] E) Brauer :=
      semidirectMulAction phi A.brauerCompatible
    ∀ g : H ⋊[phi] E,
      g ∈ MulAction.stabilizer (H ⋊[phi] E) x ↔
        ∃ h : H, ∃ e : E,
          e ∈ MulAction.stabilizer E x ∧
            g = SemidirectProduct.inl h * SemidirectProduct.inr e := by
  let _ : MulAction (H ⋊[phi] E) Brauer :=
    semidirectMulAction phi A.brauerCompatible
  exact mem_semidirect_stabilizer_iff_exists_right_factorization
    phi A.brauerCompatible A.brauerInnerTrivial x

/-- The restricted `H`-stabiliser of a Brauer-character class is all of
`H`.  Together with the concrete character identification, this is what
identifies the embedded subgroup used below with the copy of `H` in the
manuscript stabiliser. -/
theorem global_hStabilizer_eq_top
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight]
    (A : ActionData phi (Brauer := Brauer) (Weight := Weight))
    (x : Brauer) :
    letI : MulAction (H ⋊[phi] E) Brauer :=
      semidirectMulAction phi A.brauerCompatible
    hStabilizer (phi := phi) x = ⊤ := by
  let _ : MulAction (H ⋊[phi] E) Brauer :=
    semidirectMulAction phi A.brauerCompatible
  apply hStabilizer_eq_top_of_left_fixed
  intro h
  rw [semidirect_inl_smul phi A.brauerCompatible]
  exact A.brauerInnerTrivial h x

/-- The quotient of the global stabiliser by its embedded `H`-stabiliser
is cyclic.  The embedding in `E` is constructed by the right projection. -/
theorem global_stabilizer_quotient_cyclic
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight]
    (A : ActionData phi (Brauer := Brauer) (Weight := Weight))
    (x : Brauer) :
    letI : MulAction (H ⋊[phi] E) Brauer :=
      semidirectMulAction phi A.brauerCompatible
    IsCyclic (semidirectStabilizer (phi := phi) x ⧸
      embeddedHStabilizer (phi := phi) x) := by
  let _ : MulAction (H ⋊[phi] E) Brauer :=
    semidirectMulAction phi A.brauerCompatible
  exact isCyclic_stabilizer_quotient (phi := phi) x

section GlobalExtension

variable {p : ℕ} {k : Type u} {K : Type v}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Global extension in clause (iv)(a), relative only to Navarro (8.12)
and the concrete identification of the manuscript character with `varphi`.
The fixedness premise is the source-shaped character-action compatibility;
the cyclicity of the quotient and the extension are derived. -/
theorem global_extension_relative
    [MulAction H Brauer] [MulAction E Brauer]
    [MulAction H Weight] [MulAction E Weight]
    (A : ActionData phi (Brauer := Brauer) (Weight := Weight))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (x : Brauer) :
    letI : MulAction (H ⋊[phi] E) Brauer :=
      semidirectMulAction phi A.brauerCompatible
    ∀ (iota : PrimeRegularRootEmbedding p k K
          (embeddedHStabilizer (phi := phi) x))
      (varphi : IBr iota),
      (∀ d : semidirectStabilizer (phi := phi) x,
        IrreducibleBrauerCharacter.twist iota varphi
          (MulAut.conjNormal d) = varphi) →
      ∃ W : FDRep k (embeddedHStabilizer (phi := phi) x),
        Representation.IsIrreducible W.ρ ∧
        varphi.1 = Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
        Nonempty (Representation.Extension
          (embeddedHStabilizer (phi := phi) x) W.ρ) := by
  let _ : MulAction (H ⋊[phi] E) Brauer :=
    semidirectMulAction phi A.brauerCompatible
  intro iota varphi hfixed
  exact exists_extension_to_semidirect_stabilizer_of_ibr_fixed
    principle x iota varphi hfixed

end GlobalExtension

section RawWeights

variable [MulAction H RawWeight] [MulAction E RawWeight]

/-- Data which identify the first component of a raw weight and express the
standard inner-conjugation action.  The condition that the normaliser fixes
the second component is the character-theoretic input needed to identify
the `H`-stabiliser of the raw pair. -/
structure RawWeightData where
  compatible : SemidirectActionCompatible (X := RawWeight) phi
  subgroup : RawWeight → Subgroup H
  subgroupConjugate : ∀ (h : H) (w : RawWeight),
    subgroup (h • w) = (subgroup w).map (MulAut.conj h)
  normalizerFixes : ∀ (h : H) (w : RawWeight),
    h ∈ Subgroup.normalizer (subgroup w : Set H) → h • w = w

/-- The `H`-stabiliser of a raw weight is its subgroup normaliser. -/
theorem raw_weight_stabilizer_eq_normalizer
    (R : RawWeightData phi (RawWeight := RawWeight)) (w : RawWeight) :
    MulAction.stabilizer H w =
      Subgroup.normalizer (R.subgroup w : Set H) :=
  stabilizer_eq_normalizer_of_subgroup_equivariant
    R.subgroup R.subgroupConjugate R.normalizerFixes w

/-- The restricted `H`-stabiliser inside the semidirect-product stabiliser
is the normaliser of the subgroup belonging to the raw weight. -/
theorem raw_weight_embedded_stabilizer_is_normalizer
    (R : RawWeightData phi (RawWeight := RawWeight)) (w : RawWeight) :
    letI : MulAction (H ⋊[phi] E) RawWeight :=
      semidirectMulAction phi R.compatible
    hStabilizer (phi := phi) w =
      Subgroup.normalizer (R.subgroup w : Set H) := by
  let _ : MulAction (H ⋊[phi] E) RawWeight :=
    semidirectMulAction phi R.compatible
  ext h
  change (SemidirectProduct.inl h : H ⋊[phi] E) • w = w ↔
    h ∈ Subgroup.normalizer (R.subgroup w : Set H)
  rw [semidirect_inl_smul phi R.compatible]
  exact Subgroup.ext_iff.mp (raw_weight_stabilizer_eq_normalizer phi R w) h

/-- The quotient of the raw-pair stabiliser by its embedded normaliser is
cyclic.  This is the group-theoretic input for the local use of Navarro
(8.12). -/
theorem raw_weight_stabilizer_quotient_cyclic
    (R : RawWeightData phi (RawWeight := RawWeight)) (w : RawWeight) :
    letI : MulAction (H ⋊[phi] E) RawWeight :=
      semidirectMulAction phi R.compatible
    IsCyclic (semidirectStabilizer (phi := phi) w ⧸
      embeddedHStabilizer (phi := phi) w) := by
  let _ : MulAction (H ⋊[phi] E) RawWeight :=
    semidirectMulAction phi R.compatible
  exact isCyclic_stabilizer_quotient (phi := phi) w

section LocalExtension

variable {p : ℕ} {k : Type u} {K : Type v}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Cyclicity of the quotient used in the local extension step.  The first
quotient removes the concrete weight subgroup and the second removes its
normaliser.  The result is proved from the canonical embedding of the
raw-pair stabiliser quotient into `E`. -/
theorem local_quotient_tower_cyclic
    (R : RawWeightData phi (RawWeight := RawWeight))
    (w : RawWeight) :
    letI : MulAction (H ⋊[phi] E) RawWeight :=
      semidirectMulAction phi R.compatible
    ∀ (Qbar : Subgroup (semidirectStabilizer (phi := phi) w))
      (qnormal : Qbar.Normal)
      (hQ : Qbar ≤ embeddedHStabilizer (phi := phi) w),
      letI : Qbar.Normal := qnormal
      IsCyclic
        (((semidirectStabilizer (phi := phi) w) ⧸ Qbar) ⧸
          (embeddedHStabilizer (phi := phi) w).map
            (QuotientGroup.mk' Qbar)) := by
  let _ : MulAction (H ⋊[phi] E) RawWeight :=
    semidirectMulAction phi R.compatible
  intro Qbar qnormal hQ
  letI : Qbar.Normal := qnormal
  exact isCyclic_quotient_tower_of_embedding
    Qbar (embeddedHStabilizer (phi := phi) w) hQ
    (stabilizerQuotientEmbedding (phi := phi) w)
    (stabilizerQuotientEmbedding_injective (phi := phi) w)

/-- Local extension in clause (iv)(b).  The subgroup `Qbar` is the concrete
copy of the weight subgroup in the raw-pair stabiliser.  Its identification,
normality, and the identification of `theta0` with the reduction supplied by
Navarro (3.18) remain explicit source inputs.  Lean derives the two-stage
cyclic quotient and applies Navarro (8.12); existence of the extension is
not assumed. -/
theorem local_extension_relative
    (R : RawWeightData phi (RawWeight := RawWeight))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (w : RawWeight) :
    letI : MulAction (H ⋊[phi] E) RawWeight :=
      semidirectMulAction phi R.compatible
    ∀ (Qbar : Subgroup (semidirectStabilizer (phi := phi) w))
      (qnormal : Qbar.Normal)
      (hQ : Qbar ≤ embeddedHStabilizer (phi := phi) w),
      letI : Qbar.Normal := qnormal
      ∀ (iota : PrimeRegularRootEmbedding p k K
          ((embeddedHStabilizer (phi := phi) w).map
            (QuotientGroup.mk' Qbar)))
        (theta0 : IBr iota),
        (∀ d : (semidirectStabilizer (phi := phi) w) ⧸ Qbar,
          IrreducibleBrauerCharacter.twist iota theta0
            (MulAut.conjNormal d) = theta0) →
        ∃ W : FDRep k ((embeddedHStabilizer (phi := phi) w).map
              (QuotientGroup.mk' Qbar)),
          Representation.IsIrreducible W.ρ ∧
          theta0.1 =
            Representation.brauerCharacterOfRootEmbedding W.ρ iota ∧
          Nonempty (Representation.Extension
            ((embeddedHStabilizer (phi := phi) w).map
              (QuotientGroup.mk' Qbar)) W.ρ) := by
  let _ : MulAction (H ⋊[phi] E) RawWeight :=
    semidirectMulAction phi R.compatible
  intro Qbar qnormal hQ
  letI : Qbar.Normal := qnormal
  intro iota theta0 hfixed
  have hcyclic : IsCyclic
      (((semidirectStabilizer (phi := phi) w) ⧸ Qbar) ⧸
        (embeddedHStabilizer (phi := phi) w).map
          (QuotientGroup.mk' Qbar)) :=
    local_quotient_tower_cyclic phi R w Qbar qnormal hQ
  exact Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
    principle iota theta0 hcyclic hfixed

end LocalExtension

end RawWeights

end ModularRep.PaperProofs.CyclicOuterLemma37Relative


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
