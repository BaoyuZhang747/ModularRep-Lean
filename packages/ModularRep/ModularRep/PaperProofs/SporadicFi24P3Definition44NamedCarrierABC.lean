import ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow

/-!
# Named carriers for An--Dietrich Definition 4.4(3a)--(3c)

The reference is Definition 4.4(3), printed p. 332, and the centreless
specialisation in Section 4.3.4, p. 334. This file chooses the existential
`G_theta` to be the selected Brauer stabiliser. The required `A_{Q,theta}`
is defined by pointwise fixation of `Z`, preservation of the selected `Q`,
and fixation of `theta`; it is not defined as an induced image.

The manuscript right action is `theta^alpha = op(alpha) • theta` and
`Q^alpha = Q.comap alpha`. Ambient left conjugation by `g` acts on
characters through `op(rho(g)⁻¹)`. The inversion in this formula is proved
harmless for stabilisers below.

E1/U inputs are the literal coefficient/group data in `P`, centrelessness,
and the faithful, surjective selected semidirect presentation `haut`.
`S` supplies that presentation's outer involution (its inherited block
census is unused in this deduction). The correspondence is arbitrary and
fully equivariant. No source field supplies any of the conclusions below.
The source ledger records the remaining identification with Fi'24 at 3.
-/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC

open Formalisation ModularRep ModularRep.CharacterWeight
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.CyclicOuterRawPairNormalizer
open ModularRep.PaperProofs.EvenFieldFLZSourceConditions
open ModularRep.PaperProofs.SporadicFi24SelectedOuterC2
open ModularRep.PaperProofs.SporadicFi24SelectedOuterLocalCarrier
open ModularRep.PaperProofs.SporadicFi24SelectedOuterSpathAmbient
open ModularRep.PaperProofs.SporadicFi24ThreeBlockCancellationActual
open ModularRep.PaperProofs.SporadicFi24P3Definition44Clause3ACWindow
open scoped Pointwise

universe u

/-- One correspondence and one matched pair index every named carrier. -/
structure EquivariantMatch (P : Definition35Problem.{u}) where
  Omega : IBr P.iota ≃ GlobalWeight P
  theta : Definition35Brauer P
  weight : Definition35Weight P
  equivariant : ∀ (alpha : (MulAut P.H)ᵐᵒᵖ) (chi : IBr P.iota),
    Omega (alpha • chi) = alpha • Omega chi
  matched : weight.1 = Omega theta.1

variable (P : Definition35Problem.{u}) (M : EquivariantMatch P)
variable (S : Fi24ThreeBlockSource (k := P.k) (X := P.H))

abbrev X := P.H
abbrev Z := Subgroup.center P.H
abbrev GTheta := SelectedBrauerAmbient P.iota S M.theta.1
abbrev XInGTheta := SelectedBrauerBase P.iota S M.theta.1
abbrev xEmbedding := selectedClause3BaseEmbedding P M.theta S

/-- `Q` comes from the chosen representative of this very weight. -/
def Q : Subgroup P.H :=
  rawSubgroup (selectedRawWeight P.blockSource P.block M.weight)

def QInGTheta : Subgroup (GTheta P M S) :=
  (rawAmbientRadical (selectedOuterField S)
    (selectedRawWeight P.blockSource P.block M.weight)).subgroupOf
      (GTheta P M S)

abbrev PairNormalizer :=
  Subgroup.normalizer (QInGTheta P M S : Set (GTheta P M S))

abbrev inducedConjugation := selectedAmbientToMulAut P S M.theta

abbrev Centralizer := SelectedClause3Centralizer P M.theta S

local instance selectedOuterFinite : Finite (SelectedOuterGroup S) :=
  Finite.of_injective
    (fun e : SelectedOuterGroup S ↦ (e.1.unop : P.H → P.H))
    (fun _ _ h ↦ Subtype.ext
      (MulOpposite.unop_injective (DFunLike.coe_injective h)))

/-- The literal source subgroup `C_{N_A(Q)}(theta)`, `A=C_Aut(X)(Z)`.
Preserving `Q` is expressed pointwise, equivalently `Q^alpha=Q`. -/
def RequiredPairStabilizer : Subgroup (MulAut P.H) where
  carrier := {alpha | (∀ z : Z P, alpha z.1 = z.1) ∧
    (∀ x : P.H, alpha x ∈ Q P M ↔ x ∈ Q P M) ∧
    MulOpposite.op alpha • M.theta.1 = M.theta.1}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨haz, haq, hat⟩ ⟨hbz, hbq, hbt⟩
    refine ⟨fun z ↦ ?_, fun x ↦ ?_, ?_⟩
    · change a (b z.1) = z.1
      rw [hbz, haz]
    · exact (haq (b x)).trans (hbq x)
    · rw [MulOpposite.op_mul, mul_smul, hat, hbt]
  inv_mem' := by
    rintro a ⟨haz, haq, hat⟩
    refine ⟨fun z ↦ ?_, fun x ↦ ?_, ?_⟩
    · apply a.injective
      simpa using (haz z).symm
    · simpa using (haq (a⁻¹ x)).symm
    · exact (inv_smul_eq_iff.mpr hat.symm)

theorem rightAction_convention (alpha : MulAut P.H) :
    MulOpposite.op alpha • M.theta.1 =
      IrreducibleBrauerCharacter.twist P.iota M.theta.1 alpha := rfl

theorem radical_rightAction_fixed_iff (alpha : MulAut P.H) :
    (Q P M).comap alpha.toMonoidHom = Q P M ↔
      ∀ x : P.H, alpha x ∈ Q P M ↔ x ∈ Q P M := by
  exact SetLike.ext_iff

theorem ambient_mem_iff_theta_fixed (g : SelectedOuterAmbient S) :
    g ∈ GTheta P M S ↔
      MulOpposite.op (semidirectToMulAut (selectedOuterField S) g) •
        M.theta.1 = M.theta.1 := by
  let := selectedBrauerSemidirectAction P.iota S
  change (g • M.theta.1 = M.theta.1) ↔ _
  rw [selectedBrauer_smul_eq_selectedOuterOpCover]
  change MulOpposite.op
    (semidirectToMulAut (selectedOuterField S) g⁻¹) • M.theta.1 = _ ↔ _
  rw [map_inv, MulOpposite.op_inv]
  rw [inv_smul_eq_iff, eq_comm]

theorem ambient_normalizer_iff (g : SelectedOuterAmbient S) :
    g ∈ Subgroup.normalizer
        (rawAmbientRadical (selectedOuterField S)
          (selectedRawWeight P.blockSource P.block M.weight) :
            Set (SelectedOuterAmbient S)) ↔
      ∀ x : P.H,
        semidirectToMulAut (selectedOuterField S) g x ∈ Q P M ↔
          x ∈ Q P M := by
  let r := selectedRawWeight P.blockSource P.block M.weight
  have hmap :
      (rawAmbientRadical (selectedOuterField S) r).map
          (MulAut.conj g).toMonoidHom =
        ((Q P M).map
          (semidirectToMulAut (selectedOuterField S) g).toMonoidHom).map
            (SemidirectProduct.inl : P.H →* SelectedOuterAmbient S) := by
    rw [rawAmbientRadical, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext (fun x ↦ selectedOuter_conjugate_inl S g x)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  simp only [MulEquiv.toMonoidHom_eq_coe] at hmap
  rw [hmap]
  change _ = (Q P M).map
    (SemidirectProduct.inl : P.H →* SelectedOuterAmbient S) ↔ _
  rw [(Subgroup.map_injective SemidirectProduct.inl_injective).eq_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have hmem : semidirectToMulAut (selectedOuterField S) g x ∈
          (Q P M).map (semidirectToMulAut (selectedOuterField S) g) := by
        rwa [h]
      rcases hmem with ⟨y, hy, heq⟩
      exact (semidirectToMulAut (selectedOuterField S) g).injective heq ▸ hy
    · intro hx
      rw [← h]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  · intro h
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (h y).mpr hy
    · intro hx
      refine ⟨(semidirectToMulAut (selectedOuterField S) g)⁻¹ x, ?_, by simp⟩
      exact (h _).mp (by simpa using hx)

/-- Natural inclusion identifies the raw-pair stabiliser with the literal
normaliser inside `G_theta`; no normaliser equality is an input. -/
def pairNormalizerEquiv : SelectedPairStabilizer P S M.weight ≃*
    PairNormalizer P M S :=
  (MulEquiv.subgroupCongr
    (selectedPairStabilizer_eq_brauer_inf_normalizer
      P S M.Omega M.equivariant M.theta M.weight M.matched)).trans
    (infNormalizerEquivNormalizerSubgroupOf _ _
      (rawAmbientRadical_le_selectedBrauerAmbient
        P S M.Omega M.equivariant M.theta M.weight M.matched))

@[simp]
theorem pairNormalizerEquiv_coe (n : SelectedPairStabilizer P S M.weight) :
    (((pairNormalizerEquiv P M S n : PairNormalizer P M S) :
      GTheta P M S) : SelectedOuterAmbient S) = n.1 := rfl

theorem product_decomposition (a : GTheta P M S) :
    ∃ x : XInGTheta P M S, ∃ n : PairNormalizer P M S,
      a = x.1 * n.1 := by
  obtain ⟨x, n, _, heq⟩ := selectedBrauerAmbient_factorization
    P M.theta M.weight S M.Omega M.equivariant M.matched a
  refine ⟨x, pairNormalizerEquiv P M S n, ?_⟩
  exact Subtype.ext heq

theorem Q_radical : IsRadicalSubgroup P.p (Q P M) :=
  (selectedCharacterWeight P.blockSource P.block M.weight).radical

theorem embedded_Q_identification :
    QInGTheta P M S = (Q P M).map (xEmbedding P M S) := by
  apply Subgroup.map_injective (GTheta P M S).subtype_injective
  rw [QInGTheta, Subgroup.map_subgroupOf_eq_of_le
    (rawAmbientRadical_le_selectedBrauerAmbient
      P S M.Omega M.equivariant M.theta M.weight M.matched)]
  rw [Subgroup.map_map]
  rfl

theorem xEmbedding_injective : Function.Injective (xEmbedding P M S) :=
  Subtype.val_injective.comp (selectedClause3BaseEquiv P M.theta S).injective

theorem xEmbedding_range : (xEmbedding P M S).range = XInGTheta P M S := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact (selectedClause3BaseEquiv P M.theta S x).2
  · intro ha
    obtain ⟨x, hx⟩ := (selectedClause3BaseEquiv P M.theta S).surjective ⟨a, ha⟩
    exact ⟨x, congrArg Subtype.val hx⟩

theorem product_set_eq_univ :
    (XInGTheta P M S : Set (GTheta P M S)) *
      (PairNormalizer P M S : Set (GTheta P M S)) = Set.univ := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨x, n, heq⟩ := product_decomposition P M S a
    exact ⟨x.1, x.2, n.1, n.2, heq.symm⟩

theorem pairNormalizer_mem_iff (g : GTheta P M S) :
    g ∈ PairNormalizer P M S ↔
      ∀ x : P.H, inducedConjugation P M S g x ∈ Q P M ↔ x ∈ Q P M := by
  have hQ := rawAmbientRadical_le_selectedBrauerAmbient
    P S M.Omega M.equivariant M.theta M.weight M.matched
  change g ∈ Subgroup.normalizer
    ((rawAmbientRadical (selectedOuterField S)
      (selectedRawWeight P.blockSource P.block M.weight)).subgroupOf
        (GTheta P M S) : Set (GTheta P M S)) ↔ _
  rw [← Subgroup.subgroupOf_normalizer_eq hQ]
  exact ambient_normalizer_iff P M S g.1

variable (hcenter : Subgroup.center P.H = ⊥)
variable (haut : Function.Bijective (semidirectToMulAut (selectedOuterField S)))

include hcenter in
theorem center_element_eq_one (z : Z P) : z.1 = 1 :=
  (Subgroup.eq_bot_iff_forall _).mp hcenter z.1 z.2

include hcenter haut in
/-- The induced image equals the source's independently defined subgroup. -/
theorem induced_automorphisms_eq :
    (PairNormalizer P M S).map (inducedConjugation P M S) =
      RequiredPairStabilizer P M := by
  ext alpha
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, (pairNormalizer_mem_iff P M S g).mp hg,
      (ambient_mem_iff_theta_fixed P M S g.1).mp g.2⟩
    intro z
    rw [center_element_eq_one P hcenter z, map_one]
  · rintro ⟨_, hQ, htheta⟩
    obtain ⟨g, hg⟩ := haut.2 alpha
    have hmem : g ∈ GTheta P M S :=
      (ambient_mem_iff_theta_fixed P M S g).mpr (hg ▸ htheta)
    refine ⟨⟨g, hmem⟩, ?_, hg⟩
    apply (pairNormalizer_mem_iff P M S ⟨g, hmem⟩).mpr
    simpa only [inducedConjugation, selectedAmbientToMulAut,
      MonoidHom.comp_apply, Subgroup.coe_subtype, hg] using hQ

/-- Conjugation is along the actual inclusion of `X` into `G_theta`. -/
theorem conjugation_embedding (g : GTheta P M S) (x : P.H) :
    g * xEmbedding P M S x * g⁻¹ =
      xEmbedding P M S (inducedConjugation P M S g x) := by
  apply Subtype.ext
  exact selectedOuter_conjugate_inl S g.1 x

/-- The ordinary central character is realised on a one-dimensional space. -/
def lambda : OrdinaryIrreducibleCharacter.Irr P.K (Z P) :=
  ⟨fun _ ↦ 1, ⟨{
    dimension := 1
    representation := Representation.trivial P.K (Z P) (Fin 1 → P.K)
    irreducible := by
      let V := Fin 1 → P.K
      let rho := Representation.trivial P.K (Z P) V
      let : Nontrivial (Subrepresentation rho) :=
        ⟨⟨⊥, ⊤, by
          intro h
          exact (bot_ne_top : (⊥ : Submodule P.K V) ≠ ⊤)
            (congrArg Subrepresentation.toSubmodule h)⟩⟩
      let : IsSimpleOrder (Submodule P.K V) :=
        is_simple_module_of_finrank_eq_one
          (show Module.finrank P.K V = 1 by simp [V])
      refine IsSimpleOrder.mk ?_
      intro W
      rcases IsSimpleOrder.eq_bot_or_eq_top W.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.ext h)
      · exact Or.inr (Subrepresentation.ext h)
    character_eq := by
      funext z
      simp [Representation.character, Representation.trivial] }⟩⟩

include hcenter in
theorem lambda_faithful : Function.Injective (lambda P) := by
  intro z t _
  apply Subtype.ext
  rw [center_element_eq_one P hcenter z, center_element_eq_one P hcenter t]

abbrev gammaRoot := selectedClause3CentralizerRoot P hcenter M.theta S haut
abbrev gamma := selectedClause3Gamma P hcenter M.theta S haut
abbrev centralizerConjugation :=
  selectedClause3CentralizerConjugation P hcenter M.theta S haut

/-- In this centreless case the canonical equivalence is also the inclusion. -/
def zToCentralizer : Z P →* Centralizer P M S :=
  (selectedClause3CentralizerEquivCenter P hcenter M.theta S haut).toMonoidHom

theorem zToCentralizer_inclusion (z : Z P) :
    (zToCentralizer P M S hcenter haut z).1 = xEmbedding P M S z.1 := by
  change 1 = xEmbedding P M S z.1
  rw [center_element_eq_one P hcenter z, map_one]

/-- Literal restriction on prime regular elements, with an ordinary lambda. -/
theorem gamma_lies_over_lambda (z : PrimeRegularElement (G := Z P) P.p) :
    (gamma P M S hcenter haut).1
      ⟨zToCentralizer P M S hcenter haut z.1,
        z.2.map (zToCentralizer P M S hcenter haut)⟩ = lambda P z.1 := by
  exact selectedClause3Gamma_eq_one P hcenter M.theta S haut _

include hcenter in
theorem theta_lies_over_lambda (z : PrimeRegularElement (G := Z P) P.p) :
    M.theta.1.1 ⟨z.1.1, z.2.map (Subgroup.center P.H).subtype⟩ =
      M.theta.1.1 ⟨1, isPrimeRegular_one⟩ * lambda P z.1 := by
  have heq : (⟨z.1.1, z.2.map (Subgroup.center P.H).subtype⟩ :
      PrimeRegularElement (G := P.H) P.p) = ⟨1, isPrimeRegular_one⟩ :=
    Subtype.ext (center_element_eq_one P hcenter z.1)
  rw [heq]
  exact (mul_one _).symm

/-- Only Definition 4.4(3a)--(3c), on the named carriers of this same match.
The ordinary lambda and Brauer gamma are fixed constructions above. -/
structure NamedClause3ABCWitness : Prop where
  X_normal : (XInGTheta P M S).Normal
  Z_central : (Z P).map (xEmbedding P M S) ≤ Subgroup.center (GTheta P M S)
  theta_invariant : ∀ g : GTheta P M S,
    MulOpposite.op (inducedConjugation P M S g) • M.theta.1 = M.theta.1
  induced_eq : (PairNormalizer P M S).map (inducedConjugation P M S) =
    RequiredPairStabilizer P M
  product_eq : (XInGTheta P M S : Set (GTheta P M S)) *
    (PairNormalizer P M S : Set (GTheta P M S)) = Set.univ
  centralizer_abelian : ∀ c d : Centralizer P M S, c * d = d * c
  gamma_over_lambda : ∀ z : PrimeRegularElement (G := Z P) P.p,
    (gamma P M S hcenter haut).1
      ⟨zToCentralizer P M S hcenter haut z.1,
        z.2.map (zToCentralizer P M S hcenter haut)⟩ = lambda P z.1
  gamma_invariant : ∀ g : GTheta P M S,
    IrreducibleBrauerCharacter.twist (gammaRoot P M S hcenter haut)
      (gamma P M S hcenter haut) (centralizerConjugation P M S hcenter haut g) =
        gamma P M S hcenter haut

theorem namedClause3ABCWitness_of_equivariantMatch :
    NamedClause3ABCWitness P M S hcenter haut where
  X_normal := selectedClause3Base_normal P M.theta S
  Z_central := selectedClause3Center_image_le P hcenter M.theta S
  theta_invariant g := (ambient_mem_iff_theta_fixed P M S g.1).mp g.2
  induced_eq := induced_automorphisms_eq P M S hcenter haut
  product_eq := product_set_eq_univ P M S
  centralizer_abelian := selectedClause3Centralizer_commutes P hcenter M.theta S haut
  gamma_over_lambda := gamma_lies_over_lambda P M S hcenter haut
  gamma_invariant := selectedClause3Gamma_invariant P hcenter M.theta S haut

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierABC


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
