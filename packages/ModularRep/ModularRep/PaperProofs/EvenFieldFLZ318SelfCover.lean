import ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge
import ModularRep.PaperProofs.CyclicOuterLocalRepresentationInflation
import ModularRep.PaperProofs.SubgroupQuotientImage
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A self-cover skeleton for Feng--Li--Zhang, Theorem 3.18

This module packages the kernel-checkable self-cover reductions adjacent to
the actual clauses of Feng--Li--Zhang, Theorem 3.18.  That theorem has clauses
(i)(a)--(d), (ii), (iii)(a)--(c), and (iv)(a)--(b).  It has no separate
modular-character-triple input and no normalisation at the trivial radical
subgroup.

The grading of the remaining boundary is explicit.

* E1: perfectness, the centreless automorphism decomposition, local block
  induction, the source-level character interpretation of the identity
  extensions, and the standard meanings of covering and central character
  fibres.
* E2: the representation theoretic inputs already used to construct the
  `CyclicEndgameData`, and Feng--Li--Zhang, Theorem 3.18 itself.
* U: identifying the singleton, universal-set, and literal block models below
  with the covering, central character, Clifford-correspondent, and induced
  block objects in clause (iii); identifying the selected raw pair with the
  representative in clause (iv)(b); and passing from the available
  representation extensions to the exact character extensions in clause
  (iv).  Inflation of the local representation extension from the quotient
  pair stabiliser to the pair stabiliser is kernel checked below; matching
  its trace with the source Brauer character remains external.
  The application-level facts that the underlying `S` is nonabelian simple,
  that the chosen prime divides its order, and that `H` is the required
  universal cover of `S` also remain here because this module has no carrier
  for `S`.
* L: applying the cited theorem to the combined clauses and naming its
  BAW-good conclusion.

Lean checks the consequences of the self-cover and centreless assumptions:
normality of the embedded copy of `H`, its centraliser, the centreless
automorphism quotient, invariance of the singleton block set, identity
extensions, the model fibre and block equalities, singleton inner orbits, and
both stabiliser factorisations.  These statements form a skeleton, not a
claim that every source-level character-theoretic clause has already been
formalised.  No generic implication to a caller-selected conclusion is
provided.  No declaration assumes BAW-goodness or iBAW.
-/

namespace ModularRep.PaperProofs.EvenFieldFLZ318SelfCover

open scoped MonoidAlgebra

open Formalisation
open ModularRep.CharacterWeight
open ModularRep.FDRepSimpleClassKZero
open ModularRep.IBrBlockBasicSetBridge
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.ManuscriptVerification.EvenUnipotentCorrespondence
open ModularRep.OrdinaryIrreducibleCharacter
open ModularRep.PaperProofs.CyclicOuterLemma37ActualBlockFibres
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalAction
open ModularRep.PaperProofs.CyclicOuterLemma37LiteralLocalExtension
open ModularRep.PaperProofs.EvenFieldProposition38Lemma37Bridge

noncomputable section

universe u

section StructuralClauses

variable {H E : Type u} [Group H] [Group E]
variable (phi : E →* MulAut H)

/-- The embedded copy of the self-cover `H` in `H ⋊ E`. -/
abbrev EmbeddedSelfCover : Subgroup (H ⋊[phi] E) :=
  (SemidirectProduct.inl : H →* H ⋊[phi] E).range

/-- Clause (i)(a)'s stabilisation of the self-cover is automatic for a
semidirect product: the embedded copy of `H` is normal. -/
theorem embeddedSelfCover_normal :
    (EmbeddedSelfCover phi).Normal := by
  change ((SemidirectProduct.inl : H →* H ⋊[phi] E).range).Normal
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The copy of `Z(H)` in the semidirect product. -/
abbrev EmbeddedSelfCoverCentre : Subgroup (H ⋊[phi] E) :=
  (Subgroup.center H).map
    (SemidirectProduct.inl : H →* H ⋊[phi] E)

/-- In the centreless specialisation, the embedded centre is trivial. -/
theorem embeddedSelfCoverCentre_eq_bot
    (hcenter : Subgroup.center H = ⊥) :
    EmbeddedSelfCoverCentre phi = ⊥ := by
  simp [EmbeddedSelfCoverCentre, hcenter]

/-- Centrelessness supplies the normality instance needed to form the
literal quotient by the embedded centre. -/
theorem embeddedSelfCoverCentre_normal_of_centerless
    (hcenter : Subgroup.center H = ⊥) :
    (EmbeddedSelfCoverCentre phi).Normal := by
  rw [embeddedSelfCoverCentre_eq_bot phi hcenter]
  infer_instance

/-- If the canonical map `H ⋊ E → Aut(H)` is faithful, centrelessness
forces the centraliser of the embedded copy of `H` to be trivial. -/
theorem centralizer_embeddedSelfCover_eq_bot
    (hcenter : Subgroup.center H = ⊥)
    (hautinj : Function.Injective (semidirectToMulAut phi)) :
    Subgroup.centralizer (EmbeddedSelfCover phi : Set (H ⋊[phi] E)) = ⊥ := by
  apply le_antisymm
  · intro g hg
    have hcomm : ∀ h : H,
        semidirectToMulAut phi g *
            semidirectToMulAut phi (SemidirectProduct.inl h) =
          semidirectToMulAut phi (SemidirectProduct.inl h) *
            semidirectToMulAut phi g := by
      intro h
      simpa only [map_mul] using congrArg (semidirectToMulAut phi)
        (Subgroup.mem_centralizer_iff.mp hg
          (SemidirectProduct.inl h) ⟨h, rfl⟩).symm
    have htrivial : semidirectToMulAut phi g = 1 :=
      mulAut_eq_one_of_commutes_semidirect_inner hcenter phi
        (semidirectToMulAut phi g) hcomm
    have hgOne : g = 1 := by
      apply hautinj
      simpa using htrivial
    simp [hgOne]
  · exact bot_le

/-- Clause (i)(b)'s centraliser equality after the self-cover is identified
with `H` and `Z(H)=1`. -/
theorem centralizer_embeddedSelfCover_eq_embeddedCentre
    (hcenter : Subgroup.center H = ⊥)
    (hautinj : Function.Injective (semidirectToMulAut phi)) :
    Subgroup.centralizer (EmbeddedSelfCover phi : Set (H ⋊[phi] E)) =
      EmbeddedSelfCoverCentre phi := by
  rw [centralizer_embeddedSelfCover_eq_bot phi hcenter hautinj,
    embeddedSelfCoverCentre_eq_bot phi hcenter]

/-- Clause (i)(b)'s automorphism quotient in the centreless specialisation.
The quotient by the embedded centre is the quotient by `⊥`. -/
noncomputable def centerlessAutomorphismQuotientEquiv
    (hcenter : Subgroup.center H = ⊥)
    (haut : Function.Bijective (semidirectToMulAut phi)) :
    letI : (EmbeddedSelfCoverCentre phi).Normal :=
      embeddedSelfCoverCentre_normal_of_centerless phi hcenter
    ((H ⋊[phi] E) ⧸ EmbeddedSelfCoverCentre phi) ≃* MulAut H := by
  letI : (EmbeddedSelfCoverCentre phi).Normal :=
    embeddedSelfCoverCentre_normal_of_centerless phi hcenter
  exact
    (QuotientGroup.quotientMulEquivOfEq
      (embeddedSelfCoverCentre_eq_bot phi hcenter)).trans
      (QuotientGroup.quotientBot.trans
        (MulEquiv.ofBijective (semidirectToMulAut phi) haut))

/-- The genuine structural sources for clauses (i)(a)--(b) in the
self-cover specialisation.  The other statements in those clauses are
derived below. -/
structure StructuralSource where
  perfect : Group.IsPerfect H
  centerless : Subgroup.center H = ⊥
  automorphismMap_bijective :
    Function.Bijective (semidirectToMulAut phi)

end StructuralClauses

section IdentityExtensions

variable {R G V : Type u}
variable [Semiring R] [Group G] [AddCommMonoid V] [Module R V]

/-- A representation of a group extends its restriction to the whole group.
This is the identity extension used in clauses (i)(c)--(d) when
`\widetilde G=G`. -/
def identityExtension (rho : Representation R G V) :
    Representation.Extension (⊤ : Subgroup G)
      (Representation.pullback rho (⊤ : Subgroup G).subtype) where
  representation := rho
  restrictionEquiv := Representation.Equiv.refl _

end IdentityExtensions

section QuotientExtensionInflation

variable {R D V : Type u}
variable [Field R] [Group D] [AddCommGroup V] [Module R V]
variable (Q N : Subgroup D) [Q.Normal]

/-- Inflation preserves irreducibility because the quotient map is
surjective. -/
theorem inflateQuotientExtension_isIrreducible
    (rho : Representation R (QuotientImage Q N) V)
    (extension : Representation.Extension (QuotientImage Q N) rho)
    (hirr : Representation.IsIrreducible rho) :
    Representation.IsIrreducible
      (inflateQuotientExtension Q N rho extension).representation :=
  (extension.representation_isIrreducible hirr).pullback
    (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)

/-- Elementwise trace-character form of the inflated extension.  Turning
this equality into an equality of Brauer characters still requires coherent
root embeddings for the quotient and ambient groups. -/
theorem inflateQuotientExtension_character_coe
    (rho : Representation R (QuotientImage Q N) V)
    (extension : Representation.Extension (QuotientImage Q N) rho)
    (n : N) :
    (inflateQuotientExtension Q N rho extension).representation.character
        (n : D) =
      (Representation.pullback rho
        (subgroupToQuotientImage Q N)).character n :=
  (inflateQuotientExtension Q N rho extension).character_coe n

end QuotientExtensionInflation

section SelfCoverSkeleton

variable {p : ℕ} {k K H E ι : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group H] [Fintype H] [Group E] [Finite E] [IsCyclic E]
variable [Fintype ι]
variable {blockIdempotent : ι → k[H]}
variable (iota : PrimeRegularRootEmbedding p k K H)
variable (hinj : IrreducibleBrauerCharacterInjectivity iota)
variable (blocks : BlockIdempotentDecomposition blockIdempotent)
variable [MulAction (MulAut H)ᵐᵒᵖ ι]
variable (phi : E →* MulAut H)
variable (blockSource : LocalBlockInductionSource
  (p := p) (k := k) (K := K) (G := H) (Block := ι))
variable (block : ι)
variable (T : FibreTransportSource iota hinj blocks phi block)
variable (quotientInput : RawNormalizerQuotientInput
  (p := p) (K := K) (H := H))
variable (localReduction : ∀ w : LiteralWeightFibre blockSource block,
  SelectedLocalReductionSource blockSource block w)

/-- The canonical right action of `H` on the selected block index. -/
abbrev SelfCoverBlockHAction : MulAction H ι :=
  rightAutomorphismAction (X := ι)
    (MulAut.conj : H →* MulAut H)

/-- The canonical right action of the outer factor on the selected block
index. -/
abbrev SelfCoverBlockEAction : MulAction E ι :=
  rightAutomorphismAction (X := ι) phi

section SingletonBlock

include T blockSource

/-- Clause (i)(a)'s invariance of the singleton block set under the
self-cover extension. -/
theorem singletonBlock_fixed
    (g : H ⋊[phi] E) :
    let _ : MulAction H ι := SelfCoverBlockHAction
    let _ : MulAction E ι := SelfCoverBlockEAction phi
    let _ : MulAction (H ⋊[phi] E) ι :=
      semidirectMulAction phi
        (rightAutomorphismSemidirectCompatible (X := ι) phi)
    g • block = block := by
  dsimp only
  letI : MulAction H ι := SelfCoverBlockHAction
  letI : MulAction E ι := SelfCoverBlockEAction phi
  change g.left • (g.right • block) = block
  rw [show g.right • block = block from T.outerBlock_fixed g.right]
  exact FibreTransportSource.innerBlock_fixed
    (blockSource := blockSource) (block := block) g.left

end SingletonBlock

/-- Clause (i)(c) after `\widetilde G=G`: an affording representation of a
Brauer character extends its restriction to the whole self-cover by the
identity extension. -/
def ClauseICSelfCoverExtension
    (psi : BrauerFibre iota hinj blocks block) : Prop :=
  ∃ V : FDRep k H,
    Representation.IsIrreducible V.ρ ∧
    psi.1.1 = Representation.brauerCharacterOfRootEmbedding V.ρ iota ∧
    Nonempty (Representation.Extension (⊤ : Subgroup H)
      (Representation.pullback V.ρ (⊤ : Subgroup H).subtype))

/-- Clause (i)(c) is an identity in the self-cover specialisation. -/
theorem clause_i_c_selfCover
    (psi : BrauerFibre iota hinj blocks block) :
    ClauseICSelfCoverExtension iota hinj blocks block psi := by
  rcases psi.1.2 with ⟨V, hV, hcharacter⟩
  exact ⟨V, hV, hcharacter, ⟨identityExtension V.ρ⟩⟩

/-- Clause (i)(d) after `\widetilde G=G`: inflate an affording
representation of the selected defect-zero character from `N_H(Q)/Q` to
`N_H(Q)`, then extend it to the whole stabiliser by the identity extension. -/
def ClauseIDSelfCoverExtension
    (w : LiteralWeightFibre blockSource block) : Prop :=
  let Q := SelectedRadical blockSource block w
  let N := Subgroup.normalizer (Q : Set H)
  let QN := Q.subgroupOf N
  let theta :=
    (selectedCharacterWeight blockSource block w).localCharacter
  ∃ R : OrdinaryIrreducibleCharacter.Realisation K (N ⧸ QN) theta.1,
    Nonempty (Representation.Extension
      (⊤ : Subgroup N)
      (Representation.pullback
        (Representation.pullback R.representation (QuotientGroup.mk' QN))
        (⊤ : Subgroup N).subtype))

/-- Clause (i)(d) is an identity in the self-cover specialisation. -/
theorem clause_i_d_selfCover
    (w : LiteralWeightFibre blockSource block) :
    ClauseIDSelfCoverExtension blockSource block w := by
  dsimp only [ClauseIDSelfCoverExtension]
  rcases (selectedCharacterWeight blockSource block w).localCharacter.2 with
    ⟨R⟩
  exact ⟨R, ⟨identityExtension
    (Representation.pullback R.representation
      (QuotientGroup.mk'
        ((SelectedRadical blockSource block w).subgroupOf
          (Subgroup.normalizer
            (SelectedRadical blockSource block w : Set H)))))⟩⟩

/-- The covering fibre in clause (iii)(a) becomes a singleton when
`\widetilde G=G`. -/
def SelfCoverBrauerLiftFibre
    (psi : BrauerFibre iota hinj blocks block) :
    Set (BrauerFibre iota hinj blocks block) :=
  {psi}

/-- The corresponding lifted-weight fibre in clause (iii)(a). -/
def SelfCoverWeightLiftFibre
    (w : WeightFibre blockSource block) :
    Set (WeightFibre blockSource block) :=
  {w}

/-- A label-neutral singleton used to model the central linear character
index after `Z(H)=1`.  Identifying it with the source theorem's actual set of
linear characters is a separate semantic obligation. -/
abbrev TrivialCentralLinearCharacter := Unit

/-- The only central character fibre is the whole Brauer block fibre. -/
def SelfCoverCentralBrauerFibre (_ : TrivialCentralLinearCharacter) :
    Set (BrauerFibre iota hinj blocks block) :=
  Set.univ

/-- The only central character fibre is the whole weight block fibre. -/
def SelfCoverCentralWeightFibre (_ : TrivialCentralLinearCharacter) :
    Set (WeightFibre blockSource block) :=
  Set.univ

/-- Model reduction for clause (iii)(a): the image of a singleton under the
lifted bijection.  Matching these singleton carriers with the source
theorem's covering fibres remains external. -/
theorem clause_iii_a_selfCover
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) :
    omega '' SelfCoverBrauerLiftFibre iota hinj blocks block psi =
      SelfCoverWeightLiftFibre blockSource block (omega psi) := by
  simp [SelfCoverBrauerLiftFibre, SelfCoverWeightLiftFibre]

/-- Model reduction for clause (iii)(b): the image of the universal fibre
indexed by the singleton central label.  Matching this model with the source
theorem's actual central character fibres remains external. -/
theorem clause_iii_b_selfCover
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (nu : TrivialCentralLinearCharacter) :
    omega '' SelfCoverCentralBrauerFibre iota hinj blocks block nu =
      SelfCoverCentralWeightFibre blockSource block nu := by
  simp [SelfCoverCentralBrauerFibre, SelfCoverCentralWeightFibre]

/-- The literal block equality that remains after replacing every lift and
Clifford correspondent in clause (iii)(c) by its self-cover model.  The
identification of those source-level objects with this model remains
external. -/
theorem clause_iii_c_selfCover
    (omega : BrauerFibre iota hinj blocks block ≃
      WeightFibre blockSource block)
    (psi : BrauerFibre iota hinj blocks block) :
    irreducibleBrauerCharacterBlock iota hinj blocks psi.1 =
      blockSource.operations.rawWeightBlock
        (selectedCharacterWeight blockSource block (omega psi)) := by
  calc
    irreducibleBrauerCharacterBlock iota hinj blocks psi.1 = block := psi.2
    _ = blockSource.operations.rawWeightBlock
        (selectedCharacterWeight blockSource block (omega psi)) :=
      (selectedCharacterWeight_block blockSource block (omega psi)).symm

/-- In clause (iv), every orbit of the self-cover on the literal Brauer
fibre is a singleton, so the character itself is a valid representative. -/
theorem clause_iv_representative_orbit
    (psi : BrauerFibre iota hinj blocks block) :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    MulAction.orbit H psi = {psi} := by
  dsimp only
  letI : MulAction H (BrauerFibre iota hinj blocks block) :=
    rightIBrBlockMulAction iota hinj blocks
      (MulAut.conj : H →* MulAut H) block
      (FibreTransportSource.innerBlock_fixed
        (blockSource := blockSource) (block := block))
      T.brauerBlock_transport
  ext chi
  rw [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact FibreTransportSource.inner_fixes_brauerFibre
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) (T := T) h psi
  · intro hchi
    subst chi
    exact ⟨1, one_smul H psi⟩

/-- Clause (iv)(b)'s subgroup product is an identity when
`\widetilde G=G`: the first factor is already contained in the full pair
stabiliser.  This elementwise statement is the exact factorisation needed
for the subgroup equality. -/
theorem clause_iv_b_selfCover_factorization
    (w : LiteralWeightFibre blockSource block)
    (d : PairStabilizer phi blockSource block w) :
    ∃ h : EmbeddedPairHStabilizer phi blockSource block w,
      ∃ x : PairStabilizer phi blockSource block w,
        (d : H ⋊[phi] E) =
          (((h : PairStabilizer phi blockSource block w) : H ⋊[phi] E) *
            (x : H ⋊[phi] E)) := by
  exact ⟨1, d, by simp⟩

/-- Kernel evidence for the self-cover skeleton surrounding
Feng--Li--Zhang, Theorem 3.18.  The field names retain the source clause
numbers, but the fields for (iii) are model reductions and the extension
fields for (iv) are representation-level statements on the available
literal carriers.  Consequently this structure is not, by itself, the full
source hypothesis.  It contains neither a BAW-good conclusion nor an iBAW
assertion. -/
structure SelfCoverClauseSkeleton
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction) where
  i_a_normal : (EmbeddedSelfCover phi).Normal
  i_a_perfect : Group.IsPerfect H
  i_a_outer_abelian : IsMulCommutative E
  i_a_singletonBlock_invariant : ∀ g : H ⋊[phi] E,
    let _ : MulAction H ι := SelfCoverBlockHAction
    let _ : MulAction E ι := SelfCoverBlockEAction phi
    let _ : MulAction (H ⋊[phi] E) ι :=
      semidirectMulAction phi
        (rightAutomorphismSemidirectCompatible (X := ι) phi)
    g • block = block
  i_b_centralizer :
    Subgroup.centralizer (EmbeddedSelfCover phi : Set (H ⋊[phi] E)) =
      EmbeddedSelfCoverCentre phi
  i_b_embeddedCentre_normal : (EmbeddedSelfCoverCentre phi).Normal
  i_b_automorphismQuotient :
    letI : (EmbeddedSelfCoverCentre phi).Normal :=
      i_b_embeddedCentre_normal
    Nonempty (((H ⋊[phi] E) ⧸ EmbeddedSelfCoverCentre phi) ≃* MulAut H)
  i_c_brauerIdentityExtension :
    ∀ psi : BrauerFibre iota hinj blocks block,
    ClauseICSelfCoverExtension iota hinj blocks block psi
  i_d_weightIdentityExtension :
    ∀ w : WeightFibre blockSource block,
    ClauseIDSelfCoverExtension blockSource block w
  ii_omega : EquivariantEquiv E
    (BrauerFibre iota hinj blocks block)
    (WeightFibre blockSource block)
    (rightIBrBlockMulAction iota hinj blocks phi block
      T.outerBlock_fixed T.brauerBlock_transport).smul
    (rightWeightFibreMulAction phi blockSource block
      T.outerBlock_fixed).smul
  ii_semidirectEquivariant :
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction H (WeightFibre blockSource block) :=
      rightWeightFibreMulAction
        (MulAut.conj : H →* MulAut H) blockSource block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
    let _ : MulAction E (WeightFibre blockSource block) :=
      rightWeightFibreMulAction phi blockSource block T.outerBlock_fixed
    let _ : MulAction (H ⋊[phi] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi
        (FibreTransportSource.brauerFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
          (blockSource := blockSource) (block := block) (T := T))
    let _ : MulAction (H ⋊[phi] E)
        (WeightFibre blockSource block) :=
      semidirectMulAction phi
        (FibreTransportSource.weightFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
          (blockSource := blockSource) (block := block) (T := T))
    ∀ (g : H ⋊[phi] E) (psi : BrauerFibre iota hinj blocks block),
      ii_omega.toEquiv (g • psi) = g • ii_omega.toEquiv psi
  iii_liftedOmega : BrauerFibre iota hinj blocks block ≃
    WeightFibre blockSource block
  iii_liftedOmega_eq : iii_liftedOmega = ii_omega.toEquiv
  iii_a_modelCoveringFibres :
    ∀ psi : BrauerFibre iota hinj blocks block,
    iii_liftedOmega ''
        SelfCoverBrauerLiftFibre iota hinj blocks block psi =
      SelfCoverWeightLiftFibre blockSource block (iii_liftedOmega psi)
  iii_b_modelCentralCharacterFibres :
    ∀ nu : TrivialCentralLinearCharacter,
    iii_liftedOmega ''
        SelfCoverCentralBrauerFibre iota hinj blocks block nu =
      SelfCoverCentralWeightFibre blockSource block nu
  iii_c_modelBlockEquality :
    ∀ psi : BrauerFibre iota hinj blocks block,
    irreducibleBrauerCharacterBlock iota hinj blocks psi.1 =
      blockSource.operations.rawWeightBlock
        (selectedCharacterWeight blockSource block (iii_liftedOmega psi))
  iv_orbitRepresentative :
    ∀ psi : BrauerFibre iota hinj blocks block,
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    MulAction.orbit H psi = {psi}
  iv_a_globalFactorization :
    ∀ psi : BrauerFibre iota hinj blocks block,
    let _ : MulAction H (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks
        (MulAut.conj : H →* MulAut H) block
        (FibreTransportSource.innerBlock_fixed
          (blockSource := blockSource) (block := block))
        T.brauerBlock_transport
    let _ : MulAction E (BrauerFibre iota hinj blocks block) :=
      rightIBrBlockMulAction iota hinj blocks phi block
        T.outerBlock_fixed T.brauerBlock_transport
    let _ : MulAction (H ⋊[phi] E)
        (BrauerFibre iota hinj blocks block) :=
      semidirectMulAction phi
        (FibreTransportSource.brauerFibre_compatible
          (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
          (blockSource := blockSource) (block := block) (T := T))
    ∀ g : H ⋊[phi] E,
      g ∈ MulAction.stabilizer (H ⋊[phi] E) psi ↔
        ∃ h : H, ∃ e : E,
          e ∈ MulAction.stabilizer E psi ∧
            g = SemidirectProduct.inl h * SemidirectProduct.inr e
  iv_a_globalRepresentationExtension :
    ∀ psi : BrauerFibre iota hinj blocks block,
    GlobalExtensionConclusion
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T psi
  iv_b_localFactorization :
    ∀ psi : BrauerFibre iota hinj blocks block,
    let w := ii_omega.toEquiv psi
    ∀ d : PairStabilizer phi blockSource block w,
      ∃ h : EmbeddedPairHStabilizer phi blockSource block w,
        ∃ x : PairStabilizer phi blockSource block w,
          (d : H ⋊[phi] E) =
            (((h : PairStabilizer phi blockSource block w) : H ⋊[phi] E) *
              (x : H ⋊[phi] E))
  iv_b_quotientRepresentationExtension :
    ∀ psi : BrauerFibre iota hinj blocks block,
    LocalExtensionConclusion (phi := phi) (blockSource := blockSource)
      (block := block) quotientInput
      (ii_omega.toEquiv psi) (localReduction (ii_omega.toEquiv psi))
  iv_b_inflatedLocalRepresentationExtension :
    ∀ psi : BrauerFibre iota hinj blocks block,
    InflatedLocalRepresentationExtensionConclusion
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput (ii_omega.toEquiv psi)
      (localReduction (ii_omega.toEquiv psi))

/-- Construct the kernel-checkable self-cover skeleton from the structural
source and the cyclic endgame.  This does not discharge the semantic
character-level obligations described in the module documentation. -/
noncomputable def selfCoverClauseSkeletonOfCyclicEndgame
    (structural : StructuralSource phi)
    (endgame : CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction) :
    SelfCoverClauseSkeleton iota hinj blocks phi blockSource block T quotientInput
      localReduction endgame where
  i_a_normal := embeddedSelfCover_normal phi
  i_a_perfect := structural.perfect
  i_a_outer_abelian := by infer_instance
  i_a_singletonBlock_invariant := fun g ↦
    singletonBlock_fixed iota hinj blocks phi blockSource block T g
  i_b_centralizer :=
    centralizer_embeddedSelfCover_eq_embeddedCentre phi
      structural.centerless structural.automorphismMap_bijective.1
  i_b_embeddedCentre_normal :=
    embeddedSelfCoverCentre_normal_of_centerless phi structural.centerless
  i_b_automorphismQuotient :=
    ⟨centerlessAutomorphismQuotientEquiv phi structural.centerless
      structural.automorphismMap_bijective⟩
  i_c_brauerIdentityExtension := fun psi ↦
    clause_i_c_selfCover iota hinj blocks block psi
  i_d_weightIdentityExtension := fun w ↦
    clause_i_d_selfCover blockSource block w
  ii_omega := endgame.omega
  ii_semidirectEquivariant := endgame.semidirect_equivariant
  iii_liftedOmega := endgame.omega.toEquiv
  iii_liftedOmega_eq := rfl
  iii_a_modelCoveringFibres := fun psi ↦
    clause_iii_a_selfCover iota hinj blocks blockSource block
      endgame.omega.toEquiv psi
  iii_b_modelCentralCharacterFibres := fun nu ↦
    clause_iii_b_selfCover iota hinj blocks blockSource block
      endgame.omega.toEquiv nu
  iii_c_modelBlockEquality := fun psi ↦
    clause_iii_c_selfCover iota hinj blocks blockSource block
      endgame.omega.toEquiv psi
  iv_orbitRepresentative := fun psi ↦
    clause_iv_representative_orbit iota hinj blocks phi blockSource block T psi
  iv_a_globalFactorization := fun psi ↦
    FibreTransportSource.brauerFibre_stabilizer_factorization
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) (T := T) psi
  iv_a_globalRepresentationExtension := endgame.global_extension
  iv_b_localFactorization := fun psi d ↦
    clause_iv_b_selfCover_factorization phi blockSource block
      (endgame.omega.toEquiv psi) d
  iv_b_quotientRepresentationExtension := endgame.local_extension
  iv_b_inflatedLocalRepresentationExtension := fun psi ↦
    inflate_localExtensionConclusion
      (phi := phi) (blockSource := blockSource) (block := block)
      quotientInput (endgame.omega.toEquiv psi)
      (localReduction (endgame.omega.toEquiv psi))
      (endgame.local_extension psi)

/-- Existential packaging of the skeleton, convenient after the actual
Proposition 3.8 bridge has produced `Nonempty CyclicEndgameData`. -/
theorem exists_selfCoverClauseSkeleton_of_cyclicEndgame
    (structural : StructuralSource phi)
    (hendgame : Nonempty (CyclicEndgameData
      (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
      (blockSource := blockSource) (block := block) T
      quotientInput localReduction)) :
    ∃ endgame : CyclicEndgameData
        (iota := iota) (hinj := hinj) (blocks := blocks) (phi := phi)
        (blockSource := blockSource) (block := block) T
        quotientInput localReduction,
      Nonempty (SelfCoverClauseSkeleton iota hinj blocks phi blockSource block T
        quotientInput localReduction endgame) := by
  rcases hendgame with ⟨endgame⟩
  exact ⟨endgame, ⟨selfCoverClauseSkeletonOfCyclicEndgame iota hinj blocks phi
    blockSource block T quotientInput localReduction structural endgame⟩⟩

end SelfCoverSkeleton

end

end ModularRep.PaperProofs.EvenFieldFLZ318SelfCover


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
