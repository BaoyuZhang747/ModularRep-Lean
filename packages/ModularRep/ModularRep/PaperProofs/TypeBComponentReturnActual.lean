import ModularRep.PaperProofs.TypeBComponentReturnOriginalCarriers
import ModularRep.PaperProofs.TypeBComponentReturnRestriction

/-!
# Current Lemma 4.4 on the original varying finite-product factors

The external product theorem is the sole representation theoretic input.
All normalization, permutation naturality, return actions and action
compatibilities are derived. The orbit stabiliser and every return subgroup
are formed in the ORIGINAL external group, and the local selectors live on
the original first-factor Brauer characters with the same root embeddings.
The local stabiliser premise is exactly the stated hypothesis of Lemma 4.4.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBComponentReturnActual

open Formalisation
open ModularRep.ManuscriptVerification.ComponentReturnFull
open TypeBComponentCycleNormalization TypeBRegularLeviCharacterActionAdapter
open TypeBComponentReturnOriginalCarriers EvenFieldAssumption53Relative

variable {p : ℕ} {C k K E : Type} [Fintype C]
variable (m : C → ℕ) (H D : Index m → Type)
variable [∀ i, Group (H i)] [∀ i, Finite (H i)] [∀ i, Group (D i)]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group E] [Finite E] [IsCyclic E]
variable (SH : CycleCoordinates m H) (SD : CycleCoordinates m D)
variable (diagonal : ∀ i, D i →* MulAut (H i))
variable (pairs : PairEdges m H D SH SD diagonal)
variable (iota : PrimeRegularRootEmbedding p k K (Original m H))
variable (factorRoot : ∀ c, PrimeRegularRootEmbedding p k K (Base m H c))
variable (source : TypeBFiniteProductNaturality.ExternalProductData
  (fun i : Index m ↦ Base m H i.1) (normalizedRoot m H SH iota)
  (fun i ↦ factorRoot i.1))
variable (outer : E →* MulAut (Original m H))
variable (phi : E →* MulAut (Original m D))
variable (normalises : AutomorphismSemidirectCompatible
  (coordinateMulAut H D diagonal) outer phi)
variable (base : IBr iota)

variable (tau : (originalStabilizer m H D diagonal iota outer base))
variable (hH : MonomialAction m H SH ((outer.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau⁻¹))
variable (hD : MonomialAction m D SD ((phi.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau⁻¹))

include pairs in
/-- Source-instantiated component return with the original carriers.

Finite cycle enumeration, original edge isomorphisms and the original
pointwise generator equations express that E permutes the pairs. Their
normalized consequences are not premises. The output contains the actual
character, its original orbit membership, fixation by every element of the
actual orbit stabiliser and the corresponding semidirect factorisation. -/
theorem component_return_actual
    (htau : Subgroup.zpowers tau = ⊤)
    (representative : ∀ c, IBr (factorRoot c))
    (representative_orbit : ∀ c,
      let _ := rightAutomorphismAction (factorRoot c) (diagonal (first m c))
      representative c ∈ MulAction.orbit (Base m D c)
        (source.characters (characterEquiv m H SH iota base) (first m c)))
    (local_factorisation : ∀ c,
      let _ := rightAutomorphismAction (factorRoot c) (diagonal (first m c))
      let _ := rightAutomorphismAction (factorRoot c) ((TypeBComponentReturnRestriction.returnAction m H SH (outer.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau hH) c)
      SemidirectStabilizerFactors ((TypeBComponentReturnRestriction.returnAction m D SD (phi.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau hD) c)
        (brauerRightActions_semidirectCompatible (factorRoot c)
          (diagonal (first m c)) ((TypeBComponentReturnRestriction.returnAction m H SH (outer.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau hH) c) ((TypeBComponentReturnRestriction.returnAction m D SD (phi.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau hD) c)
          (TypeBComponentReturnRestriction.return_actions_compatible m H D SH SD
            diagonal (outer.comp (originalStabilizer m H D diagonal iota outer base).subtype) (phi.comp (originalStabilizer m H D diagonal iota outer base).subtype) tau hH hD (fun e d ↦ normalises e.1 d) c))
        (representative c)) :
    let _ := rightAutomorphismAction iota (coordinateMulAut H D diagonal)
    let _ := rightAutomorphismAction iota (outer.comp (originalStabilizer m H D diagonal iota outer base).subtype)
    ∃ theta : IBr iota,
      theta ∈ MulAction.orbit (Original m D) base ∧
      (∀ e : (originalStabilizer m H D diagonal iota outer base), e • theta = theta) ∧
      SemidirectStabilizerFactors (phi.comp (originalStabilizer m H D diagonal iota outer base).subtype)
        (brauerRightActions_semidirectCompatible iota
          (coordinateMulAut H D diagonal) (outer.comp (originalStabilizer m H D diagonal iota outer base).subtype) (phi.comp (originalStabilizer m H D diagonal iota outer base).subtype)
          (fun e d ↦ normalises e.1 d)) theta := by
  classical
  let EO := originalStabilizer m H D diagonal iota outer base
  let outerO := outer.comp EO.subtype
  let phiO := phi.comp EO.subtype
  let returnH := TypeBComponentReturnRestriction.returnAction m H SH outerO tau hH
  let returnD := TypeBComponentReturnRestriction.returnAction m D SD phiO tau hD
  let n : C → ℕ := fun c ↦ m c + 1
  let hn : ∀ c, 0 < n c := fun c ↦ Nat.zero_lt_succ (m c)
  let X : C → Type := fun c ↦ IBr (factorRoot c)
  let P := TypeBNormalizedProductNaturality.toFiniteProductSource n hn
    (Base m H) (normalizedRoot m H SH iota) factorRoot source
    (Base m D) (fun c ↦ diagonal (first m c))
  let tupleEquiv : IBr iota ≃ ComponentTuple n X :=
    (characterEquiv m H SH iota).trans P.characters
  letI factorAction (c : C) : MulAction (Base m D c) (X c) :=
    rightAutomorphismAction (factorRoot c) (diagonal (first m c))
  letI returnAction (c : C) :
      MulAction (TypeBComponentReturnRestriction.ReturnGroup m tau c) (X c) :=
    rightAutomorphismAction (factorRoot c) (returnH c)
  letI : MulAction (Original m D) (IBr iota) :=
    rightAutomorphismAction iota (coordinateMulAut H D diagonal)
  letI : MulAction EO (IBr iota) := rightAutomorphismAction iota outerO
  letI : MulAction (Normalized m D) (IBr (normalizedRoot m H SH iota)) :=
    rightAutomorphismAction (normalizedRoot m H SH iota)
      (coordinateMulAut (fun i : Index m ↦ Base m H i.1)
        (fun i : Index m ↦ Base m D i.1) (fun i ↦ diagonal (first m i.1)))
  letI : MulAction EO (ComponentTuple n X) := tupleEquiv.symm.mulAction EO
  have hdiag : ∀ (d : Original m D) psi,
      tupleEquiv (d • psi) = productEquiv m D SD d • tupleEquiv psi := by
    intro d psi
    change P.characters (characterEquiv m H SH iota (d • psi)) = _
    rw [characterEquiv_diagonal m H D SH SD diagonal iota pairs]
    exact P.coordinate_naturality (productEquiv m D SD d)⁻¹
      (characterEquiv m H SH iota psi)
  have horbit : ∀ psi : IBr iota,
      tupleEquiv psi ∈ MulAction.orbit (Normalized m D) (tupleEquiv base) ↔
        psi ∈ MulAction.orbit (Original m D) base := by
    intro psi
    exact TypeBComponentReturnCarrierTransport.mem_orbit_iff
      tupleEquiv (productEquiv m D SD) hdiag base psi
  have hactualStable : Set.MapsTo
      (fun psi : IBr iota ↦ IrreducibleBrauerCharacter.twist iota psi (outer tau.1⁻¹))
      (MulAction.orbit (Original m D) base)
      (MulAction.orbit (Original m D) base) := by
    intro psi hpsi
    have hset := tau.property
    change (fun psi : IBr iota ↦
      IrreducibleBrauerCharacter.twist iota psi (outer tau.1⁻¹)) ''
        MulAction.orbit (Original m D) base = MulAction.orbit (Original m D) base at hset
    rw [← hset]
    exact ⟨psi, hpsi, rfl⟩
  have hstable : Set.MapsTo (tau • ·)
      (MulAction.orbit (Normalized m D) (tupleEquiv base))
      (MulAction.orbit (Normalized m D) (tupleEquiv base)) := by
    intro x hx
    change tupleEquiv (IrreducibleBrauerCharacter.twist iota
      (tupleEquiv.symm x) (outer tau.1⁻¹)) ∈ _
    apply (horbit _).mpr
    apply hactualStable
    apply (horbit _).mp
    simpa using hx
  have hgeneratorFirst : ∀ (g : Normalized m H) c,
      normalizedAction m H SH outerO tau⁻¹ g (lastIndex n hn c) =
        returnH c (TypeBComponentReturnRestriction.returnElement m tau c)⁻¹
          (g (firstIndex n hn c)) := by
    intro g c
    exact TypeBComponentReturnRestriction.generator_first m H SH outerO tau hH g c
  have hgeneratorSucc : ∀ (g : Normalized m H) c j (hj : j + 1 < n c),
      normalizedAction m H SH outerO tau⁻¹ g ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ =
        g ⟨c, ⟨j + 1, hj⟩⟩ := by
    intro g c j hj
    exact TypeBComponentReturnRestriction.generator_succ m H SH outerO tau hH
      g c ⟨j, Nat.lt_of_succ_lt_succ hj⟩
  obtain ⟨hfirstSource, hsuccSource⟩ := P.normalised_naturality
    (normalizedAction m H SH outerO tau⁻¹)
    (fun c ↦ returnH c (TypeBComponentReturnRestriction.returnElement m tau c)⁻¹)
    hgeneratorFirst hgeneratorSucc
  have hnormalized : normalizedAction m H SH outerO tau⁻¹ =
      MulAut.congr (productEquiv m H SH) (outer tau.1⁻¹) := rfl
  rw [hnormalized] at hfirstSource hsuccSource
  have hfirst : ∀ (x : ComponentTuple n X) c,
      (tau • x) (firstIndex n hn c) =
        TypeBComponentReturnRestriction.returnElement m tau c • x (lastIndex n hn c) := by
    intro x c
    change P.characters (characterEquiv m H SH iota
      (IrreducibleBrauerCharacter.twist iota (tupleEquiv.symm x) (outer tau.1⁻¹)))
        (firstIndex n hn c) =
      IrreducibleBrauerCharacter.twist (factorRoot c) (x (lastIndex n hn c))
        (returnH c (TypeBComponentReturnRestriction.returnElement m tau c)⁻¹)
    rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist]
    have h := hfirstSource (characterEquiv m H SH iota (tupleEquiv.symm x)) c
    change _ = IrreducibleBrauerCharacter.twist (factorRoot c)
      (tupleEquiv (tupleEquiv.symm x) (lastIndex n hn c)) _ at h
    simpa only [Equiv.apply_symm_apply, normalizedAction, MonoidHom.comp_apply,
      Subgroup.coe_inv] using h
  have hsucc : ∀ (x : ComponentTuple n X) c j (hj : j + 1 < n c),
      (tau • x) ⟨c, ⟨j + 1, hj⟩⟩ = x ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ := by
    intro x c j hj
    change P.characters (characterEquiv m H SH iota
      (IrreducibleBrauerCharacter.twist iota (tupleEquiv.symm x) (outer tau.1⁻¹)))
        ⟨c, ⟨j + 1, hj⟩⟩ = _
    rw [IrreducibleBrauerCharacter.equivAlongMulEquiv_twist]
    have h := hsuccSource (characterEquiv m H SH iota (tupleEquiv.symm x)) c j hj
    change _ = tupleEquiv (tupleEquiv.symm x) ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ at h
    simpa only [Equiv.apply_symm_apply, normalizedAction, MonoidHom.comp_apply,
      Subgroup.coe_inv] using h
  let localCompat := fun c ↦ brauerRightActions_semidirectCompatible
    (factorRoot c) (diagonal (first m c)) (returnH c) (returnD c)
    (TypeBComponentReturnRestriction.return_actions_compatible m H D SH SD
      diagonal outerO phiO tau hH hD (fun e d ↦ normalises e.1 d) c)
  obtain ⟨x, hx, _, hfixed⟩ :=
    TypeBComponentReturnSourceInstantiation.normalised_component_return n hn
      (Base m D) (fun c ↦ ↥(TypeBComponentReturnRestriction.ReturnGroup m tau c)) X
      returnD localCompat (tupleEquiv base) representative
      (TypeBComponentReturnRestriction.returnElement m tau)
      local_factorisation representative_orbit tau htau hstable hfirst hsucc
  have htheta : tupleEquiv.symm x ∈ MulAction.orbit (Original m D) base := by
    apply (horbit _).mp
    simpa using hx
  have hthetaFixed : ∀ e : EO, e • tupleEquiv.symm x = tupleEquiv.symm x := by
    intro e
    apply tupleEquiv.injective
    have h := hfixed e
    change tupleEquiv (e • tupleEquiv.symm x) = x at h
    simpa only [Equiv.apply_symm_apply, normalizedAction, MonoidHom.comp_apply,
      Subgroup.coe_inv] using h
  refine ⟨tupleEquiv.symm x, htheta, hthetaFixed, ?_⟩
  exact mem_semidirect_stabilizer_iff phiO
    (brauerRightActions_semidirectCompatible iota
      (coordinateMulAut H D diagonal) outerO phiO (fun e d ↦ normalises e.1 d))
    (tupleEquiv.symm x) hthetaFixed

end ModularRep.PaperProofs.TypeBComponentReturnActual


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
