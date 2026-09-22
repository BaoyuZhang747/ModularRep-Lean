import ManuscriptIBAW.Jordan.BrauerRestriction
import ManuscriptIBAW.Jordan.GeneralGeometry
import ModularRep.PaperProofs.OddTwoFLZ57LiteralMapSource

/-!
# Restriction for Type C over a field of odd order

The source of the full field group condition remains FLZ Remark 5.4 on the
specified symplectic groups. Passing from that stronger condition to each
chosen subgroup is a theorem in this file, not part of that source.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan.TypeCOdd

open ModularRep
open ModularRep.PaperProofs
open CyclicOuterLemma37Concrete
open OddTwoConformalProjectiveRealisation
open OddTwoProjectiveAutomorphismDiagonalJoin
open OddTwoUniversalPrimeToTwoSelfCover
open OddTwoFengMalleForwardSourceJoin
open OddTwoFinalBlockOrbitCentralCoverDescentWindow
open OddTwoFLZ57LiteralMapSource

variable {n : ℕ} {F : Type} [Field F] [Fintype F]
  {C : CenterIntersectionSource n F} (S : BroughGroupSource C)
  (cover : OddSymplecticFullCoverSource n F)
  (lifting : FullCoverAutomorphismLiftingSource (n := n) (F := F))
  (P : LiteralFengMalleProblem n F)

local instance fieldAutomorphismFinite : Finite (F ≃+* F) :=
  Finite.of_injective (fun sigma : F ≃+* F => (sigma : F → F)) DFunLike.coe_injective

@[instance_reducible] def regularBrauerAction : MulAction (CSp n F) (IBr P.iota) :=
  MulAction.compHom (IBr P.iota)
    ((inverseOpHom (regularAction S cover lifting)).comp SemidirectProduct.inl)

@[instance_reducible] def fieldBrauerAction : MulAction (F ≃+* F) (IBr P.iota) :=
  rightAutomorphismAction (X := IBr P.iota) (spFieldAction (n := n) (F := F))

theorem fullHypothesis
    (h : LiteralAssumption53 S cover lifting P) :
    letI := regularBrauerAction S cover lifting P
    letI := fieldBrauerAction P
    FullBrauerHypothesis (D := CSp n F) P.iota (spFieldAction (n := n) (F := F)) := by
  letI := regularBrauerAction S cover lifting P
  letI := fieldBrauerAction P
  intro psi0
  obtain ⟨W⟩ := h.representative psi0
  obtain ⟨c, hc⟩ := W.inRegularOrbit
  obtain ⟨V, hV, hchar, extended, hext⟩ := W.fieldExtension
  refine ⟨W.representative, MulAction.mem_orbit_iff.mpr ⟨c, hc⟩, ⟨{
    factorization := ?_
    module := V
    irreducible := hV
    character_eq := hchar.symm
    extension := ⟨extended, ?_⟩ }⟩⟩
  · intro d e
    have hh := W.stabilizerFactorization (⟨d, e⟩ : RegularAmbient)
    change (inverseOpHom (regularAction S cover lifting) (⟨d, e⟩ : RegularAmbient) •
        W.representative = W.representative ↔
      inverseOpHom (regularAction S cover lifting) (SemidirectProduct.inl d) •
        W.representative = W.representative ∧
      inverseOpHom (spFieldAction (n := n) (F := F)) e •
        W.representative = W.representative) at hh
    have he : inverseOpHom (regularAction S cover lifting)
        (SemidirectProduct.inr e) = inverseOpHom (spFieldAction (n := n) (F := F)) e := by
      change MulOpposite.op (regularAction S cover lifting
        ((SemidirectProduct.inr e : RegularAmbient)⁻¹)) = _
      rw [← map_inv SemidirectProduct.inr, regularAction_field]
      rfl
    rw [← SemidirectProduct.inl_left_mul_inr_right (⟨d, e⟩ : RegularAmbient),
      map_mul, mul_smul, he] at hh
    exact hh
  · exact Representation.Equiv.mk (LinearEquiv.refl P.k V) (by
      intro g
      ext v
      exact DFunLike.congr_fun (hext g) v)

/-- This quantifier ranges over every original regular group orbit after the
subgroup for each label has been selected. -/
theorem perLabel {Label : Type*}
    (groups : Label → Subgroup (F ≃+* F))
    (h : LiteralAssumption53 S cover lifting P) :
    letI := regularBrauerAction S cover lifting P
    letI := fieldBrauerAction P
    ∀ s, RestrictedBrauerHypothesis (D := CSp n F)
      P.iota (spFieldAction (n := n) (F := F)) (groups s) := by
  letI := regularBrauerAction S cover lifting P
  letI := fieldBrauerAction P
  intro s
  exact fullBrauerHypothesis_restrict P.iota (spFieldAction (n := n) (F := F))
    (groups s) (fullHypothesis S cover lifting P h)

theorem regularBrauerAction_eq_canonical :
    regularBrauerAction S cover lifting P =
      canonicalRegularAction ((regularAction S cover lifting).comp SemidirectProduct.inl)
        P.iota := by
  change MulAction.compHom (IBr P.iota) _ = MulAction.compHom (IBr P.iota) _
  congr 1

/-- Identify the action of the regular group with the action of the same
automorphisms before constructing the hypothesis for each label. -/
theorem generalPerLabel {Label : Type*}
    (context : GeometricContext (ell := 2) (k := P.k) (S := Label)
      ((regularAction S cover lifting).comp SemidirectProduct.inl)
      (spFieldAction (n := n) (F := F)))
    (geometry : GeometricSelection
      ((regularAction S cover lifting).comp SemidirectProduct.inl)
      (spFieldAction (n := n) (F := F)) context)
    (h : LiteralAssumption53 S cover lifting P) :
    GeneralPerLabelHypothesis
      ((regularAction S cover lifting).comp SemidirectProduct.inl)
      (spFieldAction (n := n) (F := F)) P.iota context := by
  apply generalPerLabel_of_fullField _ _ P.iota context geometry
  have full := fullHypothesis S cover lifting P h
  rw [regularBrauerAction_eq_canonical S cover lifting P] at full
  exact full

end ManuscriptIBAW.Jordan.TypeCOdd

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
