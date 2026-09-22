import ModularRep.PaperProofs.TypeBCentralKernelTripleProjection

/-!
# Compatible quotient images in the actual character inertia

The quotient of the original character inertia is identified with the
actual quotient character inertia by the same ambient projection at every
point. This file proves that its base and local image subgroups are the
actual embedded quotient base and raw-weight inertia inside that group.
The restricted equivalences and their local intersection retain that same
point map. No block-triple witness or additional source assertion is used.

The inclusion of raw inertia in character inertia is construction data,
to be supplied by the single principal-fibre map in the final construction.
Neither inertia subgroup is assumed normal in the original ambient group.
-/

noncomputable section
set_option autoImplicit false

namespace ModularRep.PaperProofs.TypeBCentralKernelQuotientInertiaImages

open ModularRep TypeBCentralKernelCarriers TypeBCentralKernelInertia
open TypeBCentralKernelBrauerInflation TypeBCentralKernelTripleCarriers
open TypeBCentralKernelTripleCertificate TypeBCentralKernelTripleProjection

universe u

section QuotientImages

variable {A : Type u} [Group A]
  (P S T : Subgroup A) [P.Normal]
  (Sbar Tbar : Subgroup (QuotientA P))

/-- A full-preimage subgroup has exactly its prescribed image inside a
quotient inertia. The equivalence is anchored to the ambient projection. -/
theorem quotientImage_map
    (e : QuotientG T P ≃* Tbar)
    (point : ∀ t : T, (e (qG T P t)).val = qA P t.val)
    (preimage : S = Sbar.comap (qA P)) :
    ((inside S T).map (QuotientGroup.mk' (inside P T))).map e.toMonoidHom =
      inside Sbar Tbar := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := hx
    change (e (qG T P t)).val ∈ Sbar
    rw [point]
    change t.val ∈ Sbar.comap (qA P)
    rw [← preimage]
    exact ht
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (inside P T) x
    refine ⟨qG T P t, ?_, rfl⟩
    refine ⟨t, ?_, rfl⟩
    change t.val ∈ S
    rw [preimage]
    change qA P t.val ∈ Sbar
    change (e (qG T P t)).val ∈ Sbar at hy
    rwa [point] at hy

end QuotientImages

section ActualInertias

variable {p : ℕ} {k K A : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
  [Group A] [Finite A]
  (P G : Subgroup A) [P.Normal] [G.Normal]
  (hP : IsPGroup p (kernelInG G P))
  (root : PrimeRegularRootEmbedding p k K (QuotientG G P))
  (kernel : Navarro232Principle p k)
  (regular : PrimeRegularQuotientLiftPrinciple.{u} p)
  (thetaBar : IBr root)

abbrev inertia : Subgroup A :=
  T G (upRoot (kernelInG G P) hP root)
    (brauerEquiv (kernelInG G P) hP root kernel regular thetaBar)

abbrev quotientInertia : Subgroup (QuotientA P) :=
  brauerStabilizer (quotientAction G P) root thetaBar

local notation "TI" => inertia P G hP root kernel regular thetaBar
local notation "QI" => quotientInertia P G root thetaBar

/-- The existing canonical equivalence, with its source displayed using
the same quotient subgroup and group instance as the image carriers. -/
def inertiaQuotientEquiv : (TI ⧸ Z P TI) ≃* QI :=
  characterInertiaQuotientEquiv P G hP root kernel regular thetaBar

local notation "eT" => inertiaQuotientEquiv P G hP root kernel regular thetaBar

theorem base_le_inertia : G ≤ TI :=
  G_le_T G (upRoot (kernelInG G P) hP root)
    (brauerEquiv (kernelInG G P) hP root kernel regular thetaBar)

include hP kernel regular in
/-- The actual embedded quotient base lies in the quotient character inertia. -/
theorem embedded_quotient_le_inertia : embeddedQuotientG G P ≤ QI := by
  rintro a ⟨g, hg, rfl⟩
  have ht : g ∈ TI := base_le_inertia P G hP root kernel regular thetaBar hg
  change g ∈ T G (upRoot (kernelInG G P) hP root)
    (brauerEquiv (kernelInG G P) hP root kernel regular thetaBar) at ht
  rw [brauerStabilizer_quotient G P hP root kernel regular thetaBar] at ht
  exact ht

/-- The base image is fixed by the canonical character-inertia quotient
equivalence, rather than by an independently chosen group isomorphism. -/
theorem base_image (hPG : P ≤ G) :
    (Nbar P G TI).map (eT).toMonoidHom = inside (embeddedQuotientG G P) QI := by
  have preimage : G = (embeddedQuotientG G P).comap (qA P) := by
    exact (Subgroup.comap_map_eq_self (show (qA P).ker ≤ G from by
      rw [qA_ker]
      exact hPG)).symm
  exact quotientImage_map P G TI (embeddedQuotientG G P) QI eT
    (characterInertiaQuotientEquiv_mk_val P G hP root kernel regular thetaBar) preimage

abbrev quotientRawInertia (W : CharacterWeight p K G) : Subgroup (QuotientA P) :=
  rawStabilizer (quotientAction G P) (quotientWeight P G hP W)

/-- The local image equation uses the exact descended raw weight. It is
an intersection statement and does not itself need U ≤ T. -/
theorem local_image (W : CharacterWeight p K G) :
    (Hbar P G TI W).map (eT).toMonoidHom =
      inside (quotientRawInertia P G hP W) QI := by
  exact quotientImage_map P (U G W) TI (quotientRawInertia P G hP W) QI eT
    (characterInertiaQuotientEquiv_mk_val P G hP root kernel regular thetaBar)
    (rawStabilizer_quotient G P hP W)

/-- The downstairs raw inertia inclusion follows from the proved upstairs
inclusion and the two full-preimage equations. -/
theorem quotient_raw_le_inertia (W : CharacterWeight p K G) (hUT : U G W ≤ TI) :
    quotientRawInertia P G hP W ≤ QI := by
  intro a ha
  obtain ⟨x, rfl⟩ := qA_surjective P a
  have hx : x ∈ U G W := by
    rw [rawStabilizer_quotient G P hP W]
    exact ha
  have ht := hUT hx
  change x ∈ T G (upRoot (kernelInG G P) hP root)
    (brauerEquiv (kernelInG G P) hP root kernel regular thetaBar) at ht
  rw [brauerStabilizer_quotient G P hP root kernel regular thetaBar] at ht
  exact ht

variable (hPG : P ≤ G)

def baseImageEquiv : Nbar P G TI ≃* inside (embeddedQuotientG G P) QI :=
  ((eT).subgroupMap (Nbar P G TI)).trans
    (MulEquiv.subgroupCongr (base_image P G hP root kernel regular thetaBar hPG))

@[simp] theorem baseImageEquiv_val (x : Nbar P G TI) :
    (baseImageEquiv P G hP root kernel regular thetaBar hPG x).val = eT x.val := rfl

def quotientBaseInsideEquiv : QuotientG G P ≃* inside (embeddedQuotientG G P) QI :=
  (quotientEquiv G P).trans (insideEquiv (embeddedQuotientG G P) QI
    (embedded_quotient_le_inertia P G hP root kernel regular thetaBar))

/-- The restricted inertia equivalence agrees with the independent,
projection-defined base equivalence on every element. -/
theorem base_triangle (x : Nbar P G TI) :
    baseImageEquiv P G hP root kernel regular thetaBar hPG x =
      quotientBaseInsideEquiv P G hP root kernel regular thetaBar
        (baseProjectionEquiv P G TI
          (base_le_inertia P G hP root kernel regular thetaBar) x) := by
  obtain ⟨g, rfl⟩ := baseProjectionHom_surjective P G TI
    (base_le_inertia P G hP root kernel regular thetaBar) x
  apply Subtype.ext
  apply Subtype.ext
  change qA P g.val =
    (quotientEquiv G P (baseProjectionEquiv P G TI
      (base_le_inertia P G hP root kernel regular thetaBar)
      (baseProjectionHom P G TI
        (base_le_inertia P G hP root kernel regular thetaBar) g)) : QuotientA P)
  rw [show baseProjectionEquiv P G TI
    (base_le_inertia P G hP root kernel regular thetaBar)
    (baseProjectionHom P G TI
      (base_le_inertia P G hP root kernel regular thetaBar) g) = qG G P g from
    baseProjectionEquiv_mk P G TI
      (base_le_inertia P G hP root kernel regular thetaBar) g]
  rfl

variable (W : CharacterWeight p K G)

def localAmbientImageEquiv : Hbar P G TI W ≃*
    inside (quotientRawInertia P G hP W) QI :=
  ((eT).subgroupMap (Hbar P G TI W)).trans
    (MulEquiv.subgroupCongr (local_image P G hP root kernel regular thetaBar W))

@[simp] theorem localAmbientImageEquiv_val (x : Hbar P G TI W) :
    (localAmbientImageEquiv P G hP root kernel regular thetaBar W x).val =
      eT x.val := rfl

/-- The intersection equivalence is induced by the same ambient map as
both restricted equivalences. -/
def localImageEquiv : Mbar P G TI W ≃*
    localBase (inside (embeddedQuotientG G P) QI)
      (inside (quotientRawInertia P G hP W) QI) :=
  (localBaseEquivIntersection (Nbar P G TI) (Hbar P G TI W)).trans
    (((eT).subgroupMap (Nbar P G TI ⊓ Hbar P G TI W)).trans
      ((MulEquiv.subgroupCongr (by
        change (Nbar P G TI ⊓ Hbar P G TI W).map (eT).toMonoidHom =
          inside (embeddedQuotientG G P) QI ⊓
            inside (quotientRawInertia P G hP W) QI
        rw [Subgroup.map_inf _ _ (eT).toMonoidHom (eT).injective,
          base_image P G hP root kernel regular thetaBar hPG,
          local_image P G hP root kernel regular thetaBar W])).trans
        (localBaseEquivIntersection (inside (embeddedQuotientG G P) QI)
          (inside (quotientRawInertia P G hP W) QI)).symm))

@[simp] theorem localImageEquiv_val (x : Mbar P G TI W) :
    (localImageEquiv P G hP root kernel regular thetaBar hPG W x).val.val =
      eT x.val.val := rfl

/-- The local equivalence commutes with the actual inclusion into the
second ambient group. -/
theorem local_ambient_triangle (x : Mbar P G TI W) :
    (localImageEquiv P G hP root kernel regular thetaBar hPG W x).val =
      localAmbientImageEquiv P G hP root kernel regular thetaBar W x.val := rfl

/-- The local equivalence is anchored to the same base equivalence. -/
theorem local_base_triangle (x : Mbar P G TI W) :
    (⟨(localImageEquiv P G hP root kernel regular thetaBar hPG W x).val.val,
      (localImageEquiv P G hP root kernel regular thetaBar hPG W x).property⟩ :
        inside (embeddedQuotientG G P) QI) =
      baseImageEquiv P G hP root kernel regular thetaBar hPG
        ⟨x.val.val, x.property⟩ := rfl

/-- On the original normalizer, the local triangle retains exactly the
qN projection already used to descend the ordinary weight character. -/
theorem local_normalizer_projection (hUT : U G W ≤ TI)
    (x : Subgroup.normalizer (W.subgroup : Set G)) :
    (localImageEquiv P G hP root kernel regular thetaBar hPG W
      (quotientLocalMap (Z P TI) (N G TI) (H G TI W)
        (normalizerTripleEquiv G TI W hUT x))).val.val.val =
      quotientEmbedding G P ((normalizerProjectionHom P G hP W x).val) := rfl

end ActualInertias

end ModularRep.PaperProofs.TypeBCentralKernelQuotientInertiaImages


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
