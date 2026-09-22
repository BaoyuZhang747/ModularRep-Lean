import ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

/-!
# Standard block-triple transport through actual group coordinates

MRR (2026), Definitions 3.2 and 3.4, pp.340--341, define the standard
central/block-isomorphism relation using actual subgroup, character,
centralizer, defect and intermediate block-induction data. Simultaneous
renaming through a group isomorphism preserves that definition.
Lemma 3.6(ii), p.342, explicitly records the automorphism special case.
The different-group statement below is licensed by the definitions, not
misquoted as the printed scope of that lemma.

The universal source interface is independent of any principal carrier,
FM map, FLZ predicate or orbit. Its input computes both character-domain
maps from ONE whole-group equivalence and exact base/local subgroup
images. Compatible roots and the actual character pullbacks are retained.
Its iff asserts neither relation; it is licensed only for the authentic
standard meaning of BlockTripleSourceSemantics. No source instance is
claimed and no projective-representation foundations are reconstructed.
-/

noncomputable section

namespace ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport

open ModularRep
open ModularRep.PaperProofs.NormalCoreLemma48SourceInstantiation
open ModularRep.PaperProofs.OddTwoCentralTwoRelationInflation

universe u

variable {p : ℕ} {k K : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- Actual simultaneous coordinates on the two displayed subgroup pairs.
The maps on their character domains are computed below, not freely chosen.
-/
structure GroupCoordinates (T U : BlockTripleArguments p k K) where
  ambient : T.G ≃* U.G
  map_base : T.N.map ambient.toMonoidHom = U.N
  map_local : T.H.map ambient.toMonoidHom = U.H

namespace GroupCoordinates

variable {T U : BlockTripleArguments p k K} (C : GroupCoordinates T U)

/-- The same whole-group equivalence identifies the actual intersection. -/
theorem map_intersection :
    (T.N ⊓ T.H).map C.ambient.toMonoidHom = U.N ⊓ U.H := by
  rw [Subgroup.map_inf _ _ _ C.ambient.injective, C.map_base, C.map_local]

/-- Canonical restriction to the actual normal base. -/
def baseEquiv : T.N ≃* U.N :=
  (C.ambient.subgroupMap T.N).trans (MulEquiv.subgroupCongr C.map_base)

/-- Canonical restriction to the actual local ambient subgroup. -/
def localEquiv : T.H ≃* U.H :=
  (C.ambient.subgroupMap T.H).trans (MulEquiv.subgroupCongr C.map_local)

/-- Canonical restriction to the OWN local character domain N intersect H. -/
def intersectionEquiv : ↥(T.N ⊓ T.H) ≃* ↥(U.N ⊓ U.H) :=
  (C.ambient.subgroupMap (T.N ⊓ T.H)).trans
    (MulEquiv.subgroupCongr C.map_intersection)

@[simp] theorem baseEquiv_ambient (x : T.N) :
    (C.baseEquiv x : U.G) = C.ambient (x : T.G) := rfl

@[simp] theorem localEquiv_ambient (x : T.H) :
    (C.localEquiv x : U.G) = C.ambient (x : T.G) := rfl

@[simp] theorem intersectionEquiv_ambient (x : ↥(T.N ⊓ T.H)) :
    (C.intersectionEquiv x : U.G) = C.ambient (x : T.G) := rfl

/-- A previously computed base equivalence with this actual ambient
square is the canonical restriction. No comparison equality is assumed. -/
theorem baseEquiv_eq_of_ambient (eN : T.N ≃* U.N)
    (square : ∀ x : T.N, (eN x : U.G) = C.ambient (x : T.G)) :
    C.baseEquiv = eN := by
  apply MulEquiv.ext
  intro x
  exact Subtype.ext ((C.baseEquiv_ambient x).trans (square x).symm)

theorem localEquiv_eq_of_ambient (eH : T.H ≃* U.H)
    (square : ∀ x : T.H, (eH x : U.G) = C.ambient (x : T.G)) :
    C.localEquiv = eH := by
  apply MulEquiv.ext
  intro x
  exact Subtype.ext ((C.localEquiv_ambient x).trans (square x).symm)

/-- The own-character map is fixed by the same actual ambient square. -/
theorem intersectionEquiv_eq_of_ambient
    (eM : ↥(T.N ⊓ T.H) ≃* ↥(U.N ⊓ U.H))
    (square : ∀ x : ↥(T.N ⊓ T.H), (eM x : U.G) = C.ambient (x : T.G)) :
    C.intersectionEquiv = eM := by
  apply MulEquiv.ext
  intro x
  exact Subtype.ext ((C.intersectionEquiv_ambient x).trans (square x).symm)

end GroupCoordinates

/-- Definition-shaped transport of the SAME actual character pair.
Root compatibility is target-root first and source-root second, along
the computed forward subgroup maps. It is required for every actual
target representation, not inferred from equal character values.

No equality of whole zero-extended root lifts is required. The source
relation itself retains all usual character-triple and block conditions.
-/
structure TupleIsomorphism (T U : BlockTripleArguments p k K) where
  coordinates : GroupCoordinates T U
  theta_root_compatible : ∀ V : FDRep k U.N,
    Representation.BrauerRootLiftCompatibleAlong V.ρ U.iotaN T.iotaN
      coordinates.baseEquiv.toMonoidHom
  phi_root_compatible : ∀ V : FDRep k ↥(U.N ⊓ U.H),
    Representation.BrauerRootLiftCompatibleAlong V.ρ U.iotaM T.iotaM
      coordinates.intersectionEquiv.toMonoidHom
  theta_values : ∀ x : PrimeRegularElement (G := T.N) p,
    T.theta.1 x = U.theta.1 (PrimeRegularElement.map coordinates.baseEquiv.toMonoidHom x)
  phi_values : ∀ x : PrimeRegularElement (G := ↥(T.N ⊓ T.H)) p,
    T.phi.1 x = U.phi.1
      (PrimeRegularElement.map coordinates.intersectionEquiv.toMonoidHom x)

namespace TupleIsomorphism

variable {T U : BlockTripleArguments p k K}

/-- K adapter for existing displayed base and own-normalizer coordinates.
The actual ambient squares identify their maps with the computed ones;
the same roots and characters are then reused verbatim. -/
def ofDisplayed (C : GroupCoordinates T U)
    (eN : T.N ≃* U.N) (eM : ↥(T.N ⊓ T.H) ≃* ↥(U.N ⊓ U.H))
    (base_square : ∀ x : T.N, (eN x : U.G) = C.ambient (x : T.G))
    (intersection_square : ∀ x : ↥(T.N ⊓ T.H),
      (eM x : U.G) = C.ambient (x : T.G))
    (theta_roots : ∀ V : FDRep k U.N,
      Representation.BrauerRootLiftCompatibleAlong V.ρ U.iotaN T.iotaN eN.toMonoidHom)
    (phi_roots : ∀ V : FDRep k ↥(U.N ⊓ U.H),
      Representation.BrauerRootLiftCompatibleAlong V.ρ U.iotaM T.iotaM eM.toMonoidHom)
    (theta_values : ∀ x : PrimeRegularElement (G := T.N) p,
      T.theta.1 x = U.theta.1 (PrimeRegularElement.map eN.toMonoidHom x))
    (phi_values : ∀ x : PrimeRegularElement (G := ↥(T.N ⊓ T.H)) p,
      T.phi.1 x = U.phi.1 (PrimeRegularElement.map eM.toMonoidHom x)) :
    TupleIsomorphism T U where
  coordinates := C
  theta_root_compatible := by
    simpa only [C.baseEquiv_eq_of_ambient eN base_square] using theta_roots
  phi_root_compatible := by
    simpa only [C.intersectionEquiv_eq_of_ambient eM intersection_square] using phi_roots
  theta_values := by
    simpa only [C.baseEquiv_eq_of_ambient eN base_square] using theta_values
  phi_values := by
    simpa only [C.intersectionEquiv_eq_of_ambient eM intersection_square] using phi_values

/-- The pointwise global-character equation is the actual class-function
pullback identity used to interpret simultaneous tuple transport. -/
theorem theta_pullback (I : TupleIsomorphism T U) :
    T.theta.1 = pullbackPrimeRegularClassFunction
      I.coordinates.baseEquiv.toMonoidHom U.theta.1 := by
  ext x
  exact I.theta_values x

/-- The local pullback retains the character on N intersect H. -/
theorem phi_pullback (I : TupleIsomorphism T U) :
    T.phi.1 = pullbackPrimeRegularClassFunction
      I.coordinates.intersectionEquiv.toMonoidHom U.phi.1 := by
  ext x
  exact I.phi_values x

end TupleIsomorphism

/-- E1/E2 interpretation of the AUTHENTIC standard block-triple definition
under simultaneous actual coordinates. This universal iff asserts neither
side. It is not an instance for an arbitrary weaker Prop-valued predicate.

MRR Definitions 3.2/3.4 license simultaneous isomorphism transport;
Lemma 3.6(ii) explicitly states the automorphism case. Invariance of the
character triples, centralizers, local defect data and every intermediate
block-induction condition belongs to that standard interpretation.
-/
structure StandardTransportSource (standard : BlockTripleSourceSemantics p k K) : Prop where
  relation_iff : ∀ (T U : BlockTripleArguments p k K), TupleIsomorphism T U →
    (standard.blockIsomorphic T ↔ standard.blockIsomorphic U)

namespace StandardTransportSource

variable {standard : BlockTripleSourceSemantics p k K}

/-- K consumes the universal source only after the exact actual packet
has been supplied. No relation is obtained without the input relation. -/
theorem transport (source : StandardTransportSource standard)
    {T U : BlockTripleArguments p k K} (I : TupleIsomorphism T U)
    (h : standard.blockIsomorphic T) : standard.blockIsomorphic U :=
  (source.relation_iff T U I).mp h

/-- The same definition interpretation also supports the reverse use
of these fixed coordinates, without a separately assumed covariance. -/
theorem reflect (source : StandardTransportSource standard)
    {T U : BlockTripleArguments p k K} (I : TupleIsomorphism T U)
    (h : standard.blockIsomorphic U) : standard.blockIsomorphic T :=
  (source.relation_iff T U I).mpr h

end StandardTransportSource

end ModularRep.PaperProofs.OddTwoStandardBlockTripleTransport


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
