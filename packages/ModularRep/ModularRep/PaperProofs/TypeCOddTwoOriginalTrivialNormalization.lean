import ModularRep.PaperProofs.TypeCOddTwoOriginalChosenExtensions

/-!
# Both original trivial-radical normalizations on the chosen packets

The original ordinary normalization is stated from defect-zero characters
of the ambient group. The canonical quotient at Q=1 and injectivity of the
SAME local bijection convert it to the normalization for every character in
the trivial-radical part. The second normalization uses the SAME original
matched extensions, then their already computed reference transport.

No source law, compatible-root choice or full block witness is introduced.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeCOddTwoOriginalTrivialNormalization

open ModularRep CharacterWeight FDRepSimpleClassKZero
open CyclicOuterLemma37Concrete EvenFieldFLZSourceConditions
open EvenFieldFLZBAWGoodFamily OddTwoLiteralSpathTarget
open TypeCOddTwoOriginalBlockMatching TypeCOddTwoOriginalReferenceAmbient
open TypeCOddTwoOriginalChosenExtensions

universe u

variable {n : ℕ} {F : Type u} [Field F] [Finite F]
variable (P : Problem n F)

/-- The actual normalizer at the original trivial radical is all of X. -/
def oneNormalizerEquiv : P.Normalizer P.oneRadical ≃* X n F :=
  (MulEquiv.subgroupCongr (show
    Subgroup.normalizer (P.oneRadical.1 : Set (X n F)) = ⊤ by
      rw [P.oneRadical_eq_bot]
      exact Subgroup.normalizer_eq_top (H := (⊥ : Subgroup (X n F))))).trans Subgroup.topEquiv

/-- Quotient by the actual trivial subgroup followed by the actual inclusion. -/
def oneQuotientEquiv : NormalizerQuotient P.oneRadical.1 ≃* X n F :=
  ((QuotientGroup.quotientMulEquivOfEq (show
    P.oneRadical.1.subgroupOf (P.Normalizer P.oneRadical) = ⊥ by
      rw [P.oneRadical_eq_bot]
      exact Subgroup.bot_subgroupOf (G := X n F) (H := P.Normalizer P.oneRadical))).trans
        QuotientGroup.quotientBot).trans
    (oneNormalizerEquiv P)

@[simp] theorem oneQuotientEquiv_mk (x : P.Normalizer P.oneRadical) :
    oneQuotientEquiv P (QuotientGroup.mk x) = x.1 := rfl

/-- The ordinary character on X is the transport of this OWN quotient character. -/
def ambientOrdinary (theta : LocalDefectZeroCharacter (K := P.K) P.oneRadical) :
    OrdinaryIrreducibleCharacter.Irr P.K (X n F) :=
  OrdinaryIrreducibleCharacter.mapEquiv theta.1 (oneQuotientEquiv P)

theorem ambientOrdinary_value
    (theta : LocalDefectZeroCharacter (K := P.K) P.oneRadical)
    (x : P.Normalizer P.oneRadical) :
    ambientOrdinary P theta x.1 = theta.1 (QuotientGroup.mk x) := by
  change theta.1 ((oneQuotientEquiv P).symm x.1) = _
  exact congrArg theta.1 ((oneQuotientEquiv P).symm_apply_apply (QuotientGroup.mk x))

variable {P} (D : Definition41 P)

/-- The original existential normalization covers EVERY character in its
trivial-radical part, by injectivity of its own local equivalence. -/
theorem onePart_reduction (psi : D.map.Part P.oneRadical)
    (x : PrimeRegularElement (G := P.Normalizer P.oneRadical) 2) :
    P.inflatedOrdinary P.oneRadical (D.map.localMap P.oneRadical psi) x.1 =
      psi.1.1 (PrimeRegularElement.map (P.Normalizer P.oneRadical).subtype x) := by
  let theta := D.map.localMap P.oneRadical psi
  let chi := ambientOrdinary P theta
  have hdefect : IsDefectZeroOrdinaryCharacter 2 chi :=
    theta.2.mapEquiv (oneQuotientEquiv P)
  obtain ⟨eta, hred, hordinary⟩ := D.oneReduction chi hdefect
  have htheta : D.map.localMap P.oneRadical eta = theta := by
    apply Subtype.ext
    apply OrdinaryIrreducibleCharacter.ext
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective
      (P.oneRadical.1.subgroupOf (P.Normalizer P.oneRadical)) z
    exact (hordinary y).trans (ambientOrdinary_value P theta y)
  have heta : eta = psi := (D.map.localMap P.oneRadical).injective htheta
  subst eta
  exact (ambientOrdinary_value P theta x.1).symm.trans
    (hred (PrimeRegularElement.map (P.Normalizer P.oneRadical).subtype x))

/-- The subgroup equality identifies the actual radical, not merely its class. -/
theorem radical_eq_one (Q : RadicalSubgroup (p := 2) (G := X n F))
    (hQ : Q.1 = ⊥) : Q = P.oneRadical :=
  Subtype.ext (hQ.trans P.oneRadical_eq_bot.symm)

theorem trivialPart_reduction (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : D.map.Part Q) (hQ : Q.1 = ⊥)
    (x : PrimeRegularElement (G := P.Normalizer Q) 2) :
    P.inflatedOrdinary Q (D.map.localMap Q psi) x.1 =
      psi.1.1 (PrimeRegularElement.map (P.Normalizer Q).subtype x) := by
  have h := radical_eq_one (P := P) Q hQ
  subst Q
  exact onePart_reduction D psi x

/-- Use the original SAME-extension normalization at the equal radical. -/
theorem trivialPart_extensions (Q : RadicalSubgroup (p := 2) (G := X n F))
    (psi : D.map.Part Q) (hQ : Q.1 = ⊥)
    (x : PrimeRegularElement (G := P.LocalGroup (D.matched Q psi).ambient Q) 2) :
    (D.matched Q psi).extensions.localExtension.1.1 x =
      (D.matched Q psi).extensions.globalExtension.1.1
        (PrimeRegularElement.map (P.LocalGroup (D.matched Q psi).ambient Q).subtype x) := by
  have h := radical_eq_one (P := P) Q hQ
  subst Q
  exact D.oneExtensions psi x

variable (b : P.Block) (reference psi : Definition35Brauer (P.blockProblem b))

/-- The selected OWN ordinary character has the original Brauer reduction. -/
theorem selected_trivial_reduction
    (hQ : (selectedPair D b psi).subgroup = ⊥)
    (x : PrimeRegularElement (G := OwnNormalizer D b psi) 2) :
    (selectedPair D b psi).localCharacter (QuotientGroup.mk x.1) =
      psi.1.1 (PrimeRegularElement.map (OwnNormalizer D b psi).subtype x) := by
  have hcharacter := congrArg
    (fun theta : LocalDefectZeroCharacter (K := P.K)
      (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi) =>
        theta.1 (QuotientGroup.mk x.1)) (selectedLocalCharacter_eq D b psi)
  exact hcharacter.symm.trans (trivialPart_reduction D
    (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi)
    (selectedPart D b psi) hQ x)

/-- The same two extensions still coincide after actual reference transport. -/
theorem reference_trivial_extensions
    (hQ : (selectedPair D b psi).subgroup = ⊥) :
    PrimeRegularClassFunction.pullback (ReferenceLocalGroup D b reference psi).subtype
        (referenceExtensions D b reference psi).globalExtension.1.1 =
      (referenceExtensions D b reference psi).localExtension.1.1 := by
  apply PrimeRegularClassFunction.ext
  intro x
  exact (extension_equality_transport D b reference psi
    (trivialPart_extensions D
      (TypeCOddTwoOriginalBlockMatching.selectedRadical D b psi)
      (selectedPart D b psi) hQ) x).symm

end ModularRep.PaperProofs.TypeCOddTwoOriginalTrivialNormalization


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
