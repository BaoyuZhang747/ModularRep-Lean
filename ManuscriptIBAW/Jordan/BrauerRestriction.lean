import ManuscriptIBAW.Jordan.Restriction
import ModularRep.PaperProofs.EvenFieldAssumption53Relative

/-!
# Restriction of the Brauer hypothesis to a subgroup

All characters are in the original `IBr iota`. The field stabiliser is
computed from its stated action. The restricted extension uses the image
of `(A)_psi`, namely `A ⊓ E_psi`, inside the original acting group.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan

open ModularRep
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

variable {ell : ℕ} {k K G D E : Type*}
  [Field k] [Field K] [Group G] [Finite G] [Group D] [Group E]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (iota : PrimeRegularRootEmbedding ell k K G)
  (phi : E →* MulAut G)

section ArbitraryActions

variable [MulAction D (IBr iota)] [MulAction E (IBr iota)]

/-- The stabiliser and extension data for the full acting group, on the same
irreducible Brauer character. -/
structure FullRepresentative (psi : IBr iota) where
  factorization : ProductStabilizerFactorization (D := D) (E := E) psi
  module : FDRep k G
  irreducible : Representation.IsIrreducible module.ρ
  character_eq : psi.val = Representation.brauerCharacterOfRootEmbedding module.ρ iota
  extension : SemidirectExtension phi (MulAction.stabilizer E psi) module.ρ

/-- Restriction changes only the outer acting group. The character,
representation, root convention and inclusion of the base group stay the
same. -/
structure RestrictedRepresentative (A : Subgroup E) (psi : IBr iota) where
  factorization : letI := restrictedAction (X := IBr iota) A
    ProductStabilizerFactorization (D := D) (E := A) psi
  module : FDRep k G
  irreducible : Representation.IsIrreducible module.ρ
  character_eq : psi.val = Representation.brauerCharacterOfRootEmbedding module.ρ iota
  extension : SemidirectExtension phi (A ⊓ MulAction.stabilizer E psi) module.ρ

/-- Restrict the extension using the same orbit representative and affording
representation. -/
def FullRepresentative.restrict {psi : IBr iota}
    (W : FullRepresentative (D := D) iota phi psi) (A : Subgroup E) :
    RestrictedRepresentative (D := D) iota phi A psi where
  factorization := product_factorization_restrict A psi W.factorization
  module := W.module
  irreducible := W.irreducible
  character_eq := W.character_eq
  extension := W.extension.restrict inf_le_right

theorem RestrictedRepresentative.extension_irreducible
    {A : Subgroup E} {psi : IBr iota}
    (W : RestrictedRepresentative (D := D) iota phi A psi) :
    Representation.IsIrreducible W.extension.representation :=
  W.extension.isIrreducible W.irreducible

/-- The statement covers every orbit under the regular group, including
characters outside any particular semisimple series. -/
def FullBrauerHypothesis : Prop :=
  ∀ psi0 : IBr iota, ∃ psi : IBr iota,
    psi ∈ MulAction.orbit D psi0 ∧
      Nonempty (FullRepresentative (D := D) iota phi psi)

def RestrictedBrauerHypothesis (A : Subgroup E) : Prop :=
  ∀ psi0 : IBr iota, ∃ psi : IBr iota,
    psi ∈ MulAction.orbit D psi0 ∧
      Nonempty (RestrictedRepresentative (D := D) iota phi A psi)

/-- Restrict the hypothesis for the full field group to a chosen subgroup. -/
theorem fullBrauerHypothesis_restrict (A : Subgroup E)
    (h : FullBrauerHypothesis (D := D) iota phi) :
    RestrictedBrauerHypothesis (D := D) iota phi A := by
  intro psi0
  obtain ⟨psi, horbit, ⟨W⟩⟩ := h psi0
  exact ⟨psi, horbit, ⟨FullRepresentative.restrict iota phi W A⟩⟩

end ArbitraryActions

end ManuscriptIBAW.Jordan

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
