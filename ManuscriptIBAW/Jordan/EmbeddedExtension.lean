import ManuscriptIBAW.Jordan.BrauerRestriction
import ModularRep.CyclicOuterBrauerExtension

/-!
The theorem for even characteristic uses the copy of the base group inside
its full stabiliser. The homomorphism below is constructed in semidirect
product coordinates and commutes with the base group inclusions. Pullback
therefore preserves the original root convention and Brauer character.
-/

noncomputable section

namespace ManuscriptIBAW.Jordan

open ModularRep Formalisation
open ModularRep.ManuscriptVerification.CyclicOuterBAW
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.ManuscriptVerification.StabilizerFactorizationTransport

section StabilizerMap

variable {G E X : Type} [Group G] [Group E]
  [MulAction G X] [MulAction E X]
  (phi : E →* MulAut G)
  (compatible : SemidirectActionCompatible (X := X) phi)
  (x : X) (hleft : ∀ g : G, g • x = x)

def semidirectToStabilizer :
    letI := semidirectMulAction phi compatible
    (G ⋊[phi.comp (MulAction.stabilizer E x).subtype] MulAction.stabilizer E x) →*
      semidirectStabilizer (phi := phi) x := by
  letI := semidirectMulAction phi compatible
  let inclusion :
      (G ⋊[phi.comp (MulAction.stabilizer E x).subtype] MulAction.stabilizer E x) →*
        (G ⋊[phi] E) := SemidirectProduct.map (MonoidHom.id G)
    (MulAction.stabilizer E x).subtype (by intro e; rfl)
  exact inclusion.codRestrict (semidirectStabilizer (phi := phi) x) (by
    intro g
    change g.left • ((g.right : E) • x) = x
    rw [g.right.property]
    exact hleft g.left)

end StabilizerMap

section Brauer

variable {ell : ℕ} {k K G D E : Type}
  [Field k] [Field K] [Group G] [Finite G] [Group D] [Group E] [Finite E]
  [CharP k ell] [IsAlgClosed k] [CharZero K]
  (iota : PrimeRegularRootEmbedding ell k K G)
  (phi : E →* MulAut G)
  [MulAction D (IBr iota)]

/-- Transport the embedded extension to the specified semidirect product,
preserving its equation for the original roots. -/
theorem fullRepresentative_of_embedded (psi : IBr iota) :
    letI := rightAutomorphismAction (X := IBr iota) (MulAut.conj : G →* MulAut G)
    letI := rightAutomorphismAction (X := IBr iota) phi
    let compatible := rightAutomorphismSemidirectCompatible (X := IBr iota) phi
    letI := semidirectMulAction phi compatible
    let hinner : ∀ g : G,
        (SemidirectProduct.inl g : G ⋊[phi] E) • psi = psi := fun g ↦ by
      rw [semidirect_inl_smul]
      exact ModularRep.PaperProofs.CyclicOuterLemma37Concrete.inner_fixes_ibr iota g psi
    let eG := canonicalHToEmbeddedEquiv psi hinner
    ProductStabilizerFactorization (D := D) (E := E) psi →
    (∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi),
      Representation.IsIrreducible W.ρ ∧
      pullbackPrimeRegularAlongEquiv eG psi.val =
        Representation.brauerCharacterOfRootEmbedding W.ρ (iota.alongMulEquiv eG) ∧
      Nonempty (Representation.Extension (embeddedHStabilizer (phi := phi) psi) W.ρ)) →
    Nonempty (FullRepresentative (D := D) iota phi psi) := by
  letI := rightAutomorphismAction (X := IBr iota) (MulAut.conj : G →* MulAut G)
  letI := rightAutomorphismAction (X := IBr iota) phi
  let compatible := rightAutomorphismSemidirectCompatible (X := IBr iota) phi
  letI := semidirectMulAction phi compatible
  have hleft : ∀ g : G, g • psi = psi :=
    fun g ↦ ModularRep.PaperProofs.CyclicOuterLemma37Concrete.inner_fixes_ibr iota g psi
  have hinner : ∀ g : G,
      (SemidirectProduct.inl g : G ⋊[phi] E) • psi = psi := by
    intro g
    rw [semidirect_inl_smul]
    exact hleft g
  let eG := canonicalHToEmbeddedEquiv psi hinner
  dsimp only
  intro factorization embedded
  obtain ⟨W, hW, hchar, ⟨extension⟩⟩ := embedded
  let V : FDRep k G := FDRep.of (Representation.pullback W.ρ eG.toMonoidHom)
  have hV : Representation.IsIrreducible V.ρ := hW.pullback _ eG.surjective
  have hcharacter : psi.val = Representation.brauerCharacterOfRootEmbedding V.ρ iota := by
    change psi.val = Representation.brauerCharacterOfRootEmbedding
      (Representation.pullback W.ρ eG.toMonoidHom) iota
    rw [Representation.brauerCharacterOfRootEmbedding_pullback_of_lift_eq
      W.ρ (iota.alongMulEquiv eG) iota eG.toMonoidHom
      (funext fun z => (iota.alongMulEquiv_lift eG z).symm)]
    apply PrimeRegularClassFunction.ext
    intro x
    have hx := congrArg (fun chi : PrimeRegularClassFunction K
      (embeddedHStabilizer (phi := phi) psi) ell =>
        chi (PrimeRegularElement.map eG.toMonoidHom x)) hchar
    change psi.val (PrimeRegularElement.map eG.symm.toMonoidHom
        (PrimeRegularElement.map eG.toMonoidHom x)) = _ at hx
    have hsquare : PrimeRegularElement.map eG.symm.toMonoidHom
        (PrimeRegularElement.map eG.toMonoidHom x) = x := by
      apply Subtype.ext
      exact eG.symm_apply_apply x.val
    rw [hsquare] at hx
    exact hx
  let inclusion := semidirectToStabilizer phi compatible psi hleft
  refine ⟨{
    factorization := factorization
    module := V
    irreducible := hV
    character_eq := hcharacter
    extension := {
      representation := extension.representation.pullback inclusion
      restrictionEquiv := ?_ } }⟩
  exact extension.restrictionEquiv.pullback eG.toMonoidHom

end Brauer

end ManuscriptIBAW.Jordan

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
