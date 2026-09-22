import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSupportedIrreducibleCovering
import ModularRep.BrauerCharacterHomPullback
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignBrauer

/-! An actual irreducible extension and its quotient-sign twist meet every
covering block at index two in odd characteristic. The same construction
returns its explicit characteristic-zero quotient twist from the proved
Brauer sign formula. -/

noncomputable section
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedBrauerExtension

open ModularRep ModularRep.FDRepSimpleClassKZero
open Representation.Extension
open SporadicFi24P3Definition44NamedCarrierLinearCharacterAlgebra
open SporadicFi24P3Definition44NamedCarrierQuotientSignAlgebra
open SporadicFi24P3Definition44NamedCarrierCentralAlgebraScalar
open SporadicFi24P3Definition44NamedCarrierSupportedIrreducibleCovering
open SporadicFi24P3Definition44NamedCarrierSignBrauer

universe u

local instance subgroupFintype {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) : Fintype N := Fintype.ofFinite _

theorem exists_twisted_extension_in_covering_block_of_index_two
    {p : ℕ} {k K G V I J : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group G] [Fintype G] [Fintype I] [Fintype J]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0)
    (N : Subgroup G) [N.Normal] (hindex : N.index = 2)
    (iotaG : PrimeRegularRootEmbedding p k K G)
    (iotaN : PrimeRegularRootEmbedding p k K N)
    (rootAgreement : ∀ zeta : rootsOfUnity (primeRegularExponent p N) k,
      iotaN.lift (((zeta : kˣ) : k)) = iotaG.lift (((zeta : kˣ) : k)))
    {eG : I → k[G]} {eN : J → k[N]}
    (blocksG : BlockIdempotentDecomposition eG)
    (blocksN : BlockIdempotentDecomposition eN)
    (injG : IrreducibleBrauerCharacterInjectivity iotaG)
    (injN : IrreducibleBrauerCharacterInjectivity iotaN)
    (catalogueG : BlockCentralCharacterCatalogue blocksG)
    (catalogueN : BlockCentralCharacterCatalogue blocksN)
    (B : I) (phi : IBr iotaN)
    (initial : BrauerCharacterExtensionWitness iotaG iotaN phi)
    (sigma : Representation k G V) (rho : Representation k N V)
    [sigma.IsIrreducible] [rho.IsIrreducible]
    (hres : sigma.pullback N.subtype = rho)
    (hInitial : initial.val.val = sigma.brauerCharacterOfRootEmbedding iotaG)
    (hBase : phi.val = rho.brauerCharacterOfRootEmbedding iotaN)
    (hcover : CentralCharacterCovers N (catalogueG.centralCharacter B)
      (catalogueN.centralCharacter
        (irreducibleBrauerCharacterBlock iotaN injN blocksN phi))) :
    ∃ (selected : BrauerCharacterExtensionWitness iotaG iotaN phi)
      (lambda : (G ⧸ N) →* Kˣ),
      irreducibleBrauerCharacterBlock iotaG injG blocksG selected.val = B ∧
      ∀ x : PrimeRegularElement (G := G) p,
        selected.val.val x = (lambda (QuotientGroup.mk' N x.val) : K) * initial.val.val x := by
  classical
  let sign := quotientSign (k := k) N hindex
  let signed : Representation.Extension N rho :=
    { representation := sigma.linearCharacterTwist sign
      restrictionEquiv := Representation.Equiv.mk (LinearEquiv.refl k V) (by
        intro n
        ext v
        change (sign (n : G) : k) • sigma (n : G) v = rho n v
        have hs : sign (n : G) = 1 := quotientSign_mem N hindex n n.property
        rw [hs, Units.val_one, one_smul]
        exact congrArg (fun r : Representation k N V => r n v) hres) }
  let selectedSign := brauerCharacterExtensionWitnessOfCompatible
    signed (inferInstance : rho.IsIrreducible) iotaG iotaN phi hBase.symm
    (Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      signed.representation iotaG iotaN N.subtype rootAgreement)
  let : signed.representation.IsIrreducible :=
    signed.representation_isIrreducible (inferInstance : rho.IsIrreducible)
  have hSign : selectedSign.val.val =
      signed.representation.brauerCharacterOfRootEmbedding iotaG := rfl
  let b0 := irreducibleBrauerCharacterBlock iotaG injG blocksG initial.val
  let bT := irreducibleBrauerCharacterBlock iotaG injG blocksG selectedSign.val
  let e := blocksG.blockIdempotentInCenter B
  have he : IsIdempotentElem e := by
    change e * e = e
    apply Subtype.ext
    exact (blocksG.primitive B).idempotent.eq
  have hInitialCover := centralCharacterCovers_of_literal_restriction
    N iotaG iotaN blocksG blocksN injG injN catalogueG catalogueN
    initial.val phi sigma rho hres hInitial hBase
  have hz := centerSign_trace_supported N hindex e
  have htrace : catalogueG.centralCharacter b0 (e + centerSign N hindex e) =
      catalogueG.centralCharacter B (e + centerSign N hindex e) :=
    (hInitialCover _ hz).trans (hcover _ hz).symm
  have ht : catalogueG.centralCharacter b0 (e + centerSign N hindex e) ≠ 0 := by
    rw [htrace]
    exact idempotent_trace_ne_zero h2 (catalogueG.centralCharacter B)
      (centerSign N hindex).toAlgHom e he (catalogueG.centralCharacter_own B)
  have hchoice : catalogueG.centralCharacter b0 e ≠ 0 ∨
      catalogueG.centralCharacter b0 (centerSign N hindex e) ≠ 0 := by
    by_cases h0 : catalogueG.centralCharacter b0 e = 0
    · right
      intro h1
      apply ht
      rw [map_add, h0, h1, zero_add]
    · exact Or.inl h0
  rcases hchoice with h0 | h1
  · refine ⟨initial, 1, ?_, ?_⟩
    · change b0 = B
      by_contra hne
      exact h0 (catalogueG.centralCharacter_other hne)
    · intro x
      simp only [MonoidHom.one_apply, Units.val_one, one_mul]
  · have hscalar : catalogueG.centralCharacter bT e =
        catalogueG.centralCharacter b0 (centerSign N hindex e) := by
      apply scalar_id_injective sigma
      calc
        _ = signed.representation.asAlgebraHom e.val :=
          (catalogue_action_of_affording iotaG injG blocksG catalogueG
            selectedSign.val signed.representation hSign e).symm
        _ = sigma.asAlgebraHom (centerSign N hindex e).val :=
          twisted_algebra_action sigma sign e.val
        _ = _ := catalogue_action_of_affording iotaG injG blocksG catalogueG
          initial.val sigma hInitial (centerSign N hindex e)
    refine ⟨selectedSign, quotientSignCharacter N hindex, ?_, ?_⟩
    · change bT = B
      by_contra hne
      exact h1 (hscalar.symm.trans (catalogueG.centralCharacter_other hne))
    · intro x
      rw [hSign, hInitial]
      exact brauerCharacter_sign_twist iotaG h2 N hindex sigma x

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierSignedBrauerExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
