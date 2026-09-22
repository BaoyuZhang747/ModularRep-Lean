import ModularRep.PaperProofs.TypeBRankThreeNonprincipalBlockBinding
import ModularRep.PaperProofs.TypeBRankThreeNonprincipalSeriesBinding
import ModularRep.PaperProofs.TypeBRankThreeNonprincipalBonnafeBinding

/-!
# The actual nonprincipal rank-three block and proper rational Levi deduction

This is the first nonprincipal deduction in prop:type-b-two-rank-three.
The primal Spin block, specified two-regular dual label, projective-image
membership and odd symplectic lift are all constructed. The algebraic
Bonnafe certificate is applied through the same injective coordinate base
change; the specified identity-label principle is derived from the full
Broue--Michel union. Their contradiction gives non-quasi-isolation.
Dimension and common-torus intersections then construct the least proper
Frobenius-stable Levi containing the displayed centralizer product.

No blockwise criterion, iBAW, chosen proper Levi or non-quasi-isolation
conclusion is supplied. The actual ordinary family, coefficient system,
algebraic-point and geometric-source interpretations remain explicit.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBCentralKernelBlockSource
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalBlockBinding
open TypeBRankThreeNonprincipalSeriesBinding TypeBRankThreeNonprincipalDualLift
open TypeBRankThreeNonprincipalGeometry TypeBRankThreeNonprincipalBonnafeBinding

variable {p f : ℕ} {F A K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  (parameters : OddFieldParameters F p f) (N : NormSource 3 F)
  (orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) N)
  [Finite (Spin 3 F N)]
  (Msys : ModularSystem 2 K O k)
  (iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N))


variable
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 3 F N) => b.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : OrdinaryBlockSource Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks)
  (series : Sources parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary)
  (frobenius : FrobeniusSource p f A)
  (points : RationalPointSource F A p f frobenius)
  (geometry : GeometrySource F A p f frobenius points)

/-- The actual output data and equations of this manuscript deduction. -/
structure ManuscriptReduction
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F)) where
  spinBlock : LiteralPrimitiveBlock k (Spin 3 F N)
  image : MonoidAlgebra.mapDomainAlgHom k k
    (TypeBCliffordOrthogonalSourceBinding.spinProjection
      3 F parameters (by decide) N orthogonal) spinBlock.val = b.val
  nonprincipal : ¬ IsPrincipal spinBlock
  domination_unique : ∀ c : LiteralPrimitiveBlock k (Spin 3 F N),
    MonoidAlgebra.mapDomainAlgHom k k
      (TypeBCliffordOrthogonalSourceBinding.spinProjection
        3 F parameters (by decide) N orthogonal) c.val = b.val → c = spinBlock
  label : PCSp F 3
  associated : Associated parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series spinBlock label
  defining_regular : p.Coprime (orderOf label)
  odd_order : Odd (orderOf label)
  projective_image : label ∈ projectiveSymplecticSubgroup F
  oddLift : Sp F
  lift_value : symplecticProjection F oddLift = label
  lift_odd : Odd (orderOf oddLift)
  lift_unique : ∀ x : Sp F, symplecticProjection F x = label →
    Odd (orderOf x) → x = oddLift
  not_quasi : ¬ geometry.QuasiIsolated (points.rationalEmbedding label)
  not_strict : ¬ geometry.StrictlyQuasiIsolated (points.rationalEmbedding label)
  levi : Subgroup (PCSp A 3)
  levi_isLevi : geometry.IsLevi levi
  centralizer_containment :
    (geometry.connectedCentralizer (points.rationalEmbedding label) : Set (PCSp A 3)) *
      (finiteCentralizer frobenius (points.rationalEmbedding label) : Set (PCSp A 3)) ⊆ levi
  levi_proper : levi ≠ ⊤
  levi_frobenius : levi.map (Phi frobenius).toMonoidHom = levi
  levi_least : ∀ M : Subgroup (PCSp A 3), geometry.IsLevi M →
    geometry.H (points.rationalEmbedding label) ≤ M → levi ≤ M

/-- Construct the actual block/label/lift and its proper rational Levi. -/
theorem nonprincipal_rank_three_source_instantiated
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 p f F N)
    (navarro : NavarroCentralBlockPrinciple 2 k)
    (bonnafe : AlgebraicBonnafeCertificate p f F A parameters frobenius points geometry)
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    (nonprincipal : ¬ IsPrincipal b) :
    Nonempty (ManuscriptReduction parameters N orthogonal Msys iota blocks ordinary
      series frobenius points geometry b) := by
  let bhat := dominatingBlock parameters N orthogonal centre navarro b
  have nonprincipal_up : ¬ IsPrincipal bhat :=
    dominatingBlock_nonprincipal parameters N orthogonal centre navarro b nonprincipal
  let s := TypeBRankThreeNonprincipalSeriesBinding.label
    parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series bhat
  have associated : Associated parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series bhat s :=
    label_associated parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series bhat
  have regular : p.Coprime (orderOf s) :=
    label_defining_regular parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series bhat
  have odd : Odd (orderOf s) :=
    Nat.coprime_two_right.mp
      (label_two_prime parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series bhat)
  have htwo : (2 : F) ≠ 0 := by
    intro h
    have div : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp h
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2)
      (parameters.prime.odd_iff.mp parameters.odd) div
  have inImage : s ∈ projectiveSymplecticSubgroup F :=
    odd_mem_projectiveSymplectic F odd
  let imageParameter : PSp F := ⟨s, inImage⟩
  have imageOdd : Odd (orderOf imageParameter) := by
    simpa only [imageParameter, Subgroup.orderOf_mk] using odd
  have identityPrincipal :
      TypeBQuasiIsolation.IdentityLabelPrincipalBlockInterface
        (fun c (t : PSp F) =>
          Associated parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series c (t : PCSp F 3))
        IsPrincipal := by
    intro c hc
    exact identity_label_principal parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series hc
  have notRegularQuasi :
      ¬ (p.Coprime (orderOf (imageParameter : PCSp F 3)) ∧
        geometry.QuasiIsolated (points.rationalEmbedding (imageParameter : PCSp F 3))) :=
    (centralDoubleCover F htwo).nonprincipal_label_not_quasiIsolated
      (IsAssociated := fun (c : LiteralPrimitiveBlock k (Spin 3 F N)) (t : PSp F) =>
        Associated parameters Msys iota (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks ordinary series c (t : PCSp F 3))
      (IsPrincipalBlock := IsPrincipal) (b := bhat) (s := imageParameter)
      (bonnafe_projection_interface points parameters geometry bonnafe htwo)
      identityPrincipal associated imageOdd nonprincipal_up
  have notQuasi : ¬ geometry.QuasiIsolated (points.rationalEmbedding s) := by
    intro h
    exact notRegularQuasi ⟨regular, h⟩
  have notStrict : ¬ geometry.StrictlyQuasiIsolated (points.rationalEmbedding s) :=
    geometry.not_strictlyQuasiIsolated_of_not_quasiIsolated _ notQuasi
  obtain ⟨shat, hshat, unique⟩ := existsUnique_odd_symplectic_lift F htwo odd
  obtain ⟨L, isLevi, contains, proper, stable, least⟩ :=
    geometry.exists_proper_rational_levi s regular.symm notStrict
  exact ⟨{
    spinBlock := bhat
    image := dominatingBlock_image parameters N orthogonal centre navarro b
    nonprincipal := nonprincipal_up
    domination_unique := fun c hc =>
      dominatingBlock_unique parameters N orthogonal centre navarro b c hc
    label := s
    associated := associated
    defining_regular := regular
    odd_order := odd
    projective_image := inImage
    oddLift := shat
    lift_value := hshat.1
    lift_odd := hshat.2
    lift_unique := fun x hx ho => unique x ⟨hx, ho⟩
    not_quasi := notQuasi
    not_strict := notStrict
    levi := L
    levi_isLevi := isLevi
    centralizer_containment :=
      (geometry.centralizerProduct_subset_iff (points.rationalEmbedding s) L).mpr contains
    levi_proper := proper
    levi_frobenius := stable
    levi_least := least
  }⟩

end ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
