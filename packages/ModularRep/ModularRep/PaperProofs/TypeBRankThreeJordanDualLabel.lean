import ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication

/-!
The same nonprincipal dual label, as an actual rational point of the retained
Levi. Membership follows from the existing centralizer containment. The
rational embedding and subgroup inclusions preserve the original element
and its order. The dual carrier remains the projective conformal symplectic
quotient throughout.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreeJordanDualLabel

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBCentralKernelBlockSource
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBRankThreeNonprincipalGeometry TypeBRankThreeNonprincipalApplication
open TypeBRegularLeviRationalCarriers

variable {p f : ℕ} {F A K O k : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  [Field K] [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharZero K] [CharP k 2] [IsAlgClosed k]
  {parameters : OddFieldParameters F p f} {N : NormSource 3 F}
  {orthogonal : TypeBCliffordOrthogonalSourceBinding.Source
    3 F p f parameters (by decide) N}
  [Finite (Spin 3 F N)]
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin 3 F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  {blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 3 F N) => b.val)}
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  {ordinary : OrdinaryBlockSource Msys iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota) blocks}
  {series : Sources parameters Msys iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    blocks ordinary}
  {frobenius : FrobeniusSource p f A}
  {points : RationalPointSource F A p f frobenius}
  {geometry : GeometrySource F A p f frobenius points}
  {b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F)}
  (r : ManuscriptReduction parameters N orthogonal Msys iota blocks ordinary
    series frobenius points geometry b)

/-- The rational label belongs to its own actual finite centralizer. -/
theorem label_mem_finiteCentralizer :
    points.rationalEmbedding r.label ∈
      finiteCentralizer frobenius (points.rationalEmbedding r.label) := by
  constructor
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact points.rationalEmbedding_fixed r.label

/-- The displayed centralizer product already forces membership in this Levi. -/
theorem label_mem_levi : points.rationalEmbedding r.label ∈ r.levi := by
  exact r.centralizer_containment
    ⟨1, (geometry.connectedCentralizer (points.rationalEmbedding r.label)).one_mem,
      points.rationalEmbedding r.label, label_mem_finiteCentralizer r,
      one_mul (points.rationalEmbedding r.label)⟩

/-- The label in the actual geometric Levi, with no new choice. -/
def geometricLabel : r.levi :=
  ⟨points.rationalEmbedding r.label, label_mem_levi r⟩

@[simp]
theorem geometricLabel_value :
    (geometricLabel r).val = points.rationalEmbedding r.label := rfl

/-- Its Frobenius is the same coordinate Frobenius as in the reduction. -/
theorem geometricLabel_fixed :
    Phi frobenius (geometricLabel r).val = (geometricLabel r).val :=
  points.rationalEmbedding_fixed r.label

/-- The literal rational subgroup of the same retained geometric Levi. -/
abbrev rationalLevi : Subgroup (fixedPoints (Phi frobenius).toMonoidHom) :=
  rationalSubgroup (Phi frobenius).toMonoidHom r.levi

/-- The actual inclusion into the algebraic adjoint point carrier. -/
def rationalLeviEmbedding : rationalLevi r →* PCSp A 3 :=
  (fixedPoints (Phi frobenius).toMonoidHom).subtype.comp (rationalLevi r).subtype

theorem rationalLeviEmbedding_injective :
    Function.Injective (rationalLeviEmbedding r) :=
  Subtype.val_injective.comp Subtype.val_injective

@[simp]
theorem rationalLeviEmbedding_value (x : rationalLevi r) :
    rationalLeviEmbedding r x = x.val.val := rfl

/-- The rational label uses the original rational-point equivalence. -/
def rationalLabel : rationalLevi r :=
  ⟨points.rationalEquiv r.label, label_mem_levi r⟩

@[simp]
theorem rationalLabel_value :
    rationalLeviEmbedding r (rationalLabel r) = points.rationalEmbedding r.label := rfl

/-- Both rational-point presentations retain the identical geometric element. -/
theorem rationalLabel_geometric :
    rationalLeviEmbedding r (rationalLabel r) = (geometricLabel r).val := rfl

/-- The rational subtype carries the original Frobenius equation. -/
theorem rationalLabel_fixed :
    Phi frobenius (rationalLeviEmbedding r (rationalLabel r)) =
      rationalLeviEmbedding r (rationalLabel r) :=
  points.rationalEmbedding_fixed r.label

/-- No independent finiteness of algebraic points or of the Levi is required. -/
theorem rationalLevi_finite : Finite (rationalLevi r) :=
  Finite.of_injective
    (fun x : rationalLevi r => points.rationalEquiv.symm x.val)
    (points.rationalEquiv.symm.injective.comp Subtype.val_injective)

/-- The geometric subtype has precisely the order of the retained finite label. -/
theorem geometricLabel_order : orderOf (geometricLabel r) = orderOf r.label := by
  calc
    orderOf (geometricLabel r) = orderOf (geometricLabel r).val :=
      (orderOf_injective r.levi.subtype Subtype.val_injective (geometricLabel r)).symm
    _ = orderOf r.label :=
      orderOf_injective points.rationalEmbedding points.rationalEmbedding_injective r.label

/-- The two injective inclusions preserve the exact original element order. -/
theorem rationalLabel_order : orderOf (rationalLabel r) = orderOf r.label := by
  calc
    orderOf (rationalLabel r) = orderOf (rationalLeviEmbedding r (rationalLabel r)) :=
      (orderOf_injective (rationalLeviEmbedding r)
        (rationalLeviEmbedding_injective r) (rationalLabel r)).symm
    _ = orderOf r.label :=
      orderOf_injective points.rationalEmbedding points.rationalEmbedding_injective r.label

/-- Oddness is transported from the same output label. -/
theorem rationalLabel_odd : Odd (orderOf (rationalLabel r)) := by
  rw [rationalLabel_order]
  exact r.odd_order

/-- Defining-prime regularity retains the orientation used by the reduction. -/
theorem rationalLabel_defining_regular : p.Coprime (orderOf (rationalLabel r)) := by
  rw [rationalLabel_order]
  exact r.defining_regular

/-- The same fact in the generic prime regular carrier convention. -/
theorem rationalLabel_prime_regular : IsPrimeRegular p (rationalLabel r) :=
  (rationalLabel_defining_regular r).symm

end ModularRep.PaperProofs.TypeBRankThreeJordanDualLabel


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
