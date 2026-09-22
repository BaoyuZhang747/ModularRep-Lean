import ModularRep.PaperProofs.TypeBRankThreeNonprincipalApplication

/-!
# Full centralizer containment for the same nonprincipal dual label

Malle--Testerman, Table 9.2 and Proposition 14.20, give the two component
power laws for the actual adjoint algebraic type-C3 carrier. They are used
uniformly on defining-prime regular rational labels. Odd order enters only
the subgroup deduction, after the nonprincipal predecessor has constructed
its label and proper rational Levi.

The interpretation of the existing geometry.connectedCentralizer as the
actual algebraic identity component remains an explicit U source boundary.
The certificate below authenticates this same selector and actual point
map; it does not introduce another component selector. The coefficient,
ordinary-series and geometric interpretations of the predecessor remain
unchanged. The result retains its original reduction and adds full
geometric centralizer containment in its original Levi.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra Pointwise

namespace ModularRep.PaperProofs.TypeBRankThreeMoritaCentralizerBinding

open ModularRep OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBConformalDualCarriers TypeBCentralKernelBlockSource
open TypeBOrdinaryBlockSplitting TypeBRankThreeNonprincipalSeriesBinding
open TypeBRankThreeNonprincipalGeometry TypeBRankThreeNonprincipalBonnafeBinding
open TypeBRankThreeNonprincipalApplication

/-- Uniform component-exponent consequences of MT Proposition 14.20 on
the same algebraic PCSp points. The actual identity-component realization
of geometry.connectedCentralizer is part of the source interpretation U.
The two source laws have no odd-order guard. -/
structure AlgebraicComponentExponentCertificate
    (p f : ℕ) (F A : Type) [Field F] [Finite F] [CharP F p]
    [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
    (parameters : OddFieldParameters F p f)
    (frobenius : FrobeniusSource p f A)
    (points : RationalPointSource F A p f frobenius)
    (geometry : GeometrySource F A p f frobenius points) : Prop where
  square_mem : ∀ (s : PCSp F 3), p.Coprime (orderOf s) →
    ∀ (x : PCSp A 3),
      x ∈ fullCentralizer (points.rationalEmbedding s) →
      x ^ 2 ∈ geometry.connectedCentralizer (points.rationalEmbedding s)
  order_mem : ∀ (s : PCSp F 3), p.Coprime (orderOf s) →
    ∀ (x : PCSp A 3),
      x ∈ fullCentralizer (points.rationalEmbedding s) →
      x ^ orderOf s ∈
        geometry.connectedCentralizer (points.rationalEmbedding s)

private theorem mem_of_square_mem_of_odd_pow_mem
    {G : Type*} [Group G] (H : Subgroup G)
    {x : G} {m : ℕ} (hm : Odd m)
    (h2 : x ^ 2 ∈ H) (hmx : x ^ m ∈ H) : x ∈ H := by
  obtain ⟨a, ha⟩ := hm
  have heven : x ^ (2 * a) ∈ H := by
    rw [pow_mul]
    exact H.pow_mem h2 a
  have hodd : x ^ (2 * a) * x ∈ H := by
    simpa only [ha, pow_succ] using hmx
  exact (H.mul_mem_cancel_left heven).mp hodd

section Geometry

variable {p f : ℕ} {F A : Type}
  [Field F] [Finite F] [CharP F p]
  [Field A] [IsAlgClosed A] [CharP A p] [Algebra F A]
  {parameters : OddFieldParameters F p f}
  {frobenius : FrobeniusSource p f A}
  {points : RationalPointSource F A p f frobenius}
  {geometry : GeometrySource F A p f frobenius points}

/-- Odd order makes both uniform component power laws force membership. -/
theorem fullCentralizer_eq_connectedCentralizer
    (components : AlgebraicComponentExponentCertificate
      p f F A parameters frobenius points geometry)
    (s : PCSp F 3) (regular : p.Coprime (orderOf s))
    (odd : Odd (orderOf s)) :
    fullCentralizer (points.rationalEmbedding s) =
      geometry.connectedCentralizer (points.rationalEmbedding s) := by
  apply le_antisymm
  · intro x hx
    exact mem_of_square_mem_of_odd_pow_mem
      (geometry.connectedCentralizer (points.rationalEmbedding s)) odd
      (components.square_mem s regular x hx)
      (components.order_mem s regular x hx)
  · exact geometry.connected_le (points.rationalEmbedding s)

end Geometry

section Reduction

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
  [Fintype (LiteralPrimitiveBlock k (Spin 3 F N))]
  (blocks : BlockIdempotentDecomposition
    (fun b : LiteralPrimitiveBlock k (Spin 3 F N) => b.val))
  [HasEnoughRootsOfUnity K (Nat.card (Spin 3 F N))]
  (ordinary : OrdinaryBlockSource Msys iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    blocks)
  (series : Sources parameters Msys iota
    (FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota)
    blocks ordinary)
  (frobenius : FrobeniusSource p f A)
  (points : RationalPointSource F A p f frobenius)
  (geometry : GeometrySource F A p f frobenius points)

/-- Preserve the original reduction and its Levi while strengthening the
displayed connected-times-rational containment to full containment. -/
theorem fullCentralizer_eq_and_le_levi
    (components : AlgebraicComponentExponentCertificate
      p f F A parameters frobenius points geometry)
    {b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F)}
    (r : ManuscriptReduction parameters N orthogonal Msys iota blocks ordinary
      series frobenius points geometry b) :
    fullCentralizer (points.rationalEmbedding r.label) =
        geometry.connectedCentralizer (points.rationalEmbedding r.label) ∧
      fullCentralizer (points.rationalEmbedding r.label) ≤ r.levi := by
  have connected := fullCentralizer_eq_connectedCentralizer
    components r.label r.defining_regular r.odd_order
  refine ⟨connected, ?_⟩
  intro x hx
  have hx0 : x ∈ geometry.connectedCentralizer (points.rationalEmbedding r.label) := by
    rw [← connected]
    exact hx
  exact r.centralizer_containment
    ⟨x, hx0, 1,
      (finiteCentralizer frobenius (points.rationalEmbedding r.label)).one_mem,
      mul_one x⟩

/-- Construct the nonprincipal reduction once, retaining all its block,
label and Levi data together with the full geometric centralizer bound. -/
theorem nonprincipal_full_centralizer_source_instantiated
    (components : AlgebraicComponentExponentCertificate
      p f F A parameters frobenius points geometry)
    (centre : TypeBCentralKernelSpinBinding.SpinCentreOrderSource 3 p f F N)
    (navarro : NavarroCentralBlockPrinciple 2 k)
    (bonnafe : AlgebraicBonnafeCertificate
      p f F A parameters frobenius points geometry)
    (b : LiteralPrimitiveBlock k (TypeBOrthogonalOmegaCarriers.Omega 3 F))
    (nonprincipal : ¬ IsPrincipal b) :
    ∃ r : ManuscriptReduction parameters N orthogonal Msys iota blocks ordinary
        series frobenius points geometry b,
      fullCentralizer (points.rationalEmbedding r.label) =
          geometry.connectedCentralizer (points.rationalEmbedding r.label) ∧
        fullCentralizer (points.rationalEmbedding r.label) ≤ r.levi := by
  obtain ⟨r⟩ := nonprincipal_rank_three_source_instantiated
    parameters N orthogonal Msys iota blocks ordinary series frobenius points geometry
    centre navarro bonnafe b nonprincipal
  exact ⟨r, fullCentralizer_eq_and_le_levi parameters N orthogonal Msys iota blocks
    ordinary series frobenius points geometry components r⟩

end Reduction

end ModularRep.PaperProofs.TypeBRankThreeMoritaCentralizerBinding


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
