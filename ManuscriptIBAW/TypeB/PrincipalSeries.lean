import ModularRep.PaperProofs.TypeBCurrentPrincipalResults
import ModularRep.PaperProofs.TypeBCurrentPrincipalSeries

/-!
# Lemma 4.8 on the principal GGGR coordinates

The three clauses of Lemma 4.8 are applied here in rank at least three. This
file identifies its geometric quasi-isolation predicate, choice of ordinary
block and rational series with those used in Proposition 4.9. The principal
series assertion is reconstructed from the separate Cabanes–Enguehard and
Bonnafé source assumptions.
-/

noncomputable section
set_option autoImplicit false

namespace ManuscriptIBAW.TypeB.PrincipalSeries

open ModularRep ModularRep.PaperProofs OrdinaryIrreducibleCharacter
open TypeBCliffordCarriers TypeBCentralKernelBlockSource TypeBCurrentPrincipalResults
open TypeBCurrentPrincipalSeries
open TypeBSpinPrincipalDecompositionBinding TypeBSpinPrincipalProjectiveBinding
open TypeBSpinGGGRPrincipalSeriesBinding TypeBSpinGGGRProjectivityBinding
open TypeBSpinRationalUnipotentClassBinding

variable {n r f : ℕ} {F K O k : Type}
  [Field F] [Finite F] [CharP F r] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [Field k] [Algebra O K]
  [CharP k 2] [IsAlgClosed k]
  {N : NormSource n F} [Finite (SpecialClifford n F)] [Finite (Spin n F N)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))]
  [HasEnoughRootsOfUnity K (Nat.card (Spin n F N))]
  [Finite (Irr K (Spin n F N))]
  {parameters : OddFieldParameters F r f} {rank : 3 ≤ n}
  {Msys : ModularSystem 2 K O k}
  {iota : PrimeRegularRootEmbedding 2 k K (Spin n F N)}
  {b : LiteralPrimitiveBlock k (Spin n F N)}
  [Fintype (LiteralPrimitiveBlock k (Spin n F N))]

/-- The data for the specified GGGR context before proving principal series
membership. There is no assumed `PrincipalSeriesCertificate` field. -/
structure ContextData (parameters : OddFieldParameters F r f) (rank : 3 ≤ n)
    (Msys : ModularSystem 2 K O k)
    (iota : PrimeRegularRootEmbedding 2 k K (Spin n F N))
    (b : LiteralPrimitiveBlock k (Spin n F N)) where
  finiteClifford : FiniteCliffordSource n F
  orthogonality : OrdinaryOrthogonalitySource (N := N) (K := K)
  hcompat : StableReductionBrauerCharacterCompatibility Msys iota
  principal : IsPrincipal b
  blocks : BlockIdempotentDecomposition
    (fun c : LiteralPrimitiveBlock k (Spin n F N) => c.val)
  ordinary : OrdinaryBlockSource Msys iota blocks
  columns : DecompositionColumnIndependenceSource Msys iota
  GeometricClass : Type
  geometricClass : UnipotentClass (r := r) (N := N) → GeometricClass
  ComponentGroup : GeometricClass → Type
  componentInstances : ∀ C, Group (ComponentGroup C)
  gamma : UnipotentClass (r := r) (N := N) → Spin n F N → K
  lowerDual : Irr K (Spin n F N) → Irr K (Spin n F N)
  rationalSeries : TypeBConformalDualCarriers.PCSp F n → Irr K (Spin n F N) → Prop
  quasiIsolated : TypeBConformalDualCarriers.PCSp F n → Prop
  unipotentSupport : Irr K (Spin n F N) → GeometricClass → Prop
  m : ℕ
  classIndex : Fin m ≃ UnipotentClass (r := r) (N := N)
  closure : GeometricClass → GeometricClass → Prop
  ordering : TypeBAllRankGGGR.BasisPhysical.GeometricOrdering
    geometricClass classIndex closure
  induction : GGGRInductionSource parameters rank gamma
  expansion : OddInductionExpansionCertificate Msys iota hcompat

attribute [instance] ContextData.componentInstances

/-- Apply the general context to the same block, selector and series in rank at
least three. -/
def context (D : ContextData parameters rank Msys iota b)
    (semisimple : ∀ s chi, D.rationalSeries s chi → IsPrimeRegular r s) :
    Context Msys iota D.blocks parameters (by omega) where
  ordinaryRoots := inferInstance
  ordinary := D.ordinary
  principalBlock := b
  principal := D.principal
  rationalSeries := D.rationalSeries
  series_semisimple := semisimple

/-- Interpret the source on the specified rational dual group and characters.
The equivalence of quasi-isolation predicates does not assert principal
membership. Cabanes–Enguehard 21.14, Bonnafé 5.3(a), the parametrisation by
odd block labels and Cabanes–Enguehard 9.8(iv) remain separate published
inputs with their stated scopes. -/
structure Binding (D : ContextData parameters rank Msys iota b) where
  semisimple : ∀ s chi, D.rationalSeries s chi → IsPrimeRegular r s
  geometry : DualGeometry parameters (show 2 ≤ n by omega)
  quasi_iff : ∀ s, D.quasiIsolated s ↔ geometry.QuasiIsolated s
  ce : CE2114Source (context D semisimple)
  bonnafe : BonnafeSource geometry
  labels : BlockLabelSource (context D semisimple)
  dual_series : ∀ s chi, D.rationalSeries s chi → D.rationalSeries s (D.lowerDual chi)

omit [Finite (SpecialClifford n F)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
/-- The principal series assertion follows from the displayed source
assumptions. -/
theorem Binding.certificate {D : ContextData parameters rank Msys iota b}
    (B : Binding D) : TypeBSpinGGGRPrincipalSeriesBinding.PrincipalSeriesCertificate
      parameters rank D.ordinary.ordinaryBlock b D.principal
      D.rationalSeries D.quasiIsolated D.lowerDual where
  quasiIsolated_fourth_power s hs := B.bonnafe.fourth_power s ((B.quasi_iff s).mp hs)
  two_series_principal s chi ht hchi := (B.ce.membership_iff chi).mpr ⟨s, ht, hchi⟩
  normalizedDual_series := B.dual_series

/-- Construct the GGGR context after proving its principal series assertion,
using the original data for all other fields. -/
def Binding.context {D : ContextData parameters rank Msys iota b}
    (B : Binding D) : GGGRContext parameters rank Msys iota b where
  finiteClifford := D.finiteClifford
  orthogonality := D.orthogonality
  hcompat := D.hcompat
  principal := D.principal
  blocks := D.blocks
  ordinary := D.ordinary
  columns := D.columns
  GeometricClass := D.GeometricClass
  geometricClass := D.geometricClass
  ComponentGroup := D.ComponentGroup
  componentInstances := D.componentInstances
  gamma := D.gamma
  lowerDual := D.lowerDual
  rationalSeries := D.rationalSeries
  quasiIsolated := D.quasiIsolated
  unipotentSupport := D.unipotentSupport
  series := B.certificate
  m := D.m
  classIndex := D.classIndex
  closure := D.closure
  ordering := D.ordering
  induction := D.induction
  expansion := D.expansion

omit [Finite (SpecialClifford n F)]
  [HasEnoughRootsOfUnity K (Nat.card (SpecialClifford n F))] in
/-- All three clauses of Lemma 4.8 on these GGGR coordinates. -/
theorem lemma_4_8 {D : ContextData parameters rank Msys iota b} (B : Binding D) :
    ({chi : Irr K (Spin n F N) | D.ordinary.ordinaryBlock chi = b} =
      {chi : Irr K (Spin n F N) | IdentityTwoSeries D.rationalSeries chi}) ∧
    (∀ s chi, D.quasiIsolated s → D.rationalSeries s chi →
      D.ordinary.ordinaryBlock chi = b) ∧
    (∀ c : LiteralPrimitiveBlock k (Spin n F N),
      StrictlyQuasiIsolatedBlock (context D B.semisimple) B.geometry B.labels c ↔
        IsPrincipal c) := by
  obtain ⟨h1, h2, h3⟩ := TypeBCurrentPrincipalSeries.lemma_4_8
    (context D B.semisimple) B.ce B.geometry B.bonnafe B.labels
  exact ⟨h1, fun s chi hs hchi => h2 s chi ((B.quasi_iff s).mp hs) hchi, h3⟩

end ManuscriptIBAW.TypeB.PrincipalSeries

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
