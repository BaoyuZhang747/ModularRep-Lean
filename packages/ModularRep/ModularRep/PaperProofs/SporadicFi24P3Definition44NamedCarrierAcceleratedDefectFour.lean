import ModularRep.ModularSystem
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedBlockDefinition41
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierJ4Numerical
import Mathlib.GroupTheory.PGroup
import Mathlib.Data.ZMod.Basic

/-! Lemma5.3 relative to explicit published classification and branch inputs.
The finite case deduction is internal. Classification tags denote the published
cases through accepted E1/U bindings on the same lifted actual block. They are
not claimed as an internal formalisation of inertial or hyperfocal theory.
Only the three independently published branch principles contain iBAW outputs;
none assumes this manuscript's defect-four conclusion. -/
noncomputable section
open scoped MonoidAlgebra
namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour
open ModularRep ModularRep.CharacterWeight
open EvenFieldFLZSourceConditions
open SporadicFi24CentralSectorAssemblyLemma56Actual
open SporadicCompleteCollapseLemma52Actual
  (DefectZeroReductionSource TrivialWeightSource)
open SporadicFi24P3Definition44NamedCarrierCanonicalLocalReduction
open SporadicFi24P3Definition44NamedCarrierAcceleratedBlockDefinition41
open SporadicFi24P3Definition44NamedCarrierJ4Numerical (actualHasDefect)
universe u
variable {k K O X : Type u}
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]
variable [CommRing O] [IsDomain O] [Algebra O K]
variable [Group X] [Fintype X]
variable (iota : PrimeRegularRootEmbedding 2 k K X)
variable (R : LiteralCarrierAdapter (p := 2) (k := k) (K := K) (X := X))

/-- Actual integral block lift and coefficient bindings for the published
ordinary-block classification; splitting and root compatibility are explicit. -/
structure BlockRealization where
  system : ModularSystem 2 K O k
  integralBlock : ActualBlock (k := k) (X := X) → O[X]
  integralPrimitive : ∀ b, IsPrimitiveCentralIdempotent (integralBlock b)
  reduction : ∀ b,
    MonoidAlgebra.mapRingHom X system.residue (integralBlock b) =
      R.1.operations.ambientBlockData.blockIdempotent b
  splitting : ∀ (H : Subgroup X) (n : ℕ)
    (rho : Representation K H (Fin n → K)), rho.IsIrreducible →
      Function.Bijective (algebraMap K (Representation.IntertwiningMap rho rho))
  rootCompatibility : ∀ z : O, z ^ primeRegularExponent 2 X = 1 →
    iota.lift (system.residue z) = algebraMap O K z

inductive EKKCase
  | principal | co3Eight | nilpotentCovered | product
  deriving DecidableEq

inductive InertiaTag
  | inertial | noninertial
  deriving DecidableEq

abbrev KleinFour := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)

/-- Accepted interpretation of EKK's classification on the same integral lift. -/
structure ClassificationData (_A : BlockRealization (O := O) iota R) where
  caseOf : ActualBlock (k := k) (X := X) → EKKCase
  inertiaOf : ActualBlock (k := k) (X := X) → InertiaTag
  hyperfocalOf : ActualBlock (k := k) (X := X) → Subgroup X

variable (Cover : EllPrimeCoverSource 2 X)
variable (A : BlockRealization (O := O) iota R)
variable (L : ClassificationData iota R A)

/-- EKK&S Thm6.1 and the structural consequences recorded on Zhang–Zhou p175.
These fields contain no inductive-condition conclusion. -/
structure ClassificationConsequences : Prop where
  principal : ∀ b Q, actualHasDefect iota R b Q → IsMulCommutative Q →
    L.caseOf b = .principal → ∀ S : Sylow 2 Cover.S, IsMulCommutative S
  co3 : ∀ b Q, actualHasDefect iota R b Q → IsMulCommutative Q →
    L.caseOf b = .co3Eight → Nat.card Q = 8
  nilpotentCovered : ∀ b Q, actualHasDefect iota R b Q → IsMulCommutative Q →
    L.caseOf b = .nilpotentCovered → L.inertiaOf b = .inertial
  product : ∀ b Q, actualHasDefect iota R b Q → IsMulCommutative Q →
    L.caseOf b = .product →
      L.hyperfocalOf b = ⊥ ∨ Nonempty (L.hyperfocalOf b ≃* KleinFour)
  trivialHyperfocal : ∀ b, L.hyperfocalOf b = ⊥ → L.inertiaOf b = .inertial

variable (C : ∀ V : CharacterWeight 2 K X, CanonicalRawReduction iota V)
variable (D : DefectZeroReductionSource iota)
variable (T : TrivialWeightSource (p := 2) (X := X))

/-- Independently published fixed block-iBAW principles, each with its actual
scope and the same root, coefficient realization, cover and classification.
Their application bindings remain explicitly accepted literature assumptions. -/
structure PublishedBranchPrinciples : Prop where
  spathCorollary66 : (∀ S : Sylow 2 Cover.S, IsMulCommutative S) →
    ∀ b, BlockCertificate iota R C Cover D T b
  huZhouTheorem11 : ∀ b, L.inertiaOf b = .inertial →
    BlockCertificate iota R C Cover D T b
  zhangZhouMain : ∀ b Q, actualHasDefect iota R b Q → IsMulCommutative Q →
    L.inertiaOf b = .noninertial → Nonempty (L.hyperfocalOf b ≃* KleinFour) →
      BlockCertificate iota R C Cover D T b

/-- Manuscript Lemma5.3: an actual defect-four block satisfies the full fixed
block condition, relative only to the stated upstream inputs. -/
theorem defect_four_block_certificate
    (E : ClassificationConsequences iota R Cover A L)
    (B : PublishedBranchPrinciples iota R Cover A L C D T)
    (b : ActualBlock (k := k) (X := X)) (Q : Subgroup X)
    (hDefect : actualHasDefect iota R b Q) (hQ : Nat.card Q = 4) :
    BlockCertificate iota R C Cover D T b := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAb : IsMulCommutative Q :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by simpa using hQ)
  cases hc : L.caseOf b with
  | principal =>
      exact B.spathCorollary66 (E.principal b Q hDefect hAb hc) b
  | co3Eight =>
      have h8 := E.co3 b Q hDefect hAb hc
      omega
  | nilpotentCovered =>
      exact B.huZhouTheorem11 b (E.nilpotentCovered b Q hDefect hAb hc)
  | product =>
      cases hi : L.inertiaOf b with
      | inertial => exact B.huZhouTheorem11 b hi
      | noninertial =>
          rcases E.product b Q hDefect hAb hc with hbot | hK4
          · have h := E.trivialHyperfocal b hbot
            rw [hi] at h
            cases h
          · exact B.zhangZhouMain b Q hDefect hAb hi hK4

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierAcceleratedDefectFour


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
