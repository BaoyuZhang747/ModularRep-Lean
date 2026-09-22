import ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate
import ModularRep.PaperProofs.TypeBCentralKernelLocalBlockBinding

/-!
# Coherent literal root families for the central-kernel block triples

One prescribed root on the actual ambient group determines all intermediate
and nested subgroup roots. Character injectivity is the checked separation
theorem for each displayed root. The specified block catalogues remain
parameters on the literal primitive-idempotent carriers, with allocation
fixed to `b.val` by `PhysicalBlocks`.

`withPrescribedRoots` preserves separately prescribed base and local roots
under exactly their ambient-root guards. `canonical` constructs those roots
as well and discharges all guards. No projective representation, triple
witness, character matching, or inductive-condition input is introduced.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily

open TypeBCentralKernelTripleCertificate
open TypeBCentralKernelLocalBlockBinding
open TypeBCentralKernelBrauerInflation

universe u

variable {p : ℕ} {k K : Type u}
  [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

local instance finiteGroupFintype (H : Type u) [Group H] [Finite H] :
    Fintype H := Fintype.ofFinite H

/-- The root determines character separation; no injectivity certificate is
an additional parameter. Blocks retain their literal allocation. -/
def characterData {H : Type u} [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K H) (blocks : PhysicalBlocks k H) :
    CharacterData p k K H where
  iota := iota
  injective := FDRepSimpleClassKZero.irreducibleBrauerCharacterInjectivity_of_rootEmbedding iota
  blocks := blocks

@[simp] theorem characterData_iota {H : Type u} [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K H) (blocks : PhysicalBlocks k H) :
    (characterData iota blocks).iota = iota := rfl

@[simp] theorem characterData_blocks {H : Type u} [Group H] [Finite H]
    (iota : PrimeRegularRootEmbedding p k K H) (blocks : PhysicalBlocks k H) :
    (characterData iota blocks).blocks = blocks := rfl

variable {T : Type u} [Group T] [Finite T]

/-- Restrict the actual ambient root twice, retaining the nested carrier. -/
def nestedRoot (iota : PrimeRegularRootEmbedding p k K T)
    (H : Subgroup T) (L : Subgroup H) : PrimeRegularRootEmbedding p k K L :=
  subgroupRoot (subgroupRoot iota H) L

theorem nestedRoot_agrees (iota : PrimeRegularRootEmbedding p k K T)
    (H : Subgroup T) (L : Subgroup H)
    (z : rootsOfUnity (primeRegularExponent p L) k) :
    (nestedRoot iota H L).lift ((z : kˣ) : k) = iota.lift ((z : kˣ) : k) := by
  let hdiv : primeRegularExponent p L ∣ primeRegularExponent p H :=
    Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card L) p
  let zH := PrimeRegularRootEmbedding.rootsOfUnityInclusion hdiv z
  calc
    (nestedRoot iota H L).lift ((z : kˣ) : k) =
        (subgroupRoot iota H).lift ((z : kˣ) : k) :=
      subgroupRoot_agrees (subgroupRoot iota H) L z
    _ = iota.lift ((z : kˣ) : k) := subgroupRoot_agrees iota H zH

/-- Agreement transports across an explicit actual group equivalence,
using equality of the required root exponents. -/
theorem alongMulEquiv_agrees {X Y : Type u}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (ambient : PrimeRegularRootEmbedding p k K T)
    (iota : PrimeRegularRootEmbedding p k K X) (e : X ≃* Y)
    (agree : ∀ z : rootsOfUnity (primeRegularExponent p X) k,
      iota.lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k))
    (z : rootsOfUnity (primeRegularExponent p Y) k) :
    (iota.alongMulEquiv e).lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k) := by
  have hexp : primeRegularExponent p X = primeRegularExponent p Y :=
    congrArg (fun n : ℕ => ordCompl[p] n) (Nat.card_congr e.toEquiv)
  let zX : rootsOfUnity (primeRegularExponent p X) k :=
    ⟨z.val, by change z.val ^ _ = 1; rw [hexp]; exact z.property⟩
  exact (iota.alongMulEquiv_lift e _).trans (agree zX)

/-- An actual surjection with prime-power kernel preserves the exponent
used by the Brauer root convention. The first isomorphism retains the
literal target carrier. -/
theorem exponent_surjection {X Y : Type u}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f)
    (hp : p.Prime) (hker : IsPGroup p f.ker) :
    primeRegularExponent p X = primeRegularExponent p Y := by
  calc
    primeRegularExponent p X = primeRegularExponent p (X ⧸ f.ker) :=
      (PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq hp f.ker hker).symm
    _ = primeRegularExponent p Y :=
      congrArg (fun n : ℕ => ordCompl[p] n)
        (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv)

/-- A compatible actual p-kernel surjection transfers the downstairs
ambient-root guard to the upstairs root domain. Equality of the two full
lifts is explicit here and is supplied by the canonical quotient/equivalence
root constructions in the application. No ambient root extension is assumed. -/
theorem surjection_agrees {X Y : Type u}
    [Group X] [Finite X] [Group Y] [Finite Y]
    (ambient : PrimeRegularRootEmbedding p k K T)
    (f : X →* Y) (hf : Function.Surjective f) (hker : IsPGroup p f.ker)
    (iotaX : PrimeRegularRootEmbedding p k K X)
    (iotaY : PrimeRegularRootEmbedding p k K Y)
    (lifts : iotaX.lift = iotaY.lift)
    (agree : ∀ z : rootsOfUnity (primeRegularExponent p Y) k,
      iotaY.lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k))
    (z : rootsOfUnity (primeRegularExponent p X) k) :
    iotaX.lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k) := by
  have hexp := exponent_surjection f hf iotaX.prime hker
  let zY : rootsOfUnity (primeRegularExponent p Y) k :=
    ⟨z.val, by change z.val ^ _ = 1; rw [← hexp]; exact z.property⟩
  exact (congrFun lifts _).trans (agree zY)

/-- The canonical prime-kernel root inflation retains an ambient-root
guard. This is equality on the actual roots, not a new modular-system input. -/
theorem quotientInflationRoot_agrees {X : Type u} [Group X] [Finite X]
    (ambient : PrimeRegularRootEmbedding p k K T)
    (P : Subgroup X) [P.Normal] (hP : IsPGroup p P)
    (iota : PrimeRegularRootEmbedding p k K (X ⧸ P))
    (agree : ∀ z : rootsOfUnity (primeRegularExponent p (X ⧸ P)) k,
      iota.lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k))
    (z : rootsOfUnity (primeRegularExponent p X) k) :
    (upRoot P hP iota).lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k) := by
  have hexp := PrimeRegularRootEmbeddingPQuotient.exponent_quotient_eq iota.prime P hP
  let zQ : rootsOfUnity (primeRegularExponent p (X ⧸ P)) k :=
    ⟨z.val, by change z.val ^ _ = 1; rw [hexp]; exact z.property⟩
  exact (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift P hP iota _).trans (agree zQ)

/-- Only specified block catalogue data are packaged here. Every index is
an actual primitive idempotent of the displayed group algebra. -/
structure PhysicalBlockFamily (N U : Subgroup T) where
  base : PhysicalBlocks k N
  localData : PhysicalBlocks k (localBase N U)
  intermediate : ∀ J : Subgroup T, N ≤ J → PhysicalBlocks k J
  localIntermediateData : ∀ J : Subgroup T, N ≤ J →
    PhysicalBlocks k (localIntermediate U J)

variable (N U : Subgroup T)

/-- Preserve the prescribed actual base and local roots, with exactly their
ambient-root guards. Every other root and every injectivity proof is
constructed, for all intermediate groups. -/
def withPrescribedRoots
    (ambient : PrimeRegularRootEmbedding p k K T)
    (baseRoot : PrimeRegularRootEmbedding p k K N)
    (localRoot : PrimeRegularRootEmbedding p k K (localBase N U))
    (baseAgree : ∀ z : rootsOfUnity (primeRegularExponent p N) k,
      baseRoot.lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k))
    (localAgree : ∀ z : rootsOfUnity (primeRegularExponent p (localBase N U)) k,
      localRoot.lift ((z : kˣ) : k) = ambient.lift ((z : kˣ) : k))
    (blocks : PhysicalBlockFamily (k := k) N U) :
    TripleData (p := p) (k := k) (K := K) N U where
  ambientRoot := ambient
  base := characterData baseRoot blocks.base
  localData := characterData localRoot blocks.localData
  intermediate J hNJ := characterData (subgroupRoot ambient J) (blocks.intermediate J hNJ)
  localIntermediateData J hNJ :=
    characterData (nestedRoot ambient J (localIntermediate U J))
      (blocks.localIntermediateData J hNJ)
  baseRoots := baseAgree
  localRoots := localAgree
  intermediateRoots J _ := subgroupRoot_agrees ambient J
  localIntermediateRoots J _ := nestedRoot_agrees ambient J (localIntermediate U J)

/-- All roots are canonical restrictions from the same actual ambient root.
The only remaining inputs are the literal specified block catalogues. -/
def canonical (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) :
    TripleData (p := p) (k := k) (K := K) N U :=
  withPrescribedRoots N U ambient (subgroupRoot ambient N)
    (nestedRoot ambient U (localBase N U))
    (subgroupRoot_agrees ambient N) (nestedRoot_agrees ambient U (localBase N U)) blocks

@[simp] theorem canonical_ambientRoot
    (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) :
    (canonical N U ambient blocks).ambientRoot = ambient := rfl

@[simp] theorem canonical_base_iota
    (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) :
    (canonical N U ambient blocks).base.iota = subgroupRoot ambient N := rfl

@[simp] theorem canonical_local_iota
    (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) :
    (canonical N U ambient blocks).localData.iota =
      nestedRoot ambient U (localBase N U) := rfl

@[simp] theorem canonical_intermediate_iota
    (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) (J : Subgroup T) (hNJ : N ≤ J) :
    ((canonical N U ambient blocks).intermediate J hNJ).iota = subgroupRoot ambient J := rfl

@[simp] theorem canonical_localIntermediate_iota
    (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) (J : Subgroup T) (hNJ : N ≤ J) :
    ((canonical N U ambient blocks).localIntermediateData J hNJ).iota =
      nestedRoot ambient J (localIntermediate U J) := rfl

/-- The root family does not relabel any supplied primitive block catalogue. -/
theorem canonical_blocks
    (ambient : PrimeRegularRootEmbedding p k K T)
    (blocks : PhysicalBlockFamily (k := k) N U) :
    (canonical N U ambient blocks).base.blocks = blocks.base ∧
    (canonical N U ambient blocks).localData.blocks = blocks.localData ∧
    (∀ (J : Subgroup T) (hNJ : N ≤ J),
      ((canonical N U ambient blocks).intermediate J hNJ).blocks = blocks.intermediate J hNJ) ∧
    (∀ (J : Subgroup T) (hNJ : N ≤ J),
      ((canonical N U ambient blocks).localIntermediateData J hNJ).blocks =
        blocks.localIntermediateData J hNJ) := ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The precise ambient-root hypothesis of MRR 3.14 is a deduction when
the original root is canonically inflated from the prescribed quotient root.
The quotient groups here are the actual subgroup images used by the
certificate. There is no witness or target predicate among the inputs. -/
theorem canonical_quotient_ambientRoots
    (Z : Subgroup T) [Z.Normal] (hZ : IsPGroup p Z)
    (quotientRoot : PrimeRegularRootEmbedding p k K (T ⧸ Z))
    (blocks : PhysicalBlockFamily (k := k) N U)
    (quotientBlocks : PhysicalBlockFamily (k := k)
      (N.map (QuotientGroup.mk' Z)) (U.map (QuotientGroup.mk' Z)))
    (z : rootsOfUnity (primeRegularExponent p (T ⧸ Z)) k) :
    (canonical (N.map (QuotientGroup.mk' Z)) (U.map (QuotientGroup.mk' Z))
        quotientRoot quotientBlocks).ambientRoot.lift ((z : kˣ) : k) =
      (canonical N U (upRoot Z hZ quotientRoot) blocks).ambientRoot.lift ((z : kˣ) : k) :=
  (PrimeRegularRootEmbeddingPQuotient.ofPQuotient_lift Z hZ quotientRoot _).symm

end ModularRep.PaperProofs.TypeBCentralKernelTripleRootFamily


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
