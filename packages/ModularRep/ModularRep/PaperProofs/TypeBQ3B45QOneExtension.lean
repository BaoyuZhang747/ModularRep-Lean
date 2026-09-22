import ModularRep.PaperProofs.TypeBQ3B45IntermediateBlocks
import ModularRep.PaperProofs.TypeBQ3PrincipalInertiaQuotient
import ModularRep.PaperProofs.TypeBCentralKernelTripleCertificate
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions
import ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance

/-!
# One extension for the B4/B5 Q=1 criterion clauses

The carrier is the SAME matrix G3, and the ambient is its full actual Brauer
automorphism stabilizer. The supplied Q=1 and local-value facts are derived
from the fixed block's singleton/reduction data by the consumer. They do not
assert a criterion or an extension.

The existing matrix automorphism/index-two facts give a cyclic inertia
quotient. The universal cyclic extension theorem is applied ONCE, with one
unselected ambient root seed, retaining agreement with the prescribed base
root. Since the displayed radical is trivial, its local ambient is top.
The local character is the SAME global extension transported to that group.
Every intermediate subgroup is base or top; its irreducible restriction and
specified catalogue come from that endpoint, and self-transport proves every
selected intermediate block equation.

The base catalogue is the consumer's SAME AmbientBlockCatalogueData. It
does not require a global equality with the literal primitive index. Only
the ambient catalogue, cyclic extension principle, seed and coefficient
provenance remain additional sources. No inner-only inertia hypothesis,
local extension, covering choice, Navarro 9.2/9.5/9.6, or Spath pasting input
is used. This is a subordinate construction for the actual B4/B5 criterion.
-/

noncomputable section
set_option autoImplicit false
open scoped MonoidAlgebra

namespace ModularRep.PaperProofs.TypeBQ3B45QOneExtension

open ModularRep CharacterWeight FDRepSimpleClassKZero
open Representation.Extension
open TypeBQ3TripleCoverCarrier TypeBRankThreePrincipalCountBinding
open TypeBQ3PrincipalCriterionData
open TypeBCentralKernelTripleCertificate (PhysicalBlocks)
open SporadicFi24P3Definition44NamedCarrierActualAutomorphismAmbient

local instance groupFintype (T : Type) [Group T] [Finite T] : Fintype T :=
  Fintype.ofFinite T
local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {k K : Type} [Field k] [Field K] [CharP k 2]
  [IsAlgClosed k] [CharZero K]

/-- The top-subgroup equivalence is literally its subtype inclusion. -/
def topSubtypeEquiv {A : Type} [Group A] (D : Subgroup A) (hD : D = ⊤) : D ≃* A where
  toFun x := x.val
  invFun x := ⟨x, by rw [hD]; exact Subgroup.mem_top x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

section LocalDeduction

variable {Y A : Type} [Group Y] [Finite Y] [Group A] [Finite A]

private theorem qOneLocalGroup_eq_top (U : CharacterWeight 2 K Y)
    (hU : U.subgroup = ⊥) (B : Subgroup A) (eG : Y ≃* B) :
    localGroup U B eG = ⊤ := by
  change Subgroup.normalizer (U.subgroup.map (baseEmbedding B eG) : Set A) = ⊤
  rw [hU, Subgroup.map_bot]
  exact Subgroup.normalizer_eq_top (⊥ : Subgroup A)

private theorem qOneNormalizer_eq_top (U : CharacterWeight 2 K Y)
    (hU : U.subgroup = ⊥) : Subgroup.normalizer (U.subgroup : Set Y) = ⊤ := by
  rw [hU]
  exact Subgroup.normalizer_eq_top (⊥ : Subgroup Y)

private def qOneLocalMap (U : CharacterWeight 2 K Y)
    (hU : U.subgroup = ⊥) (B : Subgroup A) (eG : Y ≃* B) :
    Subgroup.normalizer (U.subgroup : Set Y) →* localGroup U B eG :=
  ((baseEmbedding B eG).comp (Subgroup.normalizer (U.subgroup : Set Y)).subtype).codRestrict
    (localGroup U B eG) (fun _ => by
      rw [qOneLocalGroup_eq_top U hU B eG]
      exact Subgroup.mem_top _)

private theorem qOneLocalMap_natural (U : CharacterWeight 2 K Y)
    (hU : U.subgroup = ⊥) (B : Subgroup A) (eG : Y ≃* B) :
    (localGroup U B eG).subtype.comp (qOneLocalMap U hU B eG) =
      (baseEmbedding B eG).comp (Subgroup.normalizer (U.subgroup : Set Y)).subtype := by
  ext n
  rfl

private theorem qOneLocalMap_range (U : CharacterWeight 2 K Y)
    (hU : U.subgroup = ⊥) (B : Subgroup A) (eG : Y ≃* B) :
    (qOneLocalMap U hU B eG).range = B.comap (localGroup U B eG).subtype := by
  ext d
  constructor
  · rintro ⟨n, rfl⟩
    change baseEmbedding B eG n.val ∈ B
    exact (eG n.val).property
  · intro hd
    change (d : A) ∈ B at hd
    refine ⟨⟨eG.symm ⟨d.val, hd⟩, ?_⟩, ?_⟩
    · rw [qOneNormalizer_eq_top U hU]
      exact Subgroup.mem_top _
    · apply Subtype.ext
      exact congrArg (fun z : B => (z : A)) (eG.apply_symm_apply ⟨d.val, hd⟩)

private theorem extension_globalValue
    (root : PrimeRegularRootEmbedding 2 k K Y) (phi : IBr root)
    (B : Subgroup A) (eG : Y ≃* B)
    (rA : PrimeRegularRootEmbedding 2 k K A)
    (extension : BrauerCharacterExtensionWitness rA (root.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv root eG phi))
    (x : PrimeRegularElement (G := Y) 2) :
    extension.val.val (PrimeRegularElement.map (baseEmbedding B eG) x) = phi.val x := by
  have value := congrArg
    (fun f : PrimeRegularClassFunction K B 2 => f (PrimeRegularElement.map eG.toMonoidHom x))
    extension.property
  have roundtrip : PrimeRegularElement.map eG.symm.toMonoidHom
      (PrimeRegularElement.map eG.toMonoidHom x) = x := by
    apply Subtype.ext
    exact eG.symm_apply_apply x.val
  change extension.val.val (PrimeRegularElement.map (baseEmbedding B eG) x) =
    phi.val (PrimeRegularElement.map eG.symm.toMonoidHom
      (PrimeRegularElement.map eG.toMonoidHom x)) at value
  exact value.trans (congrArg phi.val roundtrip)

private theorem topCharacter_common (D : Subgroup A) (hD : D = ⊤)
    (rA : PrimeRegularRootEmbedding 2 k K A) (phiA : IBr rA) :
    PrimeRegularClassFunction.pullback D.subtype phiA.val =
      (IrreducibleBrauerCharacter.alongMulEquiv rA (topSubtypeEquiv D hD).symm phiA).val := by
  apply PrimeRegularClassFunction.ext
  intro x
  rfl

/-- The local copy of the chosen global root has the SAME field-level lift. -/
theorem topRootAgreement (D : Subgroup A) (hD : D = ⊤)
    (rA : PrimeRegularRootEmbedding 2 k K A) (z : k) :
    (rA.alongMulEquiv (topSubtypeEquiv D hD).symm).lift z = rA.lift z :=
  rA.alongMulEquiv_lift (topSubtypeEquiv D hD).symm z

private theorem extension_localValues
    (root : PrimeRegularRootEmbedding 2 k K Y) (phi : IBr root)
    (U : CharacterWeight 2 K Y) (hU : U.subgroup = ⊥)
    (B : Subgroup A) (eG : Y ≃* B)
    (rA : PrimeRegularRootEmbedding 2 k K A)
    (extension : BrauerCharacterExtensionWitness rA (root.alongMulEquiv eG)
      (IrreducibleBrauerCharacter.alongMulEquiv root eG phi))
    (localAnchor : ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (U.subgroup : Set Y)) 2,
      phi.val (PrimeRegularElement.map (Subgroup.normalizer (U.subgroup : Set Y)).subtype n) =
        U.localCharacter (QuotientGroup.mk n.val))
    (n : PrimeRegularElement (G := Subgroup.normalizer (U.subgroup : Set Y)) 2) :
    (IrreducibleBrauerCharacter.alongMulEquiv rA
      (topSubtypeEquiv (localGroup U B eG) (qOneLocalGroup_eq_top U hU B eG)).symm
      extension.val).val (PrimeRegularElement.map (qOneLocalMap U hU B eG) n) =
      U.localCharacter (QuotientGroup.mk n.val) := by
  change extension.val.val
    (PrimeRegularElement.map (topSubtypeEquiv (localGroup U B eG)
      (qOneLocalGroup_eq_top U hU B eG)).toMonoidHom
      (PrimeRegularElement.map (qOneLocalMap U hU B eG) n)) = _
  have element : PrimeRegularElement.map (topSubtypeEquiv (localGroup U B eG)
      (qOneLocalGroup_eq_top U hU B eG)).toMonoidHom
      (PrimeRegularElement.map (qOneLocalMap U hU B eG) n) =
      PrimeRegularElement.map (baseEmbedding B eG)
        (PrimeRegularElement.map (Subgroup.normalizer (U.subgroup : Set Y)).subtype n) := by
    apply Subtype.ext
    rfl
  exact (congrArg extension.val.val element).trans
    ((extension_globalValue root phi B eG rA extension
      (PrimeRegularElement.map (Subgroup.normalizer (U.subgroup : Set Y)).subtype n)).trans
      (localAnchor n))

end LocalDeduction

/-- One cyclic extension on the actual Brauer inertia, with the exact base
root agreement retained as part of the constructed output. -/
theorem exists_actual_extension_with_agreement
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (root : PrimeRegularRootEmbedding 2 k K G3) (phi : IBr root)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (seed : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi)) :
    let eG := actualBaseEquiv root phi (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)
    let rB := root.alongMulEquiv eG
    let phiB := IrreducibleBrauerCharacter.alongMulEquiv root eG phi
    ∃ rA : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi),
      (∀ zeta : rootsOfUnity (primeRegularExponent 2 (actualBase root phi)) k,
        rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      Nonempty (BrauerCharacterExtensionWitness rA rB phiB) := by
  let hc := TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource
  exact
    SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions.exists_extensionWitness_with_retained_agreement
      (actualBase root phi) principle
      (root.alongMulEquiv (actualBaseEquiv root phi hc))
      (IrreducibleBrauerCharacter.alongMulEquiv root (actualBaseEquiv root phi hc) phi)
      (TypeBQ3PrincipalInertiaQuotient.actual_quotient_isCyclic automorphisms indexTwo root phi)
      (SporadicFi24P3Definition44NamedCarrierTrivialSectorBaseInvariance.actualGlobalBaseFixed root phi hc)
      seed

/- The private construction consumes the single extension constructed below.
All map, restriction, and intermediate-block obligations are checked in
separate deductions; the public source boundary supplies no extension. -/
private def actualClauseIIIOfExtension
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (root : PrimeRegularRootEmbedding 2 k K G3) (phi : IBr root)
    (U : CharacterWeight 2 K G3) (hU : U.subgroup = ⊥)
    (localAnchor : ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (U.subgroup : Set G3)) 2,
      phi.val (PrimeRegularElement.map (Subgroup.normalizer (U.subgroup : Set G3)).subtype n) =
        U.localCharacter (QuotientGroup.mk n.val))
    (baseBlocks : AmbientBlockCatalogueData
      (k := k) (G := G3) (Block := LiteralPrimitiveBlock k G3))
    (ambientBlocks : PhysicalBlocks k (ActualAutAmbient root phi))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two)
    (rA : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi))
    (extension : BrauerCharacterExtensionWitness rA
      (root.alongMulEquiv (actualBaseEquiv root phi
        (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)))
      (IrreducibleBrauerCharacter.alongMulEquiv root (actualBaseEquiv root phi
        (TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource)) phi)) :
    PrincipalClauseIII root phi U := by
  classical
  let hc := TypeBQ3PrincipalInertiaQuotient.center_eq_bot matrixSource
  let A : Type := ActualAutAmbient root phi
  let B : Subgroup A := actualBase root phi
  let eG : G3 ≃* B := actualBaseEquiv root phi hc
  let D : Subgroup A := localGroup U B eG
  have hD : D = ⊤ := qOneLocalGroup_eq_top U hU B eG
  let eD : D ≃* A := topSubtypeEquiv D hD
  let rB : PrimeRegularRootEmbedding 2 k K B := root.alongMulEquiv eG
  let phiB : IBr rB := IrreducibleBrauerCharacter.alongMulEquiv root eG phi
  let rD : PrimeRegularRootEmbedding 2 k K D := rA.alongMulEquiv eD.symm
  let phiD : IBr rD := IrreducibleBrauerCharacter.alongMulEquiv rA eD.symm extension.val
  have common : PrimeRegularClassFunction.pullback D.subtype extension.val.val = phiD.val :=
    topCharacter_common D hD rA extension.val
  letI : Fintype A := groupFintype A
  letI : Fintype B := groupFintype B
  letI : Fintype G3 := groupFintype G3
  letI := baseBlocks.fintypeBlock
  letI := ambientBlocks.blockFintype
  let intermediate : ∀ J : Subgroup A, B ≤ J →
      TypeBQ3PrincipalPairBlockChoice.IntermediateBlockData 2 k K D extension.val.val phiD.val J :=
    TypeBQ3B45IntermediateBlocks.allIntermediate B D hD
    (TypeBQ3PrincipalInertiaQuotient.actual_quotient_card_le_two automorphisms indexTwo root phi)
    rB phiB rA extension rD phiD common
    (baseBlocks.blocks.alongMulEquiv eG) ambientBlocks.decomposition
    (baseBlocks.catalogue.alongMulEquiv eG) ambientBlocks.catalogue fieldSource
  refine {
    A := A
    base := B
    eBase := eG
    baseCentralizer_eq_center := ?_
    centerPrimeTo := ?_
    originalConjugation := actualConjugation root phi
    conjugation_on_base := ?_
    automorphismQuotientEquiv := actualAutomorphismQuotientEquiv root phi hc
    automorphismQuotientEquiv_natural := actualAutomorphismQuotientEquiv_natural root phi hc
    globalRoot := rA
    globalCharacter := extension.val
    globalRestriction := ?_
    localMap := qOneLocalMap U hU B eG
    localMap_natural := qOneLocalMap_natural U hU B eG
    localMap_range := qOneLocalMap_range U hU B eG
    localRoot := rD
    localCharacter := phiD
    localRestriction := extension_localValues root phi U hU B eG rA extension localAnchor
    intermediate := intermediate }
  · exact (actualBase_centralizer_eq_bot root phi hc).trans
      (actualAmbient_center_eq_bot root phi hc).symm
  · change Nat.Coprime 2 (Nat.card (Subgroup.center (ActualAutAmbient root phi)))
    rw [actualAmbient_center_eq_bot root phi hc]
    simp
  · intro a y
    exact innerEmbedding_conjugation root phi a y
  · apply PrimeRegularClassFunction.ext
    intro x
    exact extension_globalValue root phi B eG rA extension x

/-- The complete current ClauseIII for a prescribed Q=1 raw weight on
actual G3. The local anchor is the actual fixed reduction equation on
prime regular normalizer elements; it is not a local extension premise. -/
theorem exists_actual_qOne_clauseIII
    (matrixSource : MatrixExceptionalSource)
    (automorphisms : TypeBQ3TripleCoverAutomorphisms.MatrixAutomorphismSource)
    (indexTwo : (G (ZMod 3)).index = 2)
    (root : PrimeRegularRootEmbedding 2 k K G3) (phi : IBr root)
    (U : CharacterWeight 2 K G3) (hU : U.subgroup = ⊥)
    (localAnchor : ∀ n : PrimeRegularElement
        (G := Subgroup.normalizer (U.subgroup : Set G3)) 2,
      phi.val (PrimeRegularElement.map (Subgroup.normalizer (U.subgroup : Set G3)).subtype n) =
        U.localCharacter (QuotientGroup.mk n.val))
    (baseBlocks : AmbientBlockCatalogueData
      (k := k) (G := G3) (Block := LiteralPrimitiveBlock k G3))
    (ambientBlocks : PhysicalBlocks k (ActualAutAmbient root phi))
    (principle : Representation.BrauerCyclicExtensionPrinciple.{0, 0, 0} 2 k)
    (ambientSeed : PrimeRegularRootEmbedding 2 k K (ActualAutAmbient root phi))
    (fieldSource : SpathCoefficientField 2 k Nat.prime_two) :
    Nonempty (PrincipalClauseIII root phi U) := by
  obtain ⟨rA, _rootAgreement, ⟨extension⟩⟩ :=
    exists_actual_extension_with_agreement matrixSource automorphisms indexTwo root phi
      principle ambientSeed
  exact ⟨actualClauseIIIOfExtension matrixSource automorphisms indexTwo root phi U hU
    localAnchor baseBlocks ambientBlocks fieldSource rA extension⟩

end ModularRep.PaperProofs.TypeBQ3B45QOneExtension


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
