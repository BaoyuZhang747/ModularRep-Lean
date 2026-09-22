import Formalisation.SemidirectStabilizer
import ModularRep.PaperProofs.OddGFactorizationLemma312ActualExtension
import ModularRep.PaperProofs.TypeBLemma411Proposition412LiteralHandoff

/-!
# Stabiliser consequences in Corollary 4.10

This file checks the elementary stabiliser and extension deductions that
follow the field fixation argument in Corollary 4.10.  The field fixedness
itself is derived by the literal handoff from Lemma 4.7 and Proposition
4.9.  Lean then proves that the field stabiliser of every principal block
Brauer character is the whole field group, derives the regular overgroup
stabiliser factorisation, and obtains the cyclic extension conditional on the
cited extension theorem.  It then chooses the original character as a
representative in its regular overgroup orbit and packages the factorisation
and extension clauses for that representative.

The regular overgroup action and its compatibility with the field action are
exact structural inputs.  This file does not construct that overgroup, the
weights, the cited Feng--Yu--Zhang criterion, BAW goodness, or iBAW.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413Completion

open Formalisation
open ModularRep.PaperProofs.TypeBGGGRRankProposition412SourceInstantiation
open ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413SourceInstantiation
open ModularRep.PaperProofs.TypeBGGGRRankProposition412Corollary413Bridge
open ModularRep.PaperProofs.TypeBLemma411Proposition412LiteralHandoff
open ModularRep.PaperProofs.CyclicOuterLemma37Concrete
open ModularRep.PaperProofs.OddGFactorizationLemma312ActualExtension
open ModularRep.ManuscriptVerification.CyclicOuterBAW

universe u

variable {p n : Nat}
variable {k K G E A RationalClass C : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [CommGroup E] [Group A] [Group C]
variable [MulAction E RationalClass]
variable {projectiveSpace : Submodule K (G → K)}
variable [FiniteDimensional K projectiveSpace]

namespace LiteralLemma411Source

variable {field : E →* (MulAut G)ᵐᵒᵖ}
variable {D : GGGRBasisSource n projectiveSpace}
variable {c : A} {f : Nat}

/-- Every principal block Brauer character has the whole field group as its
stabiliser.  This is the subgroup form of the first sentence in the second
paragraph of the proof of Corollary 4.10. -/
theorem fieldStabilizer_eq_top
    (S : LiteralLemma411Source
      (RationalClass := RationalClass) field D c f)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ phi : IBr iota,
      inPrincipalBlock phi →
        inPrincipalBlock
          (IrreducibleBrauerCharacter.twist iota phi (field e).unop))
    (projectiveStable : ∀ e : E, ∀ q : G → K, q ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop q ∈ projectiveSpace)
    (B : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable)
    (P : PrincipalProjectionFieldSource field D)
    (psi : PrincipalBrauerCarrier iota inPrincipalBlock) :
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    MulAction.stabilizer E psi = ⊤ := by
  dsimp only
  letI : MulAction E (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    principalBrauerFieldAction field iota inPrincipalBlock brauerStable
  apply top_unique
  intro e _
  exact S.corollary_4_13_from_literal_lemma_4_11 iota inPrincipalBlock
    brauerStable projectiveStable B P e psi

/-- Field fixation gives the regular overgroup stabiliser factorisation for
every principal block Brauer character.  The conclusion is stated
elementwise so that it records the two canonical factors in the semidirect
product without choosing orbit representatives. -/
theorem regularStabilizer_factorization
    (S : LiteralLemma411Source
      (RationalClass := RationalClass) field D c f)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ phi : IBr iota,
      inPrincipalBlock phi →
        inPrincipalBlock
          (IrreducibleBrauerCharacter.twist iota phi (field e).unop))
    (projectiveStable : ∀ e : E, ∀ q : G → K, q ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) (field e).unop q ∈ projectiveSpace)
    (B : ProjectiveBrauerFormulaSource field iota inPrincipalBlock
      brauerStable projectiveSpace projectiveStable)
    (P : PrincipalProjectionFieldSource field D)
    (regularAction : MulAction C
      (PrincipalBrauerCarrier iota inPrincipalBlock))
    (regularFieldAction : E →* MulAut C)
    (compatible :
      let _ := regularAction
      let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
      SemidirectActionCompatible
        (X := PrincipalBrauerCarrier iota inPrincipalBlock)
        regularFieldAction) :
    let _ := regularAction
    let _ := principalBrauerFieldAction field iota inPrincipalBlock brauerStable
    let _ := semidirectMulAction regularFieldAction compatible
    ∀ (psi : PrincipalBrauerCarrier iota inPrincipalBlock)
      (g : C ⋊[regularFieldAction] E),
      g ∈ MulAction.stabilizer (C ⋊[regularFieldAction] E) psi ↔
        ∃ d : C, d ∈ MulAction.stabilizer C psi ∧
          ∃ e : E, e ∈ MulAction.stabilizer E psi ∧
            g = SemidirectProduct.inl d * SemidirectProduct.inr e := by
  dsimp only
  letI : MulAction C (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    regularAction
  letI : MulAction E (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    principalBrauerFieldAction field iota inPrincipalBlock brauerStable
  letI : MulAction (C ⋊[regularFieldAction] E)
      (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    semidirectMulAction regularFieldAction compatible
  have hfixed : ∀ e : E, ∀ psi : PrincipalBrauerCarrier iota inPrincipalBlock,
      e • psi = psi :=
    S.corollary_4_13_from_literal_lemma_4_11 iota inPrincipalBlock
      brauerStable projectiveStable B P
  intro psi g
  exact mem_semidirect_stabilizer_iff_exists_factorization
    regularFieldAction compatible psi (fun e ↦ hfixed e psi) g

/-- The cyclic extension conclusion for a principal block Brauer character,
together with the kernel proof that its semidirect character stabiliser is
the whole group.  The representation remains typed over the actual
stabiliser.  The equality with `⊤` certifies that this is the full field group
case without adding dependent transport to a definitionally different
ambient carrier. -/
theorem extension_and_fullFieldStabilizer
    [Finite E] [IsCyclic E]
    (phi : E →* MulAut G)
    (S : LiteralLemma411Source
      (RationalClass := RationalClass) (inverseOpHom phi) D c f)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ psi : IBr iota,
      inPrincipalBlock psi →
        inPrincipalBlock
          (IrreducibleBrauerCharacter.twist iota psi
            ((inverseOpHom phi) e).unop))
    (projectiveStable : ∀ e : E, ∀ q : G → K, q ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) ((inverseOpHom phi) e).unop q ∈
        projectiveSpace)
    (B : ProjectiveBrauerFormulaSource (inverseOpHom phi) iota
      inPrincipalBlock brauerStable projectiveSpace projectiveStable)
    (P : PrincipalProjectionFieldSource (inverseOpHom phi) D)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u}
      p k)
    (psi : PrincipalBrauerCarrier iota inPrincipalBlock) :
    let _ : MulAction G (IBr iota) :=
      rightAutomorphismAction (X := IBr iota)
        (MulAut.conj : G →* MulAut G)
    let _ : MulAction E (IBr iota) :=
      rightAutomorphismAction (X := IBr iota) phi
    let hcompat := rightAutomorphismSemidirectCompatible
      (X := IBr iota) phi
    let _ : MulAction (G ⋊[phi] E) (IBr iota) :=
      semidirectMulAction phi hcompat
    let hinner : ∀ g : G,
        (SemidirectProduct.inl g : G ⋊[phi] E) • psi.1 = psi.1 :=
      fun g ↦ by
        rw [semidirect_inl_smul]
        exact inner_fixes_ibr iota g psi.1
    let eG := canonicalHToEmbeddedEquiv psi.1 hinner
    let iotaEmbedded := iota.alongMulEquiv eG
    let psiEmbedded := IrreducibleBrauerCharacter.alongMulEquiv iota eG psi.1
    semidirectStabilizer (phi := phi) psi.1 = ⊤ ∧
      ∃ W : FDRep k (embeddedHStabilizer (phi := phi) psi.1),
        Representation.IsIrreducible W.ρ ∧
        psiEmbedded.1 =
          Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
        Nonempty (Representation.Extension
          (embeddedHStabilizer (phi := phi) psi.1) W.ρ) := by
  dsimp only
  letI principalAction : MulAction E
      (PrincipalBrauerCarrier iota inPrincipalBlock) :=
    principalBrauerFieldAction (inverseOpHom phi) iota inPrincipalBlock
      brauerStable
  have hprincipal : ∀ e : E, e • psi = psi :=
    fun e ↦ S.corollary_4_13_from_literal_lemma_4_11 iota
      inPrincipalBlock brauerStable projectiveStable B P e psi
  letI : MulAction G (IBr iota) :=
    rightAutomorphismAction (X := IBr iota)
      (MulAut.conj : G →* MulAut G)
  letI : MulAction E (IBr iota) :=
    rightAutomorphismAction (X := IBr iota) phi
  have hfield : ∀ e : E, e • psi.1 = psi.1 := by
    intro e
    exact congrArg Subtype.val (hprincipal e)
  have hcompat : SemidirectActionCompatible (X := IBr iota) phi :=
    rightAutomorphismSemidirectCompatible (X := IBr iota) phi
  letI : MulAction (G ⋊[phi] E) (IBr iota) :=
    semidirectMulAction phi hcompat
  have htop : semidirectStabilizer (phi := phi) psi.1 = ⊤ := by
    apply top_unique
    intro g _
    change g.left • (g.right • psi.1) = psi.1
    rw [hfield g.right]
    exact inner_fixes_ibr iota g.left psi.1
  refine ⟨htop, ?_⟩
  exact lemma_3_12_cyclic_extension_actual iota phi principle psi.1

/-- Every regular-overgroup orbit has a representative satisfying the
stabiliser factorisation and cyclic-extension clauses proved above.  The
representative is the original character itself.  This is the exact
manuscript-owned existence deduction in the second sentence of Corollary
4.10; matching the supplied actions and stabiliser subgroups to the cited
criterion remains external. -/
theorem exists_principalSelectorRepresentative
    [Finite E] [IsCyclic E]
    (phi : E →* MulAut G)
    (S : LiteralLemma411Source
      (RationalClass := RationalClass) (inverseOpHom phi) D c f)
    (iota : PrimeRegularRootEmbedding p k K G)
    (inPrincipalBlock : IBr iota → Prop)
    (brauerStable : ∀ e : E, ∀ psi : IBr iota,
      inPrincipalBlock psi →
        inPrincipalBlock
          (IrreducibleBrauerCharacter.twist iota psi
            ((inverseOpHom phi) e).unop))
    (projectiveStable : ∀ e : E, ∀ q : G → K, q ∈ projectiveSpace →
      functionTwistLinearEquiv (K := K) ((inverseOpHom phi) e).unop q ∈
        projectiveSpace)
    (B : ProjectiveBrauerFormulaSource (inverseOpHom phi) iota
      inPrincipalBlock brauerStable projectiveSpace projectiveStable)
    (P : PrincipalProjectionFieldSource (inverseOpHom phi) D)
    (regularAction : MulAction C
      (PrincipalBrauerCarrier iota inPrincipalBlock))
    (regularFieldAction : E →* MulAut C)
    (compatible :
      let _ := regularAction
      let _ := principalBrauerFieldAction (inverseOpHom phi) iota
        inPrincipalBlock brauerStable
      SemidirectActionCompatible
        (X := PrincipalBrauerCarrier iota inPrincipalBlock)
        regularFieldAction)
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u}
      p k)
    (psi : PrincipalBrauerCarrier iota inPrincipalBlock) :
    ∃ representative : PrincipalBrauerCarrier iota inPrincipalBlock,
      (let _ : MulAction C (PrincipalBrauerCarrier iota inPrincipalBlock) :=
          regularAction
       representative ∈ MulAction.orbit C psi) ∧
      (let _ : MulAction C (PrincipalBrauerCarrier iota inPrincipalBlock) :=
          regularAction
       let _ : MulAction E (PrincipalBrauerCarrier iota inPrincipalBlock) :=
          principalBrauerFieldAction (inverseOpHom phi) iota
            inPrincipalBlock brauerStable
       let _ : MulAction (C ⋊[regularFieldAction] E)
           (PrincipalBrauerCarrier iota inPrincipalBlock) :=
          semidirectMulAction regularFieldAction compatible
       ∀ g : C ⋊[regularFieldAction] E,
         g ∈ MulAction.stabilizer (C ⋊[regularFieldAction] E) representative ↔
           ∃ d : C, d ∈ MulAction.stabilizer C representative ∧
             ∃ e : E, e ∈ MulAction.stabilizer E representative ∧
               g = SemidirectProduct.inl d * SemidirectProduct.inr e) ∧
      (let _ : MulAction G (IBr iota) :=
          rightAutomorphismAction (X := IBr iota)
            (MulAut.conj : G →* MulAut G)
       let _ : MulAction E (IBr iota) :=
          rightAutomorphismAction (X := IBr iota) phi
       let hcompat := rightAutomorphismSemidirectCompatible
          (X := IBr iota) phi
       let _ : MulAction (G ⋊[phi] E) (IBr iota) :=
          semidirectMulAction phi hcompat
       let hinner : ∀ g : G,
           (SemidirectProduct.inl g : G ⋊[phi] E) • representative.1 =
             representative.1 :=
          fun g ↦ by
            rw [semidirect_inl_smul]
            exact inner_fixes_ibr iota g representative.1
       let eG := canonicalHToEmbeddedEquiv representative.1 hinner
       let iotaEmbedded := iota.alongMulEquiv eG
       let psiEmbedded :=
          IrreducibleBrauerCharacter.alongMulEquiv iota eG representative.1
       semidirectStabilizer (phi := phi) representative.1 = ⊤ ∧
         ∃ W : FDRep k (embeddedHStabilizer (phi := phi) representative.1),
           Representation.IsIrreducible W.ρ ∧
           psiEmbedded.1 =
             Representation.brauerCharacterOfRootEmbedding W.ρ iotaEmbedded ∧
           Nonempty (Representation.Extension
             (embeddedHStabilizer (phi := phi) representative.1) W.ρ)) := by
  refine ⟨psi, ?_, ?_, ?_⟩
  · letI : MulAction C (PrincipalBrauerCarrier iota inPrincipalBlock) :=
      regularAction
    exact ⟨1, one_smul C psi⟩
  · exact regularStabilizer_factorization S iota inPrincipalBlock
      brauerStable projectiveStable B P regularAction regularFieldAction
        compatible psi
  · exact extension_and_fullFieldStabilizer phi S iota inPrincipalBlock
      brauerStable projectiveStable B P principle psi

end LiteralLemma411Source

end ModularRep.PaperProofs.TypeBPrincipalSelectorCorollary413Completion


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
