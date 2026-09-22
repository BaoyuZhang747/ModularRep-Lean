import ModularRep.PaperProofs.EvenFieldP38ChosenDefinition35Transport

/-! Isomorphism invariance of the relation in Definition 3.5. The character and
weight maps are induced by the specified group isomorphisms. Both predicates
are interpreted as the same standard block relation for character triples. -/
noncomputable section
namespace ManuscriptIBAW.TypeC.EvenApplication
open ModularRep ModularRep.PaperProofs
open EvenFieldFLZSourceConditions EvenFieldFLZDefinition35Transport
open EvenFieldP38ChosenDefinition35Transport
open CyclicOuterLemma37Concrete CyclicOuterLemma37LiteralLocalExtension
open CyclicOuterLemma37ActualBlockFibres
open OddTwoStandardBlockTripleTransport OddTwoActualStabilizerTriple
open OddTwoCentralTwoRelationInflation

universe u
/-- A change of coordinates between two finite block problems. The fibre
equivalences must have the specified values on the characters and on the
double quotient of their transport to weights. -/
structure PhysicalCoordinates (P Q : Definition35Problem.{u}) where
  groupEquiv : P.H ≃* Q.H
  prime_eq : P.p = Q.p
  modularField_eq : P.k = Q.k
  ordinaryField_eq : P.K = Q.K
  root_compatible : HEq (P.iota.alongMulEquiv groupEquiv) Q.iota
  gammaEquiv : P.Gamma ≃* Q.Gamma
  brauerEquiv : Definition35Brauer P ≃ Definition35Brauer Q
  weightEquiv : Definition35Weight P ≃ Definition35Weight Q
  gamma_compatible : Q.gamma.comp gammaEquiv.toMonoidHom =
    (MulAut.congr groupEquiv).toMonoidHom.comp P.gamma
  brauer_compatible : ∀ psi : Definition35Brauer P,
    HEq (brauerEquiv psi).1
      (IrreducibleBrauerCharacter.alongMulEquiv P.iota groupEquiv psi.1)
  weight_compatible : ∀ w : Definition35Weight P,
    HEq (weightEquiv w).1
      (Quotient.mk'' (Quotient.mk''
        ((selectedCharacterWeight P.blockSource P.block w).mapGroupEquiv groupEquiv)) :
          CharacterWeight.ConjugacyClass (p := P.p) (K := P.K) (G := Q.H))
  brauer_naturality :
    let _ : MulAction P.Gamma (Definition35Brauer P) := definition35BrauerAction P
    let _ : MulAction Q.Gamma (Definition35Brauer Q) := definition35BrauerAction Q
    ∀ g psi, brauerEquiv (g • psi) = gammaEquiv g • brauerEquiv psi
  weight_naturality :
    let _ : MulAction P.Gamma (Definition35Weight P) := definition35WeightAction P
    let _ : MulAction Q.Gamma (Definition35Weight Q) := definition35WeightAction Q
    ∀ g w, weightEquiv (g • w) = gammaEquiv g • weightEquiv w

/-- Interpret the two predicates using the reductions at the normalisers of
their selected weight subgroups. Neither interpreted relation is assumed to
hold. -/
structure StandardInterpretations (P Q : Definition35Problem.{u})
    (autP : Definition35AutomorphismStabilizerAdapter P)
    (autQ : Definition35AutomorphismStabilizerAdapter Q)
    (sourceP : FLZSourceSemantics P autP) (sourceQ : FLZSourceSemantics Q autQ) where
  standardP : BlockTripleSourceSemantics P.p P.k P.K
  standardQ : BlockTripleSourceSemantics Q.p Q.k Q.K
  sameStandard : HEq standardP standardQ
  ownP : ∀ w : Definition35Weight P, ChosenOwnReduction P w
  ownQ : ∀ w : Definition35Weight Q, ChosenOwnReduction Q w
  meaningP : ChosenDefinition35Interpretation P autP sourceP standardP ownP
  meaningQ : ChosenDefinition35Interpretation Q autQ sourceQ standardQ ownQ

/-- U/E1: universal isomorphism invariance of the standard relation, including
change of the chosen representative of a weight class. This is deliberately
independent of Type C, the unipotent theorem, and the selected bijection. -/
structure StandardIsomorphismSource {p : ℕ} {k K : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    (standard : BlockTripleSourceSemantics p k K) : Prop where
  preserves : ∀ (P Q : Definition35Problem.{u})
    (coordinates : PhysicalCoordinates P Q)
    (autP : Definition35AutomorphismStabilizerAdapter P)
    (autQ : Definition35AutomorphismStabilizerAdapter Q)
    (sourceP : FLZSourceSemantics P autP) (sourceQ : FLZSourceSemantics Q autQ),
    ∀ meaning : StandardInterpretations P Q autP autQ sourceP sourceQ,
    HEq meaning.standardP standard →
    ∀ psi w, sourceP.definition35BlockIsomorphic psi w →
      sourceQ.definition35BlockIsomorphic
        (coordinates.brauerEquiv psi) (coordinates.weightEquiv w)

/-- Instantiate the universal invariance statement for the specified coordinate
maps. -/
def PhysicalCoordinates.toForwardTransport
    {P Q : Definition35Problem.{u}} (coordinates : PhysicalCoordinates P Q)
    {autP : Definition35AutomorphismStabilizerAdapter P}
    {autQ : Definition35AutomorphismStabilizerAdapter Q}
    {sourceP : FLZSourceSemantics P autP} {sourceQ : FLZSourceSemantics Q autQ}
    (meaning : StandardInterpretations P Q autP autQ sourceP sourceQ)
    (standard : StandardIsomorphismSource meaning.standardP) :
    Definition35ForwardTransport P autP sourceP Q autQ sourceQ where
  gammaEquiv := coordinates.gammaEquiv
  brauerEquiv := coordinates.brauerEquiv
  weightEquiv := coordinates.weightEquiv
  brauer_naturality := coordinates.brauer_naturality
  weight_naturality := coordinates.weight_naturality
  relation_forward := standard.preserves P Q coordinates autP autQ sourceP sourceQ meaning HEq.rfl

end ManuscriptIBAW.TypeC.EvenApplication

/-
This file belongs to the Lean companion to Baoyu Zhang (2026),
"On the inductive blockwise Alperin weight condition for type B and type C".
It checks selected arguments under the explicit assumptions described in
docs/manuals/formalisation-companion.tex and audit/current/source-crosswalk.json.
-/
