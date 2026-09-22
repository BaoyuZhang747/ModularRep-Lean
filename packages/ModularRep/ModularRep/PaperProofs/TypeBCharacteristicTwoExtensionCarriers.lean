import ModularRep.PaperProofs.TypeBLemma47LeviApplication
import ModularRep.BrauerCharacterHomPullback

/-!
# Literal extension and Gallagher product carriers for Lemma 4.6

The extension is on the full ambient stabilizer of the selected Brauer
constituent. Its restriction is evaluated along the actual inclusion of N.
The product below evaluates that same extension on H_theta and multiplies
it by a modular linear character trivial on the embedded N. Neither an
invariance statement nor a stabilizer factorization is part of these data.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBCharacteristicTwoExtensionCarriers

open TypeBLemma47LeviApplication

universe u
variable {Gamma k K : Type u} [Group Gamma] [Finite Gamma]
variable [Field k] [Field K] [CharP k 2] [IsAlgClosed k] [CharZero K]

/-- The full ambient inertia group, with its actual conjugation action on IBr N. -/
abbrev AmbientInertia (N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN) :=
  @MulAction.stabilizer Gamma (IBr iotaN) _ (ambientBrauerAction N iotaN) theta

/-- The literal inclusion H_theta into Gamma_theta. -/
def inertiaInclusion (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN) :
    BrauerInertia H N iotaN theta →* AmbientInertia N iotaN theta where
  toFun x := ⟨x.1.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The literal inclusion N into Gamma_theta uses inner invariance of theta. -/
def baseInclusion (N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN) :
    N →* AmbientInertia N iotaN theta where
  toFun n := ⟨n.1, subgroup_element_fixes_brauer_character N iotaN n theta⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The manuscript extension hypothesis on its full, literal carrier. -/
structure AmbientExtension (N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta)) where
  character : IBr iotaA
  restriction : PrimeRegularClassFunction.pullback (baseInclusion N iotaN theta)
    character.1 = theta.1

/-- Pointwise restriction of the same ambient extension to H_theta. -/
def restrictedExtension (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
    (chi : IBr iotaA) : PrimeRegularClassFunction K (BrauerInertia H N iotaN theta) 2 :=
  PrimeRegularClassFunction.pullback (inertiaInclusion H N iotaN theta) chi.1

/-- The literal quotient-linear multiplication formula supplied by the
composite modular Gallagher certificate (Navarro 8.20 and abelian quotient
linearity). This is a formula, not an unspecified relation. -/
def HasGallagherProduct (H N : Subgroup Gamma) [N.Normal]
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN)
    (iotaI : PrimeRegularRootEmbedding 2 k K (BrauerInertia H N iotaN theta))
    (iotaA : PrimeRegularRootEmbedding 2 k K (AmbientInertia N iotaN theta))
    (chi : IBr iotaA) (eta : IBr iotaI) : Prop :=
  ∃ lambda : BrauerGallagherTwists (k := k) H N iotaN theta,
    eta.1 = PrimeRegularClassFunction.pointwiseMul
      (iotaI.liftedLinearCharacter lambda.1)
      (restrictedExtension H N iotaN theta iotaA chi)

/-- Both routes from N to Gamma_theta are the same inclusion. -/
theorem inclusion_square (H N : Subgroup Gamma) [N.Normal] (hNH : N ≤ H)
    (iotaN : PrimeRegularRootEmbedding 2 k K N) (theta : IBr iotaN) :
    (inertiaInclusion H N iotaN theta).comp
        (baseEmbeddingInBrauerInertia H N hNH iotaN theta) =
      baseInclusion N iotaN theta := rfl

end ModularRep.PaperProofs.TypeBCharacteristicTwoExtensionCarriers


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
