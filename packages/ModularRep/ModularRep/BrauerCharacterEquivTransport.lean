import ModularRep.IrreducibleBrauerCharacter
import ModularRep.Twist

/-!
# Transport of Brauer characters along a group equivalence

This file transports the explicit prime regular root embedding and the
function-valued irreducible Brauer characters used by the project along a
group equivalence.  The construction is purely formal: no character-theoretic
existence statement is assumed.
-/

noncomputable section

namespace ModularRep

universe u v w x

namespace PrimeRegularRootEmbedding

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w} {H : Type x}
variable [Field k] [Field K] [Group G] [Finite G] [Group H] [Finite H]

private def rootMulEquivTransport {m n : ℕ} (h : m = n)
    (f : rootsOfUnity m k ≃* rootsOfUnity m K) :
    rootsOfUnity n k ≃* rootsOfUnity n K :=
  h ▸ f

private noncomputable def rootLiftForExponent (n : ℕ)
    (f : rootsOfUnity n k ≃* rootsOfUnity n K) : k → K :=
  Function.extend
    (fun zeta : rootsOfUnity n k ↦ (((zeta : kˣ) : k)))
    (fun zeta ↦ (((f zeta : rootsOfUnity n K) : Kˣ) : K))
    (fun _ ↦ 0)

private theorem rootLiftForExponent_transport {m n : ℕ} (h : m = n)
    (f : rootsOfUnity m k ≃* rootsOfUnity m K) :
    rootLiftForExponent n (rootMulEquivTransport h f) =
      rootLiftForExponent m f := by
  subst n
  rfl

/-- Transport a chosen root embedding along an equivalence of finite groups.
The two root-of-unity groups have the same exponent because equivalent finite
groups have the same cardinality. -/
def alongMulEquiv (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) : PrimeRegularRootEmbedding p k K H where
  prime := iota.prime
  toMulEquiv := rootMulEquivTransport
    (congrArg (fun n : ℕ ↦ ordCompl[p] n) (Nat.card_congr e.toEquiv))
    iota.toMulEquiv

/-- Transporting the ambient group leaves the field-level root lift
unchanged. -/
theorem alongMulEquiv_lift (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (z : k) :
    (iota.alongMulEquiv e).lift z = iota.lift z := by
  change rootLiftForExponent (primeRegularExponent p H)
      (rootMulEquivTransport
        (congrArg (fun n : ℕ ↦ ordCompl[p] n) (Nat.card_congr e.toEquiv))
        iota.toMulEquiv) z =
    rootLiftForExponent (primeRegularExponent p G) iota.toMulEquiv z
  exact congrFun (rootLiftForExponent_transport
    (congrArg (fun n : ℕ ↦ ordCompl[p] n) (Nat.card_congr e.toEquiv))
    iota.toMulEquiv) z

end PrimeRegularRootEmbedding

namespace PrimeRegularClassFunction

variable {R : Type v} {G : Type w} {H : Type x}
variable [Group G] [Group H]

/-- Pull a prime regular class function back along a group homomorphism. -/
def pullback (f : H →* G) (chi : PrimeRegularClassFunction R G p) :
    PrimeRegularClassFunction R H p where
  toFun := chi.toFun.pullback f
  map_conj x g := by
    change chi (PrimeRegularElement.map f
      ⟨x * g.1 * x⁻¹, g.2.conj x⟩) =
        chi (PrimeRegularElement.map f g)
    have hmap :
        PrimeRegularElement.map f
            ⟨x * g.1 * x⁻¹, g.2.conj x⟩ =
          ⟨f x * (PrimeRegularElement.map f g).1 * (f x)⁻¹,
            (PrimeRegularElement.map f g).2.conj (f x)⟩ := by
      apply Subtype.ext
      change f (x * g.1 * x⁻¹) = f x * f g.1 * (f x)⁻¹
      simp
    rw [hmap]
    exact chi.map_conj (f x) (PrimeRegularElement.map f g)

@[simp]
theorem pullback_apply (f : H →* G)
    (chi : PrimeRegularClassFunction R G p)
    (g : PrimeRegularElement (G := H) p) :
    pullback f chi g = chi (PrimeRegularElement.map f g) :=
  rfl

end PrimeRegularClassFunction

end ModularRep

namespace Representation

universe u v w x y

variable {p : ℕ} {k : Type u} {K : Type v}
variable {G : Type w} {H : Type x} {V : Type y}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Brauer-character formation commutes with transport of a representation
and its chosen root embedding along an equivalence of finite groups. -/
theorem brauerCharacterOfRootEmbedding_pullback_mulEquiv
    (rho : Representation k G V)
    (iota : ModularRep.PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) :
    (rho.pullback e.symm.toMonoidHom).brauerCharacterOfRootEmbedding
        (iota.alongMulEquiv e) =
      ModularRep.PrimeRegularClassFunction.pullback e.symm.toMonoidHom
        (rho.brauerCharacterOfRootEmbedding iota) := by
  apply ModularRep.PrimeRegularClassFunction.ext
  intro g
  change (((rho (e.symm g.1)).charpoly.roots.map
      (iota.alongMulEquiv e).lift).sum) =
    ((rho (e.symm g.1)).charpoly.roots.map iota.lift).sum
  rw [show (iota.alongMulEquiv e).lift = iota.lift from
    funext (iota.alongMulEquiv_lift e)]

end Representation

namespace ModularRep

universe u v w x

variable {p : ℕ} {k : Type u} {K : Type v} {G : Type w} {H : Type x}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group G] [Finite G] [Group H] [Finite H]

namespace IrreducibleBrauerCharacter

/-- Transport a function-valued irreducible Brauer character along a group
equivalence.  The affording representation is pulled back canonically, and
irreducibility follows from surjectivity of the equivalence. -/
def alongMulEquiv (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) : IBr (iota.alongMulEquiv e) := by
  refine ⟨PrimeRegularClassFunction.pullback e.symm.toMonoidHom phi.1, ?_⟩
  rcases phi.2 with ⟨V, hV, hphi⟩
  refine ⟨FDRep.of (Representation.pullback V.ρ e.symm.toMonoidHom),
    hV.pullback e.symm.toMonoidHom e.symm.surjective, ?_⟩
  rw [FDRep.of_ρ', hphi,
    Representation.brauerCharacterOfRootEmbedding_pullback_mulEquiv]

@[simp]
theorem alongMulEquiv_val
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) :
    (alongMulEquiv iota e phi).1 =
      PrimeRegularClassFunction.pullback e.symm.toMonoidHom phi.1 :=
  rfl

/-- The transported irreducible Brauer character realises the literal
pullback class function, so no separate irreducibility witness is needed. -/
theorem pullback_isIrreducibleBrauerCharacter
    (iota : PrimeRegularRootEmbedding p k K G)
    (e : G ≃* H) (phi : IBr iota) :
    IsIrreducibleBrauerCharacter (iota.alongMulEquiv e)
      (PrimeRegularClassFunction.pullback e.symm.toMonoidHom phi.1) :=
  (alongMulEquiv iota e phi).2

end IrreducibleBrauerCharacter

end ModularRep


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
