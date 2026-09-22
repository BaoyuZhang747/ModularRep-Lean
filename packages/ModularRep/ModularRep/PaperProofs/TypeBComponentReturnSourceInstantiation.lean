import ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter

/-!
# Actual Brauer-character component return, with an honest wrap

This Type B file treats current Lemma 4.4.  `ComponentReturnFull` uses one
endomorphism on every edge and on the wrap of a cycle.  That presentation
does not cover an arbitrary permutation of factors: a return automorphism
need not have a root of the cycle length.  Here successors are normalised
to the identity and the wrap retains the actual return automorphism.

We reuse its product-orbit and cyclic-fixedness deductions and the checked
local semidirect stabiliser lemma.  The finite-product Brauer theorem is a
narrow E1 input: Navarro, *Characters and Blocks of Finite Groups*, product
definition p. 176 and Theorem (8.21), p. 177, iterated over a finite index.
Root agreement and the literal external-product formula are explicit.
No fixed tuple, global selector, or final stabiliser factorisation is an
external input.  A presentation of arbitrary original factors by these
normalised cycle coordinates remains a separate group-carrier obligation.
-/

noncomputable section

namespace ModularRep.PaperProofs.TypeBComponentReturnSourceInstantiation

open Formalisation
open ModularRep.ManuscriptVerification.ComponentReturnFull
open ModularRep.PaperProofs.TypeBRegularLeviCharacterActionAdapter
open ModularRep.PaperProofs.EvenFieldAssumption53Relative

section NormalisedCycleDeduction

variable {C : Type*} (n : C → ℕ) (hn : ∀ c, 0 < n c)
variable (D R X : C → Type*)
variable [∀ c, Group (D c)] [∀ c, Group (R c)]
variable [∀ c, MulAction (D c) (X c)] [∀ c, MulAction (R c) (X c)]

/-- The finite deduction with identity successors and an unrestricted actual
return on the wrap.  The representative and local factorisation are exactly
the hypothesis of the manuscript lemma, one per cycle. -/
theorem normalised_component_return
    (localPhi : ∀ c, R c →* MulAut (D c))
    (localCompat : ∀ c, SemidirectActionCompatible (X := X c) (localPhi c))
    (base : ComponentTuple n X) (representative : ∀ c, X c)
    (returnElement : ∀ c, R c)
    (hlocal : ∀ c, SemidirectStabilizerFactors
      (localPhi c) (localCompat c) (representative c))
    (hrep : ∀ c, representative c ∈
      MulAction.orbit (D c) (base (firstIndex n hn c)))
    {E : Type*} [Group E] [MulAction E (ComponentTuple n X)]
    (tau : E) (htau : Subgroup.zpowers tau = ⊤)
    (hstable : Set.MapsTo (tau • ·)
      (MulAction.orbit (ComponentGroup n D) base)
      (MulAction.orbit (ComponentGroup n D) base))
    (hfirst : ∀ (x : ComponentTuple n X) c,
      (tau • x) (firstIndex n hn c) =
        returnElement c • x (lastIndex n hn c))
    (hsucc : ∀ (x : ComponentTuple n X) c j (hj : j + 1 < n c),
      (tau • x) ⟨c, ⟨j + 1, hj⟩⟩ =
        x ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩) :
    ∃ theta : ComponentTuple n X,
      theta ∈ MulAction.orbit (ComponentGroup n D) base ∧
      (∀ c, returnElement c • representative c = representative c) ∧
      (∀ e : E, e • theta = theta) := by
  have hadj := coordinate_transport_maps_orbit_of_product_orbit_stable
    n D X tau (fun _ ↦ id) base hstable hsucc
  have hwrap := coordinate_wrap_maps_orbit_of_product_orbit_stable
    n D X hn tau (fun c x ↦ returnElement c • x) base hstable hfirst
  have hcoordinate : ∀ c j (hj : j < n c),
      representative c ∈ MulAction.orbit (D c) (base ⟨c, ⟨j, hj⟩⟩) := by
    intro c j
    induction j with
    | zero =>
        intro hj
        exact hrep c
    | succ j ih =>
        intro hj
        exact hadj c j hj (ih (Nat.lt_of_succ_lt hj))
  have hreturnOrbit : ∀ c, returnElement c • representative c ∈
      MulAction.orbit (D c) (representative c) := by
    intro c
    have h := hwrap c (hcoordinate c (n c - 1)
      (Nat.sub_lt (hn c) Nat.zero_lt_one))
    rw [MulAction.orbit_eq_iff.mpr (hrep c)]
    exact h
  have hreturn : ∀ c, returnElement c • representative c = representative c := by
    intro c
    apply fixed_return_of_semidirect_factorization
      (localPhi c) (localCompat c) (representative c) (returnElement c) (hlocal c)
    exact MulAction.mem_orbit_iff.mp (MulAction.mem_orbit_symm.mp (hreturnOrbit c))
  let theta : ComponentTuple n X := fun i ↦ representative i.1
  have horbit : theta ∈ MulAction.orbit (ComponentGroup n D) base := by
    apply (mem_product_orbit_iff n D X base theta).mpr
    intro i
    exact hcoordinate i.1 i.2.1 i.2.2
  have hfixed : tau • theta = theta := by
    funext i
    rcases i with ⟨c, j⟩
    by_cases hj : j.1 = 0
    · have heq : j = ⟨0, hn c⟩ := Fin.ext hj
      rw [heq, hfirst]
      exact hreturn c
    · have hpos : 0 < j.1 := Nat.pos_of_ne_zero hj
      have hm : j.1 - 1 + 1 = j.1 := Nat.sub_add_cancel hpos
      have hlt : j.1 - 1 + 1 < n c := hm.trans_lt j.2
      have heq : j = ⟨j.1 - 1 + 1, hlt⟩ := Fin.ext hm.symm
      rw [heq, hsucc]
  exact ⟨theta, horbit, hreturn,
    fixed_by_cyclic_group_of_generator tau htau theta hfixed⟩

end NormalisedCycleDeduction

section LiteralCharacters

variable {p : ℕ} {C k K : Type} [Fintype C]
variable (n : C → ℕ) (hn : ∀ c, 0 < n c)
variable (H D : C → Type)
variable [∀ c, Group (H c)] [∀ c, Finite (H c)] [∀ c, Group (D c)]
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]

/-- The literal finite product in the chosen cycle coordinates. -/
abbrev ProductGroup := (i : ComponentIndex n) → H i.1

abbrev DiagonalGroup := (i : ComponentIndex n) → D i.1

variable (iota : PrimeRegularRootEmbedding p k K (ProductGroup n H))
variable (iotaFactor : ∀ c, PrimeRegularRootEmbedding p k K (H c))
variable (diagonal : ∀ c, D c →* MulAut (H c))

/-- Evaluation at an actual factor. -/
def coordinateHom (i : ComponentIndex n) : ProductGroup n H →* H i.1 where
  toFun g := g i
  map_one' := rfl
  map_mul' _ _ := rfl

/-- A common modular-system external-product identification.  Its value
formula prevents an arbitrary equivariant relabelling of the characters.
The final field is the standard monomial naturality in precisely the
normalised coordinate form needed here; it is quantified independently of
the selected orbit, representatives and stabilisers. -/
structure FiniteProductSource extends
    DirectProductIBrIdentification
      (fun i : ComponentIndex n ↦ H i.1)
      (fun i : ComponentIndex n ↦ D i.1) iota
      (fun i ↦ iotaFactor i.1) (fun i ↦ diagonal i.1) where
  prime : Nat.Prime p
  roots_agree : ∀ c (zeta : rootsOfUnity (primeRegularExponent p (H c)) k),
    (iotaFactor c).lift (((zeta : kˣ) : k)) = iota.lift (((zeta : kˣ) : k))
  external_product : ∀ (psi : IBr iota)
      (g : PrimeRegularElement (G := ProductGroup n H) p),
    psi.1 g = ∏ i : ComponentIndex n,
      (characters psi i).1 ⟨g.1 i, g.2.map (coordinateHom n H i)⟩
  normalised_naturality : ∀ (a : MulAut (ProductGroup n H))
      (returnAut : ∀ c, MulAut (H c)),
    (∀ g c, a g (lastIndex n hn c) = returnAut c (g (firstIndex n hn c))) →
    (∀ g c j (hj : j + 1 < n c),
      a g ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ = g ⟨c, ⟨j + 1, hj⟩⟩) →
    (∀ psi c,
      characters (IrreducibleBrauerCharacter.twist iota psi a) (firstIndex n hn c) =
        IrreducibleBrauerCharacter.twist (iotaFactor c)
          (characters psi (lastIndex n hn c)) (returnAut c)) ∧
    (∀ psi c j (hj : j + 1 < n c),
      characters (IrreducibleBrauerCharacter.twist iota psi a) ⟨c, ⟨j + 1, hj⟩⟩ =
        characters psi ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)

/-- The componentwise automorphism homomorphism of the actual product. -/
abbrev diagonalAut := coordinateMulAut
  (fun i : ComponentIndex n ↦ H i.1)
  (fun i : ComponentIndex n ↦ D i.1) (fun i ↦ diagonal i.1)

variable {E : Type} [Group E] [Finite E] [IsCyclic E]
variable (outer : E →* MulAut (ProductGroup n H))

/-- The actual setwise stabiliser of the diagonal orbit on `IBr(N)`.
Both character actions use the established inverse-op right-action adapter. -/
def orbitSetwiseStabilizer (base : IBr iota) : Subgroup E := by
  letI := rightAutomorphismAction iota (diagonalAut n H D diagonal)
  letI := rightAutomorphismAction iota outer
  letI : MulAction E (Set (IBr iota)) := TypeBRightActionOrientation.imageSetMulAction
  exact MulAction.stabilizer E (MulAction.orbit (DiagonalGroup n D) base)

variable (base : IBr iota)
variable (tau : orbitSetwiseStabilizer n H D iota diagonal outer base)

/-- The return group is literally the subgroup generated by the cycle-length
power in the actual orbit stabiliser, not an independently named cyclic group. -/
abbrev ReturnGroup (c : C) := Subgroup.zpowers (tau ^ n c)

def returnElement (c : C) : ReturnGroup n H D iota diagonal outer base tau c :=
  ⟨tau ^ n c, Subgroup.mem_zpowers _⟩

variable (source : FiniteProductSource n hn H D iota iotaFactor diagonal)

/-- Lemma 4.4 on literal function-valued Brauer characters of the finite
product.  The only stabiliser factorisation premise is the local hypothesis
of the lemma.  The global orbit stabiliser and each return subgroup are
computed from the actual character orbit and the selected generator.

`generator_first` and `generator_succ` describe group automorphisms, not
character fixedness.  `return_coordinate` and `return_diagonal` bind the
local return homomorphisms to restrictions of the same actual ambient
actions.  Constructing these group-coordinate identifications from an
arbitrary original factor presentation is still an explicit application
obligation; no assertion that a return admits a cycle-length root is used.
-/
theorem component_return_source_instantiated
    (globalPhi : E →* MulAut (DiagonalGroup n D))
    (normalises : AutomorphismSemidirectCompatible
      (diagonalAut n H D diagonal) outer globalPhi)
    (htau : Subgroup.zpowers tau = ⊤)
    (returnAut : ∀ c, ReturnGroup n H D iota diagonal outer base tau c →*
      MulAut (H c))
    (localPhi : ∀ c, ReturnGroup n H D iota diagonal outer base tau c →*
      MulAut (D c))
    (localNormalises : ∀ c,
      AutomorphismSemidirectCompatible (diagonal c) (returnAut c) (localPhi c))
    (return_coordinate : ∀ c
      (r : ReturnGroup n H D iota diagonal outer base tau c) g,
      outer r.1.1 g (firstIndex n hn c) =
        returnAut c r (g (firstIndex n hn c)))
    (return_diagonal : ∀ c
      (r : ReturnGroup n H D iota diagonal outer base tau c) d,
      globalPhi r.1.1 d (firstIndex n hn c) = localPhi c r (d (firstIndex n hn c)))
    (generator_first : ∀ g c,
      outer tau.1⁻¹ g (lastIndex n hn c) =
        returnAut c (returnElement n H D iota diagonal outer base tau c)⁻¹
          (g (firstIndex n hn c)))
    (generator_succ : ∀ g c j (hj : j + 1 < n c),
      outer tau.1⁻¹ g ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ =
        g ⟨c, ⟨j + 1, hj⟩⟩)
    (representative : ∀ c, IBr (iotaFactor c))
    (representative_orbit : ∀ c,
      let _ := rightAutomorphismAction (iotaFactor c) (diagonal c)
      representative c ∈ MulAction.orbit (D c)
        (source.characters base (firstIndex n hn c)))
    (local_factorisation : ∀ c,
      let _ := rightAutomorphismAction (iotaFactor c) (diagonal c)
      let _ := rightAutomorphismAction (iotaFactor c) (returnAut c)
      SemidirectStabilizerFactors (localPhi c)
        (brauerRightActions_semidirectCompatible (iotaFactor c)
          (diagonal c) (returnAut c) (localPhi c) (localNormalises c))
        (representative c)) :
    let EO := orbitSetwiseStabilizer n H D iota diagonal outer base
    let _ := rightAutomorphismAction iota (diagonalAut n H D diagonal)
    let _ := rightAutomorphismAction iota (outer.comp EO.subtype)
    ∃ theta : IBr iota,
      theta ∈ MulAction.orbit (DiagonalGroup n D) base ∧
      (∀ e : EO, e • theta = theta) ∧
      SemidirectStabilizerFactors (globalPhi.comp EO.subtype)
        (brauerRightActions_semidirectCompatible iota
          (diagonalAut n H D diagonal) (outer.comp EO.subtype)
          (globalPhi.comp EO.subtype) (fun e d ↦ normalises e.1 d)) theta := by
  classical
  let EO := orbitSetwiseStabilizer n H D iota diagonal outer base
  let X := fun c ↦ IBr (iotaFactor c)
  letI factorAction (c : C) : MulAction (D c) (X c) :=
    rightAutomorphismAction (iotaFactor c) (diagonal c)
  letI returnAction (c : C) :
      MulAction (ReturnGroup n H D iota diagonal outer base tau c) (X c) :=
    rightAutomorphismAction (iotaFactor c) (returnAut c)
  letI : MulAction (DiagonalGroup n D) (IBr iota) :=
    rightAutomorphismAction iota (diagonalAut n H D diagonal)
  letI : MulAction EO (IBr iota) :=
    rightAutomorphismAction iota (outer.comp EO.subtype)
  letI : MulAction EO (ComponentTuple n X) := source.characters.symm.mulAction EO
  have hdiag : ∀ (d : DiagonalGroup n D) (psi : IBr iota),
      source.characters (d • psi) = d • source.characters psi := by
    intro d psi
    exact source.coordinate_naturality d⁻¹ psi
  have horbit : ∀ psi : IBr iota,
      source.characters psi ∈ MulAction.orbit (ComponentGroup n D)
          (source.characters base) ↔
        psi ∈ MulAction.orbit (DiagonalGroup n D) base := by
    intro psi
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, source.characters.injective ?_⟩
      rw [hdiag]
      exact hd
    · rintro ⟨d, rfl⟩
      exact ⟨d, (hdiag d base).symm⟩
  have hactualStable : Set.MapsTo
      (fun psi : IBr iota ↦ IrreducibleBrauerCharacter.twist iota psi (outer tau.1⁻¹))
      (MulAction.orbit (DiagonalGroup n D) base)
      (MulAction.orbit (DiagonalGroup n D) base) := by
    intro psi hpsi
    have hset := tau.property
    change (fun psi : IBr iota ↦
      IrreducibleBrauerCharacter.twist iota psi (outer tau.1⁻¹)) ''
        MulAction.orbit (DiagonalGroup n D) base =
          MulAction.orbit (DiagonalGroup n D) base at hset
    rw [← hset]
    exact ⟨psi, hpsi, rfl⟩
  have hstable : Set.MapsTo (tau • ·)
      (MulAction.orbit (ComponentGroup n D) (source.characters base))
      (MulAction.orbit (ComponentGroup n D) (source.characters base)) := by
    intro x hx
    change source.characters
      (IrreducibleBrauerCharacter.twist iota (source.characters.symm x)
        (outer tau.1⁻¹)) ∈ _
    apply (horbit _).mpr
    apply hactualStable
    apply (horbit _).mp
    simpa using hx
  obtain ⟨hfirstSource, hsuccSource⟩ := source.normalised_naturality
    (outer tau.1⁻¹)
    (fun c ↦ returnAut c (returnElement n H D iota diagonal outer base tau c)⁻¹)
    generator_first generator_succ
  have hfirst : ∀ (x : ComponentTuple n X) c,
      (tau • x) (firstIndex n hn c) =
        returnElement n H D iota diagonal outer base tau c • x (lastIndex n hn c) := by
    intro x c
    change source.characters
      (IrreducibleBrauerCharacter.twist iota (source.characters.symm x)
        (outer tau.1⁻¹)) (firstIndex n hn c) =
      IrreducibleBrauerCharacter.twist (iotaFactor c) (x (lastIndex n hn c))
        (returnAut c (returnElement n H D iota diagonal outer base tau c)⁻¹)
    simpa only [Equiv.apply_symm_apply] using hfirstSource (source.characters.symm x) c
  have hsucc : ∀ (x : ComponentTuple n X) c j (hj : j + 1 < n c),
      (tau • x) ⟨c, ⟨j + 1, hj⟩⟩ =
        x ⟨c, ⟨j, Nat.lt_of_succ_lt hj⟩⟩ := by
    intro x c j hj
    change source.characters
      (IrreducibleBrauerCharacter.twist iota (source.characters.symm x)
        (outer tau.1⁻¹)) ⟨c, ⟨j + 1, hj⟩⟩ = _
    simpa using hsuccSource (source.characters.symm x) c j hj
  let localCompat := fun c ↦ brauerRightActions_semidirectCompatible
    (iotaFactor c) (diagonal c) (returnAut c) (localPhi c) (localNormalises c)
  obtain ⟨x, hx, _, hfixed⟩ := normalised_component_return n hn D
    (fun c ↦ ↥(ReturnGroup n H D iota diagonal outer base tau c)) X localPhi localCompat
    (source.characters base) representative
    (returnElement n H D iota diagonal outer base tau)
    local_factorisation representative_orbit tau htau hstable hfirst hsucc
  have htheta : source.characters.symm x ∈
      MulAction.orbit (DiagonalGroup n D) base := by
    apply (horbit _).mp
    simpa using hx
  have hthetaFixed : ∀ e : EO, e • source.characters.symm x = source.characters.symm x := by
    intro e
    apply source.characters.injective
    have h := hfixed e
    change source.characters (e • source.characters.symm x) = x at h
    simpa only [Equiv.apply_symm_apply] using h
  refine ⟨source.characters.symm x, htheta, hthetaFixed, ?_⟩
  exact mem_semidirect_stabilizer_iff (globalPhi.comp EO.subtype)
    (brauerRightActions_semidirectCompatible iota
      (diagonalAut n H D diagonal) (outer.comp EO.subtype)
      (globalPhi.comp EO.subtype) (fun e d ↦ normalises e.1 d))
    (source.characters.symm x) hthetaFixed

end LiteralCharacters

end ModularRep.PaperProofs.TypeBComponentReturnSourceInstantiation


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
