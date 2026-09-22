import Formalisation.ComponentReturnAssembly
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# The full component-return deduction

This file formalises the complete representation-free deduction in manuscript
Lemma 4.4.  The component sets may be the Brauer-character sets occurring in
the manuscript, but no character theory is built into the theorem.

The primary source-shaped endpoint specifies the component actions, the
coordinate formula for a generator, setwise stability of the original product
orbit, and the local stabiliser factorisations.  It derives the adjacent and
wrap transport of coordinate orbits and the return-orbit membership.  The
returned tuple, its membership in the original product orbit, its fixedness
under the cyclic group, and its final semidirect-product stabiliser
factorisation are also proved here.
-/

namespace ModularRep.ManuscriptVerification.ComponentReturnFull

open Formalisation

variable {K : Type*}

/-- The dependent product of the component sets, indexed by the chosen cycle
decomposition. -/
abbrev ComponentTuple (n : K → Nat) (X : K → Type*) :=
  (i : ComponentIndex n) → X i.1

/-- The product of the groups acting on the individual coordinates. -/
abbrev ComponentGroup (n : K → Nat) (D : K → Type*) :=
  (i : ComponentIndex n) → D i.1

/-- The distinguished coordinate at the start of a component cycle. -/
abbrev firstIndex (n : K → Nat) (hn : ∀ k, 0 < n k) (k : K) : ComponentIndex n :=
  ⟨k, ⟨0, hn k⟩⟩

/-- The distinguished coordinate at the end of a component cycle. -/
abbrev lastIndex (n : K → Nat) (hn : ∀ k, 0 < n k) (k : K) : ComponentIndex n :=
  ⟨k, ⟨n k - 1, Nat.sub_lt (hn k) Nat.zero_lt_one⟩⟩

section ProductOrbit

variable (n : K → Nat) (D X : K → Type*)
variable [∀ k, Group (D k)] [∀ k, MulAction (D k) (X k)]

/-- Coordinatewise orbit membership is equivalent to membership in the orbit
under the full product group. -/
theorem mem_product_orbit_iff
    (base theta : ComponentTuple n X) :
    theta ∈ MulAction.orbit (ComponentGroup n D) base ↔
      ∀ i, theta i ∈ MulAction.orbit (D i.1) (base i) := by
  constructor
  · rintro ⟨d, rfl⟩ i
    exact MulAction.mem_orbit (base i) (d i)
  · intro h
    have hd : ∀ i, ∃ d : D i.1, d • base i = theta i := fun i ↦
      MulAction.mem_orbit_iff.mp (h i)
    choose d hd using hd
    refine MulAction.mem_orbit_iff.mpr ⟨d, ?_⟩
    funext i
    exact hd i

end ProductOrbit

section CoordinateTransport

variable (n : K → Nat) (D X : K → Type*)
variable [∀ k, Group (D k)] [∀ k, MulAction (D k) (X k)]

/-- If the chosen generator preserves the full product orbit, its coordinate
formula forces transport to carry each coordinate orbit to the next one.

This is the manuscript-specific passage from setwise stability of
`mathcal O` to the coordinate transport used when representatives are
propagated around a component cycle. -/
theorem coordinate_transport_maps_orbit_of_product_orbit_stable
    {E : Type*} [Group E] [MulAction E (ComponentTuple n X)]
    (tau : E) (transport : ∀ k, X k → X k)
    (base : ComponentTuple n X)
    (hproductOrbitStable :
      Set.MapsTo (tau • ·)
        (MulAction.orbit (ComponentGroup n D) base)
        (MulAction.orbit (ComponentGroup n D) base))
    (hgeneratorSucc : ∀ (x : ComponentTuple n X) k j
      (hj : j + 1 < n k),
      (tau • x) ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (x ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩)) :
    ∀ k j (hj : j + 1 < n k),
      Set.MapsTo (transport k)
        (MulAction.orbit (D k)
          (base ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩))
        (MulAction.orbit (D k) (base ⟨k, ⟨j + 1, hj⟩⟩)) := by
  classical
  intro k j hj y hy
  let source : ComponentIndex n :=
    ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩
  let target : ComponentIndex n := ⟨k, ⟨j + 1, hj⟩⟩
  let x : ComponentTuple n X := Function.update base source y
  have hxProduct : x ∈ MulAction.orbit (ComponentGroup n D) base :=
    (mem_product_orbit_iff n D X base x).mpr fun i ↦ by
      by_cases hi : i = source
      · subst i
        simpa [x, source] using hy
      · simp [x, hi]
  have htauProduct := hproductOrbitStable hxProduct
  have htauCoordinate :=
    (mem_product_orbit_iff n D X base (tau • x)).mp htauProduct target
  rw [hgeneratorSucc x k j hj] at htauCoordinate
  simpa [x, source] using htauCoordinate

/-- The same product-orbit argument at the wrap from the last coordinate of a
cycle back to its first coordinate. -/
theorem coordinate_wrap_maps_orbit_of_product_orbit_stable
    (hn : ∀ k, 0 < n k)
    {E : Type*} [Group E] [MulAction E (ComponentTuple n X)]
    (tau : E) (transport : ∀ k, X k → X k)
    (base : ComponentTuple n X)
    (hproductOrbitStable :
      Set.MapsTo (tau • ·)
        (MulAction.orbit (ComponentGroup n D) base)
        (MulAction.orbit (ComponentGroup n D) base))
    (hgeneratorFirst : ∀ (x : ComponentTuple n X) k,
      (tau • x) (firstIndex n hn k) =
        transport k (x (lastIndex n hn k))) :
    ∀ k,
      Set.MapsTo (transport k)
        (MulAction.orbit (D k) (base (lastIndex n hn k)))
        (MulAction.orbit (D k) (base (firstIndex n hn k))) := by
  classical
  intro k y hy
  let source : ComponentIndex n := lastIndex n hn k
  let target : ComponentIndex n := firstIndex n hn k
  let x : ComponentTuple n X := Function.update base source y
  have hxProduct : x ∈ MulAction.orbit (ComponentGroup n D) base :=
    (mem_product_orbit_iff n D X base x).mpr fun i ↦ by
      by_cases hi : i = source
      · subst i
        simpa [x, source] using hy
      · simp [x, hi]
  have htauProduct := hproductOrbitStable hxProduct
  have htauCoordinate :=
    (mem_product_orbit_iff n D X base (tau • x)).mp htauProduct target
  rw [hgeneratorFirst x k] at htauCoordinate
  simpa [x, source] using htauCoordinate

end CoordinateTransport

section GeneratorFixedness

variable {n : K → Nat} (hn : ∀ k, 0 < n k)
variable {X : K → Type*} (transport : ∀ k, X k → X k)
variable {E : Type*} [Group E] [MulAction E (ComponentTuple n X)]

/-- The coordinate formulas for a generator imply that a coherently
propagated tuple is fixed by that generator. -/
theorem generator_fixes_of_coordinate_transport
    (tau : E) (theta : ComponentTuple n X)
    (hgeneratorFirst : ∀ (x : ComponentTuple n X) k,
      (tau • x) (firstIndex n hn k) = transport k (x (lastIndex n hn k)))
    (hgeneratorSucc : ∀ (x : ComponentTuple n X) k j (hj : j + 1 < n k),
      (tau • x) ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (x ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩))
    (hpropagate : ∀ k j (hj : j + 1 < n k),
      theta ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (theta ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩))
    (hwrap : ∀ k,
      transport k (theta (lastIndex n hn k)) = theta (firstIndex n hn k)) :
    tau • theta = theta := by
  funext i
  rcases i with ⟨k, j⟩
  by_cases hj : j.1 = 0
  · have hjeq : j = ⟨0, hn k⟩ := Fin.ext hj
    rw [hjeq]
    rw [hgeneratorFirst]
    exact hwrap k
  · let m := j.1 - 1
    have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
    have hm : m + 1 = j.1 := Nat.sub_add_cancel hjpos
    have hm_lt : m + 1 < n k := hm.trans_lt j.2
    have hjeq : j = ⟨m + 1, hm_lt⟩ := Fin.ext hm.symm
    rw [hjeq]
    rw [hgeneratorSucc]
    exact (hpropagate k m hm_lt).symm

/-- Fixedness under a generator of a cyclic group implies fixedness under the
whole group. -/
theorem fixed_by_cyclic_group_of_generator
    (tau : E) (htau : Subgroup.zpowers tau = ⊤)
    (theta : ComponentTuple n X) (hfixed : tau • theta = theta) :
    ∀ e : E, e • theta = theta := by
  intro e
  have htauMem : tau ∈ MulAction.stabilizer E theta := hfixed
  have hle : Subgroup.zpowers tau ≤ MulAction.stabilizer E theta :=
    Subgroup.zpowers_le.mpr htauMem
  rw [htau] at hle
  exact hle (Subgroup.mem_top e)

end GeneratorFixedness

section FullReturn

variable (D R X : K → Type*)
variable [∀ k, Group (D k)] [∀ k, Group (R k)]
variable [∀ k, MulAction (D k) (X k)] [∀ k, MulAction (R k) (X k)]

/-- Full representation-free form of the component-return lemma.

The tuple `base` represents an arbitrary point of the original product orbit.
The hypotheses `hrepresentativeOrbit` and `htransportOrbit` assert only the
factorwise orbit information and its transport between adjacent coordinates.
The hypothesis `hreturnInOrbit` is only the pointwise consequence used in the
manuscript: the return of the chosen representative lies in its coordinate
orbit.  It is weaker than assuming that the return action preserves the whole
orbit.  These facts are sufficient to derive, rather than assume, membership
of the resulting tuple in the product orbit.

The two `hgenerator...` hypotheses give the coordinate action of the chosen
cyclic generator on every tuple.  Thus neither global fixedness nor the final
stabiliser factorisation occurs among the assumptions. -/
theorem component_return_full
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (localPhi : ∀ k, R k →* MulAut (D k))
    (localCompat : ∀ k, SemidirectActionCompatible (X := X k) (localPhi k))
    (transport : ∀ k, X k → X k)
    (base : ComponentTuple n X)
    (representative : ∀ k, X k)
    (returnElement : ∀ k, R k)
    (hreturnAction : ∀ k,
      (transport k)^[n k] (representative k) =
        returnElement k • representative k)
    (hlocalFactor : ∀ k,
      SemidirectStabilizerFactors
        (localPhi k) (localCompat k) (representative k))
    (hreturnInOrbit : ∀ k,
      returnElement k • representative k ∈
        MulAction.orbit (D k) (representative k))
    (hrepresentativeOrbit : ∀ k,
      representative k ∈
        MulAction.orbit (D k) (base (firstIndex n hn k)))
    (htransportOrbit : ∀ k j (hj : j + 1 < n k),
      Set.MapsTo (transport k)
        (MulAction.orbit (D k)
          (base ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩))
        (MulAction.orbit (D k) (base ⟨k, ⟨j + 1, hj⟩⟩)))
    {E : Type*} [Group E] [MulAction E (ComponentTuple n X)]
    (tau : E) (htau : Subgroup.zpowers tau = ⊤)
    (hgeneratorFirst : ∀ (x : ComponentTuple n X) k,
      (tau • x) (firstIndex n hn k) =
        transport k (x (lastIndex n hn k)))
    (hgeneratorSucc : ∀ (x : ComponentTuple n X) k j (hj : j + 1 < n k),
      (tau • x) ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (x ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩))
    (globalPhi : E →* MulAut (ComponentGroup n D))
    (globalCompat : SemidirectActionCompatible
      (X := ComponentTuple n X) globalPhi) :
    ∃ theta : ComponentTuple n X,
      theta ∈ MulAction.orbit (ComponentGroup n D) base ∧
      (∀ k, returnElement k • representative k = representative k) ∧
      (∀ e : E, e • theta = theta) ∧
      SemidirectStabilizerFactors globalPhi globalCompat theta := by
  have hcoset : ∀ k, ∃ d : D k,
      d • (returnElement k • representative k) = representative k := by
    intro k
    exact MulAction.mem_orbit_iff.mp
      (MulAction.mem_orbit_symm.mp (hreturnInOrbit k))
  obtain ⟨hreturnFixed, theta, hfirst, hsucc, hwrap⟩ :=
    component_return_assembly_of_semidirect_factorization
      D R X n hn localPhi localCompat transport representative returnElement
        hreturnAction hlocalFactor hcoset
  have hcoordinateOrbit : ∀ k j (hj : j < n k),
      theta ⟨k, ⟨j, hj⟩⟩ ∈
        MulAction.orbit (D k) (base ⟨k, ⟨j, hj⟩⟩) := by
    intro k j
    induction j with
    | zero =>
        intro hj
        rw [hfirst]
        exact hrepresentativeOrbit k
    | succ j ih =>
        intro hj
        rw [hsucc k j hj]
        exact htransportOrbit k j hj
          (ih (Nat.lt_of_succ_lt hj))
  have hproductOrbit : theta ∈
      MulAction.orbit (ComponentGroup n D) base :=
    (mem_product_orbit_iff n D X base theta).mpr fun i ↦ by
      rcases i with ⟨k, j⟩
      exact hcoordinateOrbit k j.1 j.2
  have htauFixed : tau • theta = theta :=
    generator_fixes_of_coordinate_transport hn transport tau theta
      hgeneratorFirst hgeneratorSucc hsucc hwrap
  have hEFixed : ∀ e : E, e • theta = theta :=
    fixed_by_cyclic_group_of_generator tau htau theta htauFixed
  have hglobalFactor :
      SemidirectStabilizerFactors globalPhi globalCompat theta :=
    mem_semidirect_stabilizer_iff globalPhi globalCompat theta hEFixed
  exact ⟨theta, hproductOrbit, hreturnFixed, hEFixed, hglobalFactor⟩

/-- Source-shaped form of `component_return_full` for manuscript Lemma 4.4.

Instead of assuming either the adjacent coordinate-orbit transport or the
return-orbit membership, this theorem assumes exactly that the chosen
generator belongs to the setwise stabiliser of the full product orbit.  The
coordinate formulas derive the transport around the cycle, including the
wrap, and hence derive that the full return of the selected representative
lies in its original coordinate orbit. -/
theorem component_return_full_of_product_orbit_stable
    (n : K → Nat) (hn : ∀ k, 0 < n k)
    (localPhi : ∀ k, R k →* MulAut (D k))
    (localCompat : ∀ k, SemidirectActionCompatible (X := X k) (localPhi k))
    (transport : ∀ k, X k → X k)
    (base : ComponentTuple n X)
    (representative : ∀ k, X k)
    (returnElement : ∀ k, R k)
    (hreturnAction : ∀ k,
      (transport k)^[n k] (representative k) =
        returnElement k • representative k)
    (hlocalFactor : ∀ k,
      SemidirectStabilizerFactors
        (localPhi k) (localCompat k) (representative k))
    (hrepresentativeOrbit : ∀ k,
      representative k ∈
        MulAction.orbit (D k) (base (firstIndex n hn k)))
    {E : Type*} [Group E] [MulAction E (ComponentTuple n X)]
    (tau : E) (htau : Subgroup.zpowers tau = ⊤)
    (hproductOrbitStable :
      Set.MapsTo (tau • ·)
        (MulAction.orbit (ComponentGroup n D) base)
        (MulAction.orbit (ComponentGroup n D) base))
    (hgeneratorFirst : ∀ (x : ComponentTuple n X) k,
      (tau • x) (firstIndex n hn k) =
        transport k (x (lastIndex n hn k)))
    (hgeneratorSucc : ∀ (x : ComponentTuple n X) k j (hj : j + 1 < n k),
      (tau • x) ⟨k, ⟨j + 1, hj⟩⟩ =
        transport k (x ⟨k, ⟨j, Nat.lt_of_succ_lt hj⟩⟩))
    (globalPhi : E →* MulAut (ComponentGroup n D))
    (globalCompat : SemidirectActionCompatible
      (X := ComponentTuple n X) globalPhi) :
    ∃ theta : ComponentTuple n X,
      theta ∈ MulAction.orbit (ComponentGroup n D) base ∧
      (∀ k, returnElement k • representative k = representative k) ∧
      (∀ e : E, e • theta = theta) ∧
      SemidirectStabilizerFactors globalPhi globalCompat theta := by
  have htransportOrbit :=
    coordinate_transport_maps_orbit_of_product_orbit_stable
      n D X tau transport base hproductOrbitStable hgeneratorSucc
  have hwrapOrbit :=
    coordinate_wrap_maps_orbit_of_product_orbit_stable
      n D X hn tau transport base hproductOrbitStable hgeneratorFirst
  have hreturnInOrbit : ∀ k,
      returnElement k • representative k ∈
        MulAction.orbit (D k) (representative k) := by
    intro k
    have hiterateCoordinate : ∀ j (hj : j < n k),
        (transport k)^[j] (representative k) ∈
          MulAction.orbit (D k) (base ⟨k, ⟨j, hj⟩⟩) := by
      intro j
      induction j with
      | zero =>
          intro hj
          simpa using hrepresentativeOrbit k
      | succ j ih =>
          intro hj
          rw [Function.iterate_succ_apply']
          exact htransportOrbit k j hj (ih (Nat.lt_of_succ_lt hj))
    have hlast := hiterateCoordinate (n k - 1)
      (Nat.sub_lt (hn k) Nat.zero_lt_one)
    have hclosed := hwrapOrbit k hlast
    have hnDecomposition : n k = (n k - 1) + 1 :=
      (Nat.sub_add_cancel (hn k)).symm
    have hclosedIterate :
        (transport k)^[n k] (representative k) ∈
          MulAction.orbit (D k) (base (firstIndex n hn k)) := by
      rw [hnDecomposition, Function.iterate_succ_apply']
      exact hclosed
    have hclosedReturn :
        returnElement k • representative k ∈
          MulAction.orbit (D k) (base (firstIndex n hn k)) := by
      rw [← hreturnAction k]
      exact hclosedIterate
    have horbitEq :
        MulAction.orbit (D k) (representative k) =
          MulAction.orbit (D k) (base (firstIndex n hn k)) :=
      MulAction.orbit_eq_iff.mpr (hrepresentativeOrbit k)
    rw [horbitEq]
    exact hclosedReturn
  exact component_return_full D R X n hn localPhi localCompat transport base
    representative returnElement hreturnAction hlocalFactor hreturnInOrbit
    hrepresentativeOrbit htransportOrbit tau htau hgeneratorFirst
    hgeneratorSucc globalPhi globalCompat

end FullReturn

end ModularRep.ManuscriptVerification.ComponentReturnFull


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
