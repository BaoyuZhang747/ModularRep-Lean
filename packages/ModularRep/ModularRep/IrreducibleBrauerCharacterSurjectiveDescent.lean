import ModularRep.BrauerCharacterHomPullback
import ModularRep.RepresentationSurjectiveDescent

/-!
# Irreducible Brauer characters across a finite surjection

For a finite surjection whose kernel has order prime to `p`, every
`p`-regular target element has a `p`-regular lift.  Hence pullback is
injective on prime regular class functions.  An irreducible Brauer character
upstairs descends exactly when it carries an affording irreducible modular
representation on which the kernel acts trivially.

The equivalence below is constructed from those facts.  It does not assume a
quotient-side character, a reverse pullback identity, a character
correspondence, block data, weights, BAW, or iBAW.
-/

noncomputable section

namespace ModularRep.IrreducibleBrauerCharacterSurjectiveDescent

open ModularRep.RepresentationSurjectiveDescent

universe u

/-- If the image of an element is `p`-regular and the kernel order is prime
to `p`, then the element itself is `p`-regular. -/
theorem isPrimeRegular_of_map_of_ker_card_coprime
    {p : Nat} {A B : Type u} [Group A] [Group B]
    (f : A →* B) (hkerPrimeTo : (Nat.card f.ker).Coprime p)
    (a : A) (ha : IsPrimeRegular p (f a)) :
    IsPrimeRegular p a := by
  have hmem : a ^ orderOf (f a) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  have hpow :
      (a ^ orderOf (f a)) ^ Nat.card f.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      (Subgroup.orderOf_dvd_natCard f.ker hmem)
  have horder : orderOf a ∣ orderOf (f a) * Nat.card f.ker := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    simpa only [pow_mul] using hpow
  exact Nat.Coprime.of_dvd_left horder
    (Nat.Coprime.mul_left ha hkerPrimeTo)

/-- A finite surjection with prime-to-`p` kernel is surjective on the literal
subtypes of `p`-regular elements. -/
theorem primeRegularElement_map_surjective_of_ker_card_coprime
    {p : Nat} {A B : Type u} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (hkerPrimeTo : (Nat.card f.ker).Coprime p) :
    Function.Surjective (PrimeRegularElement.map (p := p) f) := by
  intro b
  obtain ⟨a, ha⟩ := hf b.1
  refine ⟨⟨a, ?_⟩, ?_⟩
  · apply isPrimeRegular_of_map_of_ker_card_coprime f hkerPrimeTo a
    simpa only [ha] using b.2
  · apply Subtype.ext
    exact ha

/-- Under the same hypotheses, pullback is injective on all literal
prime regular class functions. -/
theorem primeRegularClassFunction_pullback_injective_of_ker_card_coprime
    {p : Nat} {K A B : Type u} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (hkerPrimeTo : (Nat.card f.ker).Coprime p) :
    Function.Injective
      (fun chi : PrimeRegularClassFunction K B p =>
        PrimeRegularClassFunction.pullback f chi) := by
  intro chi psi heq
  apply PrimeRegularClassFunction.ext
  intro b
  obtain ⟨a, ha⟩ :=
    primeRegularElement_map_surjective_of_ker_card_coprime
      f hf hkerPrimeTo b
  have hvalue := congrArg
    (fun eta : PrimeRegularClassFunction K A p => eta a) heq
  change chi (PrimeRegularElement.map f a) =
    psi (PrimeRegularElement.map f a) at hvalue
  simpa only [ha] using hvalue

variable {p : Nat} {k K A B : Type u}
variable [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
variable [Group A] [Finite A] [Group B] [Finite B]

/-- The literal upstairs irreducible Brauer characters equipped with the
property needed for descent: some exact affording irreducible `FDRep` is
trivial on the kernel.  The representation is existential proof data, not a
preselected quotient character or equivalence. -/
def KernelTrivialIBrAlong
    (f : A →* B) (iotaA : PrimeRegularRootEmbedding p k K A) :=
  {phi : IBr iotaA //
    exists V : FDRep k A,
      Representation.IsIrreducible V.ρ ∧
      phi.1 = Representation.brauerCharacterOfRootEmbedding V.ρ iotaA ∧
      f.ker ≤ V.ρ.ker}

private noncomputable def affordingRepresentation
    {G : Type u} [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota) :
    FDRep k G :=
  Classical.choose phi.2

private theorem affordingRepresentation_irreducible
    {G : Type u} [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota) :
    Representation.IsIrreducible (affordingRepresentation iota phi).ρ :=
  (Classical.choose_spec phi.2).1

private theorem affordingRepresentation_character
    {G : Type u} [Group G] [Finite G]
    (iota : PrimeRegularRootEmbedding p k K G) (phi : IBr iota) :
    phi.1 = Representation.brauerCharacterOfRootEmbedding
      (affordingRepresentation iota phi).ρ iota :=
  (Classical.choose_spec phi.2).2

private noncomputable def kernelTrivialRepresentation
    (f : A →* B) (iotaA : PrimeRegularRootEmbedding p k K A)
    (phi : KernelTrivialIBrAlong f iotaA) : FDRep k A :=
  Classical.choose phi.2

private theorem kernelTrivialRepresentation_irreducible
    (f : A →* B) (iotaA : PrimeRegularRootEmbedding p k K A)
    (phi : KernelTrivialIBrAlong f iotaA) :
    Representation.IsIrreducible
      (kernelTrivialRepresentation f iotaA phi).ρ :=
  (Classical.choose_spec phi.2).1

private theorem kernelTrivialRepresentation_character
    (f : A →* B) (iotaA : PrimeRegularRootEmbedding p k K A)
    (phi : KernelTrivialIBrAlong f iotaA) :
    phi.1.1 = Representation.brauerCharacterOfRootEmbedding
      (kernelTrivialRepresentation f iotaA phi).ρ iotaA :=
  (Classical.choose_spec phi.2).2.1

private theorem kernelTrivialRepresentation_kernel
    (f : A →* B) (iotaA : PrimeRegularRootEmbedding p k K A)
    (phi : KernelTrivialIBrAlong f iotaA) :
    f.ker ≤ (kernelTrivialRepresentation f iotaA phi).ρ.ker :=
  (Classical.choose_spec phi.2).2.2

/-- Pull a quotient `IBr` character upstairs and retain the exact pulled-back
representation as its kernel-trivial witness. -/
noncomputable def inflateToKernelTrivialIBrAlong
    (f : A →* B) (hf : Function.Surjective f)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (hcompat : ∀ W : FDRep k B,
      Representation.BrauerRootLiftCompatibleAlong
        W.ρ iotaB iotaA f)
    (phi : IBr iotaB) :
    KernelTrivialIBrAlong f iotaA := by
  let V := affordingRepresentation iotaB phi
  let rho : Representation k A V := Representation.pullback V.ρ f
  have hV : Representation.IsIrreducible V.ρ :=
    affordingRepresentation_irreducible iotaB phi
  have hrho : Representation.IsIrreducible rho := hV.pullback f hf
  have hcharacter :
      PrimeRegularClassFunction.pullback f phi.1 =
        Representation.brauerCharacterOfRootEmbedding rho iotaA := by
    calc
      PrimeRegularClassFunction.pullback f phi.1 =
          PrimeRegularClassFunction.pullback f
            (Representation.brauerCharacterOfRootEmbedding V.ρ iotaB) :=
        congrArg (PrimeRegularClassFunction.pullback f)
          (affordingRepresentation_character iotaB phi)
      _ = Representation.brauerCharacterOfRootEmbedding rho iotaA :=
        (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
          V.ρ iotaB iotaA f (hcompat V)).symm
  let phiA : IBr iotaA :=
    ⟨PrimeRegularClassFunction.pullback f phi.1,
      ⟨FDRep.of rho, by simpa only [FDRep.of_ρ'] using hrho,
        by simpa only [FDRep.of_ρ'] using hcharacter⟩⟩
  refine ⟨phiA, ?_⟩
  refine ⟨FDRep.of rho, by simpa only [FDRep.of_ρ'] using hrho, ?_, ?_⟩
  · simpa only [phiA, FDRep.of_ρ'] using hcharacter
  · intro a ha
    change V.ρ (f a) = 1
    rw [MonoidHom.mem_ker.mp ha]
    exact map_one V.ρ

/-- The first literal pullback identity: the underlying upstairs class
function of inflation is definitionally the pullback of the quotient one. -/
theorem inflateToKernelTrivialIBrAlong_val
    (f : A →* B) (hf : Function.Surjective f)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (hcompat : ∀ W : FDRep k B,
      Representation.BrauerRootLiftCompatibleAlong
        W.ρ iotaB iotaA f)
    (phi : IBr iotaB) :
    (inflateToKernelTrivialIBrAlong f hf iotaA iotaB hcompat phi).1.1 =
      PrimeRegularClassFunction.pullback f phi.1 :=
  rfl

/-- Descend an upstairs `IBr` character by descending the exact affording
representation stored in its kernel-triviality property. -/
noncomputable def descendIBrAlong
    (f : A →* B) (hf : Function.Surjective f)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (phi : KernelTrivialIBrAlong f iotaA) : IBr iotaB := by
  let V := kernelTrivialRepresentation f iotaA phi
  let hkernel : f.ker ≤ V.ρ.ker :=
    kernelTrivialRepresentation_kernel f iotaA phi
  let rhoB := descend f hf V.ρ hkernel
  exact
    ⟨Representation.brauerCharacterOfRootEmbedding rhoB iotaB,
      ⟨FDRep.of rhoB,
        by
          simpa only [FDRep.of_ρ'] using
            (descend_irreducible f hf V.ρ hkernel
              (kernelTrivialRepresentation_irreducible f iotaA phi)),
        rfl⟩⟩

/-- The second literal pullback identity: the newly constructed quotient
character pulls back to the supplied upstairs character. -/
theorem descendIBrAlong_pullback
    (f : A →* B) (hf : Function.Surjective f)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (hcompat : ∀ W : FDRep k B,
      Representation.BrauerRootLiftCompatibleAlong
        W.ρ iotaB iotaA f)
    (phi : KernelTrivialIBrAlong f iotaA) :
    PrimeRegularClassFunction.pullback f
        (descendIBrAlong f hf iotaA iotaB phi).1 =
      phi.1.1 := by
  let V := kernelTrivialRepresentation f iotaA phi
  let hkernel : f.ker ≤ V.ρ.ker :=
    kernelTrivialRepresentation_kernel f iotaA phi
  let rhoB := descend f hf V.ρ hkernel
  change PrimeRegularClassFunction.pullback f
      (Representation.brauerCharacterOfRootEmbedding rhoB iotaB) = phi.1.1
  calc
    PrimeRegularClassFunction.pullback f
        (Representation.brauerCharacterOfRootEmbedding rhoB iotaB) =
      Representation.brauerCharacterOfRootEmbedding
        (rhoB.pullback f) iotaA :=
      (Representation.brauerCharacterOfRootEmbedding_pullback_of_compatible
        rhoB iotaB iotaA f (by
          simpa only [FDRep.of_ρ'] using hcompat (FDRep.of rhoB))).symm
    _ = Representation.brauerCharacterOfRootEmbedding V.ρ iotaA := by
      rw [show rhoB.pullback f = V.ρ from
        descend_pullback f hf V.ρ hkernel]
    _ = phi.1.1 :=
      (kernelTrivialRepresentation_character f iotaA phi).symm

/-- Inflation and the constructed descent are mutually inverse.  Thus a
quotient `IBr` carrier is equivalent to the literal subtype of upstairs
characters with an exact kernel-trivial affording representation. -/
noncomputable def quotientIBrEquivKernelTrivialIBrAlong
    (f : A →* B) (hf : Function.Surjective f)
    (hkerPrimeTo : (Nat.card f.ker).Coprime p)
    (iotaA : PrimeRegularRootEmbedding p k K A)
    (iotaB : PrimeRegularRootEmbedding p k K B)
    (hcompat : ∀ W : FDRep k B,
      Representation.BrauerRootLiftCompatibleAlong
        W.ρ iotaB iotaA f) :
    IBr iotaB ≃ KernelTrivialIBrAlong f iotaA where
  toFun := inflateToKernelTrivialIBrAlong f hf iotaA iotaB hcompat
  invFun := descendIBrAlong f hf iotaA iotaB
  left_inv phi := by
    apply Subtype.ext
    apply
      primeRegularClassFunction_pullback_injective_of_ker_card_coprime
        f hf hkerPrimeTo
    simpa only [inflateToKernelTrivialIBrAlong_val] using
      (descendIBrAlong_pullback f hf iotaA iotaB hcompat
        (inflateToKernelTrivialIBrAlong f hf iotaA iotaB hcompat phi))
  right_inv phi := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [inflateToKernelTrivialIBrAlong_val] using
      (descendIBrAlong_pullback f hf iotaA iotaB hcompat phi)

end ModularRep.IrreducibleBrauerCharacterSurjectiveDescent


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
