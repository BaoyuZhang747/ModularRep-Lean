import ModularRep.BrauerCharacterExtensionBridge
import ModularRep.BrauerCharacterHomPullback
import ModularRep.BrauerCharacterCommonRootCompatibility

/-! Individual cyclic extensions with the actual root agreement retained.
The universal representation-extension principle and an unselected ambient
root seed are inputs. Invariance, root agreement, and the resulting exact
character restriction are kept distinct. -/

noncomputable section

namespace ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions

open ModularRep Representation.Extension

universe u

theorem exists_extensionWitness_of_fixed
    {p : ℕ} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Finite A]
    (B : Subgroup A) [B.Normal]
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (rB : PrimeRegularRootEmbedding p k K B)
    (phiB : IBr rB)
    (hcyclic : IsCyclic (A ⧸ B))
    (hfixed : ∀ a : A,
      IrreducibleBrauerCharacter.twist rB phiB (MulAut.conjNormal a) = phiB)
    (rA : PrimeRegularRootEmbedding p k K A)
    (agreement : ∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
      rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) :
    Nonempty (BrauerCharacterExtensionWitness rA rB phiB) := by
  obtain ⟨W, hW, hphi, ⟨extension⟩⟩ :=
    Representation.exists_extension_realisation_of_ibr_fixed_cyclic_quotient
      principle rB phiB hcyclic hfixed
  have hcompat : Representation.BrauerRootLiftCompatibleAlong
      extension.representation rA rB B.subtype :=
    Representation.brauerRootLiftCompatibleAlong_of_eq_on_source_roots
      extension.representation rA rB B.subtype agreement
  exact ⟨Representation.Extension.brauerCharacterExtensionWitnessOfCompatible
    extension hW rA rB phiB hphi.symm hcompat⟩

theorem exists_extensionWitness_with_retained_agreement
    {p : ℕ} {k K A : Type u}
    [Field k] [Field K] [CharP k p] [IsAlgClosed k] [CharZero K]
    [Group A] [Finite A]
    (B : Subgroup A) [B.Normal]
    (principle : Representation.BrauerCyclicExtensionPrinciple.{u, u, u} p k)
    (rB : PrimeRegularRootEmbedding p k K B)
    (phiB : IBr rB)
    (hcyclic : IsCyclic (A ⧸ B))
    (hfixed : ∀ a : A,
      IrreducibleBrauerCharacter.twist rB phiB (MulAut.conjNormal a) = phiB)
    (seed : PrimeRegularRootEmbedding p k K A) :
    ∃ rA : PrimeRegularRootEmbedding p k K A,
      (∀ zeta : rootsOfUnity (primeRegularExponent p B) k,
        rB.lift (((zeta : kˣ) : k)) = rA.lift (((zeta : kˣ) : k))) ∧
      Nonempty (BrauerCharacterExtensionWitness rA rB phiB) := by
  obtain ⟨rA, agreement⟩ :=
    PrimeRegularRootEmbedding.exists_ambient_agreeing_on_subgroup B rB ⟨seed⟩
  exact ⟨rA, agreement,
    exists_extensionWitness_of_fixed B principle rB phiB hcyclic hfixed rA agreement⟩

def seedOnSubgroup
    {p : ℕ} {k K A : Type u}
    [Field k] [Field K] [Group A] [Finite A]
    (seed : PrimeRegularRootEmbedding p k K A) (D : Subgroup A) :
    PrimeRegularRootEmbedding p k K D :=
  PrimeRegularRootEmbedding.ofCommonRoot seed.prime seed.toMulEquiv (by
    simpa only [primeRegularExponent] using
      Nat.ordCompl_dvd_ordCompl_of_dvd (Subgroup.card_subgroup_dvd_card D) p)

theorem local_quotient_isCyclic
    {A : Type u} [Group A]
    (B D : Subgroup A) [B.Normal]
    (hcyclic : IsCyclic (A ⧸ B)) :
    IsCyclic (D ⧸ B.comap D.subtype) := by
  let : IsCyclic (A ⧸ B) := hcyclic
  let f : D ⧸ B.comap D.subtype →* A ⧸ B :=
    QuotientGroup.map (B.comap D.subtype) B D.subtype le_rfl
  have hf : Function.Injective f := by
    change Function.Injective (QuotientGroup.map (B.comap D.subtype) B D.subtype le_rfl)
    rw [← MonoidHom.ker_eq_bot_iff,
      QuotientGroup.ker_map, QuotientGroup.map_mk'_self]
  exact isCyclic_of_injective f hf

end ModularRep.PaperProofs.SporadicFi24P3Definition44NamedCarrierActualCyclicBrauerExtensions


/-
This file is part of ModularRep, the Lean companion to
Baoyu Zhang (2026), "On the inductive blockwise Alperin weight condition
for type B and type C".

The formalisation checks selected arguments under explicit external
assumptions. See FORMALISATION_GUIDE.md in the package root.
-/
