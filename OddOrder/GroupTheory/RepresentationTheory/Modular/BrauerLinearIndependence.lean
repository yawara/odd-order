/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.RingTheory.Valuation.ValuationRing
import OddOrder.GroupTheory.RepresentationTheory.Modular.BrauerCharacterIndependence

/-!
# The irreducible Brauer characters are linearly independent

`mem_maximalIdeal_of_sum_irreducibleBrauerCharacter` says every relation among the `φ_i` on the
`p`-regular classes has all coefficients in `𝔪`.  Over a valuation ring that upgrades to `c = 0`:
divisibility is a total relation, so among finitely many coefficients one of them, say `c_j ≠ 0`,
divides all the others.  Dividing the relation through by `c_j` is again a relation, and its `j`-th
coefficient is `1` — which the one-step statement says lies in `𝔪`.

The classical argument runs over a *discrete* valuation ring, dividing by a uniformiser and
invoking Nakayama.  Taking the divisibility-minimal coefficient instead needs neither a uniformiser
nor Noetherianness, which matters because the splitting `p`-modular system `𝓞_ℂ_[p]`
(`PadicComplexSystem`) has divisible value group and is not Noetherian.

No representation theory enters here — the input is exactly the one-step statement above.

The statement is independence over `𝒪`; independence over the fraction field follows by clearing
denominators, which is not recorded here.

## Main results

* `OddOrder.RepresentationTheory.Modular.exists_dvd_forall_of_valuationRing`
* `OddOrder.RepresentationTheory.Modular.eq_zero_of_sum_irreducibleBrauerCharacter
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing Matrix MonoidAlgebra OddOrder.GroupTheory

/-- **A finite family in a valuation ring has a member dividing all of them.**  Divisibility is a
total relation there, so this is just the existence of a minimum. -/
theorem exists_dvd_forall_of_valuationRing {R ι : Type*} [CommRing R] [IsDomain R]
    [ValuationRing R] (c : ι → R) :
    ∀ s : Finset ι, s.Nonempty → ∃ j ∈ s, ∀ i ∈ s, c j ∣ c i := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro _
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨a, Finset.mem_insert_self _ _, by simp⟩
    obtain ⟨j, hj, hjmin⟩ := ih hs
    rcases ValuationRing.dvd_total (c a) (c j) with h | h
    · refine ⟨a, Finset.mem_insert_self _ _, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact dvd_rfl
      · exact h.trans (hjmin i hi)
    · refine ⟨j, Finset.mem_insert_of_mem hj, fun i hi => ?_⟩
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact h
      · exact hjmin i hi

variable {p : ℕ} {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]

/-- **The irreducible Brauer characters are linearly independent on the `p`-regular classes.**

Take a coefficient `c_j ≠ 0` dividing all the others; then `c_i / c_j` is again a relation, so
`mem_maximalIdeal_of_sum_irreducibleBrauerCharacter` puts its `j`-th coefficient `1` in `𝔪`. -/
theorem eq_zero_of_sum_irreducibleBrauerCharacter (hp : p.Prime)
    {ω : ResidueField 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
    {B : Type*} [Ring B] [Algebra (ResidueField 𝒪) B]
    {π : MonoidAlgebra (ResidueField 𝒪) G →ₐ[ResidueField 𝒪] B} (hπ : Function.Surjective π)
    {N : ℕ} (hker : ∀ y : MonoidAlgebra (ResidueField 𝒪) G, π y = 0 → y ^ N = 0)
    (e : B ≃ₐ[ResidueField 𝒪] ∀ i, Matrix (nn i) (nn i) (ResidueField 𝒪)) (c : ι → 𝒪)
    (h : ∀ g : G, IsPRegular p g →
      ∑ i, c i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g = 0) :
    c = 0 := by
  classical
  by_contra hc
  -- some coefficient is nonzero, and among those one divides all the others
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hc
  have hne : (Finset.univ.filter fun i => c i ≠ 0).Nonempty :=
    ⟨i₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩⟩
  obtain ⟨j, hjmem, hjmin⟩ := exists_dvd_forall_of_valuationRing c _ hne
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjmem).2
  have hdvdall : ∀ i, c j ∣ c i := by
    intro i
    by_cases hi : c i = 0
    · exact hi ▸ dvd_zero _
    · exact hjmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  choose d hd using hdvdall
  -- dividing through by `c j` leaves a relation whose `j`-th coefficient is `1`
  have hdj : d j = 1 := (mul_left_cancel₀ hcj (by rw [← hd j, mul_one])).symm
  have hdrel : ∀ g : G, IsPRegular p g →
      ∑ i, d i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g = 0 := by
    intro g hg
    have hfac : c j * ∑ i, d i * irreducibleBrauerCharacter (p := p) (𝒪 := 𝒪)
        (e.toAlgHom.comp π).toRingHom i g = 0 := by
      rw [Finset.mul_sum, ← h g hg]
      exact Finset.sum_congr rfl fun i _ => by rw [hd i]; ring
    exact (mul_eq_zero.mp hfac).resolve_left hcj
  have hmem := mem_maximalIdeal_of_sum_irreducibleBrauerCharacter hp hω hπ hker e d hdrel j
  rw [hdj] at hmem
  exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).mpr hmem)

end OddOrder.RepresentationTheory.Modular
