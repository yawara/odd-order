/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.Modular.CartanInverse
import OddOrder.GroupTheory.RepresentationTheory.Modular.PPrimeOrderSemisimple

/-!
# The Cartan matrix of a `p'`-group is the identity

Navarro (2.12).  For `p ∤ |G|` the decomposition matrix `D` is a permutation matrix, so
`C = DᵀD = 1`.  The proof here is a dimension count rather than a module-theoretic one:

* `∑_φ n_φ ^ 2 = |G| = ∑_i m_i ^ 2`, comparing `k[G] ≅ ∏_φ M_{n_φ}(k)` (Maschke, the kernel of the
  splitting is `J(kG) = ⊥`) with `K[G] ≅ ∏_i M_{m_i}(K)`;
* `m_i = ∑_φ d_{iφ} n_φ`, which is the decomposition of the `i`-th ordinary character evaluated at
  `1`;
* every diagonal entry of `C` is at least `1`: a zero one would make the whole `φ`-column of `C`
  vanish, and `C` is invertible (`sum_cartanMatrix_mul_pairingZero`).

Expanding the middle identity gives `∑_{φ,μ} c_{φμ} n_φ n_μ = ∑_φ n_φ ^ 2`, and the three facts
force every term to be exactly what it must be: `c_{φφ} = 1` and `c_{φμ} = 0` off the diagonal.

## Main results

* `OddOrder.RepresentationTheory.Modular.sum_decompositionMatrix_mul_card_eq` —
  `m_i = ∑_φ d_{iφ} n_φ`
* `OddOrder.RepresentationTheory.Modular.one_le_cartanMatrix_self` — `c_{φφ} ≥ 1`
* `OddOrder.RepresentationTheory.Modular.cartanMatrix_eq_ite_of_not_dvd_card` — **`C = 1`**

## References

* G. Navarro, *Characters and Blocks of Finite Groups*, (2.12) (p. 25).
-/

namespace OddOrder.RepresentationTheory.Modular

open IsLocalRing MonoidAlgebra OddOrder.GroupTheory

variable {p : ℕ} {𝒪 K : Type*} [CommRing 𝒪] [IsDomain 𝒪] [ValuationRing 𝒪]
  [HenselianLocalRing 𝒪] [IsPModularSystem p 𝒪]
  [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
variable {G ι : Type*} [Group G] [Finite G] {nn : ι → Type*}
  [∀ i, Fintype (nn i)] [∀ i, DecidableEq (nn i)] [Fintype ι] [∀ i, Nonempty (nn i)]
variable {ι' : Type*} {m : ι' → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [Fintype ι'] [∀ i, Nonempty (m i)]

variable (hp : p.Prime) {ω : 𝒪} (hω : IsPrimitiveRoot ω (pRegularExponent p G))
  {ω' : ResidueField 𝒪} (hω' : IsPrimitiveRoot ω' (pRegularExponent p G))
  {π : MonoidAlgebra (ResidueField 𝒪) G →+* ∀ j, Matrix (nn j) (nn j) (ResidueField 𝒪)}
  (hπ : Function.Surjective π)
  (hlin : ∀ (c : ResidueField 𝒪) (a : MonoidAlgebra (ResidueField 𝒪) G), π (c • a) = c • π a)
  (hkerJ : RingHom.ker π = Ring.jacobson (MonoidAlgebra (ResidueField 𝒪) G))
  (e : MonoidAlgebra K G ≃ₐ[K] ∀ j, Matrix (m j) (m j) K)

/-! ### The degrees -/

omit [Fintype ι'] [∀ i, Nonempty (m i)] in
include hp hω hω' hπ hlin hkerJ e in
/-- **`m_i = ∑_φ d_{iφ} n_φ`**: the decomposition of the `i`-th ordinary character at `g = 1`. -/
theorem sum_decompositionMatrix_mul_card_eq (i : ι') :
    ∑ φ, decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ * Fintype.card (nn φ)
      = Fintype.card (m i) := by
  classical
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have hdec := trace_eq_sum_decompositionMatrix hp hω hω' hπ hlin hkerJ e i 1 (isPRegular_one hp)
  rw [Finset.sum_congr rfl fun φ (_ : φ ∈ Finset.univ) => by
    rw [irreducibleBrauerCharacter_one (p := p) (𝒪 := 𝒪) π hp φ]] at hdec
  have hK := congrArg (algebraMap 𝒪 K) hdec
  rw [map_sum, ← ordinaryCharacter, algebraMap_ordinaryCharacter (𝒪 := 𝒪) e i 1] at hK
  have hone : LinearMap.trace K (m i → K) (wedderburnRepresentation e i 1)
      = (Fintype.card (m i) : K) := by
    rw [map_one, LinearMap.trace_one, Module.finrank_pi]
  rw [hone] at hK
  have : ((Fintype.card (m i) : ℕ) : K)
      = ((∑ φ, decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ
          * Fintype.card (nn φ) : ℕ) : K) := by
    rw [hK]
    push_cast
    exact Finset.sum_congr rfl fun φ _ => rfl
  exact (Nat.cast_injective this).symm

/-! ### The diagonal of `C` is positive -/

include hp hω hω' hπ hlin hkerJ e in
/-- **`c_{φφ} ≥ 1`.**  A vanishing diagonal entry `c_{φφ} = ∑_i d_{iφ} ^ 2` forces the whole
column `d_{·φ}` to vanish, hence the whole column of `C`; but `C` is invertible. -/
theorem one_le_cartanMatrix_self (φ : ι) :
    1 ≤ cartanMatrix hp hω hω' hπ hlin hkerJ e φ φ := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  have : Invertible (Nat.card G : K) :=
    invertibleOfNonzero (by exact_mod_cast (Nat.card_pos (α := G)).ne')
  by_contra hcon
  have hzero : cartanMatrix hp hω hω' hπ hlin hkerJ e φ φ = 0 := by omega
  -- the whole column `d_{·φ}` vanishes
  have hcol : ∀ i : ι', decompositionMatrix hp hω hω' hπ hlin hkerJ e i φ = 0 := by
    intro i
    have hsum : ∑ j : ι', decompositionMatrix hp hω hω' hπ hlin hkerJ e j φ
        * decompositionMatrix hp hω hω' hπ hlin hkerJ e j φ = 0 := hzero
    exact mul_self_eq_zero.mp (Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_univ i))
  -- hence the whole column of `C`
  have hCcol : ∀ μ : ι, cartanMatrix hp hω hω' hπ hlin hkerJ e μ φ = 0 := fun μ =>
    Finset.sum_eq_zero fun i _ => by rw [hcol i, Nat.mul_zero]
  have hinv := sum_cartanMatrix_mul_pairingZero (K := K) hp hω hω' hπ hlin hkerJ e φ φ
  rw [Finset.sum_congr rfl fun μ (_ : μ ∈ Finset.univ) => by
    rw [hCcol μ, Nat.cast_zero, zero_mul], Finset.sum_const_zero, if_pos rfl] at hinv
  exact zero_ne_one hinv

/-! ### `C = 1` -/

open scoped Classical in
include hp hω hω' hπ hlin hkerJ e in
/-- **Navarro (2.12)**: the Cartan matrix of a `p'`-group is the identity. -/
theorem cartanMatrix_eq_ite_of_not_dvd_card [IsAlgClosed (ResidueField 𝒪)]
    (hG : ¬ p ∣ Nat.card G) (φ μ : ι) :
    cartanMatrix hp hω hω' hπ hlin hkerJ e φ μ = if φ = μ then 1 else 0 := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective 𝒪 K)
  set n : ι → ℕ := fun φ => Fintype.card (nn φ) with hn
  set D : ι' → ι → ℕ := decompositionMatrix hp hω hω' hπ hlin hkerJ e with hD
  set c : ι → ι → ℕ := cartanMatrix hp hω hω' hπ hlin hkerJ e with hc
  have hcdef : ∀ a b : ι, c a b = ∑ i : ι', D i a * D i b := fun _ _ => rfl
  have hnpos : ∀ a, 0 < n a := fun _ => Fintype.card_pos
  -- both sides of the dimension count
  have hkside : ∑ a, n a ^ 2 = Nat.card G := by
    refine sum_sq_card_eq_card_of_bijective π ⟨?_, hπ⟩ hlin
    rw [RingHom.injective_iff_ker_eq_bot, hkerJ]
    exact jacobson_monoidAlgebra_eq_bot hp (CharP.cast_eq_zero (ResidueField 𝒪) p) hG
  have hKside : ∑ i : ι', Fintype.card (m i) ^ 2 = Nat.card G :=
    sum_sq_card_eq_card_of_bijective e.toRingEquiv.toRingHom e.bijective
      fun a x => e.toLinearEquiv.map_smul a x
  -- expand `m_i = ∑_φ d_{iφ} n_φ` and collect the double sum into `C`
  have hterm : ∀ i : ι', Fintype.card (m i) ^ 2
      = ∑ a, ∑ b, D i a * D i b * (n a * n b) := by
    intro i
    rw [pow_two, ← sum_decompositionMatrix_mul_card_eq hp hω hω' hπ hlin hkerJ e i,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hD]; ring
  have hswap : ∑ i : ι', (∑ a, ∑ b, D i a * D i b * (n a * n b))
      = ∑ a, ∑ b, c a b * (n a * n b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => by rw [hcdef a b, Finset.sum_mul]
  have hexpand : ∑ a, n a ^ 2 = ∑ a, ∑ b, c a b * (n a * n b) := by
    rw [hkside, ← hKside, ← hswap]
    exact Finset.sum_congr rfl fun i _ => hterm i
  -- each row of the expansion is at least `n a ^ 2`, so all slack vanishes
  have hrow : ∀ a : ι, n a ^ 2 ≤ ∑ b, c a b * (n a * n b) := by
    intro a
    calc n a ^ 2 = 1 * (n a * n a) := by rw [one_mul, pow_two]
      _ ≤ c a a * (n a * n a) :=
          Nat.mul_le_mul_right _ (one_le_cartanMatrix_self hp hω hω' hπ hlin hkerJ e a)
      _ ≤ ∑ b, c a b * (n a * n b) :=
          Finset.single_le_sum (f := fun b => c a b * (n a * n b))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
  have hrows : ∀ a ∈ Finset.univ, n a ^ 2 = ∑ b, c a b * (n a * n b) :=
    (Finset.sum_eq_sum_iff_of_le fun a _ => hrow a).mp hexpand
  -- read off the two conclusions for the fixed `φ`
  have hφ := (hrows φ (Finset.mem_univ φ)).symm
  have hdiag : c φ φ * (n φ * n φ) ≤ n φ ^ 2 := hφ ▸
    Finset.single_le_sum (f := fun b => c φ b * (n φ * n b))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ φ)
  have hcφφ : c φ φ = 1 := by
    have h1 := one_le_cartanMatrix_self hp hω hω' hπ hlin hkerJ e φ
    have hpos : 0 < n φ * n φ := Nat.mul_pos (hnpos φ) (hnpos φ)
    rw [pow_two] at hdiag
    nlinarith [hdiag, h1, hpos]
  by_cases hμ : φ = μ
  · rw [if_pos hμ, ← hμ]
    exact hcφφ
  · rw [if_neg hμ]
    have hsplit : ∑ b ∈ Finset.univ.erase φ, c φ b * (n φ * n b) = 0 := by
      have hae := Finset.add_sum_erase Finset.univ (fun b => c φ b * (n φ * n b))
        (Finset.mem_univ φ)
      rw [hφ, hcφφ, one_mul, ← pow_two] at hae
      omega
    have hzero : c φ μ * (n φ * n μ) = 0 :=
      Finset.sum_eq_zero_iff.mp hsplit μ
        (Finset.mem_erase.mpr ⟨fun h => hμ h.symm, Finset.mem_univ μ⟩)
    rcases Nat.mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (Nat.mul_pos (hnpos φ) (hnpos μ)).ne'

end OddOrder.RepresentationTheory.Modular
