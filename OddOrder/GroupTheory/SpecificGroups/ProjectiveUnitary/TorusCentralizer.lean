/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.RootGroupStructure
import OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary.StandardGenerators

/-!
# The determinant-one torus does not act faithfully on `Ω₁(S₀)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. III, §1, Proposition, p. 117:

> But, if `G₀ = PSU(3, ℓ)`, `S₀` is a Sylow `2`-subgroup of `G₀` and
> `N_{G₀}(S₀) = S₀ ⋊ D₀`, then, **as can be checked**, `C_{D₀}(Ω₁(S₀)) ≠ 1`.

Peterfalvi does not carry out the check.  In the coordinates of this
development it is a computation in `𝔽_{ℓ²}^×`:

* `Ω₁(S₀)` is `{u : RootGroup n | u.fst = 0}`, and the torus acts on the second
  coordinate through the norm `N(c) = c · c* = c^{ℓ+1}` (`scalePoint_snd`);
* the determinant-one torus `D₀` is the image of `t ↦ t^{2ℓ − 1}`
  (`PSUTorusParameter`);
* for `c = t^{2ℓ−1}` the norm is `t^{(2ℓ−1)(ℓ+1)}`, which is `1` as soon as `t`
  has order dividing `ℓ + 1`;
* an element of order exactly `ℓ + 1` gives `c ≠ 1`, because
  `2ℓ − 1 = 2(ℓ + 1) − 3` makes `(ℓ + 1) ∣ (2ℓ − 1)` equivalent to
  `(ℓ + 1) ∣ 3`, i.e. to `ℓ ≤ 2`.

This is exactly the point where `PSU(3, ℓ)` differs from `Sz(ℓ)`: the Suzuki
torus acts *regularly* on the involutions of its root group
(`standardRootTorus_actsRegularlyOnInvolutions`), so its centralizer there is
trivial, while the unitary torus has the norm-one subgroup of order `ℓ + 1` in
its kernel.

## Main results

* `exists_ne_one_mem_psuTorus_torusWeight_eq_one` — a non-trivial parameter of
  the determinant-one torus with trivial norm.
* `exists_ne_one_mem_psuTorus_scalePoint_eq_of_fst_eq_zero` — the same in the
  form Peterfalvi uses: a non-trivial `c ∈ D₀` fixing every element of
  `Ω₁(S₀)`.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary

open scoped Pointwise

/-- The order of the multiplicative group of the quadratic field. -/
theorem natCard_units_field (n : ℕ) (hn : 0 < n) :
    Nat.card (Field n)ˣ = 2 ^ (2 * n) - 1 := by
  classical
  haveI : Fintype (Field n) := Fintype.ofFinite (Field n)
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card,
    natCard_field n hn]

/-- **`C_{D₀}(Ω₁(S₀)) ≠ 1`, in torus coordinates** (Peterfalvi Part II, Ch. III
§1, p. 117): the determinant-one torus contains a non-trivial parameter of norm
one.

`(Field n)ˣ` is cyclic of order `ℓ² − 1 = (ℓ − 1)(ℓ + 1)` with `ℓ = 2ⁿ`, so it
has an element `t` of order exactly `ℓ + 1`.  Then `c = t^{2ℓ−1}` lies in the
determinant-one torus and `c^{ℓ+1} = (t^{ℓ+1})^{2ℓ−1} = 1`, while `c ≠ 1`
because `(ℓ + 1) ∤ (2ℓ − 1)` for `ℓ ≥ 4`. -/
theorem exists_ne_one_mem_psuTorus_torusWeight_eq_one (n : ℕ) (hn : 1 < n) :
    ∃ c : GeneralTorusParameter n, c ∈ PSUTorusParameter n ∧ c ≠ 1 ∧
      torusWeight c = 1 := by
  classical
  have hn0 : 0 < n := Nat.zero_lt_one.trans hn
  set l : ℕ := 2 ^ n with hl
  have hl4 : 4 ≤ l := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  -- the unit group is cyclic of order `l² − 1`
  have hcard : Nat.card (Field n)ˣ = l ^ 2 - 1 := by
    rw [natCard_units_field n hn0, hl, ← pow_mul, mul_comm]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Field n)ˣ)
  have hgord : orderOf g = l ^ 2 - 1 := by
    rw [← hcard, orderOf_eq_card_of_forall_mem_zpowers hg]
  obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hkpos : 0 < k := by omega
  have hsub : l - 1 = k := by omega
  have hsq : l ^ 2 - 1 = k * (k + 2) := by
    have h1 : l ^ 2 = k * (k + 2) + 1 := by rw [hk]; ring
    omega
  have hdvd : (l - 1) ∣ l ^ 2 - 1 := ⟨k + 2, by rw [hsub, hsq]⟩
  set t : (Field n)ˣ := g ^ (l - 1) with ht
  have htord : orderOf t = l + 1 := by
    rw [ht, orderOf_pow_of_dvd (by omega) (hgord ▸ hdvd), hgord, hsub, hsq,
      Nat.mul_div_cancel_left _ hkpos]
    omega
  refine ⟨t ^ (2 * l - 1), ⟨t, rfl⟩, ?_, ?_⟩
  · -- `c ≠ 1` because `(l + 1) ∤ (2l − 1)`
    intro hc
    have hdvd' : orderOf t ∣ 2 * l - 1 := orderOf_dvd_of_pow_eq_one hc
    rw [htord] at hdvd'
    obtain ⟨j, hj⟩ := hdvd'
    have hj2 : j < 2 := by
      by_contra hge2
      push Not at hge2
      have hmul : (l + 1) * 2 ≤ (l + 1) * j := Nat.mul_le_mul_left _ hge2
      omega
    interval_cases j <;> omega
  · -- the norm is `t ^ ((2l − 1)(l + 1)) = 1`
    have htone : t ^ (l + 1) = 1 := by
      rw [← htord]; exact pow_orderOf_eq_one t
    have hone : (t ^ (2 * l - 1)) ^ (l + 1) = (1 : (Field n)ˣ) := by
      rw [← pow_mul, mul_comm, pow_mul, htone, one_pow]
    have hval : ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) ^ (l + 1) = 1 := by
      have hv := congrArg (Units.val (α := Field n)) hone
      simpa using hv
    rw [torusWeight, star_eq_conjugation, conjugation_apply n hn0]
    calc ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) *
        ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) ^ l
        = ((t ^ (2 * l - 1) : (Field n)ˣ) : Field n) ^ (l + 1) := by ring
      _ = 1 := hval

/-- **`C_{D₀}(Ω₁(S₀)) ≠ 1`** (Peterfalvi Part II, Ch. III §1, Proposition,
p. 117, the step stated "as can be checked").

`Ω₁(S₀)` is the centre line `{u | u.fst = 0}`
(`sq_eq_one_iff_fst_eq_zero`), on which the torus acts through the norm, so the
non-trivial norm-one parameter of the previous lemma fixes it pointwise. -/
theorem exists_ne_one_mem_psuTorus_scalePoint_eq_of_sq_eq_one (n : ℕ) (hn : 1 < n) :
    ∃ c : GeneralTorusParameter n, c ∈ PSUTorusParameter n ∧ c ≠ 1 ∧
      ∀ u : RootGroup n, u ^ 2 = 1 → scalePoint c u = u := by
  obtain ⟨c, hmem, hne, hw⟩ := exists_ne_one_mem_psuTorus_torusWeight_eq_one n hn
  refine ⟨c, hmem, hne, fun u hu => ?_⟩
  have hfst : u.fst = 0 := (RootGroup.sq_eq_one_iff_fst_eq_zero u).mp hu
  ext
  · rw [scalePoint_fst, hfst, mul_zero]
  · rw [scalePoint_snd, hw, one_mul]

end OddOrder.GroupTheory.SpecificGroups.ProjectiveUnitary
