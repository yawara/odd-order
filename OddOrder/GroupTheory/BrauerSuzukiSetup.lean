import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.OrderOfElement

/-!
# Brauer–Suzuki: the generalized quaternion Sylow setup (Gorenstein Ch. 12, p. 373)

Setup for the generalized quaternion case of the Brauer–Suzuki theorem
(Gorenstein, *Finite Groups*, Ch. 12, issue 9318).  The book fixes

`S = ⟨x, y ∣ x^{2ⁿ} = 1, y² = x^{2ⁿ⁻¹}, xʸ = x⁻¹⟩`, `n ≥ 3` (so `|S| = 2^{n+1} ≥ 16`),

a generalized quaternion Sylow `2`-subgroup of `G`, and the derived objects
`X = ⟨x⟩`, `T = ⟨x²⟩`, `R = ⟨x⁴⟩`, `C = C_G(T)`, `N = N_G(T)`.

`QuaternionSylowSetup` carries the presentation data; this file develops the internal
structure of `S` that Ch. 12 uses throughout:

* `conj_x_zpow` / `y_inv_eq` — the computation rules of the presentation;
* `y_notMem_zpowers_x` — `y ∉ X` (derived, not assumed);
* `mem_iff` — the coset decomposition `S = X ∪ X·y` (every element is `xᵏ` or `xᵏ·y`).

The subsequent lemmas of Ch. 12 (`N = SH` and `C = XH`, the TI subset `A = C − RH`,
the character computation) live in sibling leaves.
-/

namespace OddOrder.GroupTheory

open Subgroup

/-- **The Gorenstein Ch. 12 setup** (p. 373): a generalized quaternion Sylow
`2`-subgroup of order `2^{n+1} ≥ 16`, presented by generators `x, y` with
`orderOf x = 2ⁿ`, `y² = x^{2ⁿ⁻¹}`, `y·x·y⁻¹ = x⁻¹`.  (That `y ∉ ⟨x⟩`, and hence
`|S| = 2^{n+1}`, is *derived* — see `y_notMem_zpowers_x`.) -/
structure QuaternionSylowSetup (G : Type*) [Group G] [Finite G] where
  /-- `|S| = 2^{n+1}`; the book's exponent parameter. -/
  n : ℕ
  /-- `n ≥ 3`, i.e. `|S| ≥ 16` — the range where ordinary character theory suffices. -/
  hn : 3 ≤ n
  /-- The generalized quaternion Sylow `2`-subgroup. -/
  S : Sylow 2 G
  /-- The generator of the cyclic maximal subgroup `X = ⟨x⟩`. -/
  x : G
  /-- The complementing generator, with `y² = x^{2ⁿ⁻¹}` and `xʸ = x⁻¹`. -/
  y : G
  hxS : x ∈ (S : Subgroup G)
  hyS : y ∈ (S : Subgroup G)
  hx_order : orderOf x = 2 ^ n
  hy_sq : y ^ 2 = x ^ 2 ^ (n - 1)
  hconj : y * x * y⁻¹ = x⁻¹
  hclosure : closure {x, y} = (S : Subgroup G)

namespace QuaternionSylowSetup

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-- Conjugation by `y` inverts every integer power of `x`. -/
theorem conj_x_zpow (k : ℤ) : Q.y * Q.x ^ k * Q.y⁻¹ = Q.x ^ (-k) := by
  rw [← conj_zpow, Q.hconj, inv_zpow, zpow_neg]

/-- `y·y = x^{2ⁿ⁻¹}` in integer-power form. -/
theorem y_mul_y : Q.y * Q.y = Q.x ^ ((2 ^ (Q.n - 1) : ℕ) : ℤ) := by
  rw [zpow_natCast, ← Q.hy_sq, sq]

/-- `y⁻¹ = x^{2ⁿ⁻¹}·y`: the inverse of `y` lies in the coset `X·y`. -/
theorem y_inv_eq : Q.y⁻¹ = Q.x ^ ((2 ^ (Q.n - 1) : ℕ) : ℤ) * Q.y := by
  have h2 : (Q.x ^ ((2 ^ (Q.n - 1) : ℕ) : ℤ) * Q.y) * Q.y = 1 := by
    rw [mul_assoc, Q.y_mul_y, ← zpow_add, ← Nat.cast_add, ← two_mul,
      show 2 * 2 ^ (Q.n - 1) = 2 ^ Q.n from by
        have := Q.hn
        rw [← pow_succ']
        congr 1
        omega,
      zpow_natCast, ← Q.hx_order, pow_orderOf_eq_one]
  exact (eq_inv_of_mul_eq_one_left h2).symm

/-- `y` is not a power of `x` (else conjugation by `y` would fix `x`, forcing
`x² = 1` against `orderOf x = 2ⁿ ≥ 8`). -/
theorem y_notMem_zpowers_x : Q.y ∉ zpowers Q.x := by
  rintro ⟨k, hk⟩
  have hk' : Q.x ^ k = Q.y := hk
  have hcomm : Q.y * Q.x * Q.y⁻¹ = Q.x := by
    rw [← hk']
    group
  have hx2 : Q.x ^ (2 : ℕ) = 1 := by
    have h : Q.x⁻¹ = Q.x := by rw [← Q.hconj, hcomm]
    rw [sq]
    nth_rewrite 1 [← h]
    rw [inv_mul_cancel]
  have := orderOf_dvd_of_pow_eq_one hx2
  rw [Q.hx_order] at this
  have h8 : (8 : ℕ) ∣ 2 ^ Q.n := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 Q.hn
  have := Nat.le_of_dvd (by norm_num) (h8.trans this)
  omega

/-- The coset decomposition of `S`: every element of `S` is `xᵏ` or `xᵏ·y`
(`S = X ∪ X·y`, Gorenstein p. 373). -/
theorem mem_iff {s : G} :
    s ∈ (Q.S : Subgroup G) ↔ ∃ k : ℤ, s = Q.x ^ k ∨ s = Q.x ^ k * Q.y := by
  constructor
  · -- the coset union is a subgroup containing `x` and `y`, hence contains `closure {x,y}`.
    intro hs
    rw [← Q.hclosure] at hs
    set c : ℤ := ((2 ^ (Q.n - 1) : ℕ) : ℤ) with hc
    let U : Subgroup G :=
      { carrier := {g | ∃ k : ℤ, g = Q.x ^ k ∨ g = Q.x ^ k * Q.y}
        one_mem' := ⟨0, Or.inl (by rw [zpow_zero])⟩
        mul_mem' := by
          rintro a b ⟨j, hj | hj⟩ ⟨k, hk | hk⟩ <;> subst hj <;> subst hk
          · exact ⟨j + k, Or.inl (by rw [zpow_add])⟩
          · exact ⟨j + k, Or.inr (by rw [zpow_add, mul_assoc])⟩
          · refine ⟨j - k, Or.inr ?_⟩
            have h := Q.conj_x_zpow k
            calc Q.x ^ j * Q.y * Q.x ^ k
                = Q.x ^ j * (Q.y * Q.x ^ k * Q.y⁻¹) * Q.y := by group
              _ = Q.x ^ j * Q.x ^ (-k) * Q.y := by rw [h]
              _ = Q.x ^ (j - k) * Q.y := by rw [← zpow_add, sub_eq_add_neg]
          · refine ⟨j - k + c, Or.inl ?_⟩
            have h := Q.conj_x_zpow k
            calc Q.x ^ j * Q.y * (Q.x ^ k * Q.y)
                = Q.x ^ j * (Q.y * Q.x ^ k * Q.y⁻¹) * (Q.y * Q.y) := by group
              _ = Q.x ^ j * Q.x ^ (-k) * Q.x ^ c := by rw [h, Q.y_mul_y]
              _ = Q.x ^ (j - k + c) := by rw [← zpow_add, ← zpow_add, sub_eq_add_neg]
        inv_mem' := by
          rintro a ⟨k, hk | hk⟩ <;> subst hk
          · exact ⟨-k, Or.inl (by rw [zpow_neg])⟩
          · refine ⟨c + k, Or.inr ?_⟩
            rw [mul_inv_rev, Q.y_inv_eq, ← zpow_neg]
            calc Q.x ^ c * Q.y * Q.x ^ (-k)
                = Q.x ^ c * (Q.y * Q.x ^ (-k) * Q.y⁻¹) * Q.y := by group
              _ = Q.x ^ c * Q.x ^ k * Q.y := by rw [Q.conj_x_zpow, neg_neg]
              _ = Q.x ^ (c + k) * Q.y := by rw [← zpow_add] }
    exact closure_le U |>.mpr (by
      rintro g (rfl | rfl)
      · exact ⟨1, Or.inl (zpow_one Q.x).symm⟩
      · exact ⟨0, Or.inr (by rw [zpow_zero, one_mul])⟩) hs
  · rintro ⟨k, rfl | rfl⟩
    · exact zpow_mem Q.hxS k
    · exact mul_mem (zpow_mem Q.hxS k) Q.hyS

end QuaternionSylowSetup

end OddOrder.GroupTheory
