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

/-! ### The derived objects `X`, `T`, `R`, `C`, `N`, `z` (Gorenstein p. 373) -/

/-- `X = ⟨x⟩`, the cyclic maximal subgroup of `S`. -/
def X : Subgroup G := zpowers Q.x

/-- `T = ⟨x²⟩` (`= S'`, the derived subgroup of `S`). -/
def T : Subgroup G := zpowers (Q.x ^ (2 : ℕ))

/-- `R = ⟨x⁴⟩`. -/
def R : Subgroup G := zpowers (Q.x ^ (4 : ℕ))

/-- `C = C_G(T)`. -/
def C : Subgroup G := centralizer (Q.T : Set G)

/-- `N = N_G(T)`. -/
def N : Subgroup G := Subgroup.normalizer Q.T

/-- `z = x^{2ⁿ⁻¹} = y²`, the unique involution of `S`. -/
def z : G := Q.x ^ 2 ^ (Q.n - 1)

theorem z_eq_y_sq : Q.z = Q.y ^ 2 := Q.hy_sq.symm

theorem z_sq : Q.z ^ 2 = 1 := by
  rw [z, ← pow_mul, ← pow_succ,
    show Q.n - 1 + 1 = Q.n from by have := Q.hn; omega,
    ← Q.hx_order, pow_orderOf_eq_one]

theorem z_ne_one : Q.z ≠ 1 := by
  intro h
  have := orderOf_dvd_of_pow_eq_one (h ▸ rfl : Q.x ^ 2 ^ (Q.n - 1) = 1)
  rw [Q.hx_order] at this
  have hlt : (2 : ℕ) ^ (Q.n - 1) < 2 ^ Q.n :=
    Nat.pow_lt_pow_right one_lt_two (by have := Q.hn; omega)
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero (by positivity)) this
  omega

/-- Conjugation by an element of the coset `X·y` inverts every power of `x`. -/
theorem coset_conj_x_zpow (k j : ℤ) :
    (Q.x ^ k * Q.y) * Q.x ^ j * (Q.x ^ k * Q.y)⁻¹ = Q.x ^ (-j) := by
  rw [mul_inv_rev]
  calc Q.x ^ k * Q.y * Q.x ^ j * (Q.y⁻¹ * (Q.x ^ k)⁻¹)
      = Q.x ^ k * (Q.y * Q.x ^ j * Q.y⁻¹) * (Q.x ^ k)⁻¹ := by group
    _ = Q.x ^ k * Q.x ^ (-j) * (Q.x ^ k)⁻¹ := by rw [Q.conj_x_zpow]
    _ = Q.x ^ (-j) := by group

/-- Every element of `S` outside `X` squares to the central involution `z`
(so `X·y` contains no involution). -/
theorem coset_sq_eq_z (k : ℤ) : (Q.x ^ k * Q.y) ^ 2 = Q.z := by
  rw [sq]
  calc (Q.x ^ k * Q.y) * (Q.x ^ k * Q.y)
      = (Q.x ^ k * (Q.y * Q.x ^ k * Q.y⁻¹)) * (Q.y * Q.y) := by group
    _ = (Q.x ^ k * Q.x ^ (-k)) * Q.x ^ ((2 ^ (Q.n - 1) : ℕ) : ℤ) := by
        rw [Q.conj_x_zpow, Q.y_mul_y]
    _ = Q.x ^ ((2 ^ (Q.n - 1) : ℕ) : ℤ) := by group
    _ = Q.z := by rw [zpow_natCast]; rfl

/-- **The unique involution of `S`** (Gorenstein p. 375, used for Lemma 1.7): an
element of `S` squaring to `1` is `1` or `z`. -/
theorem eq_one_or_eq_z_of_sq_eq_one {s : G} (hs : s ∈ (Q.S : Subgroup G))
    (h2 : s ^ 2 = 1) : s = 1 ∨ s = Q.z := by
  rcases Q.mem_iff.mp hs with ⟨k, rfl | rfl⟩
  · -- `x^{2k} = 1` forces `2ⁿ⁻¹ ∣ k`, so `xᵏ ∈ {1, z}`.
    have hzp : Q.x ^ (2 * k) = 1 := by
      rw [two_mul, zpow_add, ← sq]; exact h2
    have hdvd : ((2 ^ Q.n : ℕ) : ℤ) ∣ 2 * k := by
      rw [← Q.hx_order]
      exact orderOf_dvd_iff_zpow_eq_one.mpr hzp
    have h2n : ((2 ^ Q.n : ℕ) : ℤ) = 2 * ((2 ^ (Q.n - 1) : ℕ) : ℤ) := by
      push_cast
      rw [← pow_succ']
      congr 1
      have := Q.hn
      omega
    rw [h2n] at hdvd
    obtain ⟨m, hm⟩ := (mul_dvd_mul_iff_left (two_ne_zero (α := ℤ))).mp hdvd
    subst hm
    rw [zpow_mul, show Q.x ^ ((2 ^ (Q.n - 1) : ℕ) : ℤ) = Q.z from by rw [zpow_natCast]; rfl]
    have hz2 : Q.z ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Q.z_sq]
    rcases Int.even_or_odd m with ⟨t, ht⟩ | ⟨t, ht⟩
    · left
      rw [ht, ← two_mul, zpow_mul, hz2, one_zpow]
    · right
      rw [ht, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]
  · -- the coset `X·y` squares to `z ≠ 1`.
    exfalso
    exact Q.z_ne_one (by rw [← Q.coset_sq_eq_z k, h2])

/-! ### Membership normal forms and the first structural facts -/

theorem mem_X_iff {g : G} : g ∈ Q.X ↔ ∃ k : ℤ, g = Q.x ^ k := by
  rw [X, mem_zpowers_iff]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

theorem mem_T_iff {g : G} : g ∈ Q.T ↔ ∃ m : ℤ, g = Q.x ^ (2 * m) := by
  rw [T, mem_zpowers_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [← hm, ← zpow_natCast Q.x 2, ← zpow_mul]; norm_num⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm, ← zpow_natCast Q.x 2, ← zpow_mul]; norm_num⟩

theorem mem_R_iff {g : G} : g ∈ Q.R ↔ ∃ m : ℤ, g = Q.x ^ (4 * m) := by
  rw [R, mem_zpowers_iff]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [← hm, ← zpow_natCast Q.x 4, ← zpow_mul]; norm_num⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm, ← zpow_natCast Q.x 4, ← zpow_mul]; norm_num⟩

/-- Elements of `S` conjugate `T` into `T` (`xᵏ` centralizes, the coset `X·y`
inverts). -/
theorem conj_mem_T_of_mem {s t : G} (hs : s ∈ (Q.S : Subgroup G)) (ht : t ∈ Q.T) :
    s * t * s⁻¹ ∈ Q.T := by
  obtain ⟨m, rfl⟩ := Q.mem_T_iff.mp ht
  rcases Q.mem_iff.mp hs with ⟨k, rfl | rfl⟩
  · rw [show Q.x ^ k * Q.x ^ (2 * m) * (Q.x ^ k)⁻¹ = Q.x ^ (2 * m) from by group]
    exact Q.mem_T_iff.mpr ⟨m, rfl⟩
  · rw [Q.coset_conj_x_zpow k (2 * m)]
    exact Q.mem_T_iff.mpr ⟨-m, by rw [neg_mul_eq_mul_neg]⟩

/-- **`T ⊴ S`** (Gorenstein p. 374, opening of Lemma 1.2): `S ≤ N = N_G(T)`. -/
theorem S_le_N : (Q.S : Subgroup G) ≤ Q.N := by
  intro s hs
  rw [N, Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact fun ht => Q.conj_mem_T_of_mem hs ht
  · intro ht
    have h := Q.conj_mem_T_of_mem (inv_mem hs) ht
    rwa [show s⁻¹ * (s * t * s⁻¹) * s⁻¹⁻¹ = t from by group] at h

/-- `X ≤ C`: powers of `x` centralize `T ≤ ⟨x⟩`. -/
theorem X_le_C : Q.X ≤ Q.C := by
  intro g hg
  obtain ⟨k, rfl⟩ := Q.mem_X_iff.mp hg
  rw [C, Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨m, rfl⟩ := Q.mem_T_iff.mp hh
  exact zpow_mul_comm Q.x (2 * m) k

/-- **`S ∩ C = X`** (Gorenstein p. 374): `S` does not centralize `T` beyond `X`,
because conjugation by any element of `X·y` sends `x²` to `x⁻²` and `x⁴ ≠ 1`. -/
theorem S_inf_C_eq_X : (Q.S : Subgroup G) ⊓ Q.C = Q.X := by
  apply le_antisymm
  · rintro s ⟨hsS, hsC⟩
    rcases Q.mem_iff.mp hsS with ⟨k, rfl | rfl⟩
    · exact Q.mem_X_iff.mpr ⟨k, rfl⟩
    · exfalso
      have hx2T : Q.x ^ (2 : ℤ) ∈ (Q.T : Set G) := Q.mem_T_iff.mpr ⟨1, by norm_num⟩
      rw [C] at hsC
      have hcomm := Subgroup.mem_centralizer_iff.mp hsC _ hx2T
      have hconj2 : (Q.x ^ k * Q.y) * Q.x ^ (2 : ℤ) * (Q.x ^ k * Q.y)⁻¹ = Q.x ^ (2 : ℤ) := by
        rw [← hcomm]; group
      rw [Q.coset_conj_x_zpow k 2] at hconj2
      -- `x⁻² = x²` forces `x⁴ = 1`, against `orderOf x = 2ⁿ ≥ 8`.
      have h4 : Q.x ^ (4 : ℤ) = 1 := by
        calc Q.x ^ (4 : ℤ) = Q.x ^ (2 : ℤ) * Q.x ^ (2 : ℤ) := by
              rw [← zpow_add]; norm_num
          _ = Q.x ^ (2 : ℤ) * Q.x ^ (-2 : ℤ) := by rw [← hconj2]
          _ = 1 := by rw [← zpow_add]; norm_num
      have hdvd : ((orderOf Q.x : ℕ) : ℤ) ∣ (4 : ℤ) := orderOf_dvd_iff_zpow_eq_one.mpr h4
      have : (orderOf Q.x : ℕ) ∣ 4 := by exact_mod_cast hdvd
      rw [Q.hx_order] at this
      have h8 : (8 : ℕ) ∣ 2 ^ Q.n := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
        exact pow_dvd_pow 2 Q.hn
      have := Nat.le_of_dvd (by norm_num) this
      have := Nat.le_of_dvd (by norm_num) h8
      omega
  · exact le_inf (by rw [X]; exact zpowers_le.mpr Q.hxS) Q.X_le_C

end QuaternionSylowSetup

end OddOrder.GroupTheory
