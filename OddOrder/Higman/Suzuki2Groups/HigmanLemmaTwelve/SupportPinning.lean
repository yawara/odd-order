/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaTwelve.TwoPowerCongruence

/-!
# Higman Lemma 12: support pinning for the mixed Frobenius pairing

G. Higman, *Suzuki 2-groups*, pp. 90--92.  The mixed term of the ambient
square map, expanded in the Frobenius monomial basis as
`M(α, β) = ∑ c_{ij} α^{2^i} β^{2^j}`, satisfies the equivariance constraint
`c_{ij} (λ^{2^i} μ^{2^j} - ν) = 0`; each nonzero coefficient therefore sits at
a pair `(i, j)` with `λ^{2^i} μ^{2^j} = ν`.  This file pins down those pairs
in each of Higman's cases, feeding the eigenvalue equation into the exponent
arithmetic of `TwoPowerCongruence`:

* `θ = φ` (pp. 90--91): `μ = λ` (`eq_of_pow_eq_pow_orderOf` — both solve
  `x^{1+2^r} = ν` and the exponent is invertible mod `2^n - 1`), and
  `(i, j) = (0, 0)` for `r = 0`, `(i, j) ∈ {(0, r), (r, 0)}` for `r ≠ 0`
  (`higman_typeB_support_pinning`); `G` heads towards `B(n, θ, ε)`.
* `θ ≠ 1`, `φ = 1`, `0 < r ≤ n/2` (p. 91): `2r + 1 = n` and
  `(i, j) = (n - 1, r + 1)` — the single monomial of `C(n, ε)`
  (`higman_typeC_support_pinning`).
* `θ, φ` independent (pp. 91--92): `s ≡ 2r`, `5r ≡ 0` and
  `(i, j) ≡ (3r, r) (mod n)`, or its mirror under `X ↔ Y` — the single
  monomial of `D(n, θ, ε)` (`higman_typeD_support_pinning`).

The common upstream input `orderOf λ = 2^n - 1` (with the implicit
`gcd(1 + 2^r, 2^n - 1) = 1`) is recovered from the primitivity of
`ν = λ θ(λ)` by `orderOf_eq_and_coprime_of_pow_eq_orderOf`.
-/

set_option autoImplicit false

namespace OddOrder.Higman.Suzuki2Groups

open Finset

/-! ### Eigenvalue order recovery

`ν = λ^{1+2^r}` is a primitive `(2^n - 1)`-st root of unity, so `λ` itself is
one and the exponent `1 + 2^r` is invertible mod `2^n - 1`.  Higman uses both
facts silently (p. 90: "for some primitive `(2^n - 1)`-st root of unity `λ`"). -/

/-- If `λ ^ m` has full order `N` and `λ ^ N = 1`, then `λ` itself has order
`N` and `m` is coprime to `N`. -/
theorem orderOf_eq_and_coprime_of_pow_eq_orderOf {F : Type*} [Monoid F]
    {lam nu : F} {m N : ℕ} (hN : 0 < N) (hm : m ≠ 0)
    (hord : orderOf nu = N) (hlam : lam ^ m = nu) (hpow : lam ^ N = 1) :
    orderOf lam = N ∧ Nat.Coprime N m := by
  have hdvd : orderOf lam ∣ N := orderOf_dvd_of_pow_eq_one hpow
  have hpow' : orderOf (lam ^ m) = orderOf lam / (orderOf lam).gcd m :=
    orderOf_pow' lam hm
  rw [hlam, hord] at hpow'
  have hle : orderOf lam ≤ N := Nat.le_of_dvd hN hdvd
  have hdivle : orderOf lam / (orderOf lam).gcd m ≤ orderOf lam :=
    Nat.div_le_self _ _
  have heq : orderOf lam = N := le_antisymm hle (by omega)
  refine ⟨heq, ?_⟩
  rw [heq] at hpow'
  rcases Nat.div_eq_self.mp hpow'.symm with h0 | h1
  · omega
  · exact h1

/-- Powers with an exponent coprime to `N` are cancellable among elements
killed by `N`. -/
theorem pow_left_cancel_of_coprime {F : Type*} [Monoid F] {lam mu : F}
    {m N : ℕ} (hcop : Nat.Coprime m N)
    (hlampow : lam ^ N = 1) (hmupow : mu ^ N = 1) (h : mu ^ m = lam ^ m) :
    mu = lam := by
  by_cases hN1 : N ≤ 1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hN1 with rfl | rfl
    · -- `N = 0`: `gcd m 0 = m = 1`
      have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hcop
      rw [hm1, pow_one, pow_one] at h
      exact h
    · rw [pow_one] at hlampow hmupow
      rw [hlampow, hmupow]
  · have hN1' : 1 < N := by omega
    obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hN1'
    calc mu = mu ^ 1 := (pow_one mu).symm
      _ = mu ^ (m * a % N) := by rw [ha]
      _ = mu ^ (m * a) := (pow_eq_pow_mod _ hmupow).symm
      _ = (mu ^ m) ^ a := by rw [pow_mul]
      _ = (lam ^ m) ^ a := by rw [h]
      _ = lam ^ (m * a) := by rw [pow_mul]
      _ = lam ^ (m * a % N) := pow_eq_pow_mod _ hlampow
      _ = lam ^ 1 := by rw [ha]
      _ = lam := pow_one lam

/-- **Higman pp. 90--91, case `θ = φ`: the two factor eigenvalues coincide.**
Both `λ` and `μ` solve `x ^ m = ν` (`m = 1 + 2^r`) with `ν` of full order
`N = 2^n - 1`; the exponent `m` is then invertible mod `N`, so `μ = λ`.  This
replaces Higman's "we may assume the conjugate bases chosen so that
`x₀ ξ = λ x₀`, `y₀ ξ = λ y₀`". -/
theorem eq_of_pow_eq_pow_orderOf {F : Type*} [Monoid F] {lam mu nu : F}
    {m N : ℕ} (hN : 0 < N) (hm : m ≠ 0) (hord : orderOf nu = N)
    (hlam : lam ^ m = nu) (hmu : mu ^ m = nu)
    (hlampow : lam ^ N = 1) (hmupow : mu ^ N = 1) : mu = lam := by
  obtain ⟨-, hcop⟩ :=
    orderOf_eq_and_coprime_of_pow_eq_orderOf hN hm hord hlam hlampow
  exact pow_left_cancel_of_coprime hcop.symm hlampow hmupow
    (hmu.trans hlam.symm)

/-! ### Support pinning, case `θ = φ` (type `B`)

After `μ = λ`, a support pair satisfies `λ^{2^i + 2^j} = λ^{1 + 2^r}`, and the
binary-uniqueness arithmetic forces `{i, j} = {0, r}`. -/

/-- **Higman pp. 90--91, case `θ = φ`: support pinning.**  If
`λ^{2^i} · λ^{2^j} = ν = λ^{1+2^r}` with `λ` of full order `2^n - 1` and
`i, j, r < n`, then `(i, j) = (0, r)` or `(i, j) = (r, 0)`.  For `r = 0`
(case `θ = φ = 1`, p. 90) the two branches coincide in `(0, 0)`; for `r ≠ 0`
(p. 91) these are Higman's two monomials `α β^{2^r}`, `α^{2^r} β` surviving
`|j - i| = r` on the `ν`-eigenline. -/
theorem higman_typeB_support_pinning {F : Type*} [Monoid F] {lam nu : F}
    {n r i j : ℕ} (hrn : r < n) (hi : i < n) (hj : j < n)
    (hord : orderOf lam = 2 ^ n - 1)
    (hnu : lam ^ (1 + 2 ^ r) = nu)
    (hsupp : lam ^ 2 ^ i * lam ^ 2 ^ j = nu) :
    (i = 0 ∧ j = r) ∨ (i = r ∧ j = 0) := by
  have hn : 0 < n := by omega
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder lam := orderOf_pos_iff.mp (by rw [hord]; omega)
  have hmod : 2 ^ i + 2 ^ j ≡ 1 + 2 ^ r [MOD 2 ^ n - 1] := by
    rw [← hord]
    refine hfin.pow_eq_pow_iff_modEq.mp ?_
    rw [pow_add]
    rw [hsupp]
    exact hnu.symm
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  push_cast at hcast
  -- `hcast : (2 : ZMod (2^n - 1))^i + 2^j = 1 + 2^r`
  by_cases hr0 : r = 0
  · -- `θ = φ = 1`: two powers summing to `2^1` merge at `i = j = 0`
    subst hr0
    have h1 : (2 : ZMod (2 ^ n - 1)) ^ i + 2 ^ j = 2 ^ 1 := by
      rw [hcast]; norm_num
    obtain ⟨hab, hc⟩ := higman_two_pow_add_eq_two_pow hn h1
    have hi0 : (i : ZMod n) = 0 := by linear_combination -hc
    have hival : i % n = 0 := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hi0
    rw [Nat.mod_eq_of_lt hi] at hival
    subst hival
    have hj0 : (j : ZMod n) = 0 := by linear_combination -hab
    have hjval : j % n = 0 := natCast_zmod_eq_zero_iff_mod_eq_zero.mp hj0
    rw [Nat.mod_eq_of_lt hj] at hjval
    exact Or.inl ⟨rfl, hjval⟩
  · -- `θ = φ ≠ 1`: `{i, j}` matches `{0, r}` as sets of exponents
    have h0r : (0 : ℕ) ≠ r := fun h => hr0 h.symm
    have hTsub : ({0, r} : Finset ℕ) ⊆ Finset.range n := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
    have hTsum : (∑ x ∈ ({0, r} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
        = 1 + 2 ^ r := by
      rw [Finset.sum_pair h0r]
      norm_num
    by_cases hij : i = j
    · -- merged case `2^{i+1} = 1 + 2^r`: a singleton cannot match a pair
      subst hij
      have hSsub : ({(i + 1) % n} : Finset ℕ) ⊆ Finset.range n := by
        intro x hx
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact Finset.mem_range.mpr (Nat.mod_lt _ hn)
      have hSsum : (∑ x ∈ ({(i + 1) % n} : Finset ℕ),
          (2 : ZMod (2 ^ n - 1)) ^ x) = 1 + 2 ^ r := by
        rw [Finset.sum_singleton, ← two_pow_zmod_eq_pow_mod, pow_succ]
        linear_combination hcast
      rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
          (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
      · have h0mem : (0 : ℕ) ∈ ({(i + 1) % n} : Finset ℕ) := by
          rw [hST]; simp
        have hrmem : r ∈ ({(i + 1) % n} : Finset ℕ) := by
          rw [hST]; simp
        simp only [Finset.mem_singleton] at h0mem hrmem
        exact absurd (hrmem.trans h0mem.symm) hr0
      · exact absurd hT0 (Finset.insert_ne_empty _ _)
      · exact absurd hS0 (Finset.singleton_ne_empty _)
    · -- distinct case: `{i, j} = {0, r}`
      have hSsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> exact Finset.mem_range.mpr (by omega)
      have hSsum : (∑ x ∈ ({i, j} : Finset ℕ), (2 : ZMod (2 ^ n - 1)) ^ x)
          = 1 + 2 ^ r := by
        rw [Finset.sum_pair hij]
        exact hcast
      rcases sum_two_pow_zmod_eq_or_of_subset_range hSsub hTsub
          (hSsum.trans hTsum.symm) with hST | ⟨_, hT0⟩ | ⟨hS0, _⟩
      · have himem : i ∈ ({0, r} : Finset ℕ) := by
          rw [← hST]; simp
        have hjmem : j ∈ ({0, r} : Finset ℕ) := by
          rw [← hST]; simp
        simp only [Finset.mem_insert, Finset.mem_singleton] at himem hjmem
        rcases himem with rfl | rfl <;> rcases hjmem with rfl | rfl
        · exact absurd rfl hij
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd rfl hij
      · exact absurd hT0 (Finset.insert_ne_empty _ _)
      · exact absurd hS0 (Finset.insert_ne_empty _ _)

/-! ### Support pinning, case `θ ≠ 1`, `φ = 1` (type `C`)

The commutative factor's eigenvalue is the square root `μ = ν^{2^{n-1}}`, so a
support pair yields Higman's congruence
`1 + 2^{s-1}(1 + 2^r) ≡ 2^t (1 + 2^r) (mod 2^n - 1)`, whose unique solution
under `0 < r ≤ n/2` forces `2r + 1 = n`. -/

/-- **Higman p. 91, case `θ ≠ 1`, `φ = 1`: support pinning.**  If
`λ^{2^i} · μ^{2^j} = ν = λ^{1+2^r}` with `μ² = ν`, `λ` of full order
`2^n - 1`, `0 < r`, `2r ≤ n` and `i, j < n`, then `2r + 1 = n` (in particular
`n` is odd) and `(i, j) = (n - 1, r + 1)` — the single monomial of `C(n, ε)`
(`[x_i, y_{i+r+2}] = ε^{2^{i+1}} v_{i+1}` read on the `ν`-eigenline
`i + 1 ≡ 0`). -/
theorem higman_typeC_support_pinning {F : Type*} [Monoid F] {lam mu nu : F}
    {n r i j : ℕ} (hr : 0 < r) (h2r : 2 * r ≤ n) (hi : i < n) (hj : j < n)
    (hord : orderOf lam = 2 ^ n - 1)
    (hnu : lam ^ (1 + 2 ^ r) = nu)
    (hmu : mu ^ 2 = nu) (hmupow : mu ^ (2 ^ n - 1) = 1)
    (hsupp : lam ^ 2 ^ i * mu ^ 2 ^ j = nu) :
    2 * r + 1 = n ∧ i = n - 1 ∧ j = r + 1 := by
  have hn : 0 < n := by omega
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
  have hfin : IsOfFinOrder lam := orderOf_pos_iff.mp (by rw [hord]; omega)
  -- the commutative factor's eigenvalue is a power of `λ`
  have hmuexp : mu = lam ^ ((1 + 2 ^ r) * 2 ^ (n - 1)) := by
    have h1 : mu ^ 2 ^ n = mu := by
      have he : 2 ^ n = (2 ^ n - 1) + 1 := by omega
      rw [he, pow_succ, hmupow, one_mul]
    have h2 : mu ^ 2 ^ n = (mu ^ 2) ^ 2 ^ (n - 1) := by
      rw [← pow_mul]
      congr 1
      rw [← pow_succ']
      congr 1
      omega
    rw [← h1, h2, hmu, ← hnu, ← pow_mul]
  have key : lam ^ (2 ^ i + (1 + 2 ^ r) * 2 ^ (n - 1 + j))
      = lam ^ (1 + 2 ^ r) := by
    rw [pow_add, hnu]
    have he : (1 + 2 ^ r) * 2 ^ (n - 1 + j)
        = ((1 + 2 ^ r) * 2 ^ (n - 1)) * 2 ^ j := by
      rw [pow_add]; ring1
    rw [he, pow_mul, ← hmuexp]
    exact hsupp
  have hmod : 2 ^ i + (1 + 2 ^ r) * 2 ^ (n - 1 + j)
      ≡ 1 + 2 ^ r [MOD 2 ^ n - 1] := by
    rw [← hord]
    exact hfin.pow_eq_pow_iff_modEq.mp key
  -- normalise the `λ`-exponent of the `x`-side to `2^0` by multiplying with
  -- `2^{n-i}`
  have hmod' : 2 ^ (n - i) * (2 ^ i + (1 + 2 ^ r) * 2 ^ (n - 1 + j))
      ≡ 2 ^ (n - i) * (1 + 2 ^ r) [MOD 2 ^ n - 1] := hmod.mul_left _
  have hL : 2 ^ (n - i) * (2 ^ i + (1 + 2 ^ r) * 2 ^ (n - 1 + j))
      = 2 ^ n + (1 + 2 ^ r) * 2 ^ (n - 1 + j + (n - i)) := by
    have e1 : 2 ^ (n - i) * 2 ^ i = 2 ^ n := by
      rw [← pow_add]
      congr 1
      omega
    calc 2 ^ (n - i) * (2 ^ i + (1 + 2 ^ r) * 2 ^ (n - 1 + j))
        = 2 ^ (n - i) * 2 ^ i
          + (1 + 2 ^ r) * (2 ^ (n - 1 + j) * 2 ^ (n - i)) := by ring1
      _ = 2 ^ n + (1 + 2 ^ r) * 2 ^ (n - 1 + j + (n - i)) := by
          rw [e1, ← pow_add]
  have h2nmod : 2 ^ n ≡ 1 [MOD 2 ^ n - 1] := by
    have h0 : (2 ^ n - 1) ≡ 0 [MOD 2 ^ n - 1] :=
      Nat.modEq_zero_iff_dvd.mpr dvd_rfl
    calc 2 ^ n = 1 + (2 ^ n - 1) := by omega
      _ ≡ 1 + 0 [MOD 2 ^ n - 1] := Nat.ModEq.add_left 1 h0
      _ = 1 := by omega
  have hfinal : 1 + (1 + 2 ^ r) * 2 ^ (n - 1 + j + (n - i))
      ≡ 2 ^ (n - i) * (1 + 2 ^ r) [MOD 2 ^ n - 1] := by
    calc 1 + (1 + 2 ^ r) * 2 ^ (n - 1 + j + (n - i))
        ≡ 2 ^ n + (1 + 2 ^ r) * 2 ^ (n - 1 + j + (n - i)) [MOD 2 ^ n - 1] :=
          (h2nmod.symm.add_right _)
      _ = 2 ^ (n - i) * (2 ^ i + (1 + 2 ^ r) * 2 ^ (n - 1 + j)) := hL.symm
      _ ≡ 2 ^ (n - i) * (1 + 2 ^ r) [MOD 2 ^ n - 1] := hmod'
  have hcast := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hfinal
  push_cast at hcast
  obtain ⟨hn', hsC, htC⟩ := higman_typeC_exponent_uniqueness (n := n) (r := r)
    (s := n - 1 + j + (n - i)) (t := n - i) hr h2r (by linear_combination hcast)
  -- extract `i = n - 1` from `t ≡ 1`
  have hi' : i = n - 1 := by
    have h1n : ((n - i : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) := by
      push_cast
      exact htC
    have hmodn := (ZMod.natCast_eq_natCast_iff' _ _ _).mp h1n
    have h1m : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    by_cases hi0 : i = 0
    · subst hi0
      rw [Nat.sub_zero, Nat.mod_self, h1m] at hmodn
      omega
    · have hlt : n - i < n := by omega
      rw [Nat.mod_eq_of_lt hlt, h1m] at hmodn
      omega
  -- extract `j = r + 1` from `s ≡ r + 1`
  have hj' : j = r + 1 := by
    rw [hi'] at hsC
    have he : n - 1 + j + (n - (n - 1)) = n + j := by omega
    rw [he] at hsC
    have hnj : ((n + j : ℕ) : ZMod n) = (j : ZMod n) := by
      push_cast [ZMod.natCast_self]
      ring1
    rw [hnj] at hsC
    have hcastj : (j : ZMod n) = ((r + 1 : ℕ) : ZMod n) := by
      push_cast
      exact hsC
    have hmodn := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hcastj
    have hr1n : r + 1 < n := by omega
    rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hr1n] at hmodn
    exact hmodn
  exact ⟨hn', hi', hj'⟩

/-! ### Support pinning, independent case (type `D`) -/

/-- **Higman pp. 91--92, independent case: support pinning.**  If
`λ^{2^i} · μ^{2^j} = ν` with `ν = λ^{1+2^r} = μ^{1+2^s}` of full order
`2^n - 1` and `r, s, r + s, r - s` all nonzero mod `n`, then `s ≡ 2r`,
`5r ≡ 0`, `(i, j) ≡ (3r, r) (mod n)` — or the mirror under `r ↔ s`, `i ↔ j`
(interchanging the factors `X, Y`).  The single monomial of `D(n, θ, ε)`. -/
theorem higman_typeD_support_pinning {F : Type*} [CommMonoid F]
    {nu lam mu : F} {n r s i j : ℕ} (hn : 0 < n)
    (hr : (r : ZMod n) ≠ 0) (hs : (s : ZMod n) ≠ 0)
    (hrs : (r : ZMod n) + (s : ZMod n) ≠ 0)
    (hrs' : (r : ZMod n) ≠ (s : ZMod n))
    (hord : orderOf nu = 2 ^ n - 1)
    (hlam : lam ^ (1 + 2 ^ r) = nu) (hmu : mu ^ (1 + 2 ^ s) = nu)
    (hsupp : lam ^ 2 ^ i * mu ^ 2 ^ j = nu) :
    ((s : ZMod n) = 2 * (r : ZMod n) ∧ 5 * (r : ZMod n) = 0 ∧
      (i : ZMod n) = 3 * (r : ZMod n) ∧ (j : ZMod n) = (r : ZMod n)) ∨
    ((r : ZMod n) = 2 * (s : ZMod n) ∧ 5 * (s : ZMod n) = 0 ∧
      (i : ZMod n) = (s : ZMod n) ∧ (j : ZMod n) = 3 * (s : ZMod n)) :=
  higman_typeD_exponent_uniqueness hn hr hs hrs hrs'
    (higman_typeD_congruence_of_pow_eq hn hord hlam hmu hsupp)

end OddOrder.Higman.Suzuki2Groups
