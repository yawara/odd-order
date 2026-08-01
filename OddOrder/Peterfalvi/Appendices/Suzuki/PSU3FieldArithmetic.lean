/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.QuadraticFrobenius

/-!
# Arithmetic of `E/F` for the characterization of `PSU(3,q)`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2, pp. 123-126.

The model-independent arithmetic that Ch. IV §2 runs on: a finite field `E` of
characteristic `2` with `|E| = q²`, its subfield `F = {x | x^q = x}`, and an
automorphism `θ` of odd order.

## Main results

* `frobNorm_bijective`, `frobNormEquiv` - the book's `u ↦ u^{1+θ}` is bijective and
  multiplicative, so its inverse `τ` (p. 125) is too.
* `exists_add_inv_eq` - **step (12)**: `X² + αX + 1` has a root `β` in `E`, and `β` lies
  in `F` or satisfies `β^{q+1} = 1`.  Proved by counting, with no field extension.
* `betaSum`, `betaRatio` - the book's `c_i = β^i + β^{-i}` and `u_i = c_{i-1}/c_i`.
* `betaRatio_succ` - **step (13)**: the closed form satisfies the recursion of (11).
* `betaScale_succ` - **step (14)**: likewise for `d_i = ζ^i (c_i/α)^{2τ}`.
* `pow_eq_one_of_betaSum_eq` - the field-theoretic core of **step (16)**.

The group-theoretic side of §2 - the orbit counts of steps (8) and (9) - is in
`PSU3OrbitCount`, which imports this file.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

/-- `q − 1` and `q + 1` are coprime for `q = 2^m`, `m ≥ 1`: both are odd, and they
differ by `2`.

This is what makes `μ(K) ∩ μ(W) = 1` inside `E^×`: `μ(K)` lies in `F^×`, of order
`q − 1` (`QuotientFieldModel.mu_K_frobFixed`), while `μ(W)` lies in the norm-one
subgroup, of order `q + 1` (`QuotientFieldModel.mu_W_normOne`).  Hence
`|μ(KW)| = |μ(K)| · |μ(W)| = (q − 1) m`, the number behind step (8)'s
`n = (q + 1)/m`. -/
theorem coprime_two_pow_sub_one_two_pow_add_one {m : ℕ} (hm : m ≠ 0) :
    Nat.Coprime (2 ^ m - 1) (2 ^ m + 1) := by
  have hpow : (2 : ℕ) ∣ 2 ^ m := dvd_pow_self 2 hm
  have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h1 := Nat.gcd_dvd_left (2 ^ m - 1) (2 ^ m + 1)
  have h2 := Nat.gcd_dvd_right (2 ^ m - 1) (2 ^ m + 1)
  have hdvd : Nat.gcd (2 ^ m - 1) (2 ^ m + 1) ∣ 2 := by
    have hsub : Nat.gcd (2 ^ m - 1) (2 ^ m + 1) ∣ (2 ^ m + 1) - (2 ^ m - 1) :=
      Nat.dvd_sub h2 h1
    have e : (2 ^ m + 1) - (2 ^ m - 1) = 2 := by omega
    rwa [e] at hsub
  have hodd : ¬ (2 ∣ (2 ^ m - 1)) := by omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact h
  · rw [h] at h1
    exact absurd h1 hodd

/-- An element killed by both `q − 1` and `q + 1` is trivial, for `q = 2^m`, `m ≥ 1`.

This is the group-theoretic form of `μ(K) ∩ μ(W) = 1` in `E^×`: an element of `μ(K)`
lies in `F^×` so is killed by `q − 1` (`QuotientFieldModel.mu_K_frobFixed`), and an
element of `μ(W)` is killed by `q + 1` (`QuotientFieldModel.mu_W_normOne`). -/
theorem eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one
    {H : Type*} [Group H] {m : ℕ} (hm : m ≠ 0) {x : H}
    (h1 : x ^ (2 ^ m - 1) = 1) (h2 : x ^ (2 ^ m + 1) = 1) : x = 1 := by
  have d1 : orderOf x ∣ 2 ^ m - 1 := orderOf_dvd_of_pow_eq_one h1
  have d2 : orderOf x ∣ 2 ^ m + 1 := orderOf_dvd_of_pow_eq_one h2
  have hdvd : orderOf x ∣ 1 := by
    have := Nat.dvd_gcd d1 d2
    rwa [coprime_two_pow_sub_one_two_pow_add_one hm] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)

/-- The index arithmetic behind step (8)'s `n = (q + 1)/m`:

  `|E^×| / |μ(KW)| = (q² − 1) / ((q − 1) · m) = (q + 1) / m`,

using `q² − 1 = (q − 1)(q + 1)` and cancelling the positive factor `q − 1`. -/
theorem two_pow_sq_sub_one_div {e m : ℕ} (he : e ≠ 0) :
    ((2 ^ e) ^ 2 - 1) / ((2 ^ e - 1) * m) = (2 ^ e + 1) / m := by
  have h2 : (2 : ℕ) ≤ 2 ^ e := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr he)
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ e = r + 1 := ⟨2 ^ e - 1, by omega⟩
  have hrpos : 0 < r := by omega
  rw [hr]
  have hsq : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
  have hone : r + 1 - 1 = r := by omega
  have htwo : r + 1 + 1 = r + 2 := by omega
  rw [hsq, Nat.add_sub_cancel, hone, htwo]
  exact Nat.mul_div_mul_left _ _ hrpos

/-- **The squeeze behind step (8)**.

If `Φ : α → β` has every fibre of size at most `M`, one distinguished fibre of size at
most `M − 1`, and `|α| = |β| · M − 1`, then *all* those bounds are equalities: the
fibre over `b₀` has exactly `M − 1` elements and every other fibre exactly `M`.

This is the book's "whence all the inequalities are in fact equalities" (p. 124), with
`α = Q₀`, `β` the set of `KW`-orbits on `(Q/Q₀)^#`, `M = m = |W|`, and `b₀` the orbit
of `ω̄₁`. -/
theorem card_fiber_eq_of_card_eq {α β : Type*} [Finite α] [Finite β]
    (Φ : α → β) {M : ℕ} (hM : 1 ≤ M) (b₀ : β)
    (hle : ∀ b, {a | Φ a = b}.ncard ≤ M)
    (hb₀ : {a | Φ a = b₀}.ncard ≤ M - 1)
    (hcard : Nat.card α = Nat.card β * M - 1) :
    (∀ b, b ≠ b₀ → {a | Φ a = b}.ncard = M) ∧ {a | Φ a = b₀}.ncard = M - 1 := by
  classical
  haveI : Fintype α := Fintype.ofFinite _
  haveI : Fintype β := Fintype.ofFinite _
  have hconv : ∀ b : β, {a | Φ a = b}.ncard
      = (Finset.univ.filter fun a => Φ a = b).card := by
    intro b
    rw [Set.ncard_eq_toFinset_card']
    congr 1
    ext a
    simp
  simp only [hconv] at hle hb₀
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hcard
  set g : β → ℕ := fun b => if b = b₀ then M - 1 else M with hg
  have hpt : ∀ b ∈ (Finset.univ : Finset β),
      (Finset.univ.filter fun a => Φ a = b).card ≤ g b := by
    intro b _
    by_cases h : b = b₀
    · simp only [hg, if_pos h]
      exact h ▸ hb₀
    · simp only [hg, if_neg h]
      exact hle b
  have hsumf : ∑ b : β, (Finset.univ.filter fun a => Φ a = b).card = Fintype.card α := by
    rw [← Finset.card_eq_sum_card_fiberwise (fun a _ => Finset.mem_univ (Φ a))]
    exact Finset.card_univ
  have hsumg : ∑ b : β, g b = Fintype.card β * M - 1 := by
    have hsplit : ∑ b : β, g b = ∑ b ∈ Finset.univ.erase b₀, g b + g b₀ :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ b₀)).symm
    have hconst : ∀ b ∈ Finset.univ.erase b₀, g b = M := by
      intro b hb
      simp only [hg, if_neg (Finset.ne_of_mem_erase hb)]
    have herase : ∑ b ∈ Finset.univ.erase b₀, g b = (Fintype.card β - 1) * M := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ b₀), Finset.card_univ, smul_eq_mul]
    rw [hsplit, herase]
    simp only [hg, if_pos rfl]
    have hpos : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr ⟨b₀⟩
    obtain ⟨k, hk⟩ : ∃ k, Fintype.card β = k + 1 := ⟨Fintype.card β - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, add_mul, one_mul]
    generalize k * M = t
    omega
  have heq : ∑ b : β, (Finset.univ.filter fun a => Φ a = b).card = ∑ b : β, g b := by
    rw [hsumf, hsumg, hcard]
  have key : ∀ b, (Finset.univ.filter fun a => Φ a = b).card = g b :=
    fun b => (Finset.sum_eq_sum_iff_of_le hpt).mp heq b (Finset.mem_univ b)
  refine ⟨fun b hb => ?_, ?_⟩
  · rw [hconv b, key b]
    simp only [hg, if_neg hb]
  · rw [hconv b₀, key b₀]
    simp only [hg, if_pos rfl]

/-! ### The book's `u^{1+θ}` (p. 125)

Peterfalvi writes `u^{1+θ}` for `u · θ(u)` and uses `τ` for its inverse on `F^×`
(bijective because `θ` has odd order).  Step (10)'s hypothesis
`b^{1+θ} = α + a^{-(1+θ)}` is stated in these terms.
-/

/-- `u ↦ u^{1+θ}` is multiplicative. -/
theorem frobNorm_mul {E : Type*} [Field E] (θ : E ≃+* E) (u v : E) :
    (u * v) * θ (u * v) = (u * θ u) * (v * θ v) := by
  rw [map_mul]
  ring

/-- `u ↦ u^{1+θ}` sends `1` to `1`. -/
@[simp] theorem frobNorm_one {E : Type*} [Field E] (θ : E ≃+* E) :
    (1 : E) * θ 1 = 1 := by
  rw [map_one, mul_one]

/-- `u^{1+θ} ≠ 0` for `u ≠ 0`. -/
theorem frobNorm_ne_zero {E : Type*} [Field E] (θ : E ≃+* E) {u : E}
    (hu : u ≠ 0) : u * θ u ≠ 0 :=
  mul_ne_zero hu (by simpa using hu)

/-! ### The map `x ↦ x + x⁻¹` (p. 125, step (12))

Step (12) needs a root `β` of `X² + αX + 1`, i.e. an element with `β + β⁻¹ = α`.  The
map `x ↦ x + x⁻¹` is two-to-one, its only collisions being `x ↔ x⁻¹`; that is what makes
the counting argument for (12) work.
-/

/-- `x + x⁻¹ = y + y⁻¹` exactly when `y` is `x` or `x⁻¹`: the difference factors as
`(x − y)(xy − 1)/(xy)`.

So `x ↦ x + x⁻¹` is two-to-one on the nonzero elements, the fibres being the pairs
`{x, x⁻¹}`. -/
theorem add_inv_eq_add_inv_iff {E : Type*} [Field E] {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    x + x⁻¹ = y + y⁻¹ ↔ x = y ∨ x * y = 1 := by
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  rw [← sub_eq_zero]
  have hkey : x + x⁻¹ - (y + y⁻¹) = (x - y) * (x * y - 1) / (x * y) := by
    field_simp
    ring
  rw [hkey, div_eq_zero_iff, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  simp [hxy]

/-- **The norm-one subgroup of `E^×` has at least `q + 1` elements** when `|E^×| = q² − 1`
(written here as `|E^×| = r(r+2)` with `q = r + 1`, to keep clear of truncated
subtraction).

`u ↦ u^{q−1}` lands in it, since `u^{q²−1} = 1`, and its kernel — the `(q−1)`-st roots of
unity — has at most `q − 1` elements; so its image has at least `(q²−1)/(q−1) = q + 1`.

Step (12) needs only this lower bound, never the exact count.  That matters: mathlib's
exact root count for cyclic groups (`card_pow_eq_one_eq_orderOf_aux`) is private, whereas
the bound `card_rootsOfUnity` is public. -/
theorem card_rootsOfUnity_ge {E : Type*} [Field E] [Finite E] {r : ℕ} (hr : r ≠ 0)
    (hcard : Nat.card Eˣ = r * (r + 2)) :
    r + 2 ≤ Nat.card ↥(rootsOfUnity (r + 2) E) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  haveI : NeZero r := ⟨hr⟩
  -- `u ↦ u^r` lands in the norm-one subgroup
  have hrange : (powMonoidHom r : Eˣ →* Eˣ).range ≤ rootsOfUnity (r + 2) E := by
    rintro _ ⟨u, rfl⟩
    rw [mem_rootsOfUnity]
    change (u ^ r) ^ (r + 2) = 1
    rw [← pow_mul, ← hcard]
    exact pow_card_eq_one'
  -- its kernel is the `r`-th roots of unity, so has at most `r` elements
  have hkercard : Nat.card ↥(powMonoidHom r : Eˣ →* Eˣ).ker ≤ r := by
    rw [← rootsOfUnity_eq_ker, Nat.card_eq_fintype_card]
    exact card_rootsOfUnity (k := r) (R := E)
  have hidx : Nat.card ↥(powMonoidHom r : Eˣ →* Eˣ).range
      = (powMonoidHom r : Eˣ →* Eˣ).ker.index :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm
  have hmul := Subgroup.index_mul_card (powMonoidHom r : Eˣ →* Eˣ).ker
  -- `index · |ker| = r(r+2)` with `|ker| ≤ r` forces `index ≥ r + 2`
  have hle : (r + 2) * r ≤ (powMonoidHom r : Eˣ →* Eˣ).ker.index * r := by
    calc (r + 2) * r = r * (r + 2) := by ring
      _ = (powMonoidHom r : Eˣ →* Eˣ).ker.index *
            Nat.card ↥(powMonoidHom r : Eˣ →* Eˣ).ker := by rw [hmul, hcard]
      _ ≤ (powMonoidHom r : Eˣ →* Eˣ).ker.index * r :=
            Nat.mul_le_mul_left _ hkercard
  have hfinal : r + 2 ≤ (powMonoidHom r : Eˣ →* Eˣ).ker.index :=
    Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero hr)
  calc r + 2 ≤ (powMonoidHom r : Eˣ →* Eˣ).ker.index := hfinal
    _ = Nat.card ↥(powMonoidHom r : Eˣ →* Eˣ).range := hidx.symm
    _ ≤ Nat.card ↥(rootsOfUnity (r + 2) E) :=
        Nat.card_le_card_of_injective (Subgroup.inclusion hrange)
          (Subgroup.inclusion_injective hrange)

/-- **A two-to-one map onto a target of half the size is onto.**

If `f` sends `s` into `t`, every fibre of `f` has at most two points, and `2|t| ≤ |s| + 1`,
then `f` maps `s` *onto* `t`.  The `+1` is what makes the bound usable when `|s|` is odd,
which is the case in step (12) (`|s| = 2q − 1`, `|t| = q`). -/
theorem image_eq_of_card_fiber_le_two {α β : Type*} [DecidableEq β]
    {s : Finset α} {t : Finset β} {f : α → β} (hmaps : ∀ x ∈ s, f x ∈ t)
    (hfib : ∀ c : β, (s.filter fun x => f x = c).card ≤ 2)
    (hcard : 2 * t.card ≤ s.card + 1) :
    s.image f = t := by
  refine Finset.eq_of_subset_of_card_le (fun c hc => ?_) ?_
  · obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp hc
    exact hmaps x hxs
  · have hle : s.card ≤ 2 * (s.image f).card :=
      Finset.card_le_mul_card_image s 2 fun c _ => hfib c
    omega

/-- **Peterfalvi Part II, Ch. IV §2, step (12)** (p. 125): over a field `E` of
characteristic `2` with `|E| = q²`, `q = 2^m`, every `α` in the subfield `F = {x | x^q = x}`
is `β + β⁻¹` for some `β ≠ 0` — that is, `X² + αX + 1` has a root in `E` — and every such
`β` lies in `F` or satisfies `β^{q+1} = 1`, i.e. `β⁻¹ = β^q`.

The book states this of the roots `β, β⁻¹` of the characteristic polynomial of
`[[0,1],[1,α]]`, asserting `β ∈ E` without argument.

Proved by counting, with no field extension and no Artin–Schreier theory.  Put
`S = F^× ∪ N` with `N` the norm-one subgroup.  Then `x ↦ x + x⁻¹` maps `S` into `F`; its
fibres are the pairs `{x, x⁻¹}` (`add_inv_eq_add_inv_iff`); and

  `|S| ≥ (q − 1) + (q + 1) − 1 = 2q − 1`

because `F^× ∩ N = 1` — the orders `q − 1` and `q + 1` being coprime.  A two-to-one map
from a set that large onto a target of size `q = |F|` must be onto
(`image_eq_of_card_fiber_le_two`).  Membership of `β` in `S` is exactly the dichotomy. -/
theorem exists_add_inv_eq {E : Type*} [Field E] [Finite E] [Fact (Nat.Prime 2)] [CharP E 2]
    {m : ℕ} (hm : m ≠ 0) (hcard : Nat.card E = (2 ^ m) ^ 2) {α : E}
    (hα : α ^ 2 ^ m = α) :
    ∃ β : E, β ≠ 0 ∧ β + β⁻¹ = α ∧ (β ^ 2 ^ m = β ∨ β ^ (2 ^ m + 1) = 1) := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ m = r + 1 := ⟨2 ^ m - 1, by
    have : 2 ≤ 2 ^ m := by
      calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
    omega⟩
  have hrne : r ≠ 0 := by
    have h2 : (2:ℕ) ≤ 2 ^ m := by
      calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
    omega
  -- the fixed field and the norm-one set, as `Finset`s
  obtain ⟨Ffin, hFmem⟩ : ∃ s : Finset E, ∀ x, x ∈ s ↔ x ^ 2 ^ m = x :=
    ⟨Finset.univ.filter fun x => x ^ 2 ^ m = x, by simp⟩
  obtain ⟨Nfin, hNmem⟩ : ∃ s : Finset E, ∀ x, x ∈ s ↔ x ^ (2 ^ m + 1) = 1 :=
    ⟨Finset.univ.filter fun x => x ^ (2 ^ m + 1) = 1, by simp⟩
  -- `|F| = q`
  have hFcard : Ffin.card = 2 ^ m := by
    have h1 : Ffin.card = Fintype.card {x : E // x ∈ Ffin} := (Fintype.card_coe Ffin).symm
    have h2 : Fintype.card {x : E // x ∈ Ffin}
        = Fintype.card ↥(OddOrder.FiniteField.frobFixedSubfield E 2 m) :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun x =>
        (hFmem x).trans (OddOrder.FiniteField.mem_frobFixedSubfield).symm)
    rw [h1, h2, ← Nat.card_eq_fintype_card]
    exact OddOrder.FiniteField.natCard_frobFixedSubfield hcard hm
  -- `|N| ≥ q + 1`
  have hNcard : 2 ^ m + 1 ≤ Nfin.card := by
    have hEu : Nat.card Eˣ = r * (r + 2) := by
      have hsq : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
      rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hcard, hr]
      omega
    have hge := card_rootsOfUnity_ge (E := E) hrne hEu
    rw [show r + 2 = 2 ^ m + 1 by omega] at hge
    refine le_trans hge ?_
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe Nfin]
    refine Fintype.card_le_of_injective (fun u => ⟨((u : Eˣ) : E), ?_⟩) ?_
    · exact (hNmem _).mpr (by exact_mod_cast (mem_rootsOfUnity' _ _).mp u.2)
    · intro u v huv
      exact Subtype.ext (Units.ext (congrArg Subtype.val huv))
  -- `0 ∈ F`, so `|F^×| = q − 1`
  have h0F : (0 : E) ∈ Ffin := (hFmem 0).mpr (by rw [hr]; simp)
  have hEraseCard : (Ffin.erase 0).card = 2 ^ m - 1 := by
    rw [Finset.card_erase_of_mem h0F, hFcard]
  -- `F^× ∩ N = {1}`, by coprimality of `q − 1` and `q + 1`
  have hInter : (Ffin.erase 0 ∩ Nfin).card ≤ 1 := by
    refine le_trans (Finset.card_le_card (fun x hx => ?_)) (Finset.card_singleton (1 : E)).le
    obtain ⟨hxe, hxN⟩ := Finset.mem_inter.mp hx
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hxe
    have hxF : x ^ 2 ^ m = x := (hFmem x).mp (Finset.mem_of_mem_erase hxe)
    have hu1 : (Units.mk0 x hx0) ^ (2 ^ m - 1) = 1 := by
      refine Units.ext ?_
      push_cast
      rw [show 2 ^ m - 1 = r by omega]
      have : x * x ^ r = x := by rw [← pow_succ', ← hr]; exact hxF
      field_simp at this ⊢
      exact this
    have hu2 : (Units.mk0 x hx0) ^ (2 ^ m + 1) = 1 := by
      refine Units.ext ?_
      push_cast
      exact (hNmem x).mp hxN
    have := eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one hm hu1 hu2
    have hx1 : x = 1 := congrArg Units.val this
    simpa using hx1
  -- so `|S| ≥ 2q − 1`
  have hScard : 2 * (2 ^ m) ≤ (Ffin.erase 0 ∪ Nfin).card + 1 := by
    have hun := Finset.card_union_add_card_inter (Ffin.erase 0) Nfin
    omega
  -- `x ↦ x + x⁻¹` maps `S` into `F`
  have hmaps : ∀ x ∈ Ffin.erase 0 ∪ Nfin, x + x⁻¹ ∈ Ffin := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.ne_of_mem_erase h
      · intro hzero
        rw [hzero] at h
        have := (hNmem 0).mp h
        rw [zero_pow (by omega)] at this
        exact zero_ne_one this
    refine (hFmem _).mpr ?_
    rw [add_pow_char_pow, inv_pow]
    rcases Finset.mem_union.mp hx with h | h
    · rw [(hFmem x).mp (Finset.mem_of_mem_erase h)]
    · have hinv : x ^ 2 ^ m = x⁻¹ := by
        have h1 : x ^ 2 ^ m * x = 1 := by rw [← pow_succ]; exact (hNmem x).mp h
        field_simp at h1 ⊢
        linear_combination h1
      rw [hinv, inv_inv, add_comm]
  -- the fibres are the pairs `{x, x⁻¹}`
  have hfib : ∀ c : E, ((Ffin.erase 0 ∪ Nfin).filter fun x => x + x⁻¹ = c).card ≤ 2 := by
    intro c
    rcases Finset.eq_empty_or_nonempty
        ((Ffin.erase 0 ∪ Nfin).filter fun x => x + x⁻¹ = c) with he | ⟨x₀, hx₀⟩
    · rw [he]; simp
    obtain ⟨hx₀S, hx₀c⟩ := Finset.mem_filter.mp hx₀
    have hx₀0 : x₀ ≠ 0 := by
      rcases Finset.mem_union.mp hx₀S with h | h
      · exact Finset.ne_of_mem_erase h
      · intro hzero
        rw [hzero] at h
        have := (hNmem 0).mp h
        rw [zero_pow (by omega)] at this
        exact zero_ne_one this
    have hsub : ((Ffin.erase 0 ∪ Nfin).filter fun x => x + x⁻¹ = c)
        ⊆ {x₀, x₀⁻¹} := by
      intro y hy
      obtain ⟨hyS, hyc⟩ := Finset.mem_filter.mp hy
      have hy0 : y ≠ 0 := by
        rcases Finset.mem_union.mp hyS with h | h
        · exact Finset.ne_of_mem_erase h
        · intro hzero
          rw [hzero] at h
          have := (hNmem 0).mp h
          rw [zero_pow (by omega)] at this
          exact zero_ne_one this
      have := (add_inv_eq_add_inv_iff hx₀0 hy0).mp (hx₀c.trans hyc.symm)
      rcases this with h | h
      · exact Finset.mem_insert.mpr (Or.inl h.symm)
      · refine Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_))
        field_simp
        linear_combination h
    exact le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_insert_le _ _) (by simp))
  -- so the map is onto `F`
  have himg := image_eq_of_card_fiber_le_two hmaps hfib (by rw [hFcard]; exact hScard)
  have hαF : α ∈ Ffin := (hFmem α).mpr hα
  rw [← himg] at hαF
  obtain ⟨β, hβS, hβ⟩ := Finset.mem_image.mp hαF
  refine ⟨β, ?_, hβ, ?_⟩
  · rcases Finset.mem_union.mp hβS with h | h
    · exact Finset.ne_of_mem_erase h
    · intro hzero
      rw [hzero] at h
      have := (hNmem 0).mp h
      rw [zero_pow (by omega)] at this
      exact zero_ne_one this
  · rcases Finset.mem_union.mp hβS with h | h
    · exact Or.inl ((hFmem β).mp (Finset.mem_of_mem_erase h))
    · exact Or.inr ((hNmem β).mp h)

/-! ### The closed form (13) for `(u_i)` (p. 126)

The book solves the recursion `u_{i+1} = 1/(α + u_i)`, `u₁ = 0` of (11) by diagonalizing
`[[0,1],[1,α]]` over its eigenvalues `β, β⁻¹`, obtaining

  `u_i = (β^{i-1} + β^{-i+1}) / (β^i + β^{-i})`.

Everything rests on the quantities `c_i = β^i + β^{-i}`, which satisfy the three-term
recurrence `c_{i+2} = α c_{i+1} + c_i`; the ratios `c_i / c_{i+1}` are then the `u`'s.
-/

/-- The book's `β^i + β^{-i}` (Peterfalvi Part II, p. 126) — up to the factor `1/α`, the
entries of the `i`-th power of `[[0,1],[1,α]]`. -/
noncomputable def betaSum {E : Type*} [Field E] (β : E) (i : ℕ) : E := β ^ i + (β ^ i)⁻¹

/-- `α · c_{i+1} = c_{i+2} + c_i` when `α = β + β⁻¹`.

An identity in any field — no characteristic assumption; expanding
`(β + β⁻¹)(β^{i+1} + β^{-i-1})` gives `β^{i+2} + β^{-i-2}` plus `β^i + β^{-i}`. -/
theorem alpha_mul_betaSum {E : Type*} [Field E] {β α : E} (hβ : β ≠ 0)
    (hα : β + β⁻¹ = α) (i : ℕ) :
    α * betaSum β (i + 1) = betaSum β (i + 2) + betaSum β i := by
  subst hα
  have hβi : β ^ i ≠ 0 := pow_ne_zero _ hβ
  simp only [betaSum]
  field_simp
  ring

/-- **The three-term recurrence** `c_{i+2} = α c_{i+1} + c_i` in characteristic `2`.

This is `alpha_mul_betaSum` with the duplicated `c_i` absorbed by `2 = 0` — the point at
which the book's computation becomes a recursion rather than a two-sided identity. -/
theorem betaSum_rec {E : Type*} [Field E] (h2 : (2 : E) = 0) {β α : E} (hβ : β ≠ 0)
    (hα : β + β⁻¹ = α) (i : ℕ) :
    betaSum β (i + 2) = α * betaSum β (i + 1) + betaSum β i := by
  rw [alpha_mul_betaSum hβ hα i]
  linear_combination (-(betaSum β i)) * h2

/-- `c₀ = 0` in characteristic `2`, which is the book's `u₁ = 0`. -/
theorem betaSum_zero {E : Type*} [Field E] (h2 : (2 : E) = 0) (β : E) :
    betaSum β 0 = 0 := by
  simp only [betaSum, pow_zero, inv_one]
  linear_combination h2

/-- `c₁ = α`. -/
theorem betaSum_one {E : Type*} [Field E] {β α : E} (hα : β + β⁻¹ = α) :
    betaSum β 1 = α := by
  simp only [betaSum, pow_one]
  exact hα

/-- **`α + u_i = c_{i+2}/c_{i+1}`**, so that `u_{i+1} = 1/(α + u_i)` — the recursion of
(11) holds for the closed form (13).

With `u_{i+1} := c_i / c_{i+1}` this says `α + u_{i+1} = c_{i+2}/c_{i+1}`, whose inverse
is `c_{i+1}/c_{i+2} = u_{i+2}`. -/
theorem add_betaSum_div {E : Type*} [Field E] (h2 : (2 : E) = 0) {β α : E} (hβ : β ≠ 0)
    (hα : β + β⁻¹ = α) (i : ℕ) (hne : betaSum β (i + 1) ≠ 0) :
    α + betaSum β i / betaSum β (i + 1) = betaSum β (i + 2) / betaSum β (i + 1) := by
  rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne]
  exact (betaSum_rec h2 hβ hα i).symm

/-- **`c_i = 0` exactly when `β^i = 1`.**

`β^i + β^{-i} = 0` says `(β^i)² = 1`, and squaring is injective in characteristic `2`.
The book uses this in (16): from `b_{i-1} = (β^i + β^{-i})/α ≠ 0` it concludes `β^i ≠ 1`. -/
theorem betaSum_eq_zero_iff {E : Type*} [Field E] (h2 : (2 : E) = 0) {β : E} (hβ : β ≠ 0)
    (i : ℕ) : betaSum β i = 0 ↔ β ^ i = 1 := by
  have hβi : β ^ i ≠ 0 := pow_ne_zero _ hβ
  simp only [betaSum]
  constructor
  · intro h
    field_simp at h
    have hsq : (β ^ i + 1) * (β ^ i + 1) = 0 := by linear_combination h + (β ^ i) * h2
    have hroot := mul_self_eq_zero.mp hsq
    linear_combination hroot - h2
  · intro h
    rw [h, inv_one]
    linear_combination h2

/-- The book's `u_i` of (13), shifted to start at `0`: `betaRatio β i = c_i / c_{i+1}` is
the book's `u_{i+1}`.  The shift avoids truncated subtraction in the index. -/
noncomputable def betaRatio {E : Type*} [Field E] (β : E) (i : ℕ) : E :=
  betaSum β i / betaSum β (i + 1)

/-- `u₁ = 0`, the initial value in (11). -/
theorem betaRatio_zero {E : Type*} [Field E] (h2 : (2 : E) = 0) (β : E) :
    betaRatio β 0 = 0 := by
  simp only [betaRatio, betaSum_zero h2, zero_div]

/-- **Peterfalvi Part II, Ch. IV §2, step (13)** (p. 126): the closed form satisfies the
recursion of (11).

`u_{i+1} = 1/(α + u_i)` for the ratios `u_i = c_{i-1}/c_i`, so the sequence the book
defines recursively in (11) is the one it writes in closed form in (13).  The hypothesis
`c_{i+1} ≠ 0` is the book's `b_i ≠ 0`, equivalently `β^{i+1} ≠ 1` by
`betaSum_eq_zero_iff` — the condition under which the sequence is still defined. -/
theorem betaRatio_succ {E : Type*} [Field E] (h2 : (2 : E) = 0) {β α : E} (hβ : β ≠ 0)
    (hα : β + β⁻¹ = α) (i : ℕ) (hne : betaSum β (i + 1) ≠ 0) :
    betaRatio β (i + 1) = (α + betaRatio β i)⁻¹ := by
  simp only [betaRatio]
  rw [add_betaSum_div h2 hβ hα i hne, inv_div]

/-- **Peterfalvi Part II, Ch. IV §2, step (16)** (p. 126), the field-theoretic core: if
`c_{m-1} = α` and no `β^i` with `1 ≤ i ≤ m − 1` equals `1`, then `β^m = 1`.

The book reaches `β^m = 1` from `u_{m-1} = α` (that is, `c_{m-1} = α = c₁`) as follows:
`β^{m-1}` is then another root of `X² + αX + 1`, so `β^{m-1} = β` or `β^{m-1} = β⁻¹`; the
first would give `β^{m-2} = 1`, excluded.  Here that dichotomy is
`add_inv_eq_add_inv_iff`, the same fibre computation that drove (12).

Stated with `m = k + 3` because the argument needs `1 ≤ m − 2`; the book's own chain
forces `m ≥ 3` anyway, since `u₁ = 0` and `u_{m-1} = α ≠ 0`. -/
theorem pow_eq_one_of_betaSum_eq {E : Type*} [Field E] {β α : E} (hβ : β ≠ 0)
    (hα : β + β⁻¹ = α) {k : ℕ} (hlast : betaSum β (k + 2) = α)
    (hne : ∀ i, 1 ≤ i → i ≤ k + 2 → β ^ i ≠ 1) :
    β ^ (k + 3) = 1 := by
  have hβk : β ^ (k + 2) ≠ 0 := pow_ne_zero _ hβ
  simp only [betaSum] at hlast
  rw [← hα] at hlast
  rcases (add_inv_eq_add_inv_iff hβk hβ).mp hlast with h | h
  · -- `β^{m-1} = β` would give `β^{m-2} = 1`
    exfalso
    refine hne (k + 1) (by omega) (by omega) ?_
    have e : β ^ (k + 1) * β = 1 * β := by
      rw [one_mul, ← pow_succ]
      exact h
    exact mul_right_cancel₀ hβ e
  · -- `β^{m-1} · β = 1` is `β^m = 1`
    rw [pow_succ]
    exact h

/-- **An automorphism of odd order fixes whatever its square fixes.**

If `orderOf θ = 2m + 1` then `θ = (θ²)^{m+1}`, so every `θ²`-fixed point is `θ`-fixed. -/
theorem apply_eq_self_of_odd_orderOf {E : Type*} [Field E] {θ : E ≃+* E}
    (hodd : Odd (orderOf θ)) {u : E} (hsq : θ (θ u) = u) : θ u = u := by
  obtain ⟨m, hm⟩ := hodd
  have hsq' : (θ ^ 2) u = u := by
    rw [sq, RingAut.mul_apply]
    exact hsq
  have hpow : ∀ k : ℕ, ((θ ^ 2) ^ k) u = u := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, RingAut.mul_apply, hsq', ih]
  have hx : (θ ^ 2) ^ (m + 1) = θ := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf θ + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  calc θ u = ((θ ^ 2) ^ (m + 1)) u := by rw [hx]
    _ = u := hpow _

/-- **`u ↦ u^{1+θ}` is bijective** on a finite field of characteristic `2` whose
automorphism `θ` has odd order (Peterfalvi Part II, p. 125: "the mapping
`u ↦ u^{1+θ} : F* → F*` … is bijective since `θ` is of odd order"; Peterfalvi calls
the inverse `τ`).  That `θ` has odd order is part of Appendix III, Definition 3 — the
definition of a Suzuki `2`-group of type `B`.

The book leaves the argument out.  It is: if `u^{1+θ} = v^{1+θ}` with `u, v ≠ 0`, then
`w = u/v` satisfies `w · θ(w) = 1`, so `w` and `θ(θ w)` are both inverse to `θ w` and
hence equal; odd order upgrades that to `θ w = w`, whence `w² = 1` and so `w = 1`
because the characteristic is `2`.  Injective on a finite type is bijective. -/
theorem frobNorm_bijective {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) :
    Function.Bijective (fun u : E => u * θ u) := by
  refine Finite.injective_iff_bijective.mp ?_
  have hzero : ∀ x : E, x * θ x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    exact frobNorm_ne_zero θ hne hx
  intro u v huv
  simp only at huv
  rcases eq_or_ne u 0 with rfl | hu
  · exact (hzero v (by rw [← huv]; simp)).symm
  rcases eq_or_ne v 0 with rfl | hv
  · exact absurd (hzero u (by rw [huv]; simp)) hu
  obtain ⟨w, hwne, rfl⟩ : ∃ w : E, w ≠ 0 ∧ u = w * v :=
    ⟨u / v, div_ne_zero hu hv, by field_simp⟩
  -- cancel the `v`-part: `w^{1+θ} = 1`
  have hkey : (w * θ w) * (v * θ v) = 1 * (v * θ v) := by
    rw [one_mul, ← frobNorm_mul, huv]
  have hw1 : w * θ w = 1 := mul_right_cancel₀ (frobNorm_ne_zero θ hv) hkey
  -- `w` and `θ(θ w)` are both inverse to `θ w`
  have hθθ : θ (θ w) = w := by
    have h1 : θ w * θ (θ w) = 1 := by rw [← map_mul, hw1, map_one]
    have h2 : θ w * w = 1 := by rw [mul_comm]; exact hw1
    exact mul_left_cancel₀ (by simpa using hwne) (h1.trans h2.symm)
  have hfix : θ w = w := apply_eq_self_of_odd_orderOf hodd hθθ
  rw [hfix] at hw1
  -- `w² = 1` in characteristic `2` forces `w = 1`
  have hw : w = 1 := by
    have hsq : (w + 1) * (w + 1) = 0 := by linear_combination hw1 + w * hchar + hchar
    have hroot := mul_self_eq_zero.mp hsq
    linear_combination hroot - hchar
  rw [hw, one_mul]

/-- **`τ`** (Peterfalvi Part II, p. 125): every `c` has a unique `u` with `u^{1+θ} = c`.
`τ` is the map `c ↦ u`; the book uses it in the recursion (11) for `(d_i)`. -/
theorem existsUnique_frobNorm_eq {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) (c : E) : ∃! u : E, u * θ u = c :=
  (frobNorm_bijective hchar hodd).existsUnique c

/-- **`u ↦ u^{1+θ}` as a multiplicative equivalence** (Peterfalvi Part II, p. 125).

Bundling the bijection (`frobNorm_bijective`) with its multiplicativity (`frobNorm_mul`)
makes the book's `τ` — the inverse — multiplicative for free.  That is exactly what the
induction for (14) needs, where `(c_i/α)^{2τ}` has to be split across a product. -/
noncomputable def frobNormEquiv {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) : E ≃* E :=
  { Equiv.ofBijective (fun u : E => u * θ u) (frobNorm_bijective hchar hodd) with
    map_mul' := frobNorm_mul θ }

@[simp] theorem frobNormEquiv_apply {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) (u : E) :
    frobNormEquiv hchar hodd u = u * θ u := rfl

/-- **`τ(u)^{1+θ} = u`** — the defining property of the book's `τ`, which is
`(frobNormEquiv …).symm`.  Multiplicativity of `τ` is then `map_mul` on that `MulEquiv`. -/
@[simp] theorem frobNormEquiv_symm_spec {E : Type*} [Field E] [Finite E]
    (hchar : (2 : E) = 0) {θ : E ≃+* E} (hodd : Odd (orderOf θ)) (u : E) :
    (frobNormEquiv hchar hodd).symm u * θ ((frobNormEquiv hchar hodd).symm u) = u :=
  (frobNormEquiv hchar hodd).apply_symm_apply u

@[simp] theorem frobNormEquiv_symm_zero {E : Type*} [Field E] [Finite E]
    (hchar : (2 : E) = 0) {θ : E ≃+* E} (hodd : Odd (orderOf θ)) :
    (frobNormEquiv hchar hodd).symm 0 = 0 := by
  rw [MulEquiv.symm_apply_eq, frobNormEquiv_apply, map_zero, mul_zero]

theorem frobNormEquiv_symm_ne_zero {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) {u : E} (hu : u ≠ 0) :
    (frobNormEquiv hchar hodd).symm u ≠ 0 := fun h =>
  hu ((frobNormEquiv hchar hodd).symm.injective
    (h.trans (frobNormEquiv_symm_zero hchar hodd).symm))

/-- `τ` respects division.  It is multiplicative and sends `0` to `0`, so it restricts to
a group automorphism of `F^×`; this is that, stated where it gets used. -/
theorem frobNormEquiv_symm_div {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) (x : E) {y : E} (hy : y ≠ 0) :
    (frobNormEquiv hchar hodd).symm (x / y)
      = (frobNormEquiv hchar hodd).symm x / (frobNormEquiv hchar hodd).symm y := by
  rw [eq_div_iff (frobNormEquiv_symm_ne_zero hchar hodd hy), ← map_mul,
    div_mul_cancel₀ _ hy]

/-- **`u^{2τ} = 1` forces `u = 1`** (Peterfalvi Part II, p. 126, inside step (15)).

Step (15) reads `c_{m₁} = α` off from `d_{m₁} = ζ⁻¹`: rearranged, that is
`ζ^{m₁+1} · (c_{m₁}/α)^{2τ} = 1` with the first factor in `W` and the second in `K`, so
`K ∩ W = 1` makes each of them `1`.  Getting from `(c_{m₁}/α)^{2τ} = 1` to
`c_{m₁} = α` is this lemma: squaring is injective in characteristic `2`, and `τ` is a
bijection fixing `1`. -/
theorem eq_one_of_frobNormEquiv_symm_sq_eq_one {E : Type*} [Field E] [Finite E]
    (hchar : (2 : E) = 0) {θ : E ≃+* E} (hodd : Odd (orderOf θ)) {u : E}
    (h : ((frobNormEquiv hchar hodd).symm u) ^ 2 = 1) : u = 1 := by
  have hx : (frobNormEquiv hchar hodd).symm u = 1 := by
    have hsq : ((frobNormEquiv hchar hodd).symm u + 1) *
        ((frobNormEquiv hchar hodd).symm u + 1) = 0 := by
      linear_combination h + ((frobNormEquiv hchar hodd).symm u) * hchar + hchar
    have hroot := mul_self_eq_zero.mp hsq
    linear_combination hroot - hchar
  have himg := congrArg (frobNormEquiv hchar hodd) hx
  rwa [MulEquiv.apply_symm_apply, map_one] at himg

/-- **A positive power below the order that is trivial pins the exponent**: if
`ζ^{n+1} = 1` with `ζ` of order `m` and `n + 1 ≤ m`, then `n + 1 = m`.

Step (15) finishes with exactly this: `m₁ ≤ m − 1` and `ζ^{m₁+1} = 1` with `ζ` of order
`m` give `m₁ = m − 1`, the length of the sequences. -/
theorem eq_of_pow_succ_eq_one_of_le {H : Type*} [Group H] {ζ : H} {m n : ℕ}
    (hord : orderOf ζ = m) (h : ζ ^ (n + 1) = 1) (hle : n + 1 ≤ m) : n + 1 = m := by
  have hdvd : m ∣ n + 1 := hord ▸ orderOf_dvd_of_pow_eq_one h
  have hm : m ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) hdvd
  omega

/-- **Peterfalvi Part II, Ch. IV §2, step (14)** (p. 126): the closed form
`d_i = ζ^i (c_i/α)^{2τ}` satisfies the recursion `d_{i+1} = d_i ζ u_{i+1}^{-2τ}` of (11).

The book gets (14) "by induction on `i`" from (11); this is the induction step.  All of
its content is that `τ` is multiplicative, together with the algebraic identity
`(c_i/α) / (c_i/c_{i+1}) = c_{i+1}/α`. -/
theorem betaScale_succ {E : Type*} [Field E] [Finite E] (hchar : (2 : E) = 0)
    {θ : E ≃+* E} (hodd : Odd (orderOf θ)) {α β ζ : E} (hαne : α ≠ 0) (i : ℕ)
    (hci : betaSum β i ≠ 0) (hci1 : betaSum β (i + 1) ≠ 0) :
    ζ ^ i * ((frobNormEquiv hchar hodd).symm (betaSum β i / α)) ^ 2 * ζ *
        (((frobNormEquiv hchar hodd).symm (betaRatio β i)) ^ 2)⁻¹
      = ζ ^ (i + 1) * ((frobNormEquiv hchar hodd).symm (betaSum β (i + 1) / α)) ^ 2 := by
  have hratne : betaRatio β i ≠ 0 := by
    simp only [betaRatio]
    exact div_ne_zero hci hci1
  have hdiv : betaSum β i / α / betaRatio β i = betaSum β (i + 1) / α := by
    simp only [betaRatio]
    field_simp
  have hτ : (frobNormEquiv hchar hodd).symm (betaSum β i / α)
      / (frobNormEquiv hchar hodd).symm (betaRatio β i)
      = (frobNormEquiv hchar hodd).symm (betaSum β (i + 1) / α) := by
    rw [← frobNormEquiv_symm_div hchar hodd _ hratne, hdiv]
  have hBne : (frobNormEquiv hchar hodd).symm (betaRatio β i) ≠ 0 :=
    frobNormEquiv_symm_ne_zero hchar hodd hratne
  rw [← hτ, div_pow, pow_succ]
  field_simp
  ring

/-- `τ` maps `F^×` into `F^×`: the solution of `u^{1+θ} = c` is nonzero when `c` is.
The recursion (11) needs this, since it inverts `u_{i+1}^τ`. -/
theorem existsUnique_frobNorm_eq_of_ne_zero {E : Type*} [Field E] [Finite E]
    (hchar : (2 : E) = 0) {θ : E ≃+* E} (hodd : Odd (orderOf θ)) {c : E} (hc : c ≠ 0) :
    ∃! u : E, u ≠ 0 ∧ u * θ u = c := by
  obtain ⟨u, hu, huniq⟩ := existsUnique_frobNorm_eq hchar hodd c
  have hune : u ≠ 0 := by
    rintro rfl
    exact hc (by simpa using hu.symm)
  exact ⟨u, ⟨hune, hu⟩, fun v hv => huniq v hv.2⟩

/-! ### Step (17): `v_i = u_i + α` (p. 126)

The book shows `v_i + u_i` is constant by computing `u_i/u_{i+1} = 1 + d_i^{-(1+σ)}`.
All of that rests on one identity, `c_{i-1} c_{i+1} = c_i² + c₁²`, which holds because
squaring loses the cross term in characteristic `2`.
-/

/-- `(a + a⁻¹)² = a² + (a²)⁻¹` in characteristic `2`: the cross term `2·a·a⁻¹` vanishes. -/
theorem add_inv_sq {E : Type*} [Field E] (h2 : (2 : E) = 0) {a : E} (ha : a ≠ 0) :
    (a + a⁻¹) ^ 2 = a ^ 2 + (a ^ 2)⁻¹ := by
  have hinv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  rw [← inv_pow]
  linear_combination 2 * hinv + h2

/-- **`c_j² = c_{2j}`** in characteristic `2` — squaring doubles the index. -/
theorem betaSum_sq {E : Type*} [Field E] (h2 : (2 : E) = 0) {β : E} (hβ : β ≠ 0)
    (j : ℕ) : betaSum β j ^ 2 = betaSum β (2 * j) := by
  simp only [betaSum]
  rw [add_inv_sq h2 (pow_ne_zero j hβ), ← pow_mul, mul_comm j 2]

/-- **`c_i · c_{i+2} = c_{i+1}² + c₁²`** — the identity behind step (17)
(Peterfalvi Part II, p. 126).

Once the two squares are rewritten by `betaSum_sq` this is exact algebra: both sides come
to `β^{2i+2} + β^{-2i-2} + β² + β^{-2}`.  Dividing by `c_{i+1}²` turns it into the book's
`u_i/u_{i+1} = 1 + (c₁/c_{i+1})² = 1 + d_i^{-(1+σ)}`, which is what makes `v_i + u_i`
constant, hence equal to `v₁ + u₁ = α`. -/
theorem betaSum_mul_betaSum_add_two {E : Type*} [Field E] (h2 : (2 : E) = 0) {β : E}
    (hβ : β ≠ 0) (i : ℕ) :
    betaSum β i * betaSum β (i + 2)
      = betaSum β (i + 1) ^ 2 + betaSum β 1 ^ 2 := by
  rw [betaSum_sq h2 hβ, betaSum_sq h2 hβ]
  simp only [betaSum]
  have hβi : β ^ i ≠ 0 := pow_ne_zero _ hβ
  have hβ2 : β ≠ 0 := hβ
  field_simp
  ring

/-- **Peterfalvi Part II, Ch. IV §2, step (17)**, the computation (p. 126):

  `u_i / u_{i+1} = 1 + (c₁/c_{i+1})²`,

the book's `1 + d_i^{-(1+σ)}`.  Multiplying by `u_{i+1}` gives
`u_i = u_{i+1} + u_{i+1} d_i^{-(1+σ)}`, so the recursion
`v_{i+1} = v_i + u_{i+1} d_i^{-(1+σ)}` of (11) preserves `v + u`; hence
`v_i + u_i = v₁ + u₁ = α`, which is step (17)'s `v_i = u_i + α`. -/
theorem betaRatio_div_betaRatio {E : Type*} [Field E] (h2 : (2 : E) = 0) {β : E}
    (hβ : β ≠ 0) (i : ℕ) (hci : betaSum β i ≠ 0) (hci1 : betaSum β (i + 1) ≠ 0)
    (hci2 : betaSum β (i + 2) ≠ 0) :
    betaRatio β i / betaRatio β (i + 1)
      = 1 + (betaSum β 1 / betaSum β (i + 1)) ^ 2 := by
  have hstep : betaRatio β i / betaRatio β (i + 1)
      = betaSum β i * betaSum β (i + 2) / betaSum β (i + 1) ^ 2 := by
    simp only [betaRatio]
    field_simp
  rw [hstep, betaSum_mul_betaSum_add_two h2 hβ i, add_div,
    div_self (pow_ne_zero 2 hci1), ← div_pow]

/-- **The element `a` of step (19)** (Peterfalvi Part II, p. 127): for `x ≠ u` there is a
nonzero `a` with `a^{-(1+θ)} = x + u`, i.e. `x + a^{-(1+θ)} = u` in characteristic `2`.

`x ≠ u` says `x + u ≠ 0`, and `u ↦ u^{1+θ}` is bijective on `F^×`, so the root exists;
`a` is its inverse.  The book's hypothesis `x₁ ≠ u_i` comes from `f(ω₁(0,x₁))` not lying
in the `KW`-orbit of `ω₁`. -/
theorem exists_inv_frobNorm_eq_of_ne {E : Type*} [Field E] [Finite E]
    (hchar : (2 : E) = 0) {θ : E ≃+* E} (hodd : Odd (orderOf θ)) {x u : E} (hne : x ≠ u) :
    ∃ a : E, a ≠ 0 ∧ a⁻¹ * θ a⁻¹ = x + u := by
  have hne0 : x + u ≠ 0 := fun h => hne (by linear_combination h - u * hchar)
  obtain ⟨v, ⟨hvne, hv⟩, -⟩ := existsUnique_frobNorm_eq_of_ne_zero hchar hodd hne0
  refine ⟨v⁻¹, inv_ne_zero hvne, ?_⟩
  rw [inv_inv]
  exact hv

/-- **The conclusion `α₁ = α₂ = x₁ + x₂` of step (20)** (Peterfalvi Part II, p. 128).

Instance `i = 1` of the book's (∗∗∗) gives `x₁ = x₂ + α₂`, and instance `i = m − 1` gives
`x₁ + α₁ = x₂`.  In characteristic `2` each of those says that one of the two `α`'s is
`x₁ + x₂`, so they agree — which is the first assertion of (20), and what lets the two
families of sequences `(u_i)` and `(u'_i)` be identified. -/
theorem eq_add_of_add_char_two {E : Type*} [Field E] (h2 : (2 : E) = 0)
    {x₁ x₂ α₁ α₂ : E} (ha : x₁ = x₂ + α₂) (hb : x₁ + α₁ = x₂) :
    α₁ = x₁ + x₂ ∧ α₂ = x₁ + x₂ ∧ α₁ = α₂ := by
  have hα₁ : α₁ = x₁ + x₂ := by linear_combination hb - x₁ * h2
  have hα₂ : α₂ = x₁ + x₂ := by linear_combination -ha - x₂ * h2
  exact ⟨hα₁, hα₂, hα₁.trans hα₂.symm⟩

/-- **Unrolling the recursion of step (18)** (Peterfalvi Part II, p. 127).

From `F(i+2) = g · F(i+1) · z(i+2)` one gets `F(n+1) = gⁿ · F(1) · ∏_{j=2}^{n+1} z(j)`.

No commutativity is needed: the scalars accumulate on the right in order, and the `g`'s
collect on the left because each step contributes one at the front.

The book's `h(ω(0,u_i)) = (h(ω)ζ⁻¹) · h(ω(0,u_{i-1})) · (ζ u_i)` has exactly this shape,
with `g = h(ω)ζ⁻¹` and `z(i) = ζ u_i`. -/
theorem eq_pow_mul_prod_of_rec {H : Type*} [Group H] (F : ℕ → H) (g : H) (z : ℕ → H)
    (hrec : ∀ i, F (i + 2) = g * F (i + 1) * z (i + 2)) (n : ℕ) :
    F (n + 1) = g ^ n * F 1 * ((List.range n).map fun j => z (j + 2)).prod := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [hrec k, ih, List.range_succ, List.map_append, List.prod_append, pow_succ']
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    group

/-- **The telescoping product behind step (18)** (Peterfalvi Part II, p. 127):

  `u₂ u₃ ⋯ u_i = c₁ / c_i`.

Unrolling the recursion `h(ω(0,u_i)) = (h(ω)ζ⁻¹) · h(ω(0,u_{i-1})) · (ζ u_i)` collects the
scalars into `ζ^{i-1}` times this product — which is what produces the `α/(β^i + β^{-i})`
of the book's closed form, `α` being `c₁`. -/
theorem prod_betaRatio {E : Type*} [Field E] {β : E} (n : ℕ)
    (hne : ∀ j, j ≤ n → betaSum β (j + 1) ≠ 0) :
    ∏ j ∈ Finset.Ico 1 (n + 1), betaRatio β j = betaSum β 1 / betaSum β (n + 1) := by
  induction n with
  | zero => simp [div_self (hne 0 le_rfl)]
  | succ k ih =>
    rw [Finset.prod_Ico_succ_top (by omega), ih fun j hj => hne j (by omega)]
    have h1 : betaSum β (k + 1) ≠ 0 := hne k (by omega)
    have h2 : betaSum β (k + 1 + 1) ≠ 0 := hne (k + 1) le_rfl
    simp only [betaRatio]
    field_simp

/-! ### Step (18): `u_i` is fixed by `θ`, so `u_i^{2τ} = u_i` (p. 127)

Step (18) opens with "by (13) and (16), `u_i^θ = u_i` and so `u_i^{2τ} = u_i`".  Both
halves are recorded here: (16) says `σ` inverts `β`, which makes it fix every
`c_j = β^j + β^{-j}` and hence every ratio `u_i = c_{i-1}/c_i`; and on a `θ`-fixed
element `u ↦ u^{1+θ}` is just squaring, so `τ` is a square root there.
-/

/-- **An automorphism inverting `β` fixes every `c_j = β^j + β^{-j}`.**

This is how step (18) gets `u_i^θ = u_i`: by (16) `β` generates `W`, so `β^σ = β⁻¹`, and
`σ` then swaps the two summands of `c_j`.  The ratios `u_i = c_{i-1}/c_i` inherit it. -/
theorem betaSum_fixed_of_inv {E : Type*} [Field E] {β : E} {θ : E ≃+* E}
    (hinv : θ β = β⁻¹) (j : ℕ) : θ (betaSum β j) = betaSum β j := by
  simp only [betaSum, map_add, map_pow, map_inv₀, hinv, inv_pow, inv_inv]
  ring

/-- **`u^{2τ} = u` for `θ`-fixed `u`** (Peterfalvi Part II, p. 127, inside step (18)).

`τ(u) · θ(τ(u)) = u` by definition of `τ`; applying `θ` and cancelling gives
`θ²(τ u) = τ u`, which odd order upgrades to `θ(τ u) = τ u`
(`apply_eq_self_of_odd_orderOf`).  Then `τ(u)² = τ(u) · θ(τ(u)) = u`. -/
theorem frobNormEquiv_symm_sq_of_fixed {E : Type*} [Field E] [Finite E]
    (hchar : (2 : E) = 0) {θ : E ≃+* E} (hodd : Odd (orderOf θ)) {u : E} (hu : u ≠ 0)
    (hfix : θ u = u) : ((frobNormEquiv hchar hodd).symm u) ^ 2 = u := by
  have hspec : (frobNormEquiv hchar hodd).symm u * θ ((frobNormEquiv hchar hodd).symm u)
      = u := frobNormEquiv_symm_spec hchar hodd u
  have hvne : (frobNormEquiv hchar hodd).symm u ≠ 0 :=
    frobNormEquiv_symm_ne_zero hchar hodd hu
  have hθθ : θ (θ ((frobNormEquiv hchar hodd).symm u))
      = (frobNormEquiv hchar hodd).symm u := by
    have h1 : θ ((frobNormEquiv hchar hodd).symm u) *
        θ (θ ((frobNormEquiv hchar hodd).symm u)) = u := by
      rw [← map_mul, hspec, hfix]
    have h2 : θ ((frobNormEquiv hchar hodd).symm u) *
        (frobNormEquiv hchar hodd).symm u = u := by
      rw [mul_comm]; exact hspec
    exact mul_left_cancel₀ (by simpa using hvne) (h1.trans h2.symm)
  have hfv : θ ((frobNormEquiv hchar hodd).symm u)
      = (frobNormEquiv hchar hodd).symm u := apply_eq_self_of_odd_orderOf hodd hθθ
  calc ((frobNormEquiv hchar hodd).symm u) ^ 2
      = (frobNormEquiv hchar hodd).symm u * (frobNormEquiv hchar hodd).symm u := sq _
    _ = (frobNormEquiv hchar hodd).symm u *
          θ ((frobNormEquiv hchar hodd).symm u) := by rw [hfv]
    _ = u := hspec


/-- **The counting step behind `θ = 1`** (Peterfalvi Part II, p. 130, §3 stage (3)).

If an injective additive map `θ` on a field of characteristic `2` satisfies
`X + θ X = c` for every `X` outside the two-element set `{0, z}`, and the field has at
least `5` elements, then `θ` is the identity.

This is the book's

> `c = X + Y + (X+Y)^θ = c + c = 0`.  Thus `X^θ = X` for `X ∈ F − {0, α^{2τ}}`, whence
> `θ = 1`.

Pick `X` outside `{0, z}` and then `Y` outside the four values `0, z, X, X + z`, so that
`X`, `Y` and `X + Y` all lie where the hypothesis applies; additivity then gives
`c = c + c`, i.e. `c = 0`.  The remaining point `z` is fixed because `θ` is injective and
already fixes everything else.

The book's `|F| ≥ 8` comes from `θ` having odd order in the cyclic automorphism group of
`F`; `5` is all the counting needs. -/
theorem eq_self_of_add_eq_const {F : Type*} [Field F] [Finite F] (h2 : (2 : F) = 0)
    (θ : F →+ F) (hinj : Function.Injective θ) {z c : F}
    (hconst : ∀ X : F, X ≠ 0 → X ≠ z → X + θ X = c)
    (hcard : 5 ≤ Nat.card F) (X : F) : θ X = X := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcardF : 5 ≤ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  -- an element outside `{0, z}`
  obtain ⟨x, hx⟩ : ∃ x : F, x ∉ ({0, z} : Finset F) := by
    by_contra hcon
    push Not at hcon
    have hle := Finset.card_le_card (fun a (_ : a ∈ Finset.univ) => hcon a)
    rw [Finset.card_univ] at hle
    have e1 := Finset.card_insert_le (0 : F) {z}
    have e2 : ({z} : Finset F).card = 1 := Finset.card_singleton _
    omega
  -- an element outside `{0, z, x, x + z}`
  obtain ⟨y, hy⟩ : ∃ y : F, y ∉ ({0, z, x, x + z} : Finset F) := by
    by_contra hcon
    push Not at hcon
    have hle := Finset.card_le_card (fun a (_ : a ∈ Finset.univ) => hcon a)
    rw [Finset.card_univ] at hle
    have e1 := Finset.card_insert_le (0 : F) {z, x, x + z}
    have e2 := Finset.card_insert_le z ({x, x + z} : Finset F)
    have e3 := Finset.card_insert_le x ({x + z} : Finset F)
    have e4 : ({x + z} : Finset F).card = 1 := Finset.card_singleton _
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx hy
  obtain ⟨hx0, hxz⟩ := hx
  obtain ⟨hy0, hyz, hyx, hyxz⟩ := hy
  -- `x + y` also avoids `{0, z}`
  have hxy0 : x + y ≠ 0 := by
    intro hc
    exact hyx (by linear_combination hc - x * h2)
  have hxyz : x + y ≠ z := by
    intro hc
    exact hyxz (by linear_combination hc - x * h2)
  -- `c = 0`
  have hc0 : c = 0 := by
    have e1 := hconst x hx0 hxz
    have e2 := hconst y hy0 hyz
    have e3 := hconst (x + y) hxy0 hxyz
    rw [map_add] at e3
    linear_combination e3 - e1 - e2
  -- everything outside `{0, z}` is fixed
  have hfix : ∀ V : F, V ≠ 0 → V ≠ z → θ V = V := by
    intro V h0 hz
    have hV := hconst V h0 hz
    rw [hc0] at hV
    linear_combination hV - V * h2
  rcases eq_or_ne X 0 with rfl | hX0
  · exact map_zero θ
  rcases eq_or_ne X z with rfl | hXz
  · rcases eq_or_ne X (0 : F) with rfl | hz0
    · exact map_zero θ
    by_contra hne
    have hθz0 : θ X ≠ 0 := fun hc => hz0 (hinj (by rw [hc, map_zero]))
    exact hne (hinj (hfix (θ X) hθz0 hne))
  · exact hfix X hX0 hXz

/-- **The last line of §3 (3)** (Peterfalvi Part II, p. 130): `(∗)` with the `θ`-term
gone reads `α² = (ζ + ζ⁻¹)²`, and squaring is injective in characteristic `2`. -/
theorem eq_add_inv_of_sq_add_sq {E : Type*} [Field E] (h2 : (2 : E) = 0) {α ζ : E}
    (hstar : α ^ 2 + ζ ^ 2 + (ζ⁻¹) ^ 2 = 0) : α = ζ + ζ⁻¹ := by
  have hsq : (α + (ζ + ζ⁻¹)) ^ 2 = 0 := by
    linear_combination hstar + (α * ζ + α * ζ⁻¹ + ζ * ζ⁻¹) * h2
  have hzero : α + (ζ + ζ⁻¹) = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  linear_combination hzero - (ζ + ζ⁻¹) * h2

/-- **§3 (3), the field part** (Peterfalvi Part II, p. 130): the book's equation

  `(∗)  α² + ζ² + ζ⁻² + (ζ + ζ⁻¹)(X + X^θ) = 0`   for `X ∈ F − {0, z}`

forces `θ = 1` and `α = ζ + ζ⁻¹`.

Since `ζ + ζ⁻¹ ≠ 0`, `(∗)` says exactly that `X + X^θ` is *independent of `X`* on
`F − {0, z}`, which is the hypothesis of `eq_self_of_add_eq_const`; and once `θ = 1` the
bracket vanishes in characteristic `2`, leaving `α² = (ζ + ζ⁻¹)²`. -/
theorem eq_one_and_eq_add_inv_of_star {E : Type*} [Field E] [Finite E] (h2 : (2 : E) = 0)
    (θ : E →+ E) (hinj : Function.Injective θ) {α ζ z : E}
    (hζ : ζ + ζ⁻¹ ≠ 0) (hcard : 5 ≤ Nat.card E)
    (hstar : ∀ X : E, X ≠ 0 → X ≠ z →
      α ^ 2 + ζ ^ 2 + (ζ⁻¹) ^ 2 + (ζ + ζ⁻¹) * (X + θ X) = 0) :
    (∀ X : E, θ X = X) ∧ α = ζ + ζ⁻¹ := by
  classical
  haveI : Fintype E := Fintype.ofFinite E
  have hcardE : 5 ≤ Fintype.card E := by rwa [← Nat.card_eq_fintype_card]
  -- `X + X^θ` is the same constant for every admissible `X`
  have hconst : ∀ X : E, X ≠ 0 → X ≠ z →
      X + θ X = (α ^ 2 + ζ ^ 2 + (ζ⁻¹) ^ 2) / (ζ + ζ⁻¹) := by
    intro X h0 hz
    rw [eq_div_iff hζ]
    linear_combination hstar X h0 hz - (α ^ 2 + ζ ^ 2 + (ζ⁻¹) ^ 2) * h2
  have hθ := eq_self_of_add_eq_const h2 θ hinj hconst hcard
  refine ⟨hθ, ?_⟩
  -- an admissible `X`, at which `(∗)` loses its bracket
  obtain ⟨X, hX⟩ : ∃ X : E, X ∉ ({0, z} : Finset E) := by
    by_contra hcon
    push Not at hcon
    have hle := Finset.card_le_card (fun b (_ : b ∈ Finset.univ) => hcon b)
    rw [Finset.card_univ] at hle
    have e1 := Finset.card_insert_le (0 : E) {z}
    have e2 : ({z} : Finset E).card = 1 := Finset.card_singleton _
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hX
  have hs := hstar X hX.1 hX.2
  rw [hθ X] at hs
  refine eq_add_inv_of_sq_add_sq h2 ?_
  linear_combination hs - (ζ + ζ⁻¹) * X * h2


/-- **From the two readings of stage (2) to `b² = ζ + ζ⁻¹ + a⁻²`**
(Peterfalvi Part II, p. 130, inside §3 (3)).

Cross-multiplying `1/(a² + ζ⁻¹) = ζ a⁻²/(b² + ζ⁻¹)` gives
`b² + ζ⁻¹ = ζ a⁻²(a² + ζ⁻¹) = ζ + a⁻²`. -/
theorem sq_eq_of_one_div_eq {E : Type*} [Field E] (h2 : (2 : E) = 0) {a b ζ : E}
    (hζ : ζ ≠ 0) (ha : a ≠ 0) (hA : a ^ 2 + ζ⁻¹ ≠ 0) (hB : b ^ 2 + ζ⁻¹ ≠ 0)
    (heq : 1 / (a ^ 2 + ζ⁻¹) = ζ * (a ^ 2)⁻¹ / (b ^ 2 + ζ⁻¹)) :
    b ^ 2 = ζ + ζ⁻¹ + (a ^ 2)⁻¹ := by
  have ha2 : (a : E) ^ 2 ≠ 0 := pow_ne_zero 2 ha
  have hexp : ζ * (a ^ 2)⁻¹ * (a ^ 2 + ζ⁻¹) = ζ + (a ^ 2)⁻¹ := by
    field_simp
  rw [div_eq_div_iff hA hB, one_mul, hexp] at heq
  linear_combination heq - ζ⁻¹ * h2

/-- **`(∗)` from `b² = ζ + ζ⁻¹ + a⁻²`** (Peterfalvi Part II, p. 130, inside §3 (3)).

Raising `b² = (ζ + ζ⁻¹) + X` to the `1 + θ` and comparing with
`b^{2(1+θ)} = α² + X^{1+θ}` leaves `α² + (ζ+ζ⁻¹)² + (ζ+ζ⁻¹)(X + X^θ) = 0`, which is the
book's `(∗)` once `(ζ+ζ⁻¹)² = ζ² + ζ⁻²` is expanded.  The input `θ(ζ + ζ⁻¹) = ζ + ζ⁻¹`
is the book's "as `ζ ∈ W`, `(ζ + ζ⁻¹)^θ = ζ^σ + ζ^{-σ} = ζ + ζ⁻¹`". -/
theorem star_of_sq_eq {E : Type*} [Field E] (h2 : (2 : E) = 0) (θ : E →+ E)
    {α ζ X Y : E} (hθw : θ (ζ + ζ⁻¹) = ζ + ζ⁻¹)
    (hY : Y = (ζ + ζ⁻¹) + X) (hnorm : Y * θ Y = α ^ 2 + X * θ X) :
    α ^ 2 + ζ ^ 2 + (ζ⁻¹) ^ 2 + (ζ + ζ⁻¹) * (X + θ X) = 0 := by
  subst hY
  rw [map_add, hθw] at hnorm
  linear_combination -hnorm + (ζ * ζ⁻¹ + ζ * X + ζ * θ X + ζ ^ 2 + ζ⁻¹ * X
    + ζ⁻¹ * θ X + (ζ⁻¹) ^ 2) * h2


end OddOrder.Peterfalvi.Appendices.Suzuki
