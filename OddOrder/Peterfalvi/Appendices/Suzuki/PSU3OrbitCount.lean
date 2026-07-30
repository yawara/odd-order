/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3Preliminary
import OddOrder.Peterfalvi.Appendices.Suzuki.QuotientKWField
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelIsomorphism

/-!
# Peterfalvi Part II, Ch. IV §2: the orbit count of step (8)

The model-dependent half of step (8) (p. 124).  `PSU3Preliminary` supplies the purely
group-theoretic content — steps (1)–(7), the two fibre bounds, `D = K W` — and this
file adds what needs the standard model of Ch. III §3 (`QuotientFieldModel`):

* the scalar group `μ(KW) ≤ E^×` and its order `(q − 1)|W|`;
* the orbit count `n = |E^×| / |μ(KW)| = (q + 1)/|W|`;
* the map `Φ = orbitOfF : Q₀ → E^× ⧸ μ(KW)` sending `x` to the `KW`-orbit of
  `f(ω x)`, together with the translation of its fibres into the shape the bounds of
  `PSU3Preliminary` consume;
* the two fibre bounds `m_i ≤ |V|` and `m₁ ≤ |V| − 1` in terms of `Φ`.

The arithmetic lemmas at the top are stated for arbitrary types/groups; their only
consumers are in this file.

## Main results

* `Hypothesis.index_range_mu` — `n = (q + 1)/|W|`.
* `Hypothesis.orbitOfF` — the map `Φ` of step (8).
* `Hypothesis.ncard_fiber_orbitOfF_le`, `Hypothesis.ncard_fiber_orbitOfF_base_le` —
  the fibre bounds.
* `card_fiber_eq_of_card_eq` — the squeeze that turns them into equalities.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

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

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp
/-! ## The scalar group `μ(KW)` inside `E^×`

Step (8) counts the `KW`-orbits on `(Q/Q₀)^# ≅ E^×`, i.e. the index of `μ(KW)` in
`E^×`.  The two containments recorded in `QuotientFieldModel` — `μ(K) ⊆ F^×` and
`μ(W)` in the norm-one subgroup — pin its order down to `(q − 1) · |W|`.
-/

/-- `μ(k)^{q−1} = 1`: `μ(K)` lies in `F^× = 𝐅_q^×`
(`QuotientFieldModel.mu_K_frobFixed` says `μ(k)^q = μ(k)`). -/
theorem mu_K_pow_two_pow_sub_one {m : ℕ} (M : hyp.QuotientFieldModel m)
    (k : ↥hyp.actualKActor) : M.mu (k, 1) ^ (2 ^ m - 1) = 1 := by
  have hfix : M.mu (k, 1) ^ (2 ^ m) = M.mu (k, 1) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact M.mu_K_frobFixed k
  have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e : (2 : ℕ) ^ m = 1 + (2 ^ m - 1) := by omega
  rw [e, pow_add, pow_one] at hfix
  have h2 : M.mu (k, 1) * M.mu (k, 1) ^ (2 ^ m - 1) = M.mu (k, 1) * 1 := by
    rw [mul_one]; exact hfix
  exact mul_left_cancel h2

/-- **`|K| = q − 1`**: `μ` maps `K` bijectively onto `F^× = 𝐅_q^×`.

Injectivity is `QuotientFieldModel.mu_K_injective`; surjectivity is
`exists_actualKActor_mu_eq`; and `|F| = q` is
`OddOrder.FiniteField.natCard_frobFixedSubfield`. -/
theorem card_actualKActor_eq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) :
    Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
  classical
  set f : ↥hyp.actualKActor → M.E := fun k => ((M.mu (k, 1) : M.Eˣ) : M.E) with hf
  have hinj : Function.Injective f := fun k k' h => M.mu_K_injective (Units.ext h)
  have hrange : Set.range f
      = ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k),
        Units.ne_zero _⟩
    · rintro a ⟨haF, ha0⟩
      obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card haF
        (by simpa using ha0)
      exact ⟨k, hk⟩
  have hcardF : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E)).ncard
      = 2 ^ m := by
    rw [← Nat.card_coe_set_eq]
    exact OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
  have hT : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}).ncard
      = 2 ^ m - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem
      (OddOrder.FiniteField.frobFixedSubfield M.E 2 m).zero_mem, hcardF]
  have hcard : Nat.card ↥hyp.actualKActor = (Set.range f).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_range_of_injective hinj).symm
  rw [hcard, hrange, hT]

/-- **`μ(K) ∩ μ(W) = 1`**: a common value is killed by both `q − 1` and `q + 1`, which
are coprime. -/
theorem mu_K_eq_mu_W_imp_eq_one {m : ℕ} (hm : m ≠ 0) (M : hyp.QuotientFieldModel m)
    {k : ↥hyp.actualKActor} {v : ↥hyp.W} (heq : M.mu (k, 1) = M.mu (1, v)) :
    M.mu (k, 1) = 1 :=
  eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one hm
    (hyp.mu_K_pow_two_pow_sub_one M k)
    (by rw [heq]; exact M.mu_W_normOne v)

/-- **The number of `KW`-orbits on `(Q/Q₀)^#` is `n = (q + 1)/|W|`.**

Since `KW` acts on `Q/Q₀ ≅ E` by scalars, its orbits on `E^×` are the cosets of the
subgroup `μ(KW) ≤ E^×`, so their number is the index of that subgroup.  Its order is
`|K| · |W| = (q − 1)|W|` (by injectivity of `μ`), and `|E^×| = q² − 1`. -/
theorem index_range_mu {m : ℕ} (hm : m ≠ 0) (M : hyp.QuotientFieldModel m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1) :
    (MonoidHom.range M.mu).index = (2 ^ m + 1) / Nat.card ↥hyp.W := by
  classical
  haveI : Fintype M.E := Fintype.ofFinite _
  have hrange : Nat.card ↥(MonoidHom.range M.mu)
      = (2 ^ m - 1) * Nat.card ↥hyp.W := by
    have e1 : Nat.card (↥hyp.actualKActor × ↥hyp.W) = Nat.card ↥(MonoidHom.range M.mu) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← e1, Nat.card_prod, hK]
  have hunits : Nat.card M.Eˣ = (2 ^ m) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, M.card]
  have hidx := (MonoidHom.range M.mu).index_mul_card
  rw [hrange, hunits] at hidx
  have hpos : 0 < (2 ^ m - 1) * Nat.card ↥hyp.W := by
    have h2 : (2 : ℕ) ≤ 2 ^ m := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
    have hW : 0 < Nat.card ↥hyp.W := Nat.card_pos
    have h1 : 0 < 2 ^ m - 1 := by omega
    exact Nat.mul_pos h1 hW
  rw [← two_pow_sq_sub_one_div (e := m) (m := Nat.card ↥hyp.W) hm]
  rw [← hidx, Nat.mul_div_cancel _ hpos]

/-- The coordinate of an element of `Q − Q₀` is a **nonzero** element of `E`.

`coord` is an additive isomorphism `Q/Z(Q) ≃+ E`, and under `Z(Q) = Q₀` (the
`LemmaFiveSetup` hypothesis) an element of `Q` has trivial image in the quotient
exactly when it lies in `Q₀`.  This is what lets step (8) send `x ∈ Q₀` to a *unit*
of `E`, hence to a coset of `μ(KW)`. -/
theorem coord_ne_zero_of_not_mem_Q0 {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z : G} (hzQ : z ∈ hyp.Q) (hzQ0 : z ∉ hyp.Q0) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) ≠ 0 := by
  intro hc
  refine hzQ0 ?_
  have hzero : (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 :=
    (AddEquiv.map_eq_zero_iff M.coord).mp hc
  have hone : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = 1 := hzero
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q :=
    QuotientGroup.eq_one_iff _ |>.mp hone
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

/-- `f(ω x) ∈ Q` for `x ∈ Q₀` — named so that it can serve as the coercion proof in
`fUnit`, making `fUnit_val` hold by `rfl`. -/
theorem f_mul_mem_Q {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    f (ω * (x : G)) ∈ hyp.Q :=
  (hyp.f_mem_sdiff_Q0 H hC2 (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).1
    (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).2).1

/-- `f(ω x) ∉ Q₀` for `x ∈ Q₀`. -/
theorem f_mul_not_mem_Q0 {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    f (ω * (x : G)) ∉ hyp.Q0 :=
  (hyp.f_mem_sdiff_Q0 H hC2 (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).1
    (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).2).2

/-- The coordinate of `f(ω x)` as a **unit** of `E`. -/
noncomputable def fUnit {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) : M.Eˣ :=
  Units.mk0 (M.coord (Additive.ofMul (QuotientGroup.mk
      (⟨f (ω * (x : G)), hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x⟩ : ↥hyp.Q))))
    (hyp.coord_ne_zero_of_not_mem_Q0 M hZ _ (hyp.f_mul_not_mem_Q0 H hC2 hωQ hωQ0 x))

@[simp] theorem fUnit_val {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    ((hyp.fUnit M hZ H hC2 hωQ hωQ0 x : M.Eˣ) : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk
          (⟨f (ω * (x : G)), hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x⟩ : ↥hyp.Q))) := rfl

/-- Elements of `Q₀` have **zero** coordinate in `E` — the `(0, ·)` half of the book's
`y = (0, α)` (p. 125).

Converse of `coord_ne_zero_of_not_mem_Q0`: under `Z(Q) = Q₀` an element of `Q₀` is
trivial in `Q/Z(Q)`, so its coordinate vanishes.  Step (10) needs this to speak of the
second coordinate `α` of `y` at all. -/
theorem coord_eq_zero_of_mem_Q0 {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z : G} (hzQ : z ∈ hyp.Q) (hzQ0 : z ∈ hyp.Q0) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 := by
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q := by
    rw [hZ, Subgroup.mem_subgroupOf]
    exact hzQ0
  have hone : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  have hzero : (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 := hone
  rw [hzero, map_zero]

/-- **The map of step (8)**: `x ∈ Q₀ ↦` the `μ(KW)`-coset of the coordinate of
`f(ω x)`.

Because `KW` acts on `Q/Q₀ ≅ E` by scalars, this coset is exactly the `KW`-orbit the
book refers to. -/
noncomputable def orbitOfF {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    M.Eˣ ⧸ (MonoidHom.range M.mu) :=
  QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x)

/-- **`conjQHom kv` is conjugation by an element of `D`.**

`actualKActor` is the range of `conjQByK`, and both `conjQByK k` and `conjQByW v` are
literally `x ↦ k x k⁻¹` and `x ↦ v x v⁻¹`; composing them gives conjugation by `k v`,
which lies in `D` since `K ≤ D` and `W ≤ V ≤ D`.

This is what turns the `KW`-orbit of step (8) into a `D`-conjugacy class, so that
`exists_conj_mul_Q0_iff` applies. -/
theorem exists_mem_D_conjQHom (kv : ↥hyp.actualKActor × ↥hyp.W) :
    ∃ d ∈ hyp.D, ∀ x : ↥hyp.Q,
      ((hyp.conjQHom kv x : ↥hyp.Q) : G) = d * (x : G) * d⁻¹ := by
  obtain ⟨k, hk⟩ := (MonoidHom.mem_range).mp kv.1.2
  have hWD : hyp.W ≤ hyp.D := le_trans inf_le_left hyp.V_le_D
  refine ⟨(k : G) * (kv.2 : G),
    hyp.D.mul_mem (hyp.K_le_D k.2) (hWD kv.2.2), fun x => ?_⟩
  rw [hyp.conjQHom_apply, MulAut.mul_apply]
  simp only [Subgroup.coe_subtype]
  rw [← hk]
  change (k : G) * ((kv.2 : G) * (x : G) * (kv.2 : G)⁻¹) * (k : G)⁻¹ = _
  group

/-- Two elements of `Q` with the same image in `Q/Z(Q)` differ by an element of `Q₀`.

Step 6 of the fibre translation: the quotient equality coming from `coord` is turned
into an honest product `z' = z · w` with `w ∈ Q₀`, which is what
`exists_conj_mul_Q0_iff` consumes. -/
theorem exists_mem_Q0_mul_of_quotient_eq
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q)
    (heq : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) : ↥hyp.Q ⧸ Subgroup.center hyp.Q)
      = QuotientGroup.mk ⟨z', hz'Q⟩) :
    ∃ w ∈ hyp.Q0, z' = z * w := by
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q)⁻¹ * ⟨z', hz'Q⟩ ∈ Subgroup.center hyp.Q :=
    QuotientGroup.eq.mp heq
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  refine ⟨z⁻¹ * z', hmem, by group⟩

/-- Steps 1–4 of the fibre translation: if the coordinates of `z, z' ∈ Q` lie in the
same coset of `μ(KW)` in `E^×`, then `z'` and a `KW`-translate of `z` agree in
`Q/Z(Q)`.

`coord_act` turns multiplication by `μ(kv)` in `E` into the action of `kv` on the
quotient, and `quotientKWHom_mk` re-expresses that action as `conjQHom`. -/
theorem exists_conjQHom_quotient_eq_of_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q) {u u' : M.Eˣ}
    (hu : (u : M.E) = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))))
    (hu' : (u' : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q))))
    (heq : (QuotientGroup.mk u : M.Eˣ ⧸ MonoidHom.range M.mu) = QuotientGroup.mk u') :
    ∃ kv, (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q) : ↥hyp.Q ⧸ Subgroup.center hyp.Q)
      = QuotientGroup.mk (hyp.conjQHom kv ⟨z, hzQ⟩) := by
  obtain ⟨kv, hkv⟩ := MonoidHom.mem_range.mp (QuotientGroup.eq.mp heq)
  refine ⟨kv, ?_⟩
  -- `u' = u * μ kv`, hence the same relation between the coordinates in `E`
  have hprod : u' = u * M.mu kv := by
    rw [hkv]
    group
  have hE : M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q)))
      = ((M.mu kv : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) := by
    rw [← hu, ← hu', hprod, Units.val_mul, mul_comm]
  -- `coord_act` identifies the right-hand side with the action of `kv`
  rw [← M.coord_act kv (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))] at hE
  have := M.coord.injective hE
  have h2 := Additive.ofMul.injective this
  rw [h2, hyp.quotientKWHom_mk]

/-- **The fibre translation** (step 7, assembling steps 1–6): if the coordinates of
`z, z' ∈ Q` lie in the same coset of `μ(KW)` in `E^×`, then

  `z' = (z · y)^a`  for some `y ∈ Q₀` and `a ∈ D`,

which is exactly the hypothesis shape of `ncard_le_card_V_of_f_eq_conj` and
`not_mem_K_of_f_eq_conj_self`. -/
theorem exists_conj_of_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q) {u u' : M.Eˣ}
    (hu : (u : M.E) = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))))
    (hu' : (u' : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q))))
    (heq : (QuotientGroup.mk u : M.Eˣ ⧸ MonoidHom.range M.mu) = QuotientGroup.mk u') :
    ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D, z' = a⁻¹ * (z * y) * a := by
  obtain ⟨kv, hkv⟩ :=
    hyp.exists_conjQHom_quotient_eq_of_coset_eq M hzQ hz'Q hu hu' heq
  obtain ⟨d, hd, hconj⟩ := hyp.exists_mem_D_conjQHom kv
  obtain ⟨w, hw, hzw⟩ := hyp.exists_mem_Q0_mul_of_quotient_eq hZ
    (hyp.conjQHom kv ⟨z, hzQ⟩).2 hz'Q hkv.symm
  rw [hconj ⟨z, hzQ⟩] at hzw
  refine hyp.exists_conj_mul_Q0_iff.mp ⟨d⁻¹, hyp.D.inv_mem hd, w, hw, ?_⟩
  rw [hzw]
  group

/-- **Each fibre of `orbitOfF` has at most `|V|` elements.**

If the fibre over `c` is nonempty, pick `x₀` in it and set `ω' = f(ω x₀)`.  For any
other `x` in the fibre, `exists_conj_of_coset_eq` gives `f(ω x) = (ω' y)^a`, so the
fibre embeds in the set bounded by `ncard_le_card_V_of_f_eq_conj`.

Under Chapter IV's `V = W` this is the book's `m_i ≤ m`. -/
theorem ncard_fiber_orbitOfF_le {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (c : M.Eˣ ⧸ (MonoidHom.range M.mu)) :
    {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
      ≤ Nat.card ↥hyp.V := by
  classical
  rcases Set.eq_empty_or_nonempty
      {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c} with he | ⟨x₀, hx₀⟩
  · rw [he, Set.ncard_empty]
    exact Nat.zero_le _
  · have hsub : ((↑) : ↥hyp.Q0 → G) ''
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}
        ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
            f (ω * z) = a⁻¹ * (f (ω * (x₀ : G)) * y) * a} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have hcoset :
          (QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x₀) :
            M.Eˣ ⧸ MonoidHom.range M.mu)
            = QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x) :=
        hx₀.trans hx.symm
      exact hyp.exists_conj_of_coset_eq M hZ
        (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x₀) (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x)
        rfl rfl hcoset
    calc {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
        = (((↑) : ↥hyp.Q0 → G) ''
            {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
            f (ω * z) = a⁻¹ * (f (ω * (x₀ : G)) * y) * a}.ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Nat.card ↥hyp.V := hyp.ncard_le_card_V_of_f_eq_conj H hC2 hωQ hωQ0

/-- The coordinate of `ω` itself as a unit of `E`; its coset is the distinguished
orbit `b₀` of step (8) (the book's `ω̄₁`). -/
noncomputable def baseUnit {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) : M.Eˣ :=
  Units.mk0 (M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))))
    (hyp.coord_ne_zero_of_not_mem_Q0 M hZ hωQ hωQ0)

@[simp] theorem baseUnit_val {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    ((hyp.baseUnit M hZ hωQ hωQ0 : M.Eˣ) : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := rfl

/-- **The distinguished fibre has at most `|V| − 1` elements** — the book's
`m₁ ≤ m − 1`.

Here no representative is needed: `ω` itself is the reference point, so
`exists_conj_of_coset_eq` applies with `z = ω` directly and the target set is the one
bounded by `ncard_le_card_V_sub_one_of_f_eq_conj_self`. -/
theorem ncard_fiber_orbitOfF_base_le {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
      ≤ Nat.card ↥hyp.V - 1 := by
  classical
  have hsub : ((↑) : ↥hyp.Q0 → G) ''
      {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}
      ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
          f (ω * z) = a⁻¹ * (ω * y) * a} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    exact hyp.exists_conj_of_coset_eq M hZ hωQ
      (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x) rfl rfl hx.symm
  calc {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
      = (((↑) : ↥hyp.Q0 → G) ''
          {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
            = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
          f (ω * z) = a⁻¹ * (ω * y) * a}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card ↥hyp.V - 1 :=
        hyp.ncard_le_card_V_sub_one_of_f_eq_conj_self H hC2 hωQ hωQ0

/-- **Peterfalvi Part II, Ch. IV §2, step (8)** (p. 124):

> The number of elements `x ∈ Q₀` such that `f(ω₁ x)‾` is in the orbit of `ω̄_i` under
> `KW` is `m` if `i > 1` and `m − 1` if `i = 1`.

All the inequalities are equalities: every fibre of `Φ = orbitOfF` other than the one
over `ω`'s own orbit has exactly `|W|` elements, and that distinguished fibre has
exactly `|W| − 1`.

The bounds are `ncard_fiber_orbitOfF_le` and `ncard_fiber_orbitOfF_base_le` (which
give `|V|`, equal to `|W|` under Chapter IV's `V = W`); the counting is
`card_fiber_eq_of_card_eq` with `|Q₀| = q` and `|E^× ⧸ μ(KW)| = (q + 1)/|W|`, so that
`q = ((q+1)/|W|) · |W| − 1`. -/
theorem stepEight {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    (∀ c, c ≠ QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0) →
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
          = Nat.card ↥hyp.W)
      ∧ {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
          = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
          = Nat.card ↥hyp.W - 1 := by
  have hβ : Nat.card (M.Eˣ ⧸ MonoidHom.range M.mu) = (2 ^ m + 1) / Nat.card ↥hyp.W := by
    rw [← Subgroup.index_eq_card, hyp.index_range_mu hm M hinj hK]
  have hcard : Nat.card ↥hyp.Q0
      = Nat.card (M.Eˣ ⧸ MonoidHom.range M.mu) * Nat.card ↥hyp.W - 1 := by
    rw [hβ, Nat.div_mul_cancel hWdvd, hQ0card]
    omega
  refine card_fiber_eq_of_card_eq (hyp.orbitOfF M hZ H hC2 hωQ hωQ0) Nat.card_pos _
    (fun c => ?_) ?_ hcard
  · have := hyp.ncard_fiber_orbitOfF_le M hZ H hC2 hωQ hωQ0 c
    rwa [hVW] at this
  · have := hyp.ncard_fiber_orbitOfF_base_le M hZ H hC2 hωQ hωQ0
    rwa [hVW] at this

/-- **The set-level count is exact**: `|S| = |W| − 1`, where

  `S = {z ∈ Q₀ | ∃ y ∈ Q₀, ∃ a ∈ D, f(ω z) = (ω y)^a}`.

`≤` is `ncard_le_card_V_sub_one_of_f_eq_conj_self`; `≥` comes from step (8), which
pins the distinguished fibre at exactly `|W| − 1` and whose image lies in `S`.

Exactness is what makes the coset map on `S` *surjective* onto the nontrivial cosets
of `K`, which is how step (9) produces its `kζ`. -/
theorem ncard_eq_card_W_sub_one_of_f_eq_conj_self {m : ℕ}
    (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
        f (ω * z) = a⁻¹ * (ω * y) * a}.ncard = Nat.card ↥hyp.W - 1 := by
  classical
  refine le_antisymm ?_ ?_
  · have hle := hyp.ncard_le_card_V_sub_one_of_f_eq_conj_self H hC2 hωQ hωQ0
    rwa [hVW] at hle
  · have hstep := (hyp.stepEight M hZ H hC2 hVW hm hQ0card hinj hK hWdvd hωQ hωQ0).2
    have hsub : ((↑) : ↥hyp.Q0 → G) ''
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
          = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}
        ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
            f (ω * z) = a⁻¹ * (ω * y) * a} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      exact hyp.exists_conj_of_coset_eq M hZ hωQ
        (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x) rfl rfl hx.symm
    calc Nat.card ↥hyp.W - 1
        = {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
            = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard := hstep.symm
      _ = (((↑) : ↥hyp.Q0 → G) ''
            {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
              = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **The witnesses realize every nontrivial coset of `K`.**

The coset map on `S` is injective (step (7)), avoids the identity coset
(`not_mem_K_of_f_eq_conj_self`), and `|S| = |W| − 1 = |D : K| − 1`
(`ncard_eq_card_W_sub_one_of_f_eq_conj_self`) — so its image is *all* of
`(D/K) ∖ {1}`.

This is what lets step (9) choose the witness with `a ∈ Kζ`: `ζ ≠ 1` by (C2). -/
theorem exists_witness_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {d : G} (hdD : d ∈ hyp.D) (hdK : d ∉ hyp.K) :
    ∃ z ∈ hyp.Q0, ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
      a⁻¹ * d ∈ hyp.K ∧ f (ω * z) = a⁻¹ * (ω * y) * a := by
  classical
  set S : Set G := {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
    f (ω * z) = a⁻¹ * (ω * y) * a} with hSdef
  have key : ∀ z ∈ S, ∃ a, a ∈ hyp.D ∧ ∃ b, b ∈ hyp.Q0 ∧
      f (ω * z) = a⁻¹ * (ω * b) * a := by
    rintro z ⟨-, b, hb, a, ha, heq⟩
    exact ⟨a, ha, b, hb, heq⟩
  choose! A hAD B hBQ0 hAeq using key
  set A' : G → ↥hyp.D := fun z => if hh : A z ∈ hyp.D then ⟨A z, hh⟩ else 1 with hA'def
  have hA'val : ∀ z ∈ S, (A' z : G) = A z := by
    intro z hz
    simp only [hA'def, dif_pos (hAD z hz)]
  set Ψ : G → ↥hyp.D ⧸ hyp.K.subgroupOf hyp.D := fun z => QuotientGroup.mk (A' z)
    with hΨdef
  have hinjOn : Set.InjOn Ψ S := by
    intro z₁ hz₁ z₂ hz₂ hzz
    have hmem : (A' z₁)⁻¹ * A' z₂ ∈ hyp.K.subgroupOf hyp.D := QuotientGroup.eq.mp hzz
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : (A z₁)⁻¹ * A z₂ ∈ hyp.K := by
      have e : (((A' z₁)⁻¹ * A' z₂ : ↥hyp.D) : G) = (A z₁)⁻¹ * A z₂ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hA'val z₁ hz₁, hA'val z₂ hz₂]
      rwa [e] at hmem
    exact hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hz₁.1 hz₂.1
      (hBQ0 z₁ hz₁) (hBQ0 z₂ hz₂) (hAD z₁ hz₁) (hAD z₂ hz₂)
      (hAeq z₁ hz₁) (hAeq z₂ hz₂) hmem'
  have hmaps : Ψ '' S ⊆ (Set.univ \ {1} : Set (↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨Set.mem_univ _, fun hc => ?_⟩
    have hone : A' z ∈ hyp.K.subgroupOf hyp.D := (QuotientGroup.eq_one_iff (A' z)).mp hc
    rw [Subgroup.mem_subgroupOf, hA'val z hz] at hone
    exact hyp.not_mem_K_of_f_eq_conj_self H hC2 hωQ hωQ0 hz.1 (hBQ0 z hz)
      (hAD z hz) (hAeq z hz) hone
  have hScard := hyp.ncard_eq_card_W_sub_one_of_f_eq_conj_self M hZ H hC2 hVW hm
    hQ0card hinj hKcard hWdvd hωQ hωQ0
  have hdiff : (Set.univ \ {1} : Set (↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)).ncard
      = Nat.card ↥hyp.W - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      ← Subgroup.index_eq_card, hyp.index_K_subgroupOf_D, hVW]
  have heq : Ψ '' S = (Set.univ \ {1} : Set (↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)) :=
    Set.eq_of_subset_of_ncard_le hmaps
      (by rw [hinjOn.ncard_image, hScard, hdiff]) (Set.toFinite _)
  have hdne : (QuotientGroup.mk (⟨d, hdD⟩ : ↥hyp.D) :
      ↥hyp.D ⧸ hyp.K.subgroupOf hyp.D) ≠ 1 := by
    intro hc
    have hmm := (QuotientGroup.eq_one_iff (⟨d, hdD⟩ : ↥hyp.D)).mp hc
    rw [Subgroup.mem_subgroupOf] at hmm
    exact hdK hmm
  obtain ⟨z, hz, hzd⟩ : (QuotientGroup.mk (⟨d, hdD⟩ : ↥hyp.D)) ∈ Ψ '' S := by
    rw [heq]
    exact ⟨Set.mem_univ _, hdne⟩
  refine ⟨z, hz.1, B z, hBQ0 z hz, A z, hAD z hz, ?_, hAeq z hz⟩
  have hmm := QuotientGroup.eq.mp hzd
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hA'val z hz] at hmm
  exact hmm

/-- **Peterfalvi Part II, Ch. IV §2, step (9)** (p. 124–125):

> For all `i`, there are elements `ω'_i ∈ Q − Q₀` and `y_i ∈ Q₀^#` such that `ω̄'_i` is
> in the orbit of `ω̄_i` under `KW` and `f(ω'_i) = (ω'_i y_i)^ζ`.

Here `ζ` is any nontrivial element of `W` (the book takes a generator, nontrivial by
(C2)).  The witness for the coset `ζK` exists by `exists_witness_coset_eq`, its
`K`-part has a square root by `exists_sq_eq_of_mem_K`, and `f_conj_collapse` turns the
exponent into `ζ`. -/
theorem stepNine {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) :
    ∃ ω' ∈ hyp.Q, ω' ∉ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, y ≠ 1 ∧
      f ω' = ζ⁻¹ * (ω' * y) * ζ := by
  have hWD : hyp.W ≤ hyp.D := le_trans inf_le_left hyp.V_le_D
  have hζD : ζ ∈ hyp.D := hWD hζW
  have hζK : ζ ∉ hyp.K := by
    intro hc
    refine hζ1 ?_
    have : ζ ∈ hyp.K ⊓ hyp.W := ⟨hc, hζW⟩
    rwa [hyp.K_inf_W_eq_bot, Subgroup.mem_bot] at this
  obtain ⟨z, hzQ0, b, hbQ0, a, haD, haζ, heq⟩ :=
    hyp.exists_witness_coset_eq M hZ H hC2 hVW hm hQ0card hinj hKcard hWdvd
      hωQ hωQ0 hζD hζK
  -- `a = k ζ` with `k ∈ K`, using that `W` centralizes `K`
  have hkK : ζ⁻¹ * a ∈ hyp.K := by
    have := hyp.K.inv_mem haζ
    simpa using this
  obtain ⟨c, hcK, hcsq⟩ := hyp.exists_sq_eq_of_mem_K hkK
  have hcKSet : c ∈ hyp.KSet := by
    have hh : c ∈ (hyp.K : Set G) := hcK
    rwa [hyp.coe_K] at hh
  have haeq : a = c ^ 2 * ζ := by
    rw [hcsq]
    have hcm : ζ * (ζ⁻¹ * a) = a := by group
    rw [← hyp.commute_of_mem_W_of_mem_K hζW hkK] at hcm
    exact hcm.symm
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
  have hωz1 : ω * z ≠ 1 := fun hc => hωzQ0 (hc ▸ hyp.Q0.one_mem)
  rw [haeq] at heq
  have hcoll := hyp.f_conj_collapse H hωzQ hωz1 hzQ0 hcKSet hζW heq
  -- package the result
  have hcD : c ∈ hyp.D := hyp.K_le_D hcK
  have hω'Q : c⁻¹ * (ω * z) * c ∈ hyp.Q := hyp.rankOneSetup.DQ c hcD _ hωzQ
  have hω'Q0 : c⁻¹ * (ω * z) * c ∉ hyp.Q0 := by
    intro hcc
    refine hωzQ0 ?_
    have e : ω * z = c * (c⁻¹ * (ω * z) * c) * c⁻¹ := by group
    rw [e]
    exact hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hcD) hcc
  have hyQ0 : c⁻¹ * (z * b) * c ∈ hyp.Q0 := by
    have := hyp.conj_mem_Q0_of_mem_H (hyp.H.inv_mem (hyp.D_le_H hcD))
      (hyp.Q0.mul_mem hzQ0 hbQ0)
    rwa [inv_inv] at this
  refine ⟨_, hω'Q, hω'Q0, _, hyQ0, ?_, hcoll⟩
  exact hyp.ne_one_of_f_eq_conj H hC2 hω'Q hω'Q0 hζD hcoll

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
