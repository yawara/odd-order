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
theorem card_fiber_eq_of_card_eq {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (Φ : α → β) {M : ℕ} (hM : 1 ≤ M) (b₀ : β)
    (hle : ∀ b, (Finset.univ.filter fun a => Φ a = b).card ≤ M)
    (hb₀ : (Finset.univ.filter fun a => Φ a = b₀).card ≤ M - 1)
    (hcard : Fintype.card α = Fintype.card β * M - 1) :
    ∀ b, (Finset.univ.filter fun a => Φ a = b).card = if b = b₀ then M - 1 else M := by
  classical
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
  exact fun b => (Finset.sum_eq_sum_iff_of_le hpt).mp heq b (Finset.mem_univ b)

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

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
