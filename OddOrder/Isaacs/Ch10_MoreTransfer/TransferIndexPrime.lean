/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer

/-!
# Isaacs §10A — transfer evaluation on a normal subgroup of prime index (pp. 300-301)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10 "More Transfer
Theory", §10A 中盤: 指数 `p` の正規部分群への pretransfer の明示計算。

* **Lemma 10.6**: `M ⊴ P`, `|P : M| = p`, `V : P → M` pretransfer のとき
  (a) `x ∈ M` なら `V(x) ≡ ∏_{t ∈ T} xᵗ mod M'` (`T` は任意の transversal),
  (b) `x ∉ M` なら `V(x) ≡ x^p mod M'`。

## Lean 化の方針

Isaacs の「pretransfer `V` mod `M'`」は mathlib の transfer 準同型
`MonoidHom.transfer ϕ : G →* A` (`ϕ : ↥M →* A`, `A` 可換) で表す —
可換 target への `ϕ` は `M` の交換子を殺すので、これが「mod M'」の内容。
`A = Abelianization ↥M`, `ϕ = Abelianization.of` が Isaacs の文字通りの形。

**一般化** (Isaacs は p-群で述べるが証明はそれを使わない):
`G` は任意の群、`M ⊴ G` は指数が素数 `p` の正規部分群でよい
((a) は指数有限の正規部分群で成立)。

* `transfer_eq_prod_conj_of_mem` (10.6(a)): `x ∈ M` のとき
  `transfer ϕ x = ∏_{q : G ⧸ M} ϕ ((f q)⁻¹ x (f q))` — `f` は任意の section
  (transversal)。mathlib の軌道分解
  `transfer_eq_prod_quotient_orbitRel_zpowers_quot` で `x` の作用が自明ゆえ
  軌道が全て singleton になることから従う。
* `transfer_eq_pow_of_notMem` (10.6(b)): `x ∉ M` のとき
  `transfer ϕ x = ϕ (x^p)` — `x̄` が `G ⧸ M` (位数 `p`) を生成するので
  軌道は単一 (`minimalPeriod = p`)、代表元による共役差は `M`-共役に直せて
  `ϕ` で消える。
-/

namespace OddOrder.Isaacs.Ch10

open MulAction Subgroup Function

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]
variable {A : Type*} [CommGroup A]

section /- 10A: Lemma 10.6 (pp. 300-301) -/

/-- A homomorphism from `M` to a commutative group is invariant under conjugation
by elements of `M`: `ϕ (m⁻¹ y m) = ϕ y`. (This is what "computing mod `M'`"
means; used to replace one coset representative by another.) -/
private lemma phi_conj_eq {M : Subgroup G} (ϕ : ↥M →* A)
    {y : G} (hy : y ∈ M) {m : G} (hm : m ∈ M)
    (hmem : m⁻¹ * y * m ∈ M) :
    ϕ ⟨m⁻¹ * y * m, hmem⟩ = ϕ ⟨y, hy⟩ := by
  have h1 : (⟨m⁻¹ * y * m, hmem⟩ : ↥M) = ⟨m, hm⟩⁻¹ * ⟨y, hy⟩ * ⟨m, hm⟩ := by
    ext
    rfl
  rw [h1, map_mul, map_mul, map_inv]
  exact inv_mul_cancel_comm _ _

/-- Two representatives of the same coset of `M` conjugate `y ∈ M` to
`ϕ`-equal values. -/
private lemma phi_conj_rep_eq {M : Subgroup G} [M.Normal] (ϕ : ↥M →* A)
    {y : G} (hy : y ∈ M) {r s : G} (hrs : (r : G ⧸ M) = (s : G ⧸ M)) :
    ϕ ⟨r⁻¹ * y * r, ‹M.Normal›.conj_mem' y hy r⟩
      = ϕ ⟨s⁻¹ * y * s, ‹M.Normal›.conj_mem' y hy s⟩ := by
  -- m := s⁻¹ * r ∈ M and r = s * m
  have hm : s⁻¹ * r ∈ M := by
    rw [← QuotientGroup.eq]
    exact hrs.symm
  have hconj : r⁻¹ * y * r = (s⁻¹ * r)⁻¹ * (s⁻¹ * y * s) * (s⁻¹ * r) := by
    group
  calc ϕ ⟨r⁻¹ * y * r, ‹M.Normal›.conj_mem' y hy r⟩
      = ϕ ⟨(s⁻¹ * r)⁻¹ * (s⁻¹ * y * s) * (s⁻¹ * r), by
          rw [← hconj]; exact ‹M.Normal›.conj_mem' y hy r⟩ := by
        exact congrArg ϕ (Subtype.ext hconj)
    _ = ϕ ⟨s⁻¹ * y * s, ‹M.Normal›.conj_mem' y hy s⟩ :=
        phi_conj_eq ϕ (‹M.Normal›.conj_mem' y hy s) hm _

/-- **Isaacs Lemma 10.6(a)** (generalized): let `M ⊴ G` with `G ⧸ M` finite, let
`ϕ : M →* A` with `A` commutative, and let `f` be any section (transversal) of
`G ⧸ M`. For `x ∈ M`,
`transfer ϕ x = ∏_{q : G ⧸ M} ϕ ((f q)⁻¹ · x · f q)`.

(For `ϕ = Abelianization.of` this is Isaacs' `V(x) ≡ ∏_{t ∈ T} xᵗ mod M'`;
Isaacs states it for `p`-groups but only normality and finite index are used.) -/
theorem transfer_eq_prod_conj_of_mem {M : Subgroup G} [M.Normal] [Fintype (G ⧸ M)]
    (ϕ : ↥M →* A) {x : G} (hx : x ∈ M)
    (f : G ⧸ M → G) (hf : ∀ q, ((f q : G) : G ⧸ M) = q) :
    haveI : M.FiniteIndex := M.finiteIndex_of_finite_quotient
    MonoidHom.transfer ϕ x
      = ∏ q : G ⧸ M, ϕ ⟨(f q)⁻¹ * x * f q, ‹M.Normal›.conj_mem' x hx (f q)⟩ := by
  haveI : M.FiniteIndex := M.finiteIndex_of_finite_quotient
  classical
  -- powers of x act trivially on G ⧸ M (x ∈ M, M normal)
  have htriv : ∀ (k : ℤ) (q : G ⧸ M), (x ^ k : G) • q = q := by
    intro k q
    induction q using QuotientGroup.induction_on with
    | H y =>
      show ((x ^ k * y : G) : G ⧸ M) = (y : G ⧸ M)
      rw [QuotientGroup.eq]
      have h1 : (x ^ k * y)⁻¹ * y = y⁻¹ * (x ^ k)⁻¹ * y := by group
      rw [h1]
      exact ‹M.Normal›.conj_mem' _ (M.inv_mem (M.zpow_mem hx k)) y
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  -- all ⟨x⟩-orbits on G ⧸ M are singletons
  have horbit : ∀ c : G ⧸ M, orbit (zpowers x) c = {c} := by
    intro c
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_orbit_self c, ?_⟩
    rintro d ⟨⟨u, hu⟩, rfl⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hu
    exact htriv k c
  have hbij : Function.Bijective
      (Quotient.mk (orbitRel (zpowers x) (G ⧸ M))) := by
    constructor
    · intro c d hcd
      have h1 : c ∈ orbit (zpowers x) d := orbitRel_apply.mp (Quotient.exact hcd)
      rw [horbit d] at h1
      exact h1
    · exact Quotient.mk_surjective
  refine (Fintype.prod_bijective _ hbij _ _ (fun c => ?_)).symm
  -- factor at ⟦c⟧: the orbit representative is c itself, minimal period 1
  have hout : (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out = c := by
    have h1 : (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out
        ∈ orbit (zpowers x) c :=
      orbitRel_apply.mp (Quotient.exact (Quotient.out_eq _))
    rw [horbit c] at h1
    exact h1
  have hper : Function.minimalPeriod (x • ·)
      ((Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out) = 1 := by
    rw [hout]
    have h1 : x • c = c := by simpa using htriv 1 c
    exact Function.minimalPeriod_eq_one_iff_isFixedPt.mpr h1
  have hrep : (((Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out.out : G) : G ⧸ M)
      = ((f c : G) : G ⧸ M) := by
    rw [hf c, QuotientGroup.out_eq', hout]
  calc ϕ ⟨(f c)⁻¹ * x * f c, ‹M.Normal›.conj_mem' x hx (f c)⟩
      = ϕ ⟨((Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out.out)⁻¹ * x
            * (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out.out,
          ‹M.Normal›.conj_mem' x hx _⟩ :=
        phi_conj_rep_eq ϕ hx hrep.symm
    _ = _ := by
        refine congrArg ϕ (Subtype.ext ?_)
        show _ = _ * x ^ Function.minimalPeriod (x • ·)
            (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) c).out * _
        rw [hper, pow_one]

/-- **Isaacs Lemma 10.6(b)** (generalized): let `M ⊴ G` of prime index `p` and
`ϕ : M →* A` with `A` commutative. For `x ∉ M`,
`transfer ϕ x = ϕ (x^p)`.

(For `ϕ = Abelianization.of` this is Isaacs' `V(x) ≡ x^p mod M'`; Isaacs states
it for `p`-groups but only `|G : M| = p` prime is used: `x̄` generates the
quotient, so there is a single `⟨x⟩`-orbit on `G ⧸ M`, and the coset
representative conjugating `x^p` can be normalized to an `M`-conjugation.) -/
theorem transfer_eq_pow_of_notMem {M : Subgroup G} [M.Normal] [M.FiniteIndex]
    (hidx : M.index = p) (ϕ : ↥M →* A) {x : G} (hx : x ∉ M) :
    MonoidHom.transfer ϕ x = ϕ ⟨x ^ p, hidx ▸ M.pow_index_mem x⟩ := by
  classical
  have hp_prime : p.Prime := hp.out
  haveI : Fintype (G ⧸ M) := Fintype.ofFinite _
  have hQcard : Nat.card (G ⧸ M) = p := by rw [← Subgroup.index_eq_card, hidx]
  -- x̄ has order p and generates G ⧸ M
  have hxbar_ne : ((x : G) : G ⧸ M) ≠ 1 := by
    simpa [QuotientGroup.eq_one_iff] using hx
  have horder : orderOf ((x : G) : G ⧸ M) = p := by
    have hdvd : orderOf ((x : G) : G ⧸ M) ∣ p := by
      rw [← hQcard]; exact orderOf_dvd_natCard _
    rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hxbar_ne
    · exact h
  have htop : Subgroup.zpowers ((x : G) : G ⧸ M) = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horder, hQcard]
  -- the ⟨x⟩-action on G ⧸ M is left multiplication by x̄
  have hsmul : ∀ (k : ℤ) (c : G ⧸ M), (x ^ k : G) • c = ((x : G) : G ⧸ M) ^ k * c := by
    intro k c
    induction c using QuotientGroup.induction_on with
    | H y =>
      show ((x ^ k * y : G) : G ⧸ M) = _
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow]
  -- every point has minimal period p under x • ·
  have hper : ∀ c : G ⧸ M, Function.minimalPeriod (x • ·) c = p := by
    intro c
    have hdvd : Function.minimalPeriod (x • ·) c ∣ p := by
      apply Function.IsPeriodicPt.minimalPeriod_dvd
      show (x • ·)^[p] c = c
      rw [smul_iterate_apply]
      have := hsmul (p : ℤ) c
      rw [zpow_natCast, zpow_natCast] at this
      rw [this, ← horder, pow_orderOf_eq_one, one_mul]
    rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h
    · exfalso
      have hfix := Function.isPeriodicPt_minimalPeriod (x • ·) c
      rw [h1] at hfix
      have hxc : x • c = c := hfix
      have : ((x : G) : G ⧸ M) * c = c := by
        have := hsmul 1 c
        rw [zpow_one, zpow_one] at this
        rw [← this]
        exact hxc
      exact hxbar_ne (by
        have h2 : ((x : G) : G ⧸ M) * c = 1 * c := by rw [this, one_mul]
        exact mul_right_cancel h2)
    · exact h
  -- there is a single orbit
  haveI hsub : Subsingleton (Quotient (orbitRel (zpowers x) (G ⧸ M))) := by
    constructor
    intro a b
    induction a using Quotient.inductionOn with | h c =>
    induction b using Quotient.inductionOn with | h d =>
    apply Quotient.sound
    have hmem : c * d⁻¹ ∈ Subgroup.zpowers ((x : G) : G ⧸ M) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine orbitRel_apply.mpr ⟨⟨x ^ k, Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k⟩, ?_⟩
    show (x ^ k : G) • d = c
    rw [hsmul k d, hk]
    group
  -- collapse the product to the single factor and normalize it
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [Fintype.prod_subsingleton _ (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) 1)]
  set r : G := (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) 1).out.out with hr_def
  -- exponent is p
  have hexp : ϕ ⟨r⁻¹ * x ^ Function.minimalPeriod (x • ·)
        (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) 1).out * r,
        QuotientGroup.out_conj_pow_minimalPeriod_mem M x _⟩
      = ϕ ⟨r⁻¹ * x ^ p * r, by
          have h1 := QuotientGroup.out_conj_pow_minimalPeriod_mem M x
            (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) 1).out
          rwa [hper] at h1⟩ := by
    refine congrArg ϕ (Subtype.ext ?_)
    show r⁻¹ * x ^ Function.minimalPeriod (x • ·)
        (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) 1).out * r
      = r⁻¹ * x ^ p * r
    rw [hper]
  rw [hexp]
  -- normalize the conjugating representative into M
  have hrbar : ∃ k : ℤ, ((x : G) : G ⧸ M) ^ k = ((r : G) : G ⧸ M) := by
    have : ((r : G) : G ⧸ M) ∈ Subgroup.zpowers ((x : G) : G ⧸ M) :=
      htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_zpowers_iff.mp this
  obtain ⟨k, hk⟩ := hrbar
  have hmM : (x ^ k)⁻¹ * r ∈ M := by
    rw [← QuotientGroup.eq]
    rw [QuotientGroup.mk_zpow]
    exact hk
  have hxpM : x ^ p ∈ M := hidx ▸ M.pow_index_mem x
  have hconj : r⁻¹ * x ^ p * r
      = ((x ^ k)⁻¹ * r)⁻¹ * x ^ p * ((x ^ k)⁻¹ * r) := by
    have hcomm : (x ^ k)⁻¹ * x ^ p * x ^ k = x ^ p := by group
    calc r⁻¹ * x ^ p * r
        = r⁻¹ * ((x ^ k) * ((x ^ k)⁻¹ * x ^ p * x ^ k) * (x ^ k)⁻¹) * r := by
          rw [hcomm]; group
      _ = ((x ^ k)⁻¹ * r)⁻¹ * x ^ p * ((x ^ k)⁻¹ * r) := by
          rw [hcomm]; group
  calc ϕ ⟨r⁻¹ * x ^ p * r, _⟩
      = ϕ ⟨((x ^ k)⁻¹ * r)⁻¹ * x ^ p * ((x ^ k)⁻¹ * r), by
          rw [← hconj]
          have h1 := QuotientGroup.out_conj_pow_minimalPeriod_mem M x
            (Quotient.mk (orbitRel (zpowers x) (G ⧸ M)) 1).out
          rwa [hper] at h1⟩ := congrArg ϕ (Subtype.ext hconj)
    _ = ϕ ⟨x ^ p, hxpM⟩ := phi_conj_eq ϕ hxpM hmM _
    _ = ϕ ⟨x ^ p, hidx ▸ M.pow_index_mem x⟩ := rfl

end

end OddOrder.Isaacs.Ch10
