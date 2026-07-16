/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Transfer
import OddOrder.Isaacs.Ch10_MoreTransfer.WreathRecognition

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

/-- The image of `u ∉ M` in `G ⧸ M` (index `p` prime) has order `p`. -/
private lemma orderOf_mk_eq_prime {M : Subgroup G} [M.Normal] (hidx : M.index = p)
    {u : G} (hu : u ∉ M) : orderOf ((u : G) : G ⧸ M) = p := by
  have hp_prime : p.Prime := hp.out
  have hQcard : Nat.card (G ⧸ M) = p := by rw [← Subgroup.index_eq_card, hidx]
  have hne : ((u : G) : G ⧸ M) ≠ 1 := by simpa [QuotientGroup.eq_one_iff] using hu
  have hdvd : orderOf ((u : G) : G ⧸ M) ∣ p := by
    rw [← hQcard]; exact orderOf_dvd_natCard _
  rcases hp_prime.eq_one_or_self_of_dvd _ hdvd with h1 | h
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h

/-- For `u ∉ M` (index `p` prime): `u ^ k ∈ M ↔ p ∣ k`. -/
private lemma pow_mem_iff_dvd_of_index_prime {M : Subgroup G} [M.Normal]
    (hidx : M.index = p) {u : G} (hu : u ∉ M) (k : ℕ) :
    u ^ k ∈ M ↔ p ∣ k := by
  rw [← QuotientGroup.eq_one_iff (u ^ k), QuotientGroup.mk_pow,
    ← orderOf_dvd_iff_pow_eq_one, orderOf_mk_eq_prime hidx hu]

/-- **Isaacs Lemma 10.6(a), power-transversal form**: for `M ⊴ G` of prime index
`p`, `x ∈ M` and `u ∉ M`,
`transfer ϕ x = ∏_{i<p} ϕ (uⁱ x u⁻ⁱ)` —
the transversal `{u⁻ⁱ}` enumerates the cosets of `M`, and conjugation by it
produces `x^{uⁱ} = uⁱ x u⁻ⁱ`. (The form consumed by Lemma 10.7 / Thm 10.9.) -/
theorem transfer_eq_prod_pow_conj_of_mem {M : Subgroup G} [M.Normal] [M.FiniteIndex]
    (hidx : M.index = p) (ϕ : ↥M →* A) {x : G} (hx : x ∈ M) {u : G} (hu : u ∉ M) :
    MonoidHom.transfer ϕ x
      = ∏ i ∈ Finset.range p, ϕ ⟨u ^ i * x * (u ^ i)⁻¹, ‹M.Normal›.conj_mem x hx _⟩ := by
  classical
  have hp_prime : p.Prime := hp.out
  haveI : Fintype (G ⧸ M) := Fintype.ofFinite _
  have hQcard : Nat.card (G ⧸ M) = p := by rw [← Subgroup.index_eq_card, hidx]
  have hcardF : Fintype.card (G ⧸ M) = p := by
    rw [← Nat.card_eq_fintype_card, hQcard]
  -- the enumeration i ↦ ⟦(uⁱ)⁻¹⟧ of the cosets is bijective
  have hs : ∀ i : ℕ, u ^ i * x * (u ^ i)⁻¹ = ((u ^ i)⁻¹)⁻¹ * x * (u ^ i)⁻¹ := by
    intro i; group
  have he_inj : Function.Injective
      (fun i : Fin p => (((u ^ (i : ℕ))⁻¹ : G) : G ⧸ M)) := by
    intro i j hij
    have h1 : ((u ^ (i : ℕ) : G) : G ⧸ M) = ((u ^ (j : ℕ) : G) : G ⧸ M) := by
      have := congrArg (·⁻¹) hij
      simpa using this
    rw [QuotientGroup.eq] at h1
    -- (uⁱ)⁻¹ uʲ ∈ M forces p ∣ j - i in both orders
    rcases le_total (i : ℕ) (j : ℕ) with hle | hle
    · have h2 : u ^ ((j : ℕ) - (i : ℕ)) ∈ M := by
        have h3 : (u ^ (i : ℕ))⁻¹ * u ^ (j : ℕ) = u ^ ((j : ℕ) - (i : ℕ)) := by
          rw [show u ^ (j : ℕ) = u ^ ((j : ℕ) - (i : ℕ)) * u ^ (i : ℕ) by
            rw [← pow_add, Nat.sub_add_cancel hle]]
          group
        rwa [h3] at h1
      have h4 := (pow_mem_iff_dvd_of_index_prime hidx hu _).mp h2
      have h5 : (j : ℕ) - (i : ℕ) < p := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
      have h6 : (j : ℕ) - (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt h4 h5
      exact Fin.ext (by omega)
    · have h2 : u ^ ((i : ℕ) - (j : ℕ)) ∈ M := by
        have h3 : (u ^ (j : ℕ))⁻¹ * u ^ (i : ℕ) = u ^ ((i : ℕ) - (j : ℕ)) := by
          rw [show u ^ (i : ℕ) = u ^ ((i : ℕ) - (j : ℕ)) * u ^ (j : ℕ) by
            rw [← pow_add, Nat.sub_add_cancel hle]]
          group
        have h1' : (u ^ (j : ℕ))⁻¹ * u ^ (i : ℕ) ∈ M := by
          have := M.inv_mem h1
          simpa [mul_assoc] using this
        rwa [h3] at h1'
      have h4 := (pow_mem_iff_dvd_of_index_prime hidx hu _).mp h2
      have h5 : (i : ℕ) - (j : ℕ) < p := lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
      have h6 : (i : ℕ) - (j : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt h4 h5
      exact Fin.ext (by omega)
  have he_bij : Function.Bijective
      (fun i : Fin p => (((u ^ (i : ℕ))⁻¹ : G) : G ⧸ M)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨he_inj, by rw [Fintype.card_fin, hcardF]⟩
  -- evaluate via 10.6(a) with the canonical section, then reindex
  rw [transfer_eq_prod_conj_of_mem ϕ hx (fun q => q.out)
    (fun q => QuotientGroup.out_eq' q)]
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => ϕ ⟨u ^ i * x * (u ^ i)⁻¹, ‹M.Normal›.conj_mem x hx _⟩)]
  refine (Fintype.prod_bijective _ he_bij _ _ (fun i => ?_)).symm
  -- factor at i: the canonical representative of ⟦(uⁱ)⁻¹⟧ conjugates like (uⁱ)⁻¹
  have hrep : (((((u ^ (i : ℕ))⁻¹ : G) : G ⧸ M)).out : G ⧸ M)
      = (((u ^ (i : ℕ))⁻¹ : G) : G ⧸ M) := QuotientGroup.out_eq' _
  calc ϕ ⟨u ^ (i : ℕ) * x * (u ^ (i : ℕ))⁻¹, ‹M.Normal›.conj_mem x hx _⟩
      = ϕ ⟨((u ^ (i : ℕ))⁻¹)⁻¹ * x * (u ^ (i : ℕ))⁻¹,
          ‹M.Normal›.conj_mem' x hx _⟩ := congrArg ϕ (Subtype.ext (hs i))
    _ = ϕ ⟨((((u ^ (i : ℕ))⁻¹ : G) : G ⧸ M)).out⁻¹ * x
          * ((((u ^ (i : ℕ))⁻¹ : G) : G ⧸ M)).out,
          ‹M.Normal›.conj_mem' x hx _⟩ := phi_conj_rep_eq ϕ hx hrep.symm

end

section /- 10A: Lemma 10.7 (p. 301) -/

open OddOrder.GroupTheory
open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P]

/-- A characteristic subgroup of a normal subgroup, pushed into the ambient
group, is normal. (Local copy of
`OddOrder.BG.Ch3.normal_map_subtype_of_characteristic` — the BG leaf is
downstream of Isaacs, so it cannot be imported here; candidate for
consolidation into `OddOrder/GroupTheory/`.) -/
private lemma normal_map_subtype_of_char {W : Type*} [Group W] {N : Subgroup W}
    [N.Normal] {L : Subgroup ↥N} (hL : L.Characteristic) :
    (L.map N.subtype).Normal := by
  refine ⟨fun a ha w => ?_⟩
  obtain ⟨⟨a', ha'N⟩, ha'L, rfl⟩ := ha
  have hmap : L.map (MulAut.conjNormal w).toMonoidHom = L :=
    (Subgroup.characteristic_iff_map_eq.mp hL) (MulAut.conjNormal w)
  have hmem : (MulAut.conjNormal w) ⟨a', ha'N⟩ ∈ L := by
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ ha'L
  exact ⟨(MulAut.conjNormal w) ⟨a', ha'N⟩, hmem, MulAut.conjNormal_apply w ⟨a', ha'N⟩⟩

/-- **Isaacs Lemma 10.7**: let `P` be a finite `p`-group, `M ⊴ P` of index `p`,
and let `V = transfer (Abelianization.of)` be the transfer `P →* M^{ab}`. If
`V x` lies outside the image of `Φ(M)` for some `x ∈ M`, then `C_p ≀ C_p` is a
homomorphic image of `P`.

**証明** (Isaacs p.301): `N := Φ(M)` (`M ⊴ P` の特性部分群ゆえ `P` で正規) で割る。
`M̄ = M/Φ(M)` は elementary abelian (`M' ≤ Φ(M)`, `m^p ∈ Φ(M)`)。10.6(a) の冪
transversal 形で `V x = ∏_{i<p} (x^{uⁱ})` の像、よって `x̄` の共役積 ≠ 1。共役が
全て等しければ積は `x̄^p = 1` になるので `x̄` は `P̄` で非中心。Cor 10.5 (列挙形)
を `P̄` に適用して `C_p ≀ C_p ↞ P̄ ↞ P`。 -/
theorem exists_surjective_wreath_of_transfer_notMem_frattini
    (hP : IsPGroup p P) {M : Subgroup P} [M.Normal] (hidx : M.index = p)
    {x : P} (hx : x ∈ M)
    (hV : MonoidHom.transfer (Abelianization.of (G := ↥M)) x
      ∉ (frattini ↥M).map (Abelianization.of (G := ↥M))) :
    ∃ φ : P →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)),
      Function.Surjective φ := by
  classical
  have hp_prime : p.Prime := hp.out
  have hM_pgroup : IsPGroup p ↥M := hP.to_subgroup M
  -- N := Φ(M) as a (normal) subgroup of P
  set N : Subgroup P := (frattini ↥M).map M.subtype with hN_def
  haveI hN_normal : N.Normal := normal_map_subtype_of_char inferInstance
  have hNM : N ≤ M := Subgroup.map_subtype_le _
  set π : P →* P ⧸ N := QuotientGroup.mk' N with hπ_def
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hkerπ : π.ker = N := QuotientGroup.ker_mk' N
  -- u outside M
  obtain ⟨u, hu⟩ := exists_notMem_of_index_prime hidx
  -- the ordered class product L, its ↥M-lift, and V x = of L
  have hLmem : ∀ i : ℕ, u ^ i * x * (u ^ i)⁻¹ ∈ M :=
    fun i => ‹M.Normal›.conj_mem x hx _
  set L : P := ((List.range p).map (fun i => u ^ i * x * (u ^ i)⁻¹)).prod with hL_def
  have hLM : L ∈ M := by
    rw [hL_def]
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact hLmem i
  have hVx : MonoidHom.transfer (Abelianization.of (G := ↥M)) x
      = Abelianization.of ⟨L, hLM⟩ := by
    rw [transfer_eq_prod_pow_conj_of_mem hidx _ hx hu]
    set Lhat : ℕ → ↥M := fun i => ⟨u ^ i * x * (u ^ i)⁻¹, hLmem i⟩ with hLhat_def
    have h2 : ((((List.range p).map Lhat).prod : ↥M) : P)
        = ((List.range p).map (M.subtype ∘ Lhat)).prod := by
      rw [← List.map_map]
      exact map_list_prod M.subtype _
    have h1 : (⟨L, hLM⟩ : ↥M) = ((List.range p).map Lhat).prod := by
      apply Subtype.ext
      show L = ((((List.range p).map Lhat).prod : ↥M) : P)
      rw [hL_def, h2]
      rfl
    rw [h1, map_list_prod, List.map_map, Finset.prod_eq_multiset_prod]
    rfl
  -- L is not in N = Φ(M)
  have hLN : L ∉ N := by
    intro hLn
    apply hV
    have h2 : (⟨L, hLM⟩ : ↥M) ∈ frattini ↥M := by
      obtain ⟨w, hw, hww⟩ := Subgroup.mem_map.mp hLn
      have h3 : w = ⟨L, hLM⟩ := Subtype.ext hww
      rwa [h3] at hw
    rw [hVx]
    exact Subgroup.mem_map_of_mem _ h2
  have hπL : π L ≠ 1 := fun h1 => hLN (by rw [← hkerπ]; exact π.mem_ker.mpr h1)
  -- quotient-level data for Cor 10.5
  haveI : (M.map π).Normal := Subgroup.Normal.map ‹M.Normal› π hπsurj
  have hidx' : (M.map π).index = p := by
    rw [M.index_map_eq hπsurj (by rw [hkerπ]; exact hNM), hidx]
  have hEA' : (M.map π).IsElementaryAbelian p := by
    constructor
    · rintro ⟨y1, hy1⟩ ⟨y2, hy2⟩
      obtain ⟨m1, hm1, rfl⟩ := Subgroup.mem_map.mp hy1
      obtain ⟨m2, hm2, rfl⟩ := Subgroup.mem_map.mp hy2
      refine Subtype.ext ?_
      show π m1 * π m2 = π m2 * π m1
      rw [← map_mul, ← map_mul]
      show ((m1 * m2 : P) : P ⧸ N) = ((m2 * m1 : P) : P ⧸ N)
      rw [QuotientGroup.eq]
      -- (m1 m2)⁻¹ (m2 m1) = ⁅m̂2⁻¹, m̂1⁻¹⁆ ∈ M' ≤ Φ(M)
      have hcmem : (m1 * m2)⁻¹ * (m2 * m1) ∈ M :=
        M.mul_mem (M.inv_mem (M.mul_mem hm1 hm2)) (M.mul_mem hm2 hm1)
      have hc : (⟨(m1 * m2)⁻¹ * (m2 * m1), hcmem⟩ : ↥M)
          = ⁅(⟨m2, hm2⟩ : ↥M)⁻¹, (⟨m1, hm1⟩ : ↥M)⁻¹⁆ := by
        ext
        show (m1 * m2)⁻¹ * (m2 * m1) = m2⁻¹ * m1⁻¹ * (m2⁻¹)⁻¹ * (m1⁻¹)⁻¹
        group
      have hmem : (⟨(m1 * m2)⁻¹ * (m2 * m1), hcmem⟩ : ↥M) ∈ frattini ↥M := by
        rw [hc]
        exact (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hM_pgroup)
          (by
            rw [_root_.commutator_def]
            exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
              (Subgroup.mem_top _))
      exact Subgroup.mem_map_of_mem M.subtype hmem
    · rintro ⟨y, hy⟩
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subtype.ext ?_
      show (π m) ^ p = 1
      rw [← map_pow]
      show ((m ^ p : P) : P ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      have hmem : (⟨m, hm⟩ : ↥M) ^ p ∈ frattini ↥M :=
        OddOrder.Isaacs.Ch04.pow_p_mem_frattini_of_pgroup hM_pgroup _
      exact Subgroup.mem_map_of_mem M.subtype hmem
  have haA' : π x ∈ M.map π := Subgroup.mem_map_of_mem π hx
  have hu' : π u ∉ M.map π := by
    intro hmem
    obtain ⟨w, hwM, hw⟩ := Subgroup.mem_map.mp hmem
    have hker : w⁻¹ * u ∈ N := by
      rw [← hkerπ, MonoidHom.mem_ker, map_mul, map_inv, hw, inv_mul_cancel]
    exact hu (by simpa using M.mul_mem hwM (hNM hker))
  -- the image of the class product list
  have hmap_list : ((List.range p).map
      (fun i => (π u) ^ i * (π x) * ((π u) ^ i)⁻¹)).prod = π L := by
    rw [hL_def, map_list_prod, List.map_map]
    congr 1
  have hlist' : ((List.range p).map
      (fun i => (π u) ^ i * (π x) * ((π u) ^ i)⁻¹)).prod ≠ 1 := by
    rw [hmap_list]; exact hπL
  -- π x is noncentral in P ⧸ N
  have haZ' : π x ∉ Subgroup.center (P ⧸ N) := by
    intro hcent
    apply hπL
    rw [← hmap_list]
    have hconst : ((List.range p).map
        (fun i => (π u) ^ i * (π x) * ((π u) ^ i)⁻¹))
        = List.replicate p (π x) := by
      rw [show List.replicate p (π x) = (List.range p).map (fun _ => π x) by
        rw [List.map_const', List.length_range]]
      refine List.map_congr_left fun i _ => ?_
      rw [Subgroup.mem_center_iff.mp hcent ((π u) ^ i)]
      group
    rw [hconst, List.prod_replicate]
    rw [← map_pow]
    show ((x ^ p : P) : P ⧸ N) = 1
    rw [QuotientGroup.eq_one_iff]
    have hmem : (⟨x, hx⟩ : ↥M) ^ p ∈ frattini ↥M :=
      OddOrder.Isaacs.Ch04.pow_p_mem_frattini_of_pgroup hM_pgroup _
    exact Subgroup.mem_map_of_mem M.subtype hmem
  -- conclude via Cor 10.5 at P ⧸ N
  obtain ⟨φ, hφ⟩ := exists_surjective_wreath_of_conj_list_prod_ne_one
    (hP.to_quotient N) hidx' hEA' haA' haZ' hu' hlist'
  exact ⟨φ.comp π, hφ.comp hπsurj⟩

end

end OddOrder.Isaacs.Ch10
