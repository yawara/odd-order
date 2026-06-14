/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction
import OddOrder.GroupTheory.CoprimeConjugacy
import OddOrder.Mathlib.Subgroup

/-!
# BG §13 (cont.): 相互制約と transition (Lemma 13.7–13.13)

**Scope**: Bender–Glauberman, _Local Analysis for the Odd Order Theorem_
(LMS LNS 188, 1994), Chapter III §13 後半 (mmd `references/bg/local-analysis.mmd`
L3596–3780, pp. 100–104)。

`S13_PrimeAction.lean`（定義 + Lemma 13.1–13.6）の下流 leaf。§13 の root bottleneck
である **Lemma 13.6** (`maximalContaining_eq_singleton_of_E1`) は上流に残り、本ファイルは
13.6 と独立に着手できる 13.7 / 13.8 を frontier に持つ（Lane F）。

依存関係（mmd で確認、13.6 を root とする funnel）:

* **Lemma 13.7** `E1E3_actsPrime`: Thm 13.4 / 13.5 / Cor 13.2 / Cor 13.3(b) — **13.6 非依存**
* **Lemma 13.8** `forbidden_config_impossible`: Uniqueness / Thm 10.1(b) · 10.2 /
  Lem 12.18 / Prop 10.14(d) / Thm 13.4 — **13.6 非依存**
* **Theorem 13.9** `sigma_disjoint_of_nonconjugate`: 13.6 + 13.8（§14 Prop 14.2 funnel の要）
* **Theorem 13.10** `E1_regular_on_E3_of_noncentralize`: 13.6 + 13.8
* **Corollary 13.11** `E3_not_regular_consequences`: 13.10 + 13.7
* （未記述）**Lemma 13.12 / 13.13**: 13.6 ほか（τ₂ の素数。§14 が直接依存）

⟹ 13.7 / 13.8 は G の 13.6 着手と完全並行で証明でき、13.6 landing 後に
13.9–13.13 を分担消化する。詳細 = `notes/bg/s13_prime_action.md`。
-/

namespace OddOrder.BG.Ch3.S13

open OddOrder.GroupTheory
open OddOrder.Isaacs
open OddOrder.BG.Ch3.S12
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## helper: prime-action ⟹ trivial centralizer -/

/-- **prime-action ⟹ trivial centralizer** (BG §13 の (13.2) 適用パターン): `X` が `N` に
prime 作用し、`W ≤ N` を `X` が非中心化 (`⁅W, X⁆ ≠ ⊥`) するなら、`W` を中心化する `X` の元は
自明のみ — `C_X(W) = X ⊓ C_G(W) = 1`。

理由: `x ∈ X#` が `W` を中心化すると、`W ≤ N ⊓ C_G(x) = fixedByElement N x`、prime 作用で
これは `fixedBy N X = N ⊓ C_G(X)`、ゆえ `W ≤ C_G(X)` すなわち `⁅W, X⁆ = ⊥` で矛盾。
Lemma 13.7 step 5c (`C_{E₁}(M_σ∩M*)=1`) の核。 -/
theorem actsPrimeOn_inf_centralizer_eq_bot {N X W : Subgroup G}
    (h : ActsPrimeOn N X) (hW : W ≤ N) (hcomm : ⁅W, X⁆ ≠ ⊥) :
    X ⊓ Subgroup.centralizer (W : Set G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hxne
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_centralizer_iff] at hxC
  -- `W ≤ C_G(x)`: every `w ∈ W` commutes with `x`.
  have hWx : W ≤ Subgroup.centralizer ({x} : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    rintro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    exact (hxC w hw).symm
  -- `W ≤ fixedByElement N x = fixedBy N X` (prime action), hence `W ≤ C_G(X)`.
  have hWfix : W ≤ fixedByElement N x := by
    rw [fixedByElement_def]; exact le_inf hW hWx
  rw [h x hxX hxne, fixedBy_def] at hWfix
  exact hcomm (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (hWfix.trans inf_le_right))

/-- **prime-order 十分条件 ⟹ prime action** (BG §13 intro の「`C_N(g)=C_N(X)` ⟺
`C_N(P)⊆C_N(X)` (∀`P∈ℰ¹(X)`)」の easy 方向): `X#` の全 **素数位数**元 `x` で
`C_N(x) ≤ C_N(X)` (`fixedByElement N x ≤ fixedBy N X`) なら、`X` は `N` に prime 作用する。

任意の `g∈X#` をその素数べき部分 `x = g^{ord g/p}` (`p ∣ ord g` 素数) に落とすと
`x ∈ X#` は素数位数で `C_N(g) ⊆ C_N(x)` (x は g のべき)。Lemma 13.7 step 4 (equal case) で
`E₁⊔E₃` の prime 作用を素数位数部分群ごとに検証する土台。 -/
theorem actsPrimeOn_of_prime_order_le [Finite G] {N X : Subgroup G}
    (hpr : ∀ x ∈ X, (orderOf x).Prime → fixedByElement N x ≤ fixedBy N X) :
    ActsPrimeOn N X := by
  intro g hg hg1
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hg)
  have hord1 : orderOf g ≠ 1 := fun hc => hg1 (orderOf_eq_one_iff.mp hc)
  have hord0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨p, hp, hpdvd⟩ := (orderOf g).exists_prime_and_dvd hord1
  set d : ℕ := orderOf g / p with hd
  have hdvd : d ∣ orderOf g := ⟨p, (Nat.div_mul_cancel hpdvd).symm⟩
  have hd0 : d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hpdvd) hp.pos).ne'
  set x : G := g ^ d with hx
  have hxord : orderOf x = p := by
    rw [hx, orderOf_pow' g hd0, Nat.gcd_eq_right hdvd, hd, Nat.div_div_self hpdvd hord0]
  have hxX : x ∈ X := hx ▸ X.pow_mem hg d
  -- `C(g) ⊆ C(x)` because `x = g ^ d` is a power of `g`.
  have hgx : fixedByElement N g ≤ fixedByElement N x := by
    rw [fixedByElement_def, fixedByElement_def]
    refine inf_le_inf_left N ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    rintro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    have hgy : Commute g y := hy g rfl
    rw [hx]
    exact (hgy.pow_left d).eq
  exact hgx.trans (hpr x hxX (by rw [hxord]; exact hp))

/-- **prime action は acting 部分群について anti-monotone**: `X` が `N` に prime 作用し
`X' ≤ X` なら `X'` も `N` に prime 作用する。`g∈X'#` で `C_N(g)=C_N(X)` (X prime)、
`C_N(X) ≤ C_N(X')` (X'≤X、centralizer は antitone)、`C_N(X')≤C_N(g)` (g∈X') で挟む。
13.7 step 5(f) で `E₁ ≤ (Hall τ₁(M*))` の prime 作用を `E₁` へ落とすのに使う。 -/
theorem ActsPrimeOn.of_le_right {N X X' : Subgroup G} (h : ActsPrimeOn N X) (hX' : X' ≤ X) :
    ActsPrimeOn N X' := by
  intro g hg hg1
  refine le_antisymm ?_ (fixedBy_le_fixedByElement hg)
  rw [h g (hX' hg) hg1, fixedBy_def, fixedBy_def]
  exact inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX'))

/-- `X` が `N` を正規化するなら、`X` は `C_N(X) = fixedBy N X = N ⊓ C(X)` も正規化する。
`X` は `N` も `X`(自分自身)も正規化するので、`C(X)` も保つ。Lemma 13.7 equal case で
`x'∈E₃` が `D = C_N(E₃)` を共役で保つために使う。 -/
theorem le_normalizer_fixedBy {N X : Subgroup G} (hXN : X ≤ Subgroup.normalizer N) :
    X ≤ Subgroup.normalizer (fixedBy N X) := by
  intro z hz
  have hzNX : z ∈ Subgroup.normalizer X := Subgroup.le_normalizer hz
  have hzN : z ∈ Subgroup.normalizer N := hXN hz
  rw [Subgroup.mem_normalizer_iff]
  intro w
  rw [fixedBy_def, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  have hNpart : w ∈ N ↔ z * w * z⁻¹ ∈ N := Subgroup.mem_normalizer_iff.mp hzN w
  constructor
  · rintro ⟨hwN, hwC⟩
    refine ⟨hNpart.mp hwN, ?_⟩
    intro e he
    have hez : z⁻¹ * e * z ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hzNX) e).mp he
    have hcomm := hwC _ hez
    calc e * (z * w * z⁻¹) = z * ((z⁻¹ * e * z) * w) * z⁻¹ := by group
      _ = z * (w * (z⁻¹ * e * z)) * z⁻¹ := by rw [hcomm]
      _ = (z * w * z⁻¹) * e := by group
  · rintro ⟨hwN, hwC⟩
    refine ⟨hNpart.mpr hwN, ?_⟩
    intro e he
    have hez : z * e * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hzNX e).mp he
    have hcomm := hwC _ hez
    have hkey : z * (e * w) * z⁻¹ = z * (w * e) * z⁻¹ := by
      calc z * (e * w) * z⁻¹ = (z * e * z⁻¹) * (z * w * z⁻¹) := by group
        _ = (z * w * z⁻¹) * (z * e * z⁻¹) := hcomm
        _ = z * (w * e) * z⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel hkey)

/-- **prime action の join (equal case)**: `E₁`, `E₃` がともに `N` に prime 作用し、
互いに素な位数を持ち、`E₁` が `E₃` を正規化し、両者が `N` を正規化し、かつ
`C_N(E₁) = C_N(E₃)` (`= D`) なら、`E₁ ⊔ E₃` も `N` に prime 作用する。

BG Lemma 13.7 の equal case。素数位数 `x∈(E₁⊔E₃)#` を `x = b·a` (`b∈E₃`, `a∈E₁`) に分解。
`a=1` なら `x∈E₃` で済む。`a≠1` なら Peterfalvi (2.1) `exists_mem_centralizer_conj` で coset
`E₃·a` を `C_{E₃}(a)·a` に collapse — `x` は `c·a` (`c∈C_{E₃}(a)`) に `E₃`-共役。位数が素数ゆえ
`ord(x)=ord(c)·ord(a)` (commute+coprime) から `ord(c)=1`, すなわち `c=1`、つまり `x` は `a∈E₁#`
に共役。あとは `C_N(x)=D` を共役 (E₃ 元) で押し戻す (`le_normalizer_fixedBy` + `hD` で E₃ 経由)。 -/
theorem actsPrimeOn_sup_of_eq_centralizer [Finite G] {N E₁ E₃ : Subgroup G}
    (hE1 : ActsPrimeOn N E₁) (hE3 : ActsPrimeOn N E₃)
    (hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₃))
    (hnorm : E₁ ≤ Subgroup.normalizer E₃)
    (hN3 : E₃ ≤ Subgroup.normalizer N)
    (hD : fixedBy N E₁ = fixedBy N E₃) :
    ActsPrimeOn N (E₁ ⊔ E₃) := by
  have hHD : fixedBy N (E₁ ⊔ E₃) = fixedBy N E₁ := by
    have h1 : fixedBy N (E₁ ⊔ E₃) = fixedBy N E₁ ⊓ fixedBy N E₃ := by
      rw [fixedBy_def, fixedBy_def, fixedBy_def, Subgroup.centralizer_sup, inf_inf_distrib_left]
    rw [h1, ← hD, inf_idem]
  have hE3normD : E₃ ≤ Subgroup.normalizer (fixedBy N E₃) := le_normalizer_fixedBy hN3
  apply actsPrimeOn_of_prime_order_le
  intro x hxH hxprime
  rw [hHD]
  have hxne : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hxprime; exact hxprime.ne_one rfl
  -- decompose `x = b * a`, `b ∈ E₃`, `a ∈ E₁`
  have hxset : (x : G) ∈ (E₃ : Set G) * (E₁ : Set G) := by
    have hcoe : (↑(E₁ ⊔ E₃) : Set G) = (E₃ : Set G) * (E₁ : Set G) := by
      rw [sup_comm]; exact Subgroup.coe_mul_of_right_le_normalizer_left E₃ E₁ hnorm
    rw [← hcoe]; exact hxH
  obtain ⟨b, hb, a, ha, hba⟩ := Set.mem_mul.mp hxset
  rw [SetLike.mem_coe] at hb ha
  by_cases ha1 : a = 1
  · -- `x = b ∈ E₃`
    have hxE3 : x ∈ E₃ := by rw [← hba, ha1, mul_one]; exact hb
    exact le_of_eq (by rw [hE3 x hxE3 hxne, hD])
  · -- `a ≠ 1`: collapse the coset `E₃·a` via (2.1) and force `c = 1`
    have hordvd : orderOf a ∣ Nat.card E₁ := by
      have h := orderOf_dvd_natCard (⟨a, ha⟩ : E₁); rwa [← Subgroup.orderOf_coe] at h
    have hcop_a : Nat.Coprime (orderOf a) (Nat.card E₃) := hcop.coprime_dvd_left hordvd
    have hnorm_a : ∀ y ∈ E₃, a * y * a⁻¹ ∈ E₃ := fun y hy =>
      (Subgroup.mem_normalizer_iff.mp (hnorm ha) y).mp hy
    obtain ⟨c, hcE3C, x', hx'E3, hconj⟩ :=
      OddOrder.GroupTheory.exists_mem_centralizer_conj hcop_a hnorm_a hb
    rw [hba] at hconj
    obtain ⟨hcE3, hcCa⟩ := Subgroup.mem_inf.mp hcE3C
    have hca : Commute c a := by
      rw [Subgroup.mem_centralizer_iff] at hcCa
      exact (hcCa a (Set.mem_singleton a)).symm
    have hcordvd : orderOf c ∣ Nat.card E₃ := by
      have h := orderOf_dvd_natCard (⟨c, hcE3⟩ : E₃); rwa [← Subgroup.orderOf_coe] at h
    have hcop_ca : Nat.Coprime (orderOf c) (orderOf a) :=
      (hcop.symm.coprime_dvd_left hcordvd).coprime_dvd_right hordvd
    have hordca : orderOf (c * a) = orderOf c * orderOf a :=
      hca.orderOf_mul_eq_mul_orderOf_of_coprime hcop_ca
    have hsc : SemiconjBy x' x (c * a) := by
      show x' * x = (c * a) * x'
      rw [← hconj]; group
    have hordeq : orderOf x = orderOf (c * a) := SemiconjBy.orderOf_eq x' hsc
    have hordane : orderOf a ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    have hc1 : c = 1 := by
      have hp : (orderOf c * orderOf a).Prime := by rw [← hordca, ← hordeq]; exact hxprime
      rcases Nat.prime_mul_iff.mp hp with ⟨_, ha0⟩ | ⟨_, hc0⟩
      · exact absurd ha0 hordane
      · exact orderOf_eq_one_iff.mp hc0
    rw [hc1, one_mul] at hconj
    have hfa : fixedByElement N a = fixedBy N E₁ := hE1 a ha ha1
    intro y hy
    rw [fixedByElement_def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hy
    obtain ⟨hyN, hyC⟩ := hy
    have hyx : x * y = y * x := hyC x (Set.mem_singleton x)
    have hwN : x' * y * x'⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hN3 hx'E3) y).mp hyN
    have hwa : a * (x' * y * x'⁻¹) = (x' * y * x'⁻¹) * a := by
      rw [← hconj]
      calc x' * x * x'⁻¹ * (x' * y * x'⁻¹) = x' * (x * y) * x'⁻¹ := by group
        _ = x' * (y * x) * x'⁻¹ := by rw [hyx]
        _ = (x' * y * x'⁻¹) * (x' * x * x'⁻¹) := by group
    have hw_fix : x' * y * x'⁻¹ ∈ fixedBy N E₁ := by
      rw [← hfa, fixedByElement_def]
      exact Subgroup.mem_inf.mpr ⟨hwN, Subgroup.mem_centralizer_iff.mpr (by
        intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu; exact hwa)⟩
    rw [hD]
    rw [hD] at hw_fix
    have hgoal : x'⁻¹ * (x' * y * x'⁻¹) * x' ∈ fixedBy N E₃ := by
      have hnn := hE3normD (inv_mem hx'E3)
      rw [Subgroup.mem_normalizer_iff] at hnn
      simpa using (hnn (x' * y * x'⁻¹)).mp hw_fix
    have hyeq : x'⁻¹ * (x' * y * x'⁻¹) * x' = y := by group
    rwa [hyeq] at hgoal

/-- **Lemma 13.7 step 1** (witness 抽出): `E₁` が `E₃` に regular 作用しないなら、素数 `p, r` と
`P ∈ ℰ_p¹(E₁)`, `R ∈ ℰ_r¹(E₃)` で `R` が `P` を中心化するものが存在する。

`¬regular` から `g∈E₁#` と `h∈E₃#` (`[g,h]=1`) を取り、各々の素数べき部分
`P = ⟨g^{ord g/p}⟩`, `R = ⟨h^{ord h/r}⟩` (素数位数) を取る。`P ≤ ⟨g⟩`, `R ≤ ⟨h⟩` と
`Commute g h` から `R ≤ C(P)`。 -/
theorem exists_elemAbelian_centralizing_of_not_regular [Finite G] {E₁ E₃ : Subgroup G}
    (hreg : ¬ ActsRegularlyOn E₃ E₁) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ ∃ P R : Subgroup G,
      P ∈ elemAbelianOfRank G p 1 ∧ P ≤ E₁ ∧
      R ∈ elemAbelianOfRank G r 1 ∧ R ≤ E₃ ∧
      R ≤ Subgroup.centralizer (P : Set G) := by
  classical
  rw [actsRegularlyOn_iff] at hreg
  simp only [fixedByElement_def] at hreg
  push_neg at hreg
  obtain ⟨g, hgE1, hgne, hfix⟩ := hreg
  obtain ⟨⟨he, he_mem⟩, he_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfix
  obtain ⟨heE3, heC⟩ := Subgroup.mem_inf.mp he_mem
  have he1 : he ≠ 1 := fun hc => he_ne (Subtype.ext (by simpa using hc))
  have hghe : Commute g he := by
    rw [Subgroup.mem_centralizer_iff] at heC; exact heC g (Set.mem_singleton g)
  -- order-`s` cyclic subgroup of `⟨x⟩` inside `K`, for any `x ∈ K#`.
  have key : ∀ {K : Subgroup G} (x : G), x ∈ K → x ≠ 1 →
      ∃ s : ℕ, s.Prime ∧ ∃ Q : Subgroup G,
        Q ∈ elemAbelianOfRank G s 1 ∧ Q ≤ K ∧ Q ≤ Subgroup.zpowers x := by
    intro K x hxK hx
    have hord1 : orderOf x ≠ 1 := fun hc => hx (orderOf_eq_one_iff.mp hc)
    have hord0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
    obtain ⟨s, hs, hsdvd⟩ := (orderOf x).exists_prime_and_dvd hord1
    haveI : Fact s.Prime := ⟨hs⟩
    set d := orderOf x / s with hd
    have hdvd : d ∣ orderOf x := ⟨s, (Nat.div_mul_cancel hsdvd).symm⟩
    have hd0 : d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (orderOf_pos x) hsdvd) hs.pos).ne'
    set y := x ^ d with hy
    have hyord : orderOf y = s := by
      rw [hy, orderOf_pow' x hd0, Nat.gcd_eq_right hdvd, hd, Nat.div_div_self hsdvd hord0]
    have hycard : Nat.card (Subgroup.zpowers y) = s := by rw [Nat.card_zpowers, hyord]
    refine ⟨s, hs, Subgroup.zpowers y, ?_, ?_, ?_⟩
    · exact ⟨Subgroup.IsElementaryAbelian.of_card_prime hycard, by rw [pow_one]; exact hycard⟩
    · rw [Subgroup.zpowers_le, hy]; exact K.pow_mem hxK d
    · rw [Subgroup.zpowers_le, hy]; exact pow_mem (Subgroup.mem_zpowers x) d
  obtain ⟨p, hp, P, hP, hPE1, hPg⟩ := key g hgE1 hgne
  obtain ⟨r, hr, R, hR, hRE3, hRhe⟩ := key he heE3 he1
  refine ⟨p, r, hp, hr, P, R, hP, hPE1, hR, hRE3, ?_⟩
  have hzz : Subgroup.zpowers he ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hu
    obtain ⟨k, rfl⟩ := hu
    exact (hghe.zpow_left k).eq
  exact hRhe.trans (hzz.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hPg)))

/-- `P ∈ ℰ_s¹(X)` (`P ≤ X`, `s` 素数) + `ActsPrimeOn N X` ⟹ `C_N(P) = C_N(X)`
(`fixedBy N P = fixedBy N X`)。`P` は素数位数ゆえ生成元 `g∈P#` で `P=⟨g⟩`、
`C_N(P)=C_N(g)=C_N(X)` (prime action)。13.7 body の step 2/5 で `C_N(P)=C_N(E₁)` 等に使う。 -/
theorem fixedBy_eq_of_elemAbelian_one [Finite G] {N X P : Subgroup G} {s : ℕ} (hs : s.Prime)
    (hX : ActsPrimeOn N X) (hP : P ∈ elemAbelianOfRank G s 1) (hPX : P ≤ X) :
    fixedBy N P = fixedBy N X := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hPcard : Nat.card P = s := by rw [← pow_one s]; exact hP.2
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hPcard; exact hs.one_lt.ne' hPcard.symm
  obtain ⟨⟨g, hgP⟩, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hg1 : g ≠ 1 := fun hc => hgne (Subtype.ext (by simpa using hc))
  have hog : orderOf g = s := by
    have hdvd : orderOf g ∣ Nat.card P := by
      have h := orderOf_dvd_natCard (⟨g, hgP⟩ : P); rwa [← Subgroup.orderOf_coe] at h
    rw [hPcard] at hdvd
    rcases hs.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hg1
    · exact h2
  have hPg : P = Subgroup.zpowers g :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgP)
      (by rw [Nat.card_zpowers, hog]; exact hPcard.le)).symm
  have hzC : Subgroup.centralizer (Subgroup.zpowers g : Set G)
      = Subgroup.centralizer ({g} : Set G) := by
    apply le_antisymm
    · exact Subgroup.centralizer_le (by
        intro u hu; rw [Set.mem_singleton_iff] at hu; rw [hu]; exact Subgroup.mem_zpowers g)
    · intro w hw
      rw [Subgroup.mem_centralizer_iff] at hw ⊢
      intro u hu
      rw [SetLike.mem_coe, Subgroup.mem_zpowers_iff] at hu
      obtain ⟨k, rfl⟩ := hu
      have hc : Commute g w := hw g (Set.mem_singleton g)
      exact (hc.zpow_left k).eq
  calc fixedBy N P = fixedByElement N g := by rw [hPg, fixedBy_def, fixedByElement_def, hzC]
    _ = fixedBy N X := hX g (hPX hgP) hg1

/-- **Lemma 13.7 step 5(f)**: `E₁` (cyclic, `π(E₁)⊆τ₁(M*)`, `E₁≤M*`) と `P∈ℰ_p¹(E₁)` で
`P` が `R⊆M*_σ` を中心化するなら、`E₁` 全体が `R` を中心化する。

Hall 共役で `w•E₁ ≤ E₁*` (M* の Hall τ₁、E1_actsPrime で M*_σ に prime)。`P` の生成元を `w` で
共役した `z∈E₁*#` は `w•R⊆M*_σ` を中心化 ⟹ prime 作用で `E₁*` 全体が `w•R` を中心化 ⟹
`w•E₁≤E₁*` が `w•R` を中心化 ⟹ 共役を戻して `E₁` が `R` を中心化。prime-action 共役不変性を
直接使わず、R・P を M* の setup frame へ共役するのが鍵。 -/
theorem E1_centralizes_R_of_hall_tau1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {E₁ Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G)
    (hE1ne : E₁ ≠ ⊥) (hE1M : E₁ ≤ Mstar)
    (hπ : ∀ s ∈ (Nat.card ↥E₁).primeFactors, s ∈ tau1 Mstar)
    {p : ℕ} (hp : p.Prime) {P R : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1)
    (hPE1 : P ≤ E₁) (hRMsig : R ≤ S10.Msigma Mstar)
    (hRcP : R ≤ Subgroup.centralizer (P : Set G)) :
    E₁ ≤ Subgroup.centralizer (R : Set G) := by
  classical
  obtain ⟨Es, E1s, E2s, E3s, hs⟩ := exists_subgroupESetup hG hMstar
  have hE1pi : Ch03.Subgroup.IsPiGroup (tau1 Mstar) (E₁.subgroupOf Mstar) := by
    intro s hs'
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE1M).toEquiv] at hs'
    exact hπ s hs'
  obtain ⟨w, hwM, hwle⟩ := exists_conj_smul_le_hallPiece hG hs hs.E₁_le hs.E₁_hall
    (tau1_subset_sigma_compl Mstar) hE1M hE1pi
  -- element form of `w • E₁ ≤ E₁*`.
  have hconj : ∀ e ∈ E₁, w * e * w⁻¹ ∈ E1s := by
    intro e he
    exact hwle (Subgroup.smul_mem_pointwise_smul_iff.mpr he)
  -- `M*_σ` is `w`-stable (normal in `M*`, `w ∈ M*`).
  have hwMsig : ∀ x ∈ S10.Msigma Mstar, w * x * w⁻¹ ∈ S10.Msigma Mstar := by
    have hMle : Mstar ≤ Subgroup.normalizer (S10.Msigma Mstar : Set G) := by
      rw [S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma Mstar) Mstar
    intro x hx
    exact (Subgroup.mem_normalizer_iff.mp (hMle hwM) x).mp hx
  -- nontrivial generator `p_elt` of `P` (order `p`).
  have hPcard : Nat.card P = p := by rw [← pow_one p]; exact hP.2
  haveI : Fact p.Prime := ⟨hp⟩
  have hPne : P ≠ ⊥ := by
    intro hb; rw [hb, Subgroup.card_bot] at hPcard; exact hp.one_lt.ne' hPcard.symm
  obtain ⟨⟨p_elt, hp_eltP⟩, hp_eltne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hp_elt1 : p_elt ≠ 1 := fun hc => hp_eltne (Subtype.ext (by simpa using hc))
  -- `E₁* ≠ ⊥`, prime on `M*_σ`.
  have hE1sne : E1s ≠ ⊥ := by
    obtain ⟨⟨e₀, he₀⟩, he₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1ne
    have he₀1 : e₀ ≠ 1 := fun hc => he₀ne (Subtype.ext (by simpa using hc))
    intro hb
    have : w * e₀ * w⁻¹ ∈ E1s := hconj e₀ he₀
    rw [hb, Subgroup.mem_bot] at this
    exact he₀1 (by simpa using mul_eq_one_iff_eq_inv.mp this)
  have hE1sprime : ActsPrimeOn (S10.Msigma Mstar) E1s := E1_actsPrime hG hs hE1sne
  -- `z := w p_elt w⁻¹ ∈ E₁*#`.
  set z : G := w * p_elt * w⁻¹ with hz
  have hzE1s : z ∈ E1s := hconj p_elt (hPE1 hp_eltP)
  have hzne : z ≠ 1 := by
    rw [hz]; intro hc
    apply hp_elt1
    have hcc : MulAut.conj w p_elt = MulAut.conj w 1 := by rw [map_one]; exact hc
    exact (MulAut.conj w).injective hcc
  -- `z` centralizes `w • R`, and `w • R ⊆ M*_σ`.
  have hzfix := hE1sprime z hzE1s hzne
  have hwRsub : ∀ r ∈ R, w * r * w⁻¹ ∈ fixedByElement (S10.Msigma Mstar) z := by
    intro r hr
    rw [fixedByElement_def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    refine ⟨hwMsig r (hRMsig hr), ?_⟩
    intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu
    -- `p_elt` and `r` commute (`r ∈ C(P)`, `p_elt ∈ P`).
    have hcomm : p_elt * r = r * p_elt :=
      (Subgroup.mem_centralizer_iff.mp (hRcP hr)) p_elt hp_eltP
    rw [hz]
    calc (w * p_elt * w⁻¹) * (w * r * w⁻¹) = w * (p_elt * r) * w⁻¹ := by group
      _ = w * (r * p_elt) * w⁻¹ := by rw [hcomm]
      _ = (w * r * w⁻¹) * (w * p_elt * w⁻¹) := by group
  -- hence `E₁*` centralizes `w • R`; transport back to `E₁` centralizing `R`.
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hwr_fix : w * r * w⁻¹ ∈ fixedBy (S10.Msigma Mstar) E1s := by rw [← hzfix]; exact hwRsub r hr
  rw [fixedBy_def, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hwr_fix
  have hcomm := hwr_fix.2 (w * e * w⁻¹) (hconj e he)
  -- `(wew⁻¹)(wrw⁻¹) = (wrw⁻¹)(wew⁻¹)` ⟹ `er = re` ⟹ `r e = e r`.
  have : w * (e * r) * w⁻¹ = w * (r * e) * w⁻¹ := by
    calc w * (e * r) * w⁻¹ = (w * e * w⁻¹) * (w * r * w⁻¹) := by group
      _ = (w * r * w⁻¹) * (w * e * w⁻¹) := hcomm
      _ = w * (r * e) * w⁻¹ := by group
  have her : e * r = r * e := mul_left_cancel (mul_right_cancel this)
  exact her.symm

/-- **Lemma 13.7 step 5(a)**: もし `x ∈ E₃#` で `C_{M_σ}(x) ≠ 1` なら `τ₂(M)` は空、
よって `E₂ = ⊥`、`E = E₁ ⊔ E₃`。`τ₂(M) ≠ ∅` ⟹ `∃ p∈τ₂(M), A∈ℰ_p²(E)` ⟹ Cor 12.6(d) で
`E₃` は `M_σ` に regular 作用 ⟹ `C_{M_σ}(x)=1` で矛盾。 -/
theorem E_eq_sup_of_E3_centralizer [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥) :
    E = E₁ ⊔ E₃ := by
  have hE2 : E₂ = ⊥ := by
    by_contra hE2ne
    obtain ⟨p, hp_prime, hpdvd⟩ :=
      (Nat.card E₂).exists_prime_and_dvd (fun hc => hE2ne (Subgroup.card_eq_one.mp hc))
    haveI : Fact p.Prime := ⟨hp_prime⟩
    have hc2 : Nat.card (E₂.subgroupOf E) = Nat.card E₂ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₂_le).toEquiv
    have hpτ2 : p ∈ tau2 M :=
      h.E₂_hall.1 p (hc2 ▸ Nat.mem_primeFactors.mpr ⟨hp_prime, hpdvd, Nat.card_pos.ne'⟩)
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hpτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  rw [h.eq_sup hG, hE2, sup_bot_eq]

/-- **Lemma 13.7 step 5(b) 補助**: `R ≤ E₃` なら `E ≤ N_G(R)` (`R ⊲ E`)。`E₃` は cyclic ゆえ
任意の部分群 `R` は characteristic、`E` は `E₃` を正規化する (Lem 12.1) ので `R` も正規化。 -/
theorem E_le_normalizer_of_le_E3 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {R : Subgroup G} (hRE3 : R ≤ E₃) : E ≤ Subgroup.normalizer (R : Set G) := by
  haveI : IsCyclic ↥E₃ := h.E3_isCyclic hG
  haveI : (R.subgroupOf E₃).Characteristic := Ch04.characteristic_of_subgroup_of_isCyclic _
  intro e he
  have hmem := OddOrder.BG.Ch1.S03f.mem_normalizer_map_subtype_of_characteristic (W := E₃)
    (C := R.subgroupOf E₃) (h.E3_normal hG he)
  rwa [Subgroup.map_subgroupOf_eq_of_le hRE3] at hmem

/-- **BG Lemma 13.7, step 5** (strict case impossible): with `P ∈ ℰ_p¹(E₁)`, `R ∈ ℰ_r¹(E₃)`,
`R ≤ C(P)`, the strict containment `C_{M_σ}(E₁) ⊊ C_{M_σ}(E₃)` is contradictory.

証明 (a)-(g)、mmd L3640-3658:
(a) `1⊂R⊂E₃`, `C_{M_σ}(R)≠1` ⟹ Cor 12.6(d) で `τ₂(M)` empty ⟹ `E = E₁ ⊔ E₃`。
(b) `R ⊲ E`、`M* ∈ 𝓜(N_G(R))`、`E ⊆ M*`、`1⊂[C_{M_σ}(R),P] ⊆ [M_σ⊓M*, E₁]`。
(c) (13.2) ⟹ `C_{E₁}(M_σ⊓M*)=1` (helper `actsPrimeOn_inf_centralizer_eq_bot`)。
(d) Cor 13.2(b) ⟹ `π(E₁) ⊆ τ₁(M*)`。
(e) Cor 13.2(c) ⟹ `R ⊆ M*_σ`。
(f) `E₁ ⊆ E₁*` (Hall `τ₁(M*)`)、Thm 13.5 を M* に ⟹ `E₁` が `R` を中心化。
(g) `E=E₁E₃` + `E₁,E₃` が `R` 中心化 ⟹ `R⊆Z(E)`、`C_{E₃}(E)=1` (Lem 12.1) と矛盾。

詳細 = `notes/bg/s13_transition_lane_f.md`。 -/
theorem strict_centralizer_config_false [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) {P R : Subgroup G}
    (hP : P ∈ elemAbelianOfRank G p 1) (hPE1 : P ≤ E₁)
    (hR : R ∈ elemAbelianOfRank G r 1) (hRE3 : R ≤ E₃)
    (hRcP : R ≤ Subgroup.centralizer (P : Set G))
    (hlt : fixedBy (S10.Msigma M) E₁ < fixedBy (S10.Msigma M) E₃) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hE1ne : E₁ ≠ ⊥ := fun hb =>
    (ne_bot_of_mem_elemAbelianOfRank_one hP) (le_bot_iff.mp (hPE1.trans hb.le))
  have hRne : R ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hR
  have hE1prime : ActsPrimeOn (S10.Msigma M) E₁ := E1_actsPrime hG h hE1ne
  have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
  -- connect `hlt` to `P`, `R`.
  have hPeq : fixedBy (S10.Msigma M) P = fixedBy (S10.Msigma M) E₁ :=
    fixedBy_eq_of_elemAbelian_one hp hE1prime hP hPE1
  have hReq : fixedBy (S10.Msigma M) R = fixedBy (S10.Msigma M) E₃ :=
    fixedBy_eq_of_elemAbelian_one hr hE3prime hR hRE3
  have hlt' : fixedBy (S10.Msigma M) P < fixedBy (S10.Msigma M) R := by rw [hPeq, hReq]; exact hlt
  have hCRne : fixedBy (S10.Msigma M) R ≠ ⊥ := (lt_of_le_of_lt bot_le hlt').ne'
  -- (a) `E = E₁ ⊔ E₃`.
  obtain ⟨⟨r_elt, hr_eltR⟩, hr_eltne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRne
  have hr_elt1 : r_elt ≠ 1 := fun hc => hr_eltne (Subtype.ext (by simpa using hc))
  have hCre : S10.Msigma M ⊓ Subgroup.centralizer ({r_elt} : Set G) ≠ ⊥ := by
    refine fun hb => hCRne (le_bot_iff.mp ?_)
    rw [fixedBy_def, ← hb]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (by
      intro u hu; rw [Set.mem_singleton_iff] at hu; subst hu; exact hr_eltR))
  have hEsup : E = E₁ ⊔ E₃ := E_eq_sup_of_E3_centralizer hG h (hRE3 hr_eltR) hr_elt1 hCre
  -- (b) `R ⊲ E`, extract `M* ∈ ℳ(N_G(R))`, `E ⊆ M*`.
  have hENR : E ≤ Subgroup.normalizer (R : Set G) := E_le_normalizer_of_le_E3 hG h hRE3
  have hRM : R ≤ M := hRE3.trans h.E3_le_M
  have hNRne : Subgroup.normalizer (R : Set G) ≠ ⊤ := by
    intro htop
    haveI : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal R inferInstance with hb | ht
    · exact hRne hb
    · exact (mem_maximalSubgroups.mp h.mem_maximal).1 (top_le_iff.mp (ht ▸ hRM))
  obtain ⟨Mstar, hMstarCo, hNRM⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (R : Set G))).resolve_left hNRne
  have hMstarMem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (R : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hMstarCo, hNRM⟩
  have hMstarMax : Mstar ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMstarCo
  have hEMstar : E ≤ Mstar := hENR.trans hNRM
  have hrτ3 : r ∈ tau3 M := by
    have hc3 : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    refine h.E₃_hall.1 r (hc3 ▸ Nat.mem_primeFactors.mpr ⟨hr, ?_, Nat.card_pos.ne'⟩)
    have hdvd : Nat.card R ∣ Nat.card E₃ := Subgroup.card_dvd_of_le hRE3
    rwa [show Nat.card R = r by rw [← pow_one r]; exact hR.2] at hdvd
  have hRr : IsPGroup r ↥R := IsPGroup.of_card (by rw [hR.2, pow_one])
  have hCor132 := tau13_pSubgroup_centralizes hG h (Or.inr hrτ3) hRM hRne hRr hMstarMem
  -- (c) `C_{E₁}(M_σ ⊓ M*) = ⊥`.
  have hcommRP : ⁅fixedBy (S10.Msigma M) R, P⁆ ≠ ⊥ := by
    intro hb
    have hle : fixedBy (S10.Msigma M) R ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
    have hcontra : fixedBy (S10.Msigma M) R ≤ fixedBy (S10.Msigma M) P :=
      le_inf (by rw [fixedBy_def]; exact inf_le_left) hle
    exact absurd (le_antisymm hlt'.le hcontra) (ne_of_lt hlt')
  have hCRsub : fixedBy (S10.Msigma M) R ≤ S10.Msigma M ⊓ Mstar :=
    le_inf (by rw [fixedBy_def]; exact inf_le_left)
      (by rw [fixedBy_def]
          exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (R : Set G)).trans hNRM))
  have hcomm2 : ⁅(S10.Msigma M ⊓ Mstar : Subgroup G), E₁⁆ ≠ ⊥ := fun hb =>
    hcommRP (le_bot_iff.mp ((Subgroup.commutator_mono hCRsub hPE1).trans hb.le))
  have hCE1 : E₁ ⊓ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) = ⊥ :=
    actsPrimeOn_inf_centralizer_eq_bot hE1prime inf_le_left hcomm2
  -- (d) `π(E₁) ⊆ τ₁(M*)`.
  have hπ : ∀ s ∈ (Nat.card ↥E₁).primeFactors, s ∈ tau1 Mstar := by
    intro s hs
    by_contra hsτ1
    have hs_prime := Nat.prime_of_mem_primeFactors hs
    haveI : Fact s.Prime := ⟨hs_prime⟩
    haveI : Fintype ↥E₁ := Fintype.ofFinite _
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card (G := ↥E₁) s
      (by rw [← Nat.card_eq_fintype_card]; exact (Nat.mem_primeFactors.mp hs).2.1)
    have hxE1 : (a : G) ∈ E₁ := a.2
    have hxord : orderOf (a : G) = s := by rw [Subgroup.orderOf_coe]; exact ha
    have hxne : (a : G) ≠ 1 := by
      intro hc; apply hs_prime.ne_one; rw [← hxord, hc, orderOf_one]
    have hzxEM : Subgroup.zpowers (a : G) ≤ E ⊓ Mstar :=
      le_inf (Subgroup.zpowers_le.mpr (h.E₁_le hxE1))
        (Subgroup.zpowers_le.mpr (hEMstar (h.E₁_le hxE1)))
    have hzxpi : Subgroup.IsPiSubgroup ((tau1 Mstar)ᶜ) (Subgroup.zpowers (a : G)) := by
      intro t ht
      rw [Nat.card_zpowers, hxord, hs_prime.primeFactors, Finset.mem_singleton] at ht
      rw [ht]; exact hsτ1
    have hzxC := hCor132.2.1 (Subgroup.zpowers (a : G)) hzxEM hzxpi
    have hxbot : Subgroup.zpowers (a : G) ≤
        E₁ ⊓ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) :=
      le_inf (Subgroup.zpowers_le.mpr hxE1) hzxC
    rw [hCE1] at hxbot
    exact hxne (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hxbot))
  -- (e) `R ⊆ M*_σ`.
  have hE1MM : E₁ ≤ M ⊓ Mstar := le_inf h.E1_le_M (h.E₁_le.trans hEMstar)
  have hcomm3 : ⁅(S10.Msigma M ⊓ Mstar : Subgroup G), M ⊓ Mstar⁆ ≠ ⊥ := fun hb =>
    hcomm2 (le_bot_iff.mp ((Subgroup.commutator_mono le_rfl hE1MM).trans hb.le))
  have hrσMstar : r ∈ S10.sigma Mstar := (hCor132.2.2 hcomm3).1
  have hRMstar : R ≤ Mstar := hRE3.trans (h.E₃_le.trans hEMstar)
  have hRpiσ : Ch03.Subgroup.IsPiGroup (S10.sigma Mstar) R := by
    intro t ht
    rw [show Nat.card ↥R = r by rw [← pow_one r]; exact hR.2, hr.primeFactors,
      Finset.mem_singleton] at ht
    rw [ht]; exact hrσMstar
  have hRMsig : R ≤ S10.Msigma Mstar :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hMstarMax) hRMstar hRpiσ
  -- (f) `E₁` centralizes `R`.
  have hE1cR : E₁ ≤ Subgroup.centralizer (R : Set G) :=
    E1_centralizes_R_of_hall_tau1 hG hMstarMax hE1ne (h.E₁_le.trans hEMstar) hπ hp hP hPE1 hRMsig hRcP
  -- (g) `E₃` centralizes `R`, hence `E` does, contradiction with `C_G(E) ⊓ E₃ = ⊥`.
  have hE3cR : E₃ ≤ Subgroup.centralizer (R : Set G) := by
    haveI : IsCyclic ↥E₃ := h.E3_isCyclic hG
    letI : CommGroup ↥E₃ := IsCyclic.commGroup
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subtype.ext_iff.mp (mul_comm (⟨u, hRE3 hu⟩ : ↥E₃) ⟨e, he⟩)
  have hEcR : E ≤ Subgroup.centralizer (R : Set G) := hEsup ▸ sup_le hE1cR hE3cR
  have hRcE : R ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcR)
  have hRbot : R ≤ Subgroup.centralizer (E : Set G) ⊓ E₃ := le_inf hRcE hRE3
  rw [(subgroupE_basic hG h).2.2.2.2.2.1] at hRbot
  exact hRne (le_bot_iff.mp hRbot)

/-! ## §13 prime action の拡張解析 (cont., mmd L3596-3628) -/

/-- **BG Lemma 13.7** (mmd L3596): `E₁≠1` かつ `E₁` が `E₃` に regular 作用しないなら、`E₁E₃` は
`M_σ` に prime 作用。 -/
theorem E1E3_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1 : E₁ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn E₃ E₁) :
    ActsPrimeOn (S10.Msigma M) (E₁ ⊔ E₃) := by
  have hE1prime : ActsPrimeOn (S10.Msigma M) E₁ := E1_actsPrime hG h hE1
  have hE3prime : ActsPrimeOn (S10.Msigma M) E₃ := (cyclicSylow_actsPrime hG h).2
  -- `E₁`, `E₃` have coprime orders (τ₁ vs τ₃ disjoint, Hall subgroups).
  have hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₃) := by
    by_contra hnc
    obtain ⟨s, hs, hsm, hsn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hsN : s.Prime := hs
    have hsE1 : s ∈ (Nat.card E₁).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hsN, hsm, Nat.card_pos.ne'⟩
    have hsE3 : s ∈ (Nat.card E₃).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hsN, hsn, Nat.card_pos.ne'⟩
    have hc1 : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    have hc3 : Nat.card (E₃.subgroupOf E) = Nat.card E₃ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv
    exact not_mem_tau3_of_mem_tau1 (h.E₁_hall.1 s (hc1 ▸ hsE1)) (h.E₃_hall.1 s (hc3 ▸ hsE3))
  have hnorm : E₁ ≤ Subgroup.normalizer (E₃ : Set G) := h.E₁_le.trans (h.E3_normal hG)
  have hN3 : E₃ ≤ Subgroup.normalizer (S10.Msigma M : Set G) :=
    (h.E₃_le.trans h.E_le).trans
      (by rw [S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma M) M)
  have hD : fixedBy (S10.Msigma M) E₁ = fixedBy (S10.Msigma M) E₃ := by
    -- step 1: extract `P ∈ ℰ_p¹(E₁)`, `R ∈ ℰ_r¹(E₃)` with `R ≤ C(P)`.
    obtain ⟨p, r, hp, hr, P, R, hP, hPE1, hR, hRE3, hRcP⟩ :=
      exists_elemAbelian_centralizing_of_not_regular hreg
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact r.Prime := ⟨hr⟩
    have hPcardp : Nat.card P = p := by rw [← pow_one p]; exact hP.2
    have hRcardr : Nat.card R = r := by rw [← pow_one r]; exact hR.2
    have hc1 : Nat.card (E₁.subgroupOf E) = Nat.card E₁ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv
    have hpτ1 : p ∈ tau1 M := by
      have hpdvd : p ∣ Nat.card E₁ := hPcardp ▸ Subgroup.card_dvd_of_le hPE1
      exact h.E₁_hall.1 p (hc1 ▸ Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩)
    have hrπE : r ∈ (Nat.card E).primeFactors := by
      have hrdvd : r ∣ Nat.card E := hRcardr ▸ Subgroup.card_dvd_of_le (hRE3.trans h.E₃_le)
      exact Nat.mem_primeFactors.mpr ⟨hr, hrdvd, Nat.card_pos.ne'⟩
    -- step 2: `C_N(E₁) = C_N(P) ≤ C_N(R) = C_N(E₃)` (Theorem 13.4 + prime actions).
    have hPeq : fixedBy (S10.Msigma M) P = fixedBy (S10.Msigma M) E₁ :=
      fixedBy_eq_of_elemAbelian_one hp hE1prime hP hPE1
    have hReq : fixedBy (S10.Msigma M) R = fixedBy (S10.Msigma M) E₃ :=
      fixedBy_eq_of_elemAbelian_one hr hE3prime hR hRE3
    have hle : fixedBy (S10.Msigma M) E₁ ≤ fixedBy (S10.Msigma M) E₃ := by
      rw [← hPeq, ← hReq, fixedBy_def, fixedBy_def]
      exact centralizer_le_centralizer_of_tau1 hG h hpτ1 hrπE hP (hPE1.trans h.E₁_le) hR
        (le_inf (hRE3.trans h.E₃_le) hRcP)
    -- step 5: rule out the strict containment.
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact (strict_centralizer_config_false hG h hp hr hP hPE1 hR hRE3 hRcP hlt).elim
    · exact heq
  exact actsPrimeOn_sup_of_eq_centralizer hE1prime hE3prime hcop hnorm hN3 hD

/-! ## helper: 有限 `q`-群の normalizer-growth (Lemma 13.8 GAP 1.3) -/

/-- **有限 `q`-群の normalizer-growth**: `T` が有限 `q`-群で `Q < T` なら、`Q` はその
`T` 内 normalizer `T ⊓ N_G(Q)` に真に含まれる。冪零群の normalizer condition の帰結
(`normalizerCondition_of_isNilpotent`)。

Lemma 13.8 GAP 1.3 の核 — 「`M ∩ M*` の極大 `q`-部分群 `Q` で `N_G(Q) ⊆ M*` なら `Q` は
`M` の極大 `q`-部分群」を示すのに使う: `Q < T ≤ M` を仮定すると `T ⊓ N_G(Q) ⊆ M ⊓ M*` の
`q`-部分群が `Q` を真に含み、極大性に反する。 -/
theorem lt_inf_normalizer_of_lt_of_pgroup [Finite G] {q : ℕ} [Fact q.Prime]
    {Q T : Subgroup G} (hTq : IsPGroup q ↥T) (hQT : Q < T) :
    Q < T ⊓ Subgroup.normalizer (Q : Set G) := by
  have hQTle : Q ≤ T := hQT.le
  have hne_top : Q.subgroupOf T ≠ ⊤ := fun htop =>
    hQT.ne (le_antisymm hQTle (Subgroup.subgroupOf_eq_top.mp htop))
  haveI : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hTq
  have hNC : NormalizerCondition ↥T := normalizerCondition_of_isNilpotent
  have hgrow := hNC (Q.subgroupOf T) (lt_top_iff_ne_top.mpr hne_top)
  rw [← Subgroup.subgroupOf_normalizer_eq hQTle] at hgrow
  refine lt_of_le_of_ne (le_inf hQTle Subgroup.le_normalizer) (fun heq => hgrow.ne ?_)
  conv_lhs => rw [heq]
  rw [Subgroup.inf_subgroupOf_left]

/-! ## Lemma 13.8 step 1 — config から Lemma 12.18(b) 出力へ (GAP 1) -/

/-- **Lemma 13.8 GAP 1** (`M`-side engine): 13.8 の配置 (片側) から Lemma 12.18(b) の出力を導く。
`M ∩ M*` の極大 `q`-部分群 `Q` (`P`-不変, `C_Q(P)=1`, `N_G(Q) ⊆ M*`, `M ≠ M*`) について:

* `q ≠ p` (GAP 1.2 — `q=p` なら `P ≤ P⊔Q = Q`, `P ≤ C_Q(P)=1` で矛盾),
* `Q ≠ 1` (GAP 1.1 — `Q=1` なら `N_G(Q)=G ⊆ M*` で `M*` が極大に反する),
* `Q` は `M` の極大 `q`-部分群 (GAP 1.3 — `lt_inf_normalizer_of_lt_of_pgroup` + `N_G(Q) ⊆ M*`),
* `ℳ(N_G(Q)) ≠ {M}` (`M* ∈ ℳ(N_G(Q))`, `M* ≠ M`)

を経由して Lemma 12.18(b) (`tau1_Malpha_interaction`) を適用し
`α(M)=β(M) ∧ M_α≠1 ∧ q∉α(M) ∧ C_{M_α}(P)≠1 ∧ C_{M_α}(PQ)=1` を得る。
`M*`-side は `M ↔ M*`, `Q ↔ Q*` を入れ替えて同じ補題を再適用する。 -/
theorem forbidden_config_step1 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hMMstar : M ≠ Mstar) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : p ∈ tau1 M)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPMM : P ≤ M ⊓ Mstar)
    {Q : Subgroup G} (hQle : Q ≤ M ⊓ Mstar) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar) :
    q ≠ p ∧ Q ≠ ⊥ ∧
    S10.alpha M = S10.beta M ∧ S10.Malpha M ≠ ⊥ ∧ q ∉ S10.alpha M ∧
    S10.Malpha M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ ∧
    S10.Malpha M ⊓ Subgroup.centralizer ((P ⊔ Q : Subgroup G) : Set G) = ⊥ := by
  obtain ⟨hPea, hPcard1⟩ := mem_elemAbelianOfRank.mp hP
  have hPp : IsPGroup p ↥P := hPea.isPGroup
  have hPcard : Nat.card ↥P = p := by rw [hPcard1, pow_one]
  have hPM : P ≤ M := hPMM.trans inf_le_left
  have hQM : Q ≤ M := hQle.trans inf_le_left
  -- GAP 1.1: `Q ≠ 1`.
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    have htop : Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [htop, top_le_iff] at hNQ
    exact (mem_maximalSubgroups.mp hMstar).1 hNQ
  -- GAP 1.2: `q ≠ p`.
  have hP_le_cP : P ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr ⟨⟨hPea.comm⟩⟩
  have hqp : q ≠ p := by
    rintro rfl
    have hPQp : IsPGroup q ↥(P ⊔ Q : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hPp hQq hQinv
    have hQeq : Q = (P ⊔ Q : Subgroup G) := hQmax _ (sup_le hPMM hQle) hPQp le_sup_right
    have hP_le_Q : P ≤ Q := le_sup_left.trans hQeq.ge
    have hP_bot : P ≤ ⊥ := hCQ ▸ le_inf hP_le_Q hP_le_cP
    rw [le_bot_iff] at hP_bot
    rw [hP_bot, Subgroup.card_bot] at hPcard
    exact (Fact.out : Nat.Prime q).one_lt.ne hPcard
  -- GAP 1.3: `Q` is a maximal `q`-subgroup of `M`.
  have hQsyl : ∀ T : Subgroup G, T ≤ M → IsPGroup q ↥T → Q ≤ T → Q = T := by
    intro T hTM hTq hQT
    by_contra hne
    have hlt : Q < T := lt_of_le_of_ne hQT hne
    have hgrow := lt_inf_normalizer_of_lt_of_pgroup hTq hlt
    have hNT_le : T ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ Mstar :=
      le_inf (inf_le_left.trans hTM) (inf_le_right.trans hNQ)
    have hNT_q : IsPGroup q ↥(T ⊓ Subgroup.normalizer (Q : Set G)) := hTq.to_le inf_le_left
    exact hgrow.ne (hQmax _ hNT_le hNT_q hgrow.le)
  -- `ℳ(N_G(Q)) ≠ {M}` (since `M* ∈ ℳ(N_G(Q))` and `M* ≠ M`).
  have hMNQ : maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) ≠ {M} := by
    intro hsingle
    have hMstar_mem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Q : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar, hNQ⟩
    rw [hsingle, Set.mem_singleton_iff] at hMstar_mem
    exact hMMstar hMstar_mem.symm
  -- apply Lemma 12.18(b).
  obtain ⟨hαβ, hMαne, hqα, hCMαP, hCMαPQ⟩ :=
    (tau1_Malpha_interaction hG hM hqp hp hP hPM hQM hQne hQq hQinv hCQ hMNQ).2 hQsyl
  exact ⟨hqp, hQne, hαβ, hMαne, hqα, hCMαP, hCMαPQ⟩

/-! ## Lemma 13.8 step 3 — GAP 2 (Hall θ + Theorem 10.1(b) collapse) -/

/-- **Theorem 10.1(b) collapse** (Lemma 13.8 GAP 2.8 の核): `t ∈ σ(M)`, `Y` を `M` の非自明
`t`-部分群で `N_G(Y) ⊆ M` とすると、`Y` を含む任意の極大共役 `M^g` は `M` に等しい。

`C_G(Y)` が `{M^u ∣ Y ≤ M^u}` に推移作用する (Theorem 10.1(b) =
`S10.fusion_control_of_mem_sigma .2.1`) ことから `∃ c ∈ C_G(Y)`, `M^g = M^c`; さらに
`C_G(Y) ⊆ N_G(Y) ⊆ M` ゆえ `c ∈ M` が `M` を固定し `M^g = M`。 -/
theorem conj_eq_self_of_sigma_pSubgroup_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {t : ℕ} [Fact t.Prime]
    (htσ : t ∈ S10.sigma M) {Y : Subgroup G} (hYne : Y ≠ ⊥) (hYt : IsPGroup t ↥Y)
    (hNY : Subgroup.normalizer (Y : Set G) ≤ M) {g : G}
    (hYM : Y ≤ M) (hYg : Y ≤ MulAut.conj g • M) :
    MulAut.conj g • M = M := by
  have hY1 : Y ≤ MulAut.conj (1 : G) • M := by rw [map_one, one_smul]; exact hYM
  obtain ⟨c, hcC, hceq⟩ :=
    (S10.fusion_control_of_mem_sigma hG hM htσ hYne hYt).2.1 g 1 hYg hY1
  rw [map_one, one_smul] at hceq
  have hcM : c ∈ M := hNY ((Subgroup.centralizer_le_normalizer (Y : Set G)) hcC)
  have e1 : MulAut.conj c⁻¹ • (MulAut.conj c • (MulAut.conj g • M)) = MulAut.conj g • M := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  rw [hceq, conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (M.inv_mem hcM))] at e1
  exact e1.symm

/-- **`σ(M)`-prime の `q`-部分群は `M_σ` へ共役** (BG Theorem 10.2 の帰結): `q ∈ σ(M)`, `Y` を
`q`-群とすると、ある `g` で `Y^g ⊆ M_σ`。`M_σ` が `G` の Sylow `q`-部分群を含む
(`isSylow_sylowMap_of_mem_sigma`) ことと Sylow 共役による。Lemma 13.8 GAP 2.5
(`X = O_s(H)` を `M^g` へ入れる) の核。`S12_Corollary1216.pRank_normalizer_le_one` Step 1
のインライン論法を `hM` 直接版に切り出したもの。 -/
theorem exists_conj_smul_le_Msigma_of_pSubgroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {q : ℕ} [Fact q.Prime]
    (hqσ : q ∈ S10.sigma M) {Y : Subgroup G} (hYq : IsPGroup q ↥Y) :
    ∃ g : G, MulAut.conj g • Y ≤ S10.Msigma M := by
  obtain ⟨_, P, _⟩ := (S10.mem_sigma_iff M q).mp hqσ
  obtain ⟨SG, hSG⟩ := S10.isSylow_sylowMap_of_mem_sigma hqσ P
  have hPpi : Ch03.Subgroup.IsPiGroup (S10.sigma M) ((P : Subgroup ↥M).map M.subtype) := by
    intro s hs
    have hs_dvd : s ∣ Nat.card ↥((P : Subgroup ↥M).map M.subtype) :=
      (Nat.mem_primeFactors.mp hs).2.1
    rw [Subgroup.card_map_of_injective M.subtype_injective] at hs_dvd
    obtain ⟨n, hn⟩ := (P.2).exists_card_eq
    rw [hn] at hs_dvd
    rwa [(Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hs) Fact.out).mp
      ((Nat.prime_of_mem_primeFactors hs).dvd_of_dvd_pow hs_dvd)]
  have hPMσ : (P : Subgroup ↥M).map M.subtype ≤ S10.Msigma M :=
    S10.sigma_subgroup_le_Msigma_of_isHall (S10.Msigma_isHall hG hM)
      (Subgroup.map_subtype_le _) hPpi
  obtain ⟨Q, hYQ⟩ := hYq.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SG Q
  refine ⟨g⁻¹, le_trans (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYQ) ?_⟩
  have hQconj : MulAut.conj g⁻¹ • (Q : Subgroup G) = (P : Subgroup ↥M).map M.subtype := by
    have hQ : (Q : Subgroup G) = MulAut.conj g • (SG : Subgroup G) := by
      rw [← hg]; exact Sylow.coe_subgroup_smul
    rw [hQ, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hSG]
  rw [hQconj]; exact hPMσ

/-- **Lemma 13.8 GAP 2 の核 (H ≤ M, M-side, 向き付き)**: `s ∈ β(M)` が `F(H)` を割り、`Y` を
`M ∩ H` の非自明 `β(M)`-部分群 (`t`-群, `t ∈ β(M)`) とすると `H ≤ M`。

`X = O_s(H)` は `H` に characteristic (`H ≤ N_G(X)`) な `s`-群。`s ∈ β(M) ⊆ σ(M)` ゆえ
`exists_conj_smul_le_Msigma_of_pSubgroup` で `X^a ⊆ M_σ ⊆ M`; その `X' = X^a` に Prop 10.14(d)
を `M` 側で適用 (`N_G(X') ⊆ M`) し、共役で戻すと `H ⊆ M^{a⁻¹}`。一方 `Y ⊆ M ∩ M^{a⁻¹}` で
`conj_eq_self_of_sigma_pSubgroup_normalizer_le` (collapse) により `M^{a⁻¹} = M`、ゆえ `H ⊆ M`。

(`Y` は呼出側で `Y = O_t(C_{M_β}(P))` を渡す。β の共役不変性を要しないのが要点。) -/
theorem hall_le_of_fitting_prime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {s : ℕ} [Fact s.Prime]
    (hsβ : s ∈ S10.beta M) {H : Subgroup G}
    (hsF : s ∈ (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors)
    {t : ℕ} [Fact t.Prime] (htβ : t ∈ S10.beta M) {Y : Subgroup G}
    (hYne : Y ≠ ⊥) (hYt : IsPGroup t ↥Y) (hYM : Y ≤ M) (hYH : Y ≤ H) :
    H ≤ M := by
  -- `X = O_s(H)`: nonidentity `s`-group, characteristic in `H`.
  have hXne : opiCoreInG ({s} : Set ℕ) H ≠ ⊥ :=
    Ch2.S08.opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG hsF
  have hHNX : H ≤ Subgroup.normalizer ((opiCoreInG ({s} : Set ℕ) H : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG _ _
  have hXs : IsPGroup s ↥(opiCoreInG ({s} : Set ℕ) H) :=
    isPGroup_of_isPiSubgroup_singleton (isPiSubgroup_opiCoreInG _ _)
  have hsσ : s ∈ S10.sigma M := S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M hsβ)
  -- conjugate `X` into `M_σ`.
  obtain ⟨a, haX⟩ := exists_conj_smul_le_Msigma_of_pSubgroup hG hM hsσ hXs
  have hX'M : MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) ≤ M := haX.trans (S10.Msigma_le M)
  have hX'ne : MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) ≠ ⊥ := by
    intro hb
    apply hXne
    have h := congrArg (fun K => MulAut.conj a⁻¹ • K) hb
    simpa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, Subgroup.smul_bot] using h
  have hX's : IsPGroup s ↥(MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H)) :=
    hXs.of_equiv (Subgroup.equivMapOfInjective _ (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective)
  have hNX'M : Subgroup.normalizer
      ((MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) : Subgroup G) : Set G) ≤ M :=
    S10.normalizer_le_of_nontrivial_beta_subgroup hG hM hX'M hX'ne
      (isPiSubgroup_of_isPGroup_of_mem hX's hsβ)
  -- `conj a • H ≤ N_G(X') ≤ M`, hence `H ≤ M^{a⁻¹}`.
  have hconjH : MulAut.conj a • H ≤ M := by
    have h1 : MulAut.conj a • H ≤
        MulAut.conj a • Subgroup.normalizer ((opiCoreInG ({s} : Set ℕ) H : Subgroup G) : Set G) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hHNX
    have hnorm : MulAut.conj a •
          Subgroup.normalizer ((opiCoreInG ({s} : Set ℕ) H : Subgroup G) : Set G)
        = Subgroup.normalizer
          ((MulAut.conj a • (opiCoreInG ({s} : Set ℕ) H) : Subgroup G) : Set G) :=
      Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj a).bijective
    rw [hnorm] at h1
    exact h1.trans hNX'M
  have hHg : H ≤ MulAut.conj a⁻¹ • M := by
    have hid : MulAut.conj a⁻¹ • (MulAut.conj a • H) = H := by
      rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    calc H = MulAut.conj a⁻¹ • (MulAut.conj a • H) := hid.symm
      _ ≤ MulAut.conj a⁻¹ • M := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hconjH
  -- collapse with `Y`.
  have htσ : t ∈ S10.sigma M := S10.alpha_subset_sigma hG hM (S10.beta_subset_alpha M htβ)
  have hNY : Subgroup.normalizer (Y : Set G) ≤ M :=
    S10.normalizer_le_of_nontrivial_beta_subgroup hG hM hYM hYne
      (isPiSubgroup_of_isPGroup_of_mem hYt htβ)
  have hcollapse : MulAut.conj a⁻¹ • M = M :=
    conj_eq_self_of_sigma_pSubgroup_normalizer_le hG hM htσ hYne hYt hNY hYM (hYH.trans hHg)
  rwa [hcollapse] at hHg

/-- **`C_G(P)` は可解** (`P ≠ 1`): minimal simple `G` の真部分群はすべて可解 (`solvable_of_lt_top`)
ゆえ、`C_G(P) < ⊤` を示せばよい。`C_G(P) = ⊤` なら `P ≤ Z(G)`; `G` 単純で `Z(G) = ⊥`
(`Z(G) = ⊤` なら `G` 可換 → 可解、`notSolvable` に反す) ゆえ `P = ⊥`、仮定に反す。
Lemma 13.8 GAP 2 で `C_G(P)` の Hall θ-部分群を取るのに必要。 -/
theorem centralizer_isSolvable_of_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {P : Subgroup G} (hP : P ≠ ⊥) :
    IsSolvable ↥(Subgroup.centralizer (P : Set G)) := by
  apply hG.solvable_of_lt_top
  rw [lt_top_iff_ne_top]
  intro htop
  rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) inferInstance with hc | hc
  · apply hP
    rw [eq_bot_iff, ← hc]
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer (P : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg x hx).symm
  · apply hG.notSolvable
    apply isSolvable_of_comm
    intro a b
    have ha : a ∈ Subgroup.center G := hc ▸ Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm

/-- **`C_G(P)` の Hall `θ`-部分群で指定 `θ`-部分群 `U` を含むもの** (`P ≠ 1`): 可解群の Hall
D-定理 (`Ch03.hall_D`) を `↥C_G(P)` に適用。Lemma 13.8 GAP 2 で `H ⊇ C_{M_β}(P)` (M 側) /
`H ⊇ C_{M*_β}(P)` (M* 側) を取るのに使う。 -/
theorem exists_hall_theta_ge [Finite G] (hG : IsMinimalSimpleOdd G) {P : Subgroup G} (hP : P ≠ ⊥)
    {θ : Set ℕ} {U : Subgroup G} (hUC : U ≤ Subgroup.centralizer (P : Set G))
    (hUθ : Subgroup.IsPiSubgroup θ U) :
    ∃ H : Subgroup G, H ≤ Subgroup.centralizer (P : Set G) ∧
      Ch03.IsHallSubgroup θ (H.subgroupOf (Subgroup.centralizer (P : Set G))) ∧ U ≤ H := by
  haveI : IsSolvable ↥(Subgroup.centralizer (P : Set G)) := centralizer_isSolvable_of_ne_bot hG hP
  have hcond : ∀ q ∈ (Nat.card ↥(U.subgroupOf (Subgroup.centralizer (P : Set G)))).primeFactors,
      q ∈ θ := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUC).toEquiv] at hq
    exact hUθ q hq
  obtain ⟨H₀, hH₀hall, hUH₀⟩ :=
    Ch03.hall_D (G := ↥(Subgroup.centralizer (P : Set G))) (π := θ)
      (U := U.subgroupOf (Subgroup.centralizer (P : Set G))) hcond
  refine ⟨H₀.map (Subgroup.centralizer (P : Set G)).subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have heq : (H₀.map (Subgroup.centralizer (P : Set G)).subtype).subgroupOf
        (Subgroup.centralizer (P : Set G)) = H₀ :=
      Subgroup.comap_map_eq_self_of_injective
        (Subgroup.centralizer (P : Set G)).subtype_injective H₀
    rw [heq]; exact hH₀hall
  · intro x hxU
    have hxC : x ∈ Subgroup.centralizer (P : Set G) := hUC hxU
    rw [Subgroup.mem_map]
    exact ⟨⟨x, hxC⟩, hUH₀ (Subgroup.mem_subgroupOf.mpr hxU), rfl⟩

/-- **非自明可解部分群の Fitting には素数がある**: `H ≠ 1` が可解なら `F(H) ≠ 1`
(`fitting_ne_bot_of_solvable_nontrivial`) ゆえ `|F(H)|` を割る素数が存在。Lemma 13.8 GAP 2 で
`s ∈ π(F(H))` (X = O_s(H) 用) と `t ∈ π(F(C_{M_β}(P)))` (Y = O_t 用) を取るのに使う。 -/
theorem exists_mem_primeFactors_fittingInG [Finite G] {H : Subgroup G}
    (hHsolv : IsSolvable ↥H) (hH : H ≠ ⊥) :
    ∃ s : ℕ, s ∈ (Nat.card ↥(Ch2.S08.fittingInG H)).primeFactors := by
  haveI := hHsolv
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  have hFne : Ch01.fitting ↥H ≠ ⊥ := Ch01.fitting_ne_bot_of_solvable_nontrivial ↥H
  haveI : Nontrivial ↥(Ch01.fitting ↥H) := (Subgroup.nontrivial_iff_ne_bot _).mpr hFne
  have hcard : Nat.card ↥(Ch2.S08.fittingInG H) = Nat.card ↥(Ch01.fitting ↥H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hgt : 1 < Nat.card ↥(Ch2.S08.fittingInG H) := by
    rw [hcard]; exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨s, hsp, hsd⟩ := (Nat.card ↥(Ch2.S08.fittingInG H)).exists_prime_and_dvd (by omega)
  exact ⟨s, Nat.mem_primeFactors.mpr ⟨hsp, hsd, Nat.card_pos.ne'⟩⟩

/-- **Lemma 13.8 GAP 2 の `r` 抽出** (`H ≤ M` 確立後): `H` を `C_G(P)` の Hall
`(β(M)∪β(M*))`-部分群で `H ≤ M`, `Y₀* = C_{M*_β}(P)` を `C_G(P)` の非自明 `β(M*)`-部分群と
すると、ある素数 `r ∈ β(M*)` が `|C_M(P)|` を割り `r ∉ σ(M)`。

`r ∈ π(Y₀*) ⊆ β(M*)` を取る; `r ∈ θ` かつ `H` Hall θ ゆえ `r ∤ [C:H]` (`index_no_pi`)、
`|C| = |H|·[C:H]` で `r ∣ |H| ∣ |C_M(P)|`。`r ∉ σ(M)` は Lemma 10.12(a)
(`disjoint_of_not_conj`, `α(M*)∩σ(M)=∅`)。 -/
theorem exists_prime_betastar_dvd_of_hall_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hnc' : ¬ ∃ g : G, MulAut.conj g • Mstar = M) {P H : Subgroup G}
    (hHC : H ≤ Subgroup.centralizer (P : Set G)) (hHM : H ≤ M)
    (hHhall : Ch03.IsHallSubgroup (S10.beta M ∪ S10.beta Mstar)
      (H.subgroupOf (Subgroup.centralizer (P : Set G))))
    {Y₀star : Subgroup G} (hY₀starne : Y₀star ≠ ⊥)
    (hY₀starC : Y₀star ≤ Subgroup.centralizer (P : Set G))
    (hY₀starβ : Subgroup.IsPiSubgroup (S10.beta Mstar) Y₀star) :
    ∃ r : ℕ, r.Prime ∧ r ∈ S10.beta Mstar ∧
      r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)) ∧ r ∉ S10.sigma M := by
  haveI : Nontrivial ↥Y₀star := (Subgroup.nontrivial_iff_ne_bot _).mpr hY₀starne
  obtain ⟨r, hrp, hrd⟩ := (Nat.card ↥Y₀star).exists_prime_and_dvd
    (by have := Finite.one_lt_card_iff_nontrivial.mpr ‹Nontrivial ↥Y₀star›; omega)
  have hrβstar : r ∈ S10.beta Mstar :=
    hY₀starβ r (Nat.mem_primeFactors.mpr ⟨hrp, hrd, Nat.card_pos.ne'⟩)
  have hrC : r ∣ Nat.card ↥(Subgroup.centralizer (P : Set G)) :=
    hrd.trans (Subgroup.card_dvd_of_le hY₀starC)
  -- `r ∤ [C:H]` because `r ∈ θ` and `H` is a Hall θ-subgroup.
  have hr_ndvd_idx : ¬ r ∣ (H.subgroupOf (Subgroup.centralizer (P : Set G))).index := by
    intro hdvd
    exact (hHhall.index_no_pi r
      (Nat.mem_primeFactors.mpr ⟨hrp, hdvd, Subgroup.index_ne_zero_of_finite⟩)) (Or.inr hrβstar)
  -- `|C| = |H| · [C:H]`, so `r ∣ |H|`.
  have hcardeq : Nat.card ↥(H.subgroupOf (Subgroup.centralizer (P : Set G))) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv
  have hlag : Nat.card ↥H * (H.subgroupOf (Subgroup.centralizer (P : Set G))).index =
      Nat.card ↥(Subgroup.centralizer (P : Set G)) := by
    rw [← hcardeq]; exact Subgroup.card_mul_index _
  have hrH : r ∣ Nat.card ↥H := by
    rw [← hlag] at hrC
    exact (hrp.dvd_mul.mp hrC).resolve_right hr_ndvd_idx
  have hrMC : r ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (P : Set G)) :=
    hrH.trans (Subgroup.card_dvd_of_le (le_inf hHM hHC))
  have hrσ : r ∉ S10.sigma M := by
    intro hrσM
    have hdisj := (S10.disjoint_of_not_conj hG hMstar hM hnc').1.2
    have hmem : r ∈ S10.alpha Mstar ∩ S10.sigma M :=
      ⟨S10.beta_subset_alpha Mstar hrβstar, hrσM⟩
    rw [hdisj] at hmem
    simpa using hmem
  exact ⟨r, hrp, hrβstar, hrMC, hrσ⟩

/-! ## §13 相互制約と transition (mmd L3630-3699) -/

/-- **BG Lemma 13.8** (mmd L3630): 次の配置は不可能 — `M*∈ℳ` (`M`と非共役),
`p∈τ₁(M)∩τ₁(M*)`, `P∈ℰ_p¹(M∩M*)`, `Q,Q*` を `M∩M*` の `P`-不変 Sylow 部分群
(素数は異なってよい), `C_Q(P)=C_{Q*}(P)=1`, `N_G(Q)⊆M*`, `N_G(Q*)⊆M`。

§10 gates visible for proof-fill: Theorem 10.2's `M'/M_α` nilpotence tail,
`S10.disjoint_of_not_conj` (Lemma 10.12), and
`S10.normalizer_le_of_nontrivial_beta_subgroup` (Prop 10.14(d)). The Hall/Frattini pieces
used through §12 must remain upstream theorem calls, not new hypotheses on this statement. -/
theorem forbidden_config_impossible [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroups G) (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M) (hpstar : p ∈ tau1 Mstar)
    {P : Subgroup G} (hP : P ∈ elemAbelianOfRank G p 1) (hPM : P ≤ M ⊓ Mstar)
    {q qstar : ℕ} [Fact q.Prime] [Fact qstar.Prime] {Q Qstar : Subgroup G}
    (hQle : Q ≤ M ⊓ Mstar) (hQq : IsPGroup q ↥Q)
    (hQmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup q ↥T → Q ≤ T → Q = T)
    (hQstarle : Qstar ≤ M ⊓ Mstar) (hQstarq : IsPGroup qstar ↥Qstar)
    (hQstarmax : ∀ T : Subgroup G, T ≤ M ⊓ Mstar → IsPGroup qstar ↥T → Qstar ≤ T → Qstar = T)
    (hQinv : P ≤ Subgroup.normalizer (Q : Set G))
    (hQstarinv : P ≤ Subgroup.normalizer (Qstar : Set G))
    (hCQ : Q ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hCQstar : Qstar ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hNQ : Subgroup.normalizer (Q : Set G) ≤ Mstar)
    (hNQstar : Subgroup.normalizer (Qstar : Set G) ≤ M) :
    False := by
  sorry

/-- **BG Theorem 13.9** (mmd L3662): `M*∈ℳ` が `M` と非共役なら `σ(M)` と `σ(M*)` は disjoint。 -/
theorem sigma_disjoint_of_nonconjugate [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {Mstar : Subgroup G}
    (hMstar : Mstar ∈ maximalSubgroups G) (hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar) :
    Disjoint (S10.sigma M) (S10.sigma Mstar) := by
  sorry

/-- **BG Theorem 13.10** (mmd L3672; 結論は PDF p.102 から画像読みで復元):
ある `P∈ℰ_p¹(E₁)` が `E₃` を中心化しないなら (a) `E₁` は `E₃` に regular 作用;
(b) `E₃` は `M_σ` に regular 作用; (c) その `P` について `C_{M_σ}(P) ≠ 1`。

§10 gates visible for proof-fill: `S10.normalizer_le_of_nontrivial_beta_subgroup`
(Prop 10.14(d)) supplies `N_G(Q*)⊆M` in the `q*∈β(M)` branch; the remaining branch uses
`σ(M)` by definition. Lemma 12.18 / Lemma 12.19 carry the Cor 10.9 β-complement input. -/
theorem E1_regular_on_E3_of_noncentralize [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    (hP : ∃ p : ℕ, ∃ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 ∧ P ≤ E₁ ∧
      ¬ (P ≤ Subgroup.centralizer (E₃ : Set G))) :
    ActsRegularlyOn E₃ E₁ ∧ ActsRegularlyOn (S10.Msigma M) E₃ ∧
    (∀ p : ℕ, ∀ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 → P ≤ E₁ →
      ¬ (P ≤ Subgroup.centralizer (E₃ : Set G)) →
      S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) := by
  sorry

/-- **BG Corollary 13.11** (mmd L3696; 結論は PDF p.103 から画像読みで復元): `E₃≠1` かつ `E₃` が
`M_σ` に regular 作用しないなら (a) `E₁≠1`; (b) `E=E₁E₃`; (c) `E` は `M_σ` に prime 作用;
(d) すべての `X∈ℰ¹(E)` は `E` で正規。 -/
theorem E3_not_regular_consequences [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE3 : E₃ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn (S10.Msigma M) E₃) :
    E₁ ≠ ⊥ ∧ E = E₁ ⊔ E₃ ∧ ActsPrimeOn (S10.Msigma M) E ∧
    (∀ q : ℕ, ∀ X : Subgroup G, X ∈ elemAbelianOfRank G q 1 → X ≤ E →
      E ≤ Subgroup.normalizer (X : Set G)) := by
  sorry

end OddOrder.BG.Ch3.S13
