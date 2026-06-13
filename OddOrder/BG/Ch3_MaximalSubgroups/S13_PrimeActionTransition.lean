/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S13_PrimeAction

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

/-! ## §13 prime action の拡張解析 (cont., mmd L3596-3628) -/

/-- **BG Lemma 13.7** (mmd L3596): `E₁≠1` かつ `E₁` が `E₃` に regular 作用しないなら、`E₁E₃` は
`M_σ` に prime 作用。 -/
theorem E1E3_actsPrime [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) (hE1 : E₁ ≠ ⊥)
    (hreg : ¬ ActsRegularlyOn E₃ E₁) :
    ActsPrimeOn (S10.Msigma M) (E₁ ⊔ E₃) := by
  sorry

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
