/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S01_FrattiniBurnside
import OddOrder.GroupTheory.FittingHeredity
import OddOrder.GroupTheory.NormalHallHeredity

/-!
# BG §6: Theorem 6.4 — coprime engine and the centralizing-conjugator step

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
Chapter I §6 (p. 50), mmd `references/bg/local-analysis.mmd` L2011–L2038.

> **Theorem 6.4.** Suppose `G` is a group, `π` is a set of primes, `H` is a `π'`-subgroup of
> `G`, and `G₀` is a normal Hall subgroup of `G`. Assume that `G₀/F(G₀)` and
> `(G/G₀)/F(G/G₀)` are nilpotent. Assume further that `H` normalizes two `π`-subgroups `J₁`
> and `J₂` of `G`. Then there exists an element `x ∈ ⟨J₁, J₂⟩` such that `⟨J₁ˣ, J₂⟩` is a
> `π`-group and `x` centralizes `H`.

**状態**: 本ファイルは Theorem 6.4 の**主張** (`Thm64Statement`)・**帰納骨格**
(`thm64_of_ih`)・reduction「`G = LH` としてよい」(`thm64_of_sup_ne_top`)・
**場合 1 の完全な証明** (`thm64_case_fitting_primes_not_subset`)・上流部品を提供する。
**残るのは場合 2 (`π(F(G)) ⊆ π(H)`) のみ**なので Theorem 6.4 本体はまだ得られていない。

## 帰納骨格 (`|G| + |H|` の強帰納法)

* `Thm64Statement` — 定理の主張そのもの (仮説を含意の連鎖で並べた形)。
* `Thm64IH` — 帰納法の仮定。`OddOrder.Isaacs.Ch09.BartelsIH` と同じく**明示パラメータ**
  にしてあるので, 場合 1 / 場合 2 をそれぞれ単独の定理として書ける。
* `card_add_card_strongInduction` — 測度 `Nat.card G + Nat.card H` に関する強帰納原理。
  群の**型そのもの**を量化してあるので, 部分群 `↥S`・商 `G ⧸ N`・元の `G` という
  型の違う 3 通りの降下を一つの帰納法で扱える (三者とも `G` と同じ universe に留まる)。
* `card_lt_card_of_lt` / `card_quotient_add_card_map_mk'_lt` /
  `card_subgroup_add_card_subgroupOf_lt` — その 3 通りの降下で測度が減ることの証明。
* `thm64_of_ih` — 「`Thm64IH` のもとで主張が言えれば全体が言える」。
  残る数学的内容はこの `step` の側 = BG の場合 1 (`π(F(G)) ⊄ π(H)`, **証明済**) と
  場合 2 (`π(F(G)) ⊆ π(H)`, **未証明**)。

## 場合 1 (`π(F(G)) ⊄ π(H)`) — 証明済

* `thm64_case_fitting_primes_not_subset` / `thm64_case_exists_prime_not_mem` —
  `G = LH` (`J₁ ⊔ J₂ ⊔ H = ⊤`) と帰納法の仮定のもとで, 場合 1 の結論を出す。
  後者は例外素数 `p ∈ π(F(G)) ∖ π(H)` を明示的に取った形。原文は `O_p(F(G))` 内の
  **極小**正規部分群 `N` を取るが, 極小性は証明中で一度も使われない (使うのは
  `N ≠ 1`・`N ⊴ G`・`N` が `p`-群だけ) ので, ここでは `N := O_p(G)` を直接使う。
* その道具立て:
  `mem_normalizer_iff_conj_smul_eq` / `map_conj_smul_eq` / `map_le_normalizer_map` /
  `le_normalizer_sup` / `conj_smul_eq_self_of_mem_centralizer` / `le_normalizer_conj_smul`
  (共役・正規化・中心化の相互作用),
  `isPiSubgroup_conj` / `coprime_card_of_isPiSubgroup_compl` / `isPiSubgroup_of_isPGroup`
  (`π`-性の移送と互いに素性),
  `card_eq_card_mul_card_map_mk'` / `isPiSubgroup_of_map_mk'`
  (`N ⊴ G` に沿った `|P| = |N| · |P/N|` と `π`-性の合成),
  `opCore_ne_bot_of_mem_primeFactors_card_fitting` (`p ∈ π(F(G))` ⟹ `O_p(G) ≠ 1`),
  `exists_conj_smul_eq_of_sup_eq` (Schur–Zassenhaus の共役性; 共役子が `N` に取れる),
  `commutator_mem_of_quotient_centralizes` / `sup_eq_sup_of_map_mk'_eq` (商での計算)。

## reduction 「`G = LH` としてよい」

* `thm64_of_le_proper_subgroup` — `J₁, J₂, H` が真部分群 `S < G` に共に含まれるなら,
  帰納法の仮定を `↥S` の内部で使うだけで結論が出る。仮説 8 個を `↥S` へ移し
  (`NormalHallHeredity` / `FittingHeredity` / `subgroupOf_le_normalizer_subgroupOf`),
  得られた `x` を `S.subtype` で押し戻す。
* `thm64_of_sup_ne_top` — その BG の文言どおりの形 (`S = ⟨J₁, J₂⟩ ⊔ H = LH`)。
  これにより `step` の証明では `G = LH` を仮定してよい。
* `subgroupOf_le_normalizer_subgroupOf` — 正規化の仮説を部分群 `↥S` へ移す段。

## 上流部品

* `exists_centralizing_conj_sup_isPiGroup` — **Prop 1.5(b)+(c) の subgroup 合成形**。
  BG が Theorem 6.4 の場合 1 の最終段で「By Proposition 1.5, there exists `w ∈ C_{L*}(H)`
  such that `⟨J₁^{yzw}, J₂⟩` is a `π`-group」と一行で済ませている推論そのもの。
  作用群 `A` と作用先 `N` の位数が互いに素なとき, `A`-不変な二つの `π`-部分群は
  `C_G(A)` の元による共役で同時に一つの `π`-群へ入る。Theorem 6.4 は本補題の
  「`|A|`, `|N|` が互いに素」という仮定を Hall/Fitting 仮説へ弱めた一般化にあたるので,
  これが場合 1 の実質的なエンジンになる。

* `mem_centralizer_of_mem_normalizer_of_commutator_le` — 場合 1 の
  「`yz` は `H` を中心化する」段 (下記の**誤植訂正**込み)。

* `isSolvable_of_isNilpotent_quotient_fitting_of_normal` — Theorem 6.4 の二つの Fitting 商
  仮説 (`G₀/F(G₀)` と `(G/G₀)/F(G/G₀)` が冪零) から `G` の可解性を導く段。Proposition 1.5
  (場合 1 のエンジン `exists_centralizing_conj_sup_isPiGroup` が使う) が可解性を要求するので
  必要になる。

* `inf_eq_bot_of_isPiSubgroup_compl` — `π'`-部分群と `π`-部分群は交わらない。場合 1 の
  「`H` is a Hall `p'`-subgroup of `HN`」⟹ `H ∩ N = 1` の段で,
  `mem_centralizer_of_mem_normalizer_of_commutator_le` の仮説を供給する。

* `le_of_isPiSubgroup_of_quotient_isPiGroup` — **(6.2)**「`L` contains every `π`-subgroup
  of `G`」。`G/L` が `π'`-群であることから従う。

正規 Hall 部分群の仮説を部分群 `L ⊔ H` と商 `G ⧸ N` へ移す部分は
`OddOrder.GroupTheory.NormalHallHeredity`, Fitting 商の仮説を移す部分は
`OddOrder.GroupTheory.FittingHeredity` にある (どちらも汎用補題なので `GroupTheory/` 側)。
後者の `isNilpotent_quotient_fitting_quotient_subgroupOf` が使う単射性
`QuotientGroup.map_subgroupOf_subtype_injective` は `OddOrder.Mathlib.QuotientGroup`。

## ⚠ 原文の誤植 (p. 50)

BG p. 50 の場合 1 は, `y ∈ L` と `z ∈ N` を取って `H^{yz} = H` としたのち

> `[H, yz] ⊆ H ∩ L = 1.`

と書く (mmd L2031, PDF p. 50 の印字でも同一) が, **`H ∩ L = 1` は仮定から従わない**。
`G = LH` かつ `L ⊴ G` という直前の設定は `G/L ≅ H/(H ∩ L)` を与えるだけで,
`H ∩ L` の自明性は主張していない。

正しくは `L` ではなく `N` で, `[H, yz] ⊆ H ∩ N = 1` である:

* `yz ∈ N_G(H)` より `[H, yz] ⊆ H`;
* `y` が `HN/N` を中心化する (6.3) ので各 `h ∈ H` に対し `h⁻¹ h^y ∈ N`, かつ `z ∈ N` と
  `N ⊴ G` より `h⁻¹ h^{yz} ∈ N`, すなわち `[H, yz] ⊆ N`;
* `N ≤ O_p(F(G))` は `p`-群で `p ∉ π(H)` ゆえ `H ∩ N = 1` — これは BG 自身が直前に
  述べる「`H` is a Hall `p'`-subgroup of `HN`」と同じ内容。

よって結論 (`yz` が `H` を中心化する) は正しく, 証明は `H ∩ L` を `H ∩ N` に読み替えれば
そのまま通る。この訂正版が `mem_centralizer_of_mem_normalizer_of_commutator_le`。
-/

namespace OddOrder.BG.Ch1.S06

open Pointwise
open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-! ## 共役と `subgroupOf` の相互作用 (局所 helper) -/

private theorem subtype_comp_conj_eq {U : Subgroup G} (n' : ↥U) :
    U.subtype.comp ((MulAut.conj n').toMonoidHom) =
      ((MulAut.conj (n'.val : G)).toMonoidHom).comp U.subtype := by
  ext ⟨x, hx⟩; rfl

private theorem map_subtype_conj_subgroupOf {U : Subgroup G} (n' : ↥U) (K : Subgroup G)
    (hKU : K ≤ U) :
    ((K.subgroupOf U).map (MulAut.conj n').toMonoidHom).map U.subtype =
      K.map (MulAut.conj (n'.val : G)).toMonoidHom := by
  rw [Subgroup.map_map, subtype_comp_conj_eq, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hKU]

/-- The pointwise `MulAut.conj` action on a subgroup is the image under the conjugation
homomorphism. -/
theorem conj_smul_eq_map (g : G) (K : Subgroup G) :
    MulAut.conj g • K = K.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]; rfl

/-! ## `π`-部分群性の移送 -/

/-- A subgroup of a `π`-subgroup is a `π`-subgroup (its order divides). -/
theorem isPiSubgroup_of_le [Finite G] {π : Set ℕ} {K P : Subgroup G} (hKP : K ≤ P)
    (hP : Subgroup.IsPiSubgroup π P) : Subgroup.IsPiSubgroup π K := by
  intro p hp
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  exact hP p (Nat.mem_primeFactors.mpr
    ⟨hprime, hdvd.trans (Subgroup.card_dvd_of_le hKP), Nat.card_pos.ne'⟩)

/-- An ambient `π`-subgroup `K ≤ N` becomes a `π`-group inside the subtype `↥N`. -/
theorem isPiGroup_subgroupOf {π : Set ℕ} {N K : Subgroup G} (hKN : K ≤ N)
    (hK : Subgroup.IsPiSubgroup π K) : Ch03.Subgroup.IsPiGroup π (K.subgroupOf N) := by
  intro p hp
  exact hK p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv] at hp)

/-- A `π`-group inside the subtype `↥N` pushes forward to an ambient `π`-subgroup. -/
theorem isPiSubgroup_map_subtype {π : Set ℕ} {N : Subgroup G} {P : Subgroup ↥N}
    (hP : Ch03.Subgroup.IsPiGroup π P) : Subgroup.IsPiSubgroup π (P.map N.subtype) := by
  intro p hp
  exact hP p (by rwa [Subgroup.card_map_of_injective N.subtype_injective] at hp)

/-- The image of a `π`-subgroup under any homomorphism is a `π`-subgroup (its order
divides). -/
theorem isPiSubgroup_map [Finite G] {π : Set ℕ} {H : Type*} [Group H] {P : Subgroup G}
    (f : G →* H) (hP : Subgroup.IsPiSubgroup π P) : Subgroup.IsPiSubgroup π (P.map f) := by
  intro p hp
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  exact hP p (Nat.mem_primeFactors.mpr
    ⟨hprime, hdvd.trans (Subgroup.card_map_dvd P f), Nat.card_pos.ne'⟩)

/-- Every subgroup of a `π`-group is a `π`-subgroup. -/
theorem isPiSubgroup_of_isPiGroup [Finite G] {π : Set ℕ} (P : Subgroup G)
    (h : Ch03.IsPiGroup π G) : Subgroup.IsPiSubgroup π P := by
  intro p hp
  obtain ⟨hprime, hdvd, -⟩ := Nat.mem_primeFactors.mp hp
  exact h p (Nat.mem_primeFactors.mpr
    ⟨hprime, hdvd.trans (Subgroup.card_subgroup_dvd_card P), Nat.card_pos.ne'⟩)

/-! ## `π`-群 と `π'`-群 の交わりは自明 -/

/-- `π`-部分群でも `π'`-部分群でもある部分群は自明。位数が `1` でなければ素因子 `p` を持ち,
`p ∈ π` と `p ∉ π` が同時に成り立って矛盾する。 -/
theorem eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl [Finite G] {π : Set ℕ} {P : Subgroup G}
    (hπ : Subgroup.IsPiSubgroup π P) (hπ' : Subgroup.IsPiSubgroup πᶜ P) : P = ⊥ := by
  by_contra hne
  have hcard : Nat.card ↥P ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq P h)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  have hmem : p ∈ (Nat.card ↥P).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩
  exact (hπ' p hmem) (hπ p hmem)

/-- **`π'`-部分群と `π`-部分群は交わらない**: `H` が `π'`-部分群, `N` が `π`-部分群なら
`H ⊓ N = ⊥`。

BG Theorem 6.4 の場合 1 で「`H` is a Hall `p'`-subgroup of `HN`」から
`H ∩ N = 1` を得る段がまさにこれ (`N ≤ O_p(F(G))` は `p`-群, `p ∉ π(H)`)。
`mem_centralizer_of_mem_normalizer_of_commutator_le` の仮説 `hdisj` を供給する。 -/
theorem inf_eq_bot_of_isPiSubgroup_compl [Finite G] {π : Set ℕ} {H N : Subgroup G}
    (hH : Subgroup.IsPiSubgroup πᶜ H) (hN : Subgroup.IsPiSubgroup π N) : H ⊓ N = ⊥ :=
  eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (isPiSubgroup_of_le inf_le_right hN)
    (isPiSubgroup_of_le inf_le_left hH)

/-- **BG Theorem 6.4 (6.2)** (p. 50): `N ⊴ G` の商 `G/N` が `π'`-群なら, `G` の任意の
`π`-部分群 `P` は `N` に含まれる。

原文は `G = LH` かつ `G/L ≅ H/(H ∩ L)` が `π'`-群であることから
「`L` contains every `π`-subgroup of `G`」を結論する箇所。

証明: 像 `PN/N` は `π`-群 (`|P|` を割る) かつ `π'`-群 (`|G/N|` を割る) なので自明,
すなわち `P ≤ ker (G → G/N) = N`。 -/
theorem le_of_isPiSubgroup_of_quotient_isPiGroup [Finite G] {π : Set ℕ} {N : Subgroup G}
    [N.Normal] (hQ : Ch03.IsPiGroup πᶜ (G ⧸ N)) {P : Subgroup G}
    (hP : Subgroup.IsPiSubgroup π P) : P ≤ N := by
  have himg : P.map (QuotientGroup.mk' N) = ⊥ :=
    eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl (isPiSubgroup_map _ hP)
      (isPiSubgroup_of_isPiGroup _ hQ)
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg

/-! ## BG Proposition 1.5(b)+(c), subgroup 合成形 -/

/-- **BG Proposition 1.5(b)+(c), joint subgroup form** — Theorem 6.4 の場合 1 で使われる
「一手で二つの `π`-部分群を一つの `π`-群に入れる」推論。

`A` が `N` を正規化し `(|A|, |N|) = 1` で `N` が可解, `J₁, J₂ ≤ N` が `A`-不変な
`π`-部分群のとき, ある `w ∈ N ∩ C_G(A)` が存在して `⟨J₁^w, J₂⟩` は `π`-群になる。

証明は BG の一行 (p. 50, "By Proposition 1.5, there exists `w ∈ C_{L*}(H)` such that
`⟨J₁^{yzw}, J₂⟩` is a `π`-group") の展開: Prop 1.5(b)
(`aInvariant_piSubgroup_le_aInvariant_hall`) で `J₁, J₂` をそれぞれ `A`-不変 Hall
`π`-部分群 `P₁, P₂` に入れ, Prop 1.5(c) (`aInvariant_hall_conj`) で `P₁^w = P₂`
(`w` は `A` に固定される = `C_G(A)` の元) とすれば `J₁^w ⊔ J₂ ≤ P₂` で `P₂` は `π`-群。 -/
theorem exists_centralizing_conj_sup_isPiGroup [Finite G] {A N : Subgroup G}
    (hAN : A ≤ Subgroup.normalizer (N : Set G))
    (hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N))
    [IsSolvable ↥N] {π : Set ℕ} {J₁ J₂ : Subgroup G}
    (hJ₁N : J₁ ≤ N) (hJ₁pi : Subgroup.IsPiSubgroup π J₁)
    (hJ₁A : A ≤ Subgroup.normalizer (J₁ : Set G))
    (hJ₂N : J₂ ≤ N) (hJ₂pi : Subgroup.IsPiSubgroup π J₂)
    (hJ₂A : A ≤ Subgroup.normalizer (J₂ : Set G)) :
    ∃ w : G, w ∈ N ∧ w ∈ Subgroup.centralizer (A : Set G) ∧
      Subgroup.IsPiSubgroup π ((MulAut.conj w • J₁) ⊔ J₂) := by
  classical
  letI act : MulDistribMulAction ↥A ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hAN)
  set φ : ↥A →* MulAut ↥N := MulDistribMulAction.toMulAut ↥A ↥N with hφ
  have hφ_coe : ∀ (a : ↥A) (x : ↥N), ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  -- `A`-invariance transports to `subgroupOf N`.
  have htr : ∀ K : Subgroup G, A ≤ Subgroup.normalizer (K : Set G) →
      Ch03.IsAInvariant φ (K.subgroupOf N) := by
    intro K hK
    rw [Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    rw [hφ_coe a x]
    exact (Subgroup.mem_normalizer_iff.mp (hK a.2) (x : G)).mp hx
  -- Prop 1.5(b) twice: invariant Hall `π`-overgroups of `J₁`, `J₂` inside `↥N`.
  obtain ⟨P₁, hP₁hall, hP₁inv, hJ₁P₁⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥N) (A := ↥A) (φ := φ) hcop (isPiGroup_subgroupOf hJ₁N hJ₁pi) (htr J₁ hJ₁A)
  obtain ⟨P₂, hP₂hall, hP₂inv, hJ₂P₂⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (G := ↥N) (A := ↥A) (φ := φ) hcop (isPiGroup_subgroupOf hJ₂N hJ₂pi) (htr J₂ hJ₂A)
  -- Prop 1.5(c): an `A`-fixed conjugator `c ∈ ↥N` carrying `P₁` onto `P₂`.
  obtain ⟨c, hc_fix, hc_conj⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_hall_conj (G := ↥N) (A := ↥A) (φ := φ)
      hcop hP₁hall hP₂hall hP₁inv hP₂inv
  refine ⟨(c : G), c.2, ?_, ?_⟩
  · -- `c` is fixed by every `a ∈ A`, i.e. `c ∈ C_G(A)`.
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hval : ((φ ⟨a, ha⟩) c : G) = (c : G) :=
      congrArg (fun z : ↥N => (z : G)) (hc_fix ⟨a, ha⟩)
    rw [hφ_coe ⟨a, ha⟩ c] at hval
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `J₁^c ⊔ J₂ ≤ P₂.map N.subtype`, which is a `π`-subgroup.
    have hP₂amb : Subgroup.IsPiSubgroup π (P₂.map N.subtype) :=
      isPiSubgroup_map_subtype hP₂hall.1
    refine isPiSubgroup_of_le (sup_le ?_ ?_) hP₂amb
    · -- the conjugate of `J₁`
      have hstep : (J₁.subgroupOf N).map (MulAut.conj c).toMonoidHom ≤ P₂ := by
        have h1 : (J₁.subgroupOf N).map (MulAut.conj c).toMonoidHom
            ≤ P₁.map (MulAut.conj c).toMonoidHom := Subgroup.map_mono hJ₁P₁
        have h2 : P₁.map (MulAut.conj c).toMonoidHom = P₂ :=
          (conj_smul_eq_map c P₁).symm.trans hc_conj
        rwa [h2] at h1
      calc MulAut.conj (c : G) • J₁
          = J₁.map (MulAut.conj (c : G)).toMonoidHom := conj_smul_eq_map _ _
        _ = ((J₁.subgroupOf N).map (MulAut.conj c).toMonoidHom).map N.subtype :=
            (map_subtype_conj_subgroupOf c J₁ hJ₁N).symm
        _ ≤ P₂.map N.subtype := Subgroup.map_mono hstep
    · -- `J₂` itself
      calc J₂ = (J₂.subgroupOf N).map N.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hJ₂N).symm
        _ ≤ P₂.map N.subtype := Subgroup.map_mono hJ₂P₂

/-! ## 場合 1 の中心化段 (原文 `H ∩ L = 1` の誤植訂正版) -/

/-- **BG Theorem 6.4, 場合 1 の `yz ∈ C_G(H)` 段** (p. 50; 原文の `H ∩ L = 1` を
`H ∩ N = 1` に訂正したもの — ファイル冒頭の注記参照)。

`N ⊴ G` と `H ⊓ N = ⊥` を仮定し, `t ∈ N_G(H)` が各 `h ∈ H` について
`h⁻¹ · h^t ∈ N` を満たすなら, `t` は `H` を中心化する。

証明: `h ∈ H` に対し `h^t ∈ H` (`t` は `H` を正規化する) ゆえ `h⁻¹ h^t ∈ H`, 仮定より
`h⁻¹ h^t ∈ N`, よって `h⁻¹ h^t ∈ H ⊓ N = ⊥`, すなわち `h^t = h`。

BG での適用: `t = yz`, `N ≤ O_p(F(G))`, `H` は `p'`-群なので `H ⊓ N = ⊥` (BG が
「`H` is a Hall `p'`-subgroup of `HN`」と述べる箇所), そして `h⁻¹ h^{yz} ∈ N` は
(6.3) の「`y` は `HN/N` を中心化する」と `z ∈ N`, `N ⊴ G` から従う。 -/
theorem mem_centralizer_of_mem_normalizer_of_commutator_le {N H : Subgroup G}
    (hdisj : H ⊓ N = ⊥) {t : G} (htH : t ∈ Subgroup.normalizer (H : Set G))
    (hcomm : ∀ h ∈ H, h⁻¹ * (t⁻¹ * h * t) ∈ N) :
    t ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hconjH : t⁻¹ * h * t ∈ H := (Subgroup.mem_normalizer_iff''.mp htH h).mp hh
  have hmemH : h⁻¹ * (t⁻¹ * h * t) ∈ H := H.mul_mem (H.inv_mem hh) hconjH
  have hbot : h⁻¹ * (t⁻¹ * h * t) ∈ (⊥ : Subgroup G) := by
    rw [← hdisj]; exact ⟨hmemH, hcomm h hh⟩
  rw [Subgroup.mem_bot, inv_mul_eq_one] at hbot
  -- `h = t⁻¹ * h * t` gives `h * t = t * h`.
  have h3 : t * h = h * t :=
    calc t * h = t * (t⁻¹ * h * t) := by rw [← hbot]
      _ = h * t := by group
  exact h3.symm

/-! ## Fitting 商の冪零性からの可解性 (Proposition 1.5 を呼ぶための前提) -/

/-- **Fitting 長 `≤ 2` の有限群は可解**: `X/F(X)` が冪零なら `X` は可解。

`F(X)` は冪零 (`Isaacs.Ch01.fitting.isNilpotent`) ゆえ可解, 仮定より `X/F(X)` も冪零ゆえ
可解, そして可解群による可解群の拡大は可解 (`solvable_of_ker_le_range` を
`F(X) ↪ X ↠ X/F(X)` に適用; `ker (mk' F(X)) = F(X) = range F(X).subtype`)。 -/
theorem isSolvable_of_isNilpotent_quotient_fitting {X : Type*} [Group X] [Finite X]
    (h : Group.IsNilpotent (X ⧸ Ch01.fitting X)) : IsSolvable X := by
  haveI := h
  haveI : Group.IsNilpotent ↥(Ch01.fitting X) := Ch01.fitting.isNilpotent
  refine solvable_of_ker_le_range (Ch01.fitting X).subtype
    (QuotientGroup.mk' (Ch01.fitting X)) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/-- **BG Theorem 6.4 の可解性の段**: `N ⊴ X` について `N/F(N)` と `(X/N)/F(X/N)` が
ともに冪零なら `X` は可解。

Theorem 6.4 の仮説はまさに `N = G₀` に対するこの形 (`G₀` は `G` の正規 Hall 部分群で
`G₀/F(G₀)` と `(G/G₀)/F(G/G₀)` が冪零) なので, 本補題が場合 1 のエンジンである
Proposition 1.5 (`exists_centralizing_conj_sup_isPiGroup` の `[IsSolvable ↥N]` 仮説) を
使えるようにする。

証明: `isSolvable_of_isNilpotent_quotient_fitting` を `↥N` と `X ⧸ N` に適用して
`IsSolvable ↥N`, `IsSolvable (X ⧸ N)` を得, 再び `solvable_of_ker_le_range` を
`N ↪ X ↠ X/N` に適用する。Hall 性はここでは不要。 -/
theorem isSolvable_of_isNilpotent_quotient_fitting_of_normal {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal]
    (hN : Group.IsNilpotent (↥N ⧸ Ch01.fitting ↥N))
    (hQ : Group.IsNilpotent ((X ⧸ N) ⧸ Ch01.fitting (X ⧸ N))) :
    IsSolvable X := by
  haveI : IsSolvable ↥N := isSolvable_of_isNilpotent_quotient_fitting hN
  haveI : IsSolvable (X ⧸ N) := isSolvable_of_isNilpotent_quotient_fitting hQ
  refine solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

/-! ## 帰納法の測度 `|G| + |H|` とその減少 -/

/-- 有限群の真部分群のあいだでも位数は真に減る: `K < H` なら `|K| < |H|`。

`K.subgroupOf H ≠ ⊤` を経由して `Ch04.subgroup_card_lt_of_ne_top` を `↥H` の中で使い,
`Subgroup.subgroupOfEquivOfLe` で `|K.subgroupOf H| = |K|` に戻す。 -/
theorem card_lt_card_of_lt [Finite G] {K H : Subgroup G} (hlt : K < H) :
    Nat.card ↥K < Nat.card ↥H := by
  have hne : K.subgroupOf H ≠ ⊤ := fun htop =>
    hlt.ne (le_antisymm hlt.le (Subgroup.subgroupOf_eq_top.mp htop))
  have hcard : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hlt.le).toEquiv
  have := Ch04.subgroup_card_lt_of_ne_top (G := ↥H) hne
  omega

/-- **場合 1 の測度減少**: `1 ≠ N ⊴ G` について, 商へ降りた対 `(G ⧸ N, HN/N)` の測度
`|G/N| + |HN/N|` は `|G| + |H|` より真に小さい。

`|G/N| < |G|` は `N ≠ 1` から, `|HN/N| ≤ |H|` は像の位数が整除することから。 -/
theorem card_quotient_add_card_map_mk'_lt [Finite G] {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥)
    (H : Subgroup G) :
    Nat.card (G ⧸ N) + Nat.card ↥(H.map (QuotientGroup.mk' N)) < Nat.card G + Nat.card ↥H := by
  have h1 : Nat.card (G ⧸ N) < Nat.card G := Subgroup.card_quotient_lt_of_ne_bot hN
  have h2 : Nat.card ↥(H.map (QuotientGroup.mk' N)) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd H _)
  omega

/-- **reduction step (`G = LH` としてよい) の測度減少**: 真部分群 `S < G` について,
部分群へ降りた対 `(↥S, H ⊓ S)` の測度 `|S| + |H ⊓ S|` は `|G| + |H|` より真に小さい。

`|S| < |G|` は `S ≠ ⊤` から, `|H.subgroupOf S| ≤ |H|` は `H.subgroupOf S = H.comap S.subtype`
が `S.subtype` 単射ゆえ `H` に埋め込まれることから (`Subgroup.card_comap_dvd_of_injective`)。 -/
theorem card_subgroup_add_card_subgroupOf_lt [Finite G] {S : Subgroup G} (hS : S ≠ ⊤)
    (H : Subgroup G) :
    Nat.card ↥S + Nat.card ↥(H.subgroupOf S) < Nat.card G + Nat.card ↥H := by
  have h1 : Nat.card ↥S < Nat.card G := Ch04.subgroup_card_lt_of_ne_top hS
  have h2 : Nat.card ↥(H.subgroupOf S) ≤ Nat.card ↥H :=
    Nat.le_of_dvd Nat.card_pos
      (Subgroup.card_comap_dvd_of_injective H S.subtype S.subtype_injective)
  omega

/-! ## `|G| + |H|` に関する強帰納法 -/

universe u

/-- **測度 `|G| + |H|` に関する強帰納法**: 群の型 `G` と部分群 `H` の対を
`Nat.card G + Nat.card H` で整列させた強帰納原理。

BG Theorem 6.4 の帰納法は次の 3 通りの降下を行うが, いずれも **`G` と同じ universe に
留まる** (`↥S : Type u`, `G ⧸ N : Type u`) ので, ℕ 上の強帰納法に落とせる:

* 部分群への降下 `↥(L ⊔ H)` (「`G = LH` としてよい」の reduction) —
  `card_subgroup_add_card_subgroupOf_lt`,
* 商への降下 `G ⧸ N` (`N` は `O_p(F(G))` 内の極小正規部分群; 場合 1) —
  `card_quotient_add_card_map_mk'_lt`,
* `G` はそのままで `H` を真部分群 `H*` に取り替える降下 (場合 2) — `card_lt_card_of_lt`。

三者は型が違う (`↥S` / `G ⧸ N` / `G`) ため, **群の型そのものを量化した** 形でしか
帰納法は回らない。`motive` を `∀ (G : Type u) [Group G] [Finite G], Subgroup G → Prop`
と取るのがその形。 -/
theorem card_add_card_strongInduction
    {motive : ∀ (X : Type u) [Group X] [Finite X], Subgroup X → Prop}
    (step : ∀ (X : Type u) [Group X] [Finite X] (H : Subgroup X),
      (∀ (Y : Type u) [Group Y] [Finite Y] (H' : Subgroup Y),
          Nat.card Y + Nat.card ↥H' < Nat.card X + Nat.card ↥H → motive Y H') →
        motive X H)
    (X : Type u) [Group X] [Finite X] (H : Subgroup X) : motive X H := by
  suffices h : ∀ n : ℕ, ∀ (Y : Type u) [Group Y] [Finite Y] (H' : Subgroup Y),
      Nat.card Y + Nat.card ↥H' = n → motive Y H' from h _ X H rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y _ _ H' hcard
    exact step Y H' fun Z _ _ H'' hlt => ih _ (hcard ▸ hlt) Z H'' rfl

/-! ## Theorem 6.4 の statement と帰納骨格 -/

/-- **BG Theorem 6.4 の主張** (p. 50), 与えられたデータ `(G, π, H, G₀, J₁, J₂)` に対する形。

> `H` が `π'`-部分群, `G₀` が正規 Hall 部分群で `G₀/F(G₀)` と `(G/G₀)/F(G/G₀)` が冪零,
> `H` が `π`-部分群 `J₁, J₂` を正規化するとき, ある `x ∈ ⟨J₁, J₂⟩` が存在して
> `⟨J₁ˣ, J₂⟩` は `π`-群で `x` は `H` を中心化する。

* 「`G₀` が Hall 部分群」は `π` に依らない綴り `Nat.Coprime |G₀| [G:G₀]` で書く
  (`OddOrder.GroupTheory.NormalHallHeredity` と同じ convention)。
* 共役は本ファイルの他の補題と同じく左作用 `MulAut.conj x • J₁ = x J₁ x⁻¹` を使う。
  BG の `J₁ˣ = x⁻¹ J₁ x` とは `x ↦ x⁻¹` の違いだけで, `x ∈ ⟨J₁,J₂⟩` も
  `x ∈ C_G(H)` も逆元で閉じているので主張は同値。 -/
def Thm64Statement {X : Type*} [Group X] [Finite X] (π : Set ℕ) (H G₀ J₁ J₂ : Subgroup X)
    [G₀.Normal] : Prop :=
  Subgroup.IsPiSubgroup πᶜ H →
  Nat.Coprime (Nat.card ↥G₀) G₀.index →
  Group.IsNilpotent (↥G₀ ⧸ Ch01.fitting ↥G₀) →
  Group.IsNilpotent ((X ⧸ G₀) ⧸ Ch01.fitting (X ⧸ G₀)) →
  Subgroup.IsPiSubgroup π J₁ →
  Subgroup.IsPiSubgroup π J₂ →
  H ≤ Subgroup.normalizer (J₁ : Set X) →
  H ≤ Subgroup.normalizer (J₂ : Set X) →
  ∃ x ∈ J₁ ⊔ J₂, Subgroup.IsPiSubgroup π ((MulAut.conj x • J₁) ⊔ J₂) ∧
    x ∈ Subgroup.centralizer (H : Set X)

/-- **BG Theorem 6.4 の帰納法の仮定**: 測度 `|G'| + |H'|` が `|G| + |H|` より真に小さい
すべての対で Theorem 6.4 が成り立つ, という主張。

`OddOrder.Isaacs.Ch09.BartelsIH` と同じ設計で, 帰納法の仮定を**明示パラメータ**にして
おくことで, 証明の各場合 (BG の場合 1 / 場合 2) をそれぞれ**単独で sorry-free な定理**
として書けるようにする。帰納法自体は `thm64_of_ih` が閉じる。 -/
def Thm64IH (X : Type u) [Group X] [Finite X] (H : Subgroup X) : Prop :=
  ∀ (Y : Type u) [Group Y] [Finite Y] (H' : Subgroup Y),
    Nat.card Y + Nat.card ↥H' < Nat.card X + Nat.card ↥H →
    ∀ (π : Set ℕ) (G₀ : Subgroup Y) [G₀.Normal] (J₁ J₂ : Subgroup Y),
      Thm64Statement π H' G₀ J₁ J₂

/-- **Theorem 6.4 の帰納骨格**: 「帰納法の仮定 `Thm64IH G H` のもとで `(G, H)` について
主張が成り立つ」を示せば, すべての `(G, H)` について主張が従う。

`card_add_card_strongInduction` を motive
`fun G _ _ H => ∀ π G₀ J₁ J₂, Thm64Statement π H G₀ J₁ J₂` に適用しただけ。
**数学的内容はすべて `step` の側にある** — 現状 `step` は未証明で, BG の
場合 1 (`π(F(G)) ⊄ π(H)`) と場合 2 (`π(F(G)) ⊆ π(H)`) がそれぞれ残っている。 -/
theorem thm64_of_ih
    (step : ∀ (X : Type u) [Group X] [Finite X] (H : Subgroup X), Thm64IH X H →
      ∀ (π : Set ℕ) (G₀ : Subgroup X) [G₀.Normal] (J₁ J₂ : Subgroup X),
        Thm64Statement π H G₀ J₁ J₂)
    (X : Type u) [Group X] [Finite X] (π : Set ℕ) (H G₀ : Subgroup X) [G₀.Normal]
    (J₁ J₂ : Subgroup X) : Thm64Statement π H G₀ J₁ J₂ := by
  revert π G₀ J₁ J₂
  refine card_add_card_strongInduction
    (motive := fun Y _ _ H' => ∀ (π : Set ℕ) (G₀ : Subgroup Y) [G₀.Normal] (J₁ J₂ : Subgroup Y),
      Thm64Statement π H' G₀ J₁ J₂) ?_ X H
  intro Y _ _ H' hIH
  exact step Y H' (fun Z _ _ H'' hlt => hIH Z H'' hlt)

/-! ## reduction 「`G = LH` としてよい」 -/

/-- `H` が `K` を正規化するなら, 任意の部分群 `S` の内部でも `H.subgroupOf S` は
`K.subgroupOf S` を正規化する。

`↥S` の元の積・逆元は台のそれ (`Subgroup.coe_mul`, `Subgroup.coe_inv`) なので,
`Subgroup.mem_normalizer_iff` の同値がそのまま `subgroupOf` の言葉に移る。
`S` については何も仮定しない (`H ≤ S` すら要らない — `H.subgroupOf S` は `H ⊓ S` を見るだけ)。 -/
theorem subgroupOf_le_normalizer_subgroupOf {S H K : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (K : Set G)) :
    H.subgroupOf S ≤ Subgroup.normalizer ((K.subgroupOf S : Subgroup ↥S) : Set ↥S) := by
  intro x hx
  have hxG : (x : G) ∈ Subgroup.normalizer (K : Set G) := hH (Subgroup.mem_subgroupOf.mp hx)
  rw [Subgroup.mem_normalizer_iff]
  intro n
  simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp hxG (n : G)

/-- **BG Theorem 6.4 の reduction「`G = LH` と仮定してよい」の一般形** (p. 50, mmd L2015)。

`J₁`, `J₂`, `H` がどれも**真**部分群 `S < G` に含まれるなら, 帰納法の仮定を `↥S` の内部で
使うだけで Theorem 6.4 の結論が `G` について得られる。

証明は二段:

1. **仮説 8 個を `↥S` へ移す**。`π`-部分群性は `isPiGroup_subgroupOf`, 正規 Hall 性は
   `OddOrder.GroupTheory.normal_coprime_card_index_subgroupOf`, `G₀` 側の Fitting 商は
   `↥(G₀.subgroupOf S) ≃* ↥(G₀ ⊓ S)` (`MulEquiv.subgroupCongr` と
   `Subgroup.subgroupOfEquivOfLe`) を挟んで
   `OddOrder.GroupTheory.isNilpotent_quotient_fitting_of_le` (`G₀ ⊓ S ≤ G₀`),
   商側の Fitting 商は
   `OddOrder.GroupTheory.isNilpotent_quotient_fitting_quotient_subgroupOf`,
   正規化は `subgroupOf_le_normalizer_subgroupOf`。測度 `|S| + |H ⊓ S|` が
   `|G| + |H|` より小さいことは `card_subgroup_add_card_subgroupOf_lt`。
2. **結論を `S.subtype` で押し戻す**。`x ∈ J₁ ⊔ J₂` は `Subgroup.map_subgroupOf_eq_of_le`,
   `π`-群性は `isPiSubgroup_map` と `map_subtype_conj_subgroupOf` (共役と `subgroupOf` の
   交換), 中心化は `↥S` の積が台の積であることから。 -/
theorem thm64_of_le_proper_subgroup {X : Type u} [Group X] [Finite X] (π : Set ℕ)
    (H G₀ J₁ J₂ S : Subgroup X) [G₀.Normal] (hIH : Thm64IH X H)
    (hJ₁S : J₁ ≤ S) (hJ₂S : J₂ ≤ S) (hHS : H ≤ S) (hSne : S ≠ ⊤) :
    Thm64Statement π H G₀ J₁ J₂ := by
  intro hH hG₀hall hG₀nil hQnil hJ₁pi hJ₂pi hJ₁norm hJ₂norm
  -- ## 1. 仮説を `↥S` へ移す
  have hmeas : Nat.card ↥S + Nat.card ↥(H.subgroupOf S) < Nat.card X + Nat.card ↥H :=
    card_subgroup_add_card_subgroupOf_lt hSne H
  have hH' : Subgroup.IsPiSubgroup πᶜ (H.subgroupOf S) := isPiGroup_subgroupOf hHS hH
  have hJ₁pi' : Subgroup.IsPiSubgroup π (J₁.subgroupOf S) := isPiGroup_subgroupOf hJ₁S hJ₁pi
  have hJ₂pi' : Subgroup.IsPiSubgroup π (J₂.subgroupOf S) := isPiGroup_subgroupOf hJ₂S hJ₂pi
  have hG₀hall' : Nat.Coprime (Nat.card ↥(G₀.subgroupOf S)) (G₀.subgroupOf S).index :=
    (OddOrder.GroupTheory.normal_coprime_card_index_subgroupOf hG₀hall S).2
  have hG₀nil' : Group.IsNilpotent (↥(G₀.subgroupOf S) ⧸ Ch01.fitting ↥(G₀.subgroupOf S)) := by
    -- `G₀ ⊓ S ≤ G₀` の遺伝を `↥(G₀.subgroupOf S) ≃* ↥(G₀ ⊓ S)` で移す。
    have e : ↥(G₀.subgroupOf S) ≃* ↥(G₀ ⊓ S) :=
      (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right G₀ S)).symm.trans
        (Subgroup.subgroupOfEquivOfLe inf_le_right)
    exact OddOrder.GroupTheory.isNilpotent_quotient_fitting_of_injective e.toMonoidHom
      e.injective (OddOrder.GroupTheory.isNilpotent_quotient_fitting_of_le inf_le_left hG₀nil)
  have hQnil' : Group.IsNilpotent
      ((↥S ⧸ G₀.subgroupOf S) ⧸ Ch01.fitting (↥S ⧸ G₀.subgroupOf S)) :=
    OddOrder.GroupTheory.isNilpotent_quotient_fitting_quotient_subgroupOf S G₀ hQnil
  have hJ₁norm' : H.subgroupOf S ≤
      Subgroup.normalizer ((J₁.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
    subgroupOf_le_normalizer_subgroupOf hJ₁norm
  have hJ₂norm' : H.subgroupOf S ≤
      Subgroup.normalizer ((J₂.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
    subgroupOf_le_normalizer_subgroupOf hJ₂norm
  -- ## 2. 帰納法の仮定を `↥S` の内部で使う
  obtain ⟨x, hxmem, hxpi, hxc⟩ :=
    hIH ↥S (H.subgroupOf S) hmeas π (G₀.subgroupOf S) (J₁.subgroupOf S) (J₂.subgroupOf S)
      hH' hG₀hall' hG₀nil' hQnil' hJ₁pi' hJ₂pi' hJ₁norm' hJ₂norm'
  -- ## 3. 結論を `S.subtype` に沿って押し戻す
  refine ⟨(x : X), ?_, ?_, ?_⟩
  · -- `x ∈ J₁ ⊔ J₂`: `⊔` は `map` と交換し, `J₁ ≤ S`, `J₂ ≤ S` で `subgroupOf` が戻る。
    have hmapsup : ((J₁.subgroupOf S) ⊔ (J₂.subgroupOf S)).map S.subtype = J₁ ⊔ J₂ := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJ₁S,
        Subgroup.map_subgroupOf_eq_of_le hJ₂S]
    rw [← hmapsup]
    exact Subgroup.mem_map_of_mem S.subtype hxmem
  · -- `⟨J₁ˣ, J₂⟩` が `π`-群: 像は `π`-部分群 (`isPiSubgroup_map`) で, その像を計算する。
    have hconj : (MulAut.conj x • J₁.subgroupOf S).map S.subtype = MulAut.conj (x : X) • J₁ := by
      rw [conj_smul_eq_map, map_subtype_conj_subgroupOf x J₁ hJ₁S, conj_smul_eq_map]
    have hmap : ((MulAut.conj x • J₁.subgroupOf S) ⊔ J₂.subgroupOf S).map S.subtype
        = (MulAut.conj (x : X) • J₁) ⊔ J₂ := by
      rw [Subgroup.map_sup, hconj, Subgroup.map_subgroupOf_eq_of_le hJ₂S]
    have hpi := isPiSubgroup_map (π := π) S.subtype hxpi
    rwa [hmap] at hpi
  · -- `x ∈ C_G(H)`: `↥S` の中での可換性を台へ落とす。
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hmem : (⟨h, hHS hh⟩ : ↥S) ∈ ((H.subgroupOf S : Subgroup ↥S) : Set ↥S) :=
      Subgroup.mem_subgroupOf.mpr hh
    simpa using congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hxc _ hmem)

/-- **BG Theorem 6.4 の reduction「`G = LH` としてよい」** (p. 50, mmd L2015):

> Since `H` normalizes `J₁` and `J₂`, `H` normalizes `L`. We can assume that `G = LH`.

`L := ⟨J₁, J₂⟩ = J₁ ⊔ J₂` は `H` に正規化されるので `S := L ⊔ H` は積 `LH` に他ならない。
`S ≠ G` のときは帰納法の仮定を `↥S` の内部で使えば結論が出る
(`thm64_of_le_proper_subgroup`) ので, 帰納法の各場合を証明するときは `S = G`,
すなわち `G = LH` を仮定してよい。

なお Lean の部分群束では `J₁ ⊔ J₂ ⊔ H` は無条件に部分群なので, 原文が `H` による `L` の
正規化から `LH` が部分群であることを導く段は形式化の上では不要になる (正規化の仮説は
代わりに `hJ₁norm`, `hJ₂norm` を `↥S` へ移す段で使われる)。 -/
theorem thm64_of_sup_ne_top {X : Type u} [Group X] [Finite X] (π : Set ℕ)
    (H G₀ J₁ J₂ : Subgroup X) [G₀.Normal] (hIH : Thm64IH X H)
    (hne : J₁ ⊔ J₂ ⊔ H ≠ ⊤) : Thm64Statement π H G₀ J₁ J₂ :=
  thm64_of_le_proper_subgroup π H G₀ J₁ J₂ (J₁ ⊔ J₂ ⊔ H) hIH
    (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left) le_sup_right hne



/-! ## 場合 1 の道具立て: 共役・正規化・`π`-性の相互作用 -/

/-- `g ∈ N_G(K)` ⟺ `g` による共役が `K` を保つ。

mathlib の `Subgroup.mem_normalizer_iff_map_conj_eq` を本ファイルで使う `MulAut.conj` の
点ごと作用の綴りに直しただけのもの。 -/
theorem mem_normalizer_iff_conj_smul_eq {K : Subgroup G} {g : G} :
    g ∈ Subgroup.normalizer (K : Set G) ↔ MulAut.conj g • K = K := by
  rw [conj_smul_eq_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq

/-- 準同型は共役作用と交換する: `f (g K g⁻¹) = f g · f K · (f g)⁻¹`。 -/
theorem map_conj_smul_eq {G' : Type*} [Group G'] (f : G →* G') (g : G) (K : Subgroup G) :
    (MulAut.conj g • K).map f = MulAut.conj (f g) • K.map f := by
  rw [conj_smul_eq_map, conj_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

/-- 正規化の仮説は準同型の像へ移る: `H ≤ N_G(K)` なら `f H ≤ N_{G'}(f K)`。

場合 1 で帰納法の仮定を `G ⧸ N` で使うとき, 仮説 `H ≤ N_G(J₁)`, `H ≤ N_G(J₂)` を
商へ運ぶのに要る。 -/
theorem map_le_normalizer_map {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : H ≤ Subgroup.normalizer (K : Set G)) :
    H.map f ≤ Subgroup.normalizer ((K.map f : Subgroup G') : Set G') := by
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_normalizer_iff_conj_smul_eq, ← map_conj_smul_eq,
    mem_normalizer_iff_conj_smul_eq.mp (h hx)]

/-- 二つの部分群を正規化する部分群は, その join も正規化する。

BG が「`H` normalizes `J₁` and `J₂`, hence `H` normalizes `L = ⟨J₁, J₂⟩`」と述べる段
(p. 50, mmd L2015)。 -/
theorem le_normalizer_sup {H J₁ J₂ : Subgroup G}
    (h₁ : H ≤ Subgroup.normalizer (J₁ : Set G)) (h₂ : H ≤ Subgroup.normalizer (J₂ : Set G)) :
    H ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup G) : Set G) := fun _ hx =>
  Subgroup.normalizer_inf_normalizer_le_normalizer_sup J₁ J₂ ⟨h₁ hx, h₂ hx⟩

/-- `K` を中心化する元による共役は `K` 上恒等, したがって `K` を保つ。 -/
theorem conj_smul_eq_self_of_mem_centralizer {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (K : Set G)) : MulAut.conj g • K = K := by
  have hfix : ∀ k ∈ K, g * k * g⁻¹ = k := by
    intro k hk
    have hk' : k * g = g * k := Subgroup.mem_centralizer_iff.mp hg k hk
    rw [← hk']
    group
  rw [conj_smul_eq_map]
  refine le_antisymm ?_ fun x hx => ⟨x, hx, hfix x hx⟩
  rintro _ ⟨k, hk, rfl⟩
  change g * k * g⁻¹ ∈ K
  rw [hfix k hk]
  exact hk

/-- `t` が `H` を中心化し `H` が `J` を正規化するなら, `H` は共役 `t J t⁻¹` も正規化する。

BG p. 50 の場合 1 で「Thus `yz` centralizes `H`. Hence `H` normalizes `J₁^{yz}`」と
述べる段。 -/
theorem le_normalizer_conj_smul {H J : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.centralizer (H : Set G))
    (hJ : H ≤ Subgroup.normalizer (J : Set G)) :
    H ≤ Subgroup.normalizer ((MulAut.conj t • J : Subgroup G) : Set G) := by
  intro h hh
  rw [mem_normalizer_iff_conj_smul_eq, ← mul_smul]
  have hcomm : MulAut.conj h * MulAut.conj t = MulAut.conj t * MulAut.conj h := by
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp ht h hh]
  rw [hcomm, mul_smul, mem_normalizer_iff_conj_smul_eq.mp (hJ hh)]

/-- `π`-部分群の共役はまた `π`-部分群。 -/
theorem isPiSubgroup_conj [Finite G] {π : Set ℕ} {K : Subgroup G} (g : G)
    (hK : Subgroup.IsPiSubgroup π K) : Subgroup.IsPiSubgroup π (MulAut.conj g • K) := by
  rw [conj_smul_eq_map]
  exact isPiSubgroup_map _ hK

/-- `π'`-部分群と `π`-部分群の位数は互いに素。素因子集合が交わらないことを
`Nat.disjoint_primeFactors` で互いに素へ翻訳する。 -/
theorem coprime_card_of_isPiSubgroup_compl [Finite G] {σ : Set ℕ} {A B : Subgroup G}
    (hA : Subgroup.IsPiSubgroup σᶜ A) (hB : Subgroup.IsPiSubgroup σ B) :
    Nat.Coprime (Nat.card ↥A) (Nat.card ↥B) := by
  rw [← Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne', Finset.disjoint_left]
  intro q hqA hqB
  exact hA q hqA (hB q hqB)

/-- `p`-群は `{p}`-部分群。 -/
theorem isPiSubgroup_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hK : IsPGroup p K) : Subgroup.IsPiSubgroup ({p} : Set ℕ) K := by
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  intro q hq
  rw [hn] at hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  simp only [Set.mem_singleton_iff]
  exact (Nat.prime_dvd_prime_iff_eq hqprime Fact.out).mp
    (hqprime.dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hq))

/-! ## `N ⊴ G ≤ P` に沿った位数の分解 -/

/-- **Lagrange の三段形**: `N ⊴ G` と `N ≤ P` について `|P| = |N| · |P N / N|`。

`(N.subgroupOf P).index = |P/N|` は mathlib の `Subgroup.relIndex_ker`
(`ker f` の相対指数が像の位数に等しい) を `f = QuotientGroup.mk' N` に適用したもの。 -/
theorem card_eq_card_mul_card_map_mk' [Finite G] {N P : Subgroup G} [N.Normal] (hNP : N ≤ P) :
    Nat.card ↥P = Nat.card ↥N * Nat.card ↥(P.map (QuotientGroup.mk' N)) := by
  have hidx : (N.subgroupOf P).index = Nat.card ↥(P.map (QuotientGroup.mk' N)) := by
    have h := Subgroup.relIndex_ker (QuotientGroup.mk' N) (K := P)
    rw [QuotientGroup.ker_mk'] at h
    exact h
  have hcard : Nat.card ↥(N.subgroupOf P) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  have hmul := Subgroup.card_mul_index (N.subgroupOf P)
  rw [hcard, hidx] at hmul
  exact hmul.symm

/-- `N ⊴ G` が `σ`-群で商 `P/N` も `σ`-群なら `P` 自身が `σ`-群。

BG p. 50 の場合 1 で「By (6.3), `L*` has order relatively prime to the order of `H`」を
得る段で使う (`L* / N` は `π`-群, `N` は `p`-群, `H` は `π'`-群かつ `p ∤ |H|`)。 -/
theorem isPiSubgroup_of_map_mk' [Finite G] {σ : Set ℕ} {N P : Subgroup G} [N.Normal]
    (hNP : N ≤ P) (hN : Subgroup.IsPiSubgroup σ N)
    (hPq : Subgroup.IsPiSubgroup σ (P.map (QuotientGroup.mk' N))) :
    Subgroup.IsPiSubgroup σ P := by
  intro q hq
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hdvd : q ∣ Nat.card ↥N * Nat.card ↥(P.map (QuotientGroup.mk' N)) := by
    rw [← card_eq_card_mul_card_map_mk' hNP]
    exact Nat.dvd_of_mem_primeFactors hq
  rcases (Nat.Prime.dvd_mul hqprime).mp hdvd with h | h
  · exact hN q (Nat.mem_primeFactors.mpr ⟨hqprime, h, Nat.card_pos.ne'⟩)
  · exact hPq q (Nat.mem_primeFactors.mpr ⟨hqprime, h, Nat.card_pos.ne'⟩)

/-! ## 場合 1 の入力: `p ∈ π(F(G))` から非自明な正規 `p`-部分群 -/

/-- `p` が `|F(G)|` を割るなら `O_p(G) ≠ 1`。

`F(G)` は冪零 (`Ch01.fitting.isNilpotent`) なので Sylow `p`-部分群 `P` は `F(G)` で
正規 (`Ch01.Sylow.normal_of_isNilpotent`), したがって特性的
(`Sylow.characteristic_of_normal`), したがって像 `P ≤ G` は `F(G) ⊴ G` を経て `G` で正規。
`p`-群ゆえ Isaacs Problem 1B.2 (`Ch01.normal_pgroup_le_opCore`) で `O_p(G)` に入り,
`|P| = p^{v_p(|F(G)|)} > 1` なので `O_p(G) ≠ 1`。

BG p. 50 の場合 1 が「Let `N` be a minimal normal subgroup of `G` contained in
`O_p(F(G))`」と述べる箇所の入力。なお原文は極小性を要求するが, **場合 1 の証明は
`N` の極小性を一度も使わない** (使うのは `N ≠ 1`・`N ⊴ G`・`N` が `p`-群の三点だけ)
ので, ここでは `O_p(G)` をそのまま採る。`O_p(F(G)) = O_p(G)` なので同じものである。 -/
theorem opCore_ne_bot_of_mem_primeFactors_card_fitting [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(Ch01.fitting G)).primeFactors) : Ch01.opCore p G ≠ ⊥ := by
  classical
  haveI : Group.IsNilpotent ↥(Ch01.fitting G) := Ch01.fitting.isNilpotent
  set P : Sylow p ↥(Ch01.fitting G) := default with hPdef
  haveI hPnormal : (P : Subgroup ↥(Ch01.fitting G)).Normal := Ch01.Sylow.normal_of_isNilpotent P
  haveI : (P : Subgroup ↥(Ch01.fitting G)).Characteristic :=
    Sylow.characteristic_of_normal _ hPnormal
  haveI : (((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype)).Normal :=
    inferInstance
  have hle : (P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype ≤ Ch01.opCore p G :=
    Ch01.normal_pgroup_le_opCore (P.2.map (Ch01.fitting G).subtype)
  -- `|P| = p ^ v_p(|F(G)|) > 1`
  have hPcard : Nat.card ↥(P : Subgroup ↥(Ch01.fitting G))
      = p ^ (Nat.card ↥(Ch01.fitting G)).factorization p := P.card_eq_multiplicity
  have hpos : 0 < (Nat.card ↥(Ch01.fitting G)).factorization p :=
    Nat.Prime.factorization_pos_of_dvd Fact.out (Nat.card_pos.ne')
      (Nat.dvd_of_mem_primeFactors hp)
  have hPone : Nat.card ↥(P : Subgroup ↥(Ch01.fitting G)) ≠ 1 := by
    rw [hPcard]
    exact Nat.ne_of_gt (Nat.one_lt_pow hpos.ne' (Fact.out : p.Prime).one_lt)
  intro hbot
  refine hPone ?_
  have hmapbot : (P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype = ⊥ :=
    le_bot_iff.mp (hbot ▸ hle)
  have hcardmap : Nat.card ↥((P : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype)
      = Nat.card ↥(P : Subgroup ↥(Ch01.fitting G)) :=
    Subgroup.card_map_of_injective (Ch01.fitting G).subtype_injective
  rw [hmapbot, Subgroup.card_bot] at hcardmap
  exact hcardmap.symm

/-! ## 場合 1 の Schur-Zassenhaus 段 -/

/-- **同じ `N`-剰余をもつ二つの補群は `N` の元で共役** (Schur-Zassenhaus の共役性)。

`N ⊴ G` について `H ⊓ N = K ⊓ N = 1` かつ `H N = K N` なら, `H` と `K` は共に
`HN` の中で `N` の補群なので, ある `z ∈ N` で `z K z⁻¹ = H`。

BG p. 50 の場合 1 の「In this case, `H` is a Hall `p'`-subgroup of `HN`.
Take `z ∈ N` such that `(H^y)^z = H`」の段。共役子が `N` の内部に取れることが
本質的 (`Subgroup.IsComplement'.exists_conj_of_coprime` はそれを与える)。 -/
theorem exists_conj_smul_eq_of_sup_eq [Finite G] {N H K : Subgroup G} [N.Normal]
    (hsolv : IsSolvable ↥N) (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥H))
    (hHN : H ⊓ N = ⊥) (hKN : K ⊓ N = ⊥) (hsup : H ⊔ N = K ⊔ N) :
    ∃ z ∈ N, MulAut.conj z • K = H := by
  classical
  have hHU : H ≤ H ⊔ N := le_sup_left
  have hNU : N ≤ H ⊔ N := le_sup_right
  have hKU : K ≤ H ⊔ N := hsup ▸ le_sup_left
  haveI : (N.subgroupOf (H ⊔ N)).Normal := (inferInstance : N.Normal).subgroupOf _
  -- `↥(H ⊔ N)` の中で `H`, `K` はともに `N` の補群
  have hcompl : ∀ A : Subgroup G, A ≤ H ⊔ N → A ⊓ N = ⊥ → A ⊔ N = H ⊔ N →
      Subgroup.IsComplement' (N.subgroupOf (H ⊔ N)) (A.subgroupOf (H ⊔ N)) := by
    intro A hAU hAN hAsup
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      refine le_antisymm (fun x hx => ?_) bot_le
      obtain ⟨hxN, hxA⟩ := Subgroup.mem_inf.mp hx
      have hx1 : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hAN]
        exact ⟨Subgroup.mem_subgroupOf.mp hxA, Subgroup.mem_subgroupOf.mp hxN⟩
      exact Subgroup.mem_bot.mpr (Subtype.ext (Subgroup.mem_bot.mp hx1))
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hNU hAU, sup_comm N A, hAsup,
        Subgroup.subgroupOf_self]
      exact Subgroup.coe_top
  have hcomplH := hcompl H hHU hHN rfl
  have hcomplK := hcompl K hKU hKN hsup.symm
  -- 位数と指数の互いに素性
  have hcardN : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNU).toEquiv
  have hcardH : Nat.card ↥(H.subgroupOf (H ⊔ N)) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHU).toEquiv
  have hidx : (N.subgroupOf (H ⊔ N)).index = Nat.card ↥H := by
    rw [hcomplH.symm.index_eq_card, hcardH]
  have hcop' : Nat.Coprime (Nat.card ↥(N.subgroupOf (H ⊔ N)))
      (N.subgroupOf (H ⊔ N)).index := by
    rw [hcardN, hidx]; exact hcop
  haveI : IsSolvable ↥N := hsolv
  haveI : IsSolvable ↥(N.subgroupOf (H ⊔ N)) :=
    solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNU).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNU).injective
  obtain ⟨n, hnN, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop' (Or.inl inferInstance) hcomplK hcomplH
  refine ⟨(n : G), Subgroup.mem_subgroupOf.mp hnN, ?_⟩
  have hpush : ((K.subgroupOf (H ⊔ N)).map (MulAut.conj n).toMonoidHom).map (H ⊔ N).subtype
      = (H.subgroupOf (H ⊔ N)).map (H ⊔ N).subtype := by rw [hnconj]
  rw [map_subtype_conj_subgroupOf n K hKU, Subgroup.map_subgroupOf_eq_of_le hHU] at hpush
  rw [conj_smul_eq_map]
  exact hpush

/-! ## 場合 1 の交換子計算 -/

/-- `z ∈ N` かつ `yN` が `HN/N` を中心化するなら, `t = z y` は各 `h ∈ H` について
`h⁻¹ h^t ∈ N` を満たす。

BG p. 50 の場合 1 で `mem_centralizer_of_mem_normalizer_of_commutator_le` の仮説
`hcomm` を供給する段。計算はすべて商 `G ⧸ N` の中で行う: `zN = 1` ゆえ `tN = yN` で,
`yN` は `hN` と可換だから `(h⁻¹ h^t)N = 1`。 -/
theorem commutator_mem_of_quotient_centralizes {N H : Subgroup G} [N.Normal] {y z : G}
    (hz : z ∈ N)
    (hy : (QuotientGroup.mk' N) y ∈ Subgroup.centralizer
      ((H.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :
    ∀ h ∈ H, h⁻¹ * ((z * y)⁻¹ * h * (z * y)) ∈ N := by
  intro h hh
  have hzq : (QuotientGroup.mk' N) z = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hz
  have hhq : (QuotientGroup.mk' N) h ∈ H.map (QuotientGroup.mk' N) :=
    Subgroup.mem_map_of_mem _ hh
  have hcomm : (QuotientGroup.mk' N) h * (QuotientGroup.mk' N) y
      = (QuotientGroup.mk' N) y * (QuotientGroup.mk' N) h :=
    Subgroup.mem_centralizer_iff.mp hy _ hhq
  have hgoal : (QuotientGroup.mk' N) (h⁻¹ * ((z * y)⁻¹ * h * (z * y))) = 1 := by
    simp only [map_mul, map_inv, hzq, one_mul]
    calc ((QuotientGroup.mk' N) h)⁻¹ *
            (((QuotientGroup.mk' N) y)⁻¹ * (QuotientGroup.mk' N) h * (QuotientGroup.mk' N) y)
        = ((QuotientGroup.mk' N) h)⁻¹ *
            (((QuotientGroup.mk' N) y)⁻¹ *
              ((QuotientGroup.mk' N) h * (QuotientGroup.mk' N) y)) := by group
      _ = ((QuotientGroup.mk' N) h)⁻¹ *
            (((QuotientGroup.mk' N) y)⁻¹ *
              ((QuotientGroup.mk' N) y * (QuotientGroup.mk' N) h)) := by rw [hcomm]
      _ = 1 := by group
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hgoal

/-- `A N/N = B N/N` なら `A N = B N`。`ker (G → G/N) = N ≤ A ⊔ N` なので
`A ⊔ N = (A N/N) の逆像` であることによる。 -/
theorem sup_eq_sup_of_map_mk'_eq {N A B : Subgroup G} [N.Normal]
    (h : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) : A ⊔ N = B ⊔ N := by
  have key : ∀ C : Subgroup G,
      C ⊔ N = (C.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    intro C
    have hker : (QuotientGroup.mk' N).ker ≤ C ⊔ N := by
      rw [QuotientGroup.ker_mk']; exact le_sup_right
    have hbot : N.map (QuotientGroup.mk' N) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' N).symm)
    conv_lhs => rw [← Subgroup.comap_map_eq_self hker]
    rw [Subgroup.map_sup, hbot, sup_bot_eq]
  rw [key A, key B, h]


/-! ## BG Theorem 6.4 の場合 1 (`π(F(G)) ⊄ π(H)`) -/

/-- **BG Theorem 6.4, 場合 1** (p. 50, mmd L2019–L2035), 例外素数 `p` を明示した形。

`G = LH` (`hsup`, 一般の場合は `thm64_of_sup_ne_top` で還元済) を仮定した帰納段のうち,
`π(F(G)) ⊄ π(H)` の場合。原文の段どりに沿った証明:

1. `H` が `J₁, J₂` を正規化するので `L := ⟨J₁, J₂⟩` も正規化し, `G = LH` より `L ⊴ G`
   (`le_normalizer_sup` + `Subgroup.normalizer_eq_top_iff`)。
2. `N := O_p(G)` は非自明な正規 `p`-部分群
   (`opCore_ne_bot_of_mem_primeFactors_card_fitting`)。原文は `O_p(F(G))` 内の**極小**
   正規部分群を取るが, 極小性は場合 1 の証明で一度も使われない (使うのは `N ≠ 1`・
   `N ⊴ G`・`N` が `p`-群の三点だけ) ので `O_p(G) = O_p(F(G))` をそのまま採る。
3. `G/L ≅ H/(H ∩ L)` は `p'`-群なので **(6.2)** で `N ≤ L`
   (`le_of_isPiSubgroup_of_quotient_isPiGroup`)。
4. 仮説 8 個を `G ⧸ N` へ移して帰納法の仮定を使う (`NormalHallHeredity` の
   `normal_coprime_card_index_map_mk'`, `FittingHeredity` の
   `isNilpotent_quotient_fitting_of_surjective`, `map_le_normalizer_map`)。測度減少は
   `card_quotient_add_card_map_mk'_lt`。得られる `y ∈ L` が **(6.3)**
   「`⟨J₁ʸ, J₂⟩N/N` は `π`-群で `y` は `HN/N` を中心化する」を満たす。
5. `H` は `HN` の Hall `p'`-部分群なので Schur–Zassenhaus の共役性で `z ∈ N` を取り
   `z (y H y⁻¹) z⁻¹ = H` (`exists_conj_smul_eq_of_sup_eq`)。
6. `t := zy` は `H` を中心化する (`mem_centralizer_of_mem_normalizer_of_commutator_le`)。
   ⚠ この段の原文 `[H, yz] ⊆ H ∩ L = 1` は誤植で, 正しくは `H ∩ N = 1` —
   ファイル冒頭の注記を参照。
7. `L* := ⟨J₁ᵗ, J₂⟩N` は `H` に正規化され (`le_normalizer_conj_smul`), `L*/N` が `π`-群・
   `N` が `p`-群なので `|L*|` は `|H|` と互いに素 (`isPiSubgroup_of_map_mk'` +
   `coprime_card_of_isPiSubgroup_compl`)。よって Proposition 1.5
   (`exists_centralizing_conj_sup_isPiGroup`) が `w ∈ C_{L*}(H)` を与える。
8. `x := wt` が求める元 (`L* ≤ L` と `t ∈ L` から `x ∈ L`, 中心化元の積は中心化元)。 -/
theorem thm64_case_exists_prime_not_mem {X : Type u} [Group X] [Finite X] (π : Set ℕ)
    (H G₀ J₁ J₂ : Subgroup X) [G₀.Normal] (hIH : Thm64IH X H)
    (hsup : J₁ ⊔ J₂ ⊔ H = ⊤) {p : ℕ}
    (hpF : p ∈ (Nat.card ↥(Ch01.fitting X)).primeFactors)
    (hpH : p ∉ (Nat.card ↥H).primeFactors) :
    Thm64Statement π H G₀ J₁ J₂ := by
  intro hH hG₀hall hG₀nil hQnil hJ₁pi hJ₂pi hJ₁norm hJ₂norm
  classical
  haveI hpfact : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hpF⟩
  haveI hXsolv : IsSolvable X :=
    isSolvable_of_isNilpotent_quotient_fitting_of_normal G₀ hG₀nil hQnil
  -- `H` は `p ∉ π(H)` ゆえ `{p}'`-部分群
  have hHp : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ H := by
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl
    exact hpH hq
  -- ## 1. `L := ⟨J₁, J₂⟩` は `G = LH` ゆえ `G` で正規
  have hHnormL : H ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup X) : Set X) :=
    le_normalizer_sup hJ₁norm hJ₂norm
  haveI hLnormal : (J₁ ⊔ J₂ : Subgroup X).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← top_le_iff, ← hsup]
    exact sup_le Subgroup.le_normalizer hHnormL
  -- ## 2. `N := O_p(G)` は非自明な正規 `p`-部分群で `H ⊓ N = ⊥`
  obtain ⟨N, hNnormal, hNp, hNne⟩ :
      ∃ N : Subgroup X, N.Normal ∧ Subgroup.IsPiSubgroup ({p} : Set ℕ) N ∧ N ≠ ⊥ :=
    ⟨Ch01.opCore p X, Ch01.opCore.normal p X,
      isPiSubgroup_of_isPGroup (Ch01.opCore_isPGroup p X),
      opCore_ne_bot_of_mem_primeFactors_card_fitting hpF⟩
  haveI : N.Normal := hNnormal
  have hHN : H ⊓ N = ⊥ := inf_eq_bot_of_isPiSubgroup_compl hHp hNp
  -- ## 3. (6.2): `G/L` は `H` の像なので `p'`-群, ゆえに `N ≤ L`
  have hHmapL : H.map (QuotientGroup.mk' (J₁ ⊔ J₂)) = ⊤ := by
    have h1 : ((J₁ ⊔ J₂) ⊔ H).map (QuotientGroup.mk' (J₁ ⊔ J₂)) = ⊤ := by
      rw [hsup]
      exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
    have hbot : (J₁ ⊔ J₂).map (QuotientGroup.mk' (J₁ ⊔ J₂)) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' _).symm)
    rwa [Subgroup.map_sup, hbot, bot_sup_eq] at h1
  have hNL : N ≤ J₁ ⊔ J₂ := by
    refine le_of_isPiSubgroup_of_quotient_isPiGroup (π := ({p} : Set ℕ)) ?_ hNp
    have h1 : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (H.map (QuotientGroup.mk' (J₁ ⊔ J₂))) :=
      isPiSubgroup_map _ hHp
    rw [hHmapL] at h1
    intro q hq
    exact h1 q (by rwa [Subgroup.card_top])
  -- ## 4. `G ⧸ N` で帰納法の仮定 — (6.3)
  haveI hG₀mapnormal : (G₀.map (QuotientGroup.mk' N)).Normal :=
    (OddOrder.GroupTheory.normal_coprime_card_index_map_mk' inferInstance hG₀hall N).1
  have hmeas : Nat.card (X ⧸ N) + Nat.card ↥(H.map (QuotientGroup.mk' N))
      < Nat.card X + Nat.card ↥H := card_quotient_add_card_map_mk'_lt hNne H
  have hG₀nil' : Group.IsNilpotent
      (↥(G₀.map (QuotientGroup.mk' N)) ⧸ Ch01.fitting ↥(G₀.map (QuotientGroup.mk' N))) :=
    OddOrder.GroupTheory.isNilpotent_quotient_fitting_of_surjective
      ((QuotientGroup.mk' N).subgroupMap G₀)
      (MonoidHom.subgroupMap_surjective _ _) hG₀nil
  have hlecomap : G₀ ≤ (G₀.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) :=
    Subgroup.map_le_iff_le_comap.mp le_rfl
  have hQnil' : Group.IsNilpotent
      (((X ⧸ N) ⧸ G₀.map (QuotientGroup.mk' N)) ⧸
        Ch01.fitting ((X ⧸ N) ⧸ G₀.map (QuotientGroup.mk' N))) := by
    refine OddOrder.GroupTheory.isNilpotent_quotient_fitting_of_surjective
      (QuotientGroup.map G₀ (G₀.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N) hlecomap)
      ?_ hQnil
    intro q
    obtain ⟨q', rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q'
    exact ⟨QuotientGroup.mk x, rfl⟩
  obtain ⟨ybar, hybarmem, hybarpi, hybarc⟩ :=
    hIH (X ⧸ N) (H.map (QuotientGroup.mk' N)) hmeas π (G₀.map (QuotientGroup.mk' N))
      (J₁.map (QuotientGroup.mk' N)) (J₂.map (QuotientGroup.mk' N))
      (isPiSubgroup_map _ hH)
      (OddOrder.GroupTheory.normal_coprime_card_index_map_mk' inferInstance hG₀hall N).2
      hG₀nil' hQnil'
      (isPiSubgroup_map _ hJ₁pi) (isPiSubgroup_map _ hJ₂pi)
      (map_le_normalizer_map _ hJ₁norm) (map_le_normalizer_map _ hJ₂norm)
  rw [← Subgroup.map_sup] at hybarmem
  obtain ⟨y, hyL, rfl⟩ := hybarmem
  -- ## 5. Schur–Zassenhaus: `z ∈ N` で `z (y H y⁻¹) z⁻¹ = H`
  have hconjHmap : (MulAut.conj y • H).map (QuotientGroup.mk' N)
      = H.map (QuotientGroup.mk' N) := by
    rw [map_conj_smul_eq, conj_smul_eq_self_of_mem_centralizer hybarc]
  obtain ⟨z, hzN, hzconj⟩ :=
    exists_conj_smul_eq_of_sup_eq (N := N) (H := H) (K := MulAut.conj y • H) inferInstance
      (coprime_card_of_isPiSubgroup_compl hHp hNp).symm hHN
      (inf_eq_bot_of_isPiSubgroup_compl (isPiSubgroup_conj y hHp) hNp)
      (sup_eq_sup_of_map_mk'_eq hconjHmap).symm
  -- ## 6. `t = zy` は `H` を中心化する (原文の `H ∩ L = 1` は `H ∩ N = 1` の誤植)
  have htconj : MulAut.conj (z * y) • H = H := by
    rw [map_mul, mul_smul, hzconj]
  have htc : z * y ∈ Subgroup.centralizer (H : Set X) :=
    mem_centralizer_of_mem_normalizer_of_commutator_le hHN
      (mem_normalizer_iff_conj_smul_eq.mpr htconj)
      (commutator_mem_of_quotient_centralizes hzN hybarc)
  have htL : z * y ∈ (J₁ ⊔ J₂ : Subgroup X) := (J₁ ⊔ J₂).mul_mem (hNL hzN) hyL
  -- ## 7. `L* = ⟨J₁ᵗ, J₂⟩N` に Proposition 1.5 を当てる
  have hJ₁tpi : Subgroup.IsPiSubgroup π (MulAut.conj (z * y) • J₁) :=
    isPiSubgroup_conj _ hJ₁pi
  have hJ₁tnorm : H ≤ Subgroup.normalizer ((MulAut.conj (z * y) • J₁ : Subgroup X) : Set X) :=
    le_normalizer_conj_smul htc hJ₁norm
  have hNnormH : H ≤ Subgroup.normalizer (N : Set X) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hNnormal]
    exact le_top
  have hLstarnorm : H ≤ Subgroup.normalizer
      (((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X) : Set X) :=
    le_normalizer_sup (le_normalizer_sup hJ₁tnorm hJ₂norm) hNnormH
  have hzq : (QuotientGroup.mk' N) z = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hzN
  have hLstarmap : ((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X).map
        (QuotientGroup.mk' N)
      = (MulAut.conj ((QuotientGroup.mk' N) y) • J₁.map (QuotientGroup.mk' N))
          ⊔ J₂.map (QuotientGroup.mk' N) := by
    have hbot : N.map (QuotientGroup.mk' N) = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr (le_of_eq (QuotientGroup.ker_mk' N).symm)
    rw [Subgroup.map_sup, Subgroup.map_sup, hbot, sup_bot_eq, map_conj_smul_eq, map_mul, hzq,
      one_mul]
  have hLstarpi : Subgroup.IsPiSubgroup (π ∪ ({p} : Set ℕ))
      ((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X) := by
    refine isPiSubgroup_of_map_mk' le_sup_right (hNp.mono Set.subset_union_right) ?_
    rw [hLstarmap]
    exact hybarpi.mono Set.subset_union_left
  have hcop : Nat.Coprime (Nat.card ↥H)
      (Nat.card ↥((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X)) := by
    refine coprime_card_of_isPiSubgroup_compl ?_ hLstarpi
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff, not_or]
    exact ⟨hH q hq, hHp q hq⟩
  haveI : IsSolvable ↥((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X) := inferInstance
  obtain ⟨w, hwmem, hwc, hwpi⟩ :=
    exists_centralizing_conj_sup_isPiGroup (A := H)
      (N := ((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X)) hLstarnorm hcop
      (J₁ := MulAut.conj (z * y) • J₁) (J₂ := J₂)
      (le_sup_left.trans le_sup_left) hJ₁tpi hJ₁tnorm
      (le_sup_right.trans le_sup_left) hJ₂pi hJ₂norm
  -- ## 8. `x := w t`
  have hLstarL : ((MulAut.conj (z * y) • J₁) ⊔ J₂ ⊔ N : Subgroup X) ≤ J₁ ⊔ J₂ := by
    refine sup_le (sup_le ?_ le_sup_right) hNL
    calc MulAut.conj (z * y) • J₁
        ≤ MulAut.conj (z * y) • (J₁ ⊔ J₂ : Subgroup X) :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr le_sup_left
      _ = J₁ ⊔ J₂ := Subgroup.Normal.conj_smul_eq_self _ _
  refine ⟨w * (z * y), (J₁ ⊔ J₂).mul_mem (hLstarL hwmem) htL, ?_, ?_⟩
  · rw [map_mul, mul_smul]
    exact hwpi
  · exact (Subgroup.centralizer (H : Set X)).mul_mem hwc htc

/-- **BG Theorem 6.4, 場合 1** (p. 50) — 原文どおりの場合分けの綴り `π(F(G)) ⊄ π(H)`。

`thm64_case_exists_prime_not_mem` に例外素数を渡すだけ。 -/
theorem thm64_case_fitting_primes_not_subset {X : Type u} [Group X] [Finite X] (π : Set ℕ)
    (H G₀ J₁ J₂ : Subgroup X) [G₀.Normal] (hIH : Thm64IH X H)
    (hsup : J₁ ⊔ J₂ ⊔ H = ⊤)
    (hnotsub : ¬ (Nat.card ↥(Ch01.fitting X)).primeFactors ⊆ (Nat.card ↥H).primeFactors) :
    Thm64Statement π H G₀ J₁ J₂ := by
  obtain ⟨p, hpF, hpH⟩ := Finset.not_subset.mp hnotsub
  exact thm64_case_exists_prime_not_mem π H G₀ J₁ J₂ hIH hsup hpF hpH


end OddOrder.BG.Ch1.S06
