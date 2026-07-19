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
(`thm64_of_ih`)・**上流部品**を提供する。**帰納法の二つの場合 (下記) は未証明**なので
Theorem 6.4 本体はまだ得られていない。

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
  **残る数学的内容はすべてこの `step` の側** = BG の場合 1 (`π(F(G)) ⊄ π(H)`) と
  場合 2 (`π(F(G)) ⊆ π(H)`)。

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

end OddOrder.BG.Ch1.S06

