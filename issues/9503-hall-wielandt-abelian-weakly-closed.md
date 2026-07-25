---
id: 9503
slug: hall-wielandt-abelian-weakly-closed
title: "Hall-Wielandt (p>2, A abelian weakly closed) — Pf II (17) 用"
created: 2026-07-26
---

# Hall-Wielandt (p>2, A abelian weakly closed) — Pf II (17) 用

## 🔒 CLAIM (shared infra, hub band 9500)

**claimed by: main/hub session (issue 2053 = Pf Part II Ch.II Theorem B の駆動)**、
2026-07-26。着手前に他レーンが同種の infra を建てていないか
`ls issues/9*.md` + `grep -rn "weakly closed\|Hall.Wielandt" OddOrder/` で実測済
(2026-07-26 時点でヒット無し。既存の近縁は下記「repo 実測」の 2 件のみ)。

## 背景

Peterfalvi Part II Ch.II step (17) (p. 114) の結論が使う唯一の未形式化 infra:

> The subgroup `Z₁PΣ` of `G` is thus weakly closed in `R₂` and, as `Z₁PΣ` is abelian,
> we obtain `G/O³(G) ≅ R₂⟨s⟩/O³(R₂⟨s⟩)` by the Hall-Wielandt Theorem.

statement (Peterfalvi p. 108 に明記、[Ha] Thm 14.4.2):

> `P` を Sylow `p`、`A` を `P` 内で `G` に関し weakly closed とする。
> `A ⊆ Z_{p−1}(P)` または (`p > 2` かつ `A` abelian) ならば
> `G/O^p(G) ≅ N_G(A)/O^p(N_G(A))`。

(17) が要るのは **`p > 2` ∧ `A` abelian** の枝 (`A = Z₁PΣ` は位数 27 の初等可換、
`p = 3`)。`A ⊆ Z_{p−1}(P)` 枝は不要。

## repo 実測 (2026-07-26)

- ✅ `OddOrder.Isaacs.Ch10.transfer_range_eq_of_nilpotencyClass_lt`
  (`Isaacs/Ch10_MoreTransfer/Yoshida.lean:509`, "Hall-Wielandt strengthening via
  Yoshida"): **class(Sylow) < p** のときの版。step (12) が実際に消費している
  (`StepTwelveTransfer.lean:125`) が、(17) では Sylow = `R₂` の class が
  `< 3` とは限らない (`R̄₁ = R₁/Z₁` が class ≤ 2 ⟹ `R₁` は class ≤ 3) ので**使えない**。
- ✅ transfer 基盤一式: `OddOrder.GroupTheory.transfer_range_le` /
  `transfer_transfer` / `transferRes` / `transfer_abelianization_range_eq_bot`
  ((B2) から G-transfer 自明を出す部品、step (12) が使用) /
  `MackeyTransfer.lean` / `TransferInvariantTransversal.lean` (step (9) 用)。
- ❌ weakly closed の定義そのもの、Grün の第二定理、focal subgroup の一般形は無い
  (`grep "weakly closed\|weaklyClosed"` はヒット無し。Isaacs は演習 5C.6 のみで
  本文に無い)。

## やること

- [ ] `weaklyClosed` の定義 (`A ≤ P` かつ `∀ g, A^g ≤ P → A^g = A`) を
      `OddOrder/GroupTheory/` に新設 (leaf 名は `WeaklyClosed.lean` 想定)
- [ ] 主定理: `p` 奇素数、`P : Sylow p G`、`A ≤ P` abelian かつ `P` 内で weakly closed
      ⟹ `N_G(A)` が `p`-transfer を制御する形 (step (12) の消費形に合わせ、
      **transfer の range 一致** `v(G) = w(N_G(A))` として述べるのが実用的)
- [ ] (17) 側の消費形: (B2) (`p ∤ |G^ab|`) と併せて
      「`N_G(A) = R₂⟨s⟩` が位数 3 の商を持つ ⟹ `G` も位数 p の商を持つ ⟹ (B2) 矛盾」
      が出る形に整える
- [ ] AxiomsCheck 登録

## 🔎 2026-07-26 の発見 — **適用先は Sylow の正規化群だった**

`normalizer_sylow_eq` (StepSeventeen.lean, landed) で

> **`N_G(Z₁PΣ) = N_G(Z₁) = R₂⟨s⟩ = N_G(R₂)`**

が判明した (`R₂ = C_G(Z₁)` と `Z(R₂) = Z₁` ((14)) から、`R₂` の正規化と `Z₁` の
正規化が一致する)。つまり (17) が要るのは **「`N_G(R₂)` が 3-transfer を制御する」**
であって、weakly closed 部分群一般の制御ではない。これは **Yoshida の定理
(repo に landed) の設定そのもの**。

⟹ **方針の第一候補が変わる**: classical Hall-Wielandt (Grün 第二定理) を建てるより、
既存の Yoshida 機構を使う方が近い:

- `OddOrder.Isaacs.Ch10.exists_surjective_wreath_of_transfer_range_lt`
  (raw Yoshida 10.1): `N_G(P)` が transfer を制御しないなら `P ↠ C_p ≀ C_p`。
- ⟹ **`R₂ ↠ C₃ ≀ C₃` の非存在**を (14)-(16) の構造から言えれば完了。
  - `|C₃≀C₃| = 3⁴`、class 3、`|Z| = 3`、`|Z₂| = 9`、`|W^ab| = 9`、exponent 9。
  - repo 側の材料: `|R₂| = 3⁵ or 3⁶`、`Z(R₂) = Z₁` (位数 3)、
    `Z₁PΣ ⊆ Z₂(R₁)` (位数 27)、`⁅RΣ,RΣ⁆ = Z₁`、`⁅Z₁ΣP, R₁⁆ ≤ Z₁`、
    `R₁ = RΣL`、`|R₂ : LV| = 3`、`Ω₁(LV) = Z₁PΣ`。
  - ⚠ `Cor 10.2` (class < p 版) は使えない見込み: class(R₁) は 3 になりうる
    (書籍 (17) が `⁅R̄₁,R̄₁⁆` の位数を 1 or 3 と計算しているので、`[R₁,R₁] ⊄ Z₁`
    の場合がある)。ただし **class(R₂) ≤ 2 が実は証明できるなら Cor 10.2 で即決**
    なので、着手時にまず `[R₂,R₂] ≤ Z₁` の可否を検討する価値がある。
- 第二候補 (fallback): classical Hall-Wielandt / Grün 第二定理を建てる (下記)。

## 🔎 2026-07-26 の第二の発見 — **一般 Hall-Wielandt は要らない**

`N := N_G(R₂) = R₂⟨s⟩` では **`R₂ ⊴ N` かつ `[N : R₂] = 2`** なので、N-level transfer が
明示計算できる:

> `A := R₂^ab`、`π : R₂ → A`、`σ` = `s` の誘導自己同型とすると、`x ∈ R₂` に対し
> **`v_N(x) = π(x) · σ(π(x))`** (横断集合 `{1, s}`)。

これを使うと **focal subgroup 定理も Grün も不要**で次が出る:

1. `v_N` が自明 ⟹ `∀ y ∈ A, y·σ(y) = 1` ⟹ **`σ = inv` on `A`**。
2. すると `y⁻¹σ(y) = y⁻²` で、`A` は奇数位数ゆえ `y ↦ y⁻²` は**全射** ⟹
   `⁅N,N⁆` の `A` における像は `A` 全体 ⟹ `R₂ ≤ ⁅N,N⁆` ⟹
   `Ab(N)` は位数 2 の `N/R₂` の商 ⟹ **`¬ 3 ∣ |Ab(N)|`**。
3. これは **landed の `3 ∣ |Ab(R₂⟨s⟩)|`** (`three_dvd_card_abelianization_of_card_W_eq_{three,nine}`)
   と矛盾 ⟹ (17) 完了。

⟹ **残るのは Yoshida の二分岐だけ**:
- `v_G.range = v_N.range` なら (B2) の `v_G.range = ⊥`
  (`transfer_abelianization_range_eq_bot`, landed) から `v_N` 自明 ⟹ 上記で矛盾。
- さもなくば `exists_surjective_wreath_of_transfer_range_lt` で
  **`R₂ ↠ C₃ ≀ C₃`** が出るので、これを (14)-(16) の構造で排除する。

### 実装順 (次セッション)
1. `v_N(x) = π(x)·σ(π(x))` の計算。**mathlib の入口は確認済**:
   `MonoidHom.transfer_def (g) : transfer ϕ g = diff ϕ T (g • T)` (任意の左横断集合 `T`)
   と `MonoidHom.diff` (`Mathlib/GroupTheory/Transfer.lean`)。
   `G := ↥N`, `H := R₂.subgroupOf N` (正規・指数 2)、`T := {1, s}` を
   `Subgroup.LeftTransversal` として構成し、`G ⧸ H` (2 元) 上の積を展開すると
   `v(x) = ϕ(x)·ϕ(s⁻¹xs)` で、`s² = 1` より `= π(x)·σ(π(x))`。
   ⚠ 主な工作は「2 元の横断集合の構成」と「商上の積の展開」。
2. 上記 1→2→3 の連結 (数学は上のとおり短い)。
3. `R₂ ↠ C₃≀C₃` の排除。材料: `|R₂| = 3⁵ or 3⁶`、`Z(R₂) = Z₁` (位数 3)、
   `⁅R₁,R₁⁆ ≤ Z₁ΣP` と `|⁅R₁,R₁⁆| ≤ 9` (landed)、`Z₁PΣ ⊆ Z₂(R₁)`、
   `C₃≀C₃` 側は位数 3⁴・class 3・`|Z| = 3`・`|Z₂| = 9`・`|W^ab| = 9`・exponent 9。

## ✅ 2026-07-26 実装 — transfer 制御は landed、残りは `|W| = 9` の wreath 排除のみ

新 leaf **`OddOrder/GroupTheory/TransferIndexTwo.lean`** (generic) と
**`FirstCase/StepSeventeenTransfer.lean`** (適用) で上記 3 段のうち **1, 2 が完了**。

| 内容 | 宣言名 |
|---|---|
| **指数 2 の transfer 公式** `v(x) = ϕ(x)·ϕ(s⁻¹xs)` | `OddOrder.GroupTheory.transfer_eq_mul_conj_of_index_two` |
| `ϕ` は `H`-共役を同一視 (A 可換) | `OddOrder.GroupTheory.map_eq_of_conj_eq` |
| `x·x^s ∈ ⁅N,N⁆` (∀x) ∧ 奇数位数 ⟹ `P ≤ ⁅N,N⁆` | `le_commutator_of_conj_mul_mem` (既 landed) |
| 指数 2 + `P ≤ ⁅N,N⁆` ⟹ `¬p ∣ |Ab N|` (p 奇) | `not_dvd_card_abelianization_of_le_commutator` (既 landed) |
| **transfer 制御 (Yoshida 分岐込み)** `¬3 ∣ |Ab(N_G(R₂))|` | `not_three_dvd_card_abelianization_normalizer_sylow` |
| 全射 `f` の kernel が lower central series を含む ⟹ 商の class ≤ n | `lowerCentralSeries_eq_bot_of_le_ker` (generic) |
| 位数 3 の正規部分群は奇数位数群で中心的 | `mem_center_of_conj_mem_zpowers_of_orderOf_eq_three` (generic) |
| `Z(↥H)` の像 = `H ⊓ C(H)` | `map_center_subtype` (generic) |
| **`|W| = 3` の wreath 排除** | `not_surjective_wreath_of_card_W_eq_three` |
| (17) の矛盾 (wreath 排除を仮説に) | `false_of_no_wreath_quotient` |
| **`|W| = 3` 側 (17) 完結** | `false_of_card_W_eq_three` |

**`|W| = 3` の wreath 排除の論法** (書籍には無い、Yoshida 経由ゆえの追加分):
`|R₂| = 3⁵`・`|C₃≀C₃| = 3⁴` ⟹ `|ker φ| = 3`。位数 3 の正規部分群は
(奇数位数ゆえ) 中心的で `Z(R₂) = Z₁` も位数 3 ⟹ **`ker φ = Z₁`**。
一方 (16) の `⁅R₁,R₁⁆ ≤ Z₁ΣP` と `⁅Z₁ΣP,R₁⁆ ≤ Z₁` から
`γ₃(R₂) = ⁅⁅R₂,R₂⁆,R₂⁆ ≤ Z₁ = ker φ` ⟹ 商の class ≤ 2。
しかし `nilpotencyClass_wreath` (repo 既 landed) より class(C₃≀C₃) = 3 ⟹ 矛盾。

### 🚧 残り = **`|W| = 9` の wreath 排除だけ**

`|W| = 9` では `|R₂| = 3⁶`・`R₂ = R₁W` (`R₁ ⊴ R₂` 指数 3、`|R₁| = 3⁵`)、
`|ker φ| = 9` になるので上の「位数 3 ⟹ 中心」論法が効かない。判明している道具:

- `K := ker φ ⊴ R₂`、`|K| = 9` ⟹ `Z₁ = Z(R₂) ≤ K` (非自明正規部分群は中心と交わる)
  かつ `K ≤ Z₂(R₂)`。
- ⟹ `C₃≀C₃` は `R₂/Z₁` の商。よって **`γ₃(R₂) ≤ Z₁` (= class(R̄₂) ≤ 2) が言えれば即決**
  (|W| = 3 側と同じ機構)。
- あるいは `K ⊄ R₁` なら `φ(R₁) = C₃≀C₃` で `class(R₁/Z₁) ≤ 2` と矛盾 (これは landed
  の (16) から出る) ⟹ **残る場合は `K ≤ R₁`** (さらに `LV ≠ R₁` (W ⊄ R₁) を使うと
  `K ≤ R₁ ⊓ LV = LΣP`)。
- 別ルート: `|Ab(C₃≀C₃)| = 9` を計算すれば `|⁅R₂,R₂⁆| ≥ 27` が出るので
  `|⁅R₂,R₂⁆| ≤ 9` 系の上界が取れれば矛盾 (ただし `⁅R₁,W⁆` の評価が要る)。

### 2026-07-26 続き: `|W| = 9` 側の部品 landed + 場合分けの確定

landed (同 leaf):

| 内容 | 宣言名 |
|---|---|
| 有限 p-群の非自明正規部分群は中心と交わる | `exists_mem_center_of_normal_ne_bot` (generic) |
| 部分群 `X` が全射 `f` で `⊤` に落ちるとき `lcs X n ≤ ker f ⟹ lcs ⊤ n = ⊥` | `lowerCentralSeries_eq_bot_of_subgroup_le_ker` (generic) |
| **`⁅W, P⁆ ≤ Σ`** (W 巡回・`w⁹ = 1`・`P` は `W³ ≤ Σ` を中心化) | `commutatorElement_mem_sigma_of_mem_W_of_mem_P` |
| **`⁅LV, LV⁆ ≤ Z₁Σ`** (`⁅L,W⁆ = 1`, `⁅P,L⁆ ≤ Z₁`, `⁅W,P⁆ ≤ Σ`) | `commutator_sup_nonsplitTorus_V_le` |
| **`γ₃(LV) = 1`** (`Z₁Σ = Z(LV)` が `LV` を中心化) | `lowerCentralSeries_sup_nonsplitTorus_V_eq_bot` |

これで `|W| = 9` の残り場合分けが確定した (`K := ker φ`、`|K| = 9`):

1. `Z₁ = Z(R₂) ≤ K` (上の generic 補題; `|Z(R₂)| = 3`)。
2. **`K ⊄ R₁` なら終わり**: `R₁` は指数 3 = 極大 ⟹ `φ(R₁) = C₃≀C₃`、
   一方 (16) の `γ₃(R₁) ≤ Z₁ ≤ K` ⟹ 商の class ≤ 2 で矛盾。
3. **`K ⊄ LV` なら終わり**: 同様に `φ(LV) = C₃≀C₃`、しかし `γ₃(LV) = 1` (landed) ⟹
   class ≤ 2 で矛盾 (`K` の情報すら不要)。
4. ⟹ **残るのは `K ≤ R₁ ⊓ LV = LΣP` (位数 3⁴) の場合のみ**。
   このとき `R₁/K` と `LV/K` は `C₃≀C₃` の相異なる指数 3 部分群で、
   両者が可換なら交わり `M/K` が中心に入り class ≤ 2 で矛盾するので、
   **少なくとも一方は非可換** = `⁅R₁,R₁⁆ ⊄ K` または `⁅LV,LV⁆ ⊄ K`。
   `⁅LV,LV⁆ ≤ Z₁Σ` なので、`K = Z₁Σ` の場合は `⁅R₁,R₁⁆ ⊄ Z₁Σ` が必要。
   ⟹ **決め手の候補 = `⁅R₁, R₁⁆ ≤ Z₁Σ` の証明** (これが出れば `K = Z₁Σ` 分岐が死ぬ)。
   材料: `card_commutator_sylowThree_le` (`|⁅R₁,R₁⁆| ≤ 9`、生成元 `u ∈ R∖Z₁P` と
   `v ∈ L` の `⁅u,v⁆` で張られる)、`R ≤ C_G(P)` (`invImageF_le_centralizer`)、
   `R` は可換 (`invImageF_mul_comm`)、`Z₁ ≤ R`、`R ⊓ Σ = 1`。

### 2026-07-26 続き 2: 場合分け 2,3 を landed + **`⁅R₂,R₂⁆` 上界ルートは死んだ**

landed (同 leaf):

| 内容 | 宣言名 |
|---|---|
| 素数指数の部分群は極大 (含まれない部分群と生成すると `⊤`) | `sup_eq_top_of_index_prime` (generic) |
| `X ⊔ ker f = ⊤` なら `X.map f = ⊤` | `map_eq_top_of_sup_ker_eq_top` (generic) |
| `|C₃≀C₃| = 3⁴` / 冪零 | `card_wreathThree` / `isNilpotent_wreathThree` (generic) |
| `X` が kernel を補い `γ₃(X) ≤ ker` なら `C₃≀C₃` 商は不可能 | `false_of_wreathThree_quotient` (generic) |
| 素数指数の正規部分群は `commutator` を含む | `commutator_le_of_index_prime` (generic) |
| **指数 3 の 2 つが kernel mod で可換なら `C₃≀C₃` 商は不可能** | `false_of_two_abelian_of_index_three` (generic) |
| **`|W| = 9`: `ker φ ≤ R₁ ⊓ LV`** (場合分け 2,3 の実装) | `map_ker_le_inf_of_card_W_eq_nine` |
| **`|W| = 9`: `⁅R₁,R₁⁆ ≤ K` と `⁅LV,LV⁆ ≤ K` は両立しない** | `not_and_commutator_le_map_ker_of_card_W_eq_nine` |

⚠ **重要な否定的所見 (2026-07-26)**: `|W| = 9` では **`⁅R₂,R₂⁆ ⊄ RΣ`**、したがって
`⁅R₂,R₂⁆ ≤ Z₁Σ` も `≤ Z₁ΣP` も**偽**。理由: `⁅R,W⁆ ≤ RΣ` なら `W ≤ N_G(RΣ)` となり
`R₂ = R₁W` が `N_G(RΣ)` の位数 3⁶ の 3-部分群になる。しかし `R₁` (位数 3⁵) は
`N_G(RΣ)` の Sylow 3-部分群 (定義) なので矛盾。
⟹ 「`|⁅R₂,R₂⁆|` を小さく抑えて `|R₂^ab|` を大きくする」系のルート
(`γ₃(R₂) ≤ Z₁` 経由も含む) は**すべて死んだ**。
残る構造的手掛かりは `⁅R₂,R₂⁆ ≤ R₁ ⊓ LV = LΣP` (位数 3⁴) と `⊄ Z₁ΣP` のみ。

### ⟹ 残ギャップの評価 (2026-07-26)

`|W| = 9` の wreath 排除は、**landed の (14)–(16) 構造だけでは閉じない**見込み。
`⁅R, W⁆` (= `W` の `R` への作用) の構造が要るが、書籍 (17) はそこを論じない
(Hall–Wielandt で一気に飛ばすため)。したがって選択肢は:

1. **古典的 Hall–Wielandt (Grün 第二定理) を建てる** — 原典 M. Hall [1] pp. 206-212 は
   手元に無く、Gorenstein は「we do not require it, we shall not prove it here」と
   明言 (p. 257)。⟹ 証明の再構成が必要 ([[feedback-ask-chatgpt-for-elided-gaps]] の
   適用場面: 最強モデルに証明を再構成させ、repo の Mackey/focal/transfer 基盤で形式化)。
   repo にある素材: `focalSubgroupTheorem` (Isaacs Ch5)、`MackeyTransfer.lean`、
   `transfer_transfer` / `transferRes` / Yoshida 一式。
2. `⁅R, W⁆` の構造を (11)(14) の材料から詰めて `|W| = 9` 専用の排除を作る
   (書籍に対応論法が無いので独自論法になる)。

現時点の推奨は **1** (下流の一般性も高く、Peterfalvi の引用どおりの定理が手に入る)。

## 🎯 2026-07-26 方針転換 — **Alperin も Grün I も要らない: `Z(R₂)` の弱閉性ルート**

Gorenstein pp. 251-257 を精読した結果、**もっと短い経路**が見つかった。

- Gorenstein Thm 7.5.2 (Grün 第二定理) = 「G が `p`-normal (= `Z(P)` が `P` 内で弱閉)
  なら `P ∩ G' = P ∩ N'`, `N = N_G(Z(P))`」。証明は Grün 第一定理 (Thm 7.4.2) 経由で、
  そちらは **Alperin の融合定理**を使う (repo/mathlib に無い、重い)。
- しかし **Isaacs 演習 5C.6(d)** =「`W ≤ Z(P)` が `P` 内で弱閉なら `N_G(W)` が
  `P` の `G`-融合を制御する」は **Sylow + 弱閉性だけ**で証明できる (Alperin 不要):
  > `x, y ∈ P`, `y = x^g` とする。`W ≤ Z(P)` より `W ≤ C_G(y)` かつ `W^g ≤ C_G(y)`。
  > `C := C_G(y)` の Sylow `p` で両者を共通の `U` に入るよう `c ∈ C` で共役し、
  > `U ≤ T` (G の Sylow) を取ると `W, W^{gc} ≤ T`。5C.6(a) より `W` は `T` 内でも弱閉
  > ⟹ `W^{gc} = W` ⟹ `gc ∈ N_G(W)`、かつ `x^{gc} = y^c = y` ⟹ `x ~_N y`。
- 融合制御 + **focal subgroup 定理 (repo に landed: `Isaacs.Ch05.focalSubgroupTheorem`)**
  で `P ∩ G' = focal_G(P) = focal_N(P) = P ∩ N'` が出る。

**本 First Case への適用**: `Z(R₂) = Z₁` (landed `inf_centralizer_sylow_eq_zpowers`)、
`N_G(Z₁) = R₂⟨s⟩` (landed) なので、**`Z₁` が `R₂` 内で弱閉**でありさえすれば
`R₂ ∩ G' = R₂ ∩ N'` が出て、(B2) (`R₂ ≤ G'`) から `R₂ ≤ N'` ⟹ `¬3 ∣ |Ab N|`。
**|W| = 3 / 9 の場合分けも wreath 排除も不要**になる (Yoshida ルートを置き換える)。

### 残作業 (この方針)
- [x] `IsWeaklyClosed` の定義 + **5C.6(a)** (共役 Sylow への弱閉性の移送)
- [x] **5C.6(d)** `exists_mem_normalizer_conj_eq` : `W ≤ Z(P)` 弱閉 ⟹ `N_G(W)` が
      `P` の `G`-融合を制御 (`C_G(y)` 内で 2 つの `p`-部分群を共通 Sylow へ =
      `exists_mem_conj_le_common`)
- [x] focal 連結 `focalSubgroup_le_map_of_fusion_control` +
      `sylow_le_commutator_of_not_dvd` / `not_dvd_card_abelianization_of_sylow_le_commutator`
- [x] **`not_dvd_card_abelianization_normalizer`** : `W ≤ Z(P)` 弱閉 ∧ `¬p ∣ |Ab G|`
      ⟹ `¬p ∣ |Ab(N_G(W))|` (= (17) が要る形の Hall–Wielandt)
- [x] (17) への配線 `false_of_isWeaklyClosed_zpowers` : **`Z₁` の弱閉性から (17) の
      矛盾が両分岐まとめて出る** (wreath 排除も `|W|` の場合分けも不要)
- [ ] **`Z₁` が `R₂` 内で弱閉** (= この設定での 3-normality) ← **唯一の新しい数学**
      - 同値形: `Z₁ ≤ Q` (Sylow) ⟹ `Q = R₂`。`R₂ = C_G(Z₁)` なので
        「`Z₁` を含む Sylow は `Z₁` を中心化する」と言い換わる。
      - 手掛かり: `Z₁^x ≤ R₂ ⟹ Z₁ ≤ R₂^x` (`R₂ = C_G(Z₁)` から対称に出る)、
        `E := Z₁Z₁^x` は `C_G(E) = R₂ ⊓ R₂^x` の中心に入る、
        `Z₁` の元は強実で `C_G(z) = R₂` は奇数位数、
        (16) の「`A = Z₁ΣP` 内の強実線は `Z₁` だけ」、(17) の `A` の弱閉性。
      - ⟹ `Z₁^x ≤ A` (または `≤ LV`) さえ言えれば (16) で決着する
        (`Ω₁(LV) = A` より `Z₁^x ≤ LV` で十分)。
      - ⚠ 書籍が `Z(P)` でなく `A = Z₁PΣ` (可換・弱閉・p 奇) 版の Hall–Wielandt を
        引いているのは、`Z₁` の弱閉性が自明でないからかもしれない。
        代替案: 5C.6(d) の証明は「`W ≤ C_G(x) ∩ C_G(y)`」しか使わないので
        **`A` の元の融合は `N_G(A)` が制御する**ことは同じ論法で出る (`A` 可換)。
        ただし focal 部分群は `R₂` の**全**元の融合を要するので、それだけでは足りない。
        ⟹ 次の一手は (i) `Z₁` の弱閉性を (13)–(17) の構造から詰める、または
        (ii) 「`A` 可換弱閉 + p 奇」版 Hall–Wielandt の証明を再構成する。

## 証明方針 (旧、未確定)

古典的には **Grün の第二定理** (weakly closed abelian `A` ⟹ `N_G(A)` が p-transfer を
制御) 経由。素材として repo にある Yoshida/Mackey transfer 基盤が使える見込み。
⚠ `A ⊆ Z_{p−1}(P)` 枝は不要なので、`p` 奇 + `A` abelian の枝だけを狙う。
着手時に (a) Gorenstein §7.6 (証明は M. Hall 参照で本書に無し)、(b) Isaacs Ch.5/10
の focal subgroup / Grün 周辺、(c) Coq odd-order の対応物の有無を実測してから
方針を確定する ([[feedback-ask-chatgpt-for-elided-gaps]] も選択肢)。

## 完了条件

- ✅ transfer 制御 (`not_three_dvd_card_abelianization_normalizer_sylow`) が sorry-free で landing
- ✅ `|W| = 3` 側 (17) が `False` まで到達 (`false_of_card_W_eq_three`)
- [ ] `|W| = 9` 側の wreath 排除 (上記) ⟹ `false_of_no_wreath_quotient` が両分岐で discharge

## 参照

- issues/2053-pf-suzuki-theorem-b.md (消費点、(17) の全論法)
- references/peterfalvi/pdf/05.4_pp_108_114_The_First_Case.pdf p. 108 (statement) / p. 114 (使用)
- OddOrder/Isaacs/Ch10_MoreTransfer/Yoshida.lean (class < p 版、既存)
- OddOrder/Peterfalvi/Appendices/Suzuki/FirstCase/StepTwelveTransfer.lean (既存版の消費例)


## 🔎 2026-07-26 追加解析 — `Z₁` の弱閉性 vs `|W| = 9` wreath 排除

### `Z₁` の弱閉性について分かったこと

`Z₁^x ≤ R₂` を仮定して `u := z^x` (z = st) とおくと:

- `R₂ = C_G(Z₁)` から対称に **`Z₁ ≤ R₂^x = C_G(u)`**、`E := ⟨z,u⟩` は
  `J := R₂ ⊓ R₂^x = C_G(E) = C_{R₂}(u) = C_{R₂^x}(z)` の中心に入る。
- (16) の強実線一意性から **`u ∉ A`** かつ (共役版で) **`z ∉ A^x`**。
- ⟹ `u ∈ LV` (⟺ `u ∈ Ω₁(LV) = A`) が言えれば終わるが、landed の step-1 補題
  (`map_conj_zpowers_le_sup_nonsplitTorus_V`) は仮説が **`A^x ≤ R₂`** (位数 27 の
  共役全体) で、`Z₁^x ≤ R₂` だけからは走らない。
- ⚠ **書籍が `Z(P)` 版でなく `A` 可換版の Hall–Wielandt を引いているのは、
  `Z₁` の弱閉性 (= 3-normality) が手に入らないからかもしれない**。
  (13) の「`C_G(st)` は 3-群」は `st` 固有の counting で、`R₂` の他の位数 3 元を
  特徴づけるものではない。
- 一般論としても `p`-normality は仮説であって自動ではない (Gorenstein 7.5 冒頭)。

### `|W| = 9` wreath 排除の残りケースの絞り込み (新規)

`K := ker φ` (位数 9、`Z₁ ≤ K ≤ M := R₁ ⊓ LV`、`|M| = 3⁴`) について:

1. `K ⊴ R₂` かつ `|K| = 9` ⟹ `R₂/C_{R₂}(K) ↪ Aut(K)`。`Aut(C₉) = C₆` /
   `Aut(C₃²) = GL(2,3)` (位数 48) のいずれでも 3-part は 3 ⟹
   **`C := C_{R₂}(K)` の指数は ≤ 3**。`C = R₂` なら `K ≤ Z(R₂) = Z₁` で位数矛盾
   ⟹ **指数はちょうど 3**。
2. `C ≠ R₁` (`Z(R₁) = Z₁` は位数 3 < 9)。`C = LV` なら `K ≤ Z(LV) = Z₁Σ` ⟹ **`K = Z₁Σ`**。
3. `C ≠ LV` のときも、`W₃ = C₃≀C₃` の極大部分群はすべて `Φ(W₃) = W' = M/K` を含むので
   `M ≤ C` ⟹ `M` が `K` を中心化 ⟹ **`K ≤ Z(M)`**。
   ⟹ **`Z(M) = Z₁Σ` (位数 9) を示せば `K = Z₁Σ` が確定する**。
4. `K = Z₁Σ` なら `⁅LV,LV⁆ ≤ Z₁Σ = K` (landed) なので
   `not_and_commutator_le_map_ker_of_card_W_eq_nine` (landed) より
   **`⁅R₁,R₁⁆ ⊄ Z₁Σ`** が必要になる。

⟹ **両ルートの合流点 = `⁅R₁, R₁⁆ ≤ Z₁Σ`**。
landed の `card_commutator_sylowThree_le` の中身は `⁅R₁,R₁⁆ ≤ Z₁⟨⁅u,v⁆⟩`
(`u ∈ R ∖ Z₁P`, `v` は `L` の生成元) なので、これは **`⁅R, L⁆ ≤ Z₁Σ`**
(すなわち `⁅T, L⁆` の評価) に帰着する。既知: `R₁ ≤ N_G(RΣ)` より `⁅R,L⁆ ≤ RΣ`、
`⁅R₁,R₁⁆ ≤ A` より `⁅R,L⁆ ≤ A`、`A ⊓ R = Z₁P`。**要るのは「P-成分が消える」こと**。

### 次の一手 (優先順)
1. `⁅R, L⁆ ≤ Z₁Σ` (⟺ `⁅R₁,R₁⁆ ≤ Z₁Σ`) を (11)(14)(15) の材料で詰める。
   出れば `|W| = 9` の wreath 排除が (上の 1–4 と landed 補題で) 閉じる見込み。
2. だめなら `Z(M) = Z₁Σ` + `C_{R₂}(K)` 指数 3 の Lean 化を進めて残りケースを縮める。
3. 最後の手段: 「`A` 可換弱閉 + `p` 奇」版 Hall–Wielandt の再構成
   (Grün 第一定理 ⟹ Alperin が必要で重い; ChatGPT 相談の対象)。


## 🧭 2026-07-26 方針決定 — 古典機構 (Alperin → Grün I → Grün II) を建てる

上記の解析で、`|W| = 9` 側も `Z₁` 弱閉性も **`⁅R₁,R₁⁆ ≤ Z₁Σ` (⟺ `⁅R,L⁆` の
`P`-成分が消えること)** に帰着したが、これは**書籍が決めていない**
(Peterfalvi (17) は「`⁅R̄₁,R̄₁⁆` の位数は 1 or 3」と両方を許したまま
Hall–Wielandt に渡す)。`s` 作用 (s は `T` と `L` を反転、`P`・`Σ` を中心化) でも
`c = ⁅u,v⁆` の `P`-成分は決まらない。⟹ **First Case 側の材料だけでは閉じない**。

したがって残る道は、Peterfalvi が引いている定理そのもの
(**`p` 奇 + `A` 可換弱閉版の Hall–Wielandt = Grün 第二定理**) を建てること。
Gorenstein Ch.7 に完全な証明系列がある (本 repo の方針で Gorenstein は
「行間を埋めるために参照する」対象):

1. **Alperin の融合定理** (Gorenstein §7.2, Thm 2.6/2.7; tame intersection):
   `G`-融合は `N_G(P ⊓ Q)` (tame intersection) の族で生成される。
   mathlib にも repo にも無い ⟹ 新規 (最大の塊)。
2. **Grün 第一定理** (Gorenstein Thm 7.4.2): `P ∩ G' = ⟨P ∩ N_G(P)', P ∩ Q' | Q ∈ Syl_p⟩`。
   Alperin から数十行。
3. **Grün 第二定理** (Gorenstein Thm 7.5.2) の論法を `A` 可換弱閉版に適用。
   本 repo には既に `IsWeaklyClosed` + 5C.6(a) + 融合制御→focal の連結
   (`WeaklyClosed.lean`) と focal subgroup 定理があるので、Grün I が入れば
   `P ∩ G' = P ∩ N'` まで到達できる。

⚠ **2026-07-26 追記: この段取りは Gorenstein 自身の注記で否定される**。
Gorenstein p. 257 は Hall–Wielandt について
> "There exist other deeper results, notably the Hall-Wielandt theorem, which give
> conditions on weakly closed subgroups `W` of `P` **other than `Z(P)`** ... (See M. Hall
> [1], pp. 206-212.) **This theorem does not seem to be a direct consequence of
> Alperin's theorem**; and, as we do not require it, we shall not prove it here."

と明言している。すなわち:

- Gorenstein Thm 7.5.2 (Grün 第二定理) = **`Z(P)` 版のみ** (p-normal 前提)。
  Alperin → Grün I → これ、の系列は `Z(P)` 版までしか届かない。
- Peterfalvi が引く **`A` 可換版 (Hall Thm 14.4.2)** は Alperin の直接の系ではない。

⟹ Alperin を建てても `Z₁` の弱閉性 (3-normality) が無ければ (17) は閉じない。
そして `Z₁` の弱閉性は landed の材料からは出ない (上記解析)。

### ⟹ 現状の選択肢 (2026-07-26 時点)

1. **M. Hall, *The Theory of Groups* (1959) pp. 206-212 (Thm 14.4.2) の入手**。
   これが Peterfalvi の引用元そのもので、`p > 2 ∧ A` 可換版の証明が載っている。
   references/ に無いのでユーザーへ入手可否を報告する (issue 0147 の Navarro と同型)。
2. **ChatGPT (最強モデル) に古典証明を再構成させる** ([[feedback-ask-chatgpt-for-elided-gaps]])
   — 自己完結プロンプト + 回答の厳密検証が前提。
3. First Case 側でさらに `⁅R, L⁆` を決める材料を探す (現状 (11)(14)(15) には無い)。


## 🤖 2026-07-26 ChatGPT 相談 (実行中)

ChatGPT Pro (reasoning「非常に高い」) に Hall–Wielandt (p 奇 + A 可換弱閉) の
古典証明を依頼した (chat: "Hall Wielandt Proof")。プロンプトの要点:

- 定理の正確な statement (weakly closed の定義込み)
- **Alperin 経由・Grün II の `Z(P)` 版で済ませるのは禁止** (Gorenstein p.257 の注記を明示)
- Lean 4 形式化用なので各ステップ検証可能に、transfer 計算は横断集合を明示
- `p > 2` をどこで使うかを明示
- 副問: 本件の追加構造 (`N_G(A) = N_G(P) = N_G(Z(P))`、`P = C_G(Z(P))`、`|Z(P)| = p`、
  `A` は位数 `p³` の初等可換で `P` に正規、`p = 3` で class(P) = 3 ゆえ class < p 判定は不可、
  `Z(P)` の弱閉性は仮定できない) の下で近道はあるか

⚠ 回答は **必ず自分で厳密検証**する ([[feedback-ask-chatgpt-for-elided-gaps]])。
特に「A 可換版が Z(P) 版に帰着できる」系の主張は Gorenstein の注記と矛盾するので疑う。

### 回答 (16m54s 思考、chat URL: https://chatgpt.com/c/6a6509e6-1728-83e8-a764-3c52c0c97acb)

前半の骨格 (2026-07-26 時点で読めた範囲、**未検証**):

1. **§1**: 目標は `P ∩ G' = P ∩ N'` (focal 版)。`O^p` 版へは **Tate の定理**で上げる
   (「focal 版と O^p 版の差が Tate の定理の内容」)。Alperin は使わない旨を明言。
   ⚠ 参考文献リード: 「character-transfer による後年の一般化 (条件 `[x,y;p−1] ∈ Φ*(A)`)」
   があり、可換版はその特殊化 (`[x,y;p−1] = 1`) だという (北大リポジトリの論文を引用)。
2. **§2**: 弱閉性から即 `A ⊴ P` かつ `P ≤ N` (`u ∈ P` に対し `A^u ≤ P` ⟹ `A^u = A`)。
   ⟹ `P` は `N` の Sylow でもあり、`D := P ∩ N' ⊵ P'` で `P/D` は可換 p-群。
3. **§3**: 文字 transfer `T_H^K(χ)(k) = Σ_{t∈T} χ(h(t,k))` と推移律、
   さらに二重剰余類分解 `G = ⊔ P g_i R` (`R ≤ P`)、`S_i = R ∩ g_i^{-1} P g_i` による
   **明示公式 (17)**: `T_P^G(λ)(r) − [G:P]·λ(r) = Σ_i T_{S_i}^R(δ_i)(r)`、
   ただし `λ_i(s) = λ(g_i s g_i^{-1})`, `δ_i = λ_i − λ|_{S_i}`。横断集合も明示。
4. **§4 「odd-prime local transfer lemma」**: `R` p-群 (p 奇)、`A ⊴ R` 可換、`R = ⟨A,x⟩`、
   `S ≤ R`、`δ : S → C` が `T_S^R(δ)(x) ≠ 0` と `X_R(x) ∩ S ⊆ ker δ`
   (`X_R(x) := {(x^{p^k})^r}` = `⟨x^p⟩` の R-共役の合併) を満たすなら `S = R`。
   ← **p 奇はここで効く模様**。(証明は極大部分群 `M ⊵ R` を取る標準論法から開始。)

以降 (§5 以降) は未読 — 次 iteration で読み切って検証する。


## ✅ 2026-07-26 決着 — 証明を入手・検証、Lean 化計画確定

ChatGPT Pro の回答 (16m54s + 2m54s 思考) を**全ステップ独立に検証**し、正しいことを確認した。
証明本文と検証メモは **[`notes/meta/hall_wielandt_proof.md`](../notes/meta/hall_wielandt_proof.md)**
(本 issue の正本)。要点:

- **Alperin も Grün II(Z(P) 版) も Burnside 融合も使わない** — Gorenstein p.257 の注記と整合。
- 大域は二重剰余類の明示公式 `T_P^G(λ)(r) − [G:P]λ(r) = Σ_i T_{S_i}^R(δ_i)(r)` 1 本のみ。
- 局所は「奇素数 local transfer 補題」: `A ⊴ R` 可換・`R = ⟨A,x⟩`・`T_S^R(δ)(x) ≠ 0`・
  `X_R(x) ∩ S ⊆ ker δ` ⟹ `S = R`。`p > 2` は `(α−1)²b = 0 ⟹ (α−1)^{p-1}b = 0` の
  指数でのみ効く。**p = 3 なら `1+α+α² = (α−1)²+3α` の恒等式で済む**。
- 主証明は `x ∈ (P∩G')∖D` を位数最小に取り、(17) の非零項 `i` に補題を適用して `S = R`、
  すると `A^{g⁻¹} ≤ P` から弱閉性で `g ∈ N`、ゆえに `δ ≡ 0` で矛盾。
- 副問: 追加構造 (`P = C_G(Z(P))`, `|Z(P)|=3`, class 3, `A ≅ C₃³`) は**不要**。
  また `Z(P)` の弱閉性は出ない・我々の局所形状は `C₃≀C₃` と両立する、という
  我々の解析が**独立に裏付けられた**。`[N_G(P):P] ≤ 2` も landed と整合 (sanity check)。

### Lean 化の段取り (既存資産が効く)

| 段 | 内容 | 状態 |
|---|---|---|
| 1 | 指標 transfer = `MonoidHom.transfer`、推移律 | ✅ landed (`transfer_transfer`) |
| 2 | 二重剰余類公式 (17) | `MackeyTransfer.lean` を実測 → 差分実装 |
| 3 | 局所補題 Case 1 (`x ∉ M`) | ✅ `transfer_eq_pow_of_notMem` (Isaacs 10.6(b)) |
| 4 | 局所補題 Case 2 (`x ∈ M`) | ✅ `transfer_eq_prod_conj_of_mem` (Isaacs 10.6(a)) |
| 5 | `X_R(x) ∩ M ⊆ ker μ` の軌道論法 | 新規 (短い) |
| 6 | `(α−1)²b = 0` + `p=3` 恒等式 | 新規 (短い) |
| 7 | 主証明 (最小位数 + 弱閉性) | 新規、`IsWeaklyClosed` (landed) を使用 |
| 8 | `¬3 ∣ |Ab N|` への消費 | ✅ `WeaklyClosed.lean` の focal 連結 |

⟹ **(17) の残ギャップは「Hall–Wielandt の Lean 化」1 本に確定**し、道筋も部品も揃った。
`A = Z₁ΣP` の弱閉性は (17) で landed 済み・`A` は可換 (landed)・`N_G(A) = N_G(Z₁) = R₂⟨s⟩`
も landed なので、上記を建てれば `false_of_isWeaklyClosed_zpowers` の兄弟として即接続できる。
