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

⟹ 次の一手は **`⁅R₁, W⁆` の構造** (特に `⁅R, W⁆`、`R = invImageF`) を (14) の材料から
詰めて `γ₃(R₂) ≤ Z₁` を出すこと。

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
