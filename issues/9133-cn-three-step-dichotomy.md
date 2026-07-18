---
id: 9133
slug: cn-three-step-dichotomy
title: "CLAIM: CN 群の 3-step 二者択一 (Gorenstein Ch12 §1 Cor 1.6) — BG App.D の unlock"
created: 2026-07-18
---

# CLAIM (shared infra): CN 群の 3-step 二者択一 — BG App.D D.1/D.2 の unlock

**claim 主体**: lane c。**予定 leaf**: `OddOrder/GroupTheory/CNGroupStructure.lean` (新規)。
**関連**: issue 3020 (App.D de-opacify 済 + 本ブロッカーの特定)。

## ⚠ 原典の所在 (章番号のずれに注意)

BG App.D は「**G**, Corollary 14.1.6」「Section 14.1」と引用するが、手元の
`references/gorenstein/finite-groups.mmd` では該当内容は **Chapter 12
"GROUPS IN WHICH CENTRALIZERS ARE NILPOTENT"** にある (版差または OCR の章番号ずれ):
- `## Chapter 12` = mmd:7767、`## 1 Basic properties of CN-groups` = mmd:7773、
  `## 2 CN-groups of odd order` = mmd:7861。
- **3-step 群の定義** = mmd:7801、**Theorem 1.5** = mmd:7818、**Corollary 1.6** = mmd:7838。

## 原典の内容 (逐語)

**3-step 群の定義** (素数 `p` に関する、mmd:7801) — 次の 3 条件:
1. `O_{p,p'}(G)` は Frobenius 群で、核が `O_p(G)`、**補群は奇数位数の巡回群**。
2. `G = O_{p,p',p}(G)` かつ `G ⊋ O_{p,p'}(G)` (真の包含)。
3. `G/O_p(G)` は Frobenius 群で、核が `O_{p,p'}(G)/O_p(G)`。

**Theorem 1.5** (mmd:7818): `G` が**可解 CN 群**なら次のいずれか —
(i) `G` は冪零 / (ii) `G` は Frobenius 群で補群が巡回 or (奇数位数巡回 × 一般四元数) /
(iii) `G` は 3-step 群。

**Corollary 1.6** (mmd:7838、Thm 1.5 の即系): `G` が**可解 CN 群**かつ `O_p(G) ≠ 1` なら、
`O_p(G)` が `G` の Sylow `p` であるか、`G` が `p` に関する 3-step 群。
⚠ 仮説は「可解**かつ CN**」であって単なる可解ではない (BG は M ⊆ G が CN 群の部分群ゆえ CN、を使う)。

## BG が実際に消費するのは 2 帰結のみ

BG App.D D.1 の証明 (mmd:5155-5178) は Cor 1.6 で M を 3-step と判定した後、
「定義と短い議論から」次の 2 つだけを使う:
- `O_{p'}(M) = 1` — 定義 1 の Frobenius 性から (正規 p'-部分群は核に自明に交わる)。
- `M/O_{p,p'}(M)` が**非自明 p-群** — 定義 2 (`G = O_{p,p',p}(G)` かつ真の包含) から直ちに。

⟹ **定義 + この 2 帰結は tractable**。実質は Cor 1.6 (= Thm 1.5) の証明。

## Thm 1.5 の証明が要する道具 (repo の在庫状況)

- `C_G(F(G)) ⊆ F(G)` (可解、Gorenstein Thm 6.1.3) — **repo に在り** (Isaacs Fitting 系)。
- Hall 部分群の存在 (可解、Thm 6.4.1) — **repo に在り** (Isaacs Ch03)。
- Frobenius 補群の構造 (Thm 10.3.1: 唯一の involution / Sylow 巡回 / metacyclic) —
  **repo に相当量在り** (Isaacs Ch06 Frobenius, `DQSDRecognition` 等) — 要 verify-port-state。
- **Lemma 1.2 (CN 固有)**: `q`-元が `p`-元を中心化するなら Sylow `p` を中心化する等 — **新規**。
- Thm 1.3.1(ii) / 7.6.2 / 10.1.3 (fpf 自己同型) — 一般論、要在庫確認。

## 段階的完了条件 (tier)

1. **tier 1**: `IsThreeStepGroup` を定義 → Cor 1.6 を証明 → BG App.D の D.1 → D.2 を閉じる。
2. **tier 2**: 定義 + BG が使う 2 帰結を sorry-free で証明 (これだけでも D.1 の「短い議論」部分が埋まる)
   + Lemma 1.2 (CN 固有) を証明 + Thm 1.5 の骨組み。Cor 1.6 は honest statement + sorry。
3. **tier 3**: 上記が停まるなら、どの補題が抵抗するか・repo/mathlib に何が無いかを precise に記録。

⚠ **Gorenstein の章節を独立に全形式化することはしない** (CLAUDE.md 明示禁止)。
必要なのは Cor 1.6 とその 2 帰結に至る最小経路のみ。

## 参照
- `OddOrder/BG/AppD_CNGroups.lean` (de-opacify 済、`IsCNGroup` は既存)、BG mmd:5132-5199。
- issue 3020 (Isaacs 代替不可の検証結果 — Isaacs に CN 群も 3-step 群も無し)。
- ⚠ shared infra (`OddOrder/GroupTheory/**`) ゆえ他レーンは着手前に本 claim を確認のこと。
