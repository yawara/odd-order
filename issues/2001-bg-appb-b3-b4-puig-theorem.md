---
id: 2001
slug: bg-appb-b3-b4-puig-theorem
title: "BG App.B Lemma B.3 + Theorem B.4 (= Thm 6.2 代替)"
created: 2026-05-29
---

# BG App.B Lemma B.3 + Theorem B.4 (= Thm 6.2 代替)

## 背景

issue 2000 で **App.B 定義 + Lemma B.1(a)-(g) + B.2** が完成 (`OddOrder/BG/AppB_Puig.lean`,
sorry-free, axiom-clean)。A.5 (`thmA5_part1/part2`, issue 0049) も完成済。これにより
**Lemma B.3 + Theorem B.4 が ready-now**。

**Theorem B.4(a) は BG Thm 6.2 (Glauberman Z(J)) の代替** (BG L4691 "serves as a substitute
for Theorem 6.2")。Isaacs FGT が Z(J) 定理を省く (p.217) ため、no-Gorenstein 方針下では
これが Thm 6.2 一般形の唯一の自己完結ルート。**クリティカルパス**: B.4 → BG Thm 6.2 一般形 →
§7 (Thompson 推移性) → §8-§16。

方針正本: `notes/bg/appB_puig.md`「実装状況 (2026-05-29)」+ 「Lem B.3 / Thm B.4 詳解」、
`notes/meta/bg_s6_appAB_route_2026_05_28.md`。原文: `references/bg/local-analysis.mmd`
L4644-4757 (Lem B.3 = L4644-4684, Thm B.4 = L4686-4757)。

## やること

### 前提インフラ (B.3 が要求)

- [ ] **相対版 Lemma B.1(f)**: `H` が p-群 (`IsPGroup p ↥H`) のとき `C_G(lNIn H i) ⊓ H ≤ lNIn H i`
      (= `H`-内 self-centralizing)。issue 2000 の B.1(f) は**絶対版** (`G` 自体が p-群) のみ。
      subtype `↥H` 上で Ch06 `centralizer_eq_of_maximal_normal_isMulCommutative` を適用し
      `Subgroup.map ↥H.subtype` で `G` に transport。極大 abelian の `H`-正規性 → `lNIn H` 包含は
      2000 の一般核 (下記) で吸収できるか要検討。
- [ ] **B.1(e) の一般化** (必要なら): 現 `abelian_normal_le_lNIn` は `A.Normal` (G-正規) 要求。
      相対 (f) では `M` は `H`-正規のみ。`H ≤ N_G(A)` 版 `abelian_le_lNIn` に一般化
      (証明は `lNIn_le_self H j ≤ H ≤ N_G(A)` で `le_lRelIn` に渡すだけ; 2000 で設計済の筋)。
- [ ] **`thmA5` インターフェース補題**: `thmA5` の `hX` は abelian **p-群** で生成 (`IsMulCommutative ∧ IsPGroup p`)
      だが `lRelIn` は一般 abelian。p-群 `T`/`S` 内では abelian ⊆ p-群なので
      `lNIn (S or T) n ≤ ⨆ (abelian p-群 normalized by P), A` を示し `thmA5_part1/part2` の `hX` に橋渡し。

### Lemma B.3 (mmd L4644-4684)

- [ ] `p` odd, `G` solvable odd, `O_{p'}(G)=1`, `S ∈ Syl_p(G)`, `T = O_p(G)` のもとで
      `L_*(S) ⊆ L_*(T) ⊆ L(T) ⊆ L(S)` (= `lStarIn S ≤ lStarIn T ≤ lOddIn T ≤ lOddIn S`)。
      `T ≤ S` (O_p ≤ Sylow) ゆえ `G` の部分群として包含が型付く。
- [ ] 帰納核 (L4650): `∀ n, L_{2n}(S) ⊆ L_{2n}(T) ⊆ L_{2n+1}(T) ⊆ L_{2n+1}(S)`。
      step で `L_{2n+1}(T)` は normal p-群 → 相対 B.1(f) + **`thmA5_part2`** (P=L_{2n+1}(T),
      X=L_{2n+2}(S)) で `L_{2n+2}(S) ⊆ T`、続いて `L_{2n+1}(T) → L_{2n+2}(S)` から
      `L_{2n+2}(S) ⊆ L_{2n+2}(T)`。

### Theorem B.4 (mmd L4686-4757)

- [ ] (b) `O_{p'}(G)=1 ⇒ Z(L(S)) ⊴ G`。Step2: `Z(L(S)) ⊆ Z(L(T))` (B.3 + B.1(f))。
      Step3: `Y=Z(L(T))`, `C/C_G(Y)=O_p(G/C_G(Y))` で `L(S) ◁ N_G(C ∩ S)`
      (**`thmA5_part1`**: X=L(S), P=Y → `L·C_G(Y)/C_G(Y) ⊆ O_p(G/C_G(Y))` + B.2 で `L(C∩S)=L(S)`)。
      Step4: Frattini で `Z(L(S)) ⊴ G`。
- [ ] (a) `G = O_{p'}(G)·N_G(Z(L(S)))` (Frattini argument; (b) を bar G = G/O_{p'} で適用)。
- [ ] **(BG Thm 6.2 一般形)** `bg-thm-6-2-general`: `Z(L(S))·O_{p'}(G) ⊴ G` を B.4 から述べる
      (`OddOrder/BG/...` の Thm 6.2 placeholder と接続; 別ファイルかもしれない — 要確認)。

## 完了条件

- 上記 B.3 / Thm B.4(a)(b) すべて sorry-free, `lake build OddOrder` green,
  `OddOrder/AxiomsCheck.lean` に登録し標準 3 公理のみ。
- Thm 6.2 一般形への接続を最低限 statement レベルで用意 (証明は本 issue or 直後の別 issue)。

## 参照

- 前提 (完成済): issue 2000 (B.1/B.2), issue 0049 (`thmA5_part1/part2`)。
- `notes/bg/appB_puig.md` (Lem B.3 詳解 L174-208, Thm B.4 4-Step 詳解 L212-322)。
- `OddOrder/BG/AppB_Puig.lean`: `lRelIn_top_le_lRelIn` (B.4 Step3 の `L(C∩S)=L(S)` に再利用),
  `lOddIn_eq_of_lOddIn_le` (= B.2), `centralizer_lNIn_le` (絶対 B.1(f), 相対版の雛形)。
- `OddOrder/BG/AppA_PStability.lean`: `thmA5_part1` (L2062), `thmA5_part2` (L2099)。
- 原文 `references/bg/local-analysis.mmd` L4644-4757。
