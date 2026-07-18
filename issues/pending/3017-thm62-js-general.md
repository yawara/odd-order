---
id: 3017
slug: thm62-js-general
title: "BG Thm 6.2 一般形 J(S): Z(J(S))·O_{p'}(G)◁G — O_{p'} reduction + ZJ hypothesis discharge"
created: 2026-07-18
---

# BG Thm 6.2 一般形 (literal Thompson J(S))

## 背景

BG §6 の特殊化債務 (survey L351)。**BG Thm 6.2** (mmd L1990): G solvable odd, p prime, S∈Syl_p
⟹ `Z(J(S))·O_{p'}(G) ◁ G`。book の **Remark** (L1994): 「A substitute (Thm B.4) is proved in
App.B using L(S) (Puig) instead of J(S)」。

現状:
- **L(S) 一般形は済** = `AppB_Thm62.zCenter_lOdd_sup_oPiCore_normal` (`Z(L(S))·O_{p'}(G)◁G`、全 G、
  O_{p'} 商 → `zCenter_lOdd_normal_of_oPiCore_eq_bot` (O_{p'}=1 case) via Ḡ=G/O_{p'}, S̄=mk(S)≅S)。
  **book の推奨代替はこれで満たされている。**
- **J(S) は reduced case のみ** = `S06_Additional.normalJ_normal_of_odd` (odd solvable, p≠2, P Syl,
  `O_{p'}(G)=⊥`, **`C_G(Z(P))=P`** ⟹ J(P)◁G)、via `Ch07.normal_J` (Isaacs Thm 7.6 = ZJ)。

downstream FT (§8/§9, mmd L2471/2495/2528) は **J(S) 形** (Z(J(P))◁M) を cite。FT は完成済ゆえ
FT の使用は reduced J(S) or L(S) で満たされている。

## 一般化の課題 (M-sized, 不確実)

literal J(S) 一般形 `Z(J(S))·O_{p'}(G)◁G` を全 odd solvable G で:
1. **O_{p'} reduction**: L(S) と同じく Ḡ=G/O_{p'}(G) へ商、S̄=mk(S)≅S。tractable (L(S) mirror)。
2. **⚠ ZJ hypothesis discharge (crux)**: `normalJ_normal_of_odd` は `C_G(Z(P))=P` (P self-centralizing)
   を要求。これは L(S) 形が要らない強い条件。一般 odd solvable G (O_{p'}=1) で `C_G(Z(P))=P` は
   **自動でない**。標準 Glauberman ZJ は G p-stable (odd ⟹ 成立) + p-constrained (C_G(O_p(G))≤O_p(G)、
   solvable+O_{p'}=1 で成立) を要求だが、repo の `Ch07.normal_J` の hypothesis `C_G(Z(P))=P` とは別。
   ⟹ **Ch.7 に p-constrained 版 ZJ entry point があるか、`C_G(Z(P))=P` を discharge する route が
   あるか要調査**。

## 判断メモ

book 自身が L(S) を推奨代替として提示 (Remark)、L(S) 一般形は済。J(S) 一般形は genuine numbered
result だが FT gate 無 + ZJ hypothesis 不確実。**subagent が ZJ discharge を tractable と判断すれば
形式化、intractable なら (a) Ch.7 の p-constrained ZJ を先に整備 or (b) L(S) 形が role を満たす旨を
docstring 注記して pending 化** (feedback-generalize-specialized-fully の「一般化が数学的に無意味」
判定 = book が L(S) を推奨、要検討)。

## 参照

- BG mmd L1990-1994 (Thm 6.2 + Remark)、App.B (B.4/L(S))、既存 AppB_Thm62 / S06_Additional /
  Isaacs Ch07 (normal_J, ZJ)、survey L351

## 進捗 (2026-07-18) — O_{p'} reduction 済 (conditional)、残 = Glauberman ZJ

`S06_Thm62JS.zCenterThompsonJ_sup_oPiCore_normal_of_reduced` (commit): O_{p'} reduction を
conditional lemma として sorry-free・axiom-clean で landing (hZJ = O_{p'}=1 の J-ZJ case を仮定)。
L(S) 一般形の reduction を mirror。

**残 gap = hZJ = Glauberman Z(J) 定理** (Z(J(S))◁G, odd solvable, O_{p'}=1)。Isaacs FGT が意図的に
省いた major result (L(S) substitute の存在理由)。repo の `Ch07.normal_J` は `C_G(Z(P))=P` を要求し
非 abelian P で導出不可 (反例: extraspecial P)。⟹ 標準 Glauberman ZJ (p-stability from oddness +
p-constrainedness) の形式化が要る = **major**。

**判断 (pending 理由)**: book 自身が L(S) を推奨代替として提示し L(S) 一般形は済 + FT 消費ゆえ
BG Thm 6.2 の role は満たされている。J(S) literal は FT gate 無の低優先。Glauberman ZJ (Isaacs Ch.7
拡張) は独立の major task ゆえ、着手するなら別途 Ch.7 ZJ 整備として (lane a の Ch.9 とは別、Ch.7 は
lane c/共有)。**「一般化が数学的に無意味」ではない (genuine numbered result) が、major な upstream
(Glauberman ZJ) 待ちの正当な繰延**。

---

## 判定 (2026-07-19): **blocked on issue 3024** — pending へ

crux (「ZJ hypothesis discharge」) を調査し、**tractable でないことが確定**した。

### 1. repo に p-stable + p-constrained 版 ZJ は無い

`J`-normality の entry point を全数調査した結果、**すべて `C_G(Z(P)) = P` を経由**していた:

| 定理 | 所在 | 仮説 |
|---|---|---|
| `Isaacs.Ch07.normal_thompsonJ_of_le_opCore` | `S7B1_NormalJ.lean:1568` | `J(P) ≤ O_p(G)` のみ |
| `Isaacs.Ch07.thompsonJ_le_opCore_of_normal_J_hypotheses` | `S7B2_NormalJ_PComplement.lean:1308` | `p≠2`, `IsPiSeparable {p} G`, Sylow-2 可換, `O_{p'}=⊥`, **`C_G(Z(P))=P`** |
| `Isaacs.Ch07.normal_J` | `S7B2:1425` | 同上 |
| `BG.Ch1.S06.thompsonJ_le_opCore_of_odd` / `normalJ_normal_of_odd` / `thompsonJ_le_oPiPrimePiCore_of_odd` | `S06_Additional.lean:115/134/152` | 上の odd+solvable 特殊化 |

1 番目は仮説が軽いが**使えない**: `J(P) ≤ O_p(G)` は `J(P) ⊴ G` と同値で、これは一般に偽
(Thompson の normal-J と Glauberman ZJ の差そのもの)。

なお **ZJ の仮説 2 つは repo に在る** — `BG.AppA.IsPStable` (`AppA_PStability.lean:127`) と
p-constraint (`Isaacs.Ch07.centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot`,
`S7B1_NormalJ.lean:68`)。**欠けているのは ZJ 定理本体**。

### 2. `C_G(Z(P)) = P` は discharge できない (反例)

`p = 7`、`P = 7^{1+2}` (指数 7)、`C₃ ≤ SL(2,7)` (`3 ∣ 7−1` ゆえ存在)、`G = P ⋊ C₃` (位数 1029)。
奇数・solvable・`O_{7'}(G) = 1` だが `C₃` は行列式 1 で作用して `Z(P)` を中心化 ⟹
`C_G(Z(P)) = G ≠ P`。

### 3. BG 自身が証明を書いていない / math-comp も回避している

BG p.49 (PDF; `.mmd` は該当ページを落とす) は "Proof. **G**, Theorem 6.5.1, p. 234 and
Theorem 8.2.11, p. 279. □" のみ。**G** 8.2.11 = Glauberman ZJ。
math-comp も ZJ を形式化せず Puig `L(S)` で代替 (`coq/theories/BGappendixAB.v:16`,
`BGsection1.v:35`)。BG mmd L4593 も「odd order に絞れば `J(S)` の代わりに別の特性部分群で
より短い証明になる」と述べており、**代替こそが要点**。

⟹ 残るのは **Gorenstein Ch.8 §2 をまるごと移植する**道のみ = **issue 3024** (2,000-4,000 行 /
複数 session、加えて `J(P)` の定義違い (Gorenstein=abelian 最大位数 vs repo=elementary
abelian 最大位数) の設計判断が要る)。

### 対応

- 本 issue は **`pending/` のまま据え置き**、blocker が issue 3024 と確定した (従来は
  「crux が不確実」という理由での pending だった)。恒久対象外ではない。
- `S06_Additional.lean:130` の docstring 「一般形は `O_{p'}(G)` で商を取り本定理に簡約する
  (後続コミット)」は**誤り**だったので訂正済 (反例と正しい経路を明記)。この docstring を
  信じた session は行き止まりに入るところだった。
- 隣接する tractable な穴 (**BG Thm 6.1 一般形**) を発見 → issue 3025 へ分離。
