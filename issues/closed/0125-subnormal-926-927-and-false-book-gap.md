---
id: 125
slug: subnormal-926-927-and-false-book-gap
title: "Isaacs 9.26/9.27 を subnormal 版へ + 「書籍に gap」という誤った docstring 3 件の訂正"
created: 2026-07-19
owner: lane a (Isaacs 全域)
---

# Isaacs 9.26 / 9.27 を subnormal 版へ + 誤った「書籍 gap」注記の訂正

issue 9150 (mmd の `⊲⊲` 潰れ監査) の Isaacs 走査で確定した **2 件の MISMATCH** と、
それに伴って repo に混入していた**教科書への誤った瑕疵指摘**の是正。

監査方法: PDF から `⊲⊲` (pdftotext で `«`) を抽出 → 作用ドットの OCR ノイズを除いて
28 件の真の subnormal 使用を特定 → 23 件を **PDF ページ画像**で 1 件ずつ確認。
21 件 OK (9.13 / 9.21 は lane a の issue 1037 対応で既に修正済)、残り 2 件が下記。

## (1) Lem 9.26 — MISMATCH

**書籍 (p. 287、PDF p.300 のページ画像で確認)**:
> Let `G = SP`, where `G` is a finite group, and where **`S ⊲⊲ G`** and **`P ⊲ G`**,
> and `P` is a `p`-group. Then `O^p(G) = O^p(S)`.

`S` は **subnormal**、`P` は normal。

**repo**: `PResidual.lean:200` `pResidual_eq_map_subtype_of_sup_isPGroup` が
`[S.Normal] [P.Normal]` を要求 = **書籍より真に強い**。一般 subnormal 版は未形式化。
ambient 版 `pResidualOf_sup_eq` (PResidual.lean:389) も normal のみ。

⚠ docstring が出典を **p. 283 と誤記** (正しくは p. 287) し、仮説を `S ◁ G` と書いている
→ 意図的な特殊化の記録ではなく**取り違え**ゆえ MISMATCH 判定。

**修正の見立て** (binder を緩めるだけでは済まない): 現行証明は `S.Normal` を本質的に使う
(`R_S.Normal` を characteristic-in-normal から得る / `IsPGroup p (G ⧸ S)` に商が要る)。
書籍の証明経路が正しく、機械化可能:
`Subgroup.IsSubnormal` は inductive predicate (同ディレクトリの `SubnormalClosure.lean:115`
で既に構造帰納に使用) なので、それで帰納 → `S ≤ M ⊲ G`, `M < G` を取り、Dedekind 則で
`M = S(M ⊓ P)` → IH で `O^p(M) = O^p(S)` → `G/O^p(M)` が `p`-群ゆえ `O^p(G) = O^p(M)`。
部品は全て同ファイルに在る: `pResidualOf_sup_eq` (normal の base case) /
`Subgroup.mul_normal` (Dedekind) / `le_normalizer_pResidualOf_of_subnormal_two`
(PResidual.lean:417 = まさにこの議論を defect 2 で 1 回実行したもの)。新規理論は不要。

## (2) Cor 9.27 — MISMATCH

**書籍 (p. 287、ページ画像で確認)**:
> Let `G` be a finite group. Suppose that **`S ⊲⊲ G`**, and let **`P ⊲ G`** be a `p`-group.
> Then `P` normalizes `O^p(S)`.

**repo**: `PResidual.lean:189` `pResidual_map_subtype_normal` が `[S.Normal]`。
subnormal 被覆は `le_normalizer_pResidualOf_of_subnormal_two{,_rel}` (PResidual.lean:417/481)
の **defect 2 限定**のみで、一般 subnormal 版は無い。

**修正の見立て**: (1) の一般 9.26 が入れば書籍の 1 行経路で従う
(`O^p(S) = O^p(SP)` (9.26) かつ `O^p(SP)` は `SP` で characteristic ゆえ `P` が正規化)。
⟹ **実作業は 9.26 のみ**で、9.27 は落ちてくる。

## (3) ⚠ 「書籍に gap がある」という誤った注記 3 件 — 要訂正

issue 1037 と同じ失敗モード。9.27 を normal 版と読んだ結果、**書籍が誤っていると結論**して
しまっている。ページ画像で確認した結果、**これらの指摘はすべて誤り**:

| 箇所 | 現在の記述 | 事実 |
|---|---|---|
| `ThompsonWielandt.lean:143-145` | 「ここが書籍 p. 284 の『V ◁ M ◁ H, so V ◁ H』の箇所」 | 書籍 p.287 は "Since `V ⊲ K`, we have `V ⊲ M ⊲ H`, so **`V ⊲⊲ H`**" と subnormal で結論しており、`V ◁ H` とは書いていない |
| `ThompsonWielandt.lean:180-181` | 「書籍は『V ◁ H かつ P ◁ H ゆえ Cor 9.27』と述べるが, 実際には V ◁ M ◁ H (subnormal)」 | 書籍 p.288 は "Since **`V ⊲⊲ H`** and `P ⊲ H`, it follows by Corollary 9.27 that `P` normalizes `Y = O^p(V)`" = subnormal 版 9.27 の正しい適用。同ページで 2 度目も同形 ("Since `N ⊲ D`, we have `U^k ⊲⊲ D`, and by Corollary 9.27 applied in the group `D`…") |
| `PResidual.lean:410-411` | 「書籍 p.284 は … normal 版の Cor 9.27 を適用するが, subnormal から normal は一般には従わない」 | 同上。書籍に gap は無い |

ページ参照も p.284 → **p.287/288** が正しい。

## やること

- [x] 一般 subnormal 版 Lem 9.26 を証明する (上記の帰納経路)
- [x] 一般 subnormal 版 Cor 9.27 を 9.26 から導く
- [x] `le_normalizer_pResidualOf_of_subnormal_two{,_rel}` を一般版の系に整理
- [x] ThompsonWielandt の該当 call site を「書籍どおりの Cor 9.27」を cite する形に戻す
- [x] **上記 (3) の誤った注記 3 件を訂正**し、ページ参照を p.287/288 に直す
- [x] 既存の normal 版は**消さない** (bound がより鋭い等の独立価値がありうる。9150 の方針)

## 完了条件

一般 subnormal 版の 9.26 / 9.27 が sorry-free で入り、(3) の誤った注記が訂正されている。

## 完了 (2026-07-19, commit 7f206f802)

### 入った定理 (すべて sorry-free / axiom-clean)

| 名前 | 内容 |
|---|---|
| `pResidual_eq_pResidualOf_of_isSubnormal` | **Lem 9.26**: `G = SP`, `S ◁◁ G`, `P ◁ G` p-群 ⇒ `O^p(G) = O^p(S)` |
| `pResidualOf_sup_eq_of_isSubnormal` | 上の ambient 版 |
| `le_normalizer_pResidualOf_of_isSubnormal` | **Cor 9.27**: `S ◁◁ G`, `P ◁ G` p-群 ⇒ `P ≤ N_G(O^p(S))` |
| `le_normalizer_pResidualOf_of_isSubnormal_rel` | 上の相対形 (ambient = 部分群 `H`) |

9.26 の証明は書籍の `|G|` 帰納を `Subgroup.IsSubnormal` の**構造帰納**に置換
(書籍の `M` = 帰納の `K`)。step 段は Dedekind 則 `K = S(K ⊓ P)` +
既存 normal 版 `pResidualOf_sup_eq` を base case として使うだけで、新規理論は不要だった
(見立てどおり)。

### defect-2 版の整理

- `le_normalizer_pResidualOf_of_subnormal_two` (絶対形) は消費者 0 だったので**削除**。
- `_rel` は normalClosure を組む ~50 行の独自証明を捨て、一般版へ長さ 2 の鎖を渡す
  **4 行の adapter** に置換 (Thm 9.24 の Step A/D 2 箇所で使用中ゆえ名前は存置)。

### ページ参照

(3) の 3 件に加え、§9C 全域で p.283/284 参照が系統的にずれていたので一括修正
(p.283 は §9B の 9.20–9.22)。正しくは **Thm 9.23 = p.285 / Thm 9.24 statement = p.286 /
Lem 9.25–9.27 = p.287 / Thm 9.24 の証明 = pp.287–288**。

## 参照

- issue 9150 (監査本体)、issue 1037 (9.13/9.21 の実害初出)
- memory `mmd-collapses-subnormal-symbol`
- 該当ファイルは全て `OddOrder/Isaacs/Ch09_MoreSubnormality/` = **lane a 所有**
