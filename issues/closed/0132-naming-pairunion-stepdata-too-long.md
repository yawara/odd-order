---
id: 132
slug: naming-pairunion-stepdata-too-long
title: "命名: PairUnionBaseAnchorCommonIndexPrimePowerStepData 系が長すぎて 100 桁を切れない (lane a 判断)"
created: 2026-07-20
---

# 命名: `PairUnionBaseAnchorCommonIndexPrimePowerStepData` 系が長すぎて 100 桁を切れない

## 事実

issue 0123 の longLine wave で、**行の折り返しでは解消できない** longLine が 2 件残った。
どちらも「宣言名そのものが 100 桁を超える」ケース:

| file:line | 宣言名 | 長さ | 参照箇所 |
|---|---|---|---|
| `S08_CoherenceBasic.lean:867` | `Xset_centralCommutator_isCoherent_from_…_withCover_of_frobenius` | **106** | 1 (定義のみ) |
| `S08_CoherenceTheorems.lean:416` | `indChainDecomposition_of_frobenius_…_generator_mixed_inner` | **101** | 2 |

いずれも `noncomputable def` の**名前が単独行に置かれている**形 (indent 4 + 名前) で、
列 0 に置いても 100 桁を超えるため、書式変更では直せない。

## 原因は個々の宣言名でなく、根にある構造体名

- 構造体 **`PairUnionBaseAnchorCommonIndexPrimePowerStepData`** (`S08_CoherenceBasic.lean:696`、
  **47 文字**) が 5 つの概念 (pair-union / base / anchor / common-index / prime-power) を
  1 語に連ねている。
- 派生する宣言名がこれを丸ごと含むため、接尾辞 (`_of_frobenius` / `_withCover_of_frobenius` /
  `_generator_mixed_inner` / `_of_irreducible_X`) を足すと必ず 90〜106 文字になる。
  現在この語幹を含む識別子は **26 箇所**:

  ```
   2  pairUnionBaseAnchorCommonIndexPrimePowerData
   5  …_generator_mixed_inner
  10  …_of_frobenius
   5  …_of_irreducible_X
   1  …_withCover_of_frobenius
   3  …_withCover_of_irreducible_X
  ```

⟹ 個々の宣言だけを短くすると**構造体名との対応が切れる**ので、直すなら
**構造体名ごと**縮めるのが筋。

## なぜ hub が独断で直さないか

- `OddOrder/Peterfalvi/S08_*` は **lane a の territory**。
- 「何と呼ぶべきか」は書式でなく**設計判断** (どの概念を名前に残し、どれを docstring に
  落とすか)。hub の機械的な call-site 追従の範囲を超える。
- 26 箇所の rename 自体は機械的だが、**新しい名前の選定**が本質。

## 提案 (lane a が判断する)

語幹を縮める候補 (いずれも docstring に完全な条件を書いて補う前提):

- `PairUnionStepData` — 残り 4 概念は docstring へ
- `AnchoredPrimePowerStepData` — anchor と prime-power を残す
- `SibleyStepData` — 定理の帰属 (Sibley) で呼ぶ

決めたら `git grep -l` で 26 箇所を一括置換し、full build で検証する
(純粋な rename ゆえ意味は不変)。

## 暫定処置 (本 issue 起票時点)

**何もしていない** — 2 件の warning は残したまま。`set_option linter.style.longLine false in`
で黙らせることは**あえてしない**: 名前が長すぎるという事実が見えなくなるだけで、
本 issue の対象が消えるわけではないため。

なお同じ語幹を含む 3 件目 (`S08_CoherenceTheorems.lean:441` の
`hyp.Xset_commutator_…_of_frobenius` 呼び出し) は、**binder のインデントを 1 段浅くする**
書式変更だけでちょうど 100 桁に収まったので解消済 (commit は 0123 の wave)。

## 完了条件

`S08_CoherenceBasic.lean:867` と `S08_CoherenceTheorems.lean:416` の longLine warning が
消えること (= 語幹の rename が landing すること)。

## 参照

- `issues/0123-linter-warnings-cleanup.md` (longLine wave 本体)
- CLAUDE.md「トレーサビリティ」(定理名は記述的命名、番号は docstring のみ)

---

## 📝 2026-07-24 現状 — lint gate 観点は解消済み、残るのは命名判断のみ

該当 2 行は per-decl `set_option linter.style.longLine false in` で明示例外化済み
(`S08_CoherenceBasic.lean:859` / `S08_CoherenceTheorems.lean:409`) — 2026-07-24 の `--strict`
gate 切替後も警告は出ない。本 issue に残るのは **`PairUnionBaseAnchorCommonIndexPrimePowerStepData`
系の語幹短縮という命名リファクタ判断** (owner = lane a) のみで、lint 債務ではない。

---

## ✅ 2026-07-25 解決 — 両系統を一括 rename して close

ユーザー指示で main セッションが実施 (lane a は 1055 凍結中・hub 裁定待ちのため、この単発
リファクタは main で消化)。**姉妹構造体 (anchor 無し版) が並存していた**ので、片方だけ縮めると
「短い名前 = anchored 版、長い名前 = より弱い無印版」という逆転が起きる。よって**両系統を
一貫した対で rename** した:

| 旧 | 新 |
|---|---|
| `PairUnionBaseAnchorCommonIndexPrimePowerStepData` (47字) | `AnchoredPairUnionStepData` (25字) |
| `pairUnionBaseAnchorCommonIndexPrimePowerData` (派生語幹) | `anchoredPairUnionStepData` |
| `PairUnionCommonIndexPrimePowerStepData` (38字) | `PairUnionStepData` |
| `pairUnionCommonIndexPrimePowerData` (派生語幹) | `pairUnionStepData` |

- 選定理由: 姉妹との**判別子は anchor の有無だけ** (anchored 版 = `hanchor` field 追加 +
  `hlt`/`hlemem` を内部導出) なので、名前に残す概念は `Anchored` + `PairUnion` の 2 つで足りる。
  common-index / prime-power / base の各条件は両構造体の docstring (T8.11v / T8.11v1) が
  従来どおり全 field を記述している。issue 提案の `SibleyStepData` は namespace が既に
  `SibleyDadeHypothesis` で冗長になるため不採用。
- 派生宣言の語幹が旧 `…PrimePowerData` (Step 脱落) から `…StepData` になり、構造体名と
  **正確に一致**するようになった (対応が改善)。
- adapter 3 兄弟 (`xAdjoinStepInput_of_pairUnion[_baseAnchor]_commonIndexPrimePowerSums` 等) は
  構造体名を含まず 100 桁問題も無いので不変。
- per-decl longLine 例外 2 件 (`S08_CoherenceBasic` / `S08_CoherenceTheorems`) を除去 —
  最長の派生名 `Xset_centralCommutator_isCoherent_from_anchoredPairUnionStepData_withCover_of_frobenius`
  は 87 字で単独行に収まる。残る per-file 例外は `AxiomsCheck.lean` (意図的恒久) のみ。
- 純 token rename: Lean 6 file + live notes 5 file (`notes/peterfalvi/s08_*`, `s09_*`) を
  script 一括置換、full build + AxiomsCheck で検証。
- ついでに S09 の**死んだ longLine 例外を全廃**: `QuadraticTerm.lean` の block 例外 (265/338 対、
  保護対象は旧語幹の 2 行 = 本 rename で解消) と per-decl 4 件 (433/459/490/545、rename 以前から
  100 桁超の保護対象が無い stale) + `CoherenceFormula.lean:24-25` の隣接 false/true sandwich
  (完全に no-op)。⟹ **longLine の per-decl/block 例外は repo 全体で `AxiomsCheck.lean` のみ**になった。
