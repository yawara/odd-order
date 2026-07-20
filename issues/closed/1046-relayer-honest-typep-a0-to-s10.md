---
id: 1046
slug: relayer-honest-typep-a0-to-s10
title: "S15_HonestTypeP2A0 (§8 の A₀(M) 論) を S10 へ移設 — 層の逆転是正"
created: 2026-07-20
---

# S15_HonestTypeP2A0 (§8 の A₀(M) 論) を S10 へ移設 — 層の逆転是正

## 背景

`OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean` (**1266 行**, namespace `OddOrder.Peterfalvi.S15`)
の内容は実質すべて **書籍 §8** — 型 `𝒫` の書籍忠実な支持集合
`A₀(M) = A(M) ∪ V^M` (`S10.typePACore0`) とその (8.13)/(8.15 claim 1) 級の性質 — であって
§13 (= repo S15「The Subgroups S and T」) の内容ではない。

同型の層の逆転は本日 1 件是正済: `sSet_finite` (§9 の事実が `S15_SAndT_Setup/HypothesisBasics`
に居た) → `S11_MaximalII_III_IV/CliffordData` へ移設 (commit 998d28af5)。

## 何が block されているか

issue 1042 の**型一様な (8.15.3) の具体化**。一般 producer
`S10.inducedNonKernelFamily_subcoherent` (commit 0f2c3c7bf、axiom-clean) は landed 済で、
`A = typePACore M` / `H = M_σ` を渡せば書籍逐語の (8.15.3) が全型で立つ。その入力 2 つが
**両方 S15 に居るため §10 から呼べない**:

| 部品 | 現在地 | 型仮定 |
|---|---|---|
| `S15.dadeSupportHypothesisData_typePACore` | `S15_SAndT_Setup/SubcoherenceInputs.lean:706` | `IsTypeP` のみ = 型一様 |
| `S15.dadeSupportHypothesisData_typePACore0` | `S15_HonestTypeP2A0.lean:538` | `IsTypeP` のみ = 型一様 |

どちらも書籍 **(8.15) claim 1** そのもの。

さらに下流の issue 1045 ((9.11) の §9 レベル化) も、同じく「§8/§9 の事実が §11/§13 の
packaging に埋まっている」ことが gate なので、本件はその先例・地ならしになる。

## ✅ 依存実測 (2026-07-20, Explore subagent + 自前確認)

**結論: 抽出は clean に可能。ブロッカー無し。** 2 producer とその閉包は §10 以下だけに依存する。

- `dadeSupportHypothesisData_typePACore` (SubcoherenceInputs.lean:703, 44 行) —
  **S15 ローカル依存ゼロ**。単独で移設可能。
- `dadeSupportHypothesisData_typePACore0` (S15_HonestTypeP2A0.lean:538) — 閉包は同ファイル内
  19 補題 (`typePACore_subset_A0Set` … `typePACore0_tame_conj` / `not_isConj_typePACore_typePV`)、
  **約 512 行**。全て bare `{M : Subgroup G}` + `TypePData M` / `IsTypeP M` で述べられており
  `S15.Hypothesis` (S/T setup) を一切参照しない。
- ⚠ docstring が「the one deep `'A0`-`normedTI` pin」と呼ぶ `not_isConj_typePACore_typePV`
  (:489) は **§13 `normedTI` に循環していない**。実体は `M′ ◁ M` の共役安定性 +
  `S10.typePData_typePV_not_mem_derived` + `typePACore0_tame_conj` で、底は
  `BG.Ch4.S16.theoremII_tame_embedding` (BG §16)。**§10-clean**。
- ⚠ **置いていくもの**: `escaping_typePACore0_eq_empty` (:202-219) は閉包外で、
  `S14.typeI_frobenius` 経由で §14 に依存する。抽出範囲から外すこと (連続ブロックでない)。
- 外部参照は全 21 名で計 26 箇所 (うち 14 が `typePACore_subset_A0Set`)、10 ファイル。

## 進捗

### ✅ 段階 1 完了 (2026-07-20): `dadeSupportHypothesisData_typePACore` を S10 へ

`S15_SAndT_Setup/SubcoherenceInputs.lean` (namespace `S15`) → `S10_TypePSupport.lean`
(namespace `S10`)。この移設先は既に `typeP_exists_kappa_hall_pair` /
`escaping_typePACore_mem_sigmaSharp` / `typePACore_isConj_conj_in_M` /
`coprime_FT_signalizer_centralizerIn_typePACore` / `typePACore_subset` を持つので
依存は全て揃っている (import 追加不要)。call site 3 ファイルを `S10.` 修飾。

⚠ **踏んだ罠**: 移設時に `block.replace('S10.', '')` で一括修飾除去したところ、
`BG.Ch3.S10.Msigma_*` → `BG.Ch3.Msigma_*` と
`OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_of_subset_escaping_sigmaSharp` →
`OddOrder.Peterfalvi.dade…` まで潰した。[[lean-systematic-refactor-script]] の
「一括置換は黙って壊す」の実例。**修飾の一括除去は名前空間境界を見ずにやらない**。

### ✅ 段階 2 完了 (2026-07-20): `dadeSupportHypothesisData_typePACore0` + 閉包 19 補題

新 leaf **`OddOrder/Peterfalvi/S10_TypePSupportA0.lean`** (548 行, namespace `S10`,
import は `S10_MinimalSimpleStructure` の 1 本のみ) を作り、下表の 2 ブロックを移設。
`S15_HonestTypeP2A0.lean` は 1266 → 753 行に縮小し、新 leaf を import する。

**verbatim で移せた**: 移設するコードは `S10.foo` 形の修飾を使っており、名前空間 `S10` の
**内側**でも `S10.foo` は解決する (Lean は現名前空間の各接頭辞に対し `<ns>.S10.foo` を試すので
`OddOrder.Peterfalvi.S10.foo` に当たる)。⟹ 段階 1 で踏んだ「修飾の一括除去」を**やらずに済んだ**。

**修飾した参照 = 計 36 箇所 / 11 ファイル**:
`S15_HonestTypeP2A0` 13 / `S15_SSetMemberRFamily` 4 / `S15_NuRowPin` 4 /
`S15_BridgeCharacter` 3 / `S15_TSetMemberRFamily` 2 / `FeitThompsonCharacterData` 5 /
`S16_NonExistenceG/TGapCross` 2 / `S15_SAndT_Setup/{CoherenceEtaOrthogonality,MuColumnPin}` 各 1 /
`AxiomsCheck` 1。
⚠ 完全修飾形 (`OddOrder.Peterfalvi.S15.foo`) は語境界正規表現の `(?<![.\w])` に弾かれて
**最初のパスで漏れた** ので、`S15\.` 明示のパスを別に流して回収した (残余 0 を grep で確認)。

### ⚠ 段階 2 で露見した罠: 推移的 instance は import 名に現れない

`not_isConj_typePACore_typePV` が `((derivedInG M).subgroupOf M).Normal` の instance を
使っていたが、これは元ファイルの **§13 import 閉包から推移的に来ていた**もので、
新 leaf (import 1 本) では合成できずビルドが落ちた。
⟹ その場で導出する `haveI` を追加 (`M'.subgroupOf M` は injective な `M.subtype` に沿った
`map` の comap なので `comap_map_eq_self_of_injective` + `infer_instance`)。

**これが [[relayer-verify-with-build-not-bfs]] の実例**: import グラフ上は §13 に依存が無いと
subagent の閉包照合でも確認できていたが、**instance 合成は import 名に出ない**ので
build でしか露見しない。再層化は必ず build で検証すること。

**行境界を実測で確定済 (2026-07-20)** — `S15_HonestTypeP2A0.lean` 現状の行番号:

| 範囲 | 扱い | 中身 |
|---|---|---|
| 1–47 | 残す | header / import / `namespace S15` / `open` / `variable` |
| **48–201** | **移す (block A)** | `typePACore_subset_A0Set` (49) 〜 `escaping_typePACore0_mem_typePACore` (194、末尾 200) |
| 202–220 | **残す** | `escaping_typePACore0_eq_empty` (209)。⚠ `S14.typeI_frobenius` 経由で **§14 依存** |
| **221–580** | **移す (block B)** | `/-! ### The A₀(S) ⊆ A0Set … -/` (221) 〜 `dadeSupportHypothesisData_typePACore0` (538、末尾 579) |
| 581– | 残す | `(13.18) S-instance 'A0-Dade hypothesis` 以降 |

移設先 = 新 leaf **`OddOrder/Peterfalvi/S10_TypePSupportA0.lean`** (namespace `S10`)。
import は `S10_MinimalSimpleStructure` で足りる (subagent が推移閉包 437 modules を照合し、
使用シンボルの定義 module が全て含まれることを確認済; `S15_SAndT_Setup` /
`S13_PrimeTIResidueBridge` は**閉包に不要**)。⚠ ファイル粒度は ~530 行 = 規約内。

**修飾が要る参照 = 計 ~36 箇所** (実測):
- 元ファイルの残余から **13 箇所** (`dadeSupportHypothesisData_typePACore0` 8 /
  `escaping_typePACore0_mem_typePACore` 2 (行 204, 217) / `typePACore0_conj_mem` 2 (679, 1260) /
  `not_isConj_typePACore_typePV` 1 (588))
- 外部 **~23 箇所** / 10 ファイル (`FeitThompsonCharacterData`, `AxiomsCheck`,
  `S15_{SSetMemberRFamily,BridgeCharacter,NuRowPin,TSetMemberRFamily}`,
  `S15_SAndT_Setup/{TSideDegrees,MuColumnPin,CoherenceEtaOrthogonality}`,
  `S16_NonExistenceG/TGapCross`)。うち 14 は `typePACore_subset_A0Set`。
- `AxiomsCheck.lean:10486` の `S15.dadeSupportHypothesisData_typePACore0` も
  `S10.` へ書き換える。

⚠ **一括置換で `S10.` を消す/付けるのは禁止** (段階 1 で `BG.Ch3.S10.` と
`OddOrder.Peterfalvi.S10.` を壊した実例)。名前ごとに語境界つきで、かつ「既に修飾済でない」
ことを確認して置換する。

## やること

- [x] `S15_HonestTypeP2A0.lean` の依存を実測 (`typePACore0_subset` / `_ne_one` / `_conj_mem` /
      `escaping_typePACore0_mem_typePACore` / `not_isConj_typePACore_typePV` ほか)。
      §8/§10/BG だけに閉じているかを確認する。
- [ ] ファイルを `OddOrder/Peterfalvi/S10_TypePSupportA0.lean` へ移し namespace を `S10` に変更。
      module 名が変わるので **importer 6 件**を更新:
      `FeitThompsonNuGrid` / `FeitThompsonCharacterData` (⚠ spine) /
      `S13_PrimeTIResidueBridge` / `S15_SAndTDefs` /
      `S15_SAndT_Setup/{SubcoherenceInputs,CoherenceEtaOrthogonality}`。
- [ ] `dadeSupportHypothesisData_typePACore` (SubcoherenceInputs 側) も同様に S10 へ。
- [ ] namespace 変更に伴う修飾の修正 (S15 内の call site は `S10.` 修飾が要る)。
- [ ] **edge ごとに `lake build` で検証**する。BFS で import cycle の消滅を見るだけでは不十分
      ([[relayer-verify-with-build-not-bfs]]: `Fintype`/`open scoped` の推移依存は import 名に
      出ず build でのみ露見)。spine file を触るので subagent に丸投げしない。
- [ ] 最後にフルビルド + AxiomsCheck + sorry 非退行を確認。

## ✅ 完了 (2026-07-20)

- 段階 1 (commit 20ef484cc) / 段階 2 (commit dc51c1cb6) とも landed、`lake build OddOrder` green。
- **完了条件を満たした**: `S10.typePACore_subcoherent` (commit 26cb99374) が
  `S10_SubcoherentTypeP.lean` (§10 の file) 内で書けるようになり、issue 1042 の残件が解けた。

## 完了条件 (達成済)

- `S10.inducedNonKernelFamily_subcoherent` に `A = typePACore M` / `H = M_σ` を渡す具体化が
  §10 の file 内で書けること (issue 1042 の残件が解ける)。
- フルビルド green、AxiomsCheck OK、sorry 非退行。

## 参照

- issue 1042 ((8.15) instances; 本件が残件の gate)
- issue 1045 ((9.11) の §9 レベル化; 同型の層の逆転)
- commit 0f2c3c7bf (型一様 (8.15.3) の一般 producer)
- commit 998d28af5 (`sSet_finite` の同型移設、先例)
