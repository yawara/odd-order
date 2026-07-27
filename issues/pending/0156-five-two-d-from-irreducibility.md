---
id: 156
slug: five-two-d-from-irreducibility
title: "既約な部分族では (5.2.d)/(5.2.e) を (5.2.b) から導出する — (6.6) の Sibley/一般 二重実装の解消"
created: 2026-07-27
---

# 既約な部分族では (5.2.d)/(5.2.e) を (5.2.b) から導出する

## 背景 — [issue 0155](closed/0155-pf-six-six-general-kernel.md) からの派生

0155 で Peterfalvi (6.6) の coherence 半分が一般 kernel `K`・任意の τ で完成した
(`S08_SixSixGeneral.xSet_isCoherent_of_irreducible_X`)。ところが当初立てた完了条件
「Sibley 版 `S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X` がその特殊化に置き換わる」は
**達成不能**であることが実測でわかった。両者は仮説が違う:

| | 一般版 (0155) | Sibley 版 |
|---|---|---|
| Hypothesis (5.2) の担い手 | `InducedFamilyImageData A₀ K` — (5.2.b) の τ に加えて **𝒮 の全 member** の像族 `R(χ)` と (5.2.e) | `SibleyDadeHypothesis` — **像族フィールドを持たない** |
| 既約 member の (5.2.d) | `RD.R χ` | Dade 写像からその場で構成 (`dadeOrthonormalCharacterImageFamilyOfDiff`) |
| 可約 member の (5.2.d) | 呼び出し側が供給 (§13 の μ-grid 列族 `S13_SixTwoImageData.inducedFamilyImageData`) | **不要** — (6.6) は `𝒳 ⊆ Irr L` しか使わない |

書籍の (6.1)/(6.4) は「𝒮 が Hypothesis (5.2) を満たす」を仮定するので、一般版の仮説は
**書籍どおり**であって過剰ではない。しかし (6.6) の証明が実際に (5.2.d)/(5.2.e) を使うのは
**𝒳 の member (すべて既約) についてだけ**なので、書籍より**強い**定理が取れる。

## やること

**既約な member については (5.2.d)/(5.2.e) が (5.2.b) から導出できる**ことを使い、(6.6) の
一般版を「τ のデータだけ」で述べ直す。そうすれば Sibley 版はその instantiation になる。

材料はほぼ揃っている (2026-07-27 実測):

- ✅ `characterDifferenceImage_of_irreducible` (`S08_SixFiveGeneral:137`) —
  τ の等長性・値域・`τφ(1) = 0` だけから、既約非実 `χ` に対し (5.3.a) の符号付き 2 元対
  `τ(χ−χ̄) = ε·(μ−ν)` (`μ ≠ ν` 既約、`ε = ±1`) を作る。
- ✅ `tau_conjDiff_inner_eq_zero_of_orthogonal` + `orthogonal_of_tau_conjDiff_inner_eq_zero`
  (同 leaf) — (5.2.e) も τ だけから出る。実際 `hypothesisOfSubfamily` は現にこの経路で
  `S07.Hypothesis` を組んでおり、`RD.R` / `RD.orthogonal` を**一切使っていない**。
- ❌ **欠けている部品**: `CharacterDifferenceImage → OrthonormalCharacterImageFamily` の変換。
  前者は `{μ, ν}` と符号 `ε` を持つ構造、後者は `Finset` `R(χ)` で `τ(χ−χ̄) = ∑_{α ∈ R(χ)} α`
  を要求する。変換は `R(χ) = {ε·μ, −ε·ν}`:
  - 和 = `ε·μ − ε·ν = ε·(μ−ν) = τ(χ−χ̄)` (`image_eq`)
  - 正規直交: `μ ≠ ν` 既約 + `ε² = 1`
  - 2 元が相異なる: 内積 `⟨ε·μ, −ε·ν⟩ = 0 ≠ 1 = ⟨ε·μ, ε·μ⟩`
  - `mem_ZIrr`: `±ε·(既約)` は虚指標
  - (5.2.e) の移送: 変換後の member は元の `μ, ν` の `±` 倍なので
    `CharacterDifferenceImage.Orthogonal` からそのまま従う。
  置き場は `S08_SixTwoThreeFromImageFamilies.lean` (446 行、`OrthonormalCharacterImageFamily.congrChi`
  と同じ「2 つの (5.2.d) の形をつなぐ」トピック)。

### 手順

1. **変換の追加** (上記)。独立に価値がある — repo にある (5.2.d) の 2 形を初めて橋渡しする。
2. **`InducedFamilyImageData` の分割**: τ 部
   (`tau` / `tau_isometry` / `tau_mem_ZIrr` / `tau_apply_one`) を `InducedFamilyTauData` に切り出し、
   `InducedFamilyImageData extends InducedFamilyTauData` とする (既存の `RD.tau_*` は親射影で不変)。
   唯一の constructor は `S13_SixTwoImageData.inducedFamilyImageData` (`where` 構文なので
   フラットなフィールド指定のまま通るはず — 要検証)。
3. **τ 部だけで述べ直す**: `tau_conjDiff_inner_eq_zero_of_orthogonal` / `hypothesisOfSubfamily` /
   `hypothesis` / `adjoinHisom` (実測でいずれも τ 部しか使っていない) と、(6.6) の
   `xSetHypothesis` / `xBaseBlock_isCoherent` / `xAdjoinStep_of_degreeRatios` /
   `xSet_isCoherent_of_irreducible_X`。`R`/`orthogonal` は `hirr` から (1) 経由で内部生成する。
   旧 `InducedFamilyImageData` 版は 1 行の特殊化として残し、コンパイラに同値性を検証させる。
4. **Sibley 版を特殊化に置換**: `SibleyDadeHypothesis` から `InducedFamilyTauData` を作り
   (Dade 写像の等長性・`ℤ[Irr G]` 値域・`τφ(1) = 0` はすべて既存)、
   `hyp.Xset Z = xSet H Z` (`Xset_eq_inducedKernelFamily_sdiff`, `S08_DegreeSums/CoherenceGlue:494`)
   と `hyp.xBaseBlock Z = xBaseBlock H Z` (要確認) で橋渡しする。
   `A₀ = S04.supportInSubgroup (sharpImage H) L` に対する `hKsupp` / `h1A` も要確認。

## 進捗 (2026-07-27)

- [x] **step 1 — 変換** `CharacterDifferenceImage.toOrthonormalFamily` (`R(χ) = {ε·μ, −ε·ν}`) と
      (5.2.e) の移送 `toOrthonormalFamily_orthogonal`。`S08_SixTwoThreeFromImageFamilies`。
      併せて `inner_zsmul_irreducible_eq` を Appendices から `ZIrrFourier` へ移設。axiom-clean。
- [x] **step 2 — 構造分割** `InducedFamilyTauData` (τ 部) / `InducedFamilyImageData extends …`。
      τ 部しか使っていなかった `adjoinHisom` / `tau_conjDiff_inner_eq_zero_of_orthogonal` /
      `hypothesisOfSubfamily` / `hypothesis` / `xSetHypothesis` を τ 部の namespace へ移動。
      ⚠ **dot-notation は親構造を辿るので既存 caller は無変更で通った** (実測)。
- [x] **step 3 — (6.6) chain を τ 部だけで述べ直す**。`xBaseBlock_isCoherent` /
      `xAdjoinStep_of_degreeRatios` / `xSet_isCoherent_of_irreducible_X` が
      `InducedFamilyTauData` を取るようになり、(5.2.d)/(5.2.e) は
      `hypothesisOfSubfamily.difference_image` + step 1 の変換で**導出**される。
      ⟹ **一般 (6.6) は書籍 (6.1) より弱い仮説で成立する**。AxiomsCheck 更新済。
- [ ] **step 4 — Sibley 版の置換: ⛔ import DAG に阻まれる (2026-07-27 実測)**

### step 4 の障害 — 数学ではなく §8 の import 階層

`S08_SixSixGeneral` は **`S08_CoherenceBasic` の下流**なので、`S08_CoherenceBasic` 側から
一般版を呼ぶことができない (循環)。当初 1 本と見えた阻害 edge
`S08_SixFiveGeneral → S08_PGroupReduction` は解消済 (下記) だが、**まだ長い経路が残る**:

```
S08_SixSixGeneral → S08_SixFiveGeneral → S08_SixTwoThreeFromImageFamilies
  → S08_SixTwoGeneral → S08_CaseBEnumeration → S08_CaseBAssembly
  → …(case-B 一式)… → S08_CoherenceCore → S08_RestrictExtensionDvd
  → S08_XBlockCounting → S08_CoherenceBasic
```

すなわち **一般 (6.2) leaf (`S08_SixTwoGeneral`) が Sibley の case-B 機構に依存している**のが
根本。逆向き (Sibley 側を下流へ移す) も不可 —
`Xset_centralCommutator_isCoherent_of_{frobenius,c2_caseA}` の consumer が
`S08_XBlockCounting` / `S08_RestrictExtensionDvd` で、これらは上記経路の途中にある。

⟹ step 4 は **§8 DAG の再層化** (一般 leaf 群を Sibley 機構から独立させる) を伴う。
数学は既に揃っている (step 1-3) ので、残るのはファイル手術のみ。
⚠ 再層化は BFS で cycle 消滅を見るだけでは不十分 (transitive な instance/open scoped 依存は
import 名に出ない) — **edge ごとに build 検証**すること。

### 副産物 (2026-07-27 実施済)

`six_five_c_arith` (純 ℕ 算術、群論を一切使わない) が `S08_PGroupReduction` に置かれていたため、
一般 (6.5)/(6.6) leaf が Sibley 側 p 群 reduction ファイル一式を import 閉包に引き込んでいた。
`S08_CoherenceCorePart1` (同種の算術補題が集まる上流 leaf) へ移設し、
`S08_SixFiveGeneral → S08_PGroupReduction` の edge を削除
(`S08_SixSixGeneral` の閉包 197 → 189 module)。

## 完了条件

`S08_CoherenceBasic.Xset_isCoherent_of_irreducible_X` の証明本体が一般版の呼び出し 1 本になり、
`S08_CoherenceCorePart2/SibleyBounds` 側の X-chain 次数簿記 (`XAdjoinStepInput` 系) が
(6.6) 経路から不要になること。build green + AxiomsCheck OK + sorry 非退行。

⚠ これは**書籍被覆のギャップではなくアーキテクチャ課題** (重複解消)。step 1-3 の成果物
「既約族に対する (5.2.d)/(5.2.e) の導出」は書籍より強い主張なので数学的にも意味があり、
そこは landing 済。残る step 4 は純粋にファイル階層の問題なので、書籍被覆を優先して繰延する。
