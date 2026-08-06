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
- ✅ **`CharacterDifferenceImage → OrthonormalCharacterImageFamily` の変換は既存** —
  `toOrthonormalImage` / `toOrthonormalImage_orthogonal` (`S07_Coherence/DifferenceImage.lean`)。
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

- [x] ~~**step 1 — 変換**~~ ⚠ **不要だった (2026-07-27 訂正)**。新設した
      `CharacterDifferenceImage.toOrthonormalFamily` は、**既存の
      `CharacterDifferenceImage.toOrthonormalImage`** (`S07_Coherence/DifferenceImage.lean`) と
      同一構成だった (`toOrthonormalImage_orthogonal` も同様)。重複は撤去済 (commit dc8d3a5c3)。
      見落とし原因は grep パターンが宣言の**複数行シグネチャ**を想定していなかったこと
      (戻り値型が def 行の 2 行下にある) → memory
      `verify-port-state-by-number-not-coq-name` §I に記録。
      副産物として `inner_zsmul_irreducible_eq` の Appendices → `ZIrrFourier` 移設は保持
      (docstring 自身が指定していた upstream 化、Appendices の 9 consumer が使用中)。
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

---

## 🔓 2026-08-07 REOPENED — 繰延理由が消えた

繰延理由は「これはアーキテクチャ課題なので**書籍被覆を優先**する」だった。2026-08-07 に
Q₈ Brauer–Suzuki が閉じて repo 全体が sorry 0 になり、残スコープは「未形式化の番号付き結果」に
移った。二重実装 (`S08_CoherenceCorePart2/SibleyBounds` の X-chain 次数簿記) を抱えたままだと
その census と一般化作業のノイズになるので、繰延を解除する。

完了条件は本文のまま (`Xset_isCoherent_of_irreducible_X` の証明本体が一般版の呼び出し 1 本に
なること + build green + AxiomsCheck OK + sorry 非退行)。

---

## ✅ CLOSED (2026-08-07) — step 4 完了

### ⚠ 2026-07-27 の診断「§8 DAG の再層化が要る」は**過大評価だった**

当時の記述は「一般 (6.2) leaf が Sibley の case-B 機構に依存している」「10 段の長い経路が残る」
だったが、実測すると **`S08_SixTwoGeneral` が case-B から取っていた宣言は 2 本だけ**だった。
判定方法 = **import 行を消して leaf build を打ち、`Unknown identifier` を読む**
(BFS で経路を眺めるのでなく、コンパイラに列挙させる)。

1. `exists_finEnum_general` (`S08_CaseBEnumeration:216`) — docstring 自身が
   「**Pure formalization (no character theory)**」と書いている `Fintype.equivFin` の包装。
   ⟹ `S08_CoherenceCorePart1` へ移設 (`six_five_c_arith` の前例と同型)。
2. `S07.zSpan_subset_zSupportedSpan` / `coherentDegreeSqNormBound_of_not_coherentW_k_general` —
   それぞれ `S08_GeneralAdjoinWeighted` / `S08_CoherenceCorePart2` に在り、どちらも
   **case-B を閉包に持たない**上流 leaf。⟹ 直接 import すれば済む。

⟹ ファイル手術は **import 3 行 + 25 行の移設**で完了。閉包実測:

| leaf | 閉包 (before → after) | CaseB 系 |
|---|---|---|
| `S08_SixTwoGeneral` | — → **147** | **なし** |
| `S08_SixSixGeneral` | 189 → **158** | **なし** |

`S08_CoherenceBasic` から `S08_SixSixGeneral` を import しても循環しないことを **build で確認**
(BFS だけでは不十分 = [[relayer-verify-with-build-not-bfs]])。

### step 4 本体

`S08_CoherenceBasic` に橋を 3 本追加:

- **`SibleyDadeHypothesis.toInducedFamilyTauData`** — `hyp.tau`
  (= `S07.dadeIntegralCharacterMap hyp.dade hyp.dade.fullDadeIsometryData`) から (5.2.b) の
  τ 部 4 フィールドを構成。中身は §7 の Dade 補題 3 本
  (`dadeIntegralCharacterMap_inner_eq_on_supported_span` /
  `_mem_ZIrr_of_supported` / `_apply_one_eq_zero`) をそのまま填めるだけ
  (`S13_SixTwoImageData.inducedFamilyImageData` と同じ形)。
- **`mem_supportInSubgroup_sharpImage`** / **`one_notMem_supportInSubgroup_sharpImage`** —
  `A₀ = H^#` に対する `hKsupp` / `h1A`。`sharpImage H = (H.map L.subtype) \ {1}` なので両方 1 行。

これで `Xset_isCoherent_of_irreducible_X` の**証明本体が一般版の呼び出し 1 本**になった:

```lean
  letI : H.Normal := hyp.H_normal
  rw [hyp.Xset_eq_inducedKernelFamily_sdiff Z] at hX hXne ⊢
  exact xSet_isCoherent_of_irreducible_X (K := H) hyp.toInducedFamilyTauData hyp.card_L_odd …
```

**183 行 → 68 行** (うち docstring 44 行)。`XAdjoinStepInput` の構成は (6.6) 経路から消え、
`S08_CoherenceBasic` に残る言及は docstring 2 箇所のみ (実測)。

### 完了条件の充足

- [x] `Xset_isCoherent_of_irreducible_X` の証明本体 = 一般版の呼び出し 1 本
- [x] `S08_CoherenceCorePart2/SibleyBounds` の X-chain 次数簿記が (6.6) 経路から不要
- [x] build green / `--strict` 警告ゼロ / AxiomsCheck OK / sorry 非退行 (0 のまま)
