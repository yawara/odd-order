# Isaacs *Finite Group Theory* — 実測 frontier (2026-07-19, lane a)

> **これが Isaacs の frontier 正本**。`notes/isaacs/ch*.md` の「未着手/残作業」ラベルは
> **rot している** (ch03 の 3 件が全て完了済だった実例 = commit e97d16793)。
> 着手前は必ず本 note か実測 grep で確認する ([[verify-port-state-by-number-not-coq-name]])。
> Pf 本文側の対応物 = [`../peterfalvi/frontier_measured_2026_07_19.md`](../peterfalvi/frontier_measured_2026_07_19.md)。

## 結論 (先に)

**Isaacs Ch.1–Ch.10 の番号付き結果は被覆完了。未形式化 (= 教科書にあって repo にも mathlib にも無い) は 0 件。**

- **Isaacs 全体の実 sorry = 0** (コメント除去後の実測)。
- 教科書の番号付き結果 **約 305 件** (Ch.1–10) のうち、
  - **267 件** は repo が docstring で明示的に cite (= repo 内に形式化)、
  - **残り 42 件**を個別分類した結果 → **mathlib 被覆 37 件 / repo に記述的名前で在り 5 件 / 未形式化 0 件**。
- ⟹ **残作業は被覆でなく特殊化債務 (別軸)**。sorry を数えても被覆を数えても新規作業は出てこない。

⚠ 42 件が「repo に cite されていない」のは**欠落ではなく設計**: CLAUDE.md「ラッパー方針」により
**mathlib に直接対応がある定理の薄いラッパーは書かない**。よって Sylow C/D、Frattini 論法、
Jordan の定理、Iwasawa 補題、`A_n` 単純性などは *意図的に* repo に無い。
「repo に無い ⟹ 未形式化」と読むのは誤り。

## 測り方 (再現手順)

1. 教科書側の番号付き結果を抽出 — 本文では `N.M. Kind. 文` の形で行頭に出る:
   ```bash
   grep -nE "^\s{0,4}[0-9]{1,2}\.[0-9]{1,3}\.\s*(Theorem|Lemma|Corollary|Definition|Proposition)" \
     references/isaacs/finite-group-theory.pdftotext.txt
   ```
   ⚠ **OCR の落とし穴 3 つ**: (i) `T h e o r e m` のように 1 文字ずつ空く行がある (空白除去して照合)、
   (ii) `1.31. Theorem, i e t |G|` のように `.` でなく `,` が来る、
   (iii) 一部は statement 行が reflow で潰れて行頭に出ない (`2.14 3.15 3.16 3.18 3.19 3.20 3.21 3.24 8.32 10.19 10.25 10.26` の 12 件;
   本文中の相互参照では出現するので**存在はする**)。⟹ 機械抽出だけで「欠番」と判断しない。
2. repo 側の cite を抽出 (docstring 規約 `**Isaacs Thm 1.4**`):
   ```bash
   grep -rhoE "Isaacs [A-Za-z]{0,12} ?[0-9]{1,2}\.[0-9]{1,3}" --include=*.lean OddOrder/
   ```
3. 差分を取り、**1 件ずつ** mathlib / repo (記述的名前) を検索して分類する。
   ⚠ **ファイル名で探して無いことを「未形式化」と結論しない** — Isaacs Thm 3.34 は
   `Ch03_SplitExtensions/HartleyTurull.lean` ではなく `Ch04_Commutators/HartleyTurull.lean:1118`
   (`exists_orbit_card_mul_of_coprime_orbit_card`) に在った (Tier 2 = 3.31–3.34 は Ch.4 §4C–§4D 依存ゆえ)。
4. 実 sorry はコメント除去後に数える:
   ```bash
   find OddOrder/Isaacs -name '*.lean' -exec cat {} + | perl -0777 -pe 's{/-.*?-/}{}gs; s{--.*$}{}gm' | grep -c '\bsorry\b'
   ```

## 章別 (repo 実装規模)

| 章 | leaf 数 | 行数 | 実 sorry |
|---|---|---|---|
| Ch01_Sylow | 3 | 3,643 | 0 |
| Ch02_Subnormality | 4 | 4,280 | 0 |
| Ch03_SplitExtensions | 8 | 5,976 | 0 |
| Ch04_Commutators | 11 | 10,965 | 0 |
| Ch05_Transfer | 7 | 3,945 | 0 |
| Ch06_FrobeniusActions | 10 | 9,232 | 0 |
| Ch07_ThompsonSubgroup | 13 | 11,835 | 0 |
| Ch08_PermutationGroups | 14 | 5,707 | 0 |
| Ch09_MoreSubnormality | 18 | 6,873 | 0 |
| Ch10_MoreTransfer | 6 | 3,643 | 0 |
| Appendix | 2 | 480 | 0 |

⚠ Ch.7 は教科書側が **8 件 (7.1–7.8) しか無い**ので、repo 13 leaf / 11.8k 行は
番号付き結果でなく ZJ / p-stability の支持補題群。「Ch.7 の被覆が薄い」は誤読。

## 「repo に cite が無い」42 件の分類 (全件)

### (A) mathlib 被覆 — 37 件 (ラッパー方針により意図的に repo 実装なし)

**Ch.1 (10 件)** — repo は `Ch01_Sylow/Basic.lean` の docstring で各々の mathlib 名を記録済:
1.4 `MulAction.orbitEquivQuotientStabilizer` + `MulAction.index_stabilizer` /
1.6 `Subgroup.conjAct_pointwise_smul_iff` + `index_stabilizer` (2 行合成) /
1.8 `Nat.Choose.choose_pow_mul_pow_mul_modEq_choose_nat` /
1.12 (Sylow C) `Sylow.isPretransitive_of_finite` + `MulAction.exists_smul_eq` /
1.13 (Frattini) `Sylow.normalizer_sup_eq_top` (Sylow.lean:500) /
1.14 (Sylow D) `IsPGroup.exists_le_sylow` /
1.15 `Sylow.card_eq_index_normalizer` /
1.18 `IsPGroup.inf_normalizer_sylow` /
1.21 `ascending_central_series_le_upper` /
1.25 `Sylow.exists_subgroup_card_pow_prime`

**Ch.3–5 (10 件)**:
3.7 `Subgroup.leftTransversals.diff_mul_diff` ほか / 3.8 `Subgroup.exists_right_complement'_of_coprime` /
3.9 **`isSolvable_def`** / 3.10 `Solvable.lean` の subgroup/quotient/extension 各補題 /
4.9 (三部分群補題) `Subgroup.commutator_commutator_eq_bot_of_rotate` /
5.1 `MonoidHom.transfer_def` / 5.2 `MonoidHom.transfer` (型で従う) /
5.14 `IsCyclic.isComplement'` / 5.15 `IsZGroup → IsSolvable` instance / 5.16 `IsZGroup.isCyclic_commutator` ほか

**Ch.8 (17 件)** — 全て mathlib の primitivity/blocks/Jordan/Iwasawa/`A_n` 群:
8.2 `SubMulAction.ofStabilizer.isMultiplyPretransitive` / 8.3 `Projectivization.specialLinearGroup_is_two_pretransitive` /
8.11 `MulAction.IsBlock.ncard_dvd_card` ほか / 8.12 `IsPreprimitive.of_prime_card` /
8.13 `MulAction.block_stabilizerOrderIso` / 8.14 `isCoatom_stabilizer_iff_preprimitive` /
8.15 `IsBlock.orbit_of_normal` / 8.17 (Jordan) `Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem` /
8.18 (Jordan) `IsPreprimitive.isMultiplyPreprimitive` / 8.19 `alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem` /
8.20 `IsPreprimitive.of_card_lt` / 8.21 `SubMulAction.…ofFixingSubgroup_inter` /
8.22 `IsPreprimitive.is_two_pretransitive` / 8.27 `alternatingGroup.isSimpleGroup` (Alternating/Simple.lean:201) /
8.28 `Equiv.Perm.alternatingGroup_le_of_normal` + `alternatingGroup.index_eq_two` /
8.29 `Projectivization.SL_mulAction_ker` ほか / 8.30 (Iwasawa) `MulAction.IwasawaStructure`

repo 側の方針明記: `Ch08_PermutationGroups/RegularNormal.lean:38-42`。

### (B) repo に記述的名前で在り — 5 件 (cite 表記が無いだけ)

| 結果 | repo |
|---|---|
| 4.37 (Baer trick) | `Ch04_Commutators/Main/BaerTrick.lean:73` `baerAdd` ほか |
| 5.23 (abelian Sylow ⇒ N_G(P) が p-transfer を制御) | `Ch05_Transfer/Basic.lean:1366` `APrime_normalizer_eq_subgroupOf_APrime_of_isMulCommutative_sylow` |
| 6.18 (奇位数 Frobenius 補群) | `Ch06_FrobeniusActions/OddComplement.lean:132` `isZGroup_of_isFrobeniusAction_of_odd` (= 6.17) + 3 箇所で inline 導出 |
| 10.8 (transfer の推移性) | `GroupTheory/TransferTransitivity.lean:366` `transfer_transfer` |
| 10.17 (coprime 作用の不変補群) | `BG/Ch1_Preliminary/OperatorMaschke.lean:287` `exists_aInvariant_complement_of_isElementaryAbelian` |

### (C) 未形式化 — **0 件**

## 実測で見つかった軽微な債務 (被覆とは別軸)

1. **✅ 修正済 (本 note と同 commit)**: `Ch03_SplitExtensions/Basic.lean:449` が Thm 3.9 の mathlib 名として
   `isSolvable_iff_derivedSeries_eq_bot` を挙げていたが、**この名前は mathlib に存在しない**
   (群版は `isSolvable_def`; `derivedSeries_eq_bot_iff` は Lie 代数版)。→ `isSolvable_def` に訂正。
2. **6.18 に単一の citable 宣言が無い** — repo は 6.17 を名前付きで証明し、6.18 の 3 つの帰結は
   mathlib `IsZGroup` API から 3 箇所で inline に再導出している。下流が「6.18」を cite したいなら
   合成を 1 本の定理として名付ける価値がある (低優先)。
3. **mathlib 版が Isaacs と逐語一致しない 4 件** (いずれも下流で困らないことを確認済):
   - 8.21: mathlib は Jordan 集合 2 つでなく「集合とその平行移動 `s ∩ g • s`」版のみ。Isaacs が
     8.22/8.18 の証明で使うのはこの場合だけなので実害なし。
   - 8.28: mathlib は主要半分 (非自明正規部分群 ⇒ `A_n ≤ N`) を述べ、`{1, A_n, S_n}` の逐語形は
     `alternatingGroup.index_eq_two` 等との組合せ。
   - 8.29: PSL の 2-推移性 instance は mathlib に無い (SL 版から `rfl` で定義されるため)。
     忠実性と次数 `(q^n−1)/(q−1)` は在る。
   - 8.30: mathlib の `IwasawaStructure` は「点添字の**可換**部分群族 + `iSup = ⊤`」で、
     Isaacs の「単一の**可解** `A ⊴ H` + `A^G = G`」と包装が違う (現代的標準形)。
     repo は `Ch08_PermutationGroups/PSLSimple.lean:355` で既に消費済。

## 次に何をやるか

被覆は完了しているので、Isaacs 側で「未形式化を埋める」作業は**無い**。残る軸は:

- **特殊化債務** (`formalized_specialized`) — repo の仮説が教科書より狭い箇所。
  これは番号被覆では検出できないので、章ごとに statement を突き合わせる別 pass が要る。
  Pf 本文では frontier note の表がこれを担っている。Isaacs 側は**未整備**。
- 上記「軽微な債務」2 (6.18 の命名)。

⚠ 本 note は**被覆 (番号) の実測**であって、statement の忠実性 (特殊化債務) の実測ではない。
両者を混同しない。
