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
2. **✅ 解消済 (2026-07-19)**: 6.18 に単一の citable 宣言が無かった件 →
   `isCyclic_commutator_abelianization_coprime_of_isFrobeniusAction_of_odd`
   (`Ch06_FrobeniusActions/OddComplement.lean`, Step 1 の直後) として書籍どおりの合成
   (`A'` と `A/A'` が巡回・位数互いに素) を命名。証明は書籍と同じ 2 行 — Cor 6.17
   (`isZGroup_of_isFrobeniusAction_of_odd`) で Z-群、あとは Thm 5.16 = mathlib の
   `IsZGroup.isCyclic_commutator` / `isCyclic_abelianization` / `coprime_commutator_index`。
   axiom-clean・AxiomsCheck 登録済。
3. **✅ 解消済 (2026-07-19)**: `Ch05_Transfer/Basic.lean` の Cor 5.19 docstring が
   「原版への一般化は…extensible」と**未実装であるかのように**書いていたが、一般形は
   `not_isSimpleGroup_of_sylow_two_cyclic_strict_max_factor`
   (`Ch05_Transfer/SylowTwoDirectFactor.lean:73`) として**実装済**だった。相互参照を張って訂正。
4. **mathlib 版が Isaacs と逐語一致しない 4 件** (いずれも下流で困らないことを確認済):
   - 8.21: mathlib は Jordan 集合 2 つでなく「集合とその平行移動 `s ∩ g • s`」版のみ。Isaacs が
     8.22/8.18 の証明で使うのはこの場合だけなので実害なし。
   - 8.28: mathlib は主要半分 (非自明正規部分群 ⇒ `A_n ≤ N`) を述べ、`{1, A_n, S_n}` の逐語形は
     `alternatingGroup.index_eq_two` 等との組合せ。
   - 8.29: PSL の 2-推移性 instance は mathlib に無い (SL 版から `rfl` で定義されるため)。
     忠実性と次数 `(q^n−1)/(q−1)` は在る。
   - 8.30: mathlib の `IwasawaStructure` は「点添字の**可換**部分群族 + `iSup = ⊤`」で、
     Isaacs の「単一の**可解** `A ⊴ H` + `A^G = G`」と包装が違う (現代的標準形)。
     repo は `Ch08_PermutationGroups/PSLSimple.lean:355` で既に消費済。

## 特殊化債務 pass — Ch.1–Ch.4 実測 (2026-07-19)

被覆と違い、こちらは **repo の仮説が教科書より狭い**箇所を statement 単位で照合したもの。
判定除外: `[Finite G]` (書籍が「finite group」と言っている場合)、`[Fact p.Prime]` 等の
Lean 技術的 instance、repo の方が一般な場合、他ファイルに一般形が別途ある内部特殊化。

### ✅ 解消済

| 番号 | 内容 | 対応 |
|---|---|---|
| **1.31** | repo が `hpq : p ≠ q` を追加仮定。書籍 statement は「Let `\|G\| = p²q`, where `p` and `q` are primes」だけで相異性を課さない (証明中で `n_p > 1 ∧ n_q > 1` と仮定した局面で初めて注意する) | `hpq` を削除し `p = q` 分岐を追加。`\|G\| = p³` ゆえ `G` は `p`-群で Sylow `p` は極大性から `⊤`、よって正規。唯一の repo 内 caller (Thm 1.33 経路) も引数削除で追随 |
| **1.32** | 同上 (`\|G\| = p³q`) | 同上 (`p = q` なら `\|G\| = p⁴`; 例外 `\|G\| = 24` にも当たらない) |
| **3.35** | `cyclic_quotient_lift` だけが `[Finite G]` を担いでいた。書籍 3.35 は `G` 任意で商のみ巡回を要求。同 cluster の `cyclic_quotient_extension_unique` / `_iso_exists` は `G` 任意 | `[Finite G]` を削除 (証明本体で未使用だった) |
| **1.36** | `hpq : p ≠ q` 追加。書籍は「`\|G\| = p^a q`, where `p` and `q` are primes and `a > 0`」のみで、証明が "We can certainly assume that `p ≠ q`" と**導出**する | 強形 `exists_normal_ne_bot_ne_top_of_card_eq_pow_mul_prime` と弱形 `not_isSimpleGroup_of_card_eq_pow_mul_prime` の両方から削除。`p = q` なら `\|G\| = p^(a+1)` (指数 ≥ 2) の `p`-群 → 中心で分岐: 中心 = ⊤ なら可換ゆえ位数 `p` の部分群が正規・真・非自明 (`Subgroup.center_le_normalizer` + `normalizer_eq_top_iff`)、中心 ≠ ⊤ なら中心自身が該当 (`IsPGroup.center_nontrivial`) |
| **1.38** | `hmin` が「位数**最小**」を要求。書籍は「包含**極小**」で、**Isaacs 自身が p.61 (Thm 2.18 の注) で両者を区別**し「minimal order ⇒ minimal だが逆は成り立たない」と明記。⟹ 包含極小だが位数最小でない対を渡せなかった | 仮説を `∀ S' T', ↑S' ⊓ ↑T' ≤ ↑S ⊓ ↑T → ↑S' ⊓ ↑T' = ↑S ⊓ ↑T` に置換。`hmin` は Step 8 の 1 箇所でしか使われず `Subgroup.eq_of_le_of_card_ge` で等号を出していただけなので**直接適用**になり、証明は 3 行短くなった。唯一の caller (Thm 1.37) は位数最小の対を作るので、そこで弱形へ落として渡す |

### ✅ 解消済 (続き) — 3.29 / 3.30

| 番号 | 内容 | 対応 |
|---|---|---|
| **3.29** | `IsSolvable A ∨ IsSolvable G` を引きずっていた。**書籍 3.29 は 3.23/3.25/3.26/3.27/3.28 と違ってこの仮説を置かない** — 証明が「it is no loss to assume that `A = ⟨a⟩`. Since `A` is cyclic, it is certainly solvable, and thus Corollary 3.28 applies」と巡回還元で外すため | 現行証明を `aFixed_quotient_frattini_of_solvable` に改名し、その上に書籍どおりの `aFixed_quotient_frattini` を新設。`a : A` を固定して `φ` を `⟨a⟩` に制限 — `⟨a⟩` は巡回ゆえ可解、位数は `\|A\|` を割るので互いに素性も保存 (`Nat.Coprime.coprime_dvd_left`) |
| **3.30** | 同上 (3.29 の 1 行系) | 3.29 の一般形をそのまま使うだけで解消 |

⚠ **下流 1 箇所を追随修正**: `BG/Ch1_Preliminary/S01_Solvable.lean` の `burnside_operator` が
`R` p-群 ⇒ nilpotent ⇒ solvable を経由して `Or.inr` を渡していたが、その経由ごと不要になった
(BG はレーン c 所管だが、上流の一般化に伴う 1 行の call-site 追随ゆえ本 commit に含める)。

## 特殊化債務 pass — Ch.5–Ch.10 + Appendix 実測 (2026-07-19)

**Ch.6 / Ch.8 / Ch.9 / Ch.10 / Appendix は債務なし**と判定 (照合済)。検出は Ch.5 と Ch.7 のみ 4 件。

### ✅ 解消済

| 番号 | 内容 | 対応 |
|---|---|---|
| **7.7** | `hP_neBot : P ≠ ⊥` 追加。書籍は「If `P` is a `p`-subgroup of `G`」のみ | 計 **6 宣言**から削除 (Ch02 の `normalizer_map_of_coprime_kernel` + Ch07 の 4 宣言 + 外部 caller 2 箇所)。仮説は死んでいた (Ch02 側が既に `_hP_neBot` と未使用束縛)。⚠ **同ファイルの別補題 `map_ne_bot_of_coprime_kernel` (Ch02_Subnormality/Main.lean:455) は本当に使う** (:474 で `apply hP_neBot`) ので手を付けていない |
| **7.5** | 条件 (5) `\|V : C_V(P)\| ≤ p` を**全ての** Sylow `p` 部分群に量化。書籍は結論に現れる単一の `P` のみ (⟨P,Q⟩ 降下の帰納法の都合で ∀ 形が必要になり、Isaacs は証明中で Sylow 共役性から補っている) | `sylow_normal_of_elementary_normal_P_theorem_single` を新設 (書籍どおり単一 `P`)。任意の `P'` は `P` の共役 (`MulAction.exists_smul_eq` + `Sylow.coe_subgroup_smul`) で、共役部分群の action-centralizer は index が等しい (`actionCentralizer_map_conj_index`) ので ∀ 形へ補完できる。両形は同値 |
| **5.22** | **結論の欠落** (仮説の狭さでない): 書籍の第 2 結論 `G/A^p(G) ≅ H/A^p(H)` (= 「H が p-transfer を制御する」本体) が無かった | `quotient_aPrime_mulEquiv_of_controlsFusionIn` (Ch05_Transfer/Basic.lean、第 1 結論の直後) を新設。`H ⊔ A^p(G) = ⊤` (Sylow index と `p`-冪 index の互いに素性 + `P ≤ H`) を出し、第 2 同型定理 `QuotientGroup.quotientInfEquivProdNormalQuotient` + `QuotientGroup.congr` 2 回で `↥H ⧸ A^p(H) ≃* G ⧸ A^p(G)`。⚠ `rw` で部分群を書き換えると商の `Normal` instance 依存で motive が壊れるので、**全て `QuotientGroup.congr` による transport で組んだ** |
| **7.8** (Burnside `p^a q^b`) | `hpq : p ≠ q` 追加。書籍は「Let `G` be a finite group of order `p^a q^b`, where `p` and `q` are primes」だけで相異性を課さない | 削除し `p = q` 分岐を追加 (`\|G\| = p^(a+b)` の `p`-群 ⇒ 冪零 ⇒ 可解)。**下流の実害も解消**: `Ch07/ForwardFromCh03.lean` は素因子が 1 個のとき `hpq` を満たすためだけに**偽の第 2 素数** (`if p = 2 then 3 else 2`) を捏造していた |

### ⬜ 未解消 — **なし**

**Ch.1–Ch.10 + Appendix の特殊化債務は全て解消済 (検出 11 件 → 実装 11 件)。**

<!-- 旧・未解消表 (全件解消済につき空)
| 番号 | Lean | 狭さ | 一般化方針 |
|---|---|---|---|

-->

### 債務なしと判定した章 (Ch.5–10)

- **Ch.6**: 24 件すべて書籍強度。6.22 は素数位数 + `[IsSolvable N]` だが、**同ファイルに一般形**
  `isNilpotent_of_isFrobeniusAction` (KernelNilpotent.lean:365 = 6.24、可解性不要) が在るので債務でない。
- **Ch.8**: 全件書籍以上。8.4/8.7 は任意の可除環へ、8.31/8.32/8.33 は無限体も被覆、
  8.37 は任意の非対角 orbital (書籍は極小のもの)、8.43 は書籍の「成分ちょうど 3 個」仮定を落とす、
  など **repo の方が一般**な箇所が多数。
- **Ch.9 / Ch.10 / Appendix**: 全件一致または repo の方が一般 (10.6/10.11/9.30/9.29/10.14/9.5/X.22)。
  内部特殊化はすべて一般形の兄弟が在る (9.13/9.21/9.26/9.27 の subnormal 版、10.18 の一般 Thm 10.25 =
  `OddOrder.Algebra.transfer_pow_relindex_eq_one`)。

⚠ 境界例として記録のみ (債務でない): 9.10 は結論が「\|G_i\| ≤ n」で書籍の「同型類は有限個」より弱いが
**Isaacs 自身の証明目標がその形** (p.278); 9.28 は `subnormalClosure` 定義が無いだけで内容は完備;
5.11 / 5.26 は第 2 同型定理の言い換え / TFAE の分割で内容は同じ。

<!-- 旧・未解消表 (全件解消済につき空)
| 番号 | Lean | 狭さ | 一般化方針 |
|---|---|---|---|
| **3.29** | `aFixed_quotient_frattini` (Ch04_Commutators/ForwardFromCh03.lean:841) | `IsSolvable A ∨ IsSolvable G` 追加。**書籍 3.29 は意図的にこれを落としている** — 3.23/3.25/3.26/3.27/3.28 は「at least one of A or G is solvable」を担ぐが、3.29 の証明は "it is no loss to assume that `A = ⟨a⟩`. Since `A` is cyclic, it is certainly solvable, and thus Corollary 3.28 applies" と巡回還元で解消する | `a : A` を固定し `(Subgroup.zpowers a).subtype` に沿って `φ` を制限。`⟨a⟩` は巡回ゆえ可解、位数は `\|A\|` を割るので互いに素性も保たれ、現行補題を `Or.inl` で適用。**repo に同じ trick の実例あり**: `iterCommutator_inl_inr_two_eq_one_of_coprime` (Lem 4.29 一般形, ThreeSubgroupsCoprime.lean:509) が `SemidirectProduct.map` 転送込みで同型の還元をやっている |
| **3.30** | `aFaithful_quotient_frattini` (同 :874) | 同上 (3.29 の 1 行系なので同じ余分仮説) | 3.29 の一般化から自動的に従う |

-->

### 債務なしと判定した章

- **Ch.2 (Subnormality)**: 全 cite が書籍と仮説一致。特に 2.18 Zenkov は**包含極小**を正しく使う
  (1.38 と対照的)。2.3/2.7/2.10/2.14 は書籍どおり**任意群**で述べられており `[Finite G]` を付けていない。
- **Ch.4 (Commutators)**: 4.10–4.13 / 4.20–4.23 / 4.25 は書籍どおり任意群、4.14–4.19 (Mann) /
  4.24 / 4.26–4.36 / 4.38 も仮説一致。`ForwardFromCh03.lean` / `HartleyTurull.lean` の
  3.23–3.28 / 3.31–3.34 は書籍が「at least one of A or G is solvable」と言う箇所に**正しく**
  その仮説を置いている (3.29/3.30 だけが書籍側で落ちているのに repo が引きずっている)。

### 報告対象外とした境界例 (記録のみ)

- `isaacs_thm_4_31_external` (BaerTrick.lean:1107): Thompson の P×Q 補題を**外部**直積
  `P × Q →* MulAut G` で述べる (書籍は内部直積)。仮説の狭さでなくモデル化の流儀で、
  内部分解は `MulEquiv` で転送できるので債務ではない。
- 1.24 (Basic.lean:567): mathlib の弱形に委譲しており書籍の `L ⊴ P` を落とすが、
  書籍強度の形は `BG/Ch1_Preliminary/S01_Solvable.lean:1394`
  (`normal_subgroup_card_pow_le_of_pGroup`) に既に在る。**cross-reference が stale なだけ**。
- 1.37/1.39/1.40: repo は `hAbel` を全 Sylow `p` 部分群に量化、書籍は「a Sylow p-subgroup … is
  abelian」。Sylow 共役性で同値 (docstring もそう書いている)。

## 次に何をやるか — **レーン a の Isaacs 側は完済**

2 軸とも実測完了:

| 軸 | 状態 |
|---|---|
| 実 sorry | **0** |
| 番号被覆 (Ch.1–10) | **未形式化 0 件** (mathlib 被覆 37 / repo 5 / 欠落 0) |
| 特殊化債務 (Ch.1–10 + App) | **検出 11 件 → 実装 11 件** |

⟹ Isaacs 側に「次に埋めるもの」は無い。Pf 本文も同様に完済で、残りは全て
**hub issue 9163** (typePA / A(M) 設計裁定) に gated。次の割当は hub issue で照会済
(下記「参照」)。

将来 Isaacs 側で作業が発生しうる箇所 (現時点では債務でない):
- 書籍が文献引用のみで証明を置かない結果 / 演習問題 (Problems) — 本 note の被覆測定は
  **番号付き結果のみ**を対象にしており、演習は含まない。
- mathlib 側の API 変更で cross-reference が stale 化したとき (本 note の測り方 §3 の手順で再測)。
