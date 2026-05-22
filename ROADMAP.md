# Odd Order Theorem 形式化ロードマップ

## ゴール

有限群論の **Feit-Thompson 定理**「位数が奇数の有限群はすべて可解である」の **Lean 4 による完全形式化**。AI エージェント駆動の長期プロジェクト。

## スコープ: 3 冊を全部形式化する

| 略称 | 書名 | 役割 |
|------|------|------|
| **Isaacs** | I. M. Isaacs, *Finite Group Theory* (AMS GSM 92, 2008) | 有限群論の前提一式 (Fitting, Hall, Frobenius, ZJ, transfer, 一般化 Fitting `F*`) |
| **BG** | H. Bender & G. Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994) | Feit-Thompson 1963 原論文 Ch.IV (局所解析) + Ch.VI (最終矛盾; App.C は Peterfalvi 1984 paper の改訂版) |
| **Peterfalvi** | T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000) | Feit-Thompson 1963 原論文 Ch.V (指標理論) |

## 方針

- **すべてローカルに書く** (mathlib への PR は将来課題、当面はこのリポジトリ内)
- **mathlib 互換を可能な限り維持** (将来の upstream を見据えて命名・スタイル・namespace を mathlib に寄せる)
- **blueprint は使わない** (教科書 PDF → Lean 直接)
- **教科書として Isaacs を採用 (Gorenstein 1968 は使わない)** — BG が "**G**" として引く Gorenstein _Finite Groups_ (1968) は古典で、BG/Peterfalvi の前提知識を提供する標準文献だが、本プロジェクトでは現代記法で同等内容を扱う **Isaacs FGT を一次参照に採用**するという明示的な選択。BG 中の "G, Thm X.Y.Z" 引用は Isaacs の対応定理に読み替えて Phase 1 で形式化する
- mathlib 既存資産 (Sylow, p-群, 可解, 冪零, Frattini, Transfer, Focal subgroup, Schur-Zassenhaus, 基本表現論/指標, Maschke, 既約表現, 直交関係, 誘導表現) は再利用
- 命名: `OddOrder.Isaacs.Subgroup.fitting` のように、将来 `Subgroup.fitting` へリネームしやすい形を取る

## フェーズ

| Phase | 内容 | 状態 |
|---|---|---|
| 0 | Lean プロジェクト初期化 (Lean 4.29.1 + mathlib v4.29.1) | ✅ 2026-05-21 |
| 1 | **Isaacs** Ch.1–10 + Appendix の Lean 化 | ⏳ |
| 2a | **BG** Ch.I–IV + 補助 Appendices の Lean 化 | ⏳ |
| 2b | **Peterfalvi** 主章 + 補章 の Lean 化 | ⏳ |
| 3 | 最終矛盾の結合 (BG App.C ≅ Peterfalvi の対応物) | ⏳ |
| 4 | `FeitThompson` メイン定理ステートメント & 完全結合 | ⏳ |

Phase 2a と 2b は Phase 1 が概ね終わった後、独立に並行進行可。

## 依存グラフ

```
                  mathlib
                     │
                     ↓
            [Phase 1] Isaacs
   (Fitting, Hall, Frobenius, ZJ, F*)
                     │
         ┌───────────┴───────────┐
         ↓                       ↓
   [Phase 2a] BG          [Phase 2b] Peterfalvi
   (局所解析)             (指標理論)
         └───────────┬───────────┘
                     ↓
             [Phase 3] 最終矛盾
                     ↓
             [Phase 4] FeitThompson
```

## Lean モジュール構成 (提案)

```
OddOrder.lean                            # entry module — 章ファイルを順次 import
OddOrder/
├── Isaacs/                              # Phase 1
│   ├── Ch01_Sylow.lean
│   ├── Ch02_Subnormality.lean
│   ├── Ch03_SplitExtensions.lean        # Hall, Schur-Zassenhaus
│   ├── Ch04_Commutators.lean
│   ├── Ch05_Transfer.lean
│   ├── Ch06_FrobeniusActions.lean
│   ├── Ch07_ThompsonSubgroup.lean       # J(P), ZJ
│   ├── Ch08_PermutationGroups.lean
│   ├── Ch09_MoreSubnormality.lean       # F*(G)
│   ├── Ch10_MoreTransfer.lean
│   └── AppA_Basics.lean
├── BG/                                  # Phase 2a
│   ├── Ch1_Preliminary/
│   │   ├── S01_Solvable.lean
│   │   ├── S02_Representations.lean
│   │   ├── S03_FrobeniusActions.lean
│   │   ├── S04_PGroupsSmallRank.lean
│   │   ├── S05_NarrowPGroups.lean
│   │   └── S06_Additional.lean
│   ├── Ch2_Uniqueness/
│   │   ├── S07_Transitivity.lean
│   │   ├── S08_FittingOfMaximal.lean
│   │   └── S09_Uniqueness.lean
│   ├── Ch3_MaximalSubgroups/
│   │   ├── S10_MalphaMsigma.lean
│   │   ├── S11_ExceptionalMaximal.lean
│   │   ├── S12_E.lean
│   │   └── S13_PrimeAction.lean
│   ├── Ch4_FamilyOfMaximal/
│   │   ├── S14_TypePCounting.lean
│   │   ├── S15_MF.lean
│   │   └── S16_MainResults.lean
│   ├── AppA_Prerequisites.lean
│   ├── AppB_Puig.lean
│   ├── AppC_FinalContradiction.lean     # Peterfalvi (1984 paper) 改訂版
│   ├── AppD_CNGroups.lean
│   └── AppE_FeitThompson.lean
├── Peterfalvi/                          # Phase 2b
│   ├── S01_Introduction.lean
│   ├── S02_Notation.lean
│   ├── S03_PreliminaryCharacter.lean
│   ├── S04_DadeIsometry.lean
│   ├── S05_TICyclic.lean
│   ├── S06_DadeIsometryCertain.lean
│   ├── S07_Coherence.lean
│   ├── S08_CoherenceTheorems.lean
│   ├── S09_NonExistenceCertainGroup.lean
│   ├── S10_MinimalSimpleStructure.lean
│   ├── S11_MaximalII_III_IV.lean
│   ├── S12_MaximalIII_IV_V.lean
│   ├── S13_MaximalIII_IV.lean
│   ├── S14_MaximalI.lean
│   ├── S15_SAndT.lean
│   ├── S16_NonExistenceG.lean
│   └── Appendices/
│       ├── Suzuki.lean
│       ├── Huppert.lean
│       ├── NearFields.lean
│       ├── Suzuki2Groups.lean
│       └── FeitSibley.lean
├── FeitThompson.lean                    # Phase 4: メイン定理
└── Basic.lean                           # 一時ダミー (削除予定)
```

Namespace 階層: `OddOrder.Isaacs.Ch01`, `OddOrder.BG.Ch1.S03`, `OddOrder.Peterfalvi.S04` 等。

## ファイル粒度とトレーサビリティ

各 Lean ファイルは「文献のどこの形式化か」を一目で追える状態を保つ。

### 初期粒度

| 本 | 1 ファイル単位 | 理由 |
|---|---|---|
| Isaacs | 1 章 | 章は 20-48 ページ、Lean 500-2000 行に収まる見込み |
| BG | 1 節 (§) | 節が 3-16 ページと小さく、節境界が明確 |
| Peterfalvi | 1 節 (§) | 同上 (1-12 ページ) |

### 育ってから分割

1 ファイルが概ね **1500-2000 行** を超えた段階で、subsection 単位でディレクトリに昇格:

```
OddOrder/Isaacs/Ch01_Sylow.lean
        ↓
OddOrder/Isaacs/Ch01_Sylow/
                ├── A_Existence.lean
                ├── B_Normalizer.lean
                └── ...
```

先回りで全部 subsection 分割するのは避ける (本によって subsection 区切りが緩いところがあり、無駄な分割になりやすい)。

### トレーサビリティ慣習 (3 層)

```lean
/-!
# OddOrder.Isaacs.Ch01 — Sylow Theory

Isaacs, *Finite Group Theory*, Chapter 1 (pp. 1-44) の Lean 化。
-/
namespace OddOrder.Isaacs.Ch01

section /- 1A: Sylow's Theorems (pp. 1-10) -/

/-- **Isaacs Thm 1.4** (Sylow's existence). 任意の素数 `p` について ... -/
theorem sylowExistence ... := ...

/-- **Isaacs Thm 1.7** (Sylow's conjugacy). ... -/
theorem sylowConjugacy ... := ...

end -- 1A

section /- 1B: Counting and the index theorem (pp. 11-20) -/
...
end -- 1B
```

- **ファイル冒頭の `/-! ... -/`**: 本のどの章節か、ページ範囲、簡単な内容
- **`section /- ラベル (ページ範囲) -/ ... end`**: 本の subsection 構造をミラー (VSCode で折り畳み可、grep で位置特定可)
- **theorem の docstring 冒頭の `**Book名 Thm N.M**`**: 本での番号 + 慣用名

定理名 (`theorem` の Lean 識別子) には番号 (`thm_1_4` 等) を入れない — mathlib 互換のため命名は記述的 (`sylowExistence`, `sylowConjugacy`) に保つ。本での番号は docstring 内に。

## 進捗ログ

- **2026-05-21** Phase 0 完了 (Lean プロジェクト初期化、mathlib カバレッジ調査、3 冊スコープ確定、本ロードマップ作成)
- **2026-05-21** Phase 1 章間依存を Isaacs mmd から集計、下記の依存図を追加
- **2026-05-22** Phase 2 全体構造の調査ノート完了: [`notes/bg/_overview.md`](notes/bg/_overview.md) (BG 138 結果集計 + FT 経路 + Phase 2a 着手順), [`notes/peterfalvi/_overview.md`](notes/peterfalvi/_overview.md) (Peterfalvi 140 結果集計 + FT 経路 + Phase 2b 着手順), [`notes/meta/phase2_cross_refs.md`](notes/meta/phase2_cross_refs.md) (3 冊間クロス参照マップ + Phase 1 Isaacs ↔ Phase 2 対応表)
- **2026-05-22** Phase 2 per-section ノート 全節完了: BG 全 16 §1-§16 + App.A-E (22 ファイル), Peterfalvi 全 16 §1-§16 (§1+§2 統合) + App.A Suzuki + App.B-E 統合 (18 ファイル). 各節について TL;DR / 結果表 / Isaacs/BG 対応 / mathlib カバレッジ / Phase 2 形式化着手順 / 未解決 TODO を整理. 合計約 16200 行の調査ドキュメント
- **2026-05-22** Isaacs §2A Thm 2.2 完成 (`le_fitting_iff_isNilpotent_and_isSubnormal` + Ch.1 `opCore.characteristic`/`fitting.characteristic` instance 追加 + `|G|`-induction 補助 `le_fitting_aux`)
- **2026-05-22** Isaacs §2A Thm 2.8 完成 (`isSubnormal_of_permutable_with_conjugates`: permutability ⇒ subnormality, |G|-induction + Zipper Lemma + normal closure + `Subgroup.conj_smul_subgroupOf` 経由の H への permutability transfer)
- **2026-05-22** Isaacs §2A Thm 2.11 (Wielandt abelian-in-F(G)): sorry stub. §2B Thm 2.12 Baer 順方向 (`baer_sup_conj_isNilpotent_of_le_fitting`) 完成, 逆方向は 2.11 依存で stub
- **2026-05-22** Isaacs Ch.3 構造完成: §3A 3.3/3.4 stub, §3B mathlib 対応表 + `IsElementaryAbelian` 定義 + Thm 3.11 stub, §3C `IsHallSubgroup` 定義 + Lemma 3.16 完成 + `IsHallSubgroup.coprime_index` 完成 + Thm 3.13-3.17 stubs, §3D `IsPiSeparable` 定義 + Thm 3.18-3.22 stubs, §3E/§3F docstrings
- **2026-05-22** Isaacs §2B 完成: Thm 2.12 Baer (順方向 + 逆方向 + iff) — Zipper Lemma + Thm 2.2 経由の `|G|`-induction で逆方向を構成. Lemma 2.14 essence (`inv_by_two_involutions`) + structural (`mem_zpowers_or_mul_t_mem`) — closure induction で 4 mul cases + 2 inv cases. Thm 2.13 Matsuyama (`t ∉ O_2(G)` ⇒ 奇素数位数 inversion `x^t = x⁻¹`) — Baer iff + Cauchy + Lemma 2.14. Helpers: `mem_opCore_of_le_fitting_of_isPGroup` (Sylow `p` of F(G) = O_p(G)), `exists_odd_prime_dvd_of_not_pow_two` (Nat 強 induction)
- **2026-05-22** Isaacs §2D axiom 化: Thm 2.18 Zenkov (`zenkov_minimal_le_fitting`), Cor 2.19 (`inf_fitting_ne_bot_of_abelian_card_ge_index`), Thm 2.20 Lucchini (`lucchini_index_normalCore_lt_index`) を statement のみ axiom 化. 各 docstring に Isaacs p.61-63 の完全証明戦略 (|G|-induction + Baer + 計算) を記載. Lucchini が Ch.3 Horosevskii の必須前提
- **2026-05-22** Isaacs Ch.3 §3A Thm 3.3 Horosevskii 完成: `horosevskii_aut_order_lt` (`orderOf σ < Nat.card G`). Lucchini axiom + 半直積 `G ⋊[A.subtype] A` + `inl_range_isComplement_inr_range` (Thm 3.2) + Lemma 2.7 + `inl_aut` + `MonoidHom.map_zpowers` で完全証明 (~120 行)
- **2026-05-22** Isaacs Ch.4-7 dependency 再 audit 完了: [`notes/meta/ch04_07_audit_2026_05_22.md`](notes/meta/ch04_07_audit_2026_05_22.md) — 4 章 (Commutators / Transfer / Frobenius / Thompson) を 4 視点 (forward dep / 章内依存 / mathlib status 含む証明内 API / 先行章依存) で並列再調査. 主結果: (i) Ch.6 ↔ Ch.7 双方向依存は 6.23 一本のみ (axiom 化 clean), (ii) `IsElementaryAbelian` / `Subgroup.thompsonJ` / `IsPStable` を `OddOrder/GroupTheory/` 配下 shared module 化推奨 (BG App.A が再利用), (iii) Cor 3.28 が Ch.4 §4C-§4D 多数定理 (4.26, 4.28-30, 4.34-36, 4.38) の transitive 前提, (iv) Ch.6 6.11 は 6.12 の corollary (実装順序訂正), (v) Ch.5 大部分は Ch.4 完成を待たず実装可 (Ch.4 dep は 5.17 と 5.30 のみ), (vi) Ch.6 本文は Hall-Higman 3.21 不使用. 既存 ch04/ch06 ノートの事実誤認 4 件訂正済
- **2026-05-23** Isaacs Ch.1 (Sylow Theory) §1G Chermak-Delgado 省略判断 re-audit: [`notes/meta/ch01_audit_2026_05_23.md`](notes/meta/ch01_audit_2026_05_23.md) — fresh grep で BG/Peterfalvi/Ch.2-10 下流引用 0 件再確認, **§1G 省略を維持**. ただし tactical refinement: §1G 実装が要求する 2 helper (H1 `card_HK·card_inf=card_H·card_K`, H2 `le_centralizer_centralizer`) は mathlib v4.29.1 不在で独立に upstream 価値高 ⇒ Ch.2+ で必要時 standalone 追加方針. §1G 本体は (1) `m_G(H)` 記法の下流出現, (2) H1/H2 累積実装, (3) Phase 1 完成後の upstream pivot のいずれかでトリガー. §1G stub docstring 更新済
- **2026-05-23** (同日) §1G Chermak-Delgado **実装方針に決定変更**: ユーザ判断により mathlib upstream のため Thm 1.41-1.46 を実装する. 実装計画 [`notes/meta/ch01_chermak_delgado_plan.md`](notes/meta/ch01_chermak_delgado_plan.md) — `OddOrder/Mathlib/Subgroup.lean` (H1, H2, H3, `centralizer_sup` helper) + `OddOrder/GroupTheory/ChermakDelgado.lean` (`chermakDelgadoMeasure`, `chermakDelgadoLattice`, `chermakDelgadoSubgroup` + Thm 1.41-1.46) ~200 LOC / ~2 日. 確認済新情報: Galois connection `Subgroup.le_centralizer_iff` (Centralizer.lean:54) のおかげで H2 は **2 行 proof** (`le_centralizer_iff.mpr le_rfl`); `Sublattice` 構造体 mathlib に既存 (Order/Sublattice.lean); `Subalgebra.centralizer_sup` あり / Subgroup 版なし
- **2026-05-23** Isaacs Ch.3 (Split Extensions) 4 視点 audit 完了: [`notes/meta/ch03_audit_2026_05_23.md`](notes/meta/ch03_audit_2026_05_23.md) — mmd 欠落 (MISSING_PAGE) のため PDF (pp.78-125) 直読 + 既存 `ch03_split.md` + Ch03_SplitExtensions.lean (1029 行) で §3A-§3B / §3C-§3D / §3E-§3F の 3 並列 audit. 主結果: (i) **Cor 3.28 コスト訂正 ~1-2 週 Tier 1** (旧 audit "8-12 週" 悲観すぎ): Lem 3.24 + Thm 3.27 のみ依存, **Ch.4 §4A-§4B と並列着手可**, (ii) **`Ch06_FrobeniusActions/ForwardFromCh03.lean` (3.21 Hall-Higman) 配置ミス**: Ch.6 は 3.21 を全く使わず, 下流引用は Ch.4 4.33 + Ch.7 7.5/7.6 のみ ⇒ Ch.7 dir 移動推奨 (docstring に flag 追加済), (iii) `IsElementaryAbelian` (Ch.3 L455) を Ch.6/Ch.7 着手前に `OddOrder/GroupTheory/` 配下 shared 化推奨 (subgroup-based form), (iv) Thm 3.4 は ✅ 完成済 (既存ノートの stale TODO 訂正), (v) `isSolvable_def` (auto-gen `@[mk_iff]`) が 3.9 exact match, `derivedSeries_eq_bot_iff` 等の想定名は mathlib v4.29.1 不在, (vi) §3F (3.35, 3.36) は FT 経路完全不要, 現 weak `cyclic_quotient_lift` で恒久充分, (vii) 3.31 Hartley-Turull は BG/Peterfalvi 名前引用 0 件で Phase 4 までも skip 可. 既存 ch03 ノート 4 件 + Ch.4/Ch.6 forward placeholder docstring 2 件訂正済
- **2026-05-23** Isaacs Ch.1 §1G **Chermak-Delgado 全実装完了** (Thm 1.41-1.46, 全 6 結果). 配置: [`OddOrder/Mathlib/Subgroup.lean`](OddOrder/Mathlib/Subgroup.lean) (helper: `card_HK_mul_card_inf_eq_card_mul_card`, `le_centralizer_centralizer`, `centralizer_centralizer_centralizer`, `centralizer_sup`) + [`OddOrder/GroupTheory/ChermakDelgado.lean`](OddOrder/GroupTheory/ChermakDelgado.lean) (定義 `chermakDelgadoMeasure` / `chermakDelgadoLattice` / `chermakDelgadoSubgroup` + Lemma 1.42-1.43 + Thm 1.44 (a)(b)(c) + Cor 1.45 全 4 性質 (M ∈ L, abelian, Z(G) ≤ M, characteristic) + Thm 1.41 主定理 + Cor 1.46). [`OddOrder/Isaacs/Ch01_Sylow.lean`](OddOrder/Isaacs/Ch01_Sylow.lean) §1G section は import + export 形に変更. mathlib upstream 視野の shared module 化. **Isaacs Ch.1 全 46/46 結果完成**
- **2026-05-23** (同日) **Isaacs Ch.5 Transfer ファイル作成完了**: [`OddOrder/Isaacs/Ch05_Transfer.lean`](OddOrder/Isaacs/Ch05_Transfer.lean) 新規 (~175 行). mathlib カバレッジが Ch.5 中最厚 (~40-50%) のため no-wrapper policy 適用 — section docstring 内 mapping table で Isaacs 番号 ↔ mathlib API 対応を記録. Wrapper 実装: `abelian_sylow_commutator_inf_eq_focal` (5.18 = `commutator_inf_eq_focalSubgroup` 特殊化) のみ. mathlib 直接: 5.1/5.2 (`MonoidHom.transfer`), 5.5 (`transfer_eq_prod_quotient_*`), 5.6 (`transferCenterPow`), 5.7 (`card_commutator_le_*`), 5.13 Burnside (`ker_transferSylow_isComplement'`), 5.14 (`IsCyclic.isComplement'`), 5.15-5.17 Z-group (`IsZGroup` API), 5.20-5.21 Focal Subgroup Theorem ⭐ (`commutator_inf_eq_focalSubgroup`). §5E Frobenius (5.25-5.30) は docstring 保留 (Ch.4 §4D 4.36 依存)
- **2026-05-23** (同日) **Isaacs Ch.4 §4A Commutator basics 7 結果完成 + §4B Cor 4.10 完成**: [`OddOrder/Isaacs/Ch04_Commutators/Main.lean`](OddOrder/Isaacs/Ch04_Commutators/Main.lean) (~245 行). 完成: (i) `subgroup_le_normalizer_commutator_self` (Lem 4.1 左) — H ≤ N(⁅H,K⁆), H/K 正規性仮定なし版. Identity `g·⁅a,b⁆·g⁻¹ = ⁅ga,b⁆·⁅b,g⁆` (private `conj_commutator_split`) + `Subgroup.closure_induction` で証明, (ii) `subgroup_le_normalizer_commutator_self_right` (Lem 4.1 右) — `commutator_comm` 経由, (iii) `le_normalizer_of_commutator_le` / `commutator_le_of_le_normalizer` / `commutator_le_iff_le_normalizer` (Lem 4.3 三方向) — element identity `k·x·k⁻¹ = ⁅k,x⁆·x` + normalizer 性質, (iv) `commutator_commutator_le_of_rotate` (Cor 4.10 = Three-subgroups mod N) — 商写像 G→G/N で push し mathlib `commutator_commutator_eq_bot_of_rotate` 適用. `open scoped commutatorElement` 必須 (Bracket scoped instance). §4B-§4D 残 (Lem 4.6 chapter ハブ 5 引用, Thm 4.11 lcs additivity, 4.28-4.36 FT クリティカル) は docstring scaffolding
- **2026-05-23** (同日) **Isaacs Ch.3 §3D Thm 3.21 Hall-Higman 1.2.3 statement 確定** (proof sorry): `hall_higman_1_2_3` — G π-separable + oPiCore π' = ⊥ ⇒ centralizer(oPiCore π) ≤ oPiCore π. 5 段階証明戦略 (B = C ⊓ O_π(G) 設定 → B π-group + C 正規 → C/B 非自明 characteristic K/B が π or π'-group → 各 case で矛盾) を docstring 詳細記載. 実装規模 ~150-200 LOC 推定. **下流被引用**: Ch.4 Thm 4.33 + Ch.7 Thm 7.5/7.6 の 3 箇所. proof は Step 1-5 を補題分解する次セッションで完成予定
- **2026-05-23** (同日) **Isaacs Ch.4 Lem 4.6 (G' = ⁅A,⊤⁆) 完全証明完成** ⭐ (sorry 消去): `commutator_eq_commutator_of_normal_abelian_cyclic_quotient`. A ⊴ G abelian + G/A cyclic ⇒ commutator G = ⁅A, ⊤⁆. **章内 5 引用 + Ch.5/7/10 で多用の章内ハブ**. proof: mathlib `commutative_of_cyclic_center_quotient` (`Cyclic.lean:180`) 経由 5-step: (1) ⁅A,⊤⁆ ≤ A (commutator_top_left_le_iff + commutator_comm), (2) lift Q := G/⁅A,⊤⁆ → G/A (QuotientGroup.lift), (3) f.ker ⊆ Z(Q) (∵ y ∈ A, g ∈ G ⇒ ⁅g,y⁆ ∈ ⁅A,⊤⁆ ⇒ Q で gy = yg; QuotientGroup.eq_iff_div_mem 利用), (4) Q commutative (Cyclic.lean lemma 適用), (5) commutator G ⊆ ker(mk' ⁅A,⊤⁆) = ⁅A,⊤⁆. 後半 G' ≅ A/(A∩Z(G)) は別途
- **2026-05-23** (同日) **Isaacs Ch.4 §4B Thm 4.11 (lcs additivity) + Cor 4.13 (derived ⊆ lcs exponential) 完全証明完成** ⭐: (i) `commutator_lowerCentralSeries_le` — `⁅lcs i, lcs j⁆ ≤ lcs (i+j+1)` (mathlib indexing で Isaacs `⁅G^i, G^j⁆ ≤ G^{i+j}`). 証明: `j`-induction (`i` free), step は Cor 4.10 `commutator_commutator_le_of_rotate` を `H₁ = lcs j, H₂ = ⊤, H₃ = lcs i, N = lcs (i+j+2)` で適用 (h1: `⁅⊤, lcs i⁆ = lcs (i+1)` 経由で IH at (i+1); h2: IH + commutator_mono + lcs_succ 定義). mathlib `Characteristic (lcs n)` instance が `[N.Normal]` 自動提供. ~30 LOC. (ii) `derivedSeries_le_lowerCentralSeries_two_pow_sub_one` — `derivedSeries G r ≤ lcs G (2^r - 1)`. mathlib 既存 `derived_le_lower_central` (`derived r ≤ lcs r`) より strictly stronger (r ≥ 2 で). 証明: `r`-induction + commutator_mono + **Thm 4.11** + 算術 (`pow_succ` + omega + `Nat.one_le_two_pow`). ~10 LOC. **下流**: Thm 4.11 は Lucchini K=⊥ aux 解消経路 (Ch.2 §2D Z(F(G)) absorbs G-minimal 補題)
- **2026-05-23** (同日) **Isaacs Ch.4 §4B Cor 4.12 + 量的境界 + iterCommutator インフラ完備** ⭐ **§4B コア完成**: (i) **Cor 4.12** `iterLeftCommutator_mem_lowerCentralSeries` — `iterLeftCommutator g [g₁..gₙ] ∈ lcs G n` (重み n+1 左結合交換子). `List.foldl ⁅·, ·⁆` 定義 + accumulator-depth 汎用補題. (ii) **derived 長量的境界** `derivedSeries_eq_bot_of_lowerCentralSeries_eq_bot` — `lcs G m = ⊥ ⇒ derivedSeries G (Nat.log 2 m + 1) = ⊥`. mathlib qualitative `IsNilpotent → IsSolvable` から explicit upper bound `1 + ⌊log₂ m⌋` へ. (iii) **iterCommutator インフラ** — Lucchini K=⊥ 「Z(F(G)) absorbs G-minimal normal」補題の前哨基地: `iterCommutator E F : ℕ → Subgroup G` (= `⁅...⁅E, F⁆, F⁆..., F⁆`) 定義 + `iterCommutator_le_lowerCentralSeries_map` (`E ≤ F ⇒ iter E F n ≤ (lcs ↥F n).map F.subtype`) + `iterCommutator_normal` + `iterCommutator_succ_le_self` (antitone) + `iterCommutator_eq_bot_of_isNilpotent` (`F` 冪零 ⇒ ∃n, iter = ⊥). §4B (Cor 4.10, Thm 4.11, Cor 4.12, Cor 4.13, 量的境界) **コア完成**. Mann 4.14-4.19 は Phase 1 skip 可 (audit 確認済). 次は Lucchini K=⊥ 本体 + Hall-Higman 3.21 sorry 消去 + §4C/§4D 着手
- **2026-05-23** (同日) **Isaacs Ch.4 Z(F(G)) absorbs G-minimal normal 補題完成** ⭐ (Lucchini K=⊥ aux 核補題): `le_centralizer_of_isMinimalNormal` — E ⊴ G minimal normal + E ≤ F + F ⊴ G + F 冪零 ⇒ E ≤ centralizer F. 証明: iterCommutator 降下列 + smallest-k descent + minimality (~30 LOC). 補助 `iterCommutator_le_self` も追加. **下流**: Ch.2 §2D Lucchini K=⊥ aux の axiom 解消への核. Cor 2.19 + AE 構造解析 + IH on G/E と組み合わせて `lucchini_K_bot_aux` を theorem 化予定. Isaacs PDF p.62-63 の Lucchini Thm 2.20 proof 確認済
- **2026-05-23** (同日) **Isaacs Ch.1 §1D + Mathlib.Subgroup: Lucchini K=⊥ prereq 2 件追加**: (i) `fitting_map_subtype_le_fitting` (Ch.1 §1D) — `M ⊴ G ⇒ (fitting ↥M).map M.subtype ≤ fitting G`. `fitting.isNilpotent` + `equivMapOfInjective` + `nilpotent_of_mulEquiv` + `nilpotent_normal_le_fitting` で ~7 LOC. (ii) `inf_sup_eq_sup_inf_of_normal_of_le` (Mathlib.Subgroup) — **Dedekind modular law** `E ⊴ G, E ≤ M ⇒ M ⊓ (E ⊔ A) = E ⊔ (M ⊓ A)`. mathlib v4.29.1 `IsModularLattice (Subgroup G)` instance は `[CommGroup G]` 限定で非可換版不在. `Subgroup.mem_sup_of_normal_left` で element-level 計算 ~15 LOC. **Lucchini K=⊥ aux 解消で残: M abelian/non-abelian の 2 case 分析** (各 ~50-80 LOC)
- **2026-05-23** (同日) **Isaacs Ch.4 Lucchini K=⊥ 1st step composition 完成**: `exists_isMinimalNormal_le_fitting_le_centralizer_fitting` — G 非自明有限 + A abelian + `|A| ≥ |G:A|` ⇒ ∃ E ⊴ G minimal normal で `E ≤ F(G) ∧ E ≤ centralizer F(G)`. 既存の Cor 2.19 + exists_isMinimalNormal_le + Z(F(G)) absorbs 補題を ~10 LOC で連結. 書籍 p.62 Lucchini proof の最初の 3 ステップに対応. **残**: (i) E elem abelian p-群 結論 (E ≤ F(G) nilpotent + minimal normal 経由, ~30-50 LOC), (ii) M abelian case (φ(m)=m^p homo + B ≤ p + M=B 矛盾, ~50-80 LOC), (iii) M non-abelian case (Z(M) cyclic + B ∩ F(M) ⊆ Z(M) characteristic, ~50-80 LOC), (iv) glue together with IH on G/E (~30 LOC). **`ForwardFromCh02.lean` への移行は import structure 整理が必要** (現状 Ch03 が ForwardFromCh02 を import するため Main.lean からの逆参照不可)
- **2026-05-23** (同日) **Isaacs Ch.4 Thm 3.11 全体の nilpotent 部分群版 + Lucchini 1st step 拡張**: 3 補題追加で Lucchini K=⊥ aux **前提完全完成**: (i) `commutator_lt_self_of_isNilpotent_subtype` — `↥E` 冪零 + 非自明 ⇒ `⁅E, E⁆ < E` (mathlib `IsSolvable.commutator_lt_of_ne_bot` の冪零部分群版). (ii) `isCommutative_of_isMinimalNormal_of_isNilpotent_subtype` — Thm 3.11 part 1 (minimal normal + abelian) の nilpotent 版. (iii) `isElementaryAbelian_of_isMinimalNormal_of_isNilpotent_subtype` — Thm 3.11 全体 (minimal normal + elem abelian p-group) の nilpotent 版 (~60 LOC, Ch.3 既存 proof structure を copy + abelian step を (ii) に置換). `exists_isMinimalNormal_le_fitting_le_centralizer_fitting` も拡張: `Group.IsNilpotent ↥E` を `subgroupOfEquivOfLe` 経由で取得し elem abelian p-group 結論を出力に追加. **Lucchini K=⊥ aux 前提**: Cor 2.19 ✅ + minimal normal exists ✅ + Z(F(G)) absorbs ✅ + E nilpotent ✅ + E elem abelian ✅ + F(M) ⊆ F(G) ✅ + Dedekind law ✅. 残: body の M abelian/non-abelian 2 case 統合

## Phase 1 内の章間依存 (Isaacs)

Isaacs FGT 本文中で `Theorem|Lemma|Corollary|Proposition N.M` 形式の章間参照を `references/isaacs/finite-group-theory.mmd` から集計した実依存:

```
Ch.1 (Sylow) ──┬─→ Ch.2 (Subnormality) ──→ Ch.9 (F*)
               │     │
               │     ↓
               ├─→ Ch.3 (Hall, S-Z) ─→ Ch.4 (Commutators) ─→ Ch.5 (Transfer)
               │                                                  │
               │                                                  ↓
               │                                             Ch.6 (Frobenius)
               │                                                  │
               │                                       ┌──────────┤
               │                                       ↓          ↓
               │                                 Ch.10 (More)  Ch.7 (Thompson, ZJ)
               │
               └─→ Ch.8 (Permutation, 実質独立)

Appendix: 前提なし
```

並列着手の指針:

- **第 1 波 (前提なし、mathlib 既存資産で薄く):** Ch.1, Ch.8, Appendix
- **第 2 波 (Ch.1 完了後):** Ch.2
- **第 3 波 (Ch.2 完了後、並列可):** Ch.3, Ch.9 (F\* は Ch.2 直後に着手可)
- **第 4 波:** Ch.4 → Ch.5 → Ch.6 のシーケンス (Transfer は mathlib 既存で速い)
- **第 5 波 (Ch.6 完了後、並列可):** Ch.7 (Thompson J(P), ZJ), Ch.10 (More Transfer)

クリティカルパスは Ch.6 → Ch.7 (Frobenius 群と Thompson subgroup の新規実装が Phase 1 の山場)。Ch.9 (F\*) は意外に Ch.6/Ch.7 を待たずに並行できる。

集計再現手順 (mathlib や Isaacs 改訂で章番号が変わった場合に再実行):

```bash
mmd=references/isaacs/finite-group-theory.mmd
# 章境界: grep -n "^## Chapter " "$mmd" で取得 (Ch.3 は MISSING_PAGE_EMPTY で欠落するので前後章から推定)
# 各章本文範囲を awk で切り出し、Theorem/Lemma/Corollary/Proposition N.M の N を grep -oE で抽出
awk -v s=START -v e=END 'NR>=s && NR<e' "$mmd" \
  | grep -oE "(Theorem|Lemma|Corollary|Proposition) [0-9]+\.[0-9]+" \
  | grep -oE "[0-9]+\.[0-9]+" | awk -F. '{print "Ch."$1}' \
  | sort | uniq -c | sort -rn
```

## チャプター進捗チェックリスト

### Phase 1 — Isaacs

- [ ] Ch.1 Sylow Theory (p.1) — *前提なし*
- [ ] Ch.2 Subnormality (p.45) — *前提: Ch.1*
- [ ] Ch.3 Split Extensions (p.65) — Hall, Schur-Zassenhaus; *前提: Ch.1, Ch.2*
- [ ] Ch.4 Commutators (p.113) — *前提: Ch.3 (Ch.1, Ch.2 軽)*
- [ ] Ch.5 Transfer (p.147) — *前提: Ch.3, Ch.4*
- [ ] Ch.6 Frobenius Actions (p.177) — *前提: Ch.3, Ch.4, Ch.5*
- [ ] Ch.7 The Thompson Subgroup (p.201) — J(P), ZJ; *前提: Ch.6 (Ch.1-5 横断)*
- [ ] Ch.8 Permutation Groups (p.223) — *前提: Ch.1 (実質独立)*
- [ ] Ch.9 More on Subnormality (p.271) — F*(G); *前提: Ch.2 (Ch.1 軽)*
- [ ] Ch.10 More Transfer Theory (p.295) — *前提: Ch.4, Ch.5, Ch.6*
- [ ] Appendix: The Basics (p.325) — *前提なし (基礎集合)*

### Phase 2a — Bender-Glauberman

**Overview**: [`notes/bg/_overview.md`](notes/bg/_overview.md) — 全 138 結果 (本文 121 + Appendix 17). 3 冊間クロス参照: [`notes/meta/phase2_cross_refs.md`](notes/meta/phase2_cross_refs.md). FT クリティカル経路: §1-§5 → **§6 Thm 6.2 (= Isaacs Thm 7.6 normal-J)** → §7-§9 Uniqueness → §10-§13 Maximal → §14-§16 Main → App.C. App.A "p-Stability" は §6-§16 全体に暗黙の前提.

**Chapter I. Preliminary Results** (62 結果)
- [ ] §1 Elementary Properties of Solvable Groups (p.1) — 22 結果. **Prop 1.5-1.6 が Peterfalvi で多用**. A-invariant Hall + p-length + solvable basic. *前提: Isaacs Ch.1, Ch.3, Ch.4* — [調査メモ](notes/bg/s01_solvable.md): A-invariant Hall (Prop 1.5 = 28+ 引用, Lemma 1.1 = 43+ 引用), Prop 1.15 = Isaacs 3.21 Hall-Higman 1.2.3, 9/22 が mathlib 直接, 8/22 が Isaacs 再引用, 5/22 が新規定義/構造
- [ ] §2 General Results on Representations (p.9) — 6 結果. Operator group の表現、Fong-Swan 系. 本文使用 1-2 箇所. *前提: Isaacs Ch.6 軽* — [調査メモ](notes/bg/s02_representations.md): Thm 2.1 Schur, Thm 2.3 Fong-Swan, Thm 2.5/2.6 extraspecial. mathlib カバレッジ high (大半 `RepresentationTheory.*` 既存). **本節は optional, 必要時のみ着手**
- [ ] §3 Actions of Frobenius Groups (p.17) — 10 結果. Frobenius kernel nilpotent + 表現論的 Frobenius action. **Isaacs Ch.6 全面前提**. *前提: Isaacs Ch.6 完成* — [調査メモ](notes/bg/s03_frobenius_actions.md): Lem 3.2 = Isaacs 6.2 (quotient Frobenius), L825 Note = Isaacs 6.24 (kernel nilpotent), Thm 3.6 Z-group centralizer (244 行 13 step proof), Peterfalvi 04.11 (9.1) Wielandt 引用. mathlib `FrobeniusGroup` 完全未収載, 90% 新規
- [ ] §4 p-Groups of Small Rank (p.33) — 10 結果. Rank ≤ 2 p-群構造定理 (Blackburn). *前提: Isaacs Ch.4* — [調査メモ](notes/bg/s04_pgroups_small_rank.md): **Thm 4.16 (Blackburn) が中核**. m_p(G), r_p(G) rank 概念で §10 の α(M) = {p : r_p(M) ≥ 3} を定義. mathlib カバレッジ 30-40%, 新規 60-70%, 25-35 日推定
- [ ] §5 Narrow p-Groups (p.44) — 7 結果. Narrow p-群族, Sylow 形状制限. *前提: Isaacs Ch.4* — [調査メモ](notes/bg/s05_narrow_pgroups.md): Thm 5.3 narrow characterization (r(R) ≤ 2 自動 narrow, r ≥ 3 は elementary abelian maximal で characterize). §4 (Small Rank) を統一概念に. mathlib 100% 新規
- [ ] §6 Additional Results (p.49) — 7 結果 (Thm 6.1, 6.2, 6.3, 6.4, 6.7 + Lem 6.5, 6.6). solvable + p-length 1 + Frobenius factorization. **§7-§16 で多用される道具袋**. mmd L1957-2128 (§6 ヘッダ Nougat 抽出ミスあり、`**6.**` インライン). *前提: Isaacs Ch.5, Ch.7* — [調査メモ](notes/bg/s06_additional.md): **Thm 6.2 (normal-J) ≡ Isaacs Thm 7.6** odd-order 等価, §8 (3 箇所) §9 (2 箇所) App.A (Thm A.4(b) で再述) App.B App.C で 7+ 引用. 形式化方針: Isaacs 7.6 import 推奨 (1-2 日) vs BG App.A 経由再証明 (4-5 日). MISSING_PAGE:67 は §6 末で論理影響無し

**Chapter II. The Uniqueness Theorem** (10 結果)
- [ ] §7 The Transitivity Theorem (p.55) — 3 結果. **Hypothesis 7.1 で最小反例 G を固定** (mmd L2133). *前提: Isaacs Ch.7 (J(P))* — [調査メモ](notes/bg/s07_transitivity.md): Hypothesis 7.1 (G, ℳ, 𝒰, SCN_3(p), ℋ_H(A;π) 記法), Thm 7.4 propagation theorem, Thm 7.6 Thompson Transitivity. §8-§16 暗黙前提. 実装 11-15 日
- [ ] §8 The Fitting Subgroup of a Maximal Subgroup (p.61) — 1 結果. **Thm 6.2 を 5+ 箇所引用**. *前提: §6, §7, Isaacs Ch.7 Thm 7.6* — [調査メモ](notes/bg/s08_fitting_max.md): Theorem 8.1 + 番号付き式 (8.1)-(8.13). Case (a) F(M) not p-group / Case (b) F(M) = p-group の分岐証明. Thm 6.2 引用 L2456/L2478/L2482 の精密文脈. §9 Uniqueness の直接前提
- [ ] §9 The Uniqueness Theorem (p.64) — 6 結果. central structure + maximal subgroup 一意性. **Thm 6.2 を 4+ 箇所引用**. *前提: §8, Isaacs Ch.7 Thm 7.6* — [調査メモ](notes/bg/s09_uniqueness.md): Thm 9.6 主結果 (r(K) ≥ 2 ⇒ K ∈ 𝒰), Lemma 9.5 pivotal (SCN₃(p) ∈ 𝒰, 67 行最複雑証明), §10-§16 + App.C で連鎖被引用. 実装 7-10 日

**Chapter III. Maximal Subgroups** (32 結果)
- [ ] §10 The Subgroups M_α and M_σ (p.69) — 6 結果. maximal subgroup の族の定義・性質. *前提: §9* — [調査メモ](notes/bg/s10_malpha_msigma.md): α(M) = {p : r_p(M) ≥ 3}, σ(M) = {p : N_G(P) ⊆ M}, β(M) ideal primes. Thm 10.2 Hall M_α/M_σ 主定理, Cor 10.7 Sylow structure (5 部). Lem 6.5/6.6 多用 (L2795-L2801)
- [ ] §11 Exceptional Maximal Subgroups (p.80) — 4 結果. 例外 maximal subgroup 分類. *前提: §10* — [調査メモ](notes/bg/s11_exceptional_maximal.md): Hypothesis 11.1 + Thm 11.3/11.5/11.7 のチェーン (nilpotency → abelianity → normality M_σA ⊴ M). §10 から 13 引用箇所継承
- [ ] §12 The Subgroup E (p.83) — 15 結果 (大規模, §12 が小章相当). 部分群 E の構造と共役性. *前提: §10-§11, Isaacs Ch.7* — [調査メモ](notes/bg/s12_subgroup_e.md): τ₁/τ₂/τ₃(M) partition + Hall E₁/E₂/E₃. Group A (12.1-12.4) E 基本, Group B (12.5-12.12) τ₂(M)≠∅ 局所解析最複雑, Group C (12.13-12.19) σ(M) embedding. **2000+ 行 Lean 予想, 3 ファイル分割推奨**
- [ ] §13 Prime Action (p.97) — 7 結果. derived series, Thompson 風作用. *前提: §12* — [調査メモ](notes/bg/s13_prime_action.md): Thm 13.4 中核 (Thompson 風, derived series 制御, 33 行証明), Lem 13.7 E₁E₃ 同時作用 conditional. §12 から 13+ 引用. 800-1100 行 Lean

**Chapter IV. The Family of All Maximal Subgroups of G** (17 結果)
- [ ] §14 Maximal Subgroups of Type 𝒫 and Counting (p.105) — 7 結果. counting argument; type-𝒫 構造. *前提: §10-§13 統合* — [調査メモ](notes/bg/s14_type_p_counting.md): Thm 14.7 中核 (Type 𝒫 family duality + Z cyclicity + TI-set), Cor 14.10 **ℓ_σ(g) ≤ 2** が framework 頂点. σ-分解 + κ(M) で Type 𝒫₁/𝒫₂ 分類
- [ ] §15 The Subgroup M_F (p.117) — 9 結果. Fitting 関連 maximal. *前提: §14* — [調査メモ](notes/bg/s15_m_f.md): Theorem 15.2 (M_F ≠ M_σ ⇒ type 𝒫₁), Type ℱ/𝒫₁/𝒫₂ 分類. §16 への橋渡し. 800-1200 行 Lean, 6-12 週推定
- [ ] §16 The Main Results (p.123) — 1 結果 (Theorem B). FT 局所部の最終. App.C / Peterfalvi へ橋渡し. *前提: §1-§15 全統合* — [調査メモ](notes/bg/s16_main_results.md): **Theorem A-E** statement (Type I-V 分類確定). Peterfalvi §10 (8.11-8.13) 入力. Phase 3 結合の前提. 18-25 日独立, 10-12 日 Peterfalvi 並行

**Appendices** (17 結果)
- [ ] App.A Prerequisites and p-Stability (p.135) — 5 結果 (Thm A.1-A.5). **Thm A.4(b) ≡ Isaacs Thm 7.6 odd-order 版**. §6 Thm 6.2 の証明前提. *前提: Isaacs Ch.7 全面* — [調査メモ](notes/bg/appA_pstability.md): p-stability 概念の正式定義 (Glauberman 1968 [11] origin), Isaacs Ch.7 全体の odd-order 再構築. A.5 が App.B Puig L(S) の中核前提. 実装量 ~530 行 / 9-11 日. mathlib ~10%, Phase 1 Ch.7 import ~50%, 新規 ~40%
- [ ] App.B The Puig Subgroup L(S) (p.139) — 3 結果. J(S) の代替 Puig 不変部分群. App.A 補強の独立証明枝. *前提: App.A* — [調査メモ](notes/bg/appB_puig.md): Lem B.1-B.3 + Thm B.4 (= Thm 6.2 substitute). J(S) path vs L(S) path 二者択一, **J(S) path で BG 本文完結可** (App.B は optional)
- [ ] App.C The Final Contradiction (p.145) — 3 結果 (Theorem C, Lem C.1, C.2). **Peterfalvi 1984 paper [22] の Carlip-Wheeler 編集再録**. **Phase 2b §9 と統合形式化**. mmd L4763 `## Appendix D Main Theorem` は Nougat 抽出ミスで App.C 本文の続き. — [調査メモ](notes/bg/appC_final_contradiction.md): 指標論 (Peterfalvi) vs 有限体代数 (BG) の対応マップ. Theorem C + Lem C.1-C.3 + 11 個 Preliminary (I)-(XI). Phase 3 で統合
- [ ] App.D CN-Groups of Odd Order (p.153) — 2 結果. Feit-Hall-Thompson 1960 短縮ルート. FT 本筋外 (△). — [調査メモ](notes/bg/appD_cn_groups.md): Lem D.1 (Sylow TI for min simple CN) + Lem D.2 (P ⊆ N'). Thm 6.2 + Focal Subgroup Theorem を CN-theorem に応用. **Phase 2 完全 skip 推奨**, Phase 4 後の発展材料
- [ ] App.E Further Results of Feit and Thompson (p.157) — 5 結果. 発展結果. Phase 2a 完了後の発展材料、または Phase 4 メイン結合時に. △. — [調査メモ](notes/bg/appE_further_results.md): Thm E.1 (Philip Hall lower central) + Prop E.2 (φ(x)=x^p homo) + Thm E.3 (Feit-Thompson 1991 regular operator), BG 本書での被引用 0. Phase 4 後の発展材料 (~1000 行 Lean, 13-18 日)

### Phase 2b — Peterfalvi 本体 (Character Theory for the Odd Order Theorem)

**Overview**: [`notes/peterfalvi/_overview.md`](notes/peterfalvi/_overview.md) — 本文 113 結果 ((N.M) 形式) + 付録 27 結果 (140 結果). FT クリティカル: §3-§8 (指標論コア) → §9 (= BG App.C) → §10-§15 (型分析、BG Ch.3-Ch.4 出力依存) → §16 (G 非存在). 全節 ☆ (FT 必須). 付録は △.

- [ ] §1 Introduction (pp.1-2) — 0 結果. FT 証明戦略 + BG 依存明示. *前提なし* — [調査メモ (§1+§2 合体)](notes/peterfalvi/s01s02_intro_notation.md): FT 二部構成 (局所/指標) + [BG]/[Is]/[HB]/[H] 文献依存
- [ ] §2 Notation (pp.3-4) — 0 結果. 指標論・加群記号. *前提なし* — [調査メモ (§1+§2 合体)](notes/peterfalvi/s01s02_intro_notation.md): Irr(G), CF(G), Z[Irr G], Res/Ind, I_G(θ), F(G), O_p(G) 等 40+ 記号 → mathlib 対応表
- [ ] §3 Preliminary Results from Character Theory (pp.5-9) — 10 結果 ((1.1)-(1.10)). Isaacs [Is] 表現論 + Peterfalvi 補強. mathlib `Character.lean` API 橋渡し. *前提: Phase 1 完成, mathlib `RepresentationTheory.Character`* — [調査メモ](notes/peterfalvi/s03_preliminary_character.md): (1.4) tau isometry が §4 Dade の準備 (☆☆☆), (1.3) Fourier 展開も新規. (1.1), (1.5)-(1.8) は Isaacs [Is] Thm 6.32, 6.5, 6.11, Cor 6.28, Cor 2.30 の odd-order 再述. 実装量 ~400 行
- [ ] §4 The Dade Isometry (pp.10-14) — 6 結果 ((2.1)-(2.6)). **TI-subset 上の virtual character isometry**. **新規概念**. *前提: §3* — [調査メモ](notes/peterfalvi/s04_dade_isometry.md): **Phase 2b の山場**, mathlib 完全新規 (~70% 新規実装). 主定理 (2.6) は (a) isometry + (b) virtual character preservation. 形式化方針: **predicate-based (候補 3 推奨)** で `IsDadeIsometry τ hyp` + existence theorem. §5-§8 Coherence の前提. 実装量 ~400-450 行 / 16-18 時間
- [ ] §5 TI-Subsets with Cyclic Normalizers (pp.15-20) — 5 結果 ((3.1)-(3.5)). cyclic normalizer 特殊化. *前提: §4* — [調査メモ](notes/peterfalvi/s05_ti_cyclic_normalizer.md): (3.1) Hypothesis W = W₁×W₂ cyclic + V TI-subset, (3.2) σ Dade isometry の 4 性質, (3.5) **orthonormal (χ_{ij}) 族と分解公式** (最重要, Case I/II 矛盾排除, 計算の山場). 実装 23-31 時間
- [ ] §6 The Dade Isometry for a Certain Type of Subgroup (pp.21-24) — 5 結果 ((4.1)-(4.5)). Dade 拡張. *前提: §4-§5* — [調査メモ](notes/peterfalvi/s06_dade_certain_subgroup.md): (4.2) Hypothesis L = K ⋊ W₁ + cyclic Hall + C_K(x) = W₂, (4.3) TI-subset (W - W₂) + Induced character decomposition μ_ij, (4.5) χ_j i-independence + Irr(L) 完全性. 13-16 時間
- [ ] §7 Coherence (pp.25-29) — 6 結果 ((5.1)-(5.6)). **Coherence 定義 + 基本性質**. Dade 後の isometry 整合条件. **新規概念**. *前提: §4* — [調査メモ](notes/peterfalvi/s07_coherence.md): (5.1) Coherence の正式定義 (Z[S] への τ 拡張 + virtual character の差での expression). 形式化候補: **predicate-based (IsCoherent τ̃)** が §4 設計と整合, coherent triple (τ₁,τ₂,τ₃) 比較が自然. 14-18 時間
- [ ] §8 Some Coherence Theorems (pp.30-37) — 4 結果 ((6.1)-(6.4)). Coherence 応用定理. Sibley/Reynolds 系含む. *前提: §7* — [調査メモ](notes/peterfalvi/s08_coherence_theorems.md): Sibley 1984 (6.4)-(6.6) p-group determination bound, Reynolds 1965 (6.7) character mod \|P\|, (6.8) main theorem Frobenius family 統合 (最複雑, 7-10 日). 30 日推定
- [ ] §9 Non-existence of a Certain Type of Group of Odd Order (pp.38-43) — 6 結果 ((7.1)-(7.6)). **≡ BG App.C Theorem C**. Frobenius family の非存在. *前提: §3-§8 + BG §3* — [調査メモ](notes/peterfalvi/s09_nonexistence_certain.md): BG App.C と内容重複 (BG L4759-5005). 形式化方針: **Peterfalvi §9 を一次, BG App.C は section docstring + reference**. Phase 3 で equivalence lemma `OddOrder.BG.AppC.TheoremC ≅ OddOrder.Peterfalvi.S09.TheoremC`. 有限体 F_{p^q} + norm-1 部分群 U + Frobenius H = PU の Lean 形式化設計含む
- [ ] §10 Structure of a Minimal Simple Group of Odd Order (pp.44-49) — 6 結果 ((8.1)-(8.6)). **G の Type I-V 分類定義**. BG Theorem A-E 翻訳. *前提: **BG §10-§16 全面*** — [調査メモ](notes/peterfalvi/s10_structure_minimal_simple.md): (8.11)→BG Thm A, (8.12)/(8.13)→Thm B/D, (8.8)-(8.9)→Thm C. Type 𝓕/𝓟 基礎層 + Type I-V 精密 5 分類. `inductive PeterfalviType` Lean 設計. 20-25 日
- [ ] §11 Maximal Subgroups of G of Types II, III and IV (pp.50-57) — 9 結果 ((9.1)-(9.9)). (9.1) Wielandt 作用, (9.2) Frobenius kernel cohomology. *前提: §10 + BG §11-§13* — [調査メモ](notes/peterfalvi/s11_maximal_II_III_IV.md): (9.7) Clifford 分岐 (Case (a) 分散的 H̄ vs Case (b) F = 𝔽_{p^q} 既約), (9.10) Frobenius 実現化, (9.11) Coherence 完全性証明 (8 sub-lemma, 最大規模)
- [ ] §12 Maximal Subgroups of Types III, IV and V (pp.58-63) — 7 結果 ((10.1)-(10.7)). (10.7) [S,S] が Frobenius. *前提: §11* — [調査メモ](notes/peterfalvi/s12_maximal_III_IV_V.md): (10.7) [S,S] Frobenius §16 最終矛盾の重要段階, (10.8) ℐ non-coherent 背理法 (numerical chain). 680-850 行 Lean, 9-11 日
- [ ] §13 Maximal Subgroups of Types III and IV (pp.64-68) — 8 結果 ((11.1)-(11.8)). *前提: §12* — [調査メモ](notes/peterfalvi/s13_maximal_III_IV.md): (11.3)-(11.5) commutator 階層 M''=HC, (11.6)-(11.7) 核構造 (p-group, H₀=H', C=U'), (11.8) character orthogonality (5 段階 sub-lemma 最技巧), (11.9) Type III 確定
- [ ] §14 Maximal Subgroups of Type I (pp.69-74) — 13 結果 ((12.1)-(12.13)). 型 I は最複雑. *前提: §13 + BG §12 (E)* — [調査メモ](notes/peterfalvi/s14_maximal_type_I.md): (12.7) **Main Theorem: Type I ⇒ Frobenius group**, (12.12) complement order e は (p±1) の約数, (12.16) Sylow non-cyclic 反例排除, (12.17) Case (b) [S,T 存在] 強制. 1000-1500 行 Lean / 4-5 週
- [ ] §15 The Subgroups S and T (pp.75-86) — 17 結果 ((13.1)-(13.17)). **本文最大規模 (365 行)**. S, T の位数・正規化群・指標. §16 直前の最終仕込み. *前提: §14 + BG §15 (M_F)* — [調査メモ](notes/peterfalvi/s15_s_and_t.md): Phase A setup + B character + C 位数 c=1 + D 外部構造の 4 フェーズ. (13.12) c=1 numeric exhaustion, (13.15) u 決定, (13.19.c) §16 dichotomy 入力. **1500-1800 行 Lean / 6-7 週, 4 ファイル分割推奨**
- [ ] §16 Non-existence of G (pp.87-92) — 11 結果 ((14.1)-(14.11)). **FT 完了 = G の非存在**. 指標論計算が中心. *前提: §3-§15 + BG §16* — [調査メモ](notes/peterfalvi/s16_nonexistence_g.md): (14.11) 主結果に 4 sub-propositions, (14.11.4) norm inequality cascade で最終矛盾, BG App.C との合体方針 (Phase 3). Phase 4 FeitThompson メイン定理の statement 設計. **1000-1200 行 Lean / 5 週**

**Peterfalvi 補章** (27 結果, 全 △ = FT 経路外)
- [ ] App: A Theorem of Suzuki (pp.97-134) — 21 結果 (Prop 1-16 in 05.3 + Lemmas in 05.0-05.6). Suzuki 1962: PSL(2,q), Sz(q), PSU(3,q) の二重推移群特性化 — [調査メモ](notes/peterfalvi/appA_suzuki.md): mathlib PSL(2,q) 既存, Sz(q)/PSU(3,q) 完全新規. Phase 1 Ch.8 (Permutation Groups) 依存. 本筋外 (△). 1500-2500 行 Lean
- [ ] App: A Special Case of a Theorem of Huppert (pp.135-136) — 1 結果. Huppert 1957 定理の Peterfalvi 流再証明 — [調査メモ (B-E 合体)](notes/peterfalvi/appB_E_small_appendices.md)
- [ ] App: On Near-Fields (pp.137-138) — 2 結果. Near-field (Wedderburn 系) の基本 — [調査メモ (B-E 合体)](notes/peterfalvi/appB_E_small_appendices.md)
- [ ] App: On Suzuki 2-Groups (pp.139-143) — 4 結果. Higman 分類 Suzuki 2-群 — [調査メモ (B-E 合体)](notes/peterfalvi/appB_E_small_appendices.md)
- [ ] App: The Feit-Sibley Theorem (pp.144-150) — 2 結果. Feit-Sibley 1976 定理 — [調査メモ (B-E 合体)](notes/peterfalvi/appB_E_small_appendices.md)

### Phase 3-4

- [ ] Phase 3: 最終矛盾の結合 — BG App.C と Peterfalvi §16 の整合・統合
- [ ] Phase 4: `FeitThompson` メイン定理ステートメントと完全証明結合

## ノート・小ロードマップの管理

章節単位のミニロードマップ・調査結果・設計決定は `notes/` 配下に置く:

```
notes/
├── isaacs/
│   ├── ch01_sylow.md          # Isaacs Ch.1 用ミニロードマップ + 調査
│   ├── ch03_split.md
│   └── ...
├── bg/
│   ├── s08_fitting.md         # BG §8 用
│   └── ...
├── peterfalvi/
│   └── ...
└── meta/                       # 章節に紐づかない横断調査・設計決定
    ├── 2026-05-21-namespace-strategy.md
    └── ...
```

各 `.md` には「調査」「計画」「未解決の疑問」を見出しで混在させてよい。本 ROADMAP のチェックリストから対応する `notes/` へリンクして掘り下げる運用。

## 補足ドキュメント

- mathlib カバレッジ詳細 (どの mathlib 資産が使えるか、何が欠けているか): [`notes/meta/mathlib_coverage.md`](notes/meta/mathlib_coverage.md)
- プロジェクトセットアップ状態: メモリ `project_setup_state.md` 参照
