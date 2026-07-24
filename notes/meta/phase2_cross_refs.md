# Phase 2 形式化のクロス参照マップ (3 冊)

**目的**: Isaacs / BG / Peterfalvi 間の "Theorem X.Y" 引用関係を 1 箇所に集約。Phase 2 形式化中に「この結果はどの教科書のどこから来たか」を即座に解決するための索引。

**作成**: 2026-05-22.
**出典**: `references/isaacs/finite-group-theory.mmd`, `references/bg/local-analysis.mmd`, `references/peterfalvi/04.*.mmd` + `05-09.*.mmd`, および Phase 1 Isaacs 各章ノート `notes/isaacs/ch{01-10}_*.md`.

## 0. 凡例

| 表記 (本文中) | 意味 | 本プロジェクトでの読み替え |
|---|---|---|
| `**G**`, `G, Thm X.Y.Z` (BG 内) | Gorenstein 1968 _Finite Groups_ | **Isaacs FGT** (CLAUDE.md の選択) |
| `[Is]` (Peterfalvi 内) | Isaacs 1976 _Character Theory of Finite Groups_ | 当面 mathlib `RepresentationTheory.Character` で代用 |
| `[BG]` (Peterfalvi 内) | Bender-Glauberman 1994 _Local Analysis_ | 本プロジェクト Phase 2a |
| `[FT]` (両者) | Feit-Thompson 1963 _Solvability of Groups of Odd Order_ | Phase 4 メイン定理 |
| `[H]`, `[HB]` (Peterfalvi 内) | Huppert _Endliche Gruppen_, Huppert-Blackburn _Finite Groups_ | 個別調査 |
| `[Pe]` (BG 内) | Peterfalvi 1984 (FT Ch.VI 改訂論文) | BG App.C = 当該論文の編集再録 |

## 1. BG 内引用構造

BG 全 138 結果のうち、外部引用 (Gorenstein/Isaacs 経由) と Peterfalvi 経由は以下:

| § | 内容 | Gorenstein (Isaacs 読み替え) | Peterfalvi | 自参照 |
|---|---|---|---|---|
| §1 | Elementary Properties | **多数** (1.8 ↔ Isaacs 1.8 Burnside operator, 1.11 ↔ Isaacs 4.36, 1.13 Thompson critical ↔ G 5.3.11, 1.17 ↔ Isaacs 5.21 Focal, 1.18 ↔ Isaacs 5.13 Burnside, 1.20 Maschke ↔ mathlib `Maschke`) | 0 件 | 高 (内部) |
| §2 | Representations | **多数** (2.1 ↔ G 3.5.7, 2.3 Fong-Swan, 2.5 ↔ G 5.5.4, 2.6 ↔ G 2.6.3) | 0 件 | §1, §2 |
| §3 | Frobenius Groups | **多数** (3.1 ↔ Isaacs 6.1-6.10 Frobenius basic, 3.2 ↔ Isaacs 6.2 quotient, 3.4-3.6 ↔ G + Isaacs 6.11-6.24, Note L825 ↔ Isaacs 6.24 kernel nilpotent) | 0 件 | §1 |
| §4-§5 | p-Groups, Narrow | (自己完結) | 0 件 | 内部 |
| §6 | Additional Results | (mostly self-contained) | 0 件 | §1, §3 |
| §7-§9 | Uniqueness Theorem | **Thm 6.2** (= Isaacs 7.6) を §8 で 5+ 回, §9 で 4+ 回引用. **L2456, L2480, L2482, L2511, L2515** | 0 件 | 高度に相互 |
| §10-§13 | Maximal Subgroups | 0 件外部, §6/§9 internal | 0 件 | 内部 |
| §14-§16 | Family / Main | (App.C へ橋渡し) | 0 件 (本文) / App.C で Peterfalvi 編集再録 | 内部 |
| App.A | p-Stability | **A.4(b) は Isaacs Thm 7.6 の corollary** (同値ではない) *(2026-05-23 audit 訂正)* | 0 件 | §6 (上流) |
| **App.B** | Puig L(S) | **Thm 6.2 の自己完結代替の本線** (Thm B.4)。~~Phase 2a スキップ推奨~~ は **2026-05-28 撤回**: Isaacs が Z(J) を省くため必須。B.3+B.4 が Thm A.5 cite; J(S)⊆L(S) (equal でない) → §8-§16 を L(S) で formalize。詳細 [`bg_s6_appAB_route_2026_05_28.md`](log/bg_s6_appAB_route_2026_05_28.md) | 0 件 | (Thm A.5) |
| App.C | Final Contradiction | 0 件 | **= [Pe] 編集再録 (Carlip-Wheeler 編)** | 自己完結 |
| App.D | Cn-Groups | (Suzuki 1957 ベース) | 0 件 | 独立 |
| App.E | Further Results | 雑多な発展. FT 後の話題 | 0 件 | 独立 |

**重要観察**:
- BG 本文 (§1-§16) は **Peterfalvi 論文/本を本文中で直接引用しない**. App.C で Peterfalvi 1984 paper [22] を編集再録するだけ.
- 逆に Peterfalvi 本書は BG を多数引用 (§ 2 参照).
- BG の "G, Thm X.Y" 引用は **全て Gorenstein 1968** 経由で、本プロジェクトは Isaacs FGT に読み替え.

## 2. Peterfalvi 内引用構造

Peterfalvi 全 140 結果 (本文 113 + 付録 27) の引用パターン:

| 範囲 | [BG] 引用 | [Is] 引用 | [G]/[H]/[HB] 引用 |
|---|---|---|---|
| 04.1 Introduction | **明示** ([BG] §8 results reviewed, [BG] initial sections) | **多数** ([Is] book assumed known: Thm 6.32, 6.5, 2.21, 6.11, 6.34, 6.2, Lem 7.7, Cor 2.30, Lem 3.2, Lem 3.14) | [H] Satz 8.18, [HB] Thm 12.4 |
| 04.3-04.9 (指標論コア) | **多数** ([BG] Prop 1.5(d), 1.6(d), 1.8, Lem 1.14, 1.22, 3.2, 16.1) | **多数** ([Is] Thm 6.32, 6.5, 2.21, Cor 6.28, 2.30, Lem 7.7) | sparse |
| 04.10-04.16 (構造分析) | **多数** ([BG] Prop 3.9, 16.1, Thm 1.8, Lem 1.22, Prop 1.5(d), 1.6(d), 1.16, 3.2, Thm 2.6(a), **App.C Thm C**) | **数件** ([Is] Thm 6.32, 6.5, 6.34, Lem 1.5) | sparse |
| 05.0 (Suzuki Intro) | **[BG] Prop 1.5(d)** | **[Is] Thm 15.16, 6.5** | [Ha] Hall-Wielandt Thm 14.4.2, [HB] Ch.X Lem 1.9, [H] Satz 8.2, 10.12, 10.13 |
| 05.1-05.6 (Suzuki 詳細) | sparse | **多数 [Is]** | [HB] XI.3.6, [H] II.6.13, 10.12 |
| 06.0-09.0 (Huppert, Near-fields, Suzuki 2, Feit-Sibley) | **0 件** | sparse [Is] | [HB], [H] が主 |

**重要観察**:
- Peterfalvi 本書 (§1-§16 = 04.*) は **[BG] を多数引用** — Phase 2b §10-§16 は Phase 2a の出力を直接前提.
- Peterfalvi 04.17 Notes に編集者注 ("§8 = [FT] Thm 14.1, 14.2 翻訳" 等) — Phase 4 メイン結合時に重要.
- 付録 (05-09) は本書本体から独立で **[BG] 引用ゼロ** — Phase 2b 必須範囲は本体 §1-§16 のみ.

## 3. BG ↔ Peterfalvi 対応

### 3.1 App.C ≡ Peterfalvi §9

- **BG App.C** (L4759-5005, 246 行, 3 結果: Theorem C + Lemma C.1, C.2): Final Contradiction
- **Peterfalvi §9** (04.9_*.mmd, 162 行, 6 結果: (7.1)-(7.6)): Non-existence of a Certain Type of Group of Odd Order
- **対応関係**: BG App.C = Peterfalvi 1984 paper [22] を Carlip & Wheeler が U.Chicago Junior Group Theory Seminar [2] で再編. Peterfalvi 本書 §9 = 同論文の自著.
- **形式化方針**: **Peterfalvi §9 を一次**, BG App.C を二次 (整合性確認用). 形式化は Phase 2b §9 で実施し、`OddOrder.BG.AppC` は thin wrapper or section docstring で BG ↔ Peterfalvi 対応を明記.

### 3.2 BG §16 → Peterfalvi §10 (Theorem A-E 入力)

- **BG §16 Main Results** (L4256-4449): BG Theorem A-E の statement. Phase 2a の最終出力.
- **Peterfalvi §10 Structure of Minimal Simple Group** (04.10, 166 行, 6 結果: (8.1)-(8.6)): BG Theorem A-E を Type I-V の分類として翻訳・受け入れ.
- **形式化方針**: BG §16 で `OddOrder.BG.Ch4.S16.theoremA-E` を定義し、Peterfalvi §10 が import 経由で前提として使う.

### 3.3 BG §15 (M_F) ↔ Peterfalvi §15 (S, T)

- **BG §15** (L4086-4255, 9 結果): The Subgroup M_F (Fitting-related maximal)
- **Peterfalvi §15** (04.15, 365 行, 17 結果: (13.1)-(13.17)): The Subgroups S and T
- **対応関係**: BG が局所構造を作り、Peterfalvi が指標論で **S, T の位数・正規化群・指標** を詰める. **重複ではなく逐次** (BG 出力を入力に使う).

### 3.4 BG App.D vs Peterfalvi 付録

- **BG App.D Cn-Groups of Odd Order** (L5006-5073, 2 結果): Feit-Hall-Thompson 1960 CN-theorem の短縮ルート.
- **Peterfalvi 付録 A Suzuki Theorem** (05.*, 713 行, 27 結果): Suzuki 1962 主定理 (PSL(2,q), Sz(q), PSU(3,q) の二重推移群特性化).
- **対応関係**: 直接の重複ではない. BG App.D は CN-condition 下の simplification、Peterfalvi App.A は 2-trans 群分類. ただし両者とも Suzuki 群を介する点で関連.
- **FT 必須度**: 両者とも △ (本筋外). Phase 2 必須は無し、Phase 4 完成度のため.

## 4. Phase 1 Isaacs ↔ Phase 2 対応表

> **2026-05-27 更新**: 下表「形式化進捗」列の "Phase 1 Ch.X" は作成当時の予定。現状は **Isaacs Ch.1–7 全て sorry-free 完成** (Thm 7.6 `normal_J` / 7.8 Burnside / Ch.6 Frobenius / Hall-Higman 3.21 / Hall-C 3.14 / Schur-Zassenhaus 3.12 含む)、**BG §1–§3 完成**、Peterfalvi §1–§6 着手。被引用構造 (どの定理がどこで使われるか) は引き続き有効。

Phase 1 で形式化済 (or 予定) の Isaacs 結果と、Phase 2 での被引用箇所:

| Isaacs | BG での参照 | Peterfalvi での参照 | FT クリティカル度 | 形式化進捗 |
|--------|--------------|---------------------|-------------------|------------|
| **Thm 1.8 (Burnside operator)** | = BG Thm 1.8 (引数 specialization, BG §1) | 04.3 (Isaacs 表現論経由) | ◯ | Phase 1 Ch.1 |
| **Thm 1.17 (Focal Subgroup)** | = BG Thm 1.17 (BG §1 で再述) | — | ◯ | Phase 1 Ch.5 (mathlib `Focal.lean`) |
| **Thm 1.18 (Burnside p-comp)** | = BG Thm 1.18 (BG §1 で再述) | — | ◯ | Phase 1 Ch.5 (mathlib `Transfer.lean`) |
| **Thm 2.13 (Baer 系)** | (BG §6 で間接利用) | — | △ | Phase 1 Ch.2 (進行中) |
| **Thm 3.13-3.14 (Hall π-subgroup)** | = BG Prop 1.5, 1.6 (BG §1) | 04.11 (9.1) Wielandt action | ☆ | Phase 1 Ch.3 |
| **Thm 3.21 (Hall-Higman 1.2.3)** | = BG Prop 1.15 (BG §1) | — | ☆☆ | Phase 1 Ch.3 |
| **Thm 4.36 (p > 2 一般 p-群)** | = BG Thm 1.11 (BG §1) | — | ☆ | Phase 1 Ch.4 |
| **Thm 5.21 (Focal Subgroup)** | = BG Thm 1.17 | — | ◯ | Phase 1 Ch.5 |
| **Thm 5.26 (Frobenius normal p-complement)** | App.A Thm A.4 周辺で再述 | — | ☆ | Phase 1 Ch.5 |
| **Thm 6.2 (quotient Frobenius)** | = BG Lemma 3.2 (BG §3) | — | ☆ | Phase 1 Ch.6 |
| **Thm 6.11-6.24 (Frobenius actions)** | = BG §3 全面 (Thm 3.1-3.10) | 04.11 (9.1)-(9.6) | ☆☆ | Phase 1 Ch.6 |
| **Thm 6.24 (Frobenius kernel nilpotent)** | BG L825 で明示参照 | — | ☆ | Phase 1 Ch.6 |
| **Thm 7.1 (Thompson normal p-comp)** | (BG では Ch.6 6.24 経由間接) | — | ☆ | Phase 1 Ch.7 |
| **Thm 7.6 (normal-J theorem)** | **= BG Theorem 6.2** (odd-order specialization, BG §6) → §8, §9 で 7+ 箇所引用、App.A Thm A.4(b) で再述 | 04.10 (8.1)-(8.6) で [BG] §6 経由 | **☆☆☆** | Phase 1 Ch.7 (Phase 2a 開始の境界条件) |
| **Thm 7.8 (Burnside p^a q^b, character-free)** | BG L2633 "we can obtain Burnside's p^a q^b very easily now" — 直接引用無し | — | △ | Phase 1 Ch.7 (Phase 1 完成度) |
| **App.A 全 23 結果** | (BG 暗黙の前提) | (Peterfalvi §3 暗黙の前提) | ◯ | Phase 1 完成 = **mathlib 既存で全部覆われる**、ノートのみ |

## 5. BG 主要結果の Isaacs 読み替え

BG §1-§16 で書かれた "Theorem X.Y" の Gorenstein 引用を、Isaacs に読み替えた対応表 (BG §1 集中):

| BG | Gorenstein 原典 | Isaacs 読み替え | 内容 |
|-----|----------------|----------------|------|
| **Thm 1.8** | G 5.1.4 (p.174) | **Isaacs Thm 1.8** | Burnside operator on p-group |
| **Cor 1.10** | G 5.3.7 (p.183) | Isaacs Cor 4.34 系 | (p,q)-coprime operator on abelian |
| **Thm 1.11** | G 5.3.10 (p.184) | **Isaacs Thm 4.36** | p-odd p-群への p'-操作 + Ω₁ trivial |
| **Thm 1.13** | G 5.3.11-13 (pp.185-6) | **Isaacs Thm 1.13** (= 4.31 Thompson critical) | Thompson critical subgroup |
| **Prop 1.15** | G 6.3.3 + 6.2.2 | **Isaacs Thm 3.21 (Hall-Higman 1.2.3)** | π-Hall theorem |
| **Prop 1.16** | G 6.2.4 (p.225) | **第1式 = Isaacs FGT 6.21** = repo `Isaacs.Ch06.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic`; 第2式 = 新 `BG.Ch1.S01b.cocyclicFixedByClosure_eq_top_of_not_isCyclic` | noncyclic abelian auto 生成 ✅ commit d71cbe4 (旧記載 "Isaacs 3.16" は誤り) |
| **Thm 1.17** | G 7.3.4 (p.250) | **Isaacs Thm 5.21** (Focal Subgroup) | Focal subgroup theorem |
| **Thm 1.18** | (古典, 標準証明) | **Isaacs Thm 5.13** | Burnside normal p-complement |
| **Thm 1.20** | (古典, Maschke) | mathlib `Maschke` | Maschke の定理 |
| **Prop 2.1** (Schur+abs.irred.) | G 3.5.2, 3.5.7, 3.6.2 | **Isaacs FGT 不在**; mathlib + 新規 `RepresentationTheory/AbsolutelyIrreducible.lean` | Schur 補題 + 既約 ⟺ Hom_{FG}(M,M)=F |
| **Prop 2.2** (Clifford+cyclic 商) | G 3.4.1 | **Isaacs FGT 不在** (Ch.6 = Frobenius ≠ Clifford); 新規 `RepresentationTheory/Clifford.lean` | Clifford lift to G via cyclic quotient |
| **Lem 2.3** (Fong-Swan) | BG cite [5] Curtis-Reiner Thm 72.1 | Isaacs FGT 不在; Prop 2.2 依存; forward use 0 ⇒ defer | solvable abs.irred. ⇒ dim ∣ \|G\| |
| **Prop 2.4** (eigenspace 分解) | (純線型代数) | 新規 `RepresentationTheory/EigenspaceUnderCyclicAction.lean` | cyclic action 下 V_i ⊕ + E_{i,t} 構造 (10 部) |
| **Thm 2.5** (extraspecial+cyclic) | G 5.5.4-5.5.5 | **Isaacs FGT 不在** (representation theory 章なし); 新規 shared module | extraspecial faithful repr の cyclic H 上構造 |
| **Thm 2.6** (奇数 2-dim) | G Lem 2.6.3 (p-group fixed vec) | **Isaacs FGT 不在**; 新規 `RepresentationTheory/PGroupFixedVector.lean` + mathlib `Maschke` | odd-order 2-dim repr ⇒ abelian / Sylow abelian |

**観察 (2026-05-24 訂正)**: 旧表 (L128-130 三行版) は (i) "Isaacs 表現論 chapter 経由" と書いたが **Isaacs FGT は群論本で representation theory 章なし** (Isaacs mmd で `Clifford` 0 hit, Ch.6 は Frobenius Actions), (ii) Thm 2.6 内容を "Fong-Swan 系" と誤記 (実際は Lem 2.3 が Fong-Swan, Thm 2.6 は奇数 2-dim 構造), (iii) Prop 2.2 (Clifford), Lem 2.3 (Fong-Swan), Prop 2.4 (eigenspace) を欠落. **§2 全 6 結果ともに Isaacs FGT に対応なし** ⇒ 全部 mathlib + 新規 `OddOrder/GroupTheory/RepresentationTheory/*` shared module 経由で再構築の方針.
| **Thm 3.1-3.3** | G 2.7.6-2.7.7, Thompson Thesis | **Isaacs Thm 6.1-6.10** | Frobenius 群 basic |
| **Thm 3.4-3.10** | G + Thompson Thesis | **Isaacs Thm 6.11-6.24** + 表現論補強 | Frobenius action + kernel nilpotent |
| **Thm 6.1** | (Hall-Higman 1.2.3 別形) | **Isaacs Thm 3.21** 再述 | O_{p',p}(G) abelian normal containment |
| **Thm 6.2** | (本書独自 odd-order 版) | **Isaacs Thm 7.6** (normal-J theorem) | `Z(J(S))·O_{p'}(G) ⊴ G` for solvable odd-order |

**観察**: BG §1-§6 の主要 Gorenstein 引用は **大半が Isaacs Ch.1-§7 に直接対応**. Phase 2a §1 着手時には Isaacs Ch.1, 3, 4, 5 が完成していれば、BG §1 は **薄いラッパー or section docstring レベル** で済む見込み (mathlib ラッパー方針 §2.7 に従い、純粋リネームは避ける).

## 5b. 証明内 (mid-proof) の "**G** X.Y.Z" 引用 → repo 定理

§5 の表は **BG 番号付き結果** をキーにするため、後続節の **証明本文中**に "by **G**, Theorem X.Y.Z" として現れる引用は載らない (これを見落としやすい ← memory `bg-gorenstein-reread-as-isaacs` の再発ミス源)。確認済みの mid-proof 引用を repo 定理に解決した索引 (解決し次第ここに追記する):

| BG 出現箇所 | Gorenstein | repo 定理 (確認済み, file:line) | 内容 |
|---|---|---|---|
| §7 Prop 7.5 proof (mmd L2272) | **G 2.6.4** (p.31) | `Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial` (`OddOrder/Isaacs/Ch01_Sylow/Main.lean:355`) | 有限 p-群の非自明正規部分群は中心と非自明に交わる (`1≠N⊴P ⟹ N⊓Z(P)≠1`) |
| §3 Thm 3.4 proof (mmd L893) | **G 5.3.7** (p.181; = 当 ed. Gor 3.7/3.8/3.10, finite-groups.mmd L3850/3866/4228) | `BG.Ch1.S04.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality` (`OddOrder/BG/Ch1_Preliminary/S04e_GorThm37.lean:626`, sorry-free, AxiomsCheck:1250) | coprime minimal 作用 ⇒ special exp-p + A irred on Q/Q' + ψ trivial on Q'。**版で番号違い (BG=1st ed 5.3.7, repo=Gor 3.7)** ゆえ「5.3.7 未形式化」と即断しないこと |
| §3 Thm 3.4 proof (mmd L884) | **G 3.2.2** (p.64) | ℂ版: `RepresentationTheory.SchurCenterBound` (`OddOrder/GroupTheory/RepresentationTheory/SchurCenterBound.lean`, = Isaacs CTFG Cor 2.30, sorry-free)。一般体 F の `IsCyclic (center G)` capstone は未 (Schur→`Module.End` division ring + mathlib `isCyclic_of_subgroup_isDomain` で短い) | faithful irreducible ⇒ Z(G) cyclic |
| §2 Thm 2.5 proof (mmd L756) | **G 5.5.4-5.5.5** (extraspecial faithful irred は center で決定, dim=p^n) | ❌ 未 — Isaacs FGT 不在の **BG 自前 §2 表現論** (§5 L134)。新規 module 要 (Thm 2.5 本体と一体) | extraspecial 既約表現の構造 |

**運用ルール**: 後続節の proof を Lean 化中に "**G** X.Y.Z" を見たら — (1) §5 + 本 §5b を引く、(2) 無ければ `OddOrder/Isaacs` `OddOrder/GroupTheory` + mathlib を grep (新規形式化と即断しない)、(3) `references/gorenstein/finite-groups.mmd` を読むのは Isaacs が真に欠く場合のみ (ZJ / p-stability / critical subgroup — いずれも形式化済)、(4) 解決した対応は本表に追記して次回の引きどころにする。詳細は memory `bg-gorenstein-reread-as-isaacs`。

## 6. 未解決の参照 (TBD)

per-section ノート (`notes/bg/sNN_*.md`, `notes/peterfalvi/sNN_*.md`) で詳細化する項目:

| 内容 | ステータス | 確認先 |
|------|-----------|--------|
| BG §6 mmd 抽出問題 (`### 6` ヘッダ無し) | TBD | BG PDF p.49 で `## 6 Additional Results` 章番号確認 |
| BG App.C mmd 構造 (`## Appendix D Main Theorem` の Nougat 誤認) | TBD | BG PDF p.145 で App.C 章番号確認 |
| BG L2129 MISSING_PAGE_EMPTY:67 | TBD | BG PDF p.67 直接参照 |
| Peterfalvi [Is] (Isaacs 1976 Character Theory) → mathlib 対応 | TBD | mathlib `RepresentationTheory.Character` 探査 (Phase 2b §3 着手時) |
| Peterfalvi 04.17 Notes (編集者注) の Phase 4 影響 | TBD | Phase 4 メイン結合設計時 |
| BG App.D (CN-Groups) ↔ Suzuki 1957 ↔ Peterfalvi App.D (Suzuki 2-groups) | TBD | 三者比較は Phase 2b 完成後 |
| Peterfalvi 付録 [H] Huppert / [HB] Huppert-Blackburn の定理番号 | TBD | Phase 2b 付録 A 着手時 |
| BG App.E (Further Results of Feit and Thompson) | TBD | Phase 4 設計時、または個別 per-section ノート |

## 7. Phase 2 形式化の優先順 (Phase 1 ↔ Phase 2 依存ベース)

**Phase 1 完成境界条件**:
- **Phase 2a §1 開始** = Phase 1 Ch.1, Ch.3, Ch.4, Ch.5 完成
- **Phase 2a §3 開始** = Phase 1 Ch.6 完成
- **Phase 2a §6 開始** = Phase 1 Ch.7 完成 (**Thm 7.6 が必須**)
- **Phase 2a App.A 開始** = Phase 1 Ch.7 完成 (Thm 7.6 + 7.5 + 7.3 + 7.1 全部)
- **Phase 2b §3 開始** = Phase 1 完成 + mathlib `Character` API 確認
- **Phase 2b §10 開始** = Phase 2a §16 完成 (BG Theorem A-E)

**並列着手可能なグループ**:
- **Group α (Phase 1 Ch.1-§5 完成後)**: Phase 2a §1, §4, §5, App.B, Phase 2b §1, §2
- **Group β (Phase 1 Ch.6 完成後)**: Phase 2a §3, §6, App.A, Phase 2b §3
- **Group γ (Phase 1 Ch.7 完成後)**: Phase 2a §7-§9 (線形チェーン)
- **Group δ (Phase 2a Ch.2 完成後)**: Phase 2a §10-§13, Phase 2b §4-§8 (並列)
- **Group ε (Phase 2a Ch.4 完成後)**: Phase 2b §9 (= BG App.C), §10-§14
- **Group ζ (Phase 2b §14 完成後)**: §15, §16 (線形チェーン)
- **Group η (Phase 2 完成後)**: Phase 3 (最終結合) → Phase 4 (FeitThompson メイン)

---

*このマップは Phase 2 形式化の伴走索引. per-section ノート (`notes/bg/sNN_*.md`, `notes/peterfalvi/sNN_*.md`) で各節の詳細展開時に随時更新する.*
