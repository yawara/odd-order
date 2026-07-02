# BG: Local Analysis for the Odd Order Theorem — overview

**スコープ**: Bender & Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994).
原典: `references/bg/local-analysis.mmd` (5771 行、本全体が 1 ファイル).
形式化先 (予定): `OddOrder/BG/Ch{1-4}_*/S{NN}_*.lean` + `AppA-E_*.lean`.
ROADMAP 上の位置: **Phase 2a** (Phase 1 Isaacs 完了後着手、Phase 2b Peterfalvi と並行可).

## 現状 (2026-05-27 更新)

**Phase 1 Isaacs は Ch.1–7 完成** (全章 sorry-free, 168 flagship が AxiomsCheck で axiom-clean; **Thm 7.6 `normal_J` = BG Thm 6.2** + **Ch.6 Frobenius 全面** + Hall-Higman/Hall-C/Schur-Zassenhaus 等 BG 前提ゲートは全充足)。**BG §1/§2/§3 は実装完了・sorry-free・OddOrder root 配線済** (S03 は Isaacs Ch.6 を直接利用して sorry-free; S02 は 2026-05-27 に rc2 移行漏れを修復して配線)。共有モジュールは `OddOrder/GroupTheory/` に多数実装済 (下記 audit が予定した Wave 1a 群はほぼ実現: ChiefFactor/FrattiniPGroup/OmegaSubgroup/OpResidual/PRank/SCN/IsExtraspecial/IsMetacyclic/ThompsonSubgroup/ElementaryAbelian/SemiDihedral + RepresentationTheory 一式)。**§4 以降が次フロンティア** (§4/§5 p-group 構造は infra 完備で独立着手可、§6+App.A は FT スパイン)。Peterfalvi §1–§6 も並行着手済。toolchain は v4.30.0-rc2。

**追記 — BG cluster FROZEN-COMPLETE (2026-07-02)**: §1–§16 + App.A–C の spine 完了。残 15 sorry
= AppD_CNGroups 3 / AppE_FurtherResults 5 / S14_TypePCounting 2 / S15_MF 2 / S16_MainResults 3 の
off-spine のみ (memory [[ft-settled-findings]]; feitThompson spine は Prop 16.1 のみ消費で
sorry-free)。

以下 TL;DR 以降は **2026-05-22 作成時点**の調査内容。着手順 (§ "Phase 2a 着手順") の "Phase 1 完了後" 前提は上記で更新済 (Phase 1 は実質完了)。

## TL;DR

BG は Feit-Thompson 定理の **局所解析パート** を Gorenstein 1968 _Finite Groups_ ベースで再構築した本. 全 16 節 + 5 appendix で **本文 138 個の番号付き結果** (Theorem/Lemma/Corollary/Proposition). 構造は:

- **Ch.1 Preliminary (§1-§6)**: solvable group, Frobenius action, p-group rank, narrow p-group, additional results — **Isaacs Ch.1, 3, 4, 6, 7 の前提を BG 流に再構築** (62 結果).
- **Ch.2 Uniqueness (§7-§9)**: 一意性定理. **`Z(J(S))·O_{p'}(G) ⊴ G`** (= BG Thm 6.2 = Isaacs Thm 7.6) を 7+ 箇所で引用 (10 結果).
- **Ch.3 Maximal Subgroups (§10-§13)**: M_α, M_σ, 例外 maximal, 部分群 E, prime action (32 結果).
- **Ch.4 Family of Maximal (§14-§16)**: type 𝒫 counting, M_F, **Main Results** (17 結果).
- **Appendices**: A p-stability (Isaacs Ch.7 再述), B Puig L(S), **C Peterfalvi 1984 paper 改訂** (= Peterfalvi §9 と並行), D CN-Groups (Suzuki 1957 短縮), E Further Results (17 結果).

**FT クリティカル経路**: §1-§5 → **§6 Thm 6.2 normal-J** → §7-§9 Uniqueness → §10-§13 Maximal → §14-§16 Main Results → App.C 最終矛盾. App.A (p-Stability) は §6-§16 全体に暗黙の前提.

**mathlib カバレッジ**: §1-§2 は **mid** (solvable / Hall / 表現論基本は既存, A-invariant Hall theory が新規), §3-§16 は **low** (Frobenius / J(P) / p-stability / 局所解析独自概念は新規 100%). **App.A "p-Stability" が Isaacs Ch.7 完成と直結 = Phase 2a 開始の境界条件**.

## 章節一覧

行範囲は mmd ベース. **結果数** は `^\*\*?(Theorem|Lemma|Corollary|Proposition) [0-9A-Z]+\.[0-9A-Z]+` の grep 値. **mathlib** は high (既存 API), mid (一部 + 新規), low (新規 100%). **FT** は ☆ (FT 経路必須), ◯ (標準), △ (補助).

| § | Ch | 行範囲 | 題名 | 結果数 | mathlib | FT | Isaacs 依存 | 一言 |
|---|----|---------|---------------------------------|--------|---------|-----|-------------|------|
| 1 | I  | 310-585  | Elementary Properties of Solvable Groups | 22 | mid | ◯ | Ch.1, Ch.3, Ch.4 | A-invariant Hall + p-length + solvable basic. **Prop 1.5-1.6** が Peterfalvi で多数引用. |
| 2 | I  | 586-794  | General Results on Representations | 6 | mid | △ | Ch.6 軽 | Operator group の表現、Fong-Swan 系。本文の使用箇所は§9周辺 1-2 箇所のみ. |
| 3 | I  | 795-1358 | Actions of Frobenius Groups | 10 | low | ☆ | **Ch.6 全面** | Frobenius kernel nilpotent + 表現論的 Frobenius action. Isaacs Ch.6 を BG 流再展開. |
| 4 | I  | 1359-1788 | p-Groups of Small Rank | 10 | low | ☆ | Ch.4 | Rank ≤ 2 p-group 構造定理 (Blackburn). 新規実装. |
| 5 | I  | 1789-1968 | Narrow p-Groups | 7 | low | ☆ | Ch.4 | Narrow p-group 族, Sylow 形状制限. |
| 6 | I  | 1969-2128 | Additional Results | 7 | low | ☆ | Ch.5, Ch.7 | **Thm 6.4 / 6.7 / Lem 6.5-6.6**. solvable + p-length 1 + Frobenius factorization. **§7-§16 で多用される道具袋**. (mmd 内 `### 6` ヘッダ無し、`**6. Additional Results**` の inline marker のみ L1957/1969 — 抽出注意) |
| 7 | II | 2131-2314 | The Transitivity Theorem | 3 | low | ☆ | Ch.7 (J(P)) | Hypothesis 7.1 (最小反例 G の最大 q-subgroup への作用). G を本書で fix する節 (L2133). |
| 8 | II | 2315-2485 | The Fitting Subgroup of a Maximal Subgroup | 1 | low | ☆ | **Ch.7 Thm 7.6** 多用 | maximal subgroup の Fitting 構造定理. Thm 6.2 を 5+ 箇所で引用. |
| 9 | II | 2486-2630 | The Uniqueness Theorem | 6 | low | ☆ | **Ch.7 Thm 7.6** 多用 | central structure + maximal subgroup 一意性. Phase 2a 中盤の山場. |
| 10 | III | 2637-2912 | The Subgroups M_α and M_σ | 6 | low | ☆ | §9 → §10 | maximal subgroup の族の定義・性質. |
| 11 | III | 2913-3022 | Exceptional Maximal Subgroups | 4 | low | ◯ | §10 | 例外 maximal subgroup 分類. |
| 12 | III | 3023-3483 | The Subgroup E | 15 | low | ☆ | §10-§11, **Ch.7** | 大規模. 部分群 E の構造と共役性. 15 結果は §12 が小章相当. |
| 13 | III | 3484-3739 | Prime Action | 7 | low | ☆ | §12 | derived series, Thompson 風作用. |
| 14 | IV | 3744-4085 | Maximal Subgroups of Type 𝒫 and Counting | 7 | low | ☆ | §10-§13 統合 | counting argument; type-𝒫 構造. |
| 15 | IV | 4086-4255 | The Subgroup M_F | 9 | low | ◯ | §14 | Fitting 関連 maximal. |
| 16 | IV | 4256-4449 | The Main Results | 1 | low | ☆ | §1-§15 全統合 | Theorem (B) ≡ FT 局所部. 本文 1 結果だが章全体は前章の結論まとめ. App.C / Peterfalvi へ橋渡し. |
| A | App | 4450-4516 | Prerequisites and p-Stability | 5 | low | ☆ | **Ch.7 全面** | Thm A.1-A.5. **A.4(b) ≡ Isaacs Thm 7.6 odd-order 版**. §6 Thm 6.2 の証明前提. |
| B | App | 4517-4758 | The Puig Subgroup L(S) | 3 | low | △ | App.A | J(S) の代替 Puig 不変部分群. App.A の補強. **本文では App.B 自身が独立証明枝**, 形式化は App.A 後に. |
| C | App | 4759-5005 | The Final Contradiction | 3 | low | ☆ | (Peterfalvi §9 並行) | Peterfalvi 1984 paper 改訂 (Carlip & Wheeler 編). **Theorem C** + Lemma C.1, C.2. mmd 内 L4763 `## Appendix D The Main Theorem` は Nougat 抽出誤りで実際は App.C 本文 (Theorem C の主張). |
| D | App | 5006-5073 | Cn-Groups of Odd Order | 2 | low | △ | (Suzuki 1957) | Feit-Hall-Thompson 1960 短縮ルート. FT 本筋外だが歴史的価値. |
| E | App | 5074-5446 | Further Results of Feit and Thompson | 5 | low | △ | (Phase 4 へ) | 発展結果. Phase 2a 完了後の発展材料、または Phase 4 メイン結合時に. |

**合計**: 138 結果 (本文 121 + Appendix 17, top-level Theorem/Lemma/Corollary/Proposition の数). **mathlib カバレッジは Ch.1 (§1-§6) で mid 寄り** だが Ch.2 以降 (§7-§16 + App) は **low 寄り** = 新規実装が大半.

## FT クリティカル経路

最小反例 G が存在すると仮定したとき (L2133 で G を fix):

```
Isaacs Phase 1 完成
       ↓
[Ch.1 Preliminary]
  §1 Solvable / Hall ──┐
  §2 Repr.            ├─→ §3 Frobenius ─→ §6 Additional ─┐
  §4 Small rank ───┐  │                                   │
  §5 Narrow ──────┴──┴────────────────────────────────────┤
                                                          ↓
                                            [App.A p-Stability]
                                                          ↓
                                    ★ §6 Thm 6.2 normal-J (= Isaacs 7.6)
                                                          ↓
                              ─────────────────────────────────────
[Ch.2 Uniqueness]
  §7 Transitivity ─→ §8 Fitting of Max ─→ §9 Uniqueness
                                                          ↓
[Ch.3 Maximal Subgroups]
  §10 M_α/M_σ ─→ §11 Exceptional ─┬─→ §12 E ─┐
                                  └─→ §13 Prime Action ─┘
                                                          ↓
[Ch.4 Family of Maximal]
  §14 Type 𝒫 counting ─→ §15 M_F ─→ ★ §16 Main Results (= Theorem B)
                                                          ↓
                                            [App.C Final Contradiction]
                                            (Peterfalvi §9 と統合)
                                                          ↓
                                                   FT 矛盾完了
```

App.A は §6-§16 全体の前提として **§6 開始と同時に必要**. App.B Puig は App.A の代替/補強で **§6 完了後の発展**. App.C は **Phase 2b Peterfalvi §9 と統合** で扱う (重複部分が大半).

## Phase 2a 着手順の提案

### 第 1 波 (Phase 1 Isaacs 完了直後、並列可)
- **§1** (Elementary Properties): solvable / Hall / Prop 1.5-1.6 — Isaacs Ch.1+Ch.3 と mathlib `Solvable`/`SchurZassenhaus` を組み合わせ
- **§4** (p-Groups Small Rank): rank ≤ 2 p-群構造定理. Isaacs Ch.4 §4D (Cor 3.28 → Thm 4.36) 完成必須 *(2026-05-23 audit 訂正: 「軽前提」ではなく hard gate; 詳細 [`notes/meta/bg_phase2a_wave1_audit_2026_05_23.md`](../meta/bg_phase2a_wave1_audit_2026_05_23.md))*
- **§5** (Narrow p-Groups): §4 とほぼ独立 *(2026-05-23 audit 訂正: 実は §4 を 6 results cite, 完全独立ではない. Lem 5.1-Cor 5.4 のみ §4 partial 並行可, Thm 5.5-5.7 は §4 完成依存)*
- **§2** (Representations): 表現論. §3 + App.A の前提 *(2026-05-23 audit 訂正: 「§9 1-2 cite」は誤り, 実測 §3×5 + §4 + §15 + App.A = 8+ cites; Lem 2.3 のみ defer, Thm 2.5/2.6 は FT 中核; **Isaacs Ch.6 §6F Clifford 完成依存**)*
- ~~**App.B** (Puig L(S)): App.A 不要で独立着手可 (L(S) 定義自体は J(S) と並行)~~ **App.B は Phase 2a スキップ推奨** *(2026-05-23 audit 訂正: B.3+B.4 が Thm A.5 cite で App.A 不要は誤り; さらに App.B 自身が FT-orphan = §1-§16 + App.C + App.E + Peterfalvi 全て 0 cite, 唯一の本文使用は App.D parenthetical のみ. A.5 + App.B 共に skip で ~570 行 / ~10-13 日節約)*

### 第 2 波 (§1, §4 完了後)
- **§3** (Frobenius Actions): Isaacs Ch.6 完成必須. mathlib `FrobeniusGroup` 新規実装 (Phase 1 Ch.6 で完成想定)
- **§6** (Additional Results): §1+§3 完了後. Thm 6.4, 6.7 + Lem 6.5, 6.6 (solvable + p-length 1)
- **App.A** (p-Stability): Isaacs Ch.7 Thm 7.6 完成必須. **§6 の直前 (上流)** *(2026-05-23 audit 訂正: App.A は §6 の上流, 並行ではない. BG 序文 L4452「Theorems 6.1 and 6.2 ... by use of p-stability」. さらに **BG §1 Prop 1.8/1.15(b) + BG §2 Thm 2.6 完成必須** 追加. shared module `OpResidual.lean` ~150-250 行が必須前提)*

### 第 3 波 (Ch.1 完了後 = Phase 2a 中盤)
- **§7** (Transitivity Theorem) → **§8** (Fitting of Max) → **§9** (Uniqueness Theorem). 線形チェーン. Thm 6.2 を §8 で 5+ 回, §9 で 4+ 回引用.

### 第 4 波 (§9 完了後)
- **§10** (M_α/M_σ) → **§11** (Exceptional) → **§12** (E) ∥ **§13** (Prime Action). §12-§13 並列可だが §10-§11 後.

### 第 5 波 (§13 完了後)
- **§14** (Type 𝒫 counting) → **§15** (M_F) → **§16** (Main Results). 線形チェーン.

### 第 6 波 (Phase 2a 終盤、Phase 2b 同期)
- **App.C** (Final Contradiction): **Peterfalvi §9 と統合** で扱う. 重複部分が大半なので Phase 2b § 9 完成時に同時形式化.
- **App.D** (CN-Groups): 独立、Phase 2a 完了後の発展.
- **App.E** (Further Results): Phase 4 メイン結合時または独立発展.

## App.C と Peterfalvi §9 の関係

**App.C "The Final Contradiction" (L4759-5005)** は以下のとおり:

- **歴史**: FT 1963 原論文 Ch.VI (17 ページ generator-relation argument) を **Peterfalvi 1984 paper [22]** が大幅簡略化. BG はその Peterfalvi 論文を Walter Carlip & Wayne W. Wheeler が U. Chicago Junior Group Theory Seminar 用に再編した解説 [2] を採録.
- **構造**: L4763 `## Appendix D The Main Theorem` (Nougat 抽出ミス、実は App.C 本文の続き) で **Theorem C** (`p ≤ q for F_{p^q} Frobenius family`) を主結果として述べる. その下に Lemma C.1, C.2 など補題群.
- **本プロジェクトでの扱い**: Peterfalvi 本体 §9 (Non-existence of a Certain Type of Group, 04.9_*.mmd, 162 行) と論理的に **同じ証明**. **Phase 2b 着手時は Peterfalvi §9 を一次にし、BG App.C は二次資料として読み替え** で扱う. ただし notation や前提に微差があるかは §9 着手時の精査要.
- **Phase 3 メリット**: Peterfalvi §9 だけ形式化すれば App.C は要らないが、両者の対応関係を明示するセクション docstring を `OddOrder.BG.AppC` に置く価値あり (BG ↔ Peterfalvi 統合視点).

## mathlib カバレッジ

| 領域 | カバレッジ | 必要実装 |
|------|-----------|----------|
| Solvable, Sylow, IsNilpotent, derived/upper/lower series | **high** | 既存 `Mathlib/GroupTheory/{Solvable,Sylow,Nilpotent}.lean` |
| Fitting subgroup F(G) | **low** | Phase 1 Ch.2 で実装予定 |
| A-invariant Hall theory | **mid** | mathlib に basic Hall (3.13-3.14) はある、coprime action 下の A-invariant 版は新規 |
| p-Groups rank, Ω₁(P), mingens | **mid** | basic は OK、Blackburn rank ≤ 2 は新規 |
| Frobenius groups (定義, kernel nilpotent) | **low** | Phase 1 Ch.6 で新規実装. `IsFrobeniusGroup G K R` |
| Thompson J(P), p-stability, ZJ | **low** | Phase 1 Ch.7 で新規実装. **Isaacs Thm 7.6 完成 = Phase 2a の前提条件** |
| Transfer, Focal subgroup, Burnside p-comp | **high** | 既存 `Mathlib/GroupTheory/{Transfer,Focal}.lean` |
| 表現論基本 (Representation, Maschke, FDRep, induced) | **high** | 既存 `Mathlib/RepresentationTheory/*` |
| Character theory (orthogonality, restriction) | **mid** | 既存 `Mathlib/RepresentationTheory/Character.lean`; Peterfalvi 流の virtual character 環構造は要拡張 |
| Coprime action stabilizer / centralizer 系 | **mid** | basic OK、Hall-Higman 1.2.3 (Isaacs 3.21) は新規 |
| Peterfalvi App.C "Theorem C" (finite field F_{p^q} + Frobenius family) | **low** | mathlib に基本 finite field API はあるが、Theorem C の statement 自体は新規 |
| BG App.D CN-groups (Suzuki 1957 系) | **low** | 完全新規. ただし Phase 2a 必須ではない |

## ROADMAP リンク

- Phase 2a チェックリスト: [ROADMAP.md#phase-2a--bender-glauberman](../../ROADMAP.md)
- Phase 1 Isaacs 各章ノート (本書節 → Isaacs 章の対応): [`notes/isaacs/ch01_sylow.md`](../isaacs/ch01_sylow.md) – [`notes/isaacs/ch10_more_transfer.md`](../isaacs/ch10_more_transfer.md)
- 3 冊間クロス参照マップ: [`notes/meta/phase2_cross_refs.md`](../meta/phase2_cross_refs.md)
- Peterfalvi overview: [`notes/peterfalvi/_overview.md`](../peterfalvi/_overview.md)

## 未解決事項 / TODO

- BG §6 と §7 の境目周辺 (L2128-2131) に **MISSING_PAGE_EMPTY:67** あり. p.67 の本文 1 ページが mmd 欠落. PDF (`references/bg/local-analysis.pdf` p.67) を直接参照する必要 — §6 末尾 or §7 冒頭でかしぼうしいるか不明.
- mmd 内 §6 ヘッダが `## 6` 不在で `**6. Additional Results**` の inline marker のみ (L1957 + L1969). Nougat 抽出時に章番号の認識ミス. 形式化時には PDF 確認 + section docstring に明記要.
- App.C 内 mmd L4763 `## Appendix D The Main Theorem` は実は App.C 本文の続き (Theorem C statement). 「Theorem C」が `Appendix D` の見出しになっているのは Nougat 誤認.
- BG → Peterfalvi 引用 (BG が Peterfalvi 論文を [22] として参照する以外、本文 grep でほぼ無し). Phase 2b §3-§8 で出る指標論結果は BG 自体は使わない方針.
- BG App.E の中身詳細 (5 結果) — 内容調査は per-section ノート時に.

---

*作成: 2026-05-22. 出典: `references/bg/local-analysis.mmd` (5771 行). Phase 1 Isaacs ノート (Ch.1-10) のクロス参照確認済. ノートは `notes/bg/sNN_*.md` per-section investigation で詳細化していく.*
