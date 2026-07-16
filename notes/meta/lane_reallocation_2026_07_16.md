# 全 3 冊フェーズ レーン配分 (2026-07-16, canonical)

> **このファイルが「レーン配分 + 所有」の正本** (2026-07-16〜)。旧正本
> [`ft_lane_reallocation_2026_06_28.md`](ft_lane_reallocation_2026_06_28.md) (FT endgame 3 レーン →
> 2026-07-15 全退役) を置換する。運用原則 (ゲート無し signature contract・レーン等価・上流優先+文書順・
> claim-before-build 9000・frontier 自律・STOP 条件) は旧 note §0 と
> [`ft_path_policy.md`](ft_path_policy.md) §0 item 2–8 を**そのまま継承** (「FT 経路」→「3 冊スコープ」に読み替え)。
> 作業 scope の正本 = [`three_books_full_survey_2026_07_16.md`](three_books_full_survey_2026_07_16.md)。

---

## 0. 配分原則

- 単位 = ギャップ調査の**独立クラスタ** (数学的独立 + ファイル territory 非交差)。クラスタ間依存は
  「Isaacs Ch.8 → Pf App Suzuki」の 1 本のみで、これは同一レーン (b) 内に閉じた。
- 各レーンは自クラスタ内を**上流優先 + 文書順** (冊間 = Isaacs → BG → Peterfalvi) で進める。
- **担当 unit の特殊化債務 (`formalized_specialized`) の一般化も作業項目**。unit に着手したら missing/partial と
  併せて specialized を番号順で一般化する — docstring 注記で済ませてよいのは一般化が数学的に無意味な場合のみ
  ([[feedback-generalize-specialized-fully]]、ユーザー 2026-07-16)。
- 既存の **opaque-Prop scaffold** (Pf Appendices、BG App.D/E) は「形式化済み」と数えない — 実 statement へ
  置換してから本証明する ([[scaffold-sorry-free-not-done]])。
- effort 見積り (S/M/L/XL) は調査 note の規模感記録であり、**着手順・継続判断の基準にしない**
  ([[feedback-cost-scope-not-a-criterion]])。

## 1. レーン所有マップ (🔒 ownership)

| lane | worktree | クラスタ | 主所有 | ODD_ISSUE_BASE |
|---|---|---|---|---|
| **a** | `/home/ywr/odd-order-a` | Isaacs 本文完備化 | `OddOrder/Isaacs/**` (Ch08/Ch10 を除く)。Ch.2–6 gaps → Ch.9 (新設 `Ch09_MoreSubnormality/`) → 付録 (新設 `AppX_Basics/`) | 1000 |
| **b** | `/home/ywr/odd-order-b` | 置換群 → Suzuki チェーン | `OddOrder/Isaacs/Ch08_PermutationGroups/**` (新設) + `OddOrder/Peterfalvi/Appendices/{Suzuki,Suzuki2Groups}*.lean` | 2000 |
| **c** | `/home/ywr/odd-order-c` | Isaacs Ch.10 + BG 残 + Pf 残 | `OddOrder/Isaacs/Ch10_MoreTransfer/**` (新設) + `OddOrder/BG/**` + `OddOrder/Peterfalvi/S*.lean` (本文 partial/specialized) + `Appendices/{NearFields,Huppert,SemilinearField,FeitSibley}.lean` | 3000 |

- shared infra (`OddOrder/GroupTheory/**`, `OddOrder/Algebra/**`, `OddOrder/Mathlib/**`, root `OddOrder/*.lean`) =
  所有なし、**claim-before-build (9000 番台 issue)** 継続。hub/main = base 0。
- Pf 本文 `S*.lean` は c 所有だが、b の Suzuki 作業が §10 等の既存 statement を cite するのは通常どおり自由
  (cite は所有と無関係)。

## 2. レーン内 frontier (2026-07-16 初期値; live は git log + issues/)

- **a**: Isaacs Ch.2 (1 partial) → **Ch.3** (15 件: 3.6/3.7 crossed-hom 基礎, 3.15 Hall E 逆, 3.16 index clause,
  3.17 Wielandt, 3.18 π-separable, 3.22 Hall-Higman 帰結の完全形, 3.26 class 対応, 3.31–3.34 Hartley-Turull
  クラスタ, 3.35/3.36 cyclic extension 残り, wreath 一般形) → **Ch.4** (7 件: M(G) 定義 + 4.14/4.15/4.17/4.18/4.19
  Mann クラスタ, 4.12 括弧木一般化) → **Ch.5** (3 件) → **Ch.6** (6 件: 6.7, 6.23 系導出, 6.24 ほか) →
  **Ch.9 全域** (33 件: F\*(G) 章 — automorphism tower, Thompson–Wielandt, Bartels) → **付録 X.1–X.23**
  (mathlib 対応表化中心) + Isaacs specialized 8 件
- **b**: **Ch.8 全域** (25 件: 多重推移性・primitivity・Jordan 定理群; mathlib MulAction 資産併用) →
  **Pf App Suzuki** (32 件: Thm A → Ch.I General Properties → Ch.II First Case → Ch.III Structure of H →
  Ch.IV PSU3 特性化; 既存 `Suzuki.lean` scaffold は実 statement へ置換) → **Suzuki2Groups** (8 件: Higman 分類)
- **c**: **Ch.10 全域** (27 件) → **BG §2** (Fong-Swan 等 3 件) → **§4** (4 件) → **§6** (2 件) → **§16** (4 件)
  → **App.C** Rem (II) SL(2,2^q) 具体例 + Rem (V) wlog → **App.D** (3 件: CN 群) → **App.E** (5 件: scaffold 置換
  から) → **Pf 本文 partial** (§3×2, §4×1, §9×2, §10×1 ほか計 12 件) → **NearFields** (4 件) → **Huppert 残**
  (2 件) → **FeitSibley** (13 件) + BG/Pf specialized 46 件
- 低優先繰延 (レーン割当なし): BG App.C Rem (IV) Norton–Glauberman / Prob 1 — いずれやる (ユーザー 2026-07-16)。

結果 id ごとの内容・現状・メモ = 調査 note の per-unit 表が正本。

## 3. 再作成手順 (レーンは 2026-07-15 に全退役・worktree/branch 削除済み)

```bash
cd /home/ywr/odd-order
git worktree add /home/ywr/odd-order-a -b a   # 旧 branch は削除済みなので -b で新規
git worktree add /home/ywr/odd-order-b -b b
git worktree add /home/ywr/odd-order-c -b c
```

`.lake/packages`・`references` の symlink 共有ほか詳細 = [`worktree_setup.md`](worktree_setup.md)。
各レーンは起動プロンプトから CLAUDE.md「🔄 起動時 main 同期」→ frontier 確認 (本 note §2 + 調査 note) →
`/loop` self-pacing 自走 (wakeup 60s 固定)。hub 監視 cron は [`merge_monitor.md`](merge_monitor.md) 冒頭の
現行指定で再作成 (cron は session-only、[[cron-dies-on-model-switch]])。

## 4. 新設ディレクトリ命名 (mathlib 互換・記述的英語)

- `OddOrder/Isaacs/Ch08_PermutationGroups/` (入口 `Main.lean`、以下 topic leaves)
- `OddOrder/Isaacs/Ch09_MoreSubnormality/`
- `OddOrder/Isaacs/Ch10_MoreTransfer/`
- `OddOrder/Isaacs/AppX_Basics/`

BG/Pf の新 leaf は既存規約 (記述的英語、1500 行で分割、hub = pure re-export) に従う。

## 5. STOP 条件 (不変)

新 `axiom` / unsound carrier / signature 無断変更 / sorry regression (証明済→sorry) / build 破壊・想定外 git 状態。
それ以外 (難所・gated・コスト・規模・payoff の遠さ) は停止理由にならない (`ft_path_policy.md` §0 item 5–8、
CLAUDE.md「進捗の測り方」)。
