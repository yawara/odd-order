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
  「Isaacs Ch.8 → Pf App Suzuki」の 1 本のみ。⚠ 当初は同一レーン (b) 内に閉じていたが、**2026-07-19 に Ch.8 が a へ返還されたため現在は a → b のレーン間依存**。
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
| **a** | `/home/ywr/odd-order-a` | Isaacs 完全仕上げ + Peterfalvi 本文 | `OddOrder/Isaacs/**` (**2026-07-19 裁定 9154 で Ch08/Ch10 込みの全域**) + **`OddOrder/Peterfalvi/S*.lean` (Pf 本文全域、同 9154 で c から移管)**。⚠ 旧記載の frontier (Ch.2–6 gaps → Ch.9 → 付録) は**消化済** — `Ch09_MoreSubnormality/` は 2026-07-17 に新設され 18 leaf が存在 | 1000 |
| **b** | `/home/ywr/odd-order-b` | Suzuki チェーン (Ch.8 は 2026-07-19 に a へ返還) | `OddOrder/Peterfalvi/Appendices/{Suzuki,Suzuki2Groups}*.lean` | 2000 |
| **c** | `/home/ywr/odd-order-c` | BG 残 + Pf Appendices の非 Suzuki 系 (Ch.10 は 2026-07-19 に a へ返還) | `OddOrder/BG/**` + `Appendices/{NearFields,Huppert,SemilinearField,FeitSibley}.lean`。⚠ **Pf 本文 `OddOrder/Peterfalvi/S*.lean` は 2026-07-19 裁定 9154 で a へ移管** (9158 で一時 c へ暫定移管したが a 復帰により失効) | 3000 |

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

## 3. 再作成手順 (⚠ **2026-07-19 現在 a/b/c は稼働中** — 下記は将来また全退役したときの手順)

2026-07-15 の全退役後、**2026-07-16〜17 に 3 レーンとも再作成済み**。branch `a`/`b`/`c` と
worktree `/home/ywr/odd-order-{a,b,c}` は現存するので、**下記をそのまま実行すると `-b` が
「branch は既に存在する」で失敗する**。現況確認は `git worktree list` が正。

```bash
# 全退役状態からの新規作成時のみ (branch が存在しないことを git branch で確認してから)
cd /home/ywr/odd-order
git worktree add /home/ywr/odd-order-a -b a
git worktree add /home/ywr/odd-order-b -b b
git worktree add /home/ywr/odd-order-c -b c
```

`.lake/packages`・`references` の symlink 共有ほか詳細 = [`worktree_setup.md`](worktree_setup.md)。
各レーンは起動プロンプトから CLAUDE.md「🔄 起動時 main 同期」→ frontier 確認 (本 note §2 + 調査 note) →
`/loop` self-pacing 自走 (wakeup 60s 固定)。hub 監視 cron は [`merge_monitor.md`](merge_monitor.md) 冒頭の
現行指定で再作成 (cron は session-only、[[cron-dies-on-model-switch]])。

## 4. ディレクトリ命名 (mathlib 互換・記述的英語) — ⚠ 下 3 つは 2026-07-17 に**作成済**

- `OddOrder/Isaacs/Ch08_PermutationGroups/` (入口 `Main.lean`、以下 topic leaves) — **既存 14 leaf**
- `OddOrder/Isaacs/Ch09_MoreSubnormality/` — **既存 18 leaf**
- `OddOrder/Isaacs/Ch10_MoreTransfer/` — **既存 6 leaf**
- ~~`OddOrder/Isaacs/AppX_Basics/`~~ — **作られていない**。Isaacs 付録の作業は既存の
  `OddOrder/Isaacs/Appendix/` (`DirectDiamond.lean` / `SubgroupBasics.lean`) に landing しており、
  新ディレクトリを切る予定は無い

BG/Pf の新 leaf は既存規約 (記述的英語、1500 行で分割、hub = pure re-export) に従う。

## 5. STOP 条件 (不変)

新 `axiom` / unsound carrier / signature 無断変更 / sorry regression (証明済→sorry) / build 破壊・想定外 git 状態。
それ以外 (難所・gated・コスト・規模・payoff の遠さ) は停止理由にならない (`ft_path_policy.md` §0 item 5–8、
CLAUDE.md「進捗の測り方」)。
