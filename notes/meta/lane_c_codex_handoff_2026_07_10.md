# lane c → codex 5.6 (GPT-5.6) handoff — 2026-07-10

> ユーザー裁定 (2026-07-10): 3 レーンのうち **lane c** の operator を Claude から **codex 5.6** に切替えて trial する。
> 追跡 issue = [issues/0105](../../issues/0105-lane-c-codex-trial.md)。所有・issue base (3000)・hub 合流ゲートは**不変**
> (合流チェックはモデル非依存: build green / AxiomsCheck / sorry regression / 範囲逸脱)。

## なぜ c か (hub 所見の要約)

1. **現 frontier が template-mirror 型**: landing 済み S-side (Pf §8.16/§10.7 type-II Dade base = `8ff313b1`、§14.6
   `frobenius_PU_of_u_full` = `97a528e0`) の **T-side dual mirror** (issue 4004 / 9013) + u-value gate (issue 9077)。
   旧 lane d (codex 運用、2026-07-07 退役) の実績で codex は「Coq/既存テンプレートの忠実 mirror・sorry-free な
   群論 API の additive 生産」に強く、frontier が薄いときに dup churn へ流れた。今の c は前者の仕事が主。
   旧 lane d の再活性化トリガー (i)「S-side landing → T-side mirror」は `8ff313b1` で成立したが、d 再作成でなく
   **c の operator 切替**で対応する (T-side mirror は c territory ゆえ)。
2. **a は不可**: feitThompson を gate する唯一の bare sorry (S12 11.8) + `FeitThompson.lean` 所有 = 最重要経路。
3. **b は不可**: carve-out が最も入り組む (a 所有ファイルへの条件付き編集権多数) → 新ハーネスが範囲逸脱を
   起こしやすい。c の territory 境界が最も明快。
4. **可逆**: レーンは等価・交換可能。churn なら operator を Claude に戻すだけ (branch/worktree/成果は不変)。

## ユーザー操作手順

1. **現行の Claude lane-c セッション (/loop) を停止する** (odd-order-c で自走しているもの)。
   ⚠ 停止前に codex を起動しない — 2 エージェントが branch `c` に同時 commit すると衝突する。
2. codex 5.6 を起動:
   ```bash
   cd /home/ywr/odd-order-c
   export ODD_ISSUE_BASE=3000
   codex   # モデルは Sol (flagship) + 高 reasoning effort 推奨 — 本プロジェクトはコスト非基準
   ```
3. 下の kickoff prompt を貼る (AGENTS.md → CLAUDE.md symlink は main / odd-order-c 両方に設置済み・確認済み)。

## kickoff prompt (codex にそのまま貼る)

```
あなたは Feit–Thompson 定理 Lean 4 形式化プロジェクト (odd-order) の **lane c** を担当する。
作業ディレクトリ = /home/ywr/odd-order-c (git worktree, branch `c`)。commit は branch `c` にのみ積む
(main への合流は hub が行う。main へ直接 commit / push しない)。

## 最初に読むもの (この順)
1. AGENTS.md (= CLAUDE.md) — プロジェクト規約の正本
2. notes/meta/merge_monitor.md — レーン所有マップ (🔒) と合流手順・carve-out 境界
3. notes/meta/ft_lane_reallocation_2026_06_28.md + notes/meta/ft_path_policy.md §0 — レーン配分と作業順序
4. issues/4001 / 4004 / 9013 / 9077 — lane c の現 frontier

## 起動時 (毎セッション必須)
- `git merge main` (3-way; `--ff-only` 禁止) → `git rev-list --count HEAD..main` が 0 を確認。
  長いセッションは「次の leaf 着手前」「commit 前」にも再同期。
- `export ODD_ISSUE_BASE=3000` (issue 採番レンジ)
- `lake update` 禁止。build は `lake build OddOrder` (開発中は leaf build で回し、full build は commit 前)

## 所有 (これ以外の Peterfalvi/BG S-ファイルは編集禁止 = import cite のみ; 変更要望は issues/notes 経由)
- `OddOrder/Peterfalvi/S16_NonExistenceG.lean` (全体)
- carve-out (正確な境界は merge_monitor 🔒 マップが正本): S15_SAndT_Setup の reconciled_typePData_T
  T-side ブロック / S15_SAndT の BetaData 領域 (:3616 付近) と (13.18) S-side A0-rewire ブロック /
  S05_GridRigidity + S05_Grid* 系 + S16_GridExpansion / S15_HonestTypeP2A0.lean /
  S13_PrimeTIResidueBridge の Hypothesis.residueS 周辺
- 共有 (additive のみ): `OddOrder/{GroupTheory,Mathlib,Algebra,Isaacs}/**`, `AxiomsCheck.lean`,
  `OddOrder.lean`, `notes/**`, `issues/**`
- 新規 shared leaf は claim-before-build: 着手前に open 9000 番台 issue を scan → 自分も 9000 番台で claim

## 現在の frontier (上流優先 + 教科書文書順で自律選択、hub/ユーザーに聞かない)
- landing 済み S-side (Pf §8.16/§10.7 type-II Dade base = commit 8ff313b1、§14.6 frobenius_PU_of_u_full =
  97a528e0) の **T-side dual** を mirror する (issue 4004 の T/V-side duals、9013 の T-side (13.15))
- s_side gate は u-value 1 本 (issue 9077 参照)
- 教科書の行間は `coq/theories/PFsection{8,14,16}.v` のコメントを併読 (Coq は参照専用、直訳ソースでない)

## 規律
- 進捗 = 本物の証明の積み上げ (sorry 数でない)。既存補題の複製・checklist 更新等の busywork 禁止。
  **新補題を書く前に必ず既存 API を grep** (S01/GroupTheory に既にある事実の再証明が過去の失敗モード;
  dup は hub が合流を差し戻す)
- STOP (halt + issue 報告): 新規 `axiom` 宣言 / unsound な carrier・signature 無断変更 /
  sorry regression (証明済→sorry)。それ以外 (難所・コスト・gated) は停止理由にならない
- 難所は回避せず正面から。真に blocked なら 9000 番台 HUB issue を立てて次の frontier へ移る (停止しない)
- commit は feature/subsection 粒度で build-green を維持。1 ファイル 2000 行超は分割 (目安 300–1500 行)
```

## hub 側の追加監視 (正本 = merge_monitor.md 🤖 ブロック)

- c の合流 tick で**新規宣言の dup チェック** (最初の ~5 tick 重点):
  `git diff main...c -- '*.lean' | grep -E '^\+\s*(theorem|lemma|def) '` で新規宣言名を抽出し、
  同内容の既存宣言が無いか spot-grep。**dup 主体の tick は merge せず abort** + issue 0105 に記録 +
  notes/issue で c に de-dup (cite 置換) を差し戻す (これは STOP でなく通常継続)。
- 評価: 数 tick (~2 日) で genuine landing (実証明・実構成) が出ているかを issue 0105 に記録し、
  keep / swap-back を hub が裁定。評価軸は sorry 数でない。
