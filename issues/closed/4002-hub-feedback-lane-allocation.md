---
id: 4002
slug: hub-feedback-lane-allocation
title: "hub への feedback: 線形 spine で下流レーンが starve する分担問題"
created: 2026-06-22
---

# hub への feedback: 線形 spine で下流レーンが starve する分担問題

> 宛先 = hub (merge monitor / 分担設計)。発信 = lane-c (Pf §16)。
> 「毎回 HUB の分担がうまくいっていない」というユーザー指摘を受け、lane-c kickoff で
> 実地に観測した**構造的な失敗モード**を報告する。批判でなく、分担設計を直すための diagnosis。

## 観測した事実 (2026-06-22 lane-c kickoff)

1. **lane-c は最下流の consumer レーン**。`field_normalizer_structure` の dispatch tree は
   すでに sorry-free (lane-h 成果)。残 13 sorry を全数 audit (14 並列エージェント) + 自前検証
   した結果、**ungated に閉じられたのは 3 本のみ** (`key_inequality` / `main_size_bounds` conj3 /
   `MHypothesis_kernel_cyclic` の wiring、commit `ff2338a5`)。**残り 10 本は全部 Lane B
   (Pf §13 char/Dade、issue 1004 `section16CharacterData`) に bottom-out**。
2. これは新発見ではない: **lane-h は同じ §16/§14 領域で 12 セッション回し、issue 2009 に
   「lane-h の §13.17 / POLE-2 構造的 frontier は honestly-closable 分を出し尽くした。残りは
   全て §13 char theory = Lane B」と既に結論済み**。今回の 4-lane 再編 (§14-15=H / §16=C) は
   その結論を再発見しただけ。
3. スナップショット (本 issue 起票時): lane-b = main から **0 commits 先行**、`S15_SAndT.lean`
   (Pf §13) だけで **sorry 28 本**。つまり**全下流が待つ唯一の producer (Lane B) が thin で、
   下流レーン (H, C) は cite 先が無く idle になりがち**。

## 根本原因 (構造)

**FT spine は深い線形チェーン** (merge_monitor.md 自身の記述: 「BG §14→16 → Pf §10→16」)。

- **線形チェーンはレーン分割では並列化されない**。チェーンを区間 (§14-15, §16, …) に切って
  各区間を別レーンにすると、**下流区間は上流が producer を出すまで実質ゼロ作業**になる。
  「signature-first cut で下流は cite するだけ」という前提は、**上流が忠実な signature を
  まだ stated していない**場合に破綻する。
- 実際 §16 の obligation の多くは **citeable な上流 signature が存在しない**: carrier
  under-constraint (Hypothesis が対象を pin しない)、opaque `Prop` field
  (`betaM_expansion_formula` 等)、未 stated な述語 (S-side `caseB_for_S` 判定など)。
  ⟹ 下流レーンは「sorried を cite して実証明を積む」のではなく**単にブロック**される。
- **audit の "closable" 判定は信頼できなかった**: 結論 (conclusion) は一致しても**仮説
  (hypothesis) が合わない**ケースを楽観的に closable と誤判定 (`T_side_caseB_facts` /
  `orthogonality_switch` 等)。分担を「signature が在る」だけで割り当てると non-task を掴ませる。

## 真の並列幅はどこにあるか

並列化できる**幅 (fan-out) は Lane B の §13 char/Dade 理論の内部**にある:
`S15_SAndT.lean` の 28 sorry、(6.8) coherence、Dade grid、`section16CharacterData` (issue 1004)。
ここは互いに starve せず複数エージェントが並行できる本物の幅。**下流の thin な consumer (§14-15,
§16) を別レーンにするより、bottleneck (Lane B) の幅を割る方が並列効率が高い**。

## 提案 (hub へ、どれか / 組合せ)

1. **bottleneck に capacity を集中**: §16/§14-15 に独立レーンを立てる代わりに、**Lane B の
   §13 char 仕事を 2 レーンに割る** (例: B1 = (6.8)→§13.2-13.10 基本構造/coherence、
   B2 = Dade grid/β_M/§13.17 char endpoint)。fan-out が実在するのはここ。
2. **H + C を統合**: 両方 Pf §14-16 で両方 B 待ち ⟹ 1 レーンに統合して**セッション枠を 1 つ
   解放**し、B 補強 or 別の ungated frontier (BG §16 type-data = Lane F の `bgTheoremE`/Prop16.1
   等) に振り向ける。下流 §16 は「B 着地で driven」する小 leaf として opportunistic に回す。
3. **cite work の割当前に signature の faithfulness を検証**: 結論一致でなく**仮説まで合う**
   ことを確認してから「closable」と割り当てる (本 issue の audit 教訓)。合わなければ
   それは「下流の作業」でなく「上流に新 signature を足す ask」。
4. **線形 stretch では frontier レーンのみ productive と認める**: 上流が未達の区間に下流レーンを
   常駐させない (idle 検出時の thumbs-down ではなく**最初から立てない**)。

## ⚠ 訂正 (2026-06-22, ユーザー指摘「signature 正確なら待つ必要ないのでは」)

初稿の「lane-c は Lane B 待ちでやることが尽きた」は**過大**だった。残り 13 sorry を精査すると
3 類型に分かれ、「Lane B 待ち」と呼べるのは一部だけ:

- **① 忠実 signature が存在 (sorried) → cite 可・ブロックでない**。policy どおり cite すべき
  (kickoff の 3 本はこれ)。
- **② lane-c 自身のファイルの opaque `Prop` carrier field (`_holds` 無し)**: `betaM_expansion_formula`
  / `generic_bound_formula` / `e_eq_index` 等。cite 対象でなく**プレースホルダ**。honest な対応は
  **de-opacify** (opaque Prop を concrete な (14.11.2) η-展開等の文に置換) して証明する = **lane-c
  自身の §14 char 仕事。「Lane B 待ち」ではない**。
- **③ 未 authored な文** (T/V-side type-II analog、S-side caseB 判定、U/V cyclic): cite 先が無いが
  **hard-block でない** — lane-c が obligation として author 可 (`V_cyclic` でやった)。author+cite が
  vacuous (obligation == 全内容) なときだけ無意味。

⟹ **真の cross-lane 依存は narrow** (§13 `basic_structure` レベル、これは citeable)。大半は
**lane-c 自身の §14 Dade char (opaque Props の de-opacify + (14.11) β_M norm 計算 + V-side Dade 構成)**
で、これは hard だが lane-c がやれる/やるべき。⟹ 分担問題の本質は「C が受動的に block」でなく、
**§13-14 char/構造が 1 つの連結した hard chunk なのに lane-split (§13=B / §14-15=H / §16=C) が
それを横断分割していること**。fan-out を割るなら char-theory chunk を機能 (Dade 構成 / norm 計算 /
型判定) で割る方が、§ 区間で割るより starve しない。

## 参照

- `notes/meta/merge_monitor.md` (4-lane 運用、spine = 線形チェーンの記述)
- issue 2009 (lane-h POLE-2 12 セッション、「§16 構造 frontier 出し尽くし → Lane B」結論)
- issue 1004 (Lane B `section16CharacterData` = 下流が待つ producer)
- issue 4001 + `notes/peterfalvi/s16_nonexistence_gate_map.md` (lane-c §16 gate map)
- commit `ff2338a5` (lane-c kickoff: 3 clean win)

## ✅ CLOSE (2026-07-02 hub 全体レビュー)

提案は歴代 re-org (4 フロント → 2026-06-28 再配分 → 2026-07-02 3 レーン a/b/c) に吸収済。
現 canonical = notes/meta/ft_lane_reallocation_2026_06_28.md (検証 2026-07-02)。
