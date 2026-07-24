# FT endgame 計画 — 2026-07-07 総ざらい (レーン体制の中期方針含む)

> hub 作成 (ユーザー依頼「FT 定理の完成を見据えて必要な計画を再検討」)。
> 調査 = 6-agent workflow `wf_4d2d6126` (sorry census / opacity audit / docs / issues / velocity / frontier width)。
> 位置づけ: `ft_path_policy.md` (経路方針)・`ft_lane_reallocation_2026_06_28.md` (レーン憲章) の**上に載る中期 endgame 計画**。
> 両正本と矛盾したらこの文書を訂正する。レーン数の変遷史・Wave 構造の正本は従来どおり reallocation 文書。

## 0. TL;DR

- **現在地**: 実 sorry 87 (on-path 64 = a17/b30/c17、off-path 凍結 23)。`axiom` 宣言 0・allowlist 3 公理のみ。
  opacity はほぼ解消 — 構成子なしの真の free carrier は `TFieldModelData` 1 つ (9000/0098-item2 圏)。
  07-05 以降「scaffold 横ばい」から「実証明による実減」フェーズに移行済。
- **残構造**: 独立 workstream 幅 ≈8–9 (W1–W9)。critical path は **W2 = 9000 typeP_Galois instance tail (未着手・
  multi-consumer root gate)** が支配し、終盤は S16 T-side 直列 spine (幅 2–3 → 1) に収束する。
- **レーン体制**: **3 レーン (a/b/c) を維持。拡張はしない** (E1 条件を満たす調査確定がない限り)。
  中盤で **W2 直列化の解消 (R1)** と **3002 unsound fix の前倒し (R2)** を行い、
  終盤は **C2 (幅≤2 で 3→2)・C3 (final assembly で実質 1)** の縮小トリガーで畳む。

## 1. 現在地 (2026-07-07, main = 9cb81be4)

| 指標 | 値 | 備考 |
|---|---|---|
| 実 sorry (bin/count-sorry) | **87** | on-path 64 / off-path 凍結 23 (Pf Appendices 15 + BG AppD/E 8 — いずれも FT import closure 外、BG App は orphan leaf) |
| on-path 内訳 | a=17 / b=30 / c=17 | うち **6 本は do-not-fill** (unsound/vestigial/deprecated: S11:8302, S12:4023/4159/4419/4427, S15_Setup:2119) — 1019 redesign 等で retire 予定。実充填対象 ≈58 |
| `axiom` 宣言 | **0** | allowlist = propext / Classical.choice / Quot.sound。island 機構は空 (解散済) |
| ⚠ assert 無効化 | **1 件** | (3.9.a) `eta_pair_of_coprime` unsound carrier (issue 3002) — spine の `#assert_only_allowed_axioms` 1 本が一時 disable。**再有効化が完成条件** |
| 真の free carrier | **1** | `TFieldModelData` (S16_G0Coprime:800、(9.7) field model) — 構成子ゼロ。他の carrier は全て構成済 (残る opaque Prop field は True-carried・unread 検証済の cosmetic debt) |
| velocity (直近 14 日) | a≈22, b≈22, c≈14 merges/日 | net +82.6k 行。a/b/c は 06-28 以降 idle gap ゼロ |

**opacity 監査の結論**: プロジェクトの opacity は「構成されない free field」から
「**明示的で有限個の sorried named theorem のリスト**」への変換に成功している。doneness リスクの残りは
(i) 3002 の unsound carrier、(ii) TFieldModelData、(iii) Wave 3 の vestigial field 全数 discharge、の 3 点に局所化。

## 2. 残 frontier 構造 (幅と critical path)

独立 workstream (詳細は wf_4d2d6126 frontier-width レポート / issue 別 queue は issues-sweep):

| # | workstream | lane | 状態 |
|---|---|---|---|
| W1 | (11.8)/(9.11) coherence capstone (S12→S13) | a | 収束中 (base landed、残 = μ-pair seed→caseB→caseA 組立 + deep glue 3) — **feitThompson 唯一の bare sorry** |
| W2 | **9000 typeP_Galois instance tail** (S11 block 分解 + (11.9) char body) | a (claim) | **未着手**。multi-consumer root gate: c の型決定 chain 全体 + b の (13.12)/(13.15) + engine instantiation を一斉 unblock |
| W3 | (13.4) 残 gate 1+3 (A₀(T)-TI / θ-package) | b | gate 2 済 |
| W4 | (13.3) ← τ₁ 構成 (4.9)/(5.8) (2035/2034) | b | multi-session の deep char |
| W5 | 3002 Track A (η-grid parity + Y=0 + (13.1.d)) **+ (3.9.a) unsound fix** | b | fix が最先送り危険 (issues-sweep 指摘) |
| W6 | βₛ/Γ-bridge (13.18) → T_typeIII_ratio_le | c | de-opacify 済、tractable 2 + deep Γ-facts 5 |
| W7 | semilinear (9.7.b) field-model 新 shared leaf = TFieldModelData 構成 | c | 未着手 (0098 item2、claim 未起票) |
| W8 | eta_pair (3.9.a) finNeg↔rowInv (FeitThompson:2184) | a 領域 | standalone・完全独立 (W5 の fix と同根で解ける可能性) |
| W9 | Pf §8 producers (S10 3 本) → S14 pin 置換 + BG bookkeeping | a 領域 + b | 準機械的〜中規模 |

**critical path** (最長直列鎖、深さ ≈6–8 major obligation):
W1 → **W2** → {u_bound / caseB_order_u / c_eq_one / hVcomm 一斉 discharge} → S15 数値 tail (W3 合流) →
S16 直列 spine (T_isTypeP2 → T_typeII → T_side_caseB_facts → key_inequality (14.8)) → nonexistence_of_G →
menu 組立 (W8 含む) → feitThompson。

**幅の推移予測**: 現在 8–9 → W3 後 ~7 → **W2 後 ~4–5 (最大 fan-out 解放)** → W4+W5+W6 後 2–3 → 最後 1 (直列化)。

## 3. レーン体制の中期方針 (本計画の核心)

### 原則 (確立済・不変)

**lane 数 = ungated frontier 供給に合わせる** (2026-07-02 教訓)。コスト・token・規模は増減の判断基準にしない
(CLAUDE.md)。縮小の根拠は「idle lane は churn/busywork/衝突リスクを生む」こと、拡張の根拠は「genuine に独立な
ungated frontier が現有 lane 数を超えて存在する」ことのみ。歴史的事実: 4 レーン化は 2 回とも失敗
(char endgame は密結合 pipeline で「4 独立クラスタ」が成立しない; lane d は 2 回とも genuine 独立 frontier を
見つけられず churn 化して退役)。hot file (S15_SAndT 3-way / S15_Setup / S14 / S16) にレーンを足すと衝突が先に立つ。

### 判定: 現行 3 レーン維持、拡張なし

- 現在の幅 8–9 のうち、レーン跨ぎで独立に「深く」掘れるのは実質 3 本 (W1+W2=a 圏 / W3-W5=b 圏 / W6-W7=c 圏)。
  残りは既存レーンの queue 内の後続項目か準機械的 bookkeeping で、4 本目の deep queue を構成しない。
- **E1 (拡張の唯一条件)**: 「genuine・ungated・非衝突の独立クラスタが 4 本以上」かつ「既存 3 レーンの queue が
  全て deep」が **audit workflow で code-level に確定**した場合のみ、d 方式 (worktree + issue base 4000) で増設。
  過去 2 回の教訓により、雰囲気での増設は行わない。現時点で E1 は不成立。

### R1: W2 (9000 instance tail) の直列化解消 — 最重要の中盤介入

W2 は W1 と数学的に独立なのに lane a 内で直列化されており、これが critical path の最長極。解消 trigger:

- **trigger R1 = 次のいずれか早い方**: (i) a が 1019 の (9.11) port 組立 (μ-pair seed → caseB → caseA) を
  landing、または (ii) c が 0098 item3(A)+item4 を消化して queue が浅くなる。
- **基本線 = a が W2 へ pivot** (9000 claim は a 保持、S11/S13 文脈も a が最深)。その際 a の残 W9
  (§8 producers、準機械的) を c へ再配分して a を W2 専任化する。
- **代替 (c 枯渇が先行した場合)**: W2 の instance tail を c へ carve-out (先例 = reconciled_typePData_T 方式の
  ブロック単位所有)。deep char が c に移る点は劣後するが、W2 の未着手放置よりよい。選択は該当 tick で hub 裁定。

### R2: b の queue 先頭を 3002 (3.9.a) unsound-carrier fix に

active な unsound carrier (likely-FALSE field が S15.Hypothesis に sorried 残存 + AxiomsCheck assert disable) は
**完成条件に直結する唯一の soundness 債務**。issues-sweep でも「最も先送りが危険」と一致。b は 9017 close +
1017-G2 wiring の直後にこれを処理する (9013 gate より先)。W8 (eta_pair) と同根で同時に解ける可能性が高い。

### 縮小トリガー (終盤)

- **C1 (W2+W3 landing 後、幅 4–5)**: 3 レーン維持 (まだ 3 本の独立 deep queue が立つ)。
- **C2 (残 = S16 直列 spine + 少数 glue、幅 ≤2)**: **3→2 に縮小**。S16 spine は c (owner) が単独直列で進め、
  b の供給完了分を吸収。a または b を回収 (どちらを畳むかは残 glue の所在で hub 裁定、ユーザーに lane セッション
  停止を依頼)。idle lane を「何か探させる」形で残さない (d の教訓)。
- **C3 (Wave 3 final assembly)**: **実質 1 レーン (hub + 単一レーン)**。mp/tp/cd の vestigial field 全数
  discharge → `sectionSixteenHypothesis_of_isMinimalSimpleOdd` 実構成 → 3002 assert 再有効化 →
  `feitThompson` sorry-free + allowlist 3 公理のみの AxiomsCheck 確認。FeitThompson.lean/AxiomsCheck.lean の
  単一ファイル配線は並列化できない。
- **Post-FT (別フェーズ)**: 凍結 23 sorry (Pf App A–E / BG App D–E) + Isaacs Ch.8–10 + 3 冊網羅は自然並列幅が
  広い (per-appendix 独立) ので、そこで再拡張 (3→4+) する余地がある。FT 完成後に別途計画。

### レーン運用の実務注意 (現行のまま)

lane セッションの起動/停止はユーザー操作 (worktree + /loop 60s)。hub はトリガー成立を監視 tick で検出したら
本計画を引いて再配分/縮小を裁定し、ユーザーに lane 操作 (停止/新設) を明示依頼する。

## 4. 完成条件チェックリスト (Wave 3 到達時に全数確認)

1. `feitThompson` が sorry-free (`#print axioms` = propext, Classical.choice, Quot.sound のみ)
2. 3002 の disable 中 assert 再有効化済 (unsound carrier 解消)
3. mp/tp/cd + Section16Inputs の vestigial/True-carried field 全数 discharge or unread 検証の最終確認
4. do-not-fill 6 本の retire (1019 redesign での S12 4 本削除 + S11:8302 / S15_Setup:2119 の整理)
5. **Pf Appendices off-path 判定の math 再確認** (`ft_path_policy.md` §3 ❄): 特に 0098 item2 (field-model =
  (9.7) near-field 二分) が **App C (NearFields) を on-path に引き込む可能性** — item2 の claim 起票時に
  先に判定し、引き込むなら owner 割当 (自然候補 a) と凍結解除を行う
6. `aSets_support_slice` (BG S16_MainResults:2123) の restatement 決着 (UNDERSPECIFIED のまま証明に入らない)

## 5. Hygiene アクション (hub、通常 tick 内で漸進)

- **issue close**: 0099 (完了条件 3/3) / 9017 (BG 側完遂) — 本計画 commit と同時に実施。
  続いて 9016・7001・4003・4004 (superseded)、2022 (re-title or close+分離)、1016 (reconciled route で代替 —
  close/restate 判定)、8022 (owner 消滅 — park 判定)、9071 (d 退役で moot — branch/worktree 削除確認済)。
- **stale 記述の訂正**: 2035 tail の「prime-TI ~2-3 session gate」(9014 で解消済) など issues-sweep §4 の表に従う。
- **split backlog** (0068–0097): hot file 縮小は将来の衝突予防に効くが、lane frontier と衝突しない凍結境界での
  prefix-split に限る (従来方針)。優先 = S15_SAndT_Setup (9.3k 行) / S16_NonExistenceG (8.4k) / S14 (7.5k) /
  S07_Coherence (6.8k)。lane の活動が薄い時間帯に hub が 1 file/日程度で漸進。
- **S15 二重所有の恒久解** (9013: reconciled_typePData_T ブロックの T-side leaf 移設) — C2 縮小前に解消しておくと
  縮小後の所有が単純化する。

## 6. 見通し (時間でなく obligation 数で)

- critical path 6–8 major obligations (うち W2 = 3 項目の multi-session、W4 = multi-session)。
- on-path 実充填対象 ≈58 のうち、W2 landing で 4–5 本が連鎖 discharge、S15 数値 tail も大半が同時に閉じる —
  **sorry 数は中盤に非線形に減る**見込み (逆に言えば、それまで headline が動かなくても停滞ではない)。
- 直近 velocity (a/b 22 merges/日、実証明 burst 日で −14 sorry/日) が維持されれば、**数週間 order** の horizon。
  ただしこれは計画用の目安であり、進捗判定は従来どおり「実構成・実証明の積み上げ」で行う (CLAUDE.md)。
