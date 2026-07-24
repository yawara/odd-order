# 9501 — HUB 裁定: lane c の next frontier (Q₈ 凍結 + lint 完了後)

**発行**: hub, 2026-07-23 20:2x tick / **band**: 9500 (hub) / **対象**: lane c

## 経緯

lane c は (1) 割当 lint (0146/0133) 完了、(2) ユーザー裁定で Q₈ Brauer–Suzuki を凍結
(issue 0147 / 9318 closed) を経て、20:0x 以降 **3 tick idle** (ahead=0・worktree clean・
9400 frontier-request 未提出)。memory lane-c-frontier は「territory 完済境界・次は hub 裁定」
と記す。hub が実測で c territory を精査し裁定する。

## 実測 (2026-07-23 20:2x, hub)

**c 割当 territory (`OddOrder/BG/**` + `Peterfalvi/Appendices/{NearFields,Huppert,SemilinearField,FeitSibley}`) の残 sorry = 全て gated**:

| file:sorry | 内容 | gate |
|---|---|---|
| `Appendices/RankOneAffineModel.lean` :1 | Prop 1 の Q₈ BS | **凍結** (Q₈, issue 0147) |
| `Appendices/Suzuki/FirstCase/StepFive.lean` :1 | step (2)(b) | issue 9318 (Q₈ 凍結) + Higman `pow_four_eq_one_of_isSuzuki2Group` (**issue 2053 = b active**) |
| `Appendices/Suzuki/FirstCase/StepSix.lean` :1 | odd-order aut group | 9318 (凍結) + `F_{9,2}` aut theory |
| `Appendices/Suzuki2Groups.lean` :4 | `higman_classification` / `typeB_field_model` / `typeB_automorphism_structure` / `square_map_quadratic` | **b の active Higman Lemma 13** (`OddOrder/Higman/**`) |

- **issue 3017 (BG Thm 6.2 literal J(S) 一般形) = CLOSED** (`issues/closed/3017`)。memory L87「未」は stale (L39「close 済」が正)。→ frontier 候補でない。
- ⟹ **c の assigned territory に「非凍結・非 b-gated」の ungated frontier は無い**。

## 裁定

CLAUDE.md「自レーン最上流 sorry が他レーンに gated でも、さらに上流の ungated な genuine
math (未所有 shared infra を含む) に降りて実証明する」に従う。c の gated sorry の上流 =
**b の Higman Lemma 13**。ただし b が同 file cluster (`OddOrder/Higman/Suzuki2Groups/**`) を
高速で active に触っており、二重作業・merge 衝突リスクが高い。

**c への指示** (c は次 sync で本 issue を読むこと):

1. **Q₈/modular は凍結 (issue 0147) — 着手しない**。
2. **新 ungated scope を取る** (「3 冊全部形式化」フェーズゆえ残作業は豊富)。survey
   (`notes/meta/three_books_full_survey_2026_07_16.md`) に多数の「未」rows があるが
   **survey は stale — 必ず実測 (comment-strip sorry census + repo grep) で genuine-missing を
   確認**してから claim ([[verify-port-state-by-number-not-coq-name]])。doc-order-earliest
   (上流優先+文書順) から選ぶ。frontier の具体選択は c の自律判断 (聞きに来ない)。
3. **b の active Higman file cluster (`OddOrder/Higman/**`) は避ける** (衝突防止)。c の Pf Suzuki
   appendix sorry を閉じたいなら Higman 上流が要るが、それは b が進めている — c は b の完了を
   待つ側とし、その間は別の ungated 結果を進める。
4. shared infra / 未所有 leaf は **claim-before-build** (着手前に検索 → 9400 band で claim →
   open 9xxx scan)。territorial なのは所有 file のみゆえ未所有 leaf 新設は consumer が他レーンでも in-scope。
5. 真に「実測しても ungated frontier が全く無い」なら 9400 band で hub に再エスカレーション
   (report≠停止・AskUserQuestion 不可)。

## status
open (c の次 action 待ち)。c が新 frontier に着手 or 9400 再エスカレーションしたら本 issue を
closed/ へ。

## 2026-07-24 CLOSE (ユーザー裁定で superseded)

ユーザー裁定 2026-07-24: 「レーンに分配せずに、いったんこのハブで b → a → c のタスクを閉じる」。
本 issue の実測表も stale 化した (StepFive の sorry は Higman Thm 1(a) 合流 `859ce48bf` で閉鎖、
実 sorry 7→6→2)。hub セッションが直接実施した内容:

- Suzuki2Groups.lean の空 scaffold 4 本削除 (`3adbd2df8`、0127 ② 実施) — 「b の Higman 待ち」gate は消滅
- StepSix `card_D_le_three_of_noncomm` は Aut(Q₈) bound + near-field units ≅ Q₈ を hub が整備して閉鎖予定
- RankOneAffineModel の凍結 sorry は |S|≥16 assembly を実証明し Q₈ 単離 statement へ縮小予定

⟹ c への「新 ungated scope を取れ」指示は本 issue としては役目を終えた。c の次 frontier は
hub の次回 tick で改めて裁定する (Q₈ 凍結 = issue 0147 は不変)。
