---
id: 4005
slug: hub-relane-by-frontier-cluster
title: "HUB: 並列化設計の検証 + レーン再設計 (節区切り → 依存 frontier クラスタ区切り)"
created: 2026-06-22
---

# HUB: 並列化設計の検証 + レーン再設計 (節区切り → 依存 frontier クラスタ区切り)

> 宛先 = HUB (merge monitor / レーン分担設計)。発信 = lane-c (Pf §16)、ユーザー指示。
> ユーザー observation:「並列化がけっきょくうまくいかない。C レーンは投下したばかりだけど頻繁に止まる。
> これはそもそも並列化の設計のミスなのか?」→ **HUB が本 issue の診断を検証 → 各レーンを再設計せよ**。
> 前提診断 = issue 4002 (lane-c kickoff のレーン分担 feedback)。本 issue はその escalation +
> 今セッションで原文/signature/transitive-sorry レベルまで深掘りした追加証拠 + 再設計の mandate。

## 結論 (HUB が検証すべき主張)

**かなりの部分が並列化の設計問題。ただし「並列化が無理」ではなく、並列化の単位を『本の節』にしたのが
ミス。『依存 DAG の frontier の独立クラスタ』に変えれば改善する。**

## 根本原因: 直列な鎖を直列に切った

FT 証明本体は深い**直列依存チェーン** (BG §1→§16 → Pf §10→§16、最後の矛盾が §16)。これを
「§14-16=F / §13=B / §14-15=H / §16=C」と**区間で切って各区間を別レーン**にすると、並列でなく
**パイプライン**になる。下流区間 (C=§16) は上流が producer を出すまで実質ゼロ作業 → starve。
C レーンは証明の**最下流 (終点)** に置かれたので「ほぼ全部待ち」は構造上の必然。

### なぜ「signature-first で下流は cite するだけ」が効かないか

分割の建前は「下流は上流の signature を (sorry でも) cite して進む」。これが効くのは**上流が忠実な
signature を既に stated している**場合だけ。実際は carrier が under-constrained (opaque Prop /
free field / W₁=κ-Hall が未 pin) で、**cite すらできず単にブロック**される。

形式化の hard part は「独立した補題を証明すること」より**carrier / statement を忠実に設計すること**で、
これは本質的に**直列・大域的** (§16 の必要物は §13 の carrier が忠実に決まるまで忠実に書けない)。
設計の結合が鎖の全長に走る ⟹「補題は独立でも実は並列化できない」。

## 今セッション (lane-c) の追加証拠

- lane-c §16: 文書順最上流の 2 sorry を忠実 wiring で close (`caseB_for_S` 14.6 / `K_eq_V_index_pq`
  index 半 14.11、commit `aff0bc2a`、13→11 sorry)。**その直後に壁** = starvation の典型 (投下後すぐ停止)。
- 残 11 §16 sorry + 上流 S15 の 36 sorry を**全数**精査 → **全て**深い §13 char theory (13.5–13.15
  norm cascade) か carrier faithfulness (W₁=κ-Hall, issue 2009) に gated。**lane-c が到達できる範囲に
  clean な証明可能葉ゼロ**。
- 当初検討した「T/V-side dual」(issue 4004) を精査 → S-side チェーン (`typeII_overNormalizer_frobenius`)
  **自体が** carrier sorry を含み (`exists_typeI_maximal_overNormalizer_U` の `P⊓U=⊥` 1303 /
  Hall-coprimality 1352)、dual しても **sorry を増やすだけ**、しかも Dade fields が lane-b gated ゆえ
  `exists_MHypothesis` も閉じない。= clean な下流仕事に見えたものが実は non-task。
- **同じ結論の反復再発見**: lane-h が 12 セッション前に「§16 構造 frontier 出し尽くし → Lane B」と結論
  (issue 2009) → 2026-06-21 の 4-レーン再編がそれを再発見 → 今日 lane-c が三たび再発見。coordination 層が
  過去の自分の結論を学習せず毎回同じ「gated」を再導出 = 構造問題の上に乗った process の無駄。

## 何が機能して何が starve したか (placement の問題)

- **frontier 配置レーンは機能**: lane-f (BG §14-16)、lane-h (Pf §14-15) は実証明を積めた。
- **consumer 配置レーンは starve**: lane-c (§16=終点) は純 consumer ゆえ常時待ち。
- ⟹ 失敗は「並列化」でなく**レーン placement が依存構造を無視したこと**。frontier に置けば回り、
  frontier より下流に置けば starve する。

## 本当に並列幅 (fan-out) がある所

幅は**1 つの frontier 節の中の独立した補題クラスタ**にある (例: Pf §13 = norm cascade + Dade grid +
degree analysis + structural は互いに starve しない)。issue 4002 も「並列幅は Lane B の §13 内部にある」と
既に結論。**節 (= 本の目次, 直列) で切るのでなく、依存 DAG の frontier のクラスタ (並列) で切る**のが正解。

## HUB への ask (検証 + 再設計)

1. **診断を検証**: 上記の「直列チェーンを節区切りした」構造と「frontier vs consumer placement」を
   merge_monitor.md / 各レーン LAUNCH / master roadmap に照らして再確認。反証があれば本 issue に追記。
2. **レーン再設計** (節区切り → frontier クラスタ区切り):
   - **純 consumer / 終点レーンを standing lane として走らせない**。§16 (旧 C) は frontier が landing
     したとき機会的に閉じる「driver」に畳む (常駐させない)。
   - **frontier の独立クラスタにだけレーンを置く**。有用レーン数 = **今の frontier の実 fan-out 幅**
     (おそらく 2-3: BG §14-16 の structure/char + Pf §13 char の内部クラスタ) であって、鎖の区間数でない。
   - **依存 DAG の frontier クラスタで分解**する (book section でなく)。
3. **frontier 幅の監査**: 現 critical path の最深未証明 prerequisite 群を洗い出し、その中の**互いに
   starve しない独立クラスタ**を列挙 → それがレーン数と分担の上限。
4. **直列深さは並列で消えないことを明記**: FT は 3 冊の深い直列で critical path 長が wall-clock 下限。
   並列は critical path の**周りの幅**しか縮めない。残りの大半が critical path 上の深い char theory なら
   活かせる幅は元々小さい — レーンを水増ししても starve が増えるだけ。

## 完了条件

HUB が (1) 診断を検証し、(2) **frontier クラスタ区切り**に基づく新レーン割当 (レーン数・各レーンの
独立クラスタ・consumer レーンの driver 畳み込み) を merge_monitor.md + 各 LAUNCH に反映。
旧「節区切り」割当 (§14-16=F / §13=B / §14-15=H / §16=C) を frontier-cluster 割当に置換。

## 参照

- issue 4002 (lane-c kickoff: 線形 spine で下流レーンが starve する分担問題 = 本 issue の前提診断)
- issue 2009 (lane-h POLE-2: 「§16 構造 frontier 出し尽くし → Lane B」12 セッション前の同結論)
- issue 4001 / 4004 (lane-c §16 frontier + T/V-side dual ask) / `notes/peterfalvi/s16_nonexistence_gate_map.md`
- `notes/meta/merge_monitor.md` (4-レーン運用、spine = 線形チェーンの記述)
- commit `aff0bc2a` (lane-c resume の 2 closure)、master roadmap (`notes/meta/ft_master_roadmap_*.md`)
