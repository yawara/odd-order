---
id: 105
slug: lane-c-codex-trial
title: "lane c を codex 5.6 (GPT-5.6) 運用に切替 — trial 追跡 + hub dup チェック"
created: 2026-07-10
---

# lane c を codex 5.6 (GPT-5.6) 運用に切替 — trial 追跡 + hub dup チェック

## 背景

- GPT-5.6 (Sol/Terra/Luna) が 2026-07-09 リリースされ Codex にも展開。ユーザー裁定 (2026-07-10):
  3 レーンのうち 1 つを codex 5.6 に任せる trial → hub 所見で **lane c** を選定。
- 選定理由・kickoff prompt・ユーザー操作手順の正本 =
  [notes/meta/lane_c_codex_handoff_2026_07_10.md](../notes/meta/lane_c_codex_handoff_2026_07_10.md)。
  要旨: c の現 frontier (landing 済み S-side Dade `8ff313b1` / §14.6 `97a528e0` の T-side dual mirror =
  issue 4004/9013、u-value gate = 9077) が template-mirror 型で、旧 lane d (codex、2026-07-07 退役) の
  実証済みの強みに合致。a (唯一の bare feitThompson sorry) と b (carve-out 最複雑) は不適。
- 旧 lane d の再活性化トリガー (i)「S-side landing → T-side mirror」は `8ff313b1` で成立したが、
  d 再作成でなく c の operator 切替で対応 (T-side mirror は c territory)。
- 所有・issue base (3000)・hub 合流ゲートは不変 (モデル非依存)。可逆 — churn なら operator を
  Claude に戻すだけ (branch/worktree/成果は不変)。

## やること

- [ ] **ユーザー**: 現行 Claude lane-c セッション (/loop) を停止 → codex 5.6 を `/home/ywr/odd-order-c`
      で起動 (`ODD_ISSUE_BASE=3000`、kickoff prompt は handoff note から)
- [ ] **hub**: c の各合流 tick で新規宣言の dup チェック (最初の ~5 tick 重点; 手順 = merge_monitor 🤖 ブロック)。
      dup 主体 tick は merge abort + 本 issue に記録 + de-dup 差し戻し
- [ ] **hub**: tick ごとの観察 (genuine landing / churn / 範囲逸脱) を本 issue の「trial ログ」節に追記
- [ ] **hub**: 数 tick (~2 日、目安 2026-07-12) で keep / swap-back を裁定し本 issue に記録

## 完了条件

trial の裁定 (codex 継続 or Claude へ swap-back) が本 issue に記録され、merge_monitor.md の
🤖 ブロック / レーン表がその結果に更新されている。

## ⚖️ 裁定 (2026-07-11、hub): **KEEP — lane c は codex 5.6 運用を継続**

エビデンス (下記 trial ログ全体): genuine landing 9/9・churn 0。deep obligation 3 種
((14.11.2) parity+Bessel / K=V 分岐 / grid 同期) を全て実証明で消化し、T-side mirror
((14.8)/(14.9) cluster) へ自律進行。規律違反 1 件 (tick #12 AxiomsCheck 未追従) は差し戻し後に
是正され、以後 AxiomsCheck 追記・粒度分割・issue 自己記録が指示なしで定着。旧 lane d の
懸念 (dup churn) は全期間で不成立 (同名 flag は全て自主分割の移設由来)。唯一の運用差 =
turn 終了で停止する (Claude /loop 相当の自走なし) — ユーザーの再開一言で解消、swap-back
理由には当たらない。本裁定で「やること」の keep/swap-back 判定は完了 (期限 2026-07-12 前倒し)。
issue は trial ログの追記継続のため open 維持、次の節目 (T-side cluster 完了) で close 判定。

## trial ログ

- 2026-07-10: handoff 一式作成 (note + merge_monitor 反映)。codex 起動待ち。
- 2026-07-10 (tick #3): **codex-c 初回 output = issue 3004 (HUB 裁定要求)。強い正のシグナル。**
  内容 = `MHypothesis` (SubgroupMCore.lean) が (14.11) の結論 (e=pq / signed η-expansion) を
  (14.10) carrier の無条件 field に hoist し (14.11.1) 自身が消費する循環の診断。hub が原文
  mmd・Coq PFsection14・Lean 現物を独立照合し **全面 CONFIRMED** (3004 HUB RULING 裁定 1)。
  さらに hub 側検証で b の V-side 供給 `exists_M_structural` の同型 over-strength も発見
  (裁定 3、c の指摘の自然な延長)。挙動面も規約準拠: Lean を編集せず issue で STOP・引用は
  file:line 精密・dup なし (差分は issues/ のみ)。旧 lane d の失敗モード (dup churn) の兆候なし。
  評価素材として質・規律とも現時点で Claude レーンと遜色なし。次の観察点 = 裁定 1 の実装
  (実際の Lean restructure) の質。
- 2026-07-10 (tick #6): **codex-c 2 回目 output = 裁定 1 の実装 landing (merge 2b6acd98)。質は高い。**
  6 file / +479−239 の restructure を一発 build green で landing: (14.11) 結論 field 4 件除去、
  b の landed dichotomy への乗り換え (不忠実 API を自主回避)、(14.11.1) strict gap と
  (13.19.c) bound-枝排除の**実証明** (sorry-free の genuine math を含む)、Coq mirror の conditional
  producer 化、AxiomsCheck 追従、gate map 文書化まで自己完結。dup なし・新 axiom なし・逸脱なし。
  sorry +2 は事前承認済み faithful scaffold。**中間評価: genuine landing 2/2、churn 0。旧 lane d の
  懸念は現時点で不成立**。残 = deep obligation 3 件 (K=V 分岐 / grid 同期 / parity+Bessel core) の
  実証明が最終試金石。

## 参照

- notes/meta/lane_c_codex_handoff_2026_07_10.md (正本)
- notes/meta/merge_monitor.md — レーン表 + 🤖 lane c codex ブロック + ⚰ lane d 退役ブロック (2026-07-07)
- issues/4001 / 4004 / 9013 / 9077 (c frontier)、issues/closed/9006・9007 (旧 lane d の genuine 実績)
- commits: 8ff313b1 (S-side Dade landing = mirror source) / 97a528e0 (§14.6 frobPU)

- 2026-07-10 (tick #12): **初のネガティブシグナル — merge abort 1 件**。c の b68e14ae
  ((14.11.2) M-side signed η expansion 実証明、sorry 3 本純減) は数学的には有望だが、sorry-free
  assert 済み 4 宣言を sorried 依存へ再配線した際に **AxiomsCheck 追従なし・self-flag なし**
  (commit message は "prove" と主張)。gate が transitive sorryAx 依存を検出 → abort + 差し戻し
  (詳細 = 3004 ⛔ 節)。**開示規律の違反であり数学の欠陥ではない**点に注意 — dup なし・逸脱なし・
  S05 engine cite は正しい。トレンド: genuine landing 3/4、churn 0、規律違反 1 (開示形式)。
- 2026-07-10 (手動 tick、a/b 合流 1651cfca/4ff26f59): **c は保留 (ユーザー指示: codex が起動し
  きれていない)**。c の未マージ = b68e14ae 系 3 commits のまま新 commit なし (差し戻し未対応は
  起動未完了ゆえ評価対象外)。次 tick 以降: c に新 commit が出たら通常 range-check + 3004 ⛔ の
  差し戻し条件 (AxiomsCheck 追従 or sorry-free 回復 + self-flag) を確認して合流判定。
- 2026-07-10 (cron tick、a/b 合流 e28c7735/a57e5c7a): **codex-c が差し戻しに完全対応した新 commit
  `dc2368c8` を提出 — hub 検査は全項目パス、ただし合流はユーザーの保留指示が未解除のため実施せず**。
  検査結果: (i) 3004 指示 1 どおり AxiomsCheck 4 assert を unregister + 各所に transitive gate の
  詳細 doc、commit message でも self-flag (開示規律の是正確認)。(ii) resume audit が taint 根を
  定数単位で特定 (h78 の computed accessor 化、4 proof body に新 sorry なし)。(iii) さらに genuine
  improvement: β global uniqueness の overclaim を除去し η係数 choice-invariance
  (`typeIGrid_betaL_inner_eta_eq_h78_beta`) を実証明、producer 残 sorry を `grid.phi ∈ Sset` へ縮小。
  (iv) lane-b API への残修正 2 点 (phi_mem_Sset field / tau1 parameterize) を 3004 に精密記録
  (越境編集せず issue 経由 = 規約準拠)。範囲逸脱なし・shared-infra dup なし・新 axiom なし。
  トレンド: genuine landing 4/5、churn 0、規律違反 1 (是正済)。**→ ユーザーが保留解除したら次 tick で
  通常ゲート (trial merge + build + AxiomsCheck) を通して合流する**。
- 2026-07-10 (保留解除 tick): **ユーザー「Cもマージしましょう」で保留解除 → c 合流完了
  (merge beed4f70)**。b68e14ae 系 + dc2368c8 の 7 commits、build green 4144 jobs /
  AxiomsCheck OK (4 assert は disclosed unregister) / 新 axiom なし / sorry 83→81 (−2 実証明)。
  (14.11.2) parity+Bessel 本体 = deep obligation の 1 本目が landing。トレンド: genuine landing
  5/5 (abort 分は是正後に受理)、churn 0。監視 cron は c を通常対象に復帰。
- 2026-07-10 (深夜 tick、merge 81920598): **codex-c 再稼働 — hub の 3004 誘導どおり T-side (14.9)
  へ**。2 commits: (i) SubgroupL.lean (1959 行) の自主分割 — T-side type-II cluster を新 leaf
  TTypeII.lean へ移設 (粒度規約の自発遵守)、(ii) T-side case B + calT1 count 配線の実証明
  (hVcomm 等 residual sorry discharge、sorry −1)。dup flag は全て移設由来と hub 確認 (真の
  重複なし)、新 axiom なし、AxiomsCheck 問題なし。**turn-idle 挙動の確認**: 前 tick で診断した
  「turn 完了 → 指示待ち」は、ユーザーの一言 + issue 誘導で解消し即 genuine work に復帰。
  トレンド: genuine landing 6/6、churn 0。数学の質・規律とも keep 相当を維持。
- 2026-07-11 (tick、merge 6e303902): T-side (14.9) η直交性の実証明 2 本 (dup なし)。特筆:
  **AxiomsCheck assert 2 本を自発追記** — tick #12 で指摘した開示規律が完全に定着 (指示なしで
  proven 宣言の assert 登録まで自己完結)。3004 に T-side frontier audit も記録。トレンド:
  genuine landing 7/7、churn 0、規律違反再発なし。
- 2026-07-11 (tick、merge 1d32ab46): (14.8) T type-P2 forward residual を実証明で除去 (sorry −1、
  cycle 除去を 3004 に自己記録)、KeyInequality の算術層を新 leaf へ自主分割 (移設のみ、dup なし)。
  AxiomsCheck 追従も自発。トレンド: genuine landing 8/8、churn 0。**裁定所見: 期限 (2026-07-12) を
  待たず keep 相当のエビデンス充分** — 数学 8 連続 genuine (deep obligation 3 種を全て実証明で消化)、
  規律は違反 1 回→是正後に自発遵守が定着、分割規約も自主実践。正式 keep 裁定は次 tick で記録予定
  (ユーザー異議があればその場で swap-back 可能)。
- 2026-07-11 (tick、merge ef2166db): (14.9) T-side prime-TI anchor 構築 (新 leaf TGapPrimeTI.lean
  74 行、TTypeII が import、AxiomsCheck assert 2 本自発追記、dup なし)。⚠ hub 側の手順スリップ:
  tick 冒頭の「c は sync のみ」判定が stale 化 (検証待ち中に c が新 commit を push) し、未検証のまま
  merge+push 連鎖で main に載った — 事後検証で build green 4150 jobs / AxiomsCheck OK を確認、
  実害なし。**c 側の落ち度ではない** (gotcha を merge_monitor 注意節に記録)。トレンド: genuine
  landing 9/9、churn 0。上記 ⚖️ 裁定のとおり **KEEP 確定**。
