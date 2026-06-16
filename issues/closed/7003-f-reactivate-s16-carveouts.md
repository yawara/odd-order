---
id: 7003
slug: f-reactivate-s16-carveouts
title: "Lane F reactivate — §16 ungated carve-outs (Thm II D-subset-A + Thm A 4-conjunct bundle)"
created: 2026-06-16
---

# Lane F reactivate — §16 ungated carve-outs

## 結果 (2026-06-16, Lane F)

- ✅ **#2 `theoremA_ungated_conjuncts` DONE** (commit `72a07d93`): A(1) M_σ-Hall / **A(5) Kstar≠⊥**
  (genuine, Prop 14.2 解禁) / A(6) M_F≤M_σ / M_σ≤M' を standalone sorry-free + axiom-clean で landing。
  AxiomsCheck 登録、full build 3834 green。#3 (Kstar≠⊥) は #2 の A(5) に統合済。
- ❌ **#1 `theoremII_escaping_subset_aset` REJECT** — audit の「axiom-clean確認済」は**誤り**。
  抽出 probe を実装し `#print axioms` で実証: `[propext, sorryAx, Classical.choice, Quot.sound]`
  = **sorryAx 混入**。理由 = `D⊆M_σ#` の導出 (`hDsub`) が **sorried monolith を3つ cite**:
  `theoremB_U_and_A_tame.2.2.2.2` (B(5) TI, S16:723) / `theoremA_maximal_structure.2.2.1`
  (A(3), S16:739) / `theoremC_paired_structure` (C(9) hTIC, S16:745)。B(5)/C(9) の TI piece は
  sorried theoremB/C の conjunct で **proved standalone source が無い** (§14 Hall 構造 gated)。
  ⟹ axiom-clean な抽出は不可。audit prototype は B(5)/C(9) を**仮説に hoist**して sorry-free に
  見せた [[scaffold-sorry-free-not-done]] の罠。**§14 landing 後** (B(5)/C(9) が proved standalone
  化したら) #1 は再 actionable — それまで deferred (lane-H の typeP_duality / §14 Hall 構造待ち)。

⟹ **本 issue は resolved** (#2 landed, #1 は §14-gated と確定)。#1 再開は §14 landing がトリガー
(F の STANDBY 再開トリガーと同じ条件)。

---


## 背景

F STANDBY 判定 (@69f9435e LAUNCH.md) は **H の Thm 14.4 landing / Prop 14.2・Cor 14.3 の
sorry-free 化より前**のスナップショット。2026-06-16 の 8-agent 並列 audit (workflow
`lane-f-ungated-audit`) で **§16 に新たな ungated carve-out が 2 件**あると判明。
**Prop 14.2 (`typeP_structure`) が STANDBY 後に sorry-free 着地したことで `Kstar≠⊥` engine が解禁**
されたのが鍵。確立パターン = Thm B(1)/Thm E(3) と同じ「monolith から ungated conjunct を
standalone sorry-free lemma として cite で切り出す」。

⚠ **monolith (`theoremA_maximal_structure` 等) の署名は変更しない** — 新規 standalone lemma を
足すだけ (Thm B(1) `theoremB_U_sylow_abelian_rank_le_two` の先例)。monolith はその sorry のまま。
これで下流 caller (S16:697/724 = Thm II body が `theoremA_maximal_structure` を呼ぶ) を壊さない。

## やること (優先順)

- [ ] **#1 `theoremII_escaping_subset_aset`** (BG Thm II 中 conjunct `D ⊆ A(M)`):
  - 場所: `S16_MainResults.lean:643` の body (lines 670–712 は既に in-monolith sorry-free)。
  - cite: `theoremB_U_and_A_tame` (B(5)), `theoremC_paired_structure` (C(9) `hTIC`),
    `theoremA_maximal_structure` (A(3) K=⊥ type-F branch), `sigmaSharp_subset_hatMsigma` + `le_sup_right`。
  - 手順: `hDsub.trans hMσsharp_sub_A` (D ⊆ M_σ# ⊆ A(M)=ASet M U) を standalone lemma に抽出し、
    monolith 中段から re-cite。残 sorry (@736, @761) は触らない。
  - ~40 行 / 1 session。**最高 FT-value** (genuine extraction、Thm II spine 上)。
- [ ] **#2 `theoremA_ungated_conjuncts`** (4-conjunct A bundle: A(1) M_σ-Hall, A(5) Kstar≠⊥,
      A(6) MF≤M_σ, A(6) M_σ≤M'):
  - 場所: 新規 standalone lemma (monolith `theoremA_maximal_structure:143` は不変)。
  - cite: `S10.Msigma_isHall` (A1), `S10.Msigma_ne_bot`+`S15.isTypeP_of_isHall_kappa_subgroupOf_ne_bot`
    +`S14.typeP_structure` (A5 Kstar≠⊥ = **新解禁**), `S15.maxNilpotentNormalHall_le_Msigma` (A6 MF≤M_σ),
    `S10.Msigma_le_derived` (A6 M_σ≤M')。
  - 手順: K で case-split (K=⊥ ⇒ C(K)=⊤; K≠⊥ ⇒ IsTypeP via Prop 14.2 conjunct 2)。
    `hKM : K ≤ M` を hypothesis に追加 (`hUM` faithfulness-fix 先例)。audit の prototype は
    scratch importer で axiom-clean 確認済 ([propext, Classical.choice, Quot.sound])。
  - ~12–15 行 / 1 session。#3 (`theoremC_Kstar_ne_bot`) は同 engine ゆえ #2 の shared helper に畳む。

## やらないこと

- ❌ #4 `sigma_reps_pairwise_disjoint_forall` (Thm E(2) ∀-intro) = thin wrapper、CLAUDE.md ラッパー方針違反。
- ❌ monolith 署名変更。
- ❌ gated sorry を assumption 下で埋める (load-bearing 化する)。

## 完了条件

#1 #2 が sorry-free + axiom-clean で landing、AxiomsCheck 登録、full build green。
着地後 F は STANDBY 復帰 (残 §16 は Thm 14.7 / Cor 15.3 / 15.9 / Lem 12.17 cyclic clause に真に gated)。

## 検証フラグ (commit 前に確認, audit medium-confidence 由来)

- prototype は scratch importer 検証ゆえ、実 leaf で elaborate するか ~12s `lake build` で確認。
- standalone 方針なら monolith 署名不変ゆえ下流 caller 検査は不要 (grep 確認済: caller は S16 内 2 箇所のみ、monolith 経由)。

## 参照

- audit: workflow `lane-f-ungated-audit` (run wf_348b92fd-337, 8 agents, 2026-06-16)
- 先例: Thm B(1) `theoremB_U_sylow_abelian_rank_le_two`, Thm E(3) `sigma_reps_pairwise_disjoint`
- still-gated (STANDBY 継続部): `typeP_duality` (Thm 14.7, S14:3224) = lane-H long pole /
  Cor 15.3b (S15:1360) / Cor 15.9 (S15:2611) / Lem 12.17 cyclic clause (S12_E:73, deferred)
