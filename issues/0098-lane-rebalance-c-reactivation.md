---
id: 98
slug: lane-rebalance-c-reactivation
title: "HUB 裁定: レーン役割再点検 — c REACTIVATE (5件パッケージ) + b de-scope、a/9000 は不変"
created: 2026-07-07
---

# HUB 裁定: レーン役割再点検 — c REACTIVATE (5件パッケージ) + b de-scope、a/9000 は不変

## 背景

ユーザー提起 (2026-07-07): 「各レーンの役割を再考した方がいいかな。b は良さそうだけど、a が重くて、c がやることなくなってるかな」。
hub が 4 並列 subagent (wf_d4994964) で a queue / b queue / c gate-map / 9000 実現性を code-level 調査して裁定。

**判断軸はレーン等価原則のみ** ([[lanes-are-equivalent-no-specialty]]): レーンに適性・専門は無い。
配分 = (i) 仕事が genuine・最上流か、(ii) ファイル/territory 非衝突か、(iii) セッションが空いているか、の 3 点。
(「c は 9072 を landing したから σ-theory に適性」のような過去実績→適性の推論は**使わない** — ユーザー再訂正 2026-07-07)。

## 調査確定事実 (2026-07-07 時点)

- **a**: 1019 (Pf 11.8 redesign) は収束中 (update⁴⁰ で capstone 経路確定) だが単線 S13 grind。
  **9000 の残り = instance tail (S11 §9 block-decomposition Hbar=⊕H1^w + S13 (11.9) typeP_Galois char body)
  は未着手だが a の territory 内**で、a の issue 1017 計画 (updates #5/#6) が S11 既存 caseB 機構
  (chiefFactor_caseB_*, uActionHom) から expose する設計。他レーン並行構築は 2026-07-02 dup 事故の predicate-level 再演。
  generic σ-theory engine (SingerField/SingerLineBound/SemilinearImprimitiveBound/LineScalarCharacter/TypePGaloisUBound)
  は**既に sorry-free** (旧 lane d 構築、凍結)。
- **b**: 9017 Keystone A-C 完了・velocity 高いが、**~9 クラスタ / 29 frontier sorry を保有**し、
  **c の残 11 sorry 中 7 の gate** (9013 d=1・mᵀ・v-value / 3002 parity・signs / reconciled 残 2 field)。
  overload 継続 (merge_monitor 2026-07-06 flag は正確)。
- **c**: 満 11 sorry 全て S16_NonExistenceG.lean、gate は文書化済み。(14.9) coherence 側は horth discharge (9072 closed)
  で完了。ただし **ungated genuine work 5 件が存在** (下記パッケージ)。うち S-side βₛ bridge は
  **ownership gap** (9013 enumerate 外・3002 外・未 claim; c 自身が 255148aa で「9013 の scope 外なら別途 tracking 要」
  と flag)。放置すると :1658 → T_typeIII_ratio_le → T_isTypeP2 → T_typeII (S16 消費 6+ 箇所) の隠れ long-pole。

## 裁定

### a — 変更なし
- 1019 capstone grind 継続 (単線証明ゆえ worker 追加は無効)。
- **9000 claim は a 保持** (instance tail S11/S13 は a territory + 1017 計画と一体)。full 再配分は棄却。
- S14_MaximalI の §12 pin 11 本 (b ファイル内) は a の §8/§9 producer landing で cite 置換される
  bookkeeping — b の負荷計算から除外してよい (b の実 queue は見た目より軽い方向の補正)。

### b — active 変更なし + de-scope 2 件
- active = BG Cor 15.9 (S15_MF:11061) 継続。9013 案A の本体 ((ii) cofactor v∣Singer,
  (iii) (13.10)-dual analytic ineq) + d=1 (V_inf_centralizer_Q_eq_bot, S15_SAndT.lean:1885) + 3002 Track A は b 保持
  (estimate-generalization は b、instantiation のみ c — 案B 再演の dup hazard 回避)。
- **de-scope①**: 9013 item (i) **T-side mᵀ 定義 + 7/10<mᵀ 算術 bound → c**。c 検証済みで純算術・
  c 所有 engine file (S16_CaseBOrder) に plug — **b のファイル編集ゼロ**の純 de-scoping。
- **de-scope② (carve-out)**: **S-side βₛ bridge (Pf 13.18, Coq FTtypeP_bridge_facts PFsection13.v:1784-1792) → c**。
  Lean home = b 所有 S15_SAndT.lean:3616 (`BetaData := sorry`) の **decl 領域限定 carve-out**
  (reconciled_typePData_T carve-out の前例に同じ)。S-side Dade 基盤 (dadeHypS, S15_SAndT_Setup.lean:819) は
  genuine 済み。b は cite 側に回る。b の queue では 12 番目 = 全クラスタの後ろだったので serialization 解消効果大。
- ⚠ BG S16_MainResults `aSets_support_slice` (:2123) は **UNDERSPECIFIED — restatement が証明に先行**
  (どのレーンも as-is で証明しない)。restatement は b (Cor 15.9 後) or hub。

### c — REACTIVATE (DORMANT cite-sink 解除)。パッケージ 5 件 (上流優先+文書順)
1. **typeP_pair port** (Pf/Coq §8: FTtypeP_pair_witness/of_typeP_pair/typeP_cent_compl) — **新 shared leaf**
   (`OddOrder/GroupTheory/**`、claim-before-build: 着手時に 9000 番台 claim 起票)。
   → c 自身の carve-out 内 sorry `W2_le` (S15_SAndT_Setup.lean:4520) / `centralizer_W1` (:4590) を discharge。
   9013 追記³ の file-topology 分岐 (downstream 移設 vs upstream hoist) は **hoist-upstream でこれにより解消**。
2. **generic semilinear (9.7.b) field-model package** — 新 shared leaf
   (例 `OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean`; SingerField の
   exists_galoisField_repr を拡張、F_{q^p}⋊V* 実現 interface)。claim-before-build。
   → c 自身の FieldNormalizerData (S16_NonExistenceGCore.lean:620) / TFieldModelData (S16_G0Coprime.lean:800) に給電。
3. **S-side βₛ bridge (13.18)** — 上記 carve-out (S15_SAndT.lean:3616 BetaData 領域)。Γ = τ_S(β_#1) − 1 + η_01 の
   構成 + ⟨Γ,1⟩=0 + norm/parity facts。
4. **§14 Γ-bridge assembly (nzT1_Ga)** — c 自ファイル S16_NonExistenceG.lean (Coq PFsection14.v:772-836)。
   named carrier 相手に**今**先行構築し、b landing 後の直列 latency を消す (sorry :1658 の c-share:
   hdecomp/hΓ₁/hx)。9072 の coherence landing で buildable になった新規領域。
5. **hcard2 (S16:1606) verify-then-prove** — |V| odd + p∣|V|−1 (T/Q Frobenius, [T:T']=p landed) ⟹ 2p∣|V|−1 ⟹
   (|V|−1)/p ≥ 2。docstring の「b-gated」ラベルは crude ≥2 bound には過剰の可能性 — **検証が先、成立時のみ** relabel+証明。

### 共有 leaf の interface guard (dup/分岐予防、必須)
- shared leaf は **module-level generic のみ** (side-specific predicate 禁止) — a の S12/S13 capstone と c の S16 が
  **同一 formulation を両側 instantiate** する形に保つ。
- S11 dedup で確立した **thin singerAdapter パターンを再利用** ([Module (ZMod p) (Additive K)] binder 文脈)。
  inline fork 禁止。
- **claim-before-build** (CLAUDE.md (C)): 着手前に既存 grep → 9000 番台 claim → open 9000 scan。

## パッケージ進捗サマリ (2026-07-07 lane c, item 1 landing 後)

- **item 1 (typeP_pair port / 9073)** — ✅ **完了** (commit `32581410`, issue 9073 closed)。
  `reconciled_typePData_T` 完全 sorry-free + axiom-clean (`#print axioms` = 標準 3 公理のみ、sorryAx 無し)。
  route (a): S の型-P 構造 → partner (typeP_duality) → Fact A (W₁ κ-Hall of S) + Fact B (M_σ(S)⊓C(W₁)=W₂)
  → partner Fact B → q∈σ(T) で W₁≤M_σ(T) + fix-W transport で cardinality equality。(14.9)/IsTypeP2 T 非依存。
- **item 5 (hcard2)** — ✅ 完了 (commit `bf3b21f4`)。
- **item 3 (S-side βₛ bridge 13.18 / `betaData_of_grid` S15_SAndT.lean:3613)** — 未着手。**次の優先**
  (upstream-first: item 4 の上流 + 文書順 §13<§14)。deep §13/§3 char 構成 (β_j/Γ_j を Dade grid τ₃ から
  構築 + 6 norm/orthogonality facts)。既存 producer の mirror でなく from-scratch ⟹ multi-session、fresh context 推奨。
- **item 4 (§14 Γ-bridge nzT1_Ga assembly)** — 未着手。`T_typeIII_ratio_le` (S16:1641) は Γ-Bessel skeleton
  還元済だが item 1(v=|V| lane-b) + item 3 coherence + S-side Γ bridge に multi-gated。item 3 の後。
- **item 2 (generic semilinear (9.7.b) field-model 新 shared leaf)** — 未着手。独立 infra、claim-before-build。

## 完了条件

- [x] c が package item ≥1 に着手 — **item 1 (9073) + item 5 (hcard2) 完了** (2026-07-07)
- [ ] 9013 に de-scope①/②を反映 (本 issue から転記) — 済 (追記参照)
- [ ] merge_monitor.md レーン表の c 行を REACTIVATE に更新 — 済
- [ ] b/c の次回 main sync で本裁定が伝播 (レーンは open issue を scan)

## ✅ item 5 完了 (2026-07-07 lane c, commit `bf3b21f4`) — hcard2 は ungated と確定

hub の「b-gated ラベルは crude ≥2 bound には過剰の可能性 — 検証優先」仮説は **正しかった**。
`T_typeIII_ratio_le` の `hcard2 : 2 ≤ calT1_set.ncard` を **9013 非依存で discharge**:

- 新 sorry-free lemma `T_typeIII_two_p_add_one_le_card_V : 2*p+1 ≤ |V|` — 内在の `U ⋊ W₁` Frobenius
  (`T_typeIII_UW1_frobenius`、odd kernel `|U|=|V|` + odd complement `|W₁|=p`) に odd-order Frobenius
  size 条件 `IsFrobeniusGroup.two_mul_card_complement_add_one_le_card_kernel` を適用。
- `hcard2` = `calT1_set.ncard=(|V|−1)/p` (`hcount_V`) + `2≤(|V|−1)/p ⟺ 2p≤|V|−1` (`Nat.le_div_iff_mul_le`)
  → `omega`。**lane-b の `|V|`-lower-bound (v-value 13.15) は exact count にのみ必要で、crude ≥2 には不要**。

S16 tactic sorry 11→10。`T_typeIII_ratio_le` の残 sorry は **S-side βₛ Γ-bridge 1本のみ** (item 4 / 9013)。
⟹ 9013 の「hcard2 は 9013-gated」記述は **訂正済** (hcard2 は 9013 非依存)。leaf build green (3903)、新 axiom 無し。

**次**: item 4 (§14 Γ-bridge nzT1_Ga assembly、自ファイル、9072 coherence で buildable) → item 1/2 (新
shared leaf、claim-before-build) の順で継続予定。

## 参照

- 調査 = workflow wf_d4994964 (4 agent: lane-a / lane-b / lane-c-gates / 9000-feasibility)、2026-07-07
- issues/9000 (σ-theory 土台、a 保持 + scope 注記)、issues/9013 (de-scope 反映)、issues/3002 (b 保持)、
  issues/closed/9072 (c の horth discharge)、issues/1019 (a capstone)、issues/9017 (b Keystone)
- notes/meta/merge_monitor.md レーン表 + [[lanes-are-equivalent-no-specialty]]

## 🔬 item 1 gating 解決 (2026-07-07 lane c, loop) — docstring の「IsTypeP2 等価」は過度に悲観的、port は doable

item 1 着手前検証。`W2_le` (S15_SAndT_Setup:4520) / `centralizer_W1` (:4590) の docstring は両者を
「typeP_pair reconciliation ≡ IsTypeP2 hyp.T」に gated と記すが、**Coq 実体で反証**:

- **`FTtypeP_pair_witness` (PFsection8.v:713)** は `MtypeP` (type-P) のみを context に取り、`FTtypeP_pair_cases`
  /`typeP_pairW`/`typeP_cent_compl`/`of_typeP_compl_conj` で **任意の type-P M に partner T の
  `typeP_pair M T defW` + `of_typeP T V xdefW` を構成** — **type-II/type-P2 非依存**。
- **`typeP_cent_compl` (PFsection8.v:229): `C_M'(W1) = W2`** も `MtypeP` のみ (centralizer_W1 の直接の内容)。
- ⟹ **0098 の「item 1 doable」が正しい**。docstring の悲観 (「IsTypeP2 等価」) は、抽象 `hyp.W1/W2` を
  type-P κ-Hall 構造に同定する reconciliation を「carrier 無しでは不能」と誤読したもの。実際は canonical
  maximal-pair (hyp.S/hyp.T, W=W₁×W₂) から `typeP_pair` 構造が port で従う。

**port scope (新 shared leaf, claim-before-build)**: PFsection8 の typeP_pair 理論
(`typeP_pair`/`typeP_pairW`/`FTtypeP_pair_cases`/`FTtypeP_pair_witness`/`of_typeP_pair`/`typeP_cent_compl`
/`of_typeP_compl_conj`) を `OddOrder/GroupTheory/**` へ port し、hyp.S/hyp.T の pair 構造から
W2_le/centralizer_W1 を discharge。substantial (multi-session)。**次 loop iteration で 9000 番台 claim 起票 → leaf 構築**。
