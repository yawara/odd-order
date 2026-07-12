---
id: 1025
slug: pf-11-5-noncoherence-thread-spine
title: "Pf (11.5)/(11.6) chain を (11.3) 非coherence で hypothesis 化 → spine residual axiom-clean"
created: 2026-07-12
---

# Pf (11.5)/(11.6) chain を (11.3) 非coherence で hypothesis 化 → spine residual axiom-clean

## 背景 (2026-07-12 lane-a 再開時、1024 完遂後の frontier トレースで確定)

FT spine (`feitThompson`) の**唯一の bare sorry** = `card_kappaHall_lt_of_isTypeIIIorIV`
(AxiomsCheck:7150)。その residual = **`exists_zeta_residual_not_orthogonal_H0C_of_refuter`**
(S13_Orthogonality:1010、Pf (11.8) refuter core)。

`#print axioms` トレースで判明した residual の dirty root は **(10.8) import-DAG knot のみ**:

- `secondDerived_eq_HC` (11.5、S13_Lemmas113To115:908) が dirty。root =
  `HC_le_secondDerived` (11.5 reverse) → `coherent_quotient_bound` (11.4) →
  `S_H0C_not_coherent` (11.3) → **`S12.S_not_coherent` (10.8、S12_MaximalBasic:1386、
  do-not-fill generic partner 経由で sorried)**。
- ⚠ **honest heir は既に存在**: `S12.S_not_coherent_unconditional` (S12_Noncoherence、axiom-clean)。
  だが **S12_Noncoherence は S13_Lemmas113To115 を import (downstream)** ゆえ、上流の
  `coherent_quotient_bound` は cite 不可 (cycle)。= 純粋な import-DAG 由来 sorry (issue 1020 圏)。
- residual の他の入力は **CLEAN**: `coherent_SOf_HC` (§14 Sibley S(HC) coherence) /
  `coherent_SOf_H0C_of_glued` (world-bridge engine) 双方 axiom-clean。

∴ **(10.8) knot を解けば residual が axiom-clean → `card_kappaHall_lt_of_isTypeIIIorIV`
(spine 唯一 bare sorry) が閉じる**。

## 鍵: spine は既に clean な (11.3) を供給している

`exists_zeta_residual_not_orthogonal_H0C_of_refuter` は **`hrefute` パラメータ**
(= (11.3) 非coherence `∀ s13hyp, ¬ Nonempty (IsCoherent … (SOf H0C) …)`) を既に取る。
spine consumer `w2_lt_w1_of_hypothesis_H0C_unconditional` (S13_TypeDetermination:62) は
`hrefute := S_H0C_not_coherent_unconditional` (**axiom-clean**) を供給。

だが residual は内部で `secondDerived_eq_HC` (line 1068) と
`coherent_SOf_H0C_of_column_identities` (line 1087) を使い、これらが `hrefute` を経由せず
sorried `S_H0C_not_coherent` に落ちている。⟹ **内部 chain を hrefute 経由に付け替えれば clean**。

## やること (additive・非破壊・proof 複製なし、import bottom-up)

各 theorem X を `X_of_noncoherent (hnc : ¬ Nonempty (IsCoherent … (SOf H0C) …)) := [本体、
内部 (11.3)-cite を hnc に置換]` に factor し、legacy 版 `X := X_of_noncoherent
(S_H0C_not_coherent _hG hyp)` を wrapper で残す。既存 consumer は wrapper を呼ぶので**無変更**。

**S13_Lemmas113To115** (最上流):
- [ ] `coherent_quotient_bound` (11.4) — 内部 `S_H0C_not_coherent` (line 191、hBncoh) を hnc に
- [ ] `HC_le_secondDerived` (11.5r) — `coherent_quotient_bound` cite を `_of_noncoherent hnc` に
- [ ] `secondDerived_eq_HC` (11.5) — `le_antisymm _ (HC_le_secondDerived_of_noncoherent hnc)`

**S13_CoreStructure**:
- [ ] `H0_eq_Hprime` (11.6) — `secondDerived_eq_HC` cite (line 936) を `_of_noncoherent hnc` に
- [ ] `chief_H0_eq_bot` (11.7) — `H0_eq_Hprime` cite (line 1163) を
- [ ] `chief_N_eq_bot` — `chief_H0_eq_bot` cite (line 1212) を
- [ ] `C_eq_cSub` — `chief_N_eq_bot` cite (line 1234) を
- [ ] `columnSum_muColumnChar_mem_sOf_H0C` — `C_eq_cSub` cite (line 1424) を

**S13_Orthogonality** (downstream):
- [ ] `coherent_sOf_H0C` — caseA branch の `columnSum…`/`C_eq_cSub` を
- [ ] `coherent_SOf_H0C_of_column_identities` — 内部 `coherent_sOf_H0C` を
- [ ] `exists_zeta_residual_not_orthogonal_H0C_of_refuter` — line 1068 (`secondDerived_eq_HC`) +
      line 1087 (`coherent_SOf_H0C_of_column_identities`) を `_of_noncoherent … (hrefute s13hyp)` に

## 完了条件

- 各 file build green。最終 `#print axioms exists_zeta_residual_not_orthogonal_H0C_of_refuter`
  が sorryAx-free (propext/Classical.choice/Quot.sound のみ)。
- `card_kappaHall_lt_of_isTypeIIIorIV` / spine を再 assert (AxiomsCheck 登録)。
- ⚠ feitThompson が完全 axiom-clean になるとは限らない (§14/§15/§16 cross-lane の推移 sorry が
  別途残る可能性)。本 issue は **lane-A の spine 貢献 (= 11.5/11.6 chain の 10.8-knot) を閉じる**。

## 参照

- issue 1020 (partner/unconditional 移行)、1024 (typeP_Galois W2)、9083 (9.11 Phase E)
- `S12.S_not_coherent_unconditional` (S12_Noncoherence)、`S_H0C_not_coherent_unconditional`
  (S13_TypeDetermination)、`w2_lt_w1_of_hypothesis_H0C_unconditional`

## ⚠ 第2 artifact 判明 (2026-07-12 実装中): `isTypeIIIorIV` (10.10)

10.8 chain を全 threading (commit e63ad5a6、build green) してもなお
`exists_zeta_residual_..._of_refuter` は `#print axioms` で dirty。原因 = **第2の独立 legacy
artifact**: `coherent_quotient_bound` が内部で `hyp.base.isTypeIIIorIV hG`
(S13_SixTwoBridge:75) を使用、これが `no_typeV_maximal` (10.10、legacy sorried) 経由で dirty
(honest heir = `no_typeV_maximal_unconditional`、S12_Noncoherence 下流、同じ import-DAG 構造)。

⟹ spine bare sorry は **少なくとも 2 つの独立 legacy artifact (10.8 + 10.10)** で dirty。
`isTypeIIIorIV` は chain 全体が coherent_quotient_bound 経由で透過 hit するため、10.8 と同型の
**htype (IsTypeIII∨IsTypeIV) threading pass** が chain ~20 theorem に追加で必要
(optParam `htype := hyp.base.isTypeIIIorIV hG`、exists_zeta_residual は既に htype 保持ゆえ clean 供給可)。
さらに第3 artifact の可能性も未排除 (htype pass 後に再 probe で確認)。

**scope 改訂**: 当初「~15-25 theorem 1 pass」見積り → 実際は **artifact 数 × chain pass** の
compounding。10.8 pass 完了 (green)。10.10 pass + 追加 artifact 探索が残 (bookkeeping、honest heir 存在)。

## ⚠⚠ 第3の判明 = 方式そのものが欠陥 (optParam 汚染) — rework 要 (2026-07-12)

10.8 (commit e63ad5a6) + 10.10 (commit 435b057a) を全 threading (S11×3 + S13_CoreStructure +
S13_Orthogonality、~50 theorem、build green) してもなお `exists_zeta_residual` は
`#print axioms` で **DIRTY**。全 named cite を probe しても clean なのに theorem が dirty という
矛盾を最小例で解明:

**optParam の dirty default `(hnc : … := S_H0C_not_coherent hG hyp)` /
`(htype : … := hyp.base.isTypeIIIorIV hG)` は、call site で override しても theorem の
`#print axioms` に default の sorryAx を焼き込む** (検証: `def fooOpt (x:=dd):=x` が dd の sorryAx を
継承; memory [[lean-optparam-default-contaminates-axioms]])。⟹ S11/caseB/S13_Orthogonality を
optParam で threading した全 theorem は default 汚染ゆえ、いくら clean な hnc/htype を渡しても
clean にならない。

### 正しい方式 = explicit param + legacy wrapper のみ (aec0d595 の hnc 方式)

- `X_of_noncoherent (hnc) (htype) := [本体、cite を hnc/htype に]` を **explicit param (default 無し)** で作る。
- 元の名前 `X := X_of_noncoherent … (S_H0C_not_coherent …) (isTypeIIIorIV …)` を **wrapper** にして
  dirty legacy 値を供給。wrapper が dirty、_of_noncoherent は free param ゆえ clean。既存 consumer は
  wrapper (元名) を呼ぶので非破壊。
- aec0d595 の (11.4)-(11.7) hnc parametrize は**この正しい方式**ゆえ _of_noncoherent は clean。

### rework の範囲 (~16 theorem を optParam → explicit+wrapper へ変換)

S11 (nineElevenPairBound / caseA_two_summand / caseA_nineElevenThree / caseA_nineElevenTwo_tiWitness /
nineElevenEqualityRefutation_of_sTwoExtraction_normBound / nineElevenSevenEightRefutation /
nineElevenNormBound_of_sevenEightRefutation / nineElevenEqualityRefutation_of_sevenEightRefutation) +
caseB (columnSum_Cprime / caseB_forall / caseB_coherent_sOf_H0Cprime / caseB_coherent_sOf_H0C) +
S13_Orthogonality (coherent_sOf_H0C / pin×2 / coherent_SOf_H0C_of_column_identities) を rename+wrapper 化 +
S13_Lemmas/S13_CoreStructure の htype を optParam→explicit 化 (wrapper が dirty htype 供給)。
param LOGIC (どの sub-call か) は 435b057a で正しくマップ済 (rework 時に再利用可)。

### scope の総括 (ユーザー判断材料)

spine bare sorry 閉包 = **多 artifact (10.8/10.10/…) × chain**、かつ **explicit+wrapper でしか
clean 化できない** (optParam 不可)。当初「~15-25 theorem 1 pass」→ 実際は全 bookkeeping で
数十 theorem の rename+wrapper。honest math (unconditional 10.8/10.10 heir) は既存ゆえ、これは
**import-DAG re-wire の bookkeeping** (新規数学の積み上げでない)。⟹ 継続価値の再判断を推奨。

## 注記

- hnc の型 = `¬ Nonempty (IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)`
  (= `S_H0C_not_coherent _hG hyp` / `hrefute s13hyp` 双方の型)。
- legacy wrapper が sorried のまま残るのは意図どおり (他の legacy consumer 用)。spine path のみ clean 化。
- CLAUDE.md「sorry-free 化の着地を目的にしない」に留意しつつ: 本件は **honest math (unconditional 10.8)
  が存在するのに import-DAG で spine が cite できず bare sorry が残る**状況の解消 = spine の honest 化。

## ⚠⚠⚠ 第4 判明 = 本 issue の前提が誤り、bookkeeping plan は不十分 (2026-07-12 lane-a STEP-0 再トレース, `#print axioms` 実測)

再開時 STEP-0 で **`#print axioms` を実測**したところ、本 issue の 2 つの核心前提がいずれも FALSE と判明:

1. **前提「`S_H0C_not_coherent_unconditional` は already axiom-clean」= FALSE**。実測: **DIRTY (sorryAx)**。
   dirty root = `coherent_S_of_coherent_SH0C` (6.3, `S13_Lemmas113To115:35`) が body 内で **直接** `hyp.base.isTypeIIIorIV _hG` (legacy 10.10、`:132`/`:134`) を cite。これは (10.10) artifact ゆえ heir `no_typeV_maximal_unconditional` (CLEAN 実測) で置換可能 = fixable bookkeeping。
2. **前提「aec0d595 の `_of_noncoherent` は explicit param ゆえ clean」= FALSE**。実測: `coherent_quotient_bound_of_noncoherent` 他 **全て DIRTY**。原因 = aec0d595 は `hnc` を explicit 化したが 435b057a が **`htype` を optParam dirty default `:= hyp.base.isTypeIIIorIV _hG` で追加** (`:171`)。→ optParam 汚染 (第3判明どおり)。fixable。

**だが決定的なのは第3の dirty source (heir 無し、bookkeeping 不可)**:

- residual `exists_zeta_residual_not_orthogonal_H0C_of_refuter` は body で **無条件に**
  `coherent_SOf_H0C_of_column_identities` (`:1100`) を呼び、これが **無条件に**
  `coherent_sOf_H0C hG hyp hncH0C htype` (`S13_Orthogonality:917`) を呼ぶ。
- `coherent_sOf_H0C` は `rcases clifford_dichotomy … with hA | hB` で **両 branch とも** (9.11) coherence を要し、
  両 branch とも DIRTY: caseA = `caseA_coherent_sOf_H0Cprime_of_refuter` → `Ptype_core_coherence`
  → `cohereOfSibleyTarget (sibleyTarget_H0C chars)`; caseB = `caseB_coherent_sOf_H0C` → 同 (9.11) S(H0C') coherence。
- 終端 = **`sibleyTarget_H0C := sorry`** (`S11_MaximalII_III_IV/Coherence911.lean:48`)。これは
  **term-level `noncomputable def … := sorry`** (override すべき param 無し) かつ
  **「⚠ UNSOUND (6.8)-shortcut, do NOT fill」** (7001 audit 2026-07-07: nilpotent-Hall kernel HC の H^# は非-TI ゆえ SibleyTarget は偽)。
  honest route = **Coq `PFsection9.v:1484` の 8-step induction を port** (`coherent_H0C_commutator`) =「次の lane-a work」= **未着手の genuine 数学**。

∴ **spine `card_kappaHall_lt_of_isTypeIIIorIV` の dirty source は独立に 3 つ**:
(A) (10.8) legacy `S12.S_not_coherent` [heir `S_not_coherent_unconditional` CLEAN → fixable],
(B) (10.10) legacy `no_typeV_maximal` [heir `no_typeV_maximal_unconditional` CLEAN → fixable],
(C) **(9.11) `sibleyTarget_H0C` [heir 無し・do-not-fill unsound・honest route=Coq induction port 未着手 → bookkeeping で不可]**。

**本 issue 1025 の plan (A+B の optParam→explicit rework) は necessary-but-insufficient。(C) が binding constraint** で、
A+B を完璧に threading しても residual/`card_kappaHall_lt_of_isTypeIIIorIV` は **(9.11) 経由で DIRTY のまま**。
= 「(10.8) knot を解けば residual が axiom-clean」(本 issue 冒頭) は **誤り**。

**STEP-0 判定 = STOP+report** (元指示「sorried root が issue の主張と違えば STOP」に該当; `sibleyTarget_H0C` は
`do-not-fill`ゆえ埋めるのは unsound STOP 条件)。**A+B の ~16 theorem rename は実施せず** (capstone spine の
delicate refactor リスクを負っても spine は clean 化しない = honest 前進なし)。**真の frontier = (C) の (9.11)
coherence の Coq 8-step induction port** (`sibleyTarget_H0C`/`caseB_coherent_sOf_H0Cprime` を honest 証明で置換)。
本 issue は open のまま (spine 未 clean); 実測は上記 `#print axioms` で再現可 (heir CLEAN 2 件 / (9.11) DIRTY / residual DIRTY)。

## ⚠⚠⚠⚠ 第5判明 = 第4判明の (C) は誤り、(A)+(B) で十分 (2026-07-13 lane-a, faithful CollectAxioms-replica metaprogram)

**第4判明の (C) sibleyTarget binding は FALSE** (詳細 = issue **9091**)。前 session の STEP-0 は
`#print axioms` (sorryAx の有無のみ、localize 不可) + **手読みトレース**で「residual → `coherent_sOf_H0C`
caseA → `Ptype_core_coherence` → `cohereOfSibleyTarget (sibleyTarget_H0C)`」と誤診した。実際は
`caseA_coherent_sOf_H0Cprime_of_refuter` (caseA 本体) は sibleyTarget を **cite しない** (metaprogram 実測
CLEAN)。sibley route (`coherent_H0C_commutator`) は off-spine (S12:1747 / S15 のみ)。

**faithful CollectAxioms replica** (getUsedConstants を type+value 双方; inductInfo ctors 再帰;
sorryAx parent 記録) で spine の leaf sorry を localize すると **ちょうど 2 つ**:
`typeV_forces_coherence` (via `isTypeIIIorIV`→legacy `no_typeV_maximal`) と
`typeII_coherence_contradiction_estimate` (via legacy `S12.S_not_coherent`)。**両方 (A)/(B) 圏で
heir CLEAN・fixable。`sibleyTarget_H0C` は spine に到達しない (reaches=false 実測)。**

∴ **本 issue の当初 plan (A+B threading) は necessary AND sufficient**。第4判明の STOP rationale
(「(C) ゆえ A+B は無駄」) は無効。残 = optParam 汚染方式 (435b057a) を **explicit param + wrapper**
(:111-127) へ rework + `coherent_S_of_coherent_SH0C`/`isTypeIIIorIV` 経路の htype 化。方式選択
(DAG relayer vs pervasive threading) と継続可否は **hub 再裁定へ回付** (9091)。

## ✅ 完了 (2026-07-13 lane-a, 方式2 explicit-param threading 実装、commit e21c9acb)

第5判明どおり **A+B threading (necessary AND sufficient)** で spine
`card_kappaHall_lt_of_isTypeIIIorIV` を **axiom-clean** 化。実測 `#print axioms` =
`[propext, Classical.choice, Quot.sound]` (**sorryAx 無し**、faithful CollectAxioms-replica でも
`sorryAx=false`)。full build green (4179 jobs) で AxiomsCheck assert 通過。

**実装 (localize は canonical CollectAxioms-replica で反復収束)**:
- 40 optParam DEFAULT (`hncH0C := S_H0C_not_coherent` / `htype := isTypeIIIorIV`) → explicit param
  (script)。legacy wrapper は legacy 値を明示供給 (off-spine 不変)。435b057a の optParam 汚染訂正。
- `isTypeIIIorIV_unconditional` (S12_Noncoherence) 新設 = clean heir; `S_H0C_not_coherent_unconditional`
  が各 s13hyp に clean htype を供給するのに使用 (= issue 冒頭で heir が「なぜ要るか」の答)。
- §13 Cat2 value-cite (`coherent_S_of_coherent_SH0C` / `H0C_relIndex_HC` / `p_q_distinct_odd_primes` /
  `H_elementaryAbelian` / `chief_*_of_noncoherent` / `coprime_card_W1_derived` /
  `q_dvd_secondDerived_relIndex_HC_sub_one`) に htype 明示 threading。
- **`p_prime_and_card_H_eq` は §13 Hypothesis の clean field `hyp.type_alt` で置換** →
  (11.6) H-structure cascade (opCore/p_mem_primeFactors/pComplement 系) の htype threading を回避。
- (11.6) `H_isPGroup` / `pComplementCore_eq_bot` に hnc+htype threading
  (line 514 `secondDerived_eq_HC` → `secondDerived_eq_HC_of_noncoherent`)。
- entry point `secondDerived_eq_fitting_of_base` / `card_H_eq_of_base` に hrefute param 追加、
  card_kappaHall が `S_H0C_not_coherent_unconditional` を clean refuter として供給。

AxiomsCheck 登録: `card_kappaHall_lt_of_isTypeIIIorIV` / `isTypeIIIorIV_unconditional` /
`card_kappaHall_lt_of_isTypeP1` (後者は heir 経由で clean 化した副産物)。

⚠ **`feitThompson` 自体は依然 sorry-dirty** (issue 冒頭の「§14/§15/§16 cross-lane 推移 sorry が残る可能性」が
的中)。feitThompson が到達する ~23 leaf sorry の中に `typeV_forces_coherence` /
`typeII_coherence_contradiction_estimate` も残るが、それは **card_kappaHall subtree 外の別 consumer**
(`no_typeV_maximal` の type-P2 用途、`caseB_order_u` 等) 経由。本 issue の scope = spine
character core の clean 化は完遂。close。
