---
id: 2018
slug: s13-char-directions-gated
title: "Pf §13 (types III/IV) char-direction completion — gated on lane-b coherence/char API"
created: 2026-06-23
---

# Pf §13 (types III/IV) char-direction completion — gated on lane-b coherence/char API

## 背景

lane-h relane #2 (issue 8018+2017) で lane-h = **`S13_MaximalIII_IV`** (= Pf §11 types III/IV,
results (11.x); repo file 番号は Pf §番号 -2)。2026-06-23 に構造側を de-opacify し、char API 無しに
faithful に STATE できる定理を全て実ステートメント化 + unconditional fragment 2 本を landing
(commits `81b633cc` / `04eb6f32`、正本 = `notes/peterfalvi/s10_13_maximal_structure.md` §10)。

残る §13 sorry は **全て character-theory に gated** で、lane-h 単独では閉じられない。本 issue は
その deferred 依存とトリガ条件を記録する (cross-lane sync は notes/issue 経由、[[cross-lane-sync-via-notes]])。

## やること (lane-b の char API landing がトリガ)

§13 の各 char-direction を、対応する lane-b/上流の成果が landing したら wire する:

- **✅ (11.3) `S_H0C_not_coherent` は sorry-free 化済** (commit `5a212bc4`, cite-reduction):
  `coherent_S_of_coherent_SH0C` (新 named obligation = Thm (6.3) 適用 `S(H₀C) coh ⟹ S coh`)
  + `S12.S_not_coherent` ((10.8)) を cite → 矛盾。残 gate = `coherent_S_of_coherent_SH0C` のみ
  (Thm (6.3)、repo の §6 は `SibleyDadeHypothesis` filtration machinery `S08_Theorem63` 経由で
  standalone subfamily-extension 形が無い ⟹ lane-b §6 char で discharge)。
- **✅ (11.5) `secondDerived_eq_HC` (`M''=HC`) は sorry-free 化済** (commit `0adb8560`):
  `≤` = `secondDerived_le_HC` (proven, (8.5.a)), `≥` = `HC_le_secondDerived` (新 named obligation,
  (5.7)+(11.4) coherence、char-gated)。残 gate = `HC_le_secondDerived` のみ。
- [ ] **(11.4) `coherent_quotient_bound`** ← Peterfalvi Thm (6.2) quotient bound (= 本定理が
  Thm 6.2 そのもの、obligation 化しても rename ゆえ未処理; lane-b §6 char で discharge)。
- [ ] **(11.6) `core_structure`** 残 3 conjunct (`IsPGroup p H` / `U ≤ C_G(H₀)` / `H₀ = H'`)
  ← (9.3) [`U` centralizes `O_{p'}(H)`] + (9.6) [`C_{H₀}(W₁) = 1`] + (9.1) Wielandt (✅ done) +
  `[BG] 1.6(d)` + (11.5)。
  - **✅ `U ≤ C_G(H₀)` clause の Wielandt 部分は landed** (commit `558619f2`,
    `S13.U_centralizes_H0_of_W1_fpf`, axiom-clean): `C_{H₀}(W₁)=1` ∧ `U≠1` ⟹ `U ≤ C_G(H₀)`,
    lane-h の (9.1) `frobenius_kernel_centralizes_of_complement_fpf` 経由。**残 gate = fpf 入力
    `C_{H₀}(W₁)=1`** = `|W₂|=p` (§8 `S11.typeIIIorIV_W2_prime`, cites (8.8)) + coprime-quotient
    (`C_H(W₁)=W₂` [TypePData `centralizer_W1`] + Cor 3.28 surj + (9.6) `|W̄₂|=p`)。
  - `IsPGroup p H` ← (9.3)[U cent O_{p'}(H)]+(11.5); `H₀=H'` ← [BG]1.6(d)+(11.5)。両 (11.5)-gated。
- [ ] **(11.7) `H_elementaryAbelian`** ← (11.5) + (11.6) 下流。
- [ ] **(11.8.x)/(11.8)/(11.9)** + opaque rider field (`notOrthogonalFormula` /
  `finalOrthogonalityFormula` / `caseB_of_97`) の de-opacify
  ← σ/τ₁/ω/μ/(Irr W)^σ character API (gate #3) + (9.7)(9.8)(9.11)。最も深い char gate。

## 完了条件

§13 の 8 sorry が char API landing に伴って解消され、`S13_MaximalIII_IV` が
(BG §16 / lane-b char modulo) の実証明になる。少なくとも (11.3)/(11.4)/(11.5) が
(10.8)+Thm(6.3) cite で閉じれば第一マイルストーン。

## 参照

- `notes/peterfalvi/s10_13_maximal_structure.md` §10 (de-opacify status + gate map)
- commits `81b633cc` (構造 cluster + 2 fragment) / `04eb6f32` ((11.4) index bound)
- 上流 export: `OddOrder.Peterfalvi.S12.S_not_coherent` (10.8), `S11.typeP_commutator_U_centralizes_H` (8.5.b),
  `S11.typeP_chiefFactor_card` (9.6 card), `GroupTheory.wielandt_fixedPoint_frobenius` (9.1)
- proven fragments: `S13.Hypothesis.secondDerived_le_HC`, `S13.Hypothesis.derivedU_le_C` (AxiomsCheck 登録)
- relane: issue 8018 / 2017 (CLOSED), merge_monitor.md relane #2

## 2026-06-23 REASSIGN (relane #6、ユーザー裁可、issue 4011) — lane-h → lane-c

lane-h は POLE-2 (issue 2009) 移行で S13 を dormant 化 → **S13_MaximalIII_IV を lane-c へ移譲**
(char ボトルネック支援、lanes 等価)。lane-c は lane-b coherence ((6.2)/(6.3)/(6.8)) + §11 char を
cite して §13 char-direction を並列生産。lane-h は cite のみ。宛先 lane-h → **lane-c**。

## 2026-06-23 UPSTREAM update (relane #7) — Thm 6.2/6.3 は lane-h が生産

S13 のローカル obligation `coherent_S_of_coherent_SH0C` (Thm 6.3) / `coherent_quotient_bound` (Thm 6.2) の
standalone 版を **lane-h が §6/§8 新 leaf で生産** (relane #7、issue 2021)。lane-c は landing したら cite して
(11.3)/(11.4) を discharge。それまで sorried sig を cite して下流を積む ([[feedback-cite-sorried-lemmas-if-signature-correct]])。
