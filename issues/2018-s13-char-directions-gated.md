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

- [ ] **(11.3) `S_H0C_not_coherent`** / **(11.5) `≥` (`HC ⊆ M''`)** / **(11.4) `coherent_quotient_bound`**
  ← Peterfalvi Thm (6.2)/(6.3) coherence (extension/quotient bound) の citeable 形 + (10.8)
  `S12.S_not_coherent` (S12 に export 済 `OddOrder.Peterfalvi.S12.S_not_coherent`、sorried だが
  signature-first で cite 可)。
- [ ] **(11.6) `core_structure`** 残 3 conjunct (`IsPGroup p H` / `U ≤ C_G(H₀)` / `H₀ = H'`)
  ← (9.3) [`U` centralizes `O_{p'}(H)`] + (9.6) [`C_{H₀}(W₁) = 1`] + (9.1) Wielandt (✅ done) +
  `[BG] 1.6(d)` + (11.5)。**注**: (9.3)/(9.6) の正確な carrier 形は S11 に未 export ⟹ S11 (driver)
  への追加 (lane-h で attemptable な §8-free 群論の可能性、要 (9.1) 適用調査) か lane-b 依頼。
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
