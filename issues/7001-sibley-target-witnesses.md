---
id: 7001
slug: sibley-target-witnesses
title: "SibleyTarget witnesses for the wired §10-16 coherence riders (endpoint A residual)"
created: 2026-06-15
---

# SibleyTarget witnesses for the wired §10-16 coherence riders (endpoint A residual)

## 背景

FT-path policy の **endpoint A**(`notes/meta/ft_path_policy.md` §4)= Pf §10-16 spine の
coherence rider を (6.8) `S08.sibleySetup_is_coherent` への cite に置換する wiring。
engine + 最初の 3 rider は landing 済(commit `5b95fdb8`, `fec51141`):

- engine leaf `OddOrder/Peterfalvi/S10_CoherenceWiring.lean`(sorry-free):
  `coherent_of_sibley` / `nonempty_coherent_of_sibley` / `SibleyTarget`(carrier)/
  `coherent_of_sibleyTarget`(Nonempty 形)/ `cohereOfSibleyTarget`(unwrapped 形)。
- wired riders(各 body は engine cite で sorry-free、gap は `sibleyTarget_*` producer に局在):
  - S15 `S_coherent`(13.2.d) ← `sibleyTarget_S`
  - S11 `coherent_H0C_commutator`(9.11) ← `sibleyTarget_H0C`(下流 S12 `typeII_section11_coherence` も自動 decouple)
  - S14 `frobenius_typeI_coherent`(12.6) ← `sibleyTarget_frobI`(Frobenius = case-c1 で最構成容易)

各 rider は B が (6.8) proof body を埋めれば自動 unconditional 化する(engine 経由)。
**残る gap = 各 `sibleyTarget_*` producer**(現在 `sorry`)= 極大部分群が Sibley Dade
hypothesis (6.8)(a)/(b)/(c) を満たすことを exhibit する **§14 構造 obligation**。
これは Peterfalvi が (13.2.d) 等で「(6.8) applies to S」と読み下す箇所そのもの。

## やること

各 producer `noncomputable def sibleyTarget_* : CoherenceWiring.SibleyTarget τ S A0` を構成する。
返すべきは `SibleyTarget` の field 群:
- `H : Subgroup ↥L`(極大部分群 L = M/S の Sibley kernel、典型 = M_σ / nilpotent normal Hall)
- `invH : Invertible (Nat.card ↥H : ℂ)`(有限性から導出可)
- `sib : SibleyDadeHypothesis G L H`(6.8 の (a) H◁L nilpotent + L=H⋊W₁ split / (b) S=Ind 族 /
  (c) Frobenius ∨ Hypothesis46)
- `tau_eq : sib.tau = τ` / `S_eq : sib.S = S` / `A0_eq : supportInSubgroup (sharpImage H) L = A0`

- [ ] `sibleyTarget_frobI`(S14, **最優先**): Frobenius 枝 = `cases := Or.inl`。`hfrob` が
      `IsFrobeniusGroup ↥L (hyp.H.subgroupOf L) C` を供給するので (c1) は直接。残 = H nilpotent /
      split / H^# TI / §4 dade datum の構成(§14 type-F 構造)。
- [ ] `sibleyTarget_S`(S15, 13.2.d): type II/III。(c) は Hypothesis46 (c2) 枝(W₂ prime + (4.6))
      ⟹ §14 type-P 構造 + §6 (4.6) carrier 要。
- [ ] `sibleyTarget_H0C`(S11, 9.11): type II/III/IV の S(H₀C')。chief factor 構造依存。

## 完了条件

各 `sibleyTarget_*` の `sorry` が消える(= `SibleyTarget` を実構成)。これにより、対応 rider は
(6.8) のみに gate される状態へ移行(B 完成で完全 unconditional)。3 つ全ては §14/§6 構造の
landing に gate されるので、段階的に close 可。

## ✅ HUB 裁定 + 現況更新 (2026-07-02 全体レビュー)

**stale 前提の更新**:
- **(6.8) は完成済** (`sibleySetup_is_coherent` sorry-free、S08 帯 全 0 sorry) — 「B が (6.8) proof body を
  埋めれば自動 unconditional 化」の gate は消滅。残 gap = 各 `sibleyTarget_*` producer のみ。
- **`sibleyTarget_frobI` は issue 2032 で降格**: (12.16) witness に対し H^# 非 TI で unsound と判明、
  (12.6) は 3-case split 化済み (witness 経路は case (b)/(c) で決着)。frobI producer は **TI-case 限定**の
  producer としてのみ有効 — 本 issue の「最優先」指定は無効。

**裁定**:
1. **`sibleyTarget_H0C` (9.11, S11:6293) の owner = lane a** (S11 = a 所有、かつ 11.8.6 の S₂-coherence
   leg の前提 = a 自身の spine endpoint)。「§14/lane-b gated」と読まない — b のプランに S₂ deliverable は
   存在しない (docs/plan レビューで確認)。
2. **着工前に 2032 型 soundness 監査を必須とする**: H0C witness に対し (6.8)(a) の TI 要件 (または
   Hypothesis46 (c2) 枝) が intended use ((9.11) → 11.8.6) で本当に成立するかを Pf §9 原文 + Coq
   PFsection9 で確認してから `SibleyTarget` を構成する (frobI の前例 = 偽 pin 1 回・10 分 revert)。
3. `sibleyTarget_S` (13.2.d, lane c) は **vestigial 判定済 (closed/1004)** — 完成させず、
   s16_w4_char_cascade.md の「HUB 裁定 (2026-07-02)」節の W-side restate/retire 判定に従う。

## ✅ 2032 型 soundness 監査 COMPLETE (2026-07-07, lane-a /loop) — 裁定②の必須監査、判定 = **UNSOUND**

裁定②の「着工前 soundness 監査」を実施し、**`sibleyTarget_H0C` は unsound (= 偽 field 要求、frobI と
同一 failure mode)** と確定。**この witness の `sorry` は埋めてはならない。**

### 監査結果 (三重確証)
1. **`SibleyDadeHypothesis` (S08:3234) の TI field は無条件**: `H_sharp_ti : IsTISubset (sharpImage H) L`
   (S08:3248) と `dade_H_eq_bot : ∀ a, dade.H a = ⊥` (S08:3258) は **top-level field** = (c1) Frobenius /
   (c2) Hypothesis46 の**どちらの枝でも必須**。∴ (6.8) は常に `H^#` TI in `G` を要求。裁定②が想定した
   「Hypothesis46 (c2) 枝なら TI 回避」は**不可** — c2 でも `H_sharp_ti` は必須 field。
2. **S(H₀C') の Sibley kernel `H = HC` は非TI**: `HC ⊆ F(M)` (nilpotent Hall)、`HC^#` は G で TI でない
   (centralizer が M を escape)。∴ `H_sharp_ti`・`dade_H_eq_bot` はともに偽 → witness unprovable。
   **frobI (2032) と完全に同一** (非TI witness → 偽 `dade_H_eq_bot` → unprovable; docstring の
   「(6.8) 適用可」は overclaim)。
3. **★ smoking gun — Coq が (6.8) を使わない**: `Ptype_core_coherence` (Pf (9.11), `PFsection9.v:1484-1571`)
   は coherent(S_ H0C') を **(6.8) 抜きの 8-step induction** で証明。Galois 枝 = `uniform_degree_coherence`
   (uniform-qu 真); 非Galois 枝 = degree-`qa` subfamily を filter → `uniform_degree_coherence` (qa uniform) →
   conjugate-pair を 1 組ずつ帰納的に extend し maximality に矛盾。**(6.8) が適用可なら Gonthier et al. は
   短い (6.8) route を採ったはず** — 採らなかった = (6.8) が S(H₀C') に適用不可の決定的証拠。

### ⟹ honest route (裁定更新) = Coq (9.11) 8-step induction の port
- **`sibleyTarget_H0C` は撤回** (fill しない; sorry は wiring type-check のためだけに残置)。
- **`coherent_H0C_commutator` は `cohereOfSibleyTarget` cite を捨て**、Coq `Ptype_core_coherence` の
  induction を Lean に port して再証明する (Galois/非Galois split + `uniform_degree_coherence` on
  uniform subfamilies + coherence-extension induction)。**次 lane-a iteration の本体作業**。
- in-code に警告注記済 (S11 `sibleyTarget_H0C` / `coherent_H0C_commutator` docstring、本 commit)。
- 監査自体が裁定②の mandated deliverable ゆえ完了扱い。checklist の `sibleyTarget_H0C` は
  **「fill」でなく「induction port で置換」** に読み替え。

## 📋 port plan — Coq `Ptype_core_coherence` 8-step induction (2026-07-12, lane-a 精読)

Coq `PFsection9.v:1484-1571` の構造 (Lean port target = `coherent_H0C_commutator` の
`cohereOfSibleyTarget` cite を置換):

1. **subcoherent 供給**: `S_ H0C'` に対し subcoherent R を `FTtypeP_subcoherent` +
   `subset_subcoherent` で取得 (Lean: S07/S08 subcoherent infra、要 grep 確認)。
2. **case split `typeP_Galois`**:
   - **Galois 枝 (一行)**: `uniform_degree_coherence scohS0` — 全 χ∈S_(H0C') が uniform degree
     `#|M:HU|·u` (`typeP_Galois_characters` の `XOC'u`)。Lean `uniform_degree_coherence` は
     issue 1017 で port 済の見込み (S07、要確認)。
   - **非 Galois 枝 (本体、深い)**:
     - `S1 = filter (·1 == q·a) (S_ H0C')` (degree-qa subfamily)。`cohS1` = `uniform_degree_coherence`
       (q·a uniform、`typeP_nonGalois_characters` の構造)。
     - **induction** (`elim: nS` on `size S3`、S3 = S_(H0C')∖S2 の complement): S2 を
       conjugate-pair `(χ :: χ* :: S2)` で 1 組ずつ extend、S3 枯渇まで。空なら `subset_coherent`。
     - **extension step (9.11.1)-(9.11.8)** = `without loss` + 8 steps (最難): S3 の χ を選び
       `coherent (χ::χ*::S2)` を構成。norm bound `⟨X,X⟩≤q` + odd parity + degree qa 構造 +
       maximality 矛盾。Coq :1571 以降を精読して port。
3. **Lean 資産 (要 locate)**: `uniform_degree_coherence` (1017)、subcoherent(S_(H0C'))、
   `typeP_Galois_characters`/`typeP_nonGalois_characters` の Lean 相当 (§9 char 構造、S11 に一部済)、
   conjugate-pair coherence extension (S07 `IsCoherent` の extend 補題)。多くは §9/§7 で既 landing の
   可能性 — port 前に S11/S07 を grep。

⚠ deep multi-iteration。難所 (extension step) は Coq 精読 + 必要なら ChatGPT
([[feedback-ask-chatgpt-for-elided-gaps]])。core = 非 Galois induction。

## 参照

- `notes/meta/ft_path_policy.md` §4(endpoint A)
- `notes/peterfalvi/s10_13_maximal_structure.md`(§10-13 gate 分類)
- engine: `OddOrder/Peterfalvi/S10_CoherenceWiring.lean`
- (6.8) supplier: `OddOrder/Peterfalvi/S08_CoherenceTheorems.lean:46` `sibleySetup_is_coherent`
  / `SibleyDadeHypothesis` = `S08_CoherenceCorePart1.lean:3265`
- commits `5b95fdb8`(engine + S15), `fec51141`(S11 + S14)
- 関連: issue 7000(§14 Prop 14.2 support, H 所有)= §14 type-P 構造の隣接
