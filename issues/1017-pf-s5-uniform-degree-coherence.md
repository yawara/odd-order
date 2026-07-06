---
id: 1017
slug: pf-s5-uniform-degree-coherence
title: "Pf §5 uniform_degree_coherence + subcoherence — (10.7)/(10.8)/typeII の欠落 prereq"
created: 2026-07-05
---

# Pf §5 uniform_degree_coherence + subcoherence — (10.7)/(10.8)/typeII の欠落 prereq

> **hub 調整依頼 (shared coherence infra)**。lane-a group-theory + gate-1 完遂後、char endgame の
> 最上流 (10.8) `typeII_coherence_contradiction_estimate` を subagent 精査 (2026-07-05) →
> **§5 coherence 不在で BLOCKED** と確定。coherence infra は lane-b carve-out (S07) だが本体不在ゆえ
> 帰属/着手を hub 裁定。詳細 = `notes/peterfalvi/s13_11_8_orthogonality.md` update²⁴。

## 背景 (subagent 精査、確定)

char endgame の (10.8) `typeII_coherence_contradiction_estimate` (S12_MaximalIII_IV_V:453) =
Coq `FTtype345_noncoherence_main` (PFsection10.v:668-815)、2-sided pincer
`1−1/w₁−1/|U| < w₁w₂/|M'|`:
- **line-87 side (7.8.b)**: **assemblable** — `hypothesis78OfDade` (S09_CertificateDischarge:1637)
  + `zetaNuRhoNormSqGeOfDade` (:2406) + `card_derived_ge` proven。
- **hB side (10.7)**: **BLOCKED** — `typeII_derived_frobenius` (S12:47) 自身 sorry、root cause =
  **§5 の欠落**:
  - **`uniform_degree_coherence`** (Pf §5.x: uniform-degree seqInd family は coherent) — **不在**。
  - **`subcoherent` / `FTtypeP_subcoherent` R-datum** (Pf §5.x subcoherence) — **不在**。
  - `IsTypeF (derivedInG S)` → 完全 `[S,S]=H⋊U` Frobenius factorization の upgrade
    (`TypeIIData` は `derived_typeF` のみ、`TypeFData.frobenius_HU0` は `H⊔U₀` (U₀ exponent-proxy)
    止まりで (10.7) の完全 factorization 無)。

**★ 従来 notes の誤診断訂正**: (10.7)/hB は「§9-blocked (Section11CharacterData 未構成)」ではない
— `mkSection11CharacterData` (S12_Section9Counts:57) で構成済、Coq `Frob_der1_type2` (10.7) は §9
counts 不使用 (4-elt uniform family T2 の `uniform_degree_coherence` で local partner coherence 構築)。

## やること

- [ ] **§5 `uniform_degree_coherence`** 実装 (Pf §5.x、Dade isometry/coherence 基盤上、Coq
      PFsection5 の `uniform_degree_coherence` 対応)。
- [ ] **§5 `subcoherent` / `FTtypeP_subcoherent` R-datum** 実装 (Coq PFsection5 subcoherence)。
- [ ] 上を用いて (10.7) `typeII_derived_frobenius` (S12:47) を証明 (Coq `Frob_der1_type2`,
      PFsection10.v:549-658 mirror)。
- [ ] (8.8) enrich: `exists_typeII_maximal_with_w2` を M↔S partner counts (|H|/|S|/|V|/|W|,
      S_F#-TI) を出す形に強化 (`ub_G1` 用)。
- [ ] ⟹ (10.8) `typeII_coherence_contradiction_estimate` を close (line-87 assemblable + hB)。

## 完了条件

`typeII_coherence_contradiction_estimate` の sorry が消える (⟹ (10.8) S_not_coherent の char gate
解消 → (11.5)/(11.7)/gate-1 の char-gating + exists_zeta の一 dep 解消)。

## 参照

- notes/peterfalvi/s13_11_8_orthogonality.md update²⁴ (精査全文)、s12_10_8_noncoherence.md
- Coq: PFsection10.v:668-815 (FTtype345_noncoherence_main)、549-658 (Frob_der1_type2)、
  PFsection5.v (uniform_degree_coherence, subcoherent)
- stale docstring 修正候補: S12_Core:2836 (`exists_typeII_maximal_with_w2_of_typeP` は proven,
  「sorry」記述 stale)。

## 🧭 HUB 裁定 (2026-07-05, 帰属/着手 — POLE-2 coordination クラスタ、ユーザー「判断して」委任下)

**判定: §5 coherence infra (uniform_degree_coherence + subcoherent/FTtypeP_subcoherent) の着手 = lane a**。
理由: (1) a は gate-1 CLOSED 後 group-theory ungated frontier を完遂し**現在 free**、(2) a が subagent
精査で本 prereq を診断・Coq PFsection5 mirror を把握済み、(3) §5 coherence は a 自身の char capstone
(10.8 typeII estimate) の直接 unblock ゆえ consumer=a、(4) プロジェクト方針「deep なら正面から engage・
アイドル禁止」。**境界**: a は **新規 §5 coherence leaf を新設**する (例 `Peterfalvi/S05_UniformDegreeCoherence.lean`
or `GroupTheory/**` coherence leaf; 「未所有 leaf 新設は consumer が他レーンでも in-scope」)。**b の既存
`S07_Coherence*` は編集しない** (coherence owner=b の awareness は本 issue で確保、既存 file への追加が
必要なら hub flag)。b は §13 η-grid keystone (issue 3002) に集中継続、c は S16 consumer wiring 継続。
⟹ 3 レーン全てが char endgame の別 keystone を並行 deep-engage (a=§5 coherence / b=§13 η-grid /
c=S16 wiring)、lane 数 3 維持・アイドルなし。a は本 leaf 完成後 (10.7) typeII_derived_frobenius →
(10.8) estimate を閉じ、a 自身の char capstone を landing する。

## ★★ RE-DIAGNOSIS (2026-07-06, lane-a /loop — 前診断の重大な訂正) ★★

**本 issue の前提 (「§5 coherence infra 不在」) は部分的に誤り。code-level 検証で確定** ([[verify-port-state-by-number-not-coq-name]] の罠に前 subagent が嵌っていた — Coq 名 grep で descriptive-named repo 定理を見落とし):

1. **item 1 `uniform_degree_coherence` (Pf 5.7) は既に完遂・sorry-free**:
   repo 名 = **`coherent_of_constant_degree`** (`S07_CoherenceConstantDegree.lean:551`, file header
   に "COMPLETE — sorry-free, lane-c relane #8 issue 4012" 明記)。**lane-b の S14 が現に consume**
   (`S14_MaximalI.lean:4030, 4129`)。∴ item 1 は着手不要。前 subagent が Coq 名 `uniform_degree_coherence`
   のみ grep して見落とした。
2. **item 2 `subcoherent`/`FTtypeP_subcoherent` R-datum**: repo の subcoherent-analog =
   `S07.Hypothesis (5.2)` 構造 (`S07_Coherence.lean:1767`)。**一般 producer は無く consumer が
   family ごとに ad-hoc 構築** (S14:4030 = 7 fields を手で組む pattern)。∴ 「general R-datum producer を
   作る」でなく「(10.7) の T2 uniform family に対する `Hypothesis (5.2)` を組む」が正しい scope。
3. **真の (10.8) blocker = (10.7) `typeII_derived_frobenius` (S12:47/54)**。その Coq 証明
   `Frob_der1_type2` (PFsection10.v:549-658) は **prime-TI-reducible coherence 機構**
   (`primeTIred` / `FTtypeP_coherent_TIred` / `cyclicTIiso` / `uniform_prTIred_coherent`, Coq §3/§4)
   に依存し、これは **repo に不在 (grep 0 refs)**。∴ (10.7) は本 issue が示すより深く blocked
   (item 2 だけでなく §3/§4 prime-TI 基盤 全体が要る)。
4. **(10.8) line-87 side (7.8.b) の材料は存在**: `hypothesis78OfDade` (`S09_CertificateDischarge:1637`),
   `zetaNuRhoNormSqGeOfDade` (`:2406`), `typeII_noncoherence_arithmetic` (S12:67, proven)。

**⟹ re-scope**: 本 issue の「§5 coherence infra を作る」task は **item 1 完了・item 2 は §3/§4 prime-TI
基盤に gated**。次 subagent (2026-07-06 lane-a /loop, background agentId a8e14...) が
**(10.8) estimate (S12:453) の最小 buildable path** を scope + build 中: prime-TI 全機構を作らずに
既存 S09 infra + light `|U|≥7` で `∃u≥7, bound` を組めるか判定 → 組めれば build、不可なら最小 missing
§3/§4 基盤を named-report。結果は git log / 本 issue の次追記 / notes s13_11_8 で確認。
**hub へ**: 本 issue の当初 scope (「§5 coherence を新設」) は誤前提。真の残 = (i) §3/§4 prime-TI 基盤
(大, ungated, 誰の所有でもない leaf — 新設可) or (ii) (10.8) の Lean-specific 軽量 path (subagent が判定中)。

## ⚖️ HUB 裁定 (2026-07-06, 監視 hub) — lane-b の §5 coherence 実装の帰属

lane-b の未マージ commit (`main..b`) が §5 coherence 実装を含むため、監視 tick で帰属を裁定:

1. **`S07_Subcoherent.lean` (新規 +603) → lane-b carve-out GRANTED**。理由: 既存 b 所有
   `S07_Coherence` / `S07_CoherenceConstantDegree` を import する **coherence infra**、subcoherence
   assembler `irrSubcoherent` を提供 (§5 (5.3.a))。module note に "Nothing here is posited" 明記
   (各 R(χ) は keystone から抽出、(5.2.e) は difference-isometry から導出)。b の `S15_SAndT_Setup`
   が consume (`:815`, `:842` — "assembler `S07.irrSubcoherent` consumes for the §9 induced family")。
   **先例 = carve-out 0090** (`S09_CertificateDischarge`: b が a の S09 namespace に coherence infra 新設)。
   ⟹ step-1.5 で b が `S07_Subcoherent.lean` を編集しても逸脱でない (a が編集したら逸脱)。b の
   coherence-infra 例外 glob を `S07_{Coherence*,Subcoherent}` に拡張 (merge_monitor は b 合流時に更新)。

2. **`S05_SigmaIsometry.lean` mu2Grid 追加 (+125, commit `a1735d6a`) → 要撤去 (HOLD 原因)**。
   `mu2Grid`/`mu2GridSign`/`sigma_omega_eq_mu2GridSign_smul_mu2Grid`/`mu2Grid_orthonormal`/
   `mu2Grid_injective` 等 8 宣言。**9014 (PrimeTIResidue) 撤回後 orphan** (`mu2Grid` の参照 31 件
   全て S05 内・external 0)。**S05_SigmaIsometry は lane-a 所有の σ-theory 本丸** (ft_lane_reallocation
   line 48 "σ-theory tail/dedup" = a の distinguishing cluster)、carve-out 無。
   ⟹ **lane-b は次 sync で mu2Grid ブロックを S05 から除去** (dead code + a ファイルへの territorial
   intrusion)。もし将来 subcoherence が σ-extraction を要するなら a-owned S05 でなく shared
   `GroupTheory/**` leaf か b-owned file に置く。除去後 b は clean に合流可。

3. **合流状態 (2026-07-06 tick)**: **a** (9.8.d S11) + **c** (14.9 S16) は build-green (3932 jobs,
   AxiomsCheck OK) で local main 合流済 (push は harness 分類器が default-branch 保護で保留 →
   ユーザー裁可待ち)。**b は #2 の mu2Grid 撤去まで HELD**。

4. **⚠ cross-lane coordination flag**: 本 issue 1017 は **lane-a background /loop (agentId a8e14…) が
   §5/prime-TI を現在 再診断中**。lane-b の §5 coherence 実装と**同一ゾーン**。特に **prime-TI 基盤の
   存否で食い違い**: lane-a 再診断 = 「prime-TI-reducible coherence 機構 (`primeTIred` 等) は repo 不在
   (grep 0 refs)」 / lane-b = 「S06 が prime-TI residue theory を完全所有ゆえ 9014 leaf は duplication」
   と撤回。**両者は同じ §5/prime-TI を別診断**しており、重複・矛盾のリスク → hub/user がデコンフリクト
   要 (どちらの診断が正しいか = code-level 検証で決着可、別 tick で subagent 精査推奨)。
