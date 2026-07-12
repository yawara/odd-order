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

## 2026-07-06 更新 (lane b, verify-first 精査) — §5 subcoherent は (13.3) coherence とも shared、sibleyTarget_H0C は likely-unsound

lane b の (13.3) `character_degree_analysis` τ₁ coherence を verify-first 精査した結果、**本 issue の
§5 subcoherent gate が (13.3) coherence とも共有**と確定:

- **`uniform_degree_coherence` は実装済** — `coherent_of_constant_degree` (S07_CoherenceConstantDegree:551,
  proven)。本 issue の「uniform_degree_coherence 不在」は **stale**。残る真の gate = **`subcoherent` /
  `FTtypeP_subcoherent` R-datum** (Coq PFsection5) のみ (repo grep 空)。
- **(13.3) coherence の現 route (S11 `sibleyTarget_H0C` = (6.8)/Sibley 経由) は likely-UNSOUND** (issue
  2032 `sibleyTarget_frobI` と同 defect class): honest S-instance (family sSet=Ind_{PU}^S、support
  (C')^#) に対し `SibleyTarget` の kernel K は family 制約で K=PU・support 制約で K=C' を同時に要求するが
  **PU≠C'** ⟹ 数学的に不可能。加えて K nilpotent / S=K⋊W₁ / K^# TI in G も非充足。
- **honest route (Coq `Ptype_core_coherence` PFsection9:1484 に一致)**: (9.11) は subcoherent +
  uniform_degree_coherence + extend_coherent の (9.11.1-8) 8-step induction で証明、**(6.8)/Sibley を
  経由しない**。⟹ `sibleyTarget_H0C` は (6.8) scaffold から外し、§5 subcoherent + coherent_of_constant_degree
  cascade で再構築すべき (2032 fix と同型、signature 保存内部 re-proof)。

**⟹ `subcoherent`/`FTtypeP_subcoherent` (§5) は (10.7)/(10.8) [a] + (13.3) coherence [b] の共有 keystone
prerequisite。** これを実装すれば両方 un-gate。lane b の (13.3) tau1S engine (tau1S_ofHonest 系) は現在
likely-unsound な sibleyTarget_H0C を cite しており、subcoherent 実装後に coherent_H0Cprime_S を §5 route へ
再 grounding して健全化する必要がある。hub 裁定: subcoherent の owner/着手 (shared §5/§7 infra)。

## 2026-07-06 更新 #2 (lane b) — prime-TI は S06 に存在 (certainType 名)、prDade は assemblable + irrSubcoherent landed

subcoherence 精査で 2 点判明:
- **subcoherent structure は既 port 済** (S07.Hypothesis)。欠けは assembler のみ → `irrSubcoherent`
  (S07_Subcoherent.lean、Coq irr_subcoherent、sorry-free) を landed。**FTtypeP_subcoherent は PFsection8:819** (PFsection5 でなく)。
- **⚠ prime-TI machinery は「absent (0 refs)」でない — S06 に certainType 名で存在** (Coq 名 grep の見落とし、
  本セッション 2 度目)。`certainType_isCoherent` (S06_CertainTypeCoherence:505 = 型-P family の coherence!)、
  `certainType_columnSum_conj`/`certainType_columnSign_eq`/`certainType_nonzero`/`columnFamily_mu_injective`/
  `Hypothesis46` 等。⟹ **item 1 `prDade_subcoherent` は S06 certainType_isCoherent + irrSubcoherent から
  assemble 可能 (large 新 prime-TI port 不要)**。

**⟹ (13.3) coherence chain の tractability 上方修正**: S06 certainType_isCoherent → prDade_subcoherent
(assemble) → FTtypeP_subcoherent (thin) → (9.11) Ptype_core_coherence (8-step、coherent_of_constant_degree
既存) → (13.3) tau1S coherence (sibleyTarget_H0C を置換) + (10.7)[a]。次 = prDade を verify-first で assemble。

## 2026-07-06 更新 #3 (lane b) — (9.11) base-case glue landed、残 gap = sumnS norm chain (a+b 共有)

`subset_subcoherent` + `coherent_subset_of_constant_degree` (S07_Subcoherent.lean、sorry-free、commit
9aad60d8) landed = (9.11) の **Galois 枝 + non-Galois base case S1**。`irrSubcoherent` と合わせ subcoherent
→ uniform-subfamily coherence の glue 完備。

**残る単一共有 gap (a+b)**: honest S-family sSet は mixed-degree ゆえ full (9.11.1-8) pair-adjoining
induction が要。engine (coherentPairChain S07:4907 + (5.6) adjoining) は既存だが、per-step (5.6.2)
integer-forcing `hY` = **norm-inequality chain `lb0 ≤ … ≤ sumnS S2 ≤ lb0`** (Peterfalvi extend_coherent +
Snorm/sumnS 次数和不等式) が **repo 未在**。これが (13.3) coherent_H0Cprime_S の sibleyTarget_H0C 置換 +
(10.7) typeII_derived_frobenius の共通 keystone。

**lane a (10.7) への lead**: (10.7) の T2 が **4-element uniform-degree family** なら (issue 1017 冒頭記述)、
full induction 不要で `coherent_subset_of_constant_degree` (landed) から**直接**閉じる可能性。要 lane-a 確認
(T2 degree-uniformity は lane-b から未検証)。**⟹ 次: (a) lane a が T2 uniform で (10.7) を直接 close 試行、
(b) sumnS norm chain を実装 (full (9.11) 用、shared)。** hub 裁定: sumnS chain の owner。

## 2026-07-06 更新 #4 (lane b, subagent) — sumnS/Snorm quantity + extend_coherent 整数強制 bridge landed (sorry-free)

**verify-first で前提を 1 つ訂正**: 「sumnS norm chain は repo 未在」は**部分的に誤り**だった (本セッション 3 度目の Coq 名 grep 見落とし class)。
- **Snorm/sumnS の名前** は確かに未在 → 本更新で導入。
- **extend_coherent の正方向 engine は既存・sorry-free** = `xAdjoinStepW` (S08_CoherenceWeighted:287): `hDeg : 2·a < ∑ᵢ deg(i)²/mc(i)` から `coherent(S₁∪{χ,χ̄})` を産む = Peterfalvi (5.6) = Coq `extend_coherent_with`。その contrapositive = `coherentDegreeSqNormBound_of_not_coherentW` (:635)、raw-degree `sumnS` bound `∑ᵢ χᵢ(1).re²/‖χᵢ‖² ≤ 2·ψ(1).re·η(1).re` は §8 case-B family 用に `sMember_degreeSqNormReBound_of_not_coherent` (S08_CaseBEnumeration:1080) が既に組んでいる。

**landed (S07_Subcoherent.lean、+164 行、sorry-free、`#print axioms`=標準3公理のみ、`lake build OddOrder` GREEN 3932 jobs)**:
- `Snorm ψ := (ψ 1).re²/⟨ψ,ψ⟩.re` (Coq `Snorm`, PFsection9:1534) + `sumnS Si := ∑_{ψ∈Si} Snorm ψ` (Coq `sumnS`, :1535)。
- `Snorm_nonneg`/`sumnS_nonneg`/`sumnS_empty`/`sumnS_le_of_subset` (= Coq `lbS1'2` の (9.11.6) `S1'⊆S2` 単調性)。
- **`sumnS_image_eq_anchorSq_mul`** = raw↔normalized 橋 `sumnS = η²·∑(deg²/mc)` (§8 が inline 重複していた calc を factor out; これが raw `sumnS` squeeze を `xAdjoinStepW` の normalized `hDeg` に繋ぐ load-bearing piece)。
- **`two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS`** = extend_coherent 発火 precondition: `lb0=2·a·η² < sumnS` から `2·a < ∑(deg²/mc)` を導く (η²>0 で cancel)。
- `lb0_le_lb1_of_degreeRatio_le` = (9.11) 底 squeeze step (Coq `lb01`) の純算術単調性。

**残り (= assembly、analytic gap は解消)**: (9.11.2-9.11.5) 中間 squeeze `lb1≤lb2≤lb3≤sumnS S1'` (Coq `lb12`/`lb23`/`lb3S1'`) は ℕ-index 算術 (`two_mul_lt_sq_of_commonIndex_primePower_gap` S07:1986 + Nat index lemmas、中規模・機械的)。(9.11.1/7/8) は `coherentPairChain` を §9 induced-family Dade witnesses に対して fold (per-step `Dmem`/`hmemOrtho`/`hgen` を、§8 case-B の `sMember_degreeSqNormBound_of_not_coherent` と同型で、§9 `S_ H0C'` family 用に組む)。**⟹ (13.3) `coherent_H0Cprime_S` の sibleyTarget_H0C 置換 + (10.7) `typeII_derived_frobenius` は、§9 induced-family witnesses を thread する 1 focused multi-step session で到達圏内** (analytic content は landed、残るは family-specific 組み立て)。

## 2026-07-06 更新 #5 (lane b) — (9.11) squeeze の pure-arithmetic 層が全 landed sorry-free

更新 #4 で「残り = (9.11.2-9.11.5) 中間 squeeze + assembly」としたうち、**中間 squeeze (lb12/lb23) と
lb3S1' 左端**を landed。これで **(9.11) squeeze `lb0≤lb1≤lb2≤lb3≤sumnS S1'≤sumnS S2` の pure-arithmetic
層は全て repo に在り sorry-free**:

| Coq step | Lean 補題 (S07_Subcoherent.lean) | commit |
|---|---|---|
| `lb01` (2·q·a·χ ≤ 2·a·q²·u) | `lb0_le_lb1_of_degreeRatio_le` | ad1c339a |
| `lb12` (2a≤p−1、Gauss) | `two_mul_le_of_dvd_of_odd` (+`_dvd`/`_lt` companion) | ccc3351c |
| `lb23` ([U:C]≤[U:U']、Lagrange) | `relIndex_le_relIndex_of_le` (+`_lt` companion) | ccc3351c |
| `lb3S1'` 左端 (sumnS S1'=|S1'|·(qa)²) | `sumnS_of_norm_one_constant_degree` | 5ff2bb6d |
| `lbS1'2` (S1'⊆S2 単調) | `sumnS_le_of_subset` | ad1c339a |
| 発火 precondition (lb0<sumnS ⟹ 2a<∑) | `two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS` | ad1c339a |
| raw↔normalized 橋 | `sumnS_image_eq_anchorSq_mul` | ad1c339a |
| extend_coherent 正engine (5.6) | `xAdjoinStepW` (S08:287、既存) | — |
| 底 coherence (S1 uniform) | `coherent_subset_of_constant_degree` (既 landed) | 9aad60d8 |

**残る唯一の gate = assembly (`coherent_H0C_commutator` S11:7788 の sibleyTarget_H0C 置換)**。engine は
`coherentPairChain` (S07_Coherence:4907): 底 `S₀=S1` (coherent) + 隣接 pair 列挙 + per-step `hstep` を fold。
`hstep` は上表の squeeze + `xAdjoinStepW` で組める。**genuine な残り content は 2 つだけ**:
1. **§9 induced-family (`S_ H0C'`) の per-step Dade witness data** (`xAdjoinStepW` が要る decomposition
   `Dmem`/`hmemOrtho`/`hgen`)。§8 case-B の `sMember_degreeSqNormBound_of_not_coherent` (S08_CaseBEnumeration)
   と同型 shape、§9 family 用に組む。
2. **induction bookkeeping** = (9.11.1) `without loss` + (9.11.7/8) maximality 矛盾: S3=S_H0C'∖S1 が尽きるまで
   `lb0 < sumnS S2` が常に成り立つ (squeeze collapse が矛盾を生む) の帰納。

次 iteration はこの assembly を正面から engage (§9 `Section11CharacterData`/`TypesIIIIIIVSetup` が非Galois
setup = typeP_Galois 述語・U1/a/H1・S_H0C' Finset・lb_Sqa を expose するか確認 → fold を wiring)。
lane a (10.7) も同一 (9.11) coherence で閉じる。

## 2026-07-06 更新 #6 (lane b) — assembly scoping 結果: §9 setup の available 性を確定

更新 #5 の「次: §9 setup が typeP_Galois 述語・U1/a/H1・S_H0C'・lb_Sqa を expose するか確認」を実施。
`Section11CharacterData` (S11:2053) / `TypesIIIIIIVSetup` (S11:75) を精査:

**在る (expose 済)**: `C = C_U(H̄)` (`cSub`)、`U' = [U,U]` (`uprimeSub`)、`C' = [C,C]` (`cprimeSub`)、
`𝒳 = {χ∈Irr(HU) | H⊄Ker χ}` (`xiSet`)、`𝒮 = Ind 𝒳` (`sSet`)、`𝒳(Y)`/`𝒮(Y)` (`xiOf`/`sOf`)、
`u = |Ū|` (`u_eq_card_quotient`)。→ subgroups + character families + u は全部 genuine に在る。

**不在 (要 build)**: `typeP_Galois`/`typeP_nonGalois` **dichotomy 述語** (grep 0 in S11)、非Galois 構造
`typeP_nonGalois_characters` の `a = [HU:H⟨U1⟩]`/`U1`/`H1` data、そして **`lb_Sqa`** (`|S1| ≥ (p−1)·[U:U']/a²`
の下界; Coq `lb_Sqa`、(9.8)-level の deep datum)。

**⟹ assembly の genuine 残 content 精緻化** (更新 #5 の「§9 witnesses を thread」より大きい):
1. **(9.8)-level typeP_Galois/nonGalois character-structure dichotomy を build** (Coq
   `typeP_Galois_characters` = 全 constituent degree `|M:HU|·u` / `typeP_nonGalois_characters` =
   `a`/`U1`/`H1`/`lb_Sqa`)。これが (9.11) を 2 branch に割る前提。
2. Galois branch: 上記 + `coherent_subset_of_constant_degree` (landed) で close。
3. 非Galois branch: `coherentPairChain` fold + 上表 squeeze (全 landed) + per-step Dade witnesses。

これは multi-session の genuine §9 prerequisite (コスト・規模は着手基準でない、CLAUDE.md)。次 iteration は
(9.8) dichotomy 構造 (typeP_Galois 述語 + lb_Sqa) の build に正面着手。上流 = typeP_Galois 述語 (文書順で
先)。lane a (10.7) も同一構造依存。

## 2026-07-06 更新 #7 (lane b) — ★frontier 大修正: (9.11) は「(9.8) を scratch build」でなく「既存 dichotomy+branch counts を wire」

更新 #6 の「(9.8) typeP_Galois/nonGalois dichotomy を build」は **verify-first で誤りと判明** (更新 #6 の
scoping grep が `typeP_Galois`/`lb_Sqa` の Coq 名だけで空振り → S11 の descriptive 名 machinery を見落とし。
本 session 4 度目の同型 miss)。S11 (11,767 行) は §9 の大半を既に形式化済:

**既存 (verify-first で確認)**:
- **dichotomy**: `clifford_dichotomy` (S11:6668) = `Nonempty (CliffordCaseAData chars) ∨ Nonempty (CliffordCaseBData chars)` = Peterfalvi (9.7) の Galois/非Galois 分岐。`chiefFactor_clifford_U_dichotomy` から導出済。
- **Galois branch の uniform degree** (これが決定的): `caseB_character_counts` (S11:11709) conjunct (a) =
  `∀ φ ∈ 𝒮(H₀C'), φ 1 = q·u` を **`caseB_degree_qu` (S11:7584) で証明済**。→ Galois branch は uniform degree `qu`。
- **非Galois branch**: `CliffordCaseAData` (S11:2608、Clifford 整数 `a`=`|U:C_U(H₁)|` pin 込み) + `caseA_character_counts`
  (S11:11661)。後者の degree-`qa` 下界 count (= Coq `lb_Sqa`) は **conjunct 4 が `sorry` (S11:11691)**、`caseA_exists_irreducible_source_degree_qa` (S11:6131) に依存。
- **coherence engine**: `coherentEqualDegree_fromDade` (S07_Coherence:6090) / `coherent_subset_of_constant_degree` (landed)。

**⟹ (9.11) coherence の honest 実体**: `coherent_H0C_commutator` (sibleyTarget_H0C 経由) を、`hG` を取る新定理で
`clifford_dichotomy` case-split して置換:
- **Galois**: `caseB_character_counts.1` (uniform `qu`) → engine。**残 = §9 family の Dade/subcoherent hypothesis**。
- **非Galois**: `coherentPairChain` fold + squeeze (全 landed) + `lb_Sqa` count (S11:11691 の sorry)。

**唯一の共通 structural gap = §9 induced family (`𝒮(H₀C')`, τ=Ind) の Dade/subcoherent hypothesis**。
`coherentEqualDegree_fromDade` は `S04.Hypothesis` (Dade hyp) を要し τ を構成する。type-P Dade datum は S12
`Hypothesis` (§10) が `dadeData.dade` として持つ (`fullDadeIsometryData hyp.hconj` で Dade isometry 構成、
S13_SixTwoBridge で多用)。`Section11CharacterData.tau` は bare `IntegralCharacterMap`。→ **次 build**: §9
`Section11CharacterData` に type-P `dadeData` を接続する (or §9 subcoherence を直接 exhibit) → Galois branch を
`coherentEqualDegree_fromDade` で close → 非Galois branch を pair-chain で。

**consumers**: `coherent_H0C_commutator` は S15 (b, `coherent_H0Cprime_S`) と S12_MaximalIII_IV_V:4049 (c) が使用。
→ 新 honest 定理を建て **b の S15 のみ re-point** (c の file signature は触らない、territorial)。c にも adopt を後で flag。

次 iteration: §9 Dade-datum 接続を正面 build (Galois branch を close 目標)。lane a (10.7) も同一 §9 coherence 依存。

## 2026-07-06 更新 #8 (lane b) — ★★定義的 crux 確定: (13.3) coherence の底 = §9/S-instance Dade subcoherence (13.2.e Dade isometry 基盤)

更新 #7 の「§9 family の Dade/subcoherent hypothesis を build → Galois branch close」を掘り下げ、
crux を定義的に確定。verify-first で以下を確認:
- **S-instance の τ は placeholder**: S15 `Hypothesis` (S15:98) は `tauS : IntegralCharacterMap` を
  **bare で持ち** (`tauS_eq_induction : Prop` の placeholder のみ)、**Dade isometry でない**。`dadeData` field なし
  (S12 `Hypothesis` は `dadeData.dade` を持つが S15 は持たない)。
- **§9/S-instance Dade isometry (`FTtypeP_coh_base`/`FTtypeP_subcoherent` analogue) は grep 皆無** = 真に不在。
- **per-step pair-chain data `sixTwoDecompositionData` (S13:814) は存在するが M-instance 用** (`hyp.dadeData.dade`、
  type-P maximal M の Dade context)。S-instance には未接続。
- sSet family 基本性質 (conj-closed/no-real/orthogonal) も named lemma 不在 (`sSet_subset_ZIrr` S11:1636 のみ);
  ただし `induce_eq_induce_iff_conj` (distinct-orbit ⟹ distinct-induced) 機構は在る。

**⟹ (13.3) `coherent_H0Cprime_S` の honest 再grounding の底 = (13.2.e) S-instance Dade isometry
`τ = Ind_S^G is a Dade isometry` + それに載る §9 subcoherence**。これが唯一の foundational gate。
その上は全 ready/landed: squeeze arithmetic (全 landed)・`clifford_dichotomy` (S11:6668)・Galois uniform
degree `caseB_character_counts.1` (S11:11712)・`irrSubcoherent` (5.3.a assembler, landed)・
`coherentPairChain` engine (S07:4907)・`coherent_subset_of_constant_degree` (landed)。

**次 build = (13.2.e) S-instance Dade isometry (foundational、substantial、lane-b (13.x) territory)**。
sSet conj-closure 等の Dade-independent 小片を先に建てても subcoherence は Dade isometry で gated ゆえ
scaffold になる → 底の Dade isometry を正面 build する (難所回避しない、CLAUDE.md)。upstream = (13.2) の
S/T Dade 構成。lane a (10.7) は M-instance 側で `sixTwoDecompositionData` を既に持つため S-instance とは別 path。

## 2026-07-06 更新 #9 (lane b) — ★★★honest path 確定 (de-risked): P2 Dade = type-I ASet bridge (9008 Option A、pieces 存在)

更新 #8 の crux「(13.2.e) S-instance Dade isometry」を verify-first で更に掘り、**honest な buildable path
を確定** (本 session 5 度目の verify-first 的中):

- **type-P Dade 構成は P1 限定**: `dadeSupportHypothesisData_typePA0_of_isTypeP1` (S10:2402) は `IsTypeP1`
  (types III/IV/V) 前提。docstring が明記: **P2 (type II) の `typePA=(S')#` 上の Dade support は
  false-as-stated** (issue **9008** closed: mmd OCR で `M_s#`→`M#` 化けた over-claim、consumer 0 の phantom)。
  S-instance S は **type-P2** (`S_typeP2`) ゆえ phantom を埋めてはいけない。
- **正しい A(S) = ⋃_{x∈S_σ#} C_{S'}(x)#** (9008: `(S')#` から U# Frobenius 補元を除外、S_σ=S_F=H)。
  **9008 Option A: 「P₂ escape は type-I ASet bridge に還元」**。
- **type-I ASet Dade 構成は既存**: `DadeSupportHypothesisData M (typeIA M data)` (S10:2066、`Nonempty` で構成済)。
  → honest な S-instance Dade isometry は **type-I ASet 構成を S_σ#=S_F# 上で instantiate** して得る (phantom でない)。
- `sibleyTarget_H0C` (unsound workaround) は正にこの P2 Dade gap の穴埋めだった。

**⟹ honest build path (de-risked, pieces 存在)**:
1. S-instance の type-P 構造 data (`Sdata`/`TypePData S`) を carrier (§16、issue 4010 closed で IsTypeP2 着地済) から取得。
2. 正しい A(S) を type-I ASet (`typeIA` over S_σ#=S_F#) で構成。
3. `DadeSupportHypothesisData S A(S)` を type-I ASet 構成で得る → `dade : S04.Hypothesis G A(S) S`。
4. `coherentEqualDegree_fromDade` に Galois uniform degree (`caseB_character_counts.1`) を食わせ Galois branch close、
   非Galois は pair-chain。→ `irrSubcoherent` に Dade + 既 landed の hconj (`sSet_closedUnderConjugate`) + hreal/hortho。

次 build = 上記 1-3 (S-instance P2 Dade via type-I ASet bridge)。substantial だが phantom でなく pieces 存在。
残 Dade-independent input: hreal (`HasNoRealCharacters` S03:60 + odd-order)、hortho (`inner_induce_eq_zero_of_not_conj`)。

## 2026-07-06 更新 #10 (lane b) — ★★★★(13.2.e) foundation LANDED: honest P2 Dade support (commit fd5ccff9)

更新 #9 の crux「S-instance P2 Dade isometry を type-I ASet bridge で構成」を **landed** (subagent + 検証)。
6 iteration の drilling の到達点。

**landed (S15_SAndT_Setup.lean、+267 行、commit fd5ccff9)**:
- honest support `A(S) = ⋃_{x∈S_σ#} C_{S'}(x)# = centralizerSupport (sharpSubgroup (Msigma S)) (derivedInG S)`
  (9008-correct、phantom `typePA=(S')#` でない。A1=S_σ# では不足 — (C')#⊄S_σ#、(C')#⊆A(S) 検証済)。
- 4 substantive P2 lemma (`_subset_ASet` bridge / `coprime_FT_signalizer...` (8.13.c2) / `_subset_hatMsigma` /
  `_conj_mem`) は **axiom-clean** (標準3公理のみ)。
- `dadeSupportHypothesisData_honestTypeP2ASet (hP2 : IsTypeP2 M) : Nonempty (DadeSupportHypothesisData M (A(S)))`
  = (13.2.e) 基盤、`.dade : S04.Hypothesis G (A(S)) M` を産む。
- **sorryAx provenance 検証済 (honest)**: top-level は sorryAx を持つが pre-existing shared BG §16 Theorem II
  pins (`theoremII_tame_embedding`/`mem_sigmaSharp_of_mem_aSet_of_escape`) からの inheritance で、accepted
  on-path `dadeSupportHypotheses_typeI` と **exact parity** (#print axioms 一致)。lane-b 導入 sorry 0。
- enabler: `typeP2_exists_matched_kappa_hall_pair` (S16:1319)。S10/S11/S12 無改変。build GREEN 3932。

**残 wiring (次 iteration、全て pieces 存在)**:
1. `Hypothesis`-level wrapper: 構成を `hyp.S`/`hyp.S_typeP2`/`hyp.S_maximal` に instantiate → `hyp` に
   concrete Dade hypothesis for S。
2. Dade-independent inputs 残: `hreal` (`HasNoRealCharacters` S03:60 + odd-order)、`hortho`
   (`inner_induce_eq_zero_of_not_conj` CliffordDecomposition:509)。hconj は landed (b8a37625)。
3. `irrSubcoherent` で S07.Hypothesis 組成 (Dade + hconj/hreal/hortho) → §9 subcoherence。
4. `clifford_dichotomy` (S11:6668) case-split: Galois = `caseB_character_counts.1` uniform degree +
   `coherentEqualDegree_fromDade` / `coherent_subset_of_constant_degree`、非Galois = pair-chain + squeeze (landed)。
5. `coherent_H0Cprime_S` (S15:572) を上記 honest route に re-point (現 sibleyTarget_H0C 経由を置換; ordering
   注意 — 構成 746 が 572 より後ゆえ、re-grounding は new def or 構成を前方移動)。lane a (10.7) も同一 (9.11) coherence。

## 2026-07-06 更新 #11 (lane b) — ★★★★★残 wiring step 1+2 LANDED: dadeHypS + hortho/hreal (Dade-independent inputs 完備)

更新 #10 が示した「残 wiring (次 iteration、全て pieces 存在)」の **step 1 + step 2 の Dade-independent 部分**を landed:

- **step 1**: `Hypothesis.dadeHypS` (S15_SAndT_Setup、commit 7dac2e77) —
  `dadeSupportHypothesisData_honestTypeP2ASet hG hyp.S_maximal hyp.S_typeP2 |>.some.dade`
  で S-instance の concrete `S04.Hypothesis G (A(S)) hyp.S` を Hypothesis レベルで取得。
  `.fullDadeIsometryData` で Dade isometry `τ = Ind_S^G` を materialise する底。
  sorry-provenance = dadeSupportHypothesisData_honestTypeP2ASet と exact parity (lane-b 導入 sorry 0)。
- **step 2 (Dade-independent inputs 全完備)**: `sSet_pairwiseOrthogonal` (hortho) + `sSet_hasNoRealCharacters`
  (hreal) landed (commit 589880fe、**#print axioms = 標準3公理のみ、sorryAx 無**)。hconj
  (`sSet_closedUnderConjugate`) は既 landed (b8a37625)。⟹ **irrSubcoherent が要る 3 つの Dade-independent
  家族性 hconj/hreal/hortho が全て揃った**。
  - 技術: induceHU が bake する `Fintype.ofFinite`/`invertibleOfNonzero` は `S12.FiniteInduce` scoped
    instance と一致 → `open scoped OddOrder.Peterfalvi.S12.FiniteInduce` 下で `induceHU = ClassFunction.induce`
    が定義的還元 → 一般 `inducedKernelFamily_pairwise_orthogonal`/`_hasNoRealCharacters` (S08_SixTwoGeneral)
    の 𝒮-instance として convert/bridge 不要でクリーンに証明。

**⟹ 残る唯一の genuine crux = per-member R-datum**: `irrSubcoherent (τ) (A) (Rdatum) hconj hreal hortho hiso`
のうち、揃っていないのは **(a) `Rdatum : ∀ χ ∈ 𝒮, CharacterDifferenceImage τ χ`** (各 member `Ind χ` に対し
`τ(χ − χ̄)` を 2 既約の signed difference として与える deep family-specific data、Coq PFsection5 の R-datum)
と **(b) `hiso`** (`τ = Ind_S^G` の difference 上 isometry、`dadeHypS.fullDadeIsometryData` の `inner_eq`
S04:3821 から取る) の 2 点。

**次 build (step 3-5)**:
1. `dadeHypS.fullDadeIsometryData` (要 `HConjInvariant` of A(S)) → Dade isometry `τ` + `hiso`。
2. per-member R-datum を 𝒮 に対して構築 (S08 case-B の `sMember_degreeSqNormBound...` / §9 induced-family
   witnesses の pattern; **これが残る genuine deep content**)。
3. `irrSubcoherent τ (A(S)) Rdatum hconj hreal hortho hiso` → `S07.Hypothesis` (§9 subcoherence)。
4. `clifford_dichotomy` (S11:6668) case-split: Galois = `caseB_character_counts.1` uniform degree +
   `coherentEqualDegree_fromDade`/`coherent_subset_of_constant_degree`、非Galois = `coherentPairChain` +
   squeeze (全 landed)。
5. `coherent_H0Cprime_S` (S15_SAndT_Setup:887) を上記 honest route に re-point (現 `sibleyTarget_H0C` 経由置換;
   ordering 注意)。lane a (10.7) も同一 (9.11) coherence。

hconj/hreal/hortho の Dade-independent 三点が揃ったので、次 iteration は step 1 の `fullDadeIsometryData`
配線 + R-datum 構築に正面着手する (R-datum が残る唯一の deep crux、difficulty は着手基準でない CLAUDE.md)。
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

   **✅ RESOLVED (2026-07-06, hub 調査 + ユーザー裁可)**: 2 subagent + Coq trace で決着。**両診断とも
   別の層を指した talking-past** — lane-b「S06 が residue 所有」は誤り (S06 は既約グリッドのみ、
   residue 二分律・cyclicTIiso なし)、lane-a「grep 0」は半分誤り (`primeTIred` は PrimeTIResidue.lean
   内に存在、真に 0 は §5/§8 coherence upgrade)。**Coq: (10.7) は `primeTIred` を transitively 必要**
   (residue = coherence upgrade の前提部品)。⟹ **PrimeTIResidue.lean は KEEP** (§10+§13 共有基盤)、
   **9014 OPEN 維持**、mu2Grid は削除でなく PrimeTIResidue へ移設。詳細裁定 = **issue 9014 の HUB RULING**。
   lane-b の held merge は「PrimeTIResidue 削除を含めない + mu2Grid を S05 から PrimeTIResidue へ移設 +
   9014 を close しない」に restructure 要 (S07_Subcoherent carve-out・S15:629 witness closure は不変)。

## 2026-07-06 更新 #12 (lane b) — R-datum route 確定: dadeCharacterDifferenceImageOfDiff + hconj landed

constructor (9014) 完了後、S15 R-datum (coherent_H0Cprime_S 再grounding の残 crux) を精査:

- **R-datum の一般 constructor は存在**: `S07.dadeCharacterDifferenceImageOfDiff` (S07_Coherence:5603) —
  `(hyp : S04.Hypothesis) (hconj) (χ : IrreducibleCharacter L) (hreal : ¬IsReal χ) (hdiffsupp : (χ̄-χ).support ⊆ supportInSubgroup A L)` から
  `CharacterDifferenceImage τ χ` (= `τ(χ-χ̄)=±(μ-ν)`) を産む。S14 の R1cdi (S14:744) が同 pattern で使用。
- **揃った入力**: dadeHypS (S04.Hypothesis, landed) / **dadeHypS_hconj (hconj, landed 更新 #12)** /
  sSet_hasNoRealCharacters (hreal, landed) / τ+hiso = `dadeHypS.fullDadeIsometryData dadeHypS_hconj`。
- **残 R-datum 入力 2 点**: (a) **family member の irreducibility** — dadeCharacterDifferenceImageOfDiff は
  `χ : IrreducibleCharacter L` を要す。𝒮={Ind ξ} の member が既約か要確認 (residue Ind は reducible=μ_j ゆえ
  𝒮 全体は非既約混在の可能性 → subcoherence family は既約 constituent か既約 subfamily の要精査)。
  (b) **hdiffsupp** — support(φ̄-φ) ⊆ supportInSubgroup A(S) (A(S)=honestTypeP2ASet、構造的)。
- **その後**: R-datum → `irrSubcoherent τ A(S) Rdatum hconj hreal hortho hiso` → S07.Hypothesis →
  clifford_dichotomy case-split (Galois=caseB uniform degree + coherentEqualDegree_fromDade / 非Galois=pair-chain) →
  coherent_H0Cprime_S を honest route へ re-point。

次 = (a) subcoherence family の既約性を精査 (𝒮 の member 既約性 or 既約 subfamily の特定) + (b) hdiffsupp。
これが R-datum の残 genuine content。

## 2026-07-06 更新 #13 (lane b) — ★重要訂正: 𝒮 は mixed family (p−1 reducible residues)、coherence は full (9.11)

更新 #12 の「coherentEqualDegree_fromDade で直接」は楽観的すぎた。verify-first で訂正:

- **`coherentEqualDegree_fromDade` (S07:6090)** は `χ : Fin n → IrreducibleCharacter L` の
  **uniform-degree 既約** family を要す (Dade + hconj + hsuppdiff + h1notA から coherence を内部生成、
  別途 R-datum/irrSubcoherent 不要)。← Galois uniform 既約 subfamily には直接使える。
- **但し 𝒮(H₀C') は mixed**: `{φ ∈ sOf | ¬IsIrreducible φ}.ncard = p−1` (S11:7160/7306/8225) —
  ちょうど **p−1 個の reducible member (= residue induction μ_j, j≠0)** + 残り既約。∴ 𝒮 全体に
  coherentEqualDegree_fromDade は適用不可。honest coherence = **full (9.11) subcoherent + pair-chain
  induction** (mixed family を扱う、reducible residues を別処理)。
- **connection**: 𝒮 の reducible members = prime-TI residues μ_j = 本 session で構成した
  PrimeTIResidueData/prTIres_irr_cases が記述するもの。S-instance の 𝒮 reducible 部 ↔ prime-TI residue theory。

**揃った input** (coherence 用): dadeHypS / dadeHypS_hconj (更新 #12) / **h1notA (honestTypeP2ASet_one_not_mem, landed 更新 #13)** /
sSet_hasNoRealCharacters / hortho。**残**: (a) uniform 既約 subfamily の特定 (𝒮 の既約部、degree qu) +
その Fin n enumeration、(b) hsuppdiff (φ_j−φ_0 の support ⊆ A(S))、(c) reducible residues の別処理 (pair-chain)、
(d) coherent_H0Cprime_S を組んで re-point。genuine な (9.11) mixed-family coherence、multi-session。

## 2026-07-06 更新 #14 (lane b) — hdiffsupp 構造確定 + (C')^#⊆A(S) bridge landed

R1_diffsupp (S14:710) template を精査 → hdiffsupp の構造確定:
- **hdiffsupp** = `(φ.conj−φ).support ⊆ supportInSubgroup A(S) S`。R1_diffsupp の鍵入力は
  `data.supported : support φ ⊆ A ∪ {1}` (family member が A∪{1} 外で消える)。
- **2 support の区別**: A(S)=honestTypeP2ASet (Dade support、R-datum の support hyp) vs
  (C')^#=cprimeSharpS (§9 coherence support、H0CprimeSupport)。**(C')^# ⊆ A(S)**。
- **landed 更新 #14**: `cprimeSharpS_subset_supportA` ((C')^# ⊆ supportInSubgroup A(S) S、
  sorry-free)。= hdiffsupp の「A(S) 側」半分。
- **残 hdiffsupp 半分 (deeper)**: `support(Ind ξ) ⊆ (C')^# ∪ {1}` (family member 𝒮 が
  (C')^# 外で消える)。これは induced character Ind_{HU}^S ξ の support 構造 = §9 family の
  vanishing 性 (genuine、要 S-instance 構造)。

**R-datum inputs 現状**: dadeHypS / dadeHypS_hconj / h1notA / sSet_hasNoRealCharacters / hortho /
**cprimeSharpS_subset_supportA (hdiffsupp A(S)側)**。残: (a) 𝒮 member irreducibility (mixed family
の既約部特定)、(b) support(Ind ξ)⊆(C')^#∪{1} (hdiffsupp 残半分)、(c) mixed-family (9.11) induction。
次 = (b) の family vanishing 性 or (a) の既約部特定。genuine (9.11)、multi-session。

## 2026-07-06 更新 #15 (lane b, subagent 検証) — ★★(9.11) route 確定 + update #14 訂正 + 最後の gap 特定

background subagent が Coq PFsection9 `Ptype_core_coherence` (:1484) + repo engine を verify-first 精査、確定:

**(A) 実 (9.11) route (mixed family は subcoherent level で処理)**:
- Coq は per-member irrSubcoherent を全 𝒮 に適用しない。`subcoherent (S_ H0C') tau R` を **variable-length R-data**
  で供給 (既約=2元、reducible residue μ_j=2w₁元、cyclic-TI sigma 由来)。producer=`prDade_subcoherent`
  (PFsection5:683) が irr_subcoherent の 2元 R-data (既約部) と explicit Rmu (reducible部) を glue。
  **reducibles は irreducible-only producer に渡さない — subcoherent supply に乗る**。
- Galois: 全 𝒮 uniform-degree → `coherent_subset_of_constant_degree` (landed) 直接。
- 非Galois: base S1 (uniform 既約) → 同 + pair-adjoining induction (`coherentPairChain` S07:4907 + 済 squeeze)。
  reducible μ_j は S3 の q·u block として `coherent_subset_of_constant_degree` で処理。
- **per-member R-datum (dadeCharacterDifferenceImageOfDiff) は route 上、但し既約 member 限定**。

**(B) update #14 訂正**: hdiffsupp の target は **A(S)∪{1} 直接** (NOT (C')^#)。Coq `prDade_Ind_irr_on`
= `S_ H0C' ⊆ 'CF(M, 1|:'A(M))` (PFsection9:1991)。⟹ **`cprimeSharpS_subset_supportA` (更新#14 landed) は
true だが hdiffsupp route 上でない** (off-route、有効な構造 fact ではある)。

**(C) 最後の genuine gap = S-instance (4.7) induced-support lemma (Dade-free、tractable)**:
`∀ ξ∈xiSet, Supp(Ind ξ) ⊆ supportInSubgroup A(S) S ∪ {1}`。repo に既存の (4.7)
= `S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel` (S06_CertainTypeSupport:131)、
Dade-free core = `mem_A_of_apply_ne_zero_of_covers` (S06:49、covering `A_covers` のみ要、Dade isometry 不要)。
S-instance の構造同定: K=huSub=derivedInG S (=HU=S', S11:1494 (9.2))、subH=Msigma S=P (P_eq_SF)、
A(S)=centralizerSupport(sharpSubgroup(Msigma S))(derivedInG S) ⟹ A_covers は essentially definitional
(witness x=h)。`support_induce_subset_conjugatesIntoSet` (InducedCharacter:424) + `honestTypeP2ASet_conj_mem`
(landed、L_normalizes_A の代替) で induced-form を mirror。

**⟹ 残 = (i) 上記 (4.7) lemma (最後の構造 gap、substantial だが全 piece 済) → (ii) per-member hdiffsupp
→ dadeCharacterDifferenceImageOfDiff → irrSubcoherent (既約部) → S07.Hypothesis → (iii) clifford_dichotomy
case-split + coherent_subset_of_constant_degree + coherentPairChain で NEW IsCoherent 構築 → (iv)
coherent_H0Cprime_S を re-point (coherent_H0C_commutator は触らない、lane-c 共有 territorial)。**
subagent が (i) を tractable と確認 (全 piece 存在) だが multi-lemma wiring ゆえ本 session 未 build。次 = (i)。

## 2026-07-06 更新 #16 (lane b, subagent 検証) — ★★重要訂正: 「all inputs landed」は誤り、CORE keystone 2 つが未 build

assembly subagent が verify-first で確定 (honest STOP、sorry-hoist せず tree clean 保持)。更新 #12-15 の
「残 = wiring/assembly」は楽観的すぎた。coherent_H0Cprime_S の goal
`IsCoherent indS sSet (C')^#` (全 mixed family、plain induction、(C')^# support) に対し、
**genuine な CORE keystone が 2 つ未 build**:

**Blocker 1 — 全 mixed-family subcoherence producer (prDade_subcoherent-analog) 不在**:
- `.S = sSet` は全 mixed family (caseB でも `{φ∈SOf|¬Irr}.ncard = p−1` の reducible residues 含む)。
- `irrSubcoherent` は `∀χ∈S, CharacterDifferenceImage τ χ` を要すが、`CharacterDifferenceImage` は
  **single (mu,nu) pair** 構造。reducible residue μ_j の difference image は Coq Rmu = **2w₁ 元**で
  single-pair に収まらない ⟹ irrSubcoherent は構造的に mixed family を扱えない。
- `coherent_subset_of_constant_degree`/`coherentEqualDegree_fromDade` は uniform-degree **subset** のみ。
- Coq の mixed-family glue = `prDade_subcoherent` (variable-length R: 既約 2元 + reducible Rmu) は
  **repo 不在** (S07_Subcoherent:322 が "assemble せよ" と TODO 記載のみ、producer 未 build)。
  ⟹ 全 sSet の subcoherent/coherence を組む keystone が要 build (prime-TI residue machinery で Rmu を組む)。

**Blocker 2 — (C')^# 上の dade=Ind bridge 不在**:
- 下流 `tau1S_apply_induce_sub` (S15:1795) は `extension φ = Ind_S^G φ` を intrinsic に要求。
  だが coherence engine が産む extension は **Dade map** 一致 (Dade map = (2.10) Möbius sum、plain
  induction と非defeq、nontrivial stabilizer `ftSupportKernel S A(S) a`)。
- repo の dade=Ind bridge = `H_sharp_tau_eq_induce` (S15:2603) / `dadeMap_eq_induce_of_supported_on_trivial_H`
  (S14:2104) は **trivial stabilizer (H^#, H a=⊥)** 前提。(C')^# + dadeHypS (nontrivial stabilizer) 版は不在。
  ⟹ type-P2 で Dade stabilizers が (C')^# supported span 上で消えることを示す genuine (2.2)/(4.7) TI content が要。

**非-blocker**: (C')^# ⊆ A(S) は済 (cprimeSharpS_subset_supportA)、per-irreducible-member R-datum は構成可
(但し Blocker 1 で全 family に compose 不可)。

**⟹ 状態訂正**: landed inputs (dadeHypS/hconj/hreal/hortho/hdiffsupp/(4.7)) は本物だが、coherent_H0Cprime_S
を閉じるには CORE keystone 2 つ (Blocker 1 mixed-family coherence 機構 + Blocker 2 (C')^# dade=Ind bridge) が
残る。両者 genuine multi-lemma FT content (wiring でない)。S15 coherence は genuine multi-session frontier。
次 = Blocker 1 (mixed-family coherence 機構、prime-TI residue Rmu 活用) を優先 (Blocker 2 より central)。

## 2026-07-06 更新 #17 (lane b, subagent 検証) — ★★Blocker 1 訂正: mixed family は coherentPairChain で扱える (新構造 不要)

更新 #16 の Blocker 1 (「全 mixed-family subcoherent 構造が要 build」) は verify-first で**部分的に誤り**と判明:

- **whole-family subcoherent は不要**: repo の per-step adjoining engine
  `retarget_isCoherent_of_decompositions_and_memberFamily` (S07_Coherence:4083) / `coherentPairChain`
  (:4907) は whole-family subcoherent でなく **`IsCoherent` + per-member `CharacterPsiDecomposition`** を
  consume。`CharacterPsiDecomposition.imageFamily : OrthonormalCharacterImageFamily` は
  `imageSet : Finset` = **可変長** (:780)。⟹ reducible residue μ_j は 2w₁-元 imageFamily で
  pair-chain に adjoin 可 (2-元 CharacterDifferenceImage に収める必要なし)。**新構造 build 不要**。
- **Coq skeleton 一致** (PFsection9:1484-1660): S1 uniform base (`uniform_degree_coherence`) →
  `extend_coherent` で S3 の conjugate pairs を degree 順に adjoin (elim: nS 帰納)。
- **repo route (3 stage、engine 全 landed)**: base = `coherent_subset_of_constant_degree` (irrSubcoherent +
  per-member CharacterDifferenceImage) on S1={χ∈sSet|χ(1)=q·a} / induction = `coherentPairChain`
  (reducibles as CharacterPsiDecomposition) / norm chain = landed (Snorm/sumnS/xAdjoinStepW)。
- **注意**: `coherentUnion_of_glued` (S07:4508) は (6.8) two-block glue で shape 違い、(9.11) には不適。

**landed 更新 #17**: `oddCardS` + `sSet_member_differenceImage` (per-irreducible-member R-datum、上記 base の入力)。

**⟹ Blocker 1 は「新構造」でなく「既存 coherentPairChain engine を §9 sSet に wire」= substantial だが
tractable assembly**。Blocker 2 ((C')^# dade=Ind bridge、下流 tau1S_apply_induce 用) は依然 separate。
次 = irreducible sub-family の S07.Hypothesis (irrSubcoherent、sSet_member_differenceImage を Rdatum に
wrap、per-member irreducibility を prTIres_irr_dichotomy/inertia から) → coherent_subset_of_constant_degree
で S1 base coherence。

## 2026-07-06 更新 #18 (lane b) — ★(9.11) base subcoherence LANDED (sSetIrrDeg_subcoherent) + degree-parametrize 訂正

honest 第一段 landed: `sSetIrrDeg_subcoherent : S07.Hypothesis (sSetIrrDeg d) (supportInSubgroup A(S) S)`
(uniform-degree 既約 subfamily `sSetIrrDeg d = {φ∈sSet|IsIrr φ ∧ φ(1)=d}` の subcoherence)。

**★scope 訂正 (更新 #17→#18)**: 「全 irreducible subfamily で S07.Hypothesis」は不整合 — irreducible member
`Ind ξ` は degree `q·ξ(1)` で mixed-degree、S07.Hypothesis の isometry field は uniform degree を構造的に要す
(hiso = member diff の A-supportedness = `a(1)=b(1)`)。⟹ **degree `d` で parametrize** が正。base case=q·a、
Galois=q·u。hiso は `dadeIntegralCharacterMap_inner_eq_on_supported_span` (A-supported diff で成立)。

**残 (次段)**:
1. **S1 base coherence** = `coherent_subset_of_constant_degree` を sSetIrrDeg (q·a) に適用。要 d=q·a の
   ≥2-membership (`caseA_exists_irreducible_source_degree_qa`、S11:11691 で sorried per 更新#7) + h1A (landed)。
2. **coherentPairChain induction** で S3 の conjugate pairs を adjoin (reducibles as CharacterPsiDecomposition)。
3. **Blocker 2**: (C')^# 上の dade=Ind bridge (下流 tau1S_apply_induce 用)。
4. NEW IsCoherent → coherent_H0Cprime_S re-point。

subcoherence structure 自体 (genuine deliverable) は built & honest。次 = S1 base coherence (要 degree 機構)。

## 2026-07-06 更新 #19 (lane b) — S1 base coherence LANDED (sSetIrrDeg_coherent)、≥2 count は §9(9.8.d) gate

`sSetIrrDeg_coherent : Nonempty (IsCoherent τ (sSetIrrDeg d) A)` landed (base 段の IsCoherent、
sSetIrrDeg_subcoherent → coherent_subset_of_constant_degree)。8/9 hypotheses は landed で internal
discharge、**h2 (2≤ncard) と hd0 (d≠0) は parameter 露出** (honest deferral)。

**★≥2 count は genuine upstream gate**: `2 ≤ (sSetIrrDeg d).ncard` (2 distinct degree-d 既約 member) の
補題は repo 不在。degree-qa source (caseA_exists_irreducible_source_degree_qa S11:6437 + M-induction 版
S11:12250) は共に sorry-free だが **existence 1 member のみ**、count ≥2 は §9 (9.8.d) counting content で
未形式化。h2 露出でこの upstream fact を caller に defer (def は sorry-free)。

**S15 coherence keystone の現状 (本 session の到達点)**:
- ✅ landed: dadeHypS/hconj/hreal/hortho/hdiffsupp/(4.7) support/per-member R-datum
  (sSet_member_differenceImage)/base subcoherence (sSetIrrDeg_subcoherent)/base coherence (sSetIrrDeg_coherent)。
- 🔲 残 (genuine multi-session): (a) §9 (9.8.d) ≥2 count (h2 の供給、upstream)、
  (b) coherentPairChain induction (S3 conjugate pairs adjoin、reducibles as CharacterPsiDecomposition) で
  全 sSet coherence へ、(c) Blocker 2 ((C')^# dade=Ind bridge、下流 tau1S_apply_induce 用、genuine TI content)、
  (d) NEW IsCoherent 組成 → coherent_H0Cprime_S re-point。
route は完全確定・engine 全 landed、残は上記 4 点 (partly gated on 他レーン §9 sorried lemma + Blocker 2 TI)。

## 2026-07-06 更新 #20 (lane b, subagent VERIFY-FIRST) — ★★Blocker 2 誤診断訂正: (C')^# = ∅ (C'=[C,C]=⊥, type-P₂)

更新 #16/#19 の Blocker 2 (「(C')^# 上 dade=Ind bridge = genuine deep TI content」) は **verify-first で
誤り** と判明。Coq `FTtypeP_facts` (PFsection13.v:221) の `derG1P (abelianS _ cUU)` を repo で再現:

**LANDED (sorry-free, axioms = [propext, Classical.choice, Quot.sound]、S15 build green 3882 jobs)**:
- `Hypothesis.Cprime_eq_bot` (S15:~863): type-P₂ で `C' = [C,C] = ⊥`。`C ≤ U` (C_eq) + `U` abelian
  (`S_U_commutative` = BG 15.1(b)) ⟹ `C` abelian ⟹ `commutator ↥C = ⊥` ⟹ `derivedInG C = ⊥`。**hG 不要**
  (構造 field のみ)。dadeHypS より clean (§14 sorry-provenance を運ばない)。
- `Hypothesis.cprimeSharpS_eq_empty` (S15:~888): `C'=⊥` ⟹ `(C').subgroupOf S = ⊥` ⟹
  `cprimeSharpS = sharp({1}) = {1}\{1} = ∅`。

**⟹ Blocker 2 は誤枠組み**: `H0CprimeSupport = cprimeSharpS = ∅` (type-P₂)。
`zSupportedSpan 𝒮 ∅ = {0}` ⟹ `IsCoherent.extends_on_supported` は **∅-support 上 vacuous** (0 関数のみ)。
`(C')^#` 上で dade=Ind を要求する下流は無い。Blocker 2 が言う「(C')^# dade=Ind bridge」は不要。

**★但し本当の gap は別: `H0CprimeSupport = (C')^#` 自体が退化した support 選択**。Coq (13.2.d) の実 coherence
support は `S^#` (`coherent calS S^# tau`, PFsection13:197)。下流 `tau1S_apply_induce_sub` が要する
`tau1S(Ind θ − Ind θ')=Ind(...)` は等次数差 (H^#-supported, 1 で消える) 上で、Coq は
`Dtau1S`(coherent_with agreement on `Z[calS,S^#]`) + `H^# ⊆ A0(S)` 上 `tau=Ind` (normedTI `Dade_Ind`) で discharge
(PFsection13:1024-1028)。repo の `tau1S_ofHonest_extends_on_supported` は `H0CprimeSupport=(C')^#=∅` を使うため、
0 関数にしか効かず、等次数差 (≠0) に効かない。

**⟹ 修正すべきは (a) `mkSection11CharacterDataS_honest.H0CprimeSupport` を `(C')^#`→`S^#` (Coq 準拠) に変更、
かつ (b) `A(S)` 上 `dade=Ind` を確立** (これが本来の Blocker 2、Coq の `normedTI 'A0(S)` = `Dade_Ind` に対応)。
(b) は type-P₂ で `A(S)=honestTypeP2ASet S` が **TI-set かどうか**が crux — repo は escaping 分岐
(`dadeSupportHypothesisData_of_subset_escaping_sigmaSharp`, FT_signalizer nontrivial local subgroup) 経由で
構成しており、`IsTISubset.centralizer_le` が要求する「A(S) 全点 non-escaping」を満たすかは未検証。Coq は
`FTtypeP_facts` normedTI 証明 (PFsection13:224-238、`FTsupport_facts`+`typePF_exclusion`+type-1 Frobenius で
escaping 点の矛盾を導く) で TI 性を確立。⟹ 本物の残 = **`honestTypeP2ASet S` の TI-set 性** (or 等次数差が
非escaping 部分に supported: type-I `constituent_diff_support_subset_nonescaping` の type-P₂ 類推) を示し、
`dadeMap_eq_induce_of_supported_on_trivial_H` (S14:2104) を適用。これは genuine multi-lemma BG-§16 content。

**recommended path**: (1) H0CprimeSupport を S^# に変更 [small, but 要 downstream re-check] →
(2) `A(S)` dade=Ind: type-I 類推で「等次数 sSet 差は A(S)∖escaping に supported」を [Is]6.2 類推で示す
[genuine, S14 pattern] → (3) NEW `IsCoherent indS 𝒮 S^#` 組成 → coherent_H0Cprime_S re-point。

## 2026-07-06 更新 #21 (lane b, /loop) — ★(13.2.e) dade=Ind bridge LANDED (sInstance_dade_eq_induce_of_supported_trivial_H)

update #20 が「本当の残 gap」と特定した **A(S) 上 dade=Ind** の honest core piece を landed (commit cd6beac7):
- `Hypothesis.sInstance_dade_eq_induce_of_supported_trivial_H` (S15:848、+37、leaf GREEN 3882 jobs):
  type-P₂ S の (13.2.e) Dade isometry `dadeIntegralCharacterMap (dadeHypS)` が trivial-H sub-support
  `A₁ ⊆ A(S)` 上で `Ind_S^G` に一致。type-I `typeI_tau_eq_induce_of_supported_trivial_H` (S14:2125) の
  S-instance analogue、general `dadeMap_eq_induce_of_supported_on_trivial_H` (S14:2104) を dadeHypS で
  instantiate (`dadeIntegralCharacterMap_apply_of_support` → §4 `dadeMap` → step-3 bridge)。trivial-H facts
  (hA₁A/hA₁norm/hH₁/hf) は type-I 同様 hypotheses に defer。#print axioms の sorryAx は dadeHypS 由来のみ
  (proof body の sorry 導入 0、accepted BG §16 Theorem-II pins・on-path `dadeSupportHypotheses_typeI` と parity)。

**残る唯一の missing fact (trivial-H discharge を non-vacuous にする)** = **S-instance analogue of
`constituent_diff_support_subset_nonescaping` (S14:2235)**: §9 member differences が **non-escaping**
部 `A(S) ∖ escaping` に supported (現 `sSet_member_diffsupp` S15:1093 は full A(S) 止まり)。
type-I template (S14:2235-2278): x が escaping ⟹ escaping ⊆ σ-sharp
(`escaping_honestTypeP2ASet_mem_sigmaSharp` S15:650、既 landed) ⟹ そこで family 差が vanish
(type-I は `restrict_eq_of_mem_constituents` で H 上一致 → 差=0)。**S-instance の「差が σ-sharp=S_σ^#=P^#
上 vanish」= 残 genuine content** (family 差が P 上どう振る舞うかの構造)。A₁=A(S)∖escaping / hA₁norm / hH₁ は
mechanically 構成可 (H_eq_ftSupportKernel S10:675 + ftSupportKernel_eq_bot_of_not_escaping S10:600 +
honestTypeP2ASet_conj_mem S15:587 + escapingCentralizerSet_conj_mem S10:1259)。
次 = この non-escaping support 補題を build (or 差が P 上 vanish しないなら真の構造を named-report)。

## 2026-07-06 更新 #22 (lane b, /loop verify-first) — ★★★決定的訂正: #21 の non-escaping route は誤り、単一 gate = **A(S) が TI-set**

subagent が Rung 3 (§9 差が A(S)∖escaping に supported、type-I `constituent_diff_support_subset_nonescaping` 模倣) を
verify-first で **反証**: S-instance の差は **φ̄−φ** (単一 member の共役差、type-I の「1 つの χ の 2 constituents」でない)
ゆえ σ-sharp=H^# 上 vanish には **φ が H=S_σ 上 real** が要り、これは偽 (φ は non-real、φ,φ̄ は共通 source 無しの共役既約)。
⟹ #21 の「non-escaping support 補題」route は**構造的に閉じない**。Rungs 1-2 (A(S)∖escaping の S-invariance/trivial-H、
sorry-free だったが wrong-framing) は **revert 済** (uncommitted のまま drop)。

**★正しい route (code+Coq verify-first で確定)**: dade=Ind は **A(S)∖escaping 上の per-difference vanishing でなく、
A(S) 全体の TI-set 性**から来る (Coq `FTtypeP_facts` PFsection13.v:198/223: 結論(e)=`normedTI 'A0(S) ∧ {in CF(S,A0(S)),
tau=1 Ind}`、`suffices normedTI … apply: Dade_Ind`)。**repo に route-2 機構は既在**:
`S04.isDadeMap_induce_of_forall_H_eq_bot` (S14:2072、`∀a, H a=⊥` ⟹ Ind=dadeMap)、`induce_apply_eq_self_of_mem_tiSubset`
(S14:2025、TI-set 上 Ind self-value)、`S04.of_isTISubset` (S04:267) / `isTISubset_iff_exists_hypothesis_with_trivial_H`
(S04:314)。⟹ **iteration-1 の `sInstance_dade_eq_induce_of_supported_trivial_H` (cd6beac7) は ON-ROUTE**、
ただし **A₁ = A(S) 全体** (∖escaping でない) で instantiate: `hf` = §9 差の full-A(S) support は既 landed
(`sSet_member_diffsupp`)、`hH₁ : ∀a, dadeHypS.H a=⊥` が唯一の未証明入力。

**⟹ 単一 gate G2 = `IsTISubset (honestTypeP2ASet S) S`** (⟺ `∀a∈A(S), dadeHypS.H a=⊥` ⟺ A(S) に escaping 点なし)。
現 `dadeSupportHypothesisData_honestTypeP2ASet` は defensive な escaping 分岐 (S15:785 `_of_subset_escaping_sigmaSharp`)
で構成ゆえ H の trivial 性は未知。escaping 点は σ-sharp に confined (`escaping_honestTypeP2ASet_mem_sigmaSharp` S15:650、
既 landed) だが「escaping 点なし」は未証明。**= Coq `FTtypeP_facts` normedTI 証明 (PFsection13.v:223-234、
`normedTI_memJ_P` + escaping 点の `typePF_exclusion`∘`Frobenius_of_typeF` 矛盾) の port** = genuine BG-§13 content、substantial。

**残 2 gate (両 genuine、character_degree_analysis (13.3) が gate)**: **G1** = honest coherence の full mixed-family 拡張
(sSetIrrDeg_coherent base → coherentPairChain、tau=dade map の isometry route、subagent 確認どおり dade=Ind 不要;
≥2 count は §9(9.8.d) upstream sub-gate)。**G2** = A(S) TI-set (上記、bridge が A₁=A(S) で消費 → dade=Ind →
tau1S_apply_induce_sub)。G1+G2 で (13.3) の tau1S fields honest 化。**次 = G2 (A(S) TI、normedTI port)** を正面 build。

## 2026-07-06 更新 #23 (lane b, /loop) — ★★G2 (TI-set) は BG §15 Cor 15.9 (Sibley/FT package) に bottom out、multi-consumer gate

**Rung B (TI-set reduction) landed sorry-free (commit d375f39c、S15:878-931)**: dade=Ind on A(S) ⟸ `IsTISubset(A(S)) S`
⟸ no escaping。4 lemma (dadeHypS_H_eq_ftSupportKernel / forall_dadeHypS_H_eq_bot_of_{not_escaping,isTISubset} /
isTISubset_honestTypeP2ASet_iff_forall_dadeHypS_H_eq_bot 3-way 同値)、#axioms は dadeHypS 継承のみ。

**G2 core (IsTISubset の escaping-exclusion、Coq FTtypeP_facts (e) PFsection13.v:224-234 port) を subagent が trace**:
escaping a ⟹ σ-sharp (landed) ⟹ signalizer N (IsTypeF∨IsTypeP2、`signalizer_structure_of_mem_sigmaSharp` S16:271
sorry-free)。
- **case P2**: (S type-F)⟹¬type-P (`isTypeF_iff_not_isTypeP` S14:169 sorry-free) が要る。唯一の producer
  `exists_RData_escape_structure` (S16:5695) は **`centralizer_escape_final_local` (S15_MF:9407 = BG Cor 15.9,
  bare sorry, "Sibley/FT package for §16") 経由で sorryAx-tainted**。
- **case F**: `FTtype1_Frobenius` kernel-regularity analogue **不在** (repo type-F N は `frobenius_HU0` のみ、
  global Frobenius 無 — Coq FT-type-1 は BG type-F より narrow)。

**⟹ G2 (S-instance dade=Ind、tau1S_apply_induce_sub) は BG §15 Cor 15.9 (`centralizer_escape_final_local`) +
Thm 15.8 (`tau2_transfer_constraint` S15_MF:9397 bare sorry) + FTtype1_Frobenius analogue に gated**。deep BG
local-analysis (Sibley 1991)、**multi-consumer**: S16 `exists_RData_escape_structure` (BG side) + 本 Pf §13 coherence
(char side) が共に消費 ⟹ high-leverage cross-cluster gate。

**残 2 独立 gate**: **G1** = honest coherence の full-mixed-family 拡張 (sSetIrrDeg_coherent base → coherentPairChain、
tau=dade map の isometry route、**BG §15 に non-gated**、§9 (9.8.d) ≥2 count sub-gate のみ) / **G2** = 上記 BG §15。
**bridge (cd6beac7) + Rung B (d375f39c) で G2 の char-side wiring は完備、残 core は純 BG §15 群論**。
次判断: (a) BG §15 Cor 15.9 claim+build (upstream-most・multi-consumer) vs (b) G1 (in-cluster・§9-gated) — 9000 scan 後に決定。

## ⚖️ HUB RULING (2026-07-06 夕, レーン分担監査 + ユーザー裁可) — **§5-arith DONE、本 issue は BG §15 (9017) に収束**

分担監査で code-verified: **§5 subcoherence arithmetic は build 済** — item 1 `uniform_degree_coherence`
= `coherent_of_constant_degree` (S07_CoherenceConstantDegree:551) sorry-free、item 2 subcoherent =
`S07_Subcoherent.lean` (0 bare sorry、(9.11) Snorm/sumnS squeeze 全 landing)。**∴ 本 issue の §5 部は
実質完了**。残 2 gate の帰属を確定:

- **G2 (BG §15 Cor 15.9 / Thm 15.8)** = 真の cross-cluster bottleneck。**issue 9017 に移管、owner = lane b**
  (drift 追認、ユーザー裁可 2026-07-06)。本 issue 側は G2 の char-side wiring 完備 (bridge cd6beac7 +
  Rung B d375f39c) ゆえ、9017 の BG 群論が landing 次第 sorried-cite で dade=Ind が honest 化。
- **G1 (full-mixed-family coherence 拡張)** = b の in-cluster work (§9 (9.8.d) ≥2 count が唯一の sub-gate、
  BG §15 に non-gated)。b が正面から build。

⟹ 本 issue は「§5-arith 完了 + G2→9017 移管 + G1=b in-cluster」で整理。新規レーン割当不要 (a/b で消化)。

## ✅ 2026-07-07 (lane b): G2 CLOSED — A(S) TI-set (13.2.e normedTI) 実証明 (commit 76d1b27b)

9017 (BG Cor 15.9 sorry-free 化) の un-gate を受け、G2 wiring を完遂:
- **Rung C** `escaping_honestTypeP2ASet_eq_empty` (S15_SAndT_Setup): type-P₂ maximal の A(M) に
  escaping 点なし。Coq `FTtypeP_facts` (e) PFsection13.v:224-238 の port —
  escaping a ⟹ σ-sharp (8.13.b) ⟹ BG D(4) `exists_RData_escape_structure` (9017 で axiom-clean 化)
  の neighbour N で分岐: N type-P₂ ⟹ (D(4) tail) M type-F、M type-P₂ と矛盾 / N type-F ⟹
  Prop 16.1 dictionary + Pf (12.7) `typeI_frobenius` で N は kernel N_σ の Frobenius、
  Â_σ(N)-点 a は kernel regularity (Isaacs 6.4) で N_σ に落ち a ∉ N_σ と矛盾。
- **Hypothesis-level payoff**: `isTISubset_honestTypeP2ASet` (= normedTI TI 半分、G2 本体) +
  `forall_dadeHypS_H_eq_bot` + **`sInstance_dade_eq_induce`** (= isometry 半分、full-A(S) で
  dade = Ind_S^G — bridge cd6beac7 + Rung B d375f39c の唯一の未証明入力 hH₁ を放電)。
- 本体 sorry 導入 0。継承 sorryAx = (i) BG §16 Theorem-II pins (dadeHypS と exact parity、
  accepted)、(ii) Pf (12.7) の (12.8)-(12.16) machinery のみ (新規依存クラス)。

**⟹ (13.3) 残 = G1 のみ**: base `sSetIrrDeg_coherent` (landed) → coherentPairChain induction
(mixed family: reducible μ_j は CharacterPsiDecomposition、既約は conjugate pairs) + ≥2 count
sub-gate ((9.8.d)、S11:11691 sorried-cite 可) → NEW IsCoherent → `coherent_H0Cprime_S` re-point
→ CharacterDegreeData の tau1S 3 fields (extension= G1、差分上 Ind 一致 = G2 `sInstance_dade_eq_induce`
+ `sSet_member_diffsupp`)。SibleyTarget route (S15:2237) は G1+G2 完成時に置換・retire。

## 2026-07-08 更新 #24 (lane b, /loop 再開) — ★(9.11) port 着工: skeleton + 最初の §9 brick landed

**G1 の正体を確定**: (13.3) G1 = **Pf (9.11) `Ptype_core_coherence` の本体 port** (Coq PFsection9.v:1484-2227
精読 + 書籍 mmd 04.11 (9.11.1)-(9.11.8) 全読)。9016 HUB RULING で hY producer = b 確定済 → claim 済扱いで着工。

**構造 (書籍準拠)**: Clifford (9.7) 二分。case (b) = 全 member 次数 qu (`caseB_degree_qu` 済) → 一様次数
+ 混合ノルム (μ_j はノルム q) の adjoin。case (a) = maximality 帰納 — S₁ (次数 qa cut) → maximal coherent
conj-closed S₂ → S₃ ≠ ∅ なら (9.11.1) squeeze: strict 枝 = `xAdjoinStepW`(_k) 発火で maximality 矛盾 /
equality 枝 = 特殊配置 (a=(p-1)/2, C=U', S₂=S₁, |S₁|=2u/a, S₃ 全次数 qu) を (9.11.2)-(9.11.8) で反証
((9.11.2) 慣性論法 U₁∩U₁^w=C・u≤a² / (9.11.3) |S₄| count / (9.11.4) γ=Ind 1_{HU₁}, α=γ-ψ₁ ノルム /
(9.11.5) 算術矛盾 2^q>q+2 / (9.11.6)-(9.11.8) τ₁/τ₃ 直交性代数)。

**設計裁定 (lane a 1019 と非重複)**: (9.11) core は **Dade pair (S04.Hypothesis + hconj) パラメータ化**で
§9 world に build (per-member Dmem/hortho は入力として受ける — a の §12 部品 (columnBreakDa /
irrFamilyMemberDecomposition / R⊥R §12) と衝突しない; a の gate-2 hY 消費は S12→本 leaf の import が
必要になるため **本 leaf は S12/S13 を import しない** (循環回避、家族 fact は S11 直 or 入力)。

**landed (両 commit sorry-free, axiom-clean)**:
- d84ea453 (S07_Subcoherent): maximality skeleton 3 定理 — `exists_maximal_coherent_between` /
  `coherent_of_maximal_coherent_refuted` / `coherent_of_maximal_coherent_pair_refuted` (書籍 (9.11)
  冒頭の reduction; refuter は「S₃ nonempty + 全 pair adjoin 不能」の (9.11) 状況を受ける)。
- 1e178611 (S11_NineElevenCoherence 新設): `xiOf_H0Cprime_source_apply_one_le_u` (χ(1) ≤ u、書籍
  (9.11.1) 第1段落 / Coq lb01 内側) + member 形 `sOf_H0Cprime_apply_one_le_qu` (φ(1) ≤ qu)。

**次 (文書順)**: (i) 𝒮(H₀C') family facts (finite / S₁ = deg-qa cut の family 化)、(ii) (9.11.1) squeeze
assembly (lb0≤lb1 は上記 bound + a∣χ(1) [case (a) a_dv_XH0 = 要 port]、lb12/lb23/lb3S1'/lbS1'2 は
S07_Subcoherent 済部品 + §9 counting 接続)、(iii) strict 枝の member-data bundle (XAdjoinStepInputW
構成; S-instance 供給は S15 の sSetIrrDeg_subcoherent 内部部品 + μ_j 側 R-data)、(iv) equality 枝
(9.11.2)-(9.11.8)。case (b) 一様 route は a の 1019 特殊化と重なるため hub 経由で分担確認しつつ進む。

## ✅ 2026-07-08 (lane b) — 0101 HUB 裁定確認: caseB 非再構築を confirm

0101 裁定 (S11_NineElevenCoherence = b carve-out / caseA = b / caseB = a / full assembly = a) を
確認・受諾。**b は caseB (9.7.b) 一様 route を再構築しない** — a の S13 landed 群
(`caseB_coherent_sOf_H0Cprime_of_mixed` 系) を cite or hypothesis 入力で受ける。b の本 leaf scope =
**caseA (9.7.a) maximality 帰納のみ** ((9.11.1) squeeze + (9.11.2)-(9.11.8) 反証)。
⚠ 将来 flag: b の (13.3) 消費 (S-instance、dadeHypS/A(S) world) は a の gate-2 (base.tau/A0 world) と
別 world のため、S-instance 側 assembly の world-bridge が task #3 で要調整 (hub 相談予定、今は caseA 進行)。

**進捗 (本日 iteration 2)**: commit 7eedf681 — caseA a-divisibility の S0-witness 形
(`inertia_le_hcuInHu` + `caseA_source_degree_dvd_a_of_S0_witness`、sorry-free/axiom-clean)。
次 = W1-conj transport で S0-witness 仮定を外す (Coq a_dv_XH0 完成形)。

## 2026-07-08 更新 #25 (lane b, /loop iter 2-4) — (9.11.1) 入力群の実証明 + 供給状況の全数調査

**landed (全て S11_NineElevenCoherence、sorry-free/axiom-clean)**:
- iter 2 (7eedf681): `inertia_le_hcuInHu` + `caseA_source_degree_dvd_a_of_S0_witness` (S0-witness 形)。
- iter 3 (96d2efd8): `exists_summand_witness_of_ne_one` + **`caseA_source_degree_dvd_a` = Coq a_dv_XH0 完成**
  (W1-transport: conjBy m 移送 + LiesOver transport 降下鎖 + S0-witness 帰着)。
- iter 4: `caseA_a_odd` (Coq odd_a)。

**(9.11.1) squeeze 部品の供給状況 (全数調査済)**:
| Coq | 内容 | repo 状態 |
|---|---|---|
| lb01 内側 | χ(1) ≤ u on X(H0C') | ✅ `xiOf_H0Cprime_source_apply_one_le_u` (iter 1) |
| a_dv_XH0 | a ∣ χ(1) on X(H0) | ✅ `caseA_source_degree_dvd_a` (iter 3) |
| odd_a | Odd a | ✅ `caseA_a_odd` (iter 4) |
| a_dv_p1 | a ∣ p−1 | ✅ CliffordCaseAData.a_dvd_p_sub_one (field) |
| sU'C | U' ≤ C | ✅ `uprimeSub_le_cSub` (S11:1791) |
| U' ≤ C_U(S0) | | ✅ `uprimeSub_le_cuSub` (S11:4288) |
| **lb_Sqa (9.8.d count)** | (p−1)/a·(\|U\|/(a\|U'\|)) ≤ #{deg-qa irr in S(H0U')} | ✅ **`caseA_character_counts` part (d) LANDED** (S11:13917、notes の「(9.8.d) sorried-cite」情報は stale — 実カウント済) |
| lb12/lb23 純算術 | | ✅ S07_Subcoherent (two_mul_le_of_dvd_of_odd / relIndex_le_relIndex_of_le) |
| squeeze 骨格 | maximality skeleton | ✅ S07_Subcoherent 3 定理 (iter 1) |

**残 brick (次 iteration 以降、文書順)**:
1. **除算 exact 化**: `a·|U'| ∣ |U|` (uprimeSub_le_cuSub + a=[U:C_U(S0)] realization 経由) →
   a²|U'| ∣ (p−1)|U| → landed count の ℕ-除算 ((p−1)/a·(|U|/(a|U'|))) を Coq szS1' 形
   (p−1)[U:U']/a² と一致させる (equality 抽出に必須)。realization: `index_cuInHu_subgroupOf_uInHu_eq_a`
   (S11:4515) + card 転送 (card_cuInHu_eq/card_cuSub_eq_card_ker)。
2. **(9.11.1) squeeze assembly**: maximal S₂ + χ ∈ S₃ (isn't_qu 選択) + pair-refuted 節 →
   [strict 枝 = member-data bundle (世界固有、入力) + two_mul_lt_normalizedDegreeSq_of_lb0_lt_sumnS +
   xAdjoinStepW(_k) → 矛盾] or [equality 配置 struct 抽出]。equality 配置 = S₂=S₁⊆S(H0C)∩Irr /
   a=(p−1)/2 / C=U' / S₃ 全 deg qu / |S₁|=(p−1)u/a²=2u/a。
3. (9.11.2)-(9.11.8) 反証 (equality 配置 → False)。
4. S-instance 消費: world-bridge (0101 で hub 相談予定)。

⚠ 注意: S15 の `sSet_closedUnderConjugate`/`sSet_pairwiseOrthogonal`/`sSet_hasNoRealCharacters` は
generic (data : TypesIIIIIIVSetup M) だが S15 在住 (FiniteInduce scope 依存)。(9.11) assembly が
sOf 版を要するときは S15 から leaf への移設 or sOf 直証明を検討 (S15 は b 所有ゆえ移設可、
ただし S12.FiniteInduce scope import の循環チェック要)。

## 2026-07-08 更新 #26 (lane b, /loop iter 5-9) — (9.11.1) squeeze machinery + (9.11.2)/(9.11.5) 完組

**landed (全 S11_NineElevenCoherence、sorry-free/axiom-clean、5 commit)**:
- **981ffee2 (brick A)**: squeeze 円環ノードの §9 同定 — `relIndex_cuSub_U_eq_a` / `relIndex_cSub_U_eq_u`
  (実現 index の ambient-G relIndex 転送) / `relIndex_uprimeSub_U_eq` ([U:U']=a·[C_U(S0):U']) /
  `u_le_relIndex_uprimeSub_U` (lb23 入力) / `caseA_character_count_exact` ((p−1)[U:U']≤n₁a²、
  landed count の dv_lb exact 化)。
- **5d3a9e61 (B2a)**: `chiefFactor_p_sub_one_even` + `nineElevenOne_configuration` — 算術核
  (`nineElevenOne_squeeze_arithmetic`) に landed 同定 + world bundle (hs1'/hpair) を通し群世界
  equality 配置抽出: 2a=p−1 / **C=U'** ([U:C]=[U:U']⟹C=U' via relIndex_lt_lt 対偶) / χdeg=u /
  n₁a²=(p−1)[U:U']。
- **6f1e6ec4 (9.11.5 arith + 一様値)**: `sumnS_irreducible_constant_degree` (hs1' 供給) +
  `add_two_lt_two_pow` (q+2<2^q) + `two_mul_choose_two` + `binomial_lower_bound`
  ((2a+1)^q の k∈{0,1,2,q} 項抽出) + `nineElevenFive_arithmetic_contradiction`
  (指数 vs 多項式、2^q≤q+2 矛盾)。
- **881af4e8 (9.11.2 + 9.11.5 refutation)**: `relIndex_inf_le` (relative index-inf) +
  `nineElevenTwo_u_le_a_sq` (u≤a²、C=U₁⊓U₁ʷ 入力) + `nineElevenFive_refutation`
  (cleared ℕ 形の全 refutation: hcount/hnorm/hua2/hle → False)。

**⟹ frontier の実質変化**: (9.11.1) squeeze は arithmetic core → **core + §9 同定 + 群世界配置抽出 +
hs1' 供給 + (9.11.5) 全 refutation** まで leaf 完成。残る (9.11) caseA は **深い入力 3 種**に集約:
1. **(9.11.3) |𝒮₄| count** — X(H₀C) の次数別既約数え (sum-of-squares 類、char-theory)。leaf 可能性中。
2. **(9.11.4) ‖α‖² Mackey norm** — γ=Ind_{HU₁}^M 1 の double-coset ノルム。**HU₁ 非正規ゆえ
   `induce_inner_induce_trivial` (正規版) 不適** — general Mackey double-coset 数え infra が leaf 未到達。
3. **refuter hpair (= (5.6) 対偶)** — `coherentDegreeSqNormBound_of_not_coherentW` が要求する
   §9 S-family の per-member Dade bundle (Dmem/hortho_mem/htau1Dmem)。**coherence world (S07.Hypothesis/
   IsCoherent、Hypothesis-level)** ゆえ leaf の chars-level から届かない = **world-bridge**。
   caseB 先例 `caseB_coherent_sOf_H0Cprime_of_mixed` は S13 (a 所有、Hypothesis-level) 在住。

**次判断 (world-bridge)**: caseA の最終 assembly (`IsCoherent hyp.base.tau (sOf ...) hyp.base.A0` 産出)
は caseB と同じ Hypothesis-level ゆえ **S13 (a) or b 新 file (S13 import)** が居場所。leaf は S13 非 import
(循環回避) を維持。refuter の Dade bundle は S-instance Dade world 依存で、これは 0101 で flag 済の
world-bridge。**hub 調整事項** (b の chars-level squeeze machinery は完備供給、consumer 側 assembly の
world 選択が cross-lane 設計判断)。leaf 側で更に進められる genuine piece = (9.11.3) count (次 iteration 検討)。

## 2026-07-08 更新 #27 (lane b, /loop) — ★caseA UNBLOCKED: a の world-bridge landing + char sum-of-squares infra

**a の caseB rewire 3/3 完成 (`e9e16cd9`) + 9075 CLOSE が caseA を構造的に unblock**。caseA が必要とする
部品が全て reusable に判明:
- **base case**: `sOf_degreeSubfamily_isCoherent` (S13:1967) = 任意 degree d の sOf 部分族 coherence。
  caseA の 𝒮₁ (degree qa) coherence はこれで一発 (witness = (9.8.d) count>0 + sOf_antitone、
  sOf(H₀U')⊆sOf(H₀C') via H₀C'≤H₀U')。
- **per-member Dade R-data**: `caseB_sOf_memberRFamily` (S13:3012、既約→signed Dade /
  column→certainTypeR、degree 非依存 = caseA でも可)。maximality induction の adjoin が要する subcoherent 構造。
- **input 群** (全 sOf reusable): `caseB_sOf_memberRFamily_orthogonal` / `sOf_closedUnderConjugate` /
  `tau_inner_eq_of_supported` (iso) / `dadeIntegralCharacterMap_mem_ZIrr_of_supported` /
  `inducedKernelFamily_hasNoRealCharacters`。engine = `uniform_degree_coherence_of_families`
  (S07_PivotCoherence:793、norm-general、hDeg 撤去)。

**b の landed 部品** (全 sorry-free、caseA arithmetic scaffold + char infra):
- (9.11.1)-(9.11.5) arithmetic 核 (更新#26): squeeze 同定 / 群世界 config (C=U', a=(p−1)/2) /
  u≤a² / (9.11.5) 全 refutation / (9.11.3) count 核。
- **char sum-of-squares infra** (新): `sumDegreeSq_kernelInterval` (一般
  Σ_{N≤ker,K⊄ker} χ(1)²=|G/N|−|G/(K⊔N)|、`NonInflatedDegreeSqInterval.lean`、config-independent
  reusable) + `sum_xiOf_H0C_degreeSq` (§9 application: Σ_{𝒳(H₀C)} χ(1)² = |HU/(H₀C)|−u)。

**残 caseA assembly (次 session、multi-step)**:
1. **caseA entry point** = `coherent_of_maximal_coherent_pair_refuted` (私の skeleton) を具体 caseA
   (τ=hyp.base.tau, S=sOf H0Cprime, S₁=degree-qa cut=a の base case) に instantiate → refuter への reduction。
   **要 = 新 b-owned Hypothesis-level file** (S13 import; my leaf は循環回避で S13 非 import)。
   S11_NineElevenCoherence carve-out (0101) と同様 hub carve-out 要 (a-namespace 検出摩擦回避)。
2. **refuter deep 入力**: (9.11.3) hclass の残 = |HU/(H₀C)|=p^q·u index arith (|H|/|H₀|=p^q × [U:C]=u、
   realized-subgroup card tower) / (9.11.4) Mackey norm ‖Ind_{HU₁}^M 1‖² (double-coset、非正規 HU₁ ゆえ
   general Mackey 要 scratch build) / (9.11.2) inertia 恒等式 C=U₁⊓U₁ʷ (two-summand char inertia)。
3. **adjoin per-step wiring**: maximality induction の (5.6) engine (xAdjoinStepW) を a の R-data
   (caseB_sOf_memberRFamily) で発火。OrthonormalCharacterImageFamily → xAdjoinStepW inputs
   (CharacterPsiDecomposition) の impedance 確認要。

## 2026-07-08 追記 (lane-a): (10.7) typeII_derived_frobenius が 1017 の consumer に

Pf (10.7) `typeII_derived_frobenius` (S12_MaximalIII_IV_V:66) を bare sorry → genuine 構成に
de-scaffold (commit 3907291e、5/6 IsFrobeniusGroup field + kernel_is_SF 実証明)。残 1 sorry =
`conj_frobenius` (全 complement U の S_F 上 fixed-point-free 作用)。これは Peterfalvi の
char-theoretic contradiction に還元: HU 非 Frobenius なら (9.10)/(9.8.b)/(9.9.b) が等次数
reducible ν_r + irreducible λ を与え、**(5.7) で 4元 T2族 {λ,λ̄,ν_r,ν̄_r} coherent** → (5.8)+Dade
直交で矛盾。⟹ **(10.7) は本 issue の (9.11) 非Galois pair-adjoining coherence の consumer**
(uniform-degree 基底 = coherent_of_constant_degree は landed、pair-adjoining 帰納が残)。
sibling = `exceptional_case_frobenius_realization` (S11:14165、同 content)。

## 2026-07-08 更新 #28 (lane b) — caseA 構造確立: entry point + char sum-of-squares 完結

**landed (2 commit、sorry-free/axiom-clean)**:
- `sum_xiOf_H0C_degreeSq` 完結 (2ea09eaa): `index_realizedH0supC_eq` (|HU/(H₀C)|=p^q·u、
  realized-subgroup index tower、subagent 委譲) → **Σ_{𝒳(H₀C)} χ(1)² = p^q·u − u** (config-independent、
  (9.11.3) hclass char-side 完結)。
- **caseA entry point** (00943a2c): `caseA_coherent_sOf_H0Cprime_of_refuter` (新 leaf
  S11_NineElevenCaseA.lean、b carve-out) = caseA coherence → refuter 節 reduction。base case (a) +
  skeleton (b) + witness genuine 導出。

**⟹ caseA 構造完成**: a の world-bridge (base case sOf_degreeSubfamily_isCoherent + R-data
caseB_sOf_memberRFamily) + b の scaffold (skeleton + config 抽出 nineElevenOne_configuration +
(9.11.5) refutation nineElevenFive_refutation + char sum-of-squares) が **entry point で結線**。

**残 = refuter 節の実証明** (S11_NineElevenCaseA.lean の hrefute 引数を実証明で除去):
1. **adjoin 枝** (lb0 < sumnS 𝒮₂ → xAdjoinStepW 発火 → maximality 矛盾): a の R-data
   caseB_sOf_memberRFamily (OrthonormalCharacterImageFamily) → xAdjoinStepW inputs
   (CharacterPsiDecomposition) の impedance 確認 + per-step wiring。**要 engine-internals 調査**。
2. **equality 枝** (config → (9.11.2)-(9.11.8) 反証): config 抽出 nineElevenOne_configuration
   (landed) → nineElevenFive_refutation (landed) に hcount/hnorm/hua2 を供給。
   残 deep 入力 = (9.11.3) degree split (n·u²、config 下) / (9.11.4) Mackey norm ‖Ind_{HU₁}^M 1‖²
   (double-coset、heavy) / (9.11.2) inertia C=U₁⊓U₁ʷ (two-summand char)。
これらは相互依存の large 作業ゆえ fresh focused session が適切 (extreme session length ゆえ handoff)。

## 2026-07-08 更新 #29 (lane b, /loop 新 session iter 1) — (9.11.4) char-side reduction landing + (9.11.2) が upstream blocker と確定

**landed (S11_NineElevenCoherence、section NineElevenFour、sorry-free/axiom-clean、commit d005d10b)**:
- `cfnorm_sub_irreducible_orthogonal`: norm-one 既約 ψ ⊥ γ (⟨γ,ψ⟩=0) ⟹ ⟨γ−ψ,γ−ψ⟩=⟨γ,γ⟩+1。
  (9.11.4) の `α=γ−ψ₁` norm 分解 (Coq `'[alpha]='[gamma]+1`, PFsection9.v:1905)。
  reusable (任意 character γ、coherence/induction 非依存)。

**依存構造の確定調査 (Coq PFsection9.v:1680-1949 精読)**:
- (9.11.4) `‖γ‖²` (γ = Ind_{H<*>U₁}^M 1) は **(9.11.2) inertia identity `tiU1` (∀w∈W₁#, U₁∩U₁ʷ=C)
  に依存** — Coq 1930-1949 の triple-sum は tiU1 で評価 (w=1 項→|U₁|、残 q−1 項→|C|)。
- repo の induce-trivial-norm (`induce_trivial_inner_self`, InducedCharacter:736) は **Normal H 専用**
  (‖Ind_H^G 1‖²=[G:H])。(9.11.4) の HU₁ は **non-normal** ⟹ 直接不適、general Mackey double-coset
  count が必要 (note の「general Mackey leaf 未到達」を裏取り)。
- **⟹ (9.11.2) tiU1 が (9.11.4) の upstream blocker**。(9.11.5) は (9.11.2)+(9.11.3)+(9.11.4) 全部を
  消費するので、critical path 上の最上流 deep input = **(9.11.2)**。

**(9.11.2) tiU1 の本体 (Coq 1680-1806、次の deep push の対象)**: theta-character inertia 論法 —
θ=cfDprodl(cfBigdprod 'chi) の linear character 構成 → 商 HU/K の inertia group `I_{HU/K}[χ_t2]` →
`cfInd_Hall_central_Inertia` で誘導次数 `#|U:U₁∩U₁ʷ|` を計算 → pred2 (u or a) の二分 → a を
prime-order argument で排除 → =u ⟹ U₁∩U₁ʷ=C。**multi-iteration の genuine char theory**
(inertia group + Clifford Dprod + Hall)。leaf の setup (U₁=cuSub=C_U(S₀)、W₁-conjugation、θ 構成) から。

**残 caseA refuter deep 入力 (優先順)**: (9.11.2) tiU1 [最上流、次] → (9.11.4) ‖γ‖² [tiU1-gated] →
(9.11.3) hclass/hn degree-split [sum_xiOf_H0C_degreeSq landed、degree 構造が残] → adjoin 枝 wiring。

## 2026-07-08 更新 #30 (lane b, /loop iter 2) — equality-branch assembly landing (9.11.2-5 連鎖)

**landed (S11_NineElevenCoherence、sorry-free、commit 1d335aef)**:
- `nineElevenCaseA_equality_refutation`: (9.11.1) config `p=2a+1` の下で 3 deep 入力
  ((9.11.2) inertia identity C=K₁⊓K₂ / (9.11.3) hclass+hn / (9.11.4) hnorm) + coherence bound
  hle → False。(9.11.2)→(9.11.5) の 4 landed 定理を連鎖、p=2a+1 substitution で整合。

**⟹ equality 枝は arithmetic 全 discharge**。残 honest content = **3 named deep 入力のみ** +
refuter wiring (dichotomy = nineElevenOne_configuration で config 産出 + hle = pair-refuted→(5.6) bound)。

**deep 入力の tractability 調査 (S11 machinery 精読)**:
- (9.11.2) は `hcPsi_inertia_index_eq_u` (S11:10084、all-summands θ ⟹ inertia index=u) を
  **two-summand θ (regular on {S₀, S₀ʷ}) に一般化** して inertia index = #|U:U₁∩U₁ʷ| を得る route。
  machinery = inertia_eq_hcInHu_caseA + hcConjDescend (HU-conj ↔ Ū-precomp equivariance)。
  **repo に cfDprod 無** ゆえ Coq の θ=cfBigdprod route でなく、この一般化 route が Lean-native。
  multi-session。**⚠ `CliffordCaseAData.Ubar_embeds_product` は vacuous free field (:=True, S11:6678)**
  — (9.11.2) injectivity は honest 証明要 (この field は使えない)。
- landed 部品: `index_cuInHu_subgroupOf_uInHu_eq_a` (S11:4527, [U:C_U(S₀)]=a) /
  `relIndex_cuSub_U_eq_a` (K₁=cuSub の relIndex=a) → nineElevenTwo の hK₁ は供給済、
  残 = hK₂ (K₂=C_U(S₀ʷ) の index=a、W₁-conj-invariance) + hCinf (deep two-summand inertia)。

**次 (優先順)**: (9.11.2) two-summand inertia 一般化 [upstream 最深] → refuter dichotomy wiring →
(9.11.3) degree-split。

## 2026-07-08 更新 #31 (lane b, /loop iter 3) — (9.11.2) two-summand inertia の ⊆ 方向 landing

**landed (S11_NineElevenCoherence、section NineElevenTwoInertia、sorry-free、commit dbceccab)**:
- `caseA_char_inertia_of_summand`: 任意 order-p U-invariant summand S、θ regular on S、g fixes θ
  ⟹ aInvariantRestrictAut hSinv g = 1 (g ∈ C_U(S))。**a 所有 chiefFactor_caseA_char_inertia_single
  (S₀ 固定) を任意 summand に一般化** (pure-algebra 核 mulAut_eq_id_on_of_fixes_ne_one_on_prime 再利用)。
  ⚠ IsAInvariant は `open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)` 要 (S11_Maximal と別 open)。
- `caseA_char_inertia_two_summands`: 2 summand 適用 → I(θ)⊓U ⊆ C_U(H_i)⊓C_U(H_j) = U₁∩U₁ʷ の ⊆ 半分。

**(9.11.2) tiU1 の残 (次 iteration〜)**:
1. **⊇ 方向** (fixing both summands ⟹ fixing θ): θ = two-summand regular char (S₀,S₀ʷ で nontrivial、
   他 summand で trivial)。g ∈ C_U(S₀)∩C_U(S₀ʷ) は S₀,S₀ʷ を pointwise fix、他 summand は θ trivial
   ゆえ θ(g·x)=θ(x)。⟹ I(θ)⊓U = U₁∩U₁ʷ 確定。**要 = two-summand θ (Dprod) の構成** — repo に cfDprod 無、
   linearIrreducibleCharacter の product 構成 or hcPsi 経由で。
2. **index dichotomy** [U:U₁∩U₁ʷ] ∈ {u,a}: I(θ) の induced char が S_H0C' member ⟹ degree qu or qa。
3. **a 排除** → U₁∩U₁ʷ=C (C≤U₁∩U₁ʷ + index u)。
⟹ tiU1 完成で nineElevenCaseA_equality_refutation の hCinf 供給。

## 2026-07-08 更新 #32 (lane b, /loop iter 4) — (9.11.2) inertia identity 両方向完成

**landed (S11_NineElevenCoherence、NineElevenTwoInertia、sorry-free、commit 7d34a60a)**:
- `caseA_centralizes_two_summands_fixes_char` (⊇): χ が 2 summand supported + g が両 summand centralize
  ⟹ g fixes χ。generators 論法 (MonoidHom.eqLocus + Hpart_iSup span + eq_of_eqOn_top)。
- ⟹ ⊆ (iter 3) と合わせ **I(θ)⊓U = C_U(H_i)⊓C_U(H_j) = U₁∩U₁ʷ** 確定 (two-summand supported θ)。

**(9.11.2) tiU1 残 (次〜)**:
(a) **two-summand regular char θ 構成**: χ:(H̄)→*ℂˣ nontrivial on H_i,H_j / trivial 他。H̄=∏Hpart
    (Hpart_iSupIndep + Hpart_iSup → noncommPiCoprod bijective) の直積から per-factor char を組む。
    order-p summand は nontrivial char を持つ (has_nonprincipal_irr 類)。**cfDprod 無ゆえ直積 char 構成が infra**。
(b) inertia index [U:U₁∩U₁ʷ] ∈ {u,a}: I(θ) の induce char が S_H0C' member → degree qu/qa。
(c) a 排除 → U₁∩U₁ʷ=C (C≤U₁∩U₁ʷ + index u) → nineElevenCaseA_equality_refutation の hCinf 供給。

## 2026-07-08 更新 #33 (lane b, /loop iter 6) — ★(9.11.2) Ū-side inertia identity 完成

**landed (S11_NineElevenCoherence、NineElevenTwoInertia section、全 sorry-free、iter 3-6 で計 6 定理)**:
`caseA_inertia_iff_centralizes_two_summands` (commit 1d9becc4): 構成 θ に対し g∈U fixes θ ⟺
g が H_i,H_j 両 summand を centralize。⟹ **I(θ)⊓U = C_U(H_i)⊓C_U(H_j) = U₁∩U₁ʷ (Ū-side 完成)**。
部品: exists_two_summand_char (構成) + caseA_char_inertia_of_summand/two_summands (⊆) +
caseA_centralizes_two_summands_fixes_char (⊇)。

**残 tiU1 endgame (deep、multi-iteration — 次 session batch 候補)**:
(a) **HU-inertia index**: hcPsi bridge (hcPsi_conjBy_eq で HU-conj↔Ū-fixing) + two-summand 版
    inertia_inf_uInHu_le_cInHu_of_realized → [HU:I(hcPsi θ)]=[U:U₁∩U₁ʷ]。⚠ all-summand 版は
    inertia=HC (spanning 依存) ゆえ two-summand は plumbing chain (caseB_char_inertia_inflation_of_core
    等) の adaptation 要。
(b) **realization**: aInvariantRestrictAut=1 → G-subgroup (cuSub 型 realized centralizer) 橋渡し。
    K₁=cuSub(=C_U(S₀)) は landed、K₂=C_U(S₀ʷ) の realized 版 新設要。C=cSub=K₁⊓K₂ 形へ。
(c) **degree dichotomy** [U:U₁∩U₁ʷ]∈{u,a}: Ind(θ)∈S_H0C' → degree qu/qa + a 排除
    → tiU1 (U₁∩U₁ʷ=C) → nineElevenTwo_u_le_a_sq の hCinf 供給 → equality-branch 発火。

## 2026-07-08 更新 #34 (lane b, /loop iter 9) — ★(9.11.2) tiU1 endgame 完全マップ (landed 部品 + 残手順)

**目標**: `nineElevenTwo_u_le_a_sq` の `hCinf : chars.C = K₁ ⊓ K₂` (K₁=C_U(S₀)=cuSub relIndex a landed、
K₂=C_U(S₀ʷ) relIndex a、C=cSub) を供給 → equality-branch (nineElevenCaseA_equality_refutation) 発火。

**landed 部品 (iter 3-9、全 S11_NineElevenCoherence の `NineElevenTwoInertia` section、sorry-free)**:
| 定理 | 役割 |
|---|---|
| `exists_two_summand_char` / `exists_caseA_two_summand_char` | 2-summand supported char θ 構成 (nontrivial H_i,H_j / trivial 他) |
| `caseA_char_inertia_of_summand` / `_two_summands` | Ū-side ⊆: g fixes θ ⟹ centralize 両 summand |
| `caseA_centralizes_two_summands_fixes_char` | Ū-side ⊇: centralize 両 + supported ⟹ fixes θ |
| `caseA_inertia_iff_centralizes_two_summands` | Ū-side identity: I(θ)⊓U = U₁∩U₁ʷ |
| `centralizes_all_imp_centralizes_summand` | C⊆C_U(H_k) (easy 方向) |
| `inflation_fixing_imp_action_fixing` / `caseA_hu_char_inertia_two_summands` | HU-bridge ⊆: HU-inertia の realized g ⟹ centralize 両 |
| `caseA_centralizes_two_summands_compHom_eq` | HU-bridge ⊇ (compHom 形): centralize 両 ⟹ compHom(uActionHom g)θbar=θbar |

**残手順 (次 focused session、順に)**:
1. **realized subgroup**: `cuSubOfPair`/`cuSubOf j` = realized(ker(aInvariantRestrictAut (Hpart_aInvariant j)))
   を cuSub (S11:4178) mirror で新設 (b file)。K₂=cuSubOf j。[U:cuSubOf j]=a は **orbit-symmetry 要**
   (Hpart j = W₁-translate of S₀ ⟹ 作用共役 ⟹ |range|=a、card_U_eq_a_mul_card_cuSub の一般化)。
2. **HU ⊇ 完成**: caseA_centralizes_two_summands_compHom_eq + conjBy_compHom_hInHuEquivH +
   compHom_typeP_conjAction_inflation (cInHu_le_inertia S11:5420 pattern) → realized(U₁∩U₁ʷ)⊆I(θ₀)。
3. **I(θ₀)=H·realized(U₁∩U₁ʷ)**: inertia_eq_hcInHu_of_inf_le (S11:6488) を two-summand target で
   adapt (⊆=caseA_hu_char_inertia_two_summands realize、⊇=step 2)。
4. **index**: [HU:I(θ₀)]=[U:U₁∩U₁ʷ] (H-part cancel、hc_index_eq_u / hcPsi_inertia_index_eq_u 型)。
5. **degree dichotomy**: Ind_M(mod θ₀) ∈ S_H0C' → degree qu/qa → [U:U₁∩U₁ʷ]∈{u,a}
   (Coq cfInd_Hall_central_Inertia; landed: caseA_exists_irreducible_source_degree_qa S11:6455、
   sOf_H0Cprime_apply_one_le_qu)。a 排除 (Coq prime arg) → =u。
6. **tiU1**: C≤U₁∩U₁ʷ (centralizes_all_imp_centralizes_summand realize) + [U:U₁∩U₁ʷ]=u=[U:C]
   → U₁∩U₁ʷ=C → hCinf。
⚠ **key infra 依存**: hcConjDescend_eq_uActionHom (S11:10237, A_g=uActionHom g realized bridge)。

## 2026-07-08 更新 #35 (lane b, /loop iter 10-12) — (9.11.2) tiU1 machinery ほぼ完成、残 = degree dichotomy + a 排除

**landed (iter 10-12、subagent 3 委譲、全 sorry-free/axiom-clean)**:
- iter 10: `cuSubOf` + `relIndex_cuSubOf_U_eq_a` (realized C_U(H_j)、orbit-symmetry crux)。
- iter 11: `caseA_inertia_eq_hcuInHuPair` (I(θ₀)=hInHu⊔cuInHuPair、HU-inertia 同定) + 6 lemma。
- iter 12: `caseA_inertia_index_eq` ([I(θ₀)].index = (cuSubOf i⊓cuSubOf j).relIndex U) + 9 lemma。
⟹ **HU-inertia machinery + index 完成**。char-degree = index bridge も landed
  (`apply_one_eq_index_of_liesOver_linear_inertia`, CliffordSingleOrbit:585)。

**残 tiU1 = 2 piece (最深、次 focused)**:
1. **degree dichotomy [U:cuSubOf i⊓cuSubOf j] ∈ {u,a}**: source char (H₀C'⊆ker) を θ₀ inertia から構成
   (Clifford: linear over inertia induces irreducibly、apply_one_eq_index_of_liesOver_linear_inertia)、
   M-induce で S_H0C' member。**⚠ S_H0C' member degree 分割 (=qu∨=qa) は未 landed** (caseB は
   caseB_degree_qu 条件付き、caseA は existence caseA_exists_irreducible_source_degree_qa:6455 のみ)。
   分割構築 = §9 (9.9)/(9.10) analysis、substantial (b carve-out で建てる、a §9 piece cite)。
2. **a 排除 (Coq PFsection9.v:1785-1795)**: pred2 case-split。u-branch 即 (|U₁∩U₁ʷ|=|C|)。
   a-branch: U₁∩U₁ʷ⊆C を prime_meetG (q=|W₁| 素) で直接証明 (bigdprod H̄=∏H₁^w1、各 factor centralize)。
   C≤cuSubOf i⊓cuSubOf j は landed (cInHu_le_cuInHuPair 経由) ⟹ 両 branch で =C = tiU1。
⟹ tiU1 → nineElevenTwo_u_le_a_sq(:1468) hCinf → equality-branch。
**次 route 検討**: (B) a-branch の prime 論法を直接 (U₁∩U₁ʷ⊆C を degree 経由せず) 引けるか精査
  (引ければ degree partition 構築を回避可能、大幅短縮)。

## 2026-07-09 更新 (lane a) — (10.7) の exceptional 枝は S11 で閉じた + §9 全 conjunct proven

lane a が §9 を完遂 (commits 14b67135/a9fb79d1/e33ca028/f66c3921):
- **(9.7) 無条件 u-bound** `u_le_cyclotomicQuotient` (S11_ImprimitiveUBound、dichotomy 両枝実証明)。
- **(9.10) type-II HU-Frobenius (exceptional 枝) 完全 proven** —
  `exceptional_case_frobenius_realization` sorry-free。新 helper
  `IsFrobeniusGroup.conj_complement` (S11、complement 共役 transport、S12 からも cite 可)。

**⟹ (10.7) `typeII_derived_frobenius` (S12:47) への含意**: Coq `Frob_der1_type2` の入り口
`typeP_reducible_core_cases` の両枝が Lean で利用可能になった:
- 右枝 (exceptional): `exceptional_case_frobenius_realization` cite で **即 HU-Frobenius**。
- 左枝 (λ 存在): caseA/caseB_character_counts (proven) から reducible ν_r + irreducible λ
  (等 degree qu) を取り、**T2 = {λ,λ̄,ν_r,ν̄_r} は 4-elt uniform-degree** ⟹ 更新 #3 の予想通り
  `coherent_subset_of_constant_degree` (landed) で (9.11) full induction 回避可の見込み。
  残る genuine gap = S-side Dade τS + M↔S support disjoint (`oST`) + FTtypeP_coherent_TIred
  相当の cross-isometry 計算 (Coq PFsection10:568-658 後半)。次の lane-a focused session で
  この S12 assembly に正面着手する。

## 2026-07-12 update (lane a) — ⚠ 本 issue の (10.8) 動機は SUPERSEDED (issue 1020 完結)

本 issue の背景 「(10.8) `typeII_coherence_contradiction_estimate` は hB 側 (10.7)
`typeII_derived_frobenius` 経由で §5 不在に BLOCKED」は **2026-07-11/12 の issue 1020 arc で
supersede された**:

- **(10.7) は pair-witness route で axiom-clean に landed**: `typeII_HU_frobenius_of_coherent'`
  (S12_TypeIICrossIsometryPair、issue 9079 + 1020 Phase 1a)。§5 uniform_degree_coherence /
  subcoherence を経由しない。
- **(10.8) は無条件・axiom-clean に landed**: `S_not_coherent_unconditional` (S12_Noncoherence、
  hB は `g1_div_le_of_partner` で実 discharge)。
- 旧 chain (`exists_typeIICrossIsometryData` sorried gate → 旧 `typeII_HU_frobenius_of_coherent`
  → `typeII_derived_frobenius` → 旧 estimate hB) は **Legacy 注記済**・legacy (10.8) 専用。
  ⚠ **lane b への注意**: `S07_Subcoherent.lean` の docstring 群 (:241/:313/:351/:610) は
  「subcoherent supply が lane a の (10.7) typeII_derived_frobenius を閉じる」と述べるが、
  この供給先は上記のとおり不要になった (heir が supply なしで clean)。S07_Subcoherent の
  現在価値は **(6.5) gates (issue 2022) の general six_two chain** 側にある。

**残る本 issue の scope** = §5 `uniform_degree_coherence` 一般形 + `subcoherent` R-datum が
(6.5)/(6.8) 系 (issue 2022、lane b) と typeII 系のどこで依然必要かの再精査のみ。
(10.8)/(10.7) unblock 目的としては closed 相当。hub の帰属裁定は「lane b (2022 と同根)」を提案。

## 2026-07-12 更新 #19 (lane b) — ★uniform 底 coherence を `indS = Ind_S^G` へ re-ground (landed)

(13.3) `coherent_H0Cprime_S` 再grounding の中核 route (S-instance 側、= (10.7)/(10.8) が
superseded された後も live な本 issue の残 scope) を 1 brick 前進:

**landed (`S15_SAndT_Setup/HypothesisBasics.lean`、`Hypothesis.sSetIrrDeg_coherent_indS`、
sorry-token 0、`lake build OddOrder` GREEN 4179 jobs / 3:09)**:
- 既 landed の `sSetIrrDeg_coherent` (update #18) は **Dade map** `τ = dadeIntegralCharacterMap
  (dadeHypS hG) …` に対する `IsCoherent τ (S₁ d) A(S)` を産むが、consumer ((A) engine
  `coherentIndS_image_inner_eta_eq_zero` + 最終的に `coherent_H0Cprime_S`) は **`hyp.indS =
  Ind_S^G`** 形を要す。両 map は `A(S)`-supported 上で一致 (`sInstance_dade_eq_induce`、(13.2.e)
  `normedTI` 等長性半分、Rungs B+C landed) し、`S07.IsCoherent` は map に `extends_on_supported`
  経由でしか依存しない (domain `zSupportedSpan (S₁ d) A(S)` の各元は `A(S)`-supported) ので、
  既存 `S07.IsCoherent.congrMap` (S08_CaseBCoherence2:1084) で `indS` へ re-target。追加 analytic
  input 0。
- 技術: finiteness instance を全て `S12.FiniteInduce` scope (`[Finite G]` 由来) から取ることで、
  `indS` と `sInstance_dade_eq_induce` の `induce` が同一 `Fintype ↥S` instance を共有 →
  subsingleton-instance juggling 不要 (最初 explicit `[Fintype ↥hyp.S]` を宣言したら
  FiniteInduce と衝突して type mismatch、instance-only fix)。
- sorryAx provenance: `dadeHypS` (shared BG §16 Theorem-II pins、accepted on-path
  `dadeSupportHypotheses_typeI` と exact parity) からの inheritance のみ。lane-b 新規 sorry 0。

**⟹ (A) engine は uniform sub-family `S₁(d)` 上で即 instantiable** (abstract family 引数ゆえ):
`coh := sSetIrrDeg_coherent_indS …`、`hconj`/`hnoReal`/`hsupp` は `sSetIrrDeg_subcoherent` の
local haves (conj-closure・no-real・conjugate-diff support) を standalone 化すれば供給
(全て landed pieces、新 deep math 無)。

**残 (full-family re-grounding、順に)**:
1. (A)-engine 供給用に `sSetIrrDeg` の `ClosedUnderConjugate`/`hsupp` を standalone lemma 化
   (`sSetIrrDeg_subcoherent` の `hconjmem`/`hdiff_of_mem` を切り出し)。
2. full `sSet` への lift = (9.11.1)–(9.11.8) pair-adjoining induction (`coherentPairChain` fold +
   済 squeeze、update #5/#35)。base `S₁(qa)` (今 `indS` 形で landed) + Galois `S₁(qu)` から
   conjugate pair adjoining。`h2 : 2 ≤ (S₁ d).ncard` は §9 (9.8.d) count (exposed param、genuine
   upstream — caseA_exists_irreducible_source_degree_qa は existence のみ、2-member count 未 landed)。
3. `IsCoherent indS (full sSet) A(S)` を得たら同 `congrMap` step で `coherent_H0Cprime_S` を
   honest route へ re-point (`sibleyTarget_H0C` 置換; support は `A(S)`、`(C')^#⊆A(S)` bridge で
   `cprimeSharpS` へ絞る)。

## 2026-07-12 更新 #36 (lane b) — ★残リスト step 1 完了 + h2 sub-gate RESOLVED (sorry-free) + caseA base coherence h0 landed

更新 #35 末尾の「残 (full-family re-grounding、順に)」の **step 1 完了** + **step 2 の h2 sub-gate を
positive に RESOLVE** (更新 #35 が「2-member count 未 landed」とした点の訂正) + **caseA base coherence
`h0` (pair-adjoining lift の entry point) を landed**。全て build-green (`lake build OddOrder` 4179 jobs,
3m11s)。

### 1. 残リスト step 1 完了: (A)-engine 供給用 standalone lemma 化 (HypothesisBasics.lean、全 axiom-clean)
`sSetIrrDeg_subcoherent`/`sSetIrrDeg_coherent` の local `have` を standalone theorem に切り出し、両所で cite:
- `sSetIrrDeg_closedUnderConjugate` (hconj、`star d = d`)、`sSetIrrDeg_hasNoRealCharacters` (hnoReal、oddCardS)、
  `sSetIrrDeg_member_support_subset` (⊆ A(S)∪{1})、`sSetIrrDeg_member_diff_supported` (member 差 ⊆ A(S)、
  hsupp/hconjsupp/hsuppdiff)、`sSetIrrDeg_finite`。全て propext/Classical.choice/Quot.sound のみ (sorryAx 無)。

### 2. (A) engine を S₁(d) 上で instantiate (CoherenceEtaOrthogonality.lean、coherence hypothesis 無)
`sSetIrrDeg_coherentIndS_image_inner_eta_eq_zero` — S₁(d) の任意 coherent image `(sSetIrrDeg_coherent_indS
…).some.extension ζ` が η-grid 全体に直交。hconj/hnoReal/hsupp/coh を全て landed piece で discharge (coherence
仮説 0)。sorryAx は既存 Dade foundation (dadeHypS0) のみ inherit、新規 0。

### 3. ★ h2 sub-gate RESOLVED (更新 #35 の「2-member count 未 landed」を訂正)
`sSetIrrDeg_qa_two_le_ncard` (HypothesisBasics.lean、**完全 axiom-clean、sorryAx 無**):
`CliffordCaseAData` を与えれば `2 ≤ (sSetIrrDeg hG (q·a)).ncard`。
- **Coq PFsection9.v:1537-1551 の再現**: base `S1` は `0 < size S1` (1 member) のみ要る — 𝒮 が conjugate-closed
  + no-real ゆえ χ と distinct χ̄ で `size ≥ 2` に倍化。
- 1 member = **positive (9.8.d) count** `S11.caseA_exists_irreducible_qa` (landed、`(p−1)/a ≥ 1` via
  `CliffordCaseAData.a_dvd_p_sub_one` = Coq `a_dv_p1`、`[C_U(S₀):U′] ≥ 1`)、その witness は `𝒮(H₀U′) ⊆ 𝒮`
  (`sOf_subset_sSet`)。conj-closure + no-real で倍化。
- ∴ 更新 #35 の「caseA_exists_...qa は existence のみ、2-member count 未 landed」は**訂正**: existence +
  conjugacy doubling で 2-member は landed (新 count 不要)。

### 4. caseA base coherence h0 (lift entry point) landed
`sSetIrrDeg_qa_coherent_indS_caseA` (HypothesisBasics.lean): `CliffordCaseAData` から
`Nonempty (IsCoherent Ind_S^G (sSetIrrDeg (q·a)) A(S))` を hd/hd0/h2 全 discharge で産む
(`star_natCast`/`Nat.card_pos`+`a_pos`/上記 h2)。= Coq `Ptype_core_coherence` の pair-adjoining が start する
base `h0`。sorryAx は既存 Dade (dadeHypS) のみ inherit。

### 残 (full `sSet` への lift = (9.11.1)–(9.11.8)、順に)
base `h0 = sSetIrrDeg_qa_coherent_indS_caseA` (caseA) / `sSetIrrDeg_coherent_indS` (caseB Galois、d=q·u で
uniform ゆえ lift 不要) から `coherentOfPairChainCover` (S07_Coherence/CoherenceUnion:1620) で組む:
1. **degree-monotone decomposition** (`hpairs`/`hcover`): `sSet ∖ S₁(qa)` を conjugate pair
   `{χ, χ̄}` (irreducible、R-datum = 既 landed `sSet_member_differenceImage` の CharacterDifferenceImage)
   + reducible `μ_j` (CharacterPsiDecomposition / OrthonormalCharacterImageFamily) に分解。要 degree-enum
   (`exists_monotoneDegreeEnum` 相当を S-instance へ)。
2. **per-pair (5.6)/(9.11.5) retarget** (`hstep`): `Snorm`/`sumnS` squeeze (S07_Subcoherent、landed sorry-free)
   + `xAdjoinStepW` を各 adjoining step で発火。anchor prefix は S₀ = S₁(qa) 固定。
3. 得た `IsCoherent indS (full sSet) A(S)` を `congrMap` で `coherent_H0Cprime_S` を honest route へ
   re-point (更新 #35 step 3)。

### ⚠ cross-lane coordination (9090 との関係)
lane-a issue 9090 (2026-07-12) が「FT spine の bare sorry root = M-instance (9.11) case-a coherence
`sibleyTarget_H0C` (Coherence911:43、honest port 要)」を確定し、hub に (9.11) の lane 帰属 reconcile を依頼。
本 lane-b work は **S-instance** (9.11) coherence (`coherent_H0Cprime_S` re-grounding、S15_SAndT_Setup b-owned)
で、同 Coq PFsection9.v:1484 の pair-adjoining 構造を使うが M-instance `sibleyTarget_H0C`/`Coherence911.lean` は
一切触れていない (b-territory 内、shared engine は cite のみ)。hub は 9090 の reconcile 時に本 lane-b の
S-instance (9.11) base landing (本更新) を合わせて確認されたい。

**commit**: 329c1dd7 (step 1+2)、95863704 (h2)、58f15891 (base h0)。

## 2026-07-12 更新 #37 (lane b, /loop 再開 hub[b]) — 9090 coordination 応答 + step 1/2 landed 検証

**9090 HUB RULING (Opus hub 本日) の coordination flag への lane-b 応答** (「8-step induction core を
instance-generic に切り出せば二重 port 回避」):

- **deep core は既に shared/b-owned** — lane a の M-instance port と b の S-instance は共に以下を consume、
  二重 port なし: (i) (9.11.1)-(9.11.8) 算術 brick 群 = **b 所有 `S11_NineElevenCoherence.lean`**
  (sorry-free、Dade-pair parameterized 設計 = 元々 instance-generic)、(ii) Snorm/sumnS squeeze =
  **b carve-out `S07_Subcoherent.lean`** (sorry-free)、(iii) 組立 engine `coherentOfPairChainCover` =
  **b carve-out `S07_Coherence.lean`** (CoherenceUnion:1620)。
- **per-instance に異なるのは family-specific assembly のみ** (M = type-III/IV family / S = type-II sSet)、
  これは genuinely 別物ゆえ両方 genuine。⟹ **b は S-instance assembly を独立継続 (非 dup、hub 裁定と整合)**。
  lane a が M-instance port で shared engine を generalize したら b は main sync で re-point (通常 merge flow)。
- **file 非衝突確認**: b は Coherence911/S13_Orthogonality (lane-a、M-instance) を touch せず。a は
  S15_SAndT_Setup (b、S-instance) を touch せず。

**本 session landed (step 1+2、full build 4179 green、全 b-territory、新 axiom/sorry 無)**:
- step 1: `sSetIrrDeg_coherentIndS_image_inner_eta_eq_zero` (CoherenceEtaOrthogonality) = (A) engine を
  uniform 底 S₁(d) に instantiate (coherence 仮説を `sSetIrrDeg_coherent_indS` で discharge)。+ standalone
  4 補題 (closedUnderConjugate/hasNoRealCharacters/member_support_subset/member_diff_supported、axiom-clean)。
- step 2: `sSetIrrDeg_qa_two_le_ncard` (h2 count、**fully axiom-clean** — (9.8.d) existence +conj-closure ≥2、
  #35 の「2-member count 未 landed」訂正) + `sSetIrrDeg_qa_coherent_indS_caseA` (caseA 底 h0、hd/hd0/h2 全 discharge)。
- commits: 329c1dd7 / 95863704 / 58f15891 / cdb80586。

**残 (次 iteration、文書順)**: (a) caseB Galois route (全 sSet uniform 次数 q·u → `sSetIrrDeg_coherent_indS`
@ d=q·u 直接) / (b) caseA 非Galois pair-adjoining lift (h0 → `coherentOfPairChainCover`: 次数単調
decomposition hpairs/hcover [μ_j = CharacterPsiDecomposition、既約対 = CharacterDifferenceImage、per-member
R-datum `sSet_member_differenceImage` landed] + per-pair retarget hstep [squeeze + xAdjoinStepW]) /
(c) clifford_dichotomy で結合 → `IsCoherent indS sSet A(S)` 無条件 / (d) `coherent_H0Cprime_S` を congrMap
で re-point、`sibleyTarget_H0C` を drop (payoff)。
