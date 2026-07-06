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
