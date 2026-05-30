---
id: 51
slug: bg-s04-thm-4-16-blackburn
title: "BG §4 Thm 4.16 Blackburn rank≤2 分類を形式化 (D)"
created: 2026-05-30
---

# BG §4 Thm 4.16 Blackburn rank≤2 分類を形式化 (D)

## 背景

BG §4 の頂点定理 = **Theorem 4.16 (Blackburn)**。p 奇, R 非自明 p-群, A p′-自己同型群, `r(R)≤2`, `[R,A]=R`, `|A|` odd ⇒ **p>3** かつ R は (1) abelian or (2) `R₁∘R₂` (R₁ exp-p extraspecial 位数 p³, R₂ cyclic, `Ω₁(R₂)=R₁'`)。

**Blackburn フル分類は Gorenstein/Isaacs に無く、BG が §4 内で完全自前展開** (`bg-s04-design` workflow wf_39c356b8-eb2 で確定)。形式化対象 = BG §4 補題チェーン (Prop 4.3→4.5→4.8→4.11 Huppert→4.12→4.13-15→4.16)。

§4 v1 (2026-05-30, `bg-s04-v1-impl` workflow) で **PRank 性質補強 / SCN₃ / Prop 4.4(a) / Lem 4.7⇒ / Lem 4.2 / Lem 4.5(a) 部分 / GL(2,p) 分岐エンジン** が sorry-free 完成。本 issue はその上に Thm 4.16 を載せる。

**詳細な cold-start 着手手順 = [`notes/bg/s04_thm416_handoff.md`](../notes/bg/s04_thm416_handoff.md)** (self-contained)。全体計画 = `notes/bg/s04_implementation_plan_2026_05_30.md`。

## やること

handoff §6 の sub-issue ロードマップに従う (各々別 issue 化推奨):

- [x] 新規 API: `OddOrder/GroupTheory/CentralProduct.lean` + exp-p extraspecial + agemo `℧` ✅ **2026-05-30 完了** (workflow `bg-s04-thm416-api-bundle`, commits 4656738/560312b/4d0269a, sorry-free/axiom-clean/build green 3352 jobs)
- [ ] Prop 4.3(a) cl≤3 分岐 + Lem 4.5 general/4.5(b)(c) (Gorenstein 5.4.10/5.4.3 行間)
- [ ] Prop 4.8 + Prop 4.11 Huppert + Thm 4.12 (§4 第2の山, 設計先行)
- [ ] Lem 4.13/4.14/4.15 (aut order + extraspecial commutator)
- [ ] Thm 4.16 本体 (Case A metacyclic / Case B-1 central product / Case B-2 GL(2,p) 矛盾)

## 進捗 (2026-05-30)

**issue 1 (新規 API 束) 完了** — workflow `bg-s04-thm416-api-bundle` (10 agent, design→implement→verify, anti-scaffold gated):

- `OddOrder/GroupTheory/CentralProduct.lean` 新規 — `IsCentralProduct R R₁ R₂ := R = R₁⊔R₂ ∧ ⁅R₁,R₂⁆=⊥`。overlap `R₁⊓R₂ ≤ Z(R)` は導出補題 (anti-hoist)。+ `of_le_centralizer` (Case B-1 producer)。
- `IsExtraspecial.lean` — `IsExpPExtraspecial p G := IsExtraspecial p G ∧ Monoid.exponent G = p` + `pow_eq_one`。
- `OmegaSubgroup.lean` — `Agemo p n G` (BG 𝒰ⁿ, Omega 双対) + `anti`/`characteristic`。
- 全て sorry-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`)、`lake build OddOrder` green (3352 jobs)。

**設計書** `notes/bg/s04_prop411_thm416_design.md` (Prop 4.11/Thm 4.12/Thm 4.16, scaffold-trap audit + sub-issue I-0a..I-5)。**最深 gate = N-4 (A の R/S 商作用 + Maschke)** を設計書が指摘。

**I-1b (Prop 1.6(b) R-内部形) 完了 + N-4 半分既存判明** — workflow `bg-s04-n4-quotient-action`:

- `OperatorQuotientAction.lean` 新規 — `actionCommutator_restrict_self_eq_top` (`[[R,A],A]=[R,A]` ⇒ `[N,A]=N` = Thm 4.12(a) step a-1「R=[R,A] WLOG」) ほか 3 補題、sorry-free/axiom-clean (commit 3641c6a)。
- **N-4 φ̄ lift は Ch04 既存判明** (`quotientMulAutHom`@Ch04:2248)。workflow が誤って再実装したが破棄。設計書 §2 N-4 を訂正。残 N-4 = **Maschke bridge のみ** = `notes/bg/s04_n4_maschke_bridge_design.md` (難度 ⭐⭐→⭐)。
- ⚠ 既存 `quotientMulAutHom` は `_root_` 欠落で実名二重 nest → Ch04 修正 issue を spawn。

次 = (A) issue 2 (Prop 4.3(a) cl≤3 + Lem 4.5 general) か (B) N-4 Maschke bridge。

**issue 2 (Wave 2) 一部完了** — workflow `bg-s04-issue2-prop43-lem45b` (commit 46e9e5c, 全 sorry-free/axiom-clean):

- ✅ **Lem 4.5(b) 完全** `isElementaryAbelian_omega1_of_isCyclic_index_prime` (crux `|Ω₁|≤p²` を hoist せず証明、核 `x^p∈Z` は Isaacs Thm 6.12/Lem 6.16 共役エンジン再利用で Gorenstein 5.4.3/4.4 を回避)。
- ✅ **Lem 4.10 完全** `isElementaryAbelian_omega1_of_isMetacyclic` (4.5(b) の系)。
- ⚠ **Prop 4.3(a) cl≤3 precursor のみ** `commutatorElement_pow_left_of_triple_central`。full collection+|R|帰納未完 (γ₄=1 要、BG の f/g exponent が mathlib convention で誤り判明)。

→ **Prop 4.11 (Huppert) の gate (Lem 4.5(b)/agemo) が開いた**。次候補 = Prop 4.11 / N-4 Maschke / Prop 4.3(a) full / Lem 4.9+Prop 4.8 (handoff §8)。

**N-4 Maschke A-invariant complement bridge 完了** (2026-05-30, commit 91fc115) — handoff §1/§8 が「最深 scaffold-trap gate」と名指しした所:

- `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean` 新規。中核 = `exists_aInvariant_complement_in_omega1_quotient`: `(|A|,|R|)` coprime 作用下で `Ω₁(R⧸S)` 内の A-不変 `W₀⧸S` に A-不変 complement `X⧸S` (`⊓=⊥`/`⊔=Ω₁` を field 化, `S≤X`)。Thm 4.12(a) a-3 / Thm 4.16 B-2 が直接呼べる。
- 経路 = Ω₁ を `F_p[A]`-加群化 (`mulAutToEnd ∘ quotientMulAutHom.restrict`) → `Subrepresentation` + `IsSemisimpleRepresentation` (mathlib Maschke) で complement → order-iso (`AddSubgroup.toZModSubmodule`/`Subgroup.toAddSubgroup`) で R の subgroup に復元。
- ⚠ 設計書 (`s04_n4_maschke_bridge_design.md`) は `mapSubmodule`/`asModule` 経由を想定したが, **`asModule` の AddCommMonoid 二重 instance (derived vs AddCommGroup.toAddCommMonoid) の defeq trap** で詰まり, **`Subrepresentation` 経由に変更** (V=Additive ↥E 上で instance 一貫, asModule 合成不要)。実装者向け教訓として記録。
- sorry-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`), `lake build OddOrder` green (3354 jobs)。`OddOrder.lean` に import 追加済。
- 補助: `isElementaryAbelian_omega_one_of_comm` / `neZero_natCast_zmod_of_coprime` / `isAInvariant_{map_mk',comap_mk',subgroupOf_restrict,map_subtype_of_restrict}` / `mulAutToEnd` (AppA private helper の自前複製; 将来 AppA と共有 module 化候補)。

→ **Thm 4.12(a) (Huppert, metacyclic+[R,A]=R⇒abelian) の最深 gate が開いた**。次候補 = Thm 4.12(a) 本体 (N-4 + Lem 4.10✅/4.5(b)✅ で書ける) / Prop 4.11 (Huppert) / Prop 4.3(a) full。⚠ Ch04 `quotientMulAutHom` の `_root_` 欠落 (二重 nest 実名) は未修正 — 本ファイルは explicit 実名で回避 (S7A2 と同様)。

**Thm 4.12(a) building blocks 一部 + §5 infra 着地** (2026-05-31, workflow `bg-thm412-s5-fronthalf` wf_13fd7d0a-618, 11 agent, design→逐次 build-green→report, **全 landed を axiom-clean 独立検証済**):

- ✅ **`IsMetacyclic.isCyclic_commutator`** (c3c7a99, `IsMetacyclic.lean`) — metacyclic ⇒ R′ cyclic (a-2 部品)。
- ✅ **`isCyclic_of_card_omega1_le_prime`** (9891140, S04) — |Ω₁(R)|≤p ⇒ R cyclic (Lem 4.5 逆, a-3/a-4 engine, Isaacs Thm 6.11 経由)。
- ✅ **§5 S5-0 infra** = 新規 `OddOrder/GroupTheory/NarrowPGroup.lean` (bcfb437/b9484b0/8bc0601/2b1d685/539aeae): `IsNarrow` (r≤2 ∨ C_R(R₀)=R₀×R₁ cyclic) / `IsMaximalElementaryAbelian`(E*(R))+`exists_maximalElementaryAbelian_ge` / `omega1UpperCentralTwo`(W=Ω₁(Z₂(R)))+`commutator_upperCentralSeries_two_le_center`(Z₂ class≤2, genuine) + **Lem 4.5(c) exp-p 半** `pow_eq_one_of_mem_omega1UpperCentralTwo` + T=C_R(W) char/Z(R)⊆T。全 sorry-free/axiom-clean。
- ❌ wrapper `mulAut_comm_of_isCyclic` は意図的に不着地 (mathlib ZGroup.lean:169 の 1 行 idiom, caller 0, ラッパー方針で禁止 — agent の正しい判断)。

**両 leg の次 gate (workflow 設計が特定)**:
- **Thm 4.12(a) = D-a2 が最深难所** (mmd L1592-1600): A-不変 cyclic 極大 S の存在は軽いが **S◁R + S⊆Z(R)** が deep ((RA)′⊆C_{RA}(S) を半直積 R⋊[φ]A に lift)。hoist 厳禁。D-a2 後に D-a3 (Maschke 統合, N-4✅) → D-main → D-bc。設計 `notes/bg/s04_thm412_design_2026_05_30.md`。
- **§5 = Lem 4.7⇒ (=Lem 5.1(a), Gorenstein 5.4.15) と Lem 4.5(c) noncyclic 半 (=Lem 4.5(a) general, Gorenstein 5.4.10) が gate** (ともに §4 側で要)。§5 本体 (Lem 5.1/5.2/Thm 5.3/Cor 5.4) はこれら待ち。設計 `notes/bg/s05_design_2026_05_30.md`。
- ⚠ **§5 survey の「Lem 1.22 repo 不在」は誤り** — `normal_subgroup_card_pow_le_of_pGroup`@S01:1247 既存 sorry-free (workflow 訂正)。

## 完了条件

- BG Thm 4.16 が sorry-free / axiom-clean で `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` に着地。
- `lake build OddOrder` + `lake build OddOrder.AxiomsCheck` green。
- ⚠ **scaffold trap 厳守** (handoff §1): hard content を未充足仮説に hoist しない、`/goal` 単発不可、設計先行 + sub-issue 分割。

## 参照

- **handoff (cold-start 手順)**: `notes/bg/s04_thm416_handoff.md`
- 全体計画: `notes/bg/s04_implementation_plan_2026_05_30.md`
- BG 原典: `references/bg/local-analysis.mmd` L1636-1704 (Thm 4.16 本体)
- 既存: `OddOrder/BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean`, `OddOrder/GroupTheory/{PRank,SCN,CriticalSubgroup,IsMetacyclic,IsExtraspecial}.lean`
- 設計 workflow: `bg-s04-design` wf_39c356b8-eb2 / 実装 v1: `bg-s04-v1-impl` wf_ec23ca53-2a1
