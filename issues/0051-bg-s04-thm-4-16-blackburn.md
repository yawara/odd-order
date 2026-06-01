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
- [x] Thm 4.16 faithful statement を Lean に着地 (`blackburnRankTwoClassification`, proof は `sorry`) ✅ **2026-06-02**
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

**Thm 4.12(a) step a-2 完全着地** (2026-05-31, commits 017a888 / ce7645f, sorry-free / axiom-clean, build green 3359 jobs) — 設計 (`s04_thm412_design` §4) が「最深 山場」と名指した D-a2:

- ✅ `actionCommutator_le_centralizer_of_isCyclic_isAInvariant` (`OperatorQuotientAction.lean`): cyclic A-不変 normal `S ⊴ G` ⇒ `[G,A] ⊆ C_G(S)`。
- ✅ `isCyclic_le_center_of_actionCommutator_eq_top`: 上 + `[G,A]=⊤` ⇒ `S ⊆ Z(G)` (a-2 結論)。
- ✅ `exists_maximal_isCyclic_isAInvariant_commutator_le`: 極大 A-不変 cyclic `S ⊇ R'` 存在 (S 構成)。
- 🔑 **設計の半直積 RA ルート (`R=[R,A]⊆(RA)′⊆C_{RA}(S)`, ZGroup.lean:168 技法を RA に lift) は不要だった** — 共役作用 `α:G→*MulAut↥S` と制限作用 `ρ:=φ|_S` の同変性 `ρa·αg=α((φa)g)·ρa` + `MulAut↥S` abelian (S cyclic) で `α((φa)g)=αg`, 生成元 `g·(φa)g⁻¹` が `ker α=C_G(S)` に落ちる。**半直積を一切作らない**。
- 実装メモ: (1) `CommGroup (MulAut↥S)` を instance 登録すると canonical `MulAut.instGroup` と inv 競合のダイヤモンド → `have hcomm` で mul_comm のみ局所抽出。(2) `IsAInvariant.toMulAutHom_apply_val` は Ch04 `_root_` 欠落で二重 nest 名 → defeq (`change`/`congrArg Subtype.val`) で名前回避。

→ **Thm 4.12(a) の a-2 ビルディングブロック全完**。次 frontier = **D-a3 (Maschke 統合 `Ω₁(R/S)=Ω₁(R)S/S`)** (gate: D-a2✅ / N-4 Maschke✅ / Lem4.10✅ / LEAF-4✅ 全揃い) → D-main (|R|帰納) → D-bc。S⊴R は R'⊆S から即。

**Prop 4.11 (Huppert) 完全形式化完了** (2026-05-31, 逐次分解 workflow `bg-prove` ×3, 全 PASS 独立監査済) — §4 第2の山:

- ✅ (4.7) lift `exists_metacyclic_lift_of_isMetacyclic_quotient_center_prime` (be039f2): metacyclic 商 R/⟨z⟩ ⇒ ⟨a,z⟩◁R, R'⊆⟨a,z⟩, R=⟨a,b,z⟩, ⟨a,z⟩/⟨z⟩・R/⟨a,z⟩ cyclic (K-bundle 形)。
- ✅ step8 `isMetacyclic_of_isCyclic_commutator_of_card_omega1_le` (630cd73): R' cyclic + |Ω₁|≤p² + Odd p ⇒ metacyclic (maximal cyclic S + Lem4.5(b) + 唯一 order-p 部分群 ⇒ R/S cyclic)。
- ✅ main `isMetacyclic_of_omega1_card_le_prime_sq` (0ed392e, S04c, faithful 追加仮説0): |R|強帰納で 8 step 統合 (abelian base + (4.7)lift + Lem4.9 + 𝒰¹(R') 分岐: ≠⊥⇒K=⟨a⟩cyclic / =⊥⇒[a,b]∈Z⇒R'cyclic→step8)。新 private helper 4個 (Cauchy/closure-form/STEP4+5 bundle) 全て β 出力等から genuine discharge。
- 全 sorry-free / axiom-clean (`[propext, Classical.choice, Quot.sound]`) / `lake build OddOrder` green 3362 jobs。S04c_Prop411.lean 1150 行。

→ **Thm 4.16 Case A の gate (Prop4.11 + Thm4.12) が両方開いた**。Thm4.16 残ゲート = **Lem 4.13/4.14** (q∣\|Aut R\|⇒q∣p²-1, q<p; ⚠ "Lem4.7 and **G** Thm5.4.15" の Gorenstein行間)。

**Thm 4.16 最終ゲート = Gorenstein Thm 4.15 chain (2026-05-31, #9 BLOCKED_DESIGN が map)** — Lem4.13=G Thm4.15(ii) が **precursor(1) `pRank_le_two_of_scn3_empty` (=G Thm4.15(i)=SCN₃=∅⇒pRank≤2, §5共有) + precursor(2) (minimal ψ-inv⇒special exp p=G Thm3.7/3.10)** を消費。底辺補題 (G 3.9(i)/3.12/1.3.4/GL橋) は present。**完全 precursor tree + 実装順 + 7 anti-scaffold trap = [`../notes/bg/s04_lem413_gorenstein_precursors.md`](../notes/bg/s04_lem413_gorenstein_precursors.md)**。自走キュー #8.5→8.6→8.7→9。

**Gorenstein chain 進捗 (2026-05-31)**: `S04d_GorThm415.lean` に Gorenstein Lemma 4.12/4.13 (inline, commits e0378e9/34f04fb) + **Lemma 4.14** `omega1_centralizer_omega1_eq_omega1_of_maximal_rank`@S04d:857 (commit 17d0c0e) が着地し **S04d 全体 sorry-free**。自走キュー **#8.5 / #8.6 = PASS**。⇒ 残ゲートは **#8.7 precursor(1) `pRank_le_two_of_scn3_empty` (=G Thm4.15(i)=SCN₃=∅⇒pRank≤2; `S04_PGroupsSmallRank.lean:1036` にゲート明記、§5 も開く) → precursor(2) → BG Lem 4.13 (#9) → Thm 4.16 apex (#11, 未 statement)**。Thm 4.16 本体はまだ宣言されていない (docstring 言及のみ)。

**precursor(1) 分解 + easy-half 着地 (2026-05-31, workflow なし直接証明, 全 sorry-free/build green)**:
- ✅ `exists_maximalAbelianNormal_ge` (SCN.lean) — abelian normal ⊆ maximal abelian normal (finiteness)。
- ✅ `exists_maxRank_maximalAbelianNormal` (SCN.lean) — d_n を realise する maximal-abelian-normal A = Lemma 4.14 適用 companion (hA_maxAb / hA_maxRank をちょうど供給)。
- ✅ `normalAbelian_pRank_le_two_of_scn3_empty` (S04 §SCN3Empty) — **translation/easy half**: SCN₃=∅ ⇒ ∀ normal abelian B, pRank B ≤ 2 (= d_n≤2)。anti-scaffold TRAP 1 回避 (normal abelian のみ制約、R 全体の rank bound でない)。
- ✅ **GL-squeeze kernel 完成 (PRank.lean, 全 sorry-free)** = G 4.15(i) の唯一の難所だった数値核:
  - `card_le_prime_of_isPGroup_of_not_sq_dvd` — p²∤|G| ⇒ p-部分群 |K|≤p (抽象核)。
  - `card_pSubgroup_mulAut_le_prime_of_card_le_prime_sq` — elem-ab E (|E|≤p²) の MulAut の p-部分群は ≤p (p²∤|MulAut E|=∏(pⁿ-pⁱ) via `not_sq_dvd_prod_pow_sub`, n≤2)。GL(2,p) iso 不要、純 cardinality。
- ✅ **G Thm 4.15(i) 本体完成** `pRank_le_two_of_normalAbelian_pRank_le_two` (d_n≤2 ⇒ pRank P≤2, S04d, sorry-free): Lemma 4.14 を A に適用 → H=Ω₁A normal+elem-ab+|H|≤p² → φ=`MulAut.conjNormal(H)∘E.subtype` の range p-群 ⇒ |range|≤p → |E|=|range|·|ker φ| ⇒ |ker|≥p² ⇒ ker↦H ⇒ H≤E ⇒ E abelian で E≤C_P(H) ⇒ E≤Ω₁(C_P(H))=H ⇒ 矛盾。補助 `IsElementaryAbelian.log_card_le_pRank`@PRank。
- ✅ **precursor(1) `pRank_le_two_of_scn3_empty` COMPLETE** (commit c1d23e8, S04d) = G415i ∘ translation。**AxiomsCheck で axiom-clean 確認済** (3 標準公理, `OddOrder.BG.Ch1.S04.pRank_le_two_of_scn3_empty`)。→ **§5 (Lem 5.1(a) 等) と Thm 4.16 への gate が開いた**。残 §4 = precursor(2) (special exp p, G Thm 3.7/3.10) → BG Lem 4.13/4.14 (q∣p²-1) → Thm 4.16 apex。

**Thm 4.16 faithful statement visible (2026-06-02)**:

- ✅ `BlackburnCentralProductCase`: printed condition (2) をそのまま package — `R = R₁ ∘ R₂`, `R₁` nonabelian of order `p^3` and exponent `p`, `R₂` cyclic, `Ω₁(R₂)=R₁'` (both sides mapped into ambient `R`).
- ✅ `blackburnRankTwoClassification`: printed Theorem 4.16 statement — `p > 3` and either `R` is abelian or `BlackburnCentralProductCase p R`. Operator hypotheses use the existing §4 convention `φ : A →* MulAut R`, `Nat.Coprime (Nat.card A) (Nat.card R)`, and `actionCommutator φ = ⊤`.
- Verification: `lake build OddOrder.BG.Ch1_Preliminary.S04_PGroupsSmallRank` green.
- Remaining: proof body of `blackburnRankTwoClassification` and its upstream gates; the theorem is now visible in bare-`sorry` census.

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
