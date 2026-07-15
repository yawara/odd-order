---
id: 9013
slug: t-side-13-15-general
title: "HUB: T-side (13.15) v-value + frobenius-kernel exact-values — generalize lane-b §13 estimates for both sides"
created: 2026-07-06
---

# HUB: T-side (13.15) v-value + frobenius-kernel exact-values — generalize lane-b §13 estimates for both sides

**起票者**: lane c (/loop). **判断者**: hub / lane b. **種別**: cross-lane coordination (non-duplication)。

## 背景 (2026-07-06 確定, lane c 精査)

C の S16 (`S16_NonExistenceG.lean`) は **top-level `nonexistence_of_G` まで assembly 完了**。残 8 sorry は
**全て lane-b の §13/§15 char cascade body** に gated (lane-d は 2026-07-02 退役ゆえ無関係; 9000 σ-theory
divisibility/upper-bound は完成・frozen)。内訳:

- **v-value** (`T_side_caseB_facts:179`) = `v = (q^p−1)/(q−1)` = **T-side (13.15)**。`key_ratio_inequality_of_caseB_data`
  が `Tdata.v_eq` (exact) を要する (v は不等式の大側 → **lower bound** 必須。9000 は upper bound のみ)。
- **s/t_side_frobenius_kernel** (:2594/:2607) = field-model carrier (exact u/v 値要)。
- **carrier fields** (m_row/m_col/grid_mem :5294/5297/5315) + **1_G+Δ η-grid** (:6317) = S15 grid fields (issue 3002) + η-grid。

**exact u-value は C 内で proven** (`u_final_value`, (14.15) fpf-congruence route — (13.15) 非経由・ungated)。
だが **T-side には (14.15) 相当の route が無い** (v は (14.4) case-(9.7.b) = (13.15)-dual 直行)。

## やること (非重複の判断 = claim-before-build)

lane-b が §13 S-side estimate ((13.10)/(13.11)/(13.12) `c_eq_one`) を **active に building** (commit a1dc3748,
2026-07-05)。だが lane-b の版は **S-side hardcoded** (`hyp.c` 等)。T-side (13.15) v-value を閉じるには:

- [x] **案 A 採択 (HUB 裁定 2026-07-06)**: lane-b が §13 estimate
  ((13.10)/(13.11)/(13.14)/(13.15)) を generic type-II maximal subgroup 版に generalize
  → C が S/T 両側で instantiate (cite)。非重複・signature-contract 準拠。
- [x] 案 B は却下: C が T-side dual を自 file で re-derive すると lane-b S-side と重複する。
- [x] 案 C は却下: C は (14.9) type-III char exclusion の ungated infra を並行 engage。

## 完了条件

lane-b/hub が案を裁定。案 A なら generic §13 lemma export 後、C が v-value + frobenius_kernel exact-value を
cite で close (sorry 8→5 目安)。

## 参照

- `notes/peterfalvi/s16_w4_char_cascade.md` cont.⁷⁰/⁷¹
- lane-b commit a1dc3748 (Pf 13.12 c_eq_one, (13.10)+(13.11) 組立)
- `S16_NonExistenceG.lean`: `u_final_value:5874` (proven exact-u, (14.15) route), `key_ratio_inequality_of_caseB_data:1565`

## 🧭 HUB 裁定 (2026-07-06, POLE-2 coordination — routing)

**判定: 案 A (lane-b が §13 estimate を generic type-II maximal subgroup 版に一般化)**。理由:
1. **anti-duplication doctrine** — 案 B (c が T-side dual を自 file 再導出) は lane-b S-side estimate の
   重複ゆえ却下。
2. **territorial に自然** — §13 estimate ((13.10)/(13.11)/(13.14)/(13.15)/c_eq_one) は b の S15_SAndT(_Setup)
   所有・§13 keystone 領域。b は現に S-side を active building (commit a1dc3748/b6ddff8e、c_eq_one chain)、
   その generic 化は自然な延長。新 carve-out 不要 (b 自所有ファイル内)。
3. **c は idle にならない** — 案 C の懸念「c 別 work 不在」は不正確。c は唯一の ungated my-lane 深経路
   **(14.9) κ(T)≠σ'(T) の type-III char exclusion** (Γ-bridge + calT1 coherence → (14.8) 矛盾、cont.⁷⁰) を
   並行 grind 可能。b の generic §13 export が landing したら v-value/frobenius_kernel を cite で close。

**分担 (確定)**:
- **lane-b**: §13 S-side estimate を **generic type-II maximal subgroup 版に一般化** (現 `hyp.c` 等 S-side
  hardcoded → 抽象 type-II hypothesis 上で). export した generic lemma を C が S/T 両側で instantiate。
  b の §13 keystone (issue 3002 / 2035) work の一部として進める (優先順は b 自律、(3.9.a) fix と並走)。
- **lane-c**: (14.9) type-III char exclusion を並行 engage (ungated my-lane)。b の generic §13 landing 後、
  v-value ((13.15) `v=(q^p−1)/(q−1)` lower bound) + s/t_frobenius_kernel を cite で close (sorry 8→5 目安)。
- **lane-a**: 無関係 (§10-13 char core + §5/prime-TI、本 issue 非接触)。

**⟹ POLE-2 pipeline は健全に流れている**: c が S16 を top-level まで assembly 完了 = FT 最終矛盾の骨格が
組み上がった段階。残は b の §13 char body が S/T 両側の exact estimate を供給すれば閉じる。lane 数 3 維持。
9000 σ-theory は divisibility/upper-bound 完成・frozen (v-value の lower bound は §13 経路ゆえ 9000 非該当)。

## 🔎 追記 (2026-07-06 lane c、(14.9) char body 着手で判明) — d=1 が char body の linchpin

(14.9) char body (`T_typeIII_ratio_le`) を subagent が着手 (commit aa15383d、group-theoretic 基盤 4 lemma
= `T_derived_index_eq_p`/`T_Q_isComplement_V_derived`/`T_card_quot_Q_derived_eq_card_V` 等 sorry-free landing)。
**判明した linchpin**: char body は `|calT1|=(|V|−1)/p` を structural に導くが、goal は `(v−1)/p`。
両者の接続には **`v = |V|`** が要る。Lean では `Hypothesis.v` は free ℕ (`card_V_eq_vd: |V|=v·d` のみ)
ゆえ `v=|V| ⟺ d=1 ⟺ `S15.V_inf_centralizer_Q_eq_bot` (V⊓C_G(Q)=⊥) = **Pf (13.12) T-side dual**。

- **`V_inf_centralizer_Q_eq_bot` (S15:1885) は sorry + `_hTTypeII` 引数は UNUSED** (type II 非依存、nominal gating)。
- これは lane-b が既証明の `c_eq_one` (S-side (13.12)) の **T-side dual** = (13.10)/(13.11)-dual 要 = 本 issue 案 A の
  §13 generalization スコープ内。
- **⟹ 案 A の generic §13 に d=1 (T-side (13.12)) を含める**と、(14.9) char body の linchpin が解ける
  (v=|V| 接続 → `|calT1|=(v−1)/p`)。char apparatus (calT1 orbit count / S07 coherence instance / β_S bridge) は
  d=1 と独立の large follow-on ゆえ c が |V| 版で並行 build 可 (最終 v 置換のみ d=1 待ち)。

## 🔻 追記² (2026-07-06 lane c、(14.9) char body count assembly で確定) — char body の gate = lane-b S15 reconciliation

(14.9) char body の calT1 count を subagent が assemble 着手 (commit 17a5bdc7): **ungated glue は完成・green**
(`calT1_image_induce_card_eq` = orbit-count engine [T:QV]=p 特化 / `T_derivedSubgroupOf_normal`、+ 既landing
`OrbitOnIrr`/`FrobeniusGroupQuotient`)。だが `|calT1|=(|V|−1)/p` の残り2前提は **type-III branch で lane-b S15 gated**
(`#print axioms` 検証済):

1. **V abelian**: `typeP_hall_derived_eq_and_abelian` (BG 15.1b) は **(κ∪σ)'-Hall complement U** の abelian のみ
   (`T'=U⊔Mσ`)。Hypothesis の **V** (Q=M_F の complement、`T'=Q⊔V`) に届くには `M_F=Mσ` = **IsTypeP2 T** 要。
   type-III は `M_F ⊊ Mσ` 厳密ゆえ届かず。⟹ V abelian は `reconciled_typePData_T` (S15:sorried) 経由でのみ。
2. **Frobenius V⋊W₂** (`I_T(inflate θ)=QV` 用): 唯一 source `S11.typeP_uW1_frobenius` は `.U=V,.W1=W₂` の
   `TypePData T` 要 = `reconciled_typePData_T` (sorryAx: W2_le/centralizer_W1 消費)。

⟹ **char body の 3 前提 = lane-b S15 に集約**: `reconciled_typePData_T` (V-abelian + Frobenius、Hypothesis 抽象
V/W₂ ⇄ type-P 構造の reconciliation) + **d=1** (v=|V|)。S07 coherence / β_S bridge も同 gated facts を消費。

**⟹ C は (14.9) の ungated infra を全 build 完了** (reduction→skeleton→foundation→orbit-count engine→Frobenius
transport→structural glue、全 proven/green)。char body は lane-b の `reconciled_typePData_T` + `d=1` landing 待ち
(consume 態勢)。案 A の §13 generalization に **`reconciled_typePData_T` の discharge (or type-III-usable な
V-abelian/Frobenius export)** を含めれば C が即 cite で count→coherence→β_S→ratio を組める。

## 🟢 追記³ (2026-07-06 lane c /loop) — `reconciled_typePData_T` を complement-conjugacy で partial discharge (5→4)

`reconciled_typePData_T` (S15_SAndT_Setup:4035) の 5 structural sorried field を精査、**upstream-only な
complement-conjugacy で closable なものを実証明** (commit `fc2a1523`):

- ✅ **`U_nilpotent` (V nilpotent) landed** — 新 `Hypothesis.isNilpotent_V`: `V` と bare 型-P complement
  `tpd0.U` (`typePData_of_isTypeNonI T_nonI`) は共に `Q=T_F` を `T'=QV` で complement → Schur–Zassenhaus
  共役 (`exists_conj_of_coprime`, coprimality from `Q` Hall) が `tpd0.U → V` を写し `IsNilpotent` を transport。
  S16 `isMulCommutative_typePData_U_of_V` の mirror。**upstream-only facts のみ**ゆえ Setup 位置で証明可能。

- ⏭ **`fitting_eq` / `secondDerived_le_fitting` は同 U-conjugacy で closable (次 iteration 実装予定)**:
  `TypePData.conj (MulAut.conj g)` (g = 上記共役元、g∈T ゆえ `(conj g)•T=T`) で `tpd0` を写すと `d.U=V`,
  `d.H=Q` (Q は conj-invariant) → `d.fitting_eq`/`d.secondDerived_le_fitting` が reconciled 版を直接供給
  (Q/F(T)/T'' は char/normal ゆえ conj-invariant、U-factor のみ V に写る)。要 subgroupOf→G-level lift
  (`map_map` + `map_subgroupOf_eq_of_le` + `pointwise_mulAut_smul_eq_map`) + cast (`eq_rec_constant`)。

- 🔒 **`W2_le` (W₁≤Q⊓T'') / `centralizer_W1` は残 gate**: W-factor alignment (`tpd0.W1^g=W₂`) 要 =
  full simultaneous reconciliation、OR downstream `W1_le_Q` (S15_SAndT:1218) の上流 hoist。**file topology
  block**: reconciled は Setup(上流)、ingredient は S15_SAndT/S13(下流) → reconciled を下流移動 or
  ingredient 上流 hoist が要 (lane-b/hub 設計判断)。

**⟹ lane-b へ**: `U_nilpotent` は済 (重複回避)。残 4 field の内 `fitting_eq`/`secondDerived_le_fitting` は
上記 recipe で c が続行、`W2_le`/`centralizer_W1` の topology 解消 (下流移動 or hoist) は設計判断。

### 追記⁴ (2026-07-06 同 /loop、subagent 実装完了) — `reconciled_typePData_T` **5→2** 達成

`fitting_eq` + `secondDerived_le_fitting` も **実証明・landed** (commit `d3917274`、build green 3882 jobs)。
新 helper `Hypothesis.exists_typePData_U_eq_V` (`∃ d:TypePData T, d.U=V ∧ d.H=Q`、TypePData.conj で U-共役を
whole-datum transport) から両 field を rw で discharge。**reconciled_typePData_T は 5→2 sorries**
(U-conjugacy-derivable な U/intrinsic 3 field を全 close)。

**残 2 field は verified 深部 σ-structure (lane-b 領域、c 導出不可)**:
- `W2_le` (W₁≤Q⊓T'') は **PRIMARY fact** — `W1_le_Q` (S15_SAndT:1218) 自身が `reconciled_typePData_T` の
  `W2_le` を消費して W₁≤Q を出す ⟹ W2_le を W1_le_Q で埋めると**循環**。W2_le は §16 T-side 構造から直接要。
- `centralizer_W1` (∀x∈W₂#, T'⊓C_G(x)=W₁ = 双対 cyclic factor 特性) も同様。
- S-side は carried `Sdata` (§16 construction 供給) から両 field を無料取得。T-side は carrier 不在 (設計)
  ゆえ reconciled が代替、この 2 field のみ §16 T-side 構造 (W-factor simultaneous conjugacy or
  intrinsic W₁ characterization) を要 = lane-b σ-structure。c は U-side を出し切った (principled stop)。

## ⚖️ HUB 補足 (2026-07-06 夕, c FOLD 裁定, wf_00a0db07)

c の S16 領域枯渇で **c を DORMANT cite-sink 化** (正本 = ft_lane_reallocation「lane c FOLD」節)。本 issue の残 2 gate の
帰属を確定: **W2_le / centralizer_W1 = lane-b** (§15-16 T-side W-factor σ-structure、9017 と連動)、**§13 v-value
lower-bound export (案 A) = lane-b**。これらが landing すれば **c が reactivation trigger で自動再開**し S16 の
`reconciled_typePData_T` 残 field + T-side cascade を assemble。c は本 issue で新規 build しない (b 待ち)。

## 🟢 追記⁴ (2026-07-07 lane c, ユーザー裁可「(13.15) numeric engine を build + 9000 flag」) — engine LANDED

ユーザーが C 明示再開 → v-value の精密 trace で **v-value → (13.15) → (13.12) c=1/d=1 →
`pc_le_maxNilpotentNormalHall` (bare sorry) → typeP_Galois (issue 9000)** を確定 (V-abelian と同根)。
S-side `caseB_order_u` (13.15) も bare sorry (両側とも (13.15) exact 値は未形式化) で、b の proven lemma の
dup でなく fresh formalization。ユーザー裁可に従い **genuine・ungated・非-dup な (13.15) numeric-elimination
engine を新 c-owned leaf `OddOrder/Peterfalvi/S16_CaseBOrder.lean` に実証明** (sorry-free, build green):

- **`caseB_order_x_absurd_of_ge`**: cofactor `x ≥ 2q+1` は不可能。`c_eq_one_forces_params` (13.12) と
  同型 (analytic ineq (13.10) + (13.11) m-bounds → q=3 → p∈{5,7}) だが **endgame は純算術** —
  `x ∣ (p²+p+1) ∈ {31,57}` with `u≠1`, `q∤u`。**structural residual なし** (13.12 と対照的、後者は
  `pc_le_maxNilpotentNormalHall` = typeP_Galois gated)。
- **`caseB_order_u_full_of_not_modEq`**: 非-(p≡1 mod q) branch → `u = (p^q−1)/(p−1)`。(13.14)
  divisor-congruence (`cyclotomic_quotient_dvd_modEq_one_of_not_modEq_one` = proven) で `x≡1 mod q`,
  x odd ⟹ x=1。
- `cyclotomic_quotient_three` helper ((p³−1)/(p−1)=p²+p+1)。

**char/σ-theory 入力は全て仮説パラメータ**: m-value (13.9)・analytic ineq (13.10) with c=1/d=1・
(13.11.c) bound は engine の hypothesis (gated-endpoint skeleton pattern)。⟹ **engine は ungated**。
T-side v-value `v=(q^p−1)/(q−1)` (14.4) は **p↔q instance + `q≢1 mod p`** で `caseB_order_u_full_of_not_modEq`
に直結 (caller が analytic ineq を供給、それが 9000 に bottom-out)。

**⚠ 9000 FLAG (ユーザー裁可の「9000 flag」部分)**: v-value + V-abelian (T_not_isTypeIV) + a の (10.7)/(10.8)
+ S/T frobenius kernel が **全て typeP_Galois (issue 9000, d claim 済・a と dup 履歴の deep σ-theory
= semilinear/near-field dichotomy Pf 9.7) に収束** = multi-consumer root gate。9000 が landing すれば
本 engine を cite して v-value + caseB_order_u 両側が閉じる。9000 の allocation (d claim vs a-dup vs 優先度)
は hub/ユーザーの cross-lane 判断事項。**c は本 engine で (13.15) の ungated 部分を前倒し完了**、9000 landing
待ちで caller wiring (S16 T-side + S15 caseB_order_u instantiation) を assemble。

## 🟢 追記⁵ (2026-07-07 lane c 再開、ユーザー「C レーン再開」) — engine dichotomy 完成 + T-side v-value に WIRED (gate isolate)

前 session の未コミット WIP (`caseB_order_u_div_q_of_modEq`) を完結させ、engine を FT spine に**実接続**。

**(1) (13.15) dichotomy 完成** (commit `5476b09b`, `S16_CaseBOrder` sorry-free green):
- `caseB_order_u_div_q_of_modEq` (**`p ≡ 1 mod q` 分岐** → `u=(p^q−1)/(q(p−1))`): (13.14)
  `cyclotomic_quotient_dvd_of_modEq_one` で `q ∣ Singer=u·x` + `q∤u` ⟹ `q∣x`; `x=q·t`, x odd ⟹ t odd,
  `t≠1` ⟹ `t≥3` ⟹ `x≥3q≥2q+1` を `caseB_order_x_absurd_of_ge` で排除 ⟹ `x=q`。
- `caseB_order_u_value`: 両分岐を **`caseB_order_u` (S15:8390 bare sorry) と同一 conjunction 形**に組立
  (9000 landing 後に Hypothesis データで instantiate → discharge 可能な shape)。

**(2) T-side v-value を engine に WIRED** (commit `6dd5f456`, `S16_NonExistenceG` green 3903 jobs):
`T_side_caseB_facts.2` = Pf (14.4) `v=(q^p−1)/(q−1)` が **`caseB_order_u_full_of_not_modEq` を p↔q swap で
cite**。ungated arithmetic を call site で honest に discharge: primality/oddness/branch-selector
(`q_not_modEq_one_mod_p`) + **`¬p∣v`** ((13.14)-dual divisor congruence: `p∣v∣Singer ⟹ p≡1 mod p` 矛盾) +
**`h11c` は T-side で vacuous** (p≥5≠3, `five_le_p`)。gate は **1 命名 lemma `tSide_caseB_v_gated_inputs`**
に isolate: cofactor `x` (`v·x=Singer`) + T-side norm param `mᵀ` の (13.11)-dual bounds + (13.10)-dual
analytic ineq + `v≠1`。net real sorry 不変 (10→10) だが engine が **used** + gate typed。

**(3) 検証済み findings (issue の従来分析を精緻化)**:
- **Peterfalvi 04.16 p.87 精読**: (14.4) の v-value は (13.15) の **直接 black-box 適用** (「q≢1 mod p, and so
  v=(q^p−1)/(q−1) by (13.15)」)。engine が正しいツールと確定。char inputs は (13.15) **内部証明**の一部で,
  T-side 適用時は generic §13 estimate (案 A) が供給 = gated。
- **⚠ 従来「T-side = p↔q instance (同一 m)」は不正確**: engine の m-bound `hm5:5≤(engine-q=p)→7/10<m` は
  p≥5 常成立ゆえ `7/10<m` を無条件要求するが、**q=3 のとき S-side m≈0.5<0.7** (formula
  `m=1−1/(q−1)−…`)。⟹ T-side は S-side と同一 m では通らず **T-side 固有の mᵀ** (dual formula, p≥5 で
  `7/10<mᵀ` は arithmetic) を要する。案 A の generic §13 は **T-side mᵀ + その bound** を含む必要あり
  (単純な変数 rename でない)。
- **h11c は T-side 不要** (vacuous, p≠3) — 案 A の T-side instantiation で (13.11.c)-dual bound は不要。
- **最終矛盾の算術 core は既 proven** (`caseB_forces_q_three_and_p_five`:6700 / `pq_lt_v`:2494 /
  `norm_cascade_contradiction`:2980、全 ungated)。C の残 10 sorry は全て char/field/grid gated。

**⟹ lane-b/hub へ**: 案 A の generic §13 export に **(i) T-side mᵀ 定義+bound (dual formula)、(ii)
cofactor `v∣Singer` (field-model TFieldModelData 経由)、(iii) analytic ineq (13.10)-dual** を含めれば、
C が `tSide_caseB_v_gated_inputs` を即 discharge (v-value close)。h11c-dual は不要。

## 🔗 lane-c → 9013 downstream 依存の精緻化 (2026-07-07 lane c, post-horth)

**C の (14.9) coherence side は完了** (issue 9072 CLOSED, commit `c8875eb2` → 統合 `06d5a0cb`):
`T_typeIII_ratio_le` の `horth` coherence carrier を実証明 (`T_typeIII_hyp07` + `irrSubcoherent` で Dade package
構成)。上記裁定 (2026-07-06) の「c は (14.9) を並行 grind」の grind は **coherence 部分が landing 済**。⟹
9013 landing 後に C が cite で close する残 consumer が確定:

1. **`tSide_caseB_v_gated_inputs` (S16:1962)** — (i)-(iii) で即 discharge (既述、v-value close)。
2. **`T_typeIII_ratio_le` (S16:1563) の残 2 sorry**:
   - **`hcard2 : 2 ≤ calT1_set.ncard`** — `|calT1_set|=(|V|−1)/p` は **proven** (`T_typeIII_calT1_family`)。
     残 = `(|V|−1)/p ≥ 2` = **`|V|` 下界**。d=1 で `v=|V|` (`S15.V_inf_centralizer_Q_eq_bot`) を通せば 9013 の
     v-value lower bound に接続 (上記「d=1 linchpin」節と同経路)。
   - **S-side βₛ bridge** (`Γ=∑x_ζ·τ₁ζ+Γ₁` + norm `⟨Γ,Γ⟩≤(u−1)/q`) — coherent count `|calT1|=(v−1)/p`
     (proven) + **S-side βₛ** (Coq `nzT1_Ga`, `S09.cfdot_real_vchar_even`)。⚠ v-value gate とは**別カテゴリ**
     (S-side βₛ construction 依存); 9013 の scope 外なら別途 tracking 要 (S16 コメント S16:1642-1649 に isolate 済)。

C 側 coherence machinery (`horth`/count/isometry) は全て proven。9013 の v-value + (別 issue の) S-side βₛ が
landing 次第、`T_typeIII_ratio_le` は薄い cite で閉じる。sorry 目安は当初裁定の 8→5 から、horth 完了で
**coherence carrier 分を先取り済**。

## 🧭 HUB RULING (2026-07-07, issue 0098 レーン再点検): de-scope 2 件

hub 裁定 (詳細 = issues/0098-lane-rebalance-c-reactivation.md、調査 = wf_d4994964):

1. **item (i) T-side mᵀ 定義 + 7/10<mᵀ 算術 bound → lane c に de-scope**。c 検証済みの純算術で、
   plug 先も c 所有 engine (S16_CaseBOrder)。**b のファイル編集ゼロ**。b の案 A deliverable は
   **(ii) cofactor v∣Singer + (iii) (13.10)-dual analytic ineq + d=1 (V_inf_centralizer_Q_eq_bot)** に縮小。
   estimate-generalization は従来通り b (instantiation のみ c、案 B 再演の dup 禁止)。
2. **S-side βₛ bridge (13.18) の ownership gap を解消**: **lane c への decl 領域限定 carve-out**
   (S15_SAndT.lean:3616 `BetaData := sorry` 周辺; reconciled_typePData_T carve-out の前例に同じ)。
   c が Γ = τ_S(β_#1) − 1 + η_01 構成 + facts を build、b は cite。上記「9013 の scope 外なら別途 tracking 要」
   への回答 = 本 carve-out で tracking。
3. 追記³ の file-topology 分岐 (reconciled downstream 移設 vs ingredients hoist) は **hoist-upstream で解消方向**:
   c が typeP_pair port (Pf §8, 新 shared leaf, claim-before-build) を build し、自身の carve-out 内
   W2_le (S15_SAndT_Setup:4520) / centralizer_W1 (:4590) を discharge する (0098 パッケージ item 1)。

## 🔧 訂正 (2026-07-07 lane c, commit `bf3b21f4`) — `hcard2` は 9013 非依存だった

上の「🔗 lane-c → 9013 downstream」節で `T_typeIII_ratio_le` の `hcard2` を 9013 consumer に挙げたが、
**これは誤り**。`hcard2 : 2 ≤ (|V|−1)/p` の **crude ≥2** は odd-order Frobenius `U⋊W₁` (|U|=|V| odd,
|W₁|=p odd) の size 条件 `2p+1 ≤ |V|` から **ungated で従う** (新 lemma `T_typeIII_two_p_add_one_le_card_V`、
commit `bf3b21f4`、0098 item 5)。9013 の `v`-value lower bound は **exact count `(v−1)/p` にのみ必要**で、
coherence input の `≥2` には不要。⟹ **9013 が unblock する C の `T_typeIII_ratio_le` consumer は S-side βₛ
Γ-bridge 1本のみ** (`hcard2` は除外)。

## ✅ 案A item (iii) 部分 landing (2026-07-07 lane b, /loop) — 側非依存 analytic core を抽出

案A の deliverable (b が §13 estimate を generic type-II 版に一般化) の**中核**を landing:

- **新 sorry-free 定理 `analytic_singer_m_bound`** (`S15_SAndT_Setup.lean`, `c_eq_one` 直前) —
  (13.12) の**側非依存 analytic core**を pure `ℚ`-arithmetic として抽出:
  ```
  {a b u c : ℕ} {m : ℚ} (hbR : 0<b) (hcR : 0<c) (haR : 1<a)
    (hanalytic : u/c > m·a^(b−1)/b)      -- (13.10)
    (hsinger   : u·(a−1) ≤ a^b − 1)      -- (13.2.c) Singer UPPER
    ⊢ m < b·(a^b−1) / (c·a^(b−1)·(a−1))
  ```
- **`c_eq_one` を refactor して cite** (S-side = `a=p, b=q, u=u, c=c`) — faithful 化を build で実証
  (leaf green 3882 jobs、S15_SAndT_Setup real sorry 12→12 不変 = 純増分の proven 補題)。
- **c への含意**: T-side `d = 1` (`V_inf_centralizer_Q_eq_bot`) は同 core を `a=q, b=p, u=v, c=d` で
  instantiate すれば assembly が済む。**core は Singer UPPER のみ使用ゆえ ungated** — c は (14.9) type-II
  structure が landing 次第、T-side の (13.10)-dual + T-side Singer を供給して cite するだけ。
  (9013 の `v`-value LOWER bound gate は ratio 不等式 = 別 consumer で、この core には入らない。)
- **残 (案A の未 landing 部分)**: (ii) cofactor `v ∣ Singer`、T-side numeric elimination
  (`c_eq_one_forces_params` の T 版 = q^p vs p^q で非対称ゆえ別途要)、および V_inf 本体の
  (14.9)-gate。これらは c の (14.9) landing 待ち。

## 🟢 追記⁶ (2026-07-07 lane b、0099 landing 後の §13 原文精査) — **(13.4) が T-side d=1 + v-full の最短供給路** (案A の再スコープ材料)

0099 (S07 isometry 弱化、mixed-family S07.Hypothesis unblock) を landing した後、案A (iii) の実装前に
Pf §13 の依存構造を原文精査 (04.15 mmd:49-58/144-180/206-232/258+) して確定した load-bearing 事実:

1. **Pf (13.4) の内容 = 「𝒮 が deg-uq induced-from-linear-of-PC な irreducible λ を含む ⟹ case (9.7.b)
   for M=T, D=1, v=(q^p−1)/(q−1)」**。つまり **T-side の d=1 と v-full は、T-side (13.10)-dual cascade
   を経ずに (13.4) 一発で出る** (λ-branch)。証明は短い grid 直交性論法: (H^#)^G ∩ (K^#)^G = ∅
   (K=QD) + disjoint-support Dade 直交 (α^τ,β^τ)=0 + (13.3.c) 両側 grid 展開 → 0 = ±(η_rs,η_rs) = ±1 矛盾。
2. **§13 の branch 構造**: (13.3.b) = 「族に induced-linear irreducible が**無ければ** (9.7.b)+trivial
   centralizer+full value がタダで従う」(per side、§9 (9.8.c)/(9.9.a,c))。(13.4) = λ ∈ 𝒮 なら T-side が
   タダ。∴ T-side (13.10)-dual cascade ((13.12)/(13.15)-on-T) が真に要るのは
   **case 3 (𝒮 に λ 無し ∧ 𝒯 に θ 有り) のみ**。
3. **(13.4) は S-side (13.10) の唯一上流でもある**: (13.10) の h2/TT 計数
   (`TT = 1/p − 1/(p(q−1)) + 1/(p(q−1)q^p)`) は「By (13.4), D=1 and v=(q^p−1)/(q−1)」を代入して得る
   (mmd:174)。Lean 側も同構造: `lambda_forces_T_caseB` (S15:2300, **sorried**) を
   `analyticEstimate_*`/counting chain が 4+1 箇所で cite (S15:6903/7063/7101/7179/7314)。
   ∴ **(13.4) は 案A (iii) より文書順・依存順の両方で上流** — b の次 frontier はこれ。
4. **c の wiring への含意** (拘束でなく option): `T_side_caseB_facts` (S16:2069) の 2 conjunct は
   λ-branch では (13.4)+(13.3.b)-dichotomy 直 cite で閉じ得る (V_inf/`tSide_caseB_v_gated_inputs` 経由の
   (13.15)-on-T route は case 3 用に残る)。engine (S16_CaseBOrder) は無駄にならない (case 3 + S-side
   (13.15) 本体が consumer)。

**campaign 分解 (13.4 = `lambda_forces_T_caseB` S15:2300)**:
- (a) **T-side (13.3.b) dichotomy producer** [gate: §9-on-T (9.8.c)/(9.9.a,c) — by_contra branch で
  θ ∈ 𝒯 (irreducible, induced from linear of K=QD, deg vp) を供給]
- (b) **T-side ν₁-grid formula** [(13.3.c)-on-T: ν₁^{τ₁T} = ±Σⱼ η_{rj} — CharacterDegreeData は tau1T を
  carry 済みだが T-side property fields 未搭載 → 追加 or T-side data 構造]
- (c) **A₀(T)-TI の materialize** [(13.2.e)-on-T: 現状 `A0S_TI` は opaque Prop (:= True) パターン;
  proven `Q_sharp_isTISubset` (S15:4768) は D=⊥ 特殊形 — by_contra branch では K=QD ⊇ Q ゆえ
  K^# ⊆ A₀(T) の TI が要る]
- (d) **b-buildable core (ungated)**: H^#/(K^#)^g 非交差 (x ∈ H^# ⟹ P ≤ C_G(x) [P elem-abelian
  (13.2.b) + C = C_U(P)] + C_G(x) ≤ T^g [TI] + |P|=p^q > p = T の p-part 矛盾) +
  disjoint-support 内積 0 (元素的) + grid 展開の直交 bookkeeping (η pairwise orthogonal
  (tau1S_induce_inner_eta 既 field) + λ^{τ₁}⊥θ^{τ₁T})。
- 実装形: `lambda_forces_T_caseB := by by_contra` → (a)(b)(c) を **精密 sorried T-side producer 1 本**
  (「¬結論 ⟹ θ+ν-grid+TI」bundle) に隔離 → (d) を実証明。reconciled_typePData_T と同じ
  precise-reduction パターン。

### ✅ 追記⁶ 実施 (2026-07-07 lane b) — (13.4) `lambda_forces_T_caseB` **本体組立 PROVEN** (bare sorry → typed gates 3 本)

campaign (a)-(d) を実施、`lambda_forces_T_caseB` は **sorry-free 組立**になった (S15_SAndT_Setup、
full build green 3934 jobs)。landed bricks (全て実証明):

- `Hypothesis.P_le_centralizer_of_mem_H` — x ∈ H = PC ⟹ P ≤ C_G(x) (H abelian 経由)
- `Hypothesis.eta_orthonormal` — η-grid 直交正規性 (tau3_isometry + omega_orthonormal)
- `eta_cross_expansion_ne_zero` — endgame: ⟨λ°−δΣᵢη_is, θ°−δ'Σⱼη_rj⟩ = δδ' ≠ 0
- `disjoint_conjugatesIntoSet_of_centralizer` — 共役非交差 core (abstract、gates 仮説化)
- `inner_induce_induce_eq_zero_of_disjoint` — 非交差支持 ⟹ (α^τ, β^τ) = 0
- 本体: α = λ − μ_{j₀} の H^#-支持 (H ⊴ S = `H_sharp_subgroupOf_normal` + 等次数) +
  τ₁-additivity + (13.3.c) column formula で α^τ = λ° − δΣᵢη_{i1} に書換え → 矛盾。

**残 gate 3 本 (typed sorry、S15 内 sorry 11→13 net +2 = bare→精密の交換)**:
1. `QD_sharp_centralizer_le_T` — (13.2.e)-on-T: K^# = (QD)^# 点の中心化 ≤ T (A₀(T)-TI の
   materialize。proven `Q_sharp_isTISubset` は D=⊥ 特殊形)
2. `P_conj_forall_not_le_T` — p-part: P^w ≰ T (|P| = p^q > p = |T|_p; |Q| q-群性 =
   reconciled_typePData_T 圏)
3. `tSide_theta_package_of_not_caseB` — (13.3.b,c)-on-T char package (¬結論 ⟹ θ ∈ 𝒯 +
   ν_r-row grid formula + η/λ° 直交)。**§9-on-T (9.8.c)/(9.9.a,c) + T-side τ₁T 意味論が実体**
   — c の 9073 typeP_pair port / reconciled と同圏の T-side char 構造。

⟹ S-side (13.10) chain (analyticEstimate_* 5 cite) と T-side d=1+v-full の唯一上流が
bare 1 本から**構造 3 gate に精密化**され、うち 2 本 (TI/p-part) は group-theoretic
(char 不要)。次: gate 2 本の group-theoretic 攻略 (Q_sharp_isTISubset の一般化 route) →
gate 3 は §9-on-T の形式化計画とセット。

### 🔓 9073 完結 (c、reconciled_typePData_T 完全 sorry-free) による gate unlock map (2026-07-07 lane b 調査)

merge 700f92d4 で `reconciled_typePData_T` が sorry-free になり、(13.4) 残 gate の材料が大きく前進:

- **gate 2 `P_conj_forall_not_le_T` は discharge 可能になった (route 確定)**:
  `|Q| = q^p` は `card_Q_eq` (S15_SAndT:2241) / `Q_elementaryAbelian_T` (:1823、**proven**、内部で
  Wielandt (9.3) order relation `|H| = |W₂|^|W₁|` を reconciled-setupT 経由で計算)。`p ∤ |V|` は
  V⋊W₂ Frobenius (reconciled + `typeP_uW1_frobenius`、`centralizer_W2_inf_V_eq_bot` :1299 が
  access パターンの実例) の kernel-complement 互素性。`|T| = |T'|·p` は `W2_isComplement_T_deriv`、
  `|T'| = |Q|·|V|` は `Q_inf_V_eq_bot` + `T_deriv_eq_QV`。⟹ v_p(|T|) = 1 < q ⟹ P^w ≤ T 不可能。
  **⚠ 設計注意**: この route は `hTTypeII : IsTypeII hyp.T` を要する (Q_elementaryAbelian_T /
  card_Q_eq の前提、TypeIIData.common の V≠⊥ + Wielandt type-II branch)。だが
  `lambda_forces_T_caseB` は現 signature に T-type hypothesis を持たない ((13.2.a)-on-T は
  「T type II **or III**」)。選択肢: (i) gate 2/1 に hTTypeII を持たせ (13.4) にも threading
  (5 cite site 修正、S16 は T_typeII proven 済で供給可)、(ii) type III branch でも同じ order
  relation が成るか typeII_III_IV_order_relations .2 を確認して II∨III で閉じる。
  **次 iteration の最初の設計判断**。
- **gate 3 の router が実在**: `Q_elementaryAbelian_T` の証明が `setupT : TypesIIIIIIVSetup hyp.T`
  を reconciled tpd から**インライン構築済み** (S15_SAndT:1837-1841)。これを def
  `toTypesIIIIIIVSetupT` に抽出すれば §9 machinery ((9.8)/(9.9)、typeII_III_IV_order_relations
  等) が T 側で cite 可能になる = θ-package ((13.3.b)-on-T) の形式化基盤。
- gate 1 (A₀(T)-TI) は unlock 対象外 (TI は σ-structure の別系統、Q_sharp_isTISubset の
  一般化 or A1_eq_sigmaSharp 系 route)。
- 別途: S15_SAndT の reconciled-gated だった b-queue (`complement_inf_Q_structure`:3060 等) も
  再点検対象 (V_inf:1887 は analytic chain 要で対象外のまま)。

### ✅ gate 2 discharge 完了 (2026-07-07 lane b、commit 62fb13a8) — (13.4) 残 gate 3→2

**`P_conj_forall_not_le_T` を type-free で実証明** — 上記「⚠ 設計注意」の hTTypeII threading は
**不要と確定** (route を type-free に組み替え): p ∤ |Q| は **Hall 性** (maxNilpotentNormalHall_isHall +
index = (v·d)·p、type 不問)、p ∤ |V| は **V⋊W₂ Frobenius** (typeP_uW1_frobenius は TypePData のみ要 +
card_kernel_modEq_one、V=⊥ 場合分け) — どちらも IsTypeII 不要。|T| = |Q|·(v·d)·p (card_T_eq、
reconciled 消費) + Lagrange + 純 Nat 算術で v_p(|T|) = 1 < q。(13.4) block は card_T_eq 後方へ移動。

**残 gate 2 本の攻略 route (次 iteration)**:
1. **gate 1 `QD_sharp_centralizer_le_T`**: 有望 route = **c の 9072 S10 機構**。
   `S10.dadeSupportHypothesisData_of_subset_sigmaSharp` (ungated、hub 検証済) が
   `X ⊆ sigmaSharp T` に対し Dade support datum を返す — その TI/centralizer 性質 field を確認し、
   `(QD)^# ⊆ sigmaSharp T` (Q = T_F ≤ M_σ ✓; **D ≤ M_σ(T) が要検証** — D = V⊓C(Q) の σ-性) を
   併せれば gate 1 が S10 cite で閉じる可能性。要調査: DadeSupportHypothesisData の fields +
   sigmaSharp の TI property (`Msigma_TI`?)。
2. **gate 3 `tSide_theta_package_of_not_caseB`**: router = TypesIIIIIIVSetup T の抽出だが、
   `type_alt : IsTypeII ∨ IsTypeIII` field が **T の型判定を要求** — S15 レベルでは T_nonI のみ
   carry (IsTypeII T は S16 (14.9) 結果で forward-sorry 付き)。選択肢: (a) (13.2.a)-on-T
   (「T type II∨III」 = (10.10)+(11.9.b,c) on T) を S15 で materialize (basic_structure の T-mirror、
   type V/IV 排除)、(b) θ-package の statement に type_alt を仮説として持たせ S16 から供給。
   文書順は (a) が本筋 ((13.2.a) は §13 冒頭)。その上で (9.8.c)/(9.9.a,c)-on-T の cite 網を確認。
