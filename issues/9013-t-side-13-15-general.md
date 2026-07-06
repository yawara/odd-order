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

- [ ] **(案 A, 推奨) lane-b が §13 estimate ((13.10)/(13.11)/(13.14)/(13.15)) を generic type-II maximal
  subgroup 版に generalize** → C が S/T 両側で instantiate (cite)。非重複・signature-contract 準拠。
- [ ] (案 B) C が T-side dual を自 file で re-derive → **lane-b S-side と重複** (anti-doctrine, 非推奨)。
- [ ] (案 C) C は landing 待ちで別 ungated work へ (但し C 自クラスタは assembly 完了ゆえ別 work 不在)。

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
