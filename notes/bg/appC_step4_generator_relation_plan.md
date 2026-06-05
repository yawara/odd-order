# BG App.C Lemma C.3 Step 4 — generator-relation `s₁ = s⁻¹` 形式化 plan (2026-06-05)

**スコープ**: BG Appendix C, Lemma C.3 **Step 4** (mmd L4994–5095) の核 = 正規形の中央
prime-line 因子が `c = -1` (= `s₁ = s⁻¹`) であることの確定。これが App.C に残る**唯一の数学的
ギャップ**であり、`S16.FieldNormalizerData.appC_twisted_normOne_step` という producer obligation
1 点に集約されている。完成すれば `appC_twisted_normOne_step` を構造体 field から**削除**でき、
BG App.C 経路 (`theoremC` → `final_contradiction`) が carrier だけで閉じる。

正本: 本ノート。先行: `notes/bg/appC_final_contradiction.md` (位置づけ) /
`notes/bg/appC_normset_plan.md` (有限体核 — **完成済**, 「残 3 ブロック」記述は stale) /
`notes/meta/s16_appc_downstream_audit_2026_06_04.md`。

---

## 🚩 次セッション START HERE (2026-06-05 handoff 続き)

**worktree セットアップ** (この worktree は `.lake`/`references` symlink が無い場合がある):
```bash
cd <worktree>
mkdir -p .lake && ln -sfn /home/ywr/odd-order/.lake/packages .lake/packages
ln -sfn /home/ywr/odd-order/references references
[ -d .lake/build ] || cp -a /home/ywr/odd-order/.lake/build .lake/build
```
build: `lake build OddOrder.Peterfalvi.S16_NonExistenceG` (leaf) → 完了直前に `lake build OddOrder` (full 3580)。
作業対象 = **`OddOrder/Peterfalvi/S16_NonExistenceG.lean` の `namespace FieldNormalizerData` 末尾の `section Step4`**。

### 🔴🔴 最重要の戦略確定 (このセッション, commit 730eaae): 経路B が唯一の faithful path

旧 plan §1.1 は「**経路A 推奨**」だったが、これは**循環するので不可**と確定:
- c=-1 (`s₁=s⁻¹`) 論証は **base relation で `a∈E` を必須**とする。理由: (C.2) は `b=2-a∈U`
  (= `σ(inr b)` を作るため) を要し、`a∈U ∧ 2-a∈U ⟺ a∈E` (E の定義そのもの)。
- 経路A の hstep は `∀ w∈E` で decomp(`s·σ(inr w)·s⁻²`) の middle が s⁻¹ を要求。この w に対応する
  BG-a は `(w⁻¹)^{t^{-3}}` で、これが E に入ることは **E=E⁻¹ (証明目標) と同値 → 循環**。
- ∴ **経路B** (`normSetETwistedNormOneStep φ`, φ=tConjAut³ 系) を採る。終端 `appCNormSetGeneratorRelation_of_twisted_normOne_step` (S16:173) で `appC_normSet_generator_relation` を field 非経由化できる。

### ✅ 解決済 (commit e1b1991): φ-matching + 経路B 配線を Lean で検証

PDF pp.150-152 精読 + Lean 検証で確定。**残るは `Step4Capstone` の証明 1 点のみ**:
- repo の E-extraction (`unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition`) は
  decomp(`s·σ(inr W)·s⁻²`, middle s⁻¹) ⟹ **`(↑W)⁻¹∈E`** を与える。
- `exists_step4_first_k_three_decomposition(input)` の slot は `(tConjAut³)(input⁻¹)` 固定。
- capstone 入力条件は `↑a⁻¹∈E` (base relation `↑a⁻¹+↑b⁻¹=2` 由来; `unitVal a⁻¹+unitVal b⁻¹=2`)。
- **twisted step は capstone を入力 `a=u⁻¹` で呼ぶ**ことで一致: cond=`↑(u⁻¹)⁻¹=↑u∈E` (手持ち)、
  slot=`(tConjAut³)((u⁻¹)⁻¹)=(tConjAut³)(u)=W`、E-extraction `(↑W)⁻¹=↑((tConjAut³)(u⁻¹))∈E`
  が twisted step `∀u∈E, ↑((tConjAut³)(u⁻¹))∈E` に過不足なく合致。**循環なし**。
- 配線補題 (全 build-green, sorry-free):
  - `Step4Capstone (data) : Prop` = ∀a, ↑a⁻¹∈E → exists_step4_first_k_three(a) の middle が s⁻¹。
  - `normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone` : capstone ⟹ twisted step (現 φ=(tConjAut³)⁻¹)。
  - `appCNormSetTwistedNormOneStep_of_capstone` / `appC_normSet_generator_relation_of_capstone` :
    capstone ⟹ generator relation を **field 非経由**で。
- **capstone 完成後**: `appC_normSet_generator_relation` (S16:1631) を `_of_capstone` 版に差し替え →
  `FieldNormalizerData.appC_twisted_normOne_step` field を削除 (+ producer `field_normalizer_structure`
  からも削除) → full build + AxiomsCheck。**30 分の配線作業**。

### ✅ landed (このセッション, S16 `section Step4`, 全 sorry-free / full build 3580 green / AxiomsCheck OK)
- **scalar 抽象** `sScalar x := σ(inl(ofAdd x))` (BG の `s^x`) + API: `sScalar_mul`/`sScalar_zero`/
  `sScalar_inv`/`s_eq_sScalar_one`/`s_inv_eq_sScalar_neg_one`/`s_sq_eq_sScalar_two`/
  `sigma_primeLineElement_eq_sScalar`/`sScalar_neg_one_eq_sigma_primeLineElement`。
- **`sScalar_conj`**: `σ(inr a)⁻¹·s^x·σ(inr a) = s^{(↑a⁻¹)·x}` (= BG の s^a 共役 = scalar `↑a⁻¹`)。
- `unitVal a := ↑↑a` (norm-one unit の field 値) + `unitVal_inv`/`unitVal_ne_zero`。
- **base relation** `sBGConj_mul_sBGConj`: `(σ(inr a)⁻¹ s σ(inr a))·(σ(inr b)⁻¹ s σ(inr b)) = s²`
  (条件 `unitVal a⁻¹ + unitVal b⁻¹ = 2`)。
- **`relationC2`**: `s⁻²·(σ(inr a)⁻¹ s σ(inr a))·(σ(inr b)⁻¹ s σ(inr b)) = 1`。
- **E-extraction** `unitVal_inv_mem_normSetE_of_sigma_first_k_three_decomposition`:
  decomp(middle s⁻¹) ⟹ `(↑W)⁻¹∈E` (BG final paragraph `v₁=2-W` の repo 版; 既存終端 u₁-route 経由)。
- **companion 構成** `exists_companion_of_unitVal_inv_mem_normSetE` (🆕 2026-06-05 続2):
  `↑a⁻¹∈E ⟹ ∃ b, ↑a⁻¹+↑b⁻¹=2 ∧ ↑b⁻¹∈E` (b=bU⁻¹, bU=`normOneUnitOfMemNormSetE (2-↑a⁻¹∈E)`)。
  `sBGConj_mul_sBGConj`/`relationC2` の仮説 `↑a⁻¹+↑b⁻¹=2` を放電する入口。build-green。
- **🆕🆕 backward restate done** (commit 9be100a): `Step4Capstone` + 配線を forward `tConjAut³` から
  **backward `(tConjNormOneUnitsAut^3)⁻¹`** に切替 (BG-provable 形)。配線名 →
  `normSetETwistedNormOneStep_tConj_pow_three_inv_of_capstone` / `appCNormSetTwistedNormOneStep_of_capstone`
  (φ=(tConjAut³)⁻¹, φ^p=1 は `inv_pow`+pow_p) / `appC_normSet_generator_relation_of_capstone`。
  **capstone M₁ = `s·t⁻³σ(inr a⁻¹)t³·s⁻²` が BG M₁ と完全一致** ⟹ BG (C.4) q-swap 直接移植可。build-green。
- **🆕🆕 backward 入口補題 done** (commit 71fc608): `t_inv_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow_inv`
  (`(t^n)⁻¹σ(inr u)t^n=σ(inr((tConjAut^n)⁻¹ u))`) + `exists_step4_first_k_three_inv_decomposition`
  (M₁ の `∃c u₁v₁`, Step1 経由)。
- **🆕🆕🆕 (C.4) done** (commit be3b427): `connectorC4_one/two/three` (Q-swap: `s⁻³t²s=t⁻¹s⁻²t³` 等,
  `Q_mul_comm`) + **`relationC4`** = `s⁻³t²M₁t⁻¹M₂t⁻¹M₃s³=1` (M_i backward 共役形)。証明 = group で
  `conn1·C2·conn2·C4·conn3·C6` 再結合 → connector rw → group telescope → relationC2。**backward 切替で
  BG telescoping がそのまま通った (forward 障害完全解消)**。build-green。
- **🆕 (2026-06-06) C.5 mod-P right-component bridge done**: `right_component_of_step4_sigma_inr_decomposition`
  (neutral `s^m·σ(inr w)·s^r = σ(inr u₁)·σ(P₀ c)·σ(inr v₁) ⟹ w=u₁v₁`) と
  `right_component_of_step4_first_k_three_inv_decomposition` (backward `k=3` M₁ の `((tConjAut^3)⁻¹ a⁻¹)=u₁v₁`) を追加。
  `lake build OddOrder.Peterfalvi.S16_NonExistenceG` green。
- **🆕 (2026-06-06) FT-critical C.5 normal-form bundle done**: neutral decomposition
  `exists_step4_sigma_inr_decomposition`, named BG factors `step4M1/2/3`, `relationC4_step4M`,
  and `Step4C5NormalForms`/`exists_step4C5NormalForms` landed.  This packages the three C.5
  normal forms plus their mod-`P` right-component readings for the already-proved backward C.4.
  `lake build OddOrder.Peterfalvi.S16_NonExistenceG` green。
- **🆕 (2026-06-06) C.4+C.5 substitution / C.7 seed done**:
  `Step4C5NormalForms.factor1/2/3`, `relationC4_step4C5NormalForms`, and `relationC7_seed`
  landed.  This proves the post-substitution relation
  `t²·(u₁s₁v₁)·t⁻¹·(u₂s₂v₂)·t⁻¹·(u₃s₃v₃)=1`.
  `lake build OddOrder.Peterfalvi.S16_NonExistenceG` green。
- **🆕 (2026-06-06) exact C.7 done**:
  BG words `Step4C5NormalForms.w1/2/3`, ambient rewrites `sigma_inr_w1/2/3`,
  U-membership `sigma_inr_w_mem_U`, and exact rearrangement `relationC7` landed.
  This proves `t⁻¹s₂t⁻¹=(w₁s₃w₂t²s₁w₃)⁻¹` in the transported `G` notation.
  `lake build OddOrder.Peterfalvi.S16_NonExistenceG` green.  次は (C.8) Frobenius
  replacement で (C.5)/(C.7) を p-th powers に移し、(C.9) → Step3 → `wᵢ=1` → (C.10)。
- 経路B 配線 (元 commit e1b1991, 現在は backward に restate 済): 上記 + `Step4Capstone` (def)。
- 先行 landed (前セッション): (X)/(XI) infra (`w2ConjQAut`/FPF/`exists_yD_..` 等) + `sigma_inr_inv_mul_s_mul_sigma_inr`。

### 次の 1 手 (最優先): `Step4Capstone` を証明する ((C.3)→(C.10) → kernel → s₁=s⁻¹)
**全 infra 完備**。capstone を埋めれば即 field 削除可能 (配線済)。PDF pp.150-152 が正確な式 (mmd は (C.3) が garble)。

> 🆕🆕 **2026-06-05 続2 の進捗**: (a) **companion 構成 done** (`exists_companion_of_unitVal_inv_mem_normSetE`,
> build-green) — `↑a⁻¹∈E ⟹ ∃b, ↑a⁻¹+↑b⁻¹=2 ∧ ↑b⁻¹∈E`、`relationC2` の入口。
> (b) **🔴 (C.4) forward-conj 障害を発見 → 🆕 backward 切替で解決**: forward では BG q-swap 不能
> (Q 元が U 元に刺さる)。**capstone/配線を backward `(tConjAut³)⁻¹` に restate** (commit 9be100a) ⟹
> capstone M₁ が BG M₁ と完全一致。
> (c) **🆕🆕🆕 (C.4) `relationC4` 証明完了 (commit be3b427, build-green)**: connector q-swap 3 本
> (`connectorC4_one/two/three`, `Q_mul_comm`) + telescope + relationC2 で `s⁻³t²M₁t⁻¹M₂t⁻¹M₃s³=1`。
> backward 化で BG telescoping がそのまま通った。+ 入口補題 (backward conj + M₁ decomposition) も landed。
> **次セッション = (C.5)-(C.10) + kernel** (下記 step 2-7; (C.4) より mechanical だが kernel が最難)。
> 💡 **推奨: M₁/M₂/M₃ を `def` 化** (大きな式の反復を避け (C.5)以降を簡潔に)。

> 💡 **k=3 に固定して導出してよい** (推奨): BG は (C.2)-(C.10) を一般 k∈F_p で進め s₁=s⁻¹ を出すが、
> 論証は **各 k で独立** (異なる k を混ぜない) で、最終利用は k=3 のみ。`Step4Capstone` 自体が slot
> `(tConjAut³)(a⁻¹)` で k=3。∴ ℓ=k-2=1 で固定すると冪が具体的自然数 (M₁=`s¹(a⁻¹)^{t³}s⁻²`,
> M₂=`s³(ab⁻¹)^{t²}s⁻¹`, M₃=`s²b^t s⁻³`; 共役は t³/t²/t¹) になり、**既存 ℕ-共役補題
> `t_pow_conj_sigma_inr_eq_sigma_inr_tConjNormOneUnitsAut_pow` (S16:1038, left-conj 規約) が直接使える**
> (BG は right-conj `(u)^{t^j}=t^{-j}u t^j`、repo は left-conj `t^j σ(inr u) t^{-j}=σ(inr(tConjAut^j u))`;
> repo の `data.t = y·s·y⁻¹` で BG の y と逆規約 — 規約変換は最初に 1 回だけ吸収する)。
> zpow/一般 k を避けられるので大幅に楽。
1. **(C.3)→(C.4)** [最 convention-heavy。🆕🆕 2026-06-05 続2: forward-conj で repo 冪を確定]:
   `relationC2` から (C.4)。**⚠️ BG の `s⁻³t²M₁t⁻¹M₂t⁻¹M₃s³` はそのまま移植不可**。理由 = repo
   engine の共役は **forward** (`σ(inr(tConjAut³ a⁻¹)) = t³σ(inr a⁻¹)t⁻³`、`normOneUnitsEquivU_..._apply_coe`
   S16:990) で BG の backward `(a⁻¹)^{t³}=t⁻³At³` と逆。素朴な `t→t⁻¹` 置換も**不可** (BG は
   `qⱼ=s⁻ʲtʲ∈Q` を使うが置換後 `s⁻ʲt⁻ʲ∉Q` — G/Q で `s̄=t̄` (∵`s⁻¹t∈Q`) ゆえ `s⁻ʲt⁻ʲ≡s̄⁻²ʲ≠1`)。
   - **✅ repo (C.4) の正しい冪を確定 (mod-Q で検算済; G-level Q-juggling は未実装)**:
     - **M_i (forward, k=3)** = engine `exists_step4_decomposition_of_zpow_tConjNormOneUnitsAut_pow` 出力:
       M₁=`s¹·σ(inr(tConjAut³ a⁻¹))·s⁻²` (= `exists_step4_first_k_three_decomposition` の LHS),
       M₂=`s³·σ(inr(tConjAut² (a·b⁻¹)))·s⁻¹`, M₃=`s²·σ(inr(tConjAut¹ b))·s⁻³`。
       (s 冪 (1,-2)/(3,-1)/(2,-3) は **BG と同一**; 共役 tConjAut^{3/2/1} の向きだけ forward。
       単位対応: relationC2 = `s⁻²·σ(inr a)⁻¹·s·σ(inr(a·b⁻¹))·s·σ(inr b)` の 3 共役単位 = `a⁻¹`,`a·b⁻¹`,`b`。)
     - **stripped (C.4)** = `t⁻²·M₁·t·M₂·t·M₃ = 1` (connector 冪 **(-2,+1,+1)**; BG は (+2,-1,-1) で**符号反転**)。
       これが (C.7) に渡る形。**full (C.4)** = `s⁻⁴·t⁻²·M₁·t·M₂·t·M₃·s⁴ = 1` (α=-4,β=-2,γ=δ=+1,ε=4;
       stripped から `s⁴(·)s⁻⁴`)。
   - **🔴🔴 重要訂正: forward は BG の局所 q-swap が機能しない (当初「同等」判断は誤り)**:
     φ-push (`t^β M₁ t^γ M₂ t^δ M₃ = φ^β(M₁)φ^{β+γ}(M₂)φ^{β+γ+δ}(M₃)·t^{β+γ+δ}`, φ(x)=txt⁻¹) で
     **β+γ+δ=0** (=-2+1+1) + **γ=δ=+1 で U-元 (A,D,E) が一様 φ¹** までは BG と同形。だが残る
     **s-共役 `φ^j(s)` (j=-2,-1,0) の非一様性**を消す段で差が出る:
     - BG (backward C_i=`t⁻ᵏAtᵏ`): connector+M₁s+C₁の t = `s⁻³t²s·t⁻³` で **t が局所相殺** → `t⁻¹s⁻²`
       (clean s-冪)。各 connector が単一 q-swap で綺麗に畳める (full=`t⁻¹·relationC2·t`)。
     - repo (forward C_i=`tᵏAt⁻ᵏ`): connector+M₁s+C₁の t = `t⁻²s·t³` = `r₂q₁t²` (r₂=t⁻²s²,q₁=s⁻¹t∈Q)
       — **Q 元 r₂q₁ が残り、leftover t² が U-元 A に刺さる** (`r₂q₁t²·A = r₂q₁·φ²(A)·t²`, Q と U は
       非可換で消えない)。**局所では畳めない**。
   - **∴ G-level の真偽は未確定** (mod-Q skeleton `s̄²Ās̄D̄s̄Ēs̄⁻⁴` = `s̄²(Ās̄D̄s̄Ē=s̄²)s̄⁻⁴`=1 は OK だが、
     Q-part が大域的に消えるかは未検証)。さらに **forward = BG-argument を τ=t⁻¹ で回す版に対応しない**
     (BG q_j=`s⁻ʲτʲ` を要求するが τ=t⁻¹ では `s⁻ʲt⁻ʲ∉Q`; τ=t⁻¹ は s の y-共役でなく s⁻¹ の共役)。
     つまり **BG の証明そのものは forward M₁ に直接適用できない**。
   - **🚩🚩 推奨解 = (b) capstone/配線を backward `tConjAut⁻³` に切替** (このセッションで feasibility 確認済):
     - **根拠**: BG の結論は `(a⁻¹)^{t³}_{BG-bwd} ∈ E`。repo (forward tConjAut) では
       `(a⁻¹)^{t³}_{bwd} = t⁻³σ(inr a⁻¹)t³ = σ(inr((tConjAut⁻³)(a⁻¹)))` = **backward = `tConjAut⁻³`**。
       現行配線は `tConjAut³` (forward) を使うが、**BG が自然に与えるのは `tConjAut⁻³`**。逆向きを使うと
       capstone M₁ = `s·σ(inr(tConjAut⁻³ a⁻¹))·s⁻² = s·t⁻³A t³·s⁻²` が **BG の M₁ `s(a⁻¹)^{t³}s⁻²` と完全一致**
       ⟹ BG の (C.4) q-swap (q_j=s⁻ʲtʲ∈Q, repo に既存) が**そのまま移植可能** (forward 障害が消える)。
     - **✅ 検証済 (3 点)**: ① downstream `normSetE_eq_inv_of_twisted_normOne_step` (AppC_NormSet:1120) は
       **任意の φ (φ^p=1) で動作** (`(tConjAut⁻³)^p=(tConjAut^p)⁻³=1` OK)。② φ-matching は backward でも成立
       (capstone を a=u⁻¹ で呼び、E-extraction `(↑W)⁻¹∈E` (W=tConjAut⁻³ u) = `↑(tConjAut⁻³ u⁻¹)∈E` =
       twisted step に過不足なく合致)。③ backward repo M₁ = BG M₁ なので q-swap が同一 q_j で telescope。
     - **作業**: ✅ (iii) `Step4Capstone`/配線の `(tConjAut³)⁻¹` restate は **done** (commit 9be100a, build-green)。
       残り: (i) backward conj lemma `(t^n)⁻¹σ(inr u)t^n=σ(inr((tConjAut^n)⁻¹ u))` (forward S16:1038 を逆に;
       `← map_inv` 系で ~5 行)、(ii) **backward decomposition** = capstone の `∃c u₁v₁` を与える lemma
       (`s·σ(inr((tConjAut³)⁻¹ a⁻¹))·s⁻² ∈ P⊔U` を Step1 `exists_sigma_normOne_primeLine_normOne_of_mem_PU`
       に通す; forward `exists_step4_first_k_three_decomposition` (S16:1179) の逆向き版、(i) を使い ~15 行)、
       (iv) BG (C.4) q-swap を写経 (下の「🔁 BG (C.4) q-swap」が backward で**そのまま有効**) → c=-1。
   - 代替: (a) forward を大域 Q-argument で押す (真偽リスク有、非推奨) / (c) module/End 抽象で一括 (大工事)。
   - **🔁 BG (C.4) q-swap (backward なら有効・写経対象)**: M₁=`s(a⁻¹)^{t³}s⁻²` (=backward capstone LHS),
     M₂=`s³(ab⁻¹)^{t²}s⁻¹`, M₃=`s²b^t s⁻³`。(C.4)=`s⁻³t²M₁t⁻¹M₂t⁻¹M₃s³=1`。各 connector が単一 Q-swap
     `qᵢ⁻¹qⱼ=qⱼqᵢ⁻¹` (qᵢ=s⁻ⁱtⁱ∈Q): conn1 `s⁻³t²s=q₃q₁⁻¹=q₁⁻¹q₃=t⁻¹s⁻²t³`, conn2 `s⁻²t⁻¹s³=q₂q₃⁻¹=t⁻³st²`,
     conn3 `s⁻¹t⁻¹s²=q₁q₂⁻¹=t⁻²st`。swap 後 telescope で `t⁻¹·(C.2-LHS)·t=t⁻¹·1·t=1`。
   - **Q-membership/comm は既存**: `s_inv_pow_mul_t_pow_mem_Q`/`t_inv_pow_mul_s_pow_mem_Q`/`Q_mul_comm`。
2. **(C.5)-(C.6)**: Step1 で uᵢsᵢvᵢ、Step2/3 で sᵢ≠1。
3. **(C.7)**: ✅ landed (`Step4C5NormalForms.w1/2/3`, `sigma_inr_w_mem_U`, `relationC7`):
   `s^k·(C.4)·s^{-k}` + (C.5) 代入 → `t⁻¹s₂t⁻¹=(w₁s₃w₂t²s₁w₃)⁻¹`、wᵢ∈U (PDF p.150-151)。
4. **(C.8)-(C.9) Frobenius**: (C.5) は a,b,uᵢ,vᵢ→aᵖ,bᵖ,uᵢᵖ,vᵢᵖ で不変 (s₁=`(s^{k-2})^{u₁}(s^{-k+1})^{v₁⁻¹}`,
   F で `s₁=(k-2)su₁+(-k+1)s/v₁`、p乗 Frobenius)。⟹ (C.9) `s₁w₃^{p-1}s₁⁻¹∈(PU)∩(PU)^{t²}`。
5. **w_i=1**: Step3 ⟹ s₁w₃^{p-1}s₁⁻¹∈U、Step2 (s₁≠1) ⟹ w₃^{p-1}=1 ⟹ (A) で w₃=1。同様 w₁=w₂=1。
   ⟹ (C.10) `t²s₁t⁻¹s₂t⁻¹s₃=1`。mod Q (`W2_inf_Q_eq_bot` S16:1454) ⟹ s₁s₂s₃=1。
6. **kernel/End** (PDF p.151-152): (C.10) を `t=y⁻¹sy` で展開 + `P₀` を `End([Q,P₀])` 像と同一視 →
   `y∈ker((s⁻¹+1-s₁⁻¹s⁻¹-s₃)(s⁻¹-1))`。**FPF** (`w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed`,
   s で固定⟹W₂で固定⟹∈C_Q(W₂)⊓⁅Q,W₂⁆=1, (X)) で `(s⁻¹-1)` 可逆 → `y∈ker(s⁻¹+1-s₁⁻¹s⁻¹-s₃)`。
   **(XI)** で `y∈⁅Q,W₂⁆` (`exists_yD_mem_actionCommutator_conj_s_eq_t`)。
7. **s₁=s⁻¹**: tᵢ=y⁻¹sᵢy ⟹ `s₁t₁⁻¹t⁻¹=t⁻¹t₃⁻¹s₃` ⟹ (t₁≠t⁻¹ なら Step3+Step2 で s₁=1 矛盾) ⟹ t₁=t⁻¹ ∧ **s₁=s⁻¹**。
   ⟹ k=3 第1式の middle が s⁻¹ = `Step4Capstone`。
⚠️ kernel 段 (6) は `End([Q,P₀])` を ℤ-module 作用として実装する必要 (P₀=⟨s⟩ の作用、`actionCommutator` 上)。最難。

---

## 0. 現状サマリ (2026-06-05 監査)

App.C の有限体核は **全完成** (sorry-free・axiom-clean, build 3487 green):
- **C.1** `NormSet.lemmaC1` (多項式根数 → p≤q)
- **C.2** `NormSet.lemmaC2` (|E|≥2; q=3 / q≥5 Frobenius 指標論とも `AppC_FrobeniusClassSum.lean` で完了)
- **C.3 tail** `normSetE_eq_inv_of_twisted_normOne_step` (Step 4 出力 → E=E⁻¹ の奇数反復)
- **Theorem C** `AppC.theoremC` / `AppC.final_contradiction` 組み上げ済 (`FieldNormalizerData` modulo)

S16 の sorry は**すべて Peterfalvi (14.x) 指標論チェーン** (`caseB_for_T`, `betaM_expansion`,
`field_normalizer_structure` 等) = main BG/Pf work。**Step 4 はこれらと非交差** (carrier を仮説に
使うだけで指標論に触れない)。唯一の例外的依存 = (X)/(XI) の coprime-action データ (§4 で詳述、
指標論でなく Fitting 分解)。

---

## 1. ターゲットと終端の配線 (既存・証明済)

最終的に埋めるのは `S16.FieldNormalizerData` の field:

```
appC_twisted_normOne_step : appCNormSetTwistedNormOneStep hyp
  -- = ∃ φ : MulAut (normOneUnits p q), φ^p = 1 ∧ normSetETwistedNormOneStep p q φ
```

これを field でなく **derived theorem** にする。終端から逆算した既存チェーン (全部証明済):

| repo lemma (S16 / NormSet) | 役割 |
|---|---|
| `NormSet.normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition` (NormSet:773) | H=P⋊U の関係 `inl(1)·inr(w)·inl(-2) = inr(u₁)·inl(-1)·inr(v₁)` → `N(2·w_value−1)=1` 【代数核】 |
| `FieldNormalizerData.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition` (S16:1228) | 上を G 側 `s·σ(inr w)·s⁻²` 関係 (中央因子 `-1`) から `N(2·w−1)=1` へ bridge |
| `appC_normSet_generator_relation_of_first_k_three_coordinate` (S16:1324) | **hstep** (∀w∈E, 中央 `-1` の k=3 分解) → `appCNormSetGeneratorRelation hyp` (∀a∈E, N(2a−1)=1) |
| `appC_twisted_normOne_step_of_tConjNormOneUnitsAut` (S16:1370) | `normSetETwistedNormOneStep tConjNormOneUnitsAut` → field 充足 |
| `exists_step4_first_k_three_decomposition` (S16:1179) | ∀u, `s·σ(inr (tConjAut³ u⁻¹))·s⁻²` に **ある** c の正規形 `σ(inr u₁)·σ(P₀ c)·σ(inr v₁)` |
| `right_component_of_step4_first_k_three_decomposition` (S16:1198) | 分解から `(tConjAut³)u⁻¹ = u₁·v₁` (mod P) |

⟹ **既存機構は「ある c の分解」までを与える。残ギャップ = その `c = −1`**。

### 1.1 二つの配線経路 (✅ 2026-06-05 確定: **経路B**。経路A は循環で不可 — START HERE 参照)

> **訂正 (commit 730eaae)**: 下記の「推奨=経路A」は **撤回**。経路A の hstep `∀w∈E` は循環する
> (c=-1 論証が `a∈E` 必須 ⟹ 経路A の w に対する BG-a=`(w⁻¹)^{t^{-3}}` が E に入る必要 = E=E⁻¹ と同値)。
> **経路B が唯一の faithful path**。以下は経緯として残す。

- **経路A (first-k-three / generator-relation)**: `appC_normSet_generator_relation_of_first_k_three_coordinate`
  の hstep を証明。hstep = 「∀w∈E (unit), `s·σ(inr w)·s⁻²` が中央 `-1` の分解を持つ」。
  これで `appCNormSetGeneratorRelation` が **field 非経由**で出る ⟹ `lemmaC3_inverse_closed` /
  `theoremC` を `appC_normSet_generator_relation` accessor 経由でなく直接これに繋ぎ替え、field 削除。
- **経路B (twisted-step)**: `normSetETwistedNormOneStep φ` を φ で証明し field を `⟨φ, _, _⟩` で充足。
  BG 本文の one-step は **φ = conj-by-`t³`** (a∈E ⟹ (a⁻¹)^{t³}∈E)。よって既存
  `appC_twisted_normOne_step_of_tConjNormOneUnitsAut` (φ=単一 t) は**そのままでは BG と不一致** —
  φ = `tConjNormOneUnitsAut^3` 版の reduction を別途書くか、field を直接 `⟨tConjAut³, pow, step⟩` で埋める
  ((tConjAut³)^p = (tConjAut^p)³ = 1)。

**🔴 実装時の確定事項 (sign/inversion/t-vs-t³ reconciliation)**: BG は w=`(a⁻¹)^{t³}` について
中央 `-1` を出し `N(2−(a⁻¹)^{t³})=1` ⟹ `(a⁻¹)^{t³}∈E` と結論。一方 repo の終端代数核は
`N(2·w−1)=1`。`N(2w−1) = N(w)·N(2−w⁻¹) = N(2−w⁻¹)` (w∈U) なので **terminal は `w⁻¹∈E` を与える**
形 — BG の `w∈E` と inversion 1 つずれる。**経路A の hstep が w-全称で BG の per-a 導出と量化が
合うか**、**経路B の φ=t³ と terminal の inversion が整合するか**を、実装の最初に Lean 型検査で
固定する (机上では sign を詰め切らない方針)。**推奨 = 経路A** (field を消せて最もクリーン;
hstep は w∈E 全称だが、§3 の核 `s₁=s⁻¹` は w に依らず carrier の generator-relation から従う見込み)。

---

## 2. BG Step 4 の論証構造 (mmd L4994–5095)

設定: `s ∈ P₀^#` (= `data.s = σ(inl(ofAdd 1))`), `t = s^y` (= `data.t`), `P₁ = P₀^y` (= `data.P1`)。
`a ∈ E^#`, `b ∈ E` with `a+b=2`。記法 `s^a := inl(a)` (= 場のスカラー a に対応する P 元 = `σ(inl(ofAdd a))`;
**群共役でなく F-加法群 P=F⁺ のスカラー元**)。`s^a s^b = s^{a+b} = s² ` (加法)。

| BG eq | 内容 | repo 既存 API / 新規 |
|---|---|---|
| **base** | `a+b=2` ⟹ `s^a·s^b = s²` (P 内加法) | 新規 (自明, `map_mul`+`ofAdd_add`) |
| **(C.2)** | `s⁻² a⁻¹ s a b⁻¹ s b = 1` (a,b は U の unit; `a⁻¹ s a` 等は共役) | 新規 (base の共役書き換え) |
| **(C.3)** | `t^{-ℓ}` 左 `t^{ℓ}` 右倍 (ℓ=k−2, k∈F_p) | 新規 |
| **(C.4)** | `s⁻ⁱtⁱ = [sⁱ,y] ∈ Q`, Q 可換 ⟹ 整理 | **既存** `s_inv_pow_mul_t_pow_mem_Q` (S16:1416) + `Q_mul_comm` (S16:1424) + `s_inv_pow_mul_t_pow_mul_comm` 系 |
| **(C.5)** | Step1 正規形 `uᵢsᵢvᵢ` (i=1,2,3) | **既存** `exists_sigma_normOne_primeLine_normOne_of_mem_PU` (S16:617) |
| **(C.6)** | `sᵢ≠1` | **既存** Step2 `generatorRelation_step2_primeLine*` (S16:643/672) + Step3 (下記) |
| **(C.7)** | `t⁻¹s₂t⁻¹ = (w₁s₃w₂t²s₁w₃)⁻¹` (wᵢ∈U) | ✅ landed: `Step4C5NormalForms.w1/2/3`, `sigma_inr_w_mem_U`, `relationC7` |
| **(C.8)** | a→aᵖ 置換不変 (Frobenius `aᵖ+bᵖ=2`) | 新規 (有限体 Frobenius; `add_pow_char` 系) |
| **(C.9)** | `s₁w₃^{p-1}s₁⁻¹ ∈ (PU)∩(PU)^{t²}` | 新規 |
| Step3 適用 | `w₃^{p-1}=1` ⟹ (A) で `w₃=1`, 同様に `w₁=w₂=1` | **既存** Step3 `P_sup_U_inf_conj_t_pow_eq_U_or_eq_P_sup_U` (S16:937) + Step2 |
| **(C.10)** | `t²s₁t⁻¹s₂t⁻¹s₃=1` | 新規 |
| mod Q | `P₀∩Q=1` ⟹ `s₁s₂s₃=1` | **既存** `W2_inf_Q_eq_bot` (S16:1454) |
| **kernel** | End([Q,P₀]) で `y ∈ ker((s⁻¹+1−s₁⁻¹s⁻¹−s₃)(s⁻¹−1))` | **新規 + (X)/(XI) 要** (§4) |
| FPF | s⁻¹ が [Q,P₀] 上 fixed-point-free ⟹ `(s⁻¹−1)` 可逆 ⟹ `y∈ker(s⁻¹+1−s₁⁻¹s⁻¹−s₃)` | **新規 + (X)/(XI) 要** |
| 仕上げ | `t_i = y⁻¹sᵢy` 設定 ⟹ `s₁t₁⁻¹t⁻¹ = t⁻¹t₃⁻¹s₃` ⟹ (t₁≠t⁻¹ なら Step3+Step2 で矛盾) ⟹ **t₁=t⁻¹ ∧ s₁=s⁻¹** | 新規 (既存 Step2/Step3 を使用) |

### 2.1 Step 4 後段 (s₁=s⁻¹ → one-step、mmd L5090–5095) — 既存寄り
k=3 第1式 + `s₁=s⁻¹`: `s·(a⁻¹)^{t³}·s⁻² = u₁s⁻¹v₁` ⟹ `v₁ = 2−(a⁻¹)^{t³}` ⟹
`N(2−(a⁻¹)^{t³})=1` ⟹ `(a⁻¹)^{t³}∈E` (one-step)。奇数反復 (n=p, (-1)^p=-1) で `a⁻¹∈E`。
**この後段は terminal 代数核 + tail (`inv_mem_of_twistedInv_step`) が既存**。`s₁=s⁻¹` さえ出れば
`normN_two_mul_sub_one_of_sigma_first_k_three_decomposition` (中央=-1 版) が直接適用できる。

---

## 3. Lean 補題分解 (新規) — 実装順

`OddOrder/Peterfalvi/S16_NonExistenceG.lean` の `FieldNormalizerData` namespace に追加 (Step1-3 と同居)。
※ファイルが肥大なら `S16_AppCStep4.lean` leaf へ切り出し → hub import も検討 (CLAUDE.md ファイル粒度)。

1. **base/(C.2)/(C.3) 入口** (容易):
   - `sScalar_mul_sScalar` : `a+b=2 → σ(inl a)·σ(inl b) = s²`。
   - `relationC2` : `s⁻² · σ(inr a⁻¹)·s·σ(inr a) · σ(inr b⁻¹)·s·σ(inr b) = 1` 形 (a,b∈U, a+b=2)。
     ※ `s^a`(共役 a⁻¹sa)と `s^a`(スカラー)の BG 記法を Lean で曖昧さなく固定すること (🔴 最重要)。
   - `relationC3` : (C.2) を `t^{±ℓ}` 共役した形。
2. **(C.4)–(C.6)** (既存 Q-commutator + Step1/2/3 を chain):
   - `relationC4` (Q 可換で整理), `decompositionC5` (Step1 で uᵢsᵢvᵢ), `sᵢ_ne_one` (Step2/3)。
3. **(C.7)–(C.10)** (Frobenius 置換 + Step3):
   - ✅ `relationC7` landed.  次は `frobenius_replacement_C8` : (C.5) が a→aᵖ で不変 (有限体 `add_pow_char`)。
   - `w_eq_one` : `w₁=w₂=w₃=1` (Step3 `..._inf_conj_t_pow_..` + Step2 + 条件A `w₃^{p-1}=1→w₃=1`)。
   - `relationC10` : `t²s₁t⁻¹s₂t⁻¹s₃=1`, `s₁s₂s₃_eq_one` (mod Q, `W2_inf_Q_eq_bot`)。
4. **kernel/FPF** (🔴 (X)/(XI) 依存, §4):
   - `y_mem_ker_of_relationC10` : `y∈ker((s⁻¹+1−s₁⁻¹s⁻¹−s₃)(s⁻¹−1))`。
   - `sInv_fixedPointFree_on_QP0` : s⁻¹ が [Q,P₀] 上 FPF。
   - `y_mem_ker_linear` : `y∈ker(s⁻¹+1−s₁⁻¹s⁻¹−s₃)`。
5. **s₁=s⁻¹** (capstone):
   - `s1_eq_sInv` : 上 + Step2/Step3 で `t₁=t⁻¹ ∧ s₁=s⁻¹`。
6. **配線** (経路A):
   - `step4_first_k_three_middle_neg_one` : ∀w∈E, `s·σ(inr w)·s⁻²` が中央 `-1` の分解 (= hstep)。
   - `appC_normSet_generator_relation` を field 非経由で `..._of_first_k_three_coordinate` から導出。
   - `FieldNormalizerData` から `appC_twisted_normOne_step` field **削除** (producer の義務が減る)。

---

## 4. (X)/(XI) coprime-action infra (新規・要 mathlib feasibility 確認)

BG Remark (X): `Q = C_Q(P₀) ⊕ [Q,P₀]` (P₀ は p-group, Q は abelian p′-group ⟹ coprime 作用)。
`C_Q(P₀) ∩ [Q,P₀] = 1`。Remark (XI): **y ∈ [Q,P₀] と仮定してよい**。

kernel 論法が要求する具体:
- `commQP0 := ⁅Q, W2⁆` 相当 (W2 = σ(P₀))、または P₀ 作用での `[Q,P₀]` submodule。
- `C_Q(P₀) ∩ [Q,P₀] = 1` (coprime ⟹ direct decomposition)。
- **s⁻¹ (= P₀ 生成元の作用) が [Q,P₀] 上 fixed-point-free** : `x∈[Q,P₀], x^{s⁻¹}=x ⟹ x∈C_Q(P₀)∩[Q,P₀]=1`。
- **y ∈ [Q,P₀]** : carrier に field 追加 **or** (XI) を「y をその [Q,P₀]-成分で置換してよい」補題で導出。

**carrier への影響 (overlap 評価)**: `y ∈ [Q,P₀]` と分解を `FieldNormalizerData` に field 追加すると
producer (`field_normalizer_structure` 等, §14) がそれを供給する義務を負う。ただしこれは**指標論でなく
coprime 作用の標準事実**ゆえ:
- 案(i): field 追加 (producer 側で coprime-action 一般補題から供給) — 最小 interface 変更。
- 案(ii): 既存 `Q_elementaryAbelian` (= Q は q-elementary abelian) + `W2_normalizes_Q` +
  `W2_pow_p_eq_one` から **derived theorem** として分解・FPF・(XI) 置換を出す — field 追加ゼロ、完全非交差。
  **推奨 = 案(ii)** が可能か mathlib coprime-action API で feasibility 確認 (下記)。

**✅ feasibility 確定 (2026-06-05): (X) 分解は既存 repo API で実現可能**:
- **`fixedPoints_isComplement_actionCommutator_of_abelian`** (`OddOrder/BG/Ch1_Preliminary/S01_Solvable.lean:1515`,
  = **Isaacs Thm 4.34 (Fitting) / BG Prop 1.6(d)**):
  ```
  {G A}[CommGroup G][Finite G][IsSolvable G][Group A][Finite A]{φ : A →* MulAut G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card G)) :
    Subgroup.IsComplement' (Subgroup.fixedPointsOfMulAut φ) (OddOrder.Isaacs.Ch04.actionCommutator φ)
  ```
  ⟹ `G = C_G(A) × [G,A]`。**これが (X) そのもの**。`G := Q` (elementary abelian q-group ⟹ CommGroup/Finite/IsSolvable),
  `A := P₀` (cyclic order p), `φ :=` P₀ の Q への共役作用, `hCop := Coprime p |Q|` (p≠q)。
  - `actionCommutator φ` (`OddOrder/Isaacs/Ch04_Commutators/Main.lean:2006`) = `[Q,P₀]`。
  - `Subgroup.fixedPointsOfMulAut φ` = `C_Q(P₀)`。
  - `IsComplement'` から `C_Q(P₀) ⊓ [Q,P₀] = ⊥` (disjoint) と `⊔ = ⊤`。
- **FPF は (X) から直接**: `x∈[Q,P₀]`, `φ(s)·x = x` ⟹ `x∈fixedPointsOfMulAut φ = C_Q(P₀)` ⟹
  `x∈C_Q(P₀)⊓[Q,P₀]=⊥` ⟹ `x=1`。(s が P₀ を生成するので「s で固定」⟹「P₀ で固定」)。
- **(XI) `y∈[Q,P₀]`**: 分解 `y = y_C · y_[Q,P₀]` (y_C∈C_Q(P₀))。BG「y∈[Q,P₀] と仮定してよい」は
  y_C が P₀ と可換ゆえ関係式から落ちることに対応。**実装案**: carrier に field 追加せず、`t=s^y` を
  `s^{y_[Q,P₀]}` で置換しても (C.2)-(C.10) が不変であることを示す reduction、または最小限 `y∈[Q,P₀]` を
  carrier field 追加 (producer は 4.34 分解で供給)。**まず reduction を試行、無理なら field 追加**。
- **✅ LANDED (2026-06-05, commits 9fae5e2 / 6bea62c)**: (X) 分解 core を `FieldNormalizerData` に実装済:
  - `W2_card_coprime_Q_card` : `Coprime |W2| |Q|` (|W2|=p, |Q|=q^k via `card_eq_pow_finrank`, p≠q)。
  - `w2ConjQAut : ↥W2 →* MulAut ↥Q` = mathlib `Subgroup.normalizerMonoidHom (H:=Q)` ∘
    `Subgroup.inclusion W2_normalizes_Q` (BG Ch2 S07 conjAction 不要・新規 import 無)。
  - `w2ConjQAut_fixedPoints_inf_actionCommutator_eq_bot` : **`C_Q(W2) ⊓ ⁅Q,W2⁆ = ⊥`**
    (`Ch04.fixedPoints_inf_actionCommutator_eq_bot_of_abelian` + 上記 coprimality;
    CommGroup ↥Q は `{ (inferInstance:Group ↥Q) with mul_comm := Q_elementaryAbelian.comm }` で diamond 回避)。
  - `w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed` : **FPF** — `x∈⁅Q,W2⁆` かつ W2-固定 ⟹ x=1。
- **✅ (XI) bridge LANDED (2026-06-05, commit 5b1288b)**:
  - `w2ConjQAut_apply_coe` : `(w2ConjQAut w x : G) = w·x·w⁻¹` (rfl)。
  - `exists_yD_mem_actionCommutator_conj_s_eq_t` : **BG Remark (XI)** —
    `∃ yD ∈ ⁅Q,W2⁆, MulAut.conj yD s = t`。Q = ⁅Q,W2⁆·C_Q(W2) (`fixedPoints_sup_actionCommutator_eq_top`)
    で y=yD·yC、yC∈C_Q(W2) が s と可換 ⟹ t = y·s·y⁻¹ = yD·s·yD⁻¹。kernel 段は yD (∈[Q,W2]) を使える。
- 🔴 残り (Step 4 の残作業、(X)/(XI) infra は完了):
  1. **(C.2)–(C.10) 群関係鎖** (convention-heavy, 既存 API chain): `s^a s^b=s²` → … → `s₁s₂s₃=1` /
     `t²s₁t⁻¹s₂t⁻¹s₃=1`。§3 補題分解参照。`s^a` 二義性 (§6) を最初に固定。
  2. **kernel→End 翻訳**: (C.10) から得る `y∈ker((s⁻¹+1−s₁⁻¹s⁻¹−s₃)(s⁻¹−1))` を ⁅Q,W2⁆ 上の
     ℤ-module 作用に落とし、FPF (`w2ConjQAut_eq_one_of_mem_actionCommutator_of_fixed`; s-only 形は
     W2=⟨s⟩ で s-固定⟹W2-固定 を経由) で `(s⁻¹−1)` 可逆化 → `y∈ker(s⁻¹+1−s₁⁻¹s⁻¹−s₃)`。
  3. **`s₁=s⁻¹` capstone** + 配線 (経路A: `appC_normSet_generator_relation_of_first_k_three_coordinate`)。
  ⟹ infra (X)/(XI) は全て landed。残りは群関係鎖 (1) → End 計算 (2) → capstone (3)。

---

## 5. 規模・段取り

- **規模**: BG ~100 行 → Lean 推定 600–1000 行。**multi-session** 確実。
- **リスク順**: §4 (X)/(XI) coprime infra (最高, mathlib 依存) > §3 kernel 段 > (C.7)-(C.10) Frobenius >
  入口 (C.2)-(C.6) (既存 API chain, 最低)。
- **推奨着手順**: (a) §4 feasibility (案(ii) 可否) → (b) 入口 (C.2)-(C.6) (既存 chain で確実に進む) →
  (c) (C.7)-(C.10) → (d) kernel/FPF → (e) `s₁=s⁻¹` capstone → (f) 配線 + field 削除。
- 各段 build-green を維持。`s₁=s⁻¹` まで `sorry` を 1 個置いて配線を先に通す案も可 (granular obligation 化)。

---

## 6. 🔴 実装で最初に固定すべき曖昧点

1. **`s^a` の二義性 — ✅ 確定済 (2026-06-05, commit e5ba700)**: `sigma_inr_inv_mul_s_mul_sigma_inr` で
   **右共役 `σ(inr a)⁻¹ · s · σ(inr a) = σ(inl(ofAdd((a:F)⁻¹·1)))`** と確定 (= scalar `a⁻¹`)。
   🔴 **重要 sign 注意**: repo convention では右共役 by σ(inr a) は scalar **a⁻¹** (a でない;
   `normOneFrobenius_conj_inl : inr(u)·inl(s)·inr(u)⁻¹ = inl(u·s)` の向きゆえ)。よって BG の base
   `a+b=2 ⟹ s^a s^b=s²` を素直に取ると `s^a=σ(inl a⁻¹)` で `a⁻¹+b⁻¹=2` を要し a+b=2 と非整合。
   **解決方針**: BG の exponent ラベル a は終端補題
   `normOneFrobenius_normN_two_mul_sub_one_of_first_k_three_decomposition` の encoding
   (中央 `inl(-1)`, w の coe) に合わせて downstream で a↔a⁻¹ を吸収する。(C.2) を組むときは
   この bridge をスカラー側で使い、BG の a を「σ(inr a⁻¹) で共役した scalar a」と読むのが安全
   (= `σ(inr a⁻¹)⁻¹·s·σ(inr a⁻¹) = σ(inl a)`)。次セッションは終端補題の w と (C.5) 第1式の
   `(a⁻¹)^{t³}` の coe を突き合わせて sign を 1 回で固定すること。
2. **t vs t³**: BG one-step は t³。field 充足は φ=tConjAut³ で直接 (§1.1 経路B) か、経路A で w-全称。
3. **inversion (terminal `N(2w−1)` vs BG `N(2−w)`)**: `N(2w−1)=N(2−w⁻¹)` を使い w⁻¹/w を実装時に整合。
4. **経路A vs B の最終決定**: 推奨 A (field 削除可)。実装の最初に型検査で確定。

---

*作成 2026-06-05. 出典 `references/bg/local-analysis.mmd` L4994–5095, PDF pp.150–152.
先行 `notes/bg/appC_normset_plan.md` (有限体核完成) / `notes/meta/s16_appc_downstream_audit_2026_06_04.md`.*
