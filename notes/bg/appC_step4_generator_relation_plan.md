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

### 1.1 二つの配線経路 (実装時にどちらを取るか確定する)

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
| **(C.7)** | `t⁻¹s₂t⁻¹ = (w₁s₃w₂t²s₁w₃)⁻¹` (wᵢ∈U) | 新規 (再結合) |
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
   - `frobenius_replacement_C8` : (C.5) が a→aᵖ で不変 (有限体 `add_pow_char`)。
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
