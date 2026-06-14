# BG §13 後半 (Lemma 13.7–13.13) — Lane F 作業ノート

> 正本ファイル = `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeActionTransition.lean` (Lane F 所有)。
> 上流 `S13_PrimeAction.lean` (定義 + 13.1–13.6) は **Lane G 領域、cite のみ**。
> mmd `references/bg/local-analysis.mmd` L3596–3780 / PDF book pp.100–104 (**PDF page = book page + 13**)。

## 着手順 (13.6 非依存を先に)

- **13.7 `E1E3_actsPrime`** — ✅ **COMPLETE (2026-06-14, commit 916b471a, sorry-free, full build 緑)**。
  step 5 を `strict_centralizer_config_false` + sub-lemma 群 (5a/5b/step-f/H1/fixedBy_eq/anti-mono) で完遂。
- **13.8 `forbidden_config_impossible`** — 13.6 非依存。**現フロンティア**。
- 13.9 / 13.10 / 13.11 — Lane G の 13.6 landing 後 (13.9=13.6+13.8, 13.10=13.6+13.8, 13.11=13.10+13.7)。
- 13.12 / 13.13 — 未記述 (statement から)。§14 funnel が直接依存。

## ⚠ Nougat が落とした §13 の式番号 (PDF book p.100 で確定)

mmd の 13.7 証明にある `(13.2)`/`(13.4)` は Nougat が本文に残したが**定義側を落としている**。
PDF book p.100 (= PDF page 113) で確定:

- **(13.2)** = 「`E₁` and `E₃` act in a prime manner on `M_σ`」 (Thm 13.5 + Cor 13.3(b) で得る事実)
- **(13.3)** = 「`C_{M_σ}(P) ⊂ C_{M_σ}(R)`」 (strict 包含。背理法の仮定)
- **(13.4)** = 「`E = E₁E₂E₃ = E₁E₃`」 (τ₂(M) empty から)

⟹ 「By (13.2), `C_{E₁}(M_σ∩M*)=1`」は **prime-action ⟹ trivial-centralizer** の段
(下記 step 5c)。「By (13.4), `R⊆Z(E)`」は `E=E₁E₃` + `E₁` が `R` を中心化 + `E₃` 可換 ⟹ `R` を
`E` 全体が中心化。

## Lemma 13.7 証明計画 (PDF book pp.100–101)

`E₁≠1` かつ `¬ ActsRegularlyOn E₃ E₁` ⟹ `ActsPrimeOn (M_σ) (E₁⊔E₃)`。

**step 1** `¬regular` から prime 順位部分群を取る:
`¬ ActsRegularlyOn E₃ E₁` = `∃ g∈E₁#, fixedByElement E₃ g ≠ ⊥`。
g∈E₁# と h∈C_{E₃}(g)# を取り、Cauchy (`exists_prime_orderOf_dvd_card` 等) で
`P = (order p) ≤ ⟨g⟩ ≤ E₁` (`P∈ℰ_p¹(E₁)`)、`R = (order r) ≤ ⟨h⟩ ≤ E₃` (`R∈ℰ_r¹(E₃)`)。
`P` は `R` を中心化 (`P≤⟨g⟩`, `R≤⟨h⟩`, `[g,h]=1`)。

**step 2** Thm 13.4 `centralizer_le_centralizer_of_tau1` (S13_Theorem134):
`C_{M_σ}(P) ≤ C_{M_σ}(R)` (p∈τ₁M [P≤E₁ ⟹ p∈τ₁], R∈ℰ_r¹, R≤E⊓C(P))。
※ 引数: `hp:p∈tau1 M`, `hr:r∈(card E).primeFactors`, `hR:R∈elemAbelianOfRank G r 1`,
`hRC:R≤E⊓centralizer P`。

**step 3** (13.2): `E1_actsPrime` (Thm 13.5) で `ActsPrimeOn M_σ E₁`、
`cyclicSylow_actsPrime hG h |>.2` (Cor 13.3(b)) で `ActsPrimeOn M_σ E₃`。

**step 4 (equal case ⟹ 結論)**: `C_{M_σ}(P)=C_{M_σ}(R)` の場合に `ActsPrimeOn M_σ (E₁⊔E₃)`。
- prime action ⟹ `C_{M_σ}(P)=C_{M_σ}(E₁)`、`C_{M_σ}(R)=C_{M_σ}(E₃)` (各 ⟨g⟩ で fixedByElement=fixedBy)。
  ⟹ `D := C_{M_σ}(E₁) = C_{M_σ}(E₃)`、`C_{M_σ}(E₁⊔E₃)=C_{M_σ}(E₁)⊓C_{M_σ}(E₃)=D`。
- **🔑 D は E₁ と E₃ の両方で正規化される** (E₁ normalizes C_{M_σ}(E₁)=D, E₃ normalizes
  C_{M_σ}(E₃)=D)。ℰ¹ 特徴付けで: 任意の `P'∈ℰ_s¹(E₁⊔E₃)` について
  - s∈π(E₃): E₃⊲ ⟹ P'≤E₃ ⟹ C_{M_σ}(P')=C_{M_σ}(E₃)=D。
  - s∈π(E₁): Hall 共役で P'^x≤E₁ (x∈E₁⊔E₃) ⟹ C_{M_σ}(P')=x·D·x⁻¹=D (x が D を正規化)。
  ⟹ どちらも `C_{M_σ}(P')⊆D=C_{M_σ}(E₁⊔E₃)`。
- ⚠ 実装上の壁: repo `ActsPrimeOn` は **element-wise** (`C_N(g)=C_N(X)`) 定義。g=ab (a∈E₁,b∈E₃,
  非可換) を直接扱うのは困難。**ℰ¹ ⟺ element-wise の同値補題** (Cor 13.3(a) core が ℰ¹→element
  方向で似た構造) か、g=ab の C_N(ab) を上の正規化で押す補題が要る。**ここが 13.7 の本丸**。

**step 5 (strict case ⟹ 矛盾)**: `C_{M_σ}(P)⊊C_{M_σ}(R)` (13.3)。
- (a) `1⊂R⊂E₃` + `C_{M_σ}(R)≠1` + Cor 12.6(d) ⟹ τ₂(M) empty ⟹ E₂=⊥ ⟹ (13.4) `E=E₁⊔E₃`。
- (b) `R⊲E` (E₃ cyclic normal), `M*∈𝓜(N_G(R))`。`E⊆M*`、
  `1⊂[C_{M_σ}(R),P]⊆[M_σ⊓M*,E₁]` (strict 包含から P が C_{M_σ}(R) を非中心化)。
- (c) **(13.2)⟹ `C_{E₁}(M_σ⊓M*)=⊥`** = helper `actsPrimeOn_inf_centralizer_eq_bot`
  (下記 ✅landed): `ActsPrimeOn M_σ E₁` + `[M_σ⊓M*, E₁]≠⊥` (b より) ⟹ `E₁⊓C(M_σ⊓M*)=⊥`。
- (d) Cor 13.2(b) (`tau13_pSubgroup_centralizes` の `.2.1`、P:=R, p:=r∈τ₃M, M*∈𝓜(N_G(R))):
  τ₁(M*)'-部分群は M_σ⊓M* を中心化 ⟹ E₁ の τ₁(M*)'-部分は C_{E₁}(M_σ⊓M*)=⊥ ⟹ `π(E₁)⊆τ₁(M*)`。
- (e) Cor 13.2(c) (`.2.2`、[M_σ⊓M*,M⊓M*]≠⊥ は (b) より): `r∈σ(M*)` ⟹ `R⊆M*_σ`。
- (f) E₁ は M* の Hall τ₁(M*)-部分群 E₁* に入る。`E1_actsPrime` を M* に適用 ⟹ E₁* prime on M*_σ。
  `P⊆C_{E₁*}(R)`, R⊆M*_σ ⟹ E₁* (ゆえ E₁) が R を中心化。
- (g) (13.4)+E₃可換 ⟹ `R⊆Z(E)`。Lemma 12.1 `C_{E₃}(E)=1` と R≤E₃,R≠1 で矛盾。

## Lemma 13.8 証明計画 (PDF book p.101)

5 条件の配置不可能。M↔M* 対称。
- (3)(5)+Uniqueness Thm ⟹ Q は M の非自明 Sylow q-部分群 (q∉α(M))。`C_Q(P)=1` ⟹ `Q=[Q,P]⊆M'∩M*'`。
  ⟹ `QM_α⊲M`, `M=N_M(Q)M_α` (M'/M_α nilpotent, Thm 10.2)。
- Lemma 12.18 ⟹ `C_{M_β}(P)≠1`, `C_{M*_β}(P)≠1`。Prop 10.14(d) ⟹ β(M)-部分群 X⊆C_M(P) で N_G(X)⊆M。
- H = Hall (β(M)∪β(M*))-部分群 of C_G(P)。s∈π(F(H)), t∈π(F(C_{M_β}(P)))。対称性で s∈β(M)、H⊇C_{M_β}(P)。
  X=O_s(H), Y=O_t(C_{M_β}(P))。X⊆M^g ⟹ M^g⊇N_G(X)⊇H⊇Y, M⊇N_G(Y)⊇C_G(Y)。Y⊆M∩M^g、
  Thm 10.1(b) ⟹ M^g=M (∃h∈C_G(Y)⊆M)。⟹ M⊇H。
- r∈β(M*)∩π(H) ⟹ r | |C_M(P)|, Lemma 10.12(a) ⟹ r∉σ(M)。
  M=N_M(Q)M_α ⟹ ∃R⊆N_M(Q) (order r) centralized by P。R⊆N_G(Q)⊆M*, N_G(R)⊆M* (Prop 10.14(d))。
  PR は M 内で E の可換部分群に共役 ⟹ Thm 13.4: `1⊂X⊆C_{M_σ}(P)⊆C_{M_σ}(R)⊆M*`。
- `[X,Q]⊆[M_α∩M*,Q]⊆M*_α` (Q⊆M*', M*'/M*_α nilpotent, M_α∩M* は Q-invariant q'-群)。
  一方 `[X,Q]⊆M_α`, `M_α∩M*_α=1` (Lemma 10.12) ⟹ `[X,Q]=1`, `X⊆C_{M_α}(PQ)`。
  Lemma 12.18 の `C_{M_α}(PQ)=1` と矛盾。

依存はすべて landed (Uniqueness/Thm 10.1(b)/10.2/Lem 12.18/Prop 10.14(d)/Lem 10.12/Thm 13.4)。
Hall (β∪β)-部分群 + F(H) の素因子取りが mathlib API 探索ポイント。

### 13.8 handle map (2026-06-14 Lane F, 13.7 完成後の調査)
- Uniqueness (9.6): `Ch2.uniquenessTheorem` (S09_Uniqueness:47)。
- Thm 10.2 (M'/M_α nilpotent): `S10.derived_quotient_Malpha_le_fitting` 系 (S10_HallStructure:154+)。
- Lemma 12.18: `S12.tau1_Malpha_centralizer_PQ_eq_bot` (C_{M_α}(PQ)=1, S12_Lemma1218:410) +
  `tau1_Malpha_centralizer_P_ne_bot` (C_{M_α}(P)≠1, S12_E:760) + `tau1_Malpha_interaction` (main, :1025)。
- Prop 10.14(d): `S10.normalizer_le_of_nontrivial_beta_subgroup` (S10_BetaRadicalGlobal:294)。
- Lemma 10.12: `S10.disjoint_of_not_conj` (M_α∩M*_α=1 等, S10_LocalLemmasCore:1200)。
- Thm 13.4: `S13.centralizer_le_centralizer_of_tau1`。
- Fitting: `Ch01.fitting`; Hall existence: `Ch03.hall_E_exists`。
- ✅ **Thm 10.1(b) 特定 (2026-06-14)**: 機構は **`IsUniquelyMaximal`** (`OddOrder.GroupTheory.
  MaximalSubgroup`)。`IsUniquelyMaximal.existsUnique` (∃! maximal ⊇ Y) + line-139 の eq 補題
  (`IsUniquelyMaximal H → IsCoatom M → H≤M → M = uniqueMaximalSubgroup`)。Y uniquely-maximal
  + Y≤M + Y≤M^g ⟹ M=M^g。Y の uniquely-maximal は Uniqueness Thm (rank≥2 + (rank≥3 ∨
  r(C_G(Y))≥3)) で出す。⟹ 13.8 の全 handle 特定完了。step 3 の組立は ChatGPT 再構成待ち
  (`s13_8_chatgpt_prompt.md`)。

### ⚠ 状況 (2026-06-14, ユーザー判断用)
13.7 完成 (major milestone)。13.8 は ~150 行・step 3 が 13.7 step 5 級の deep grind。
**downstream value は当面低い**: 13.9-13.11 は Lane G の 13.6 待ち (Lane G は step-2/6 gap で停滞中,
issue 8003, ChatGPT 再構成中)、§14 は §13 全体待ち。13.8 自体は 13.6 非依存ゆえ Lane F で grind 可
だが、完成しても 13.6 landing まで下流は動かない。"advance Lane F" 継続として 13.8 を grind 予定
(難所回避せず) — ただしユーザーが Lane F 再配置を望む場合の判断材料として記録。

## equal-case helper の実装戦略 (refined)

step 4 を一般 helper として切る:
`E₁,E₃ prime on N` + `E₃ ⊲ (E₁⊔E₃)` + coprime orders + **`C_N(E₁)=C_N(E₃)`** ⟹
`ActsPrimeOn N (E₁⊔E₃)`。

Unit A (`actsPrimeOn_of_prime_order_le`) で素数位数 `x∈(E₁⊔E₃)#` ごとに `C_N(x) ≤ D` を示す
(`D := C_N(E₁)=C_N(E₃)`, `C_N(E₁⊔E₃)=C_N(E₁)⊓C_N(E₃)=D`):
- **s∈π(E₃)** (易): x の像が (E₁E₃)/E₃≅E₁ で位数 | gcd(s,|E₁|)=1 ⟹ x∈E₃ ⟹ E₃ prime で C_N(x)=C_N(E₃)=D。
- **s∈π(E₁)** (難): ⟨x⟩ は E₁E₃ の Sylow s。E₁ ⊇ Sylow s(E₁E₃)。**Sylow 共役**で x^g≤E₁ (g∈E₁E₃)。
  E₁ prime で C_N(x^g)=C_N(E₁)=D。C_N(x)=C_N(x^g)^{g⁻¹}=D^{g⁻¹}。**D は E₁E₃ で正規化**
  (E₁ 可換 ⟹ E₁ normalizes E₁ ⟹ C(E₁); E₃ normalizes C_N(E₃)=D; N⊲M で N も保つ) ⟹ D^{g⁻¹}=D。
  - mathlib: Sylow-in-subgroup は ↥(E₁⊔E₃) で `Sylow` を取るのが要点。共役 = `Sylow.exists_smul_eq`。
  - 注意: 一般 Hall 共役は不要 (素数 s ゆえ Sylow で足りる)。

⚠ **`C_N(E₁)=C_N(E₃)` の確立**が前提 = 13.7 body の step 2 (`≤`, Thm 13.4) + step 5 (`¬strict`,
背理法)。だから equal-case helper 単体では 13.7 は閉じない。body 側で C_N(E₁)≤C_N(E₃) と
¬(strict) を出して `=` にしてから helper を呼ぶ。

step 1 (witness 抽出) は body 内: `¬ActsRegularlyOn E₃ E₁` を push して g∈E₁#, h∈E₃⊓C({g}) 非自明、
`P=zpowers(g^{ord g/p})`, `R=zpowers(h^{ord h/r})` (`zpowers _ ∈ elemAbelianOfRank G _ 1` =
`⟨IsElementaryAbelian.of_card_prime, by rw[pow_one]; exact card=prime⟩`、card = orderOf =
`orderOf_eq_prime`)。P≤C(R) は ⟨g⟩,⟨h⟩ commute から。

## 13.8 ChatGPT 再構成 検証結果 + 形式化計画 (2026-06-14)

ChatGPT 回答 = `notes/bg/bg-lemma-13-8-elided-steps.md` (GAP 1 + GAP 2 のみ; **GAP 3 [steps 5-6] 未収録**)。
**厳密検証済: GAP 1 / GAP 2 とも健全**。ChatGPT の good catch:
- GAP 1: 「Q が M の Sylow」は Uniqueness 不要 (p-群 normalizer-growth + (5) で直接)。Uniqueness は q∉α(M) 用。
- GAP 2: Cor 12.16 (α-部分群→M_α へ共役)、Thm 10.1(b)=C_G(Y) transitivity、Lem 10.12(a) を **役割入替** で r∉σ(M)。
### 🔑 12.18(b) で GAP 1.4 (Uniqueness) は不要に
`tau1_Malpha_interaction` の **第 2 連言** (S12_Lemma1218:1039-1042): 仮定
`∀T≤M, IsPGroup q T, Q≤T → Q=T` (Q が M の極大 q-部分群 = Sylow) から直接
`q∉α(M) ∧ α(M)=β(M) ∧ M_α⊓C(P)≠⊥ ∧ M_α⊓C(P⊔Q)=⊥`。
⟹ GAP 1 は 1.1 (Q≠1) + 1.2 (q≠p) + 1.3 (Q 極大 q-sub of M, normalizer-growth) のみ。
**step 6 の punchline `C_{M_α}(PQ)=1` も 12.18(b) から無料**。
### 形式化計画 (sub-lemma 分解)
- `step1` (M側): config → 12.18(b) outputs。1.3 = normalizer-growth (`lt_normalizer_inf_sylow_of_lt`
  Isaacs Ch07:91、or NormalizerCondition of nilpotent q-group) + (5)。M* 側は対称に再適用。
- `step3` (GAP 2): Hall θ=β(M)∪β(M*) of C_G(P) → r∈β(M*)∩π(C_M(P)), r∉σ(M)。
  handles: Hall 存在/共役 (Prop 1.5)、Cor 12.16、`IsUniquelyMaximal`/Thm 10.1(b) transitivity、
  Prop 10.14(d) `normalizer_le_of_nontrivial_beta_subgroup`、Lem 10.12 `disjoint_of_not_conj`、
  F(H)=`Ch01.fitting`、O_s = `S10.opiCoreInG`?。⚠ Thm 10.1(b) の transitivity form を repo で要特定。
- `step5/6` (GAP 3, **要追加再構成 or 自力**): R⊆N_M(Q) order r P-centralized + Thm 13.4
  `centralizer_le_centralizer_of_tau1` → X⊆C_{M_σ}(P)⊆C_{M_σ}(R)⊆M*; [X,Q]=1 (M_α∩M*_α=1) →
  X⊆C_{M_α}(PQ)=1 (12.18(b)) 矛盾。

## 進捗

- 2026-06-14 (Lane F, /loop 続き⁸): **🎉 13.8 GAP 1 (Uniqueness step) COMPLETE** (commit c7fb4c19, full build 緑 3807)。
  - `lt_inf_normalizer_of_lt_of_pgroup` (標準補題): 有限 q-群 T で Q<T ⟹ Q<T⊓N_G(Q)。
    `normalizerCondition_of_isNilpotent`+`IsPGroup.isNilpotent`+`subgroupOf_normalizer_eq`。
    ⚠ `Group.IsNilpotent` 修飾必須 (`IsNilpotent` 単体は環の冪零元 → `Zero (Type)` エラー)。
  - `forbidden_config_step1` (M-side engine, M↔M*/Q↔Q* 対称再利用可): config → 12.18(b) 出力
    `α=β ∧ M_α≠1 ∧ q∉α ∧ C_{M_α}(P)≠1 ∧ C_{M_α}(PQ)=1`。GAP 1.1 (Q≠1: `normalizer_eq_top_iff`+
    coatom), 1.2 (q≠p: `to_sup_of_normal_right'` で P⊔Q が p-群→hQmax で Q=P⊔Q→P≤C_Q(P)=⊥),
    1.3 (`lt_inf_normalizer_of_lt_of_pgroup`+hQmax), ℳ(N_G(Q))≠{M} (`mem_maximalSubgroupsContaining`)。
  - **残 = GAP 2 (Hall θ=β(M)∪β(M*) of C_G(P) → r∈β(M*)∩π(H), r|C_M(P), r∉σ(M))**
    + GAP 3 (steps 5-6: R⊆N_M(Q) order r → Thm 13.4 → X⊆C_{M_σ}(P)⊆C_{M_σ}(R)⊆M*;
    [X,Q]=1 (M_α∩M*_α=1) → X⊆C_{M_α}(PQ)=1 矛盾) + 本体配線。
  - **⚠ GAP 3 は ChatGPT 回答 (bg-lemma-13-8-elided-steps.md) 未収録** — 次イテレーションで
    GAP 2 を進めつつ、GAP 3 は s13_8_chatgpt_prompt.md の該当部を再依頼 or 自力再構成。
  - 次標的: GAP 2 の Hall θ-部分群存在/共役 (Prop 1.5) + Cor 12.16 + Thm 10.1(b) transitivity
    (`IsUniquelyMaximal`) + Prop 10.14(d) + Lem 10.12(a) の repo handle 特定。
  ### GAP 2 handle scout (2026-06-14)
  - **r∉σ(M)** (GAP 2.11): `S10.disjoint_of_not_conj hMstar hM hnc' |>.1.2 : alpha M* ∩ sigma M = ∅`
    (roles 入替: 第1=M*, 第2=M; hnc'=¬∃g,conj g•M*=M を hnc から共役対称で導出)。
    `r∈α(M*)` (←β(M*)⊆α(M*)) かつ `r∈σ(M)` を `∈ ∅` に落として矛盾。
  - **Hall**: `Isaacs.Ch03.hall_E_exists [Finite ·] [IsSolvable ·] (π) : ∃ H, IsHallSubgroup π H`
    (Ch03 Main:837)。C_G(P) の Hall θ-部分群は ↥(C_G(P)) に適用 (solvable: 真部分群)→transport。
    π-membership: `IsHallSubgroup.primeFactors_card_subset` (Main:585) 等。
  - **Cor 12.16(a) q-group specialization** = `S12_Corollary1216` line 307 (要署名精読: 非自明
    q-群 Y⊆? が M_α へ共役)。X=O_s(H) は s∈β(M)⊆α(M) の s-群ゆえ適用可。
  - **Thm 10.1(b) transitivity** = `IsUniquelyMaximal` (Y uniquely-maximal ⟹ ℳ(Y) 一意): Y=O_t(C_{M_β}(P)),
    Uniqueness Thm (rank) で Y∈𝒰 → M=M^g。MaximalSubgroup.lean の `.existsUnique` + eq 補題。
  - **F(H)/O_s** = `Ch01.fitting` / p-core (opi 系)。⚠ subtype transport (Hall in ↥C_G(P)) が最大の工数。
- 2026-06-14 (Lane F, /loop 続き⁹): **🎉 13.8 GAP 2.8 collapse 補題 COMPLETE** (commit 65fd4216, full build 緑)。
  `conj_eq_self_of_sigma_pSubgroup_normalizer_le`: t∈σ(M), Y 非自明 t-部分群 of M, N_G(Y)⊆M, Y≤M^g
  ⟹ M^g=M。**Thm 10.1(b) = `S10.fusion_control_of_mem_sigma .2.1`** (transitivity; S12_Lemma1211:1087
  の M*=M** 適用を mirror) + C_G(Y)⊆N_G(Y)⊆M で c∈M が M 固定。
  ### GAP 2 r-existence 補題 構成計画 (次イテレーション、全 handle 確定)
  目標: `∃ r, r∈β(M*) ∧ r ∣ |C_M(P)| ∧ r∉σ(M)`。step1 両側 (C_{M_β}(P)≠1, C_{M*_β}(P)≠1) を入力。
  1. **C_G(P) 可解**: C_G(P)<⊤ (P≠1, simple) → `eq_top_or_exists_le_coatom` で coatom M'⊇C_G(P)
     → `hG.solvable_of_mem_maximalSubgroups` + `solvable_of_solvable_injective`。
  2. **Hall θ of C_G(P)**: `Ch03.hall_E_exists (G:=↥C) (beta M ∪ beta Mstar)` → H₀:Subgroup ↥C;
     G へ `H₀.map C.subtype`。⚠ WLOG「H⊇C_{M_β}(P)」= Hall 共役 (`exists_conj...hallPiece` 系)。
  3. **conj-into-Msigma** (要 standalone 抽出, `pRank_normalizer_le_one` Step1 を mirror, ~20行):
     q-群 Y, q∈σ(M) ⟹ ∃g, conj g•Y ≤ M_σ。ingredients = `S10.mem_sigma_iff`/
     `isSylow_sylowMap_of_mem_sigma`/`sigma_subgroup_le_Msigma_of_isHall`/`hYq.exists_le_sylow`/
     `MulAction.exists_smul_eq`。X=O_s(H) (s∈β(M)⊆σ(M)) に適用 → X≤M^g。
  4. **N_G(X)≤M^g, N_G(Y)≤M**: `S10.normalizer_le_of_nontrivial_beta_subgroup` (Prop 10.14d, 要
     `IsPiSubgroup (beta ·) ·` = `isPiSubgroup_of_isPGroup_of_mem` [S12_ExceptionalBridge:129])。
     β conj-invariance (`sigma_conj` 類推 or `beta_conj`) で s∈β(M^g)。
  5. **collapse**: `conj_eq_self_of_sigma_pSubgroup_normalizer_le` (Y, t∈β(M)⊆σ(M), N_G(Y)⊆M,
     Y≤M^g [←H≤M^g]) ⟹ M^g=M ⟹ H≤M ⟹ H≤C_M(P)。
  6. **r 抽出**: C_{M*_β}(P)≠1 → ∃r∈β(M*), r∣|C_G(P)|; r∈θ ∧ H Hall θ ⟹ r∣|H|∣|C_M(P)|.
     r∉σ(M): `S10.disjoint_of_not_conj hMstar hM hnc' |>.1.2` (α(M*)∩σ(M)=∅, β⊆α)。
  ⚠ 最難 = WLOG s∈β(M) (M↔M* 対称化) + H⊇C_{M_β}(P) (Hall 共役) + subtype transport。2-3 iter 見込み。
- 2026-06-14 (Lane F, /loop 続き¹⁰): **🎉 conj-into-Msigma 補題 COMPLETE** (commit, full build 緑)。
  `exists_conj_smul_le_Msigma_of_pSubgroup`: q∈σ(M), q-群 Y ⟹ ∃g, Y^g⊆M_σ。GAP 2.5 の核。
  - ✅ **13.6 は Lane G で進行中** (main: 09a53a44 infra, c6580a9a gaps RESOLVED; S13_PrimeAction:558 は
    まだ sorry だが近い) ⟹ 13.8 完成は **間もなく high-value 化** (13.6+13.8→13.9-13.11 解禁)。継続が正。
  ### 🔑 GAP 2 精密アーキテクチャ確定 (hall_D で WLOG 簡略化)
  - **`hall_D [Finite][IsSolvable] {π}{U} (∀q∈π(U), q∈π) : ∃H, IsHallSubgroup π H ∧ U≤H`** (Ch03 Main:1486)
    ⟹ ↥C で U=C_{M_β}(P).subgroupOf C に適用すれば「H⊇C_{M_β}(P)」が一発 (Hall 共役不要)。
  - **核 (A) `hall_le_of_fitting_prime_mem_beta` (H≤M, 向き付き s∈β(M), M 側のみ・M* 不要)** [GAP2 steps4-8]:
    入力 = M maximal, s∈β(M), H Hall θ of C_G(P) with C_{M_β}(P)≤H ∧ C_{M_β}(P)≠1 ∧ s∈π(F(H))。
    X=O_s(H) (char in H→H≤N_G(X); s-群; s∈σ(M)→`exists_conj_smul_le_Msigma_of_pSubgroup`→X≤M^g;
    Prop10.14d→N_G(X)≤M^g; ⟹ H≤M^g)。Y=O_t(C_{M_β}(P)) (t∈π(F(C_{M_β}P))⊆β(M), Y≤M∩M^g, N_G(Y)≤M,
    t∈σ(M)) → **collapse** `conj_eq_self_of_sigma_pSubgroup_normalizer_le` → M^g=M → H≤M。
    **次イテレーションの標的**。要 handle: O_s=opiCore char+nontrivial-from-F-prime, F(H) prime, O_t。
  - **(B) main dispatch**: 汎用 H 構成 → s∈π(F(H))⊆β(M)∪β(M*); s∈β(M) なら (A)+GAP3(M,M*);
    s∈β(M*) なら (A)(M:=M*)+GAP3(M*,M) [M↔M* 対称]。⟹ GAP3 も対称 helper 化要。
  - **r 抽出** (H≤M 後): C_{M*_β}(P)≠1→∃r∈β(M*), r∣|C_G(P)|; r∈θ∧H Hall θ→r∣|H|∣|C_M(P)|; r∉σ(M)
    via `S10.disjoint_of_not_conj hMstar hM hnc' |>.1.2`。
- 2026-06-14 (Lane F, /loop 続き¹¹): **🎉🎉 13.8 GAP 2 の核 `hall_le_of_fitting_prime` (H≤M) COMPLETE**
  (commit 3ea53795, full build 緑 3807, アーキ分析が効いて一発)。s∈β(M) が F(H) を割り Y を M∩H の
  非自明 β(M)-部分群 (t-群) とすると H≤M。X=O_s(H) を M_σ へ共役 → X'=X^a に Prop 10.14(d) を M 側で
  適用 (β 共役不変性回避) → H≤M^{a⁻¹}, Y で collapse → H≤M。
  ### 🔑 残り 13.8 アーキテクチャ (WLOG は 13.8 本体レベル)
  - **(B') oriented r-existence**: s∈β(M) (F(H)-prime) なら r∈β(M*) ∣ |C_M(P)|, r∉σ(M)。[M 側]
    = C_G(P) 可解 + `hall_D` で H⊇C_{M_β}(P) (θ-Hall) + F(H)≠1 で s 抽出 + `hall_le_of_fitting_prime` +
    C_{M*_β}(P)≠1 で r∈β(M*)∣|H|∣|C_M(P)| + `disjoint_of_not_conj.1.2` で r∉σ(M)。
    ⚠ Y=O_t(C_{M_β}(P)): t∈π(F(C_{M_β}P))⊆β(M), Y≠⊥ (fittingInG≠⊥ from nontrivial solvable),
    Y≤C_{M_β}(P)≤M ∧ ≤H。C_{M_β}(P)=C_{M_α}(P) (α=β from step1), β-group (Malpha_isPiGroup+α=β)。
  - **GAP 3 oriented (symmetric)**: r∈β(M*)∣|C_M(P)|, r∉σ(M) + step1 outputs → False。[M 側]
    ⚠ **要 reconstruction** (ChatGPT 未収録): M=N_M(Q)M_α + PR を E の可換部分群へ共役 + Thm 13.4 →
    X⊆C_{M_σ}(R)⊆M*; [X,Q]=1 (M_α∩M*_α=1) → X⊆C_{M_α}(PQ)=1 矛盾。
  - **main**: H 構成 → s∈π(F(H))⊆β(M)∪β(M*); s∈β(M): (B'-M)+(GAP3-M); s∈β(M*): (B'-M*)+(GAP3-M*)。
  - landed building blocks: step1 / normalizer-growth / collapse / conj-into-Msigma / **hall_le (核)**。
  - 次: BG 本文 (mmd ~L3640) で GAP 3 steps 5-6 を精読し自力再構成可否を判断 → (B') か GAP 3 を執筆。
- 2026-06-14 (Lane F, /loop 続き¹²): BG 本文 (mmd L3660-3690) で 13.8 全証明精読 + `centralizer_isSolvable_of_ne_bot`
  landed (commit 59f534fa, B' の基礎)。**GAP 3 (steps 5-6) は reconstruction-gap (BG が lemma 名明示)**。
  ### 🔑 GAP 3 (最終矛盾) の 4 elision (BG L3686-3690, lemma 名付き — research-gap でない)
  X := C_{M_α}(P) (≠1 from step1, ⊆M_α⊆M_σ, P 中心化) を矛盾に追い込む:
  - **(i) `M=N_M(Q)M_α`** (L3674, GAP 3 前): QM_α⊲M + M'/M_α nilpotent (Thm 10.2) の Frattini。
    Q=[Q,P]⊆M'∩M*' (Q Sylow of M, C_Q(P)=1)。Thm 10.2 = `S10.derived_quotient_Malpha...`。
  - **(ii) ∃R⊆N_M(Q) 位数 r, [R,P]=1** (L3686): M=N_M(Q)M_α + r∈π(C_M(P)) + r∉σ(M)⊇π(M_α)
    (r∤|M_α|) → r-part は N_M(Q) 側; coprime action (p≠r) で P-不変 → R⊆C_{N_M(Q)}(P)。
  - **(iii) `PR を E の可換部分群へ M-共役`** (L3686): PR=P×R ({p,r}-群, [R,P]=1 で可換), p∈τ₁⊆σ',
    r∉σ ⟹ σ'-群 → Hall E (σ'-Hall) へ M-共役。⟹ Thm 13.4 適用可 → C_{M_σ}(P)⊆C_{M_σ}(R)。
  - **(iv) `[M_α∩M*,Q]⊆M*_α`** (L3690): M_α∩M* は q'-群 (q∉α ⟹ q∤|M_α|), Q-不変; Q⊆M*',
    M*'/M*_α nilpotent + coprime ⟹ commutator ⊆ M*_α。
  矛盾組立: X⊆C_{M_σ}(R)⊆N_G(R)⊆M* (R⊆M*, Prop10.14d N_G(R)⊆M*) ∧ X⊆M_α ⟹ X⊆M_α∩M*;
  [X,Q]⊆M*_α (iv) ∧ [X,Q]⊆M_α ∧ M_α∩M*_α=1 (Lem10.12) ⟹ [X,Q]=1 ⟹ X⊆C_{M_α}(PQ)=1 (step1) 矛盾。
  - **(B') r-existence dispatch**: H 構成 → s∈π(F(H)); s∈β(M) なら hall_le→H≤M→r∈β(M*)|C_M(P);
    s∈β(M*) なら hall_le(M:=M*)→H≤M*→r∈β(M)|C_{M*}(P)。GAP3 は対称ゆえ両 disjunct を処理。
  building blocks (7): step1/normalizer-growth/collapse/conj-into-Msigma/hall_le/**centralizer_solvable**。
  - 次: (B') r-existence_or_swapped (Hall θ 構成 + F(H) prime + hall_le + r 抽出) を執筆。GAP 3 は
    その後 (4 elision を BG 本文 + repo lemma で自力再構成; 詰まれば ChatGPT に該当 elision のみ依頼)。
- 2026-06-14 (Lane F, /loop 続き¹³): **🎉🎉🎉 GAP 2 (M-oriented) 完成 — 計 11 building blocks**。
  3 補題 landed (commits 42b4c551/8877eceb/6524fa30): `exists_mem_primeFactors_fittingInG` (F(H)≠1→素数),
  `exists_prime_betastar_dvd_of_hall_le` (H≤M 後 r 抽出, Hall index 算術), `oriented_r_existence`
  (M-oriented GAP 2 全体)。+ `centralizer_isSolvable_of_ne_bot` + `exists_hall_theta_ge` (前 iter)。
  ### 残り 13.8 (assembly のみ — building blocks 出揃い)
  - **GAP 3 (oriented, symmetric)**: r∈β(M*)∣|C_M(P)|, r∉σ(M) + config → False。4 elision:
    (i) Frattini M=N_M(Q)M_α, (ii) coprime R⊆N_M(Q), (iii) σ'-群 PR を Hall E へ共役 [Thm 13.4 適用],
    (iv) nilpotent [M_α∩M*,Q]⊆M*_α。X=C_{M_α}(P)≠1 を C_{M_α}(PQ)=1 と矛盾。**次の標的**。
  - **main dispatch**: H⊇C_{M_β}(P) 構成 (`exists_hall_theta_ge`) → s∈π(F(H)) (`exists_mem_primeFactors_fittingInG`);
    s∈β(M): `oriented_r_existence`(M,M*)+GAP3(M,M*); s∈β(M*): H*⊇C_{M*_β}(P) + Hall 共役 (`hall_C`)
    で s∈π(F(H*)) 移送 → `oriented_r_existence`(M*,M)+GAP3(M*,M)。⚠ Hall 共役 + Fitting card 不変が要。
  - **配線**: step1 両側 + C_{M_α}(P)≠1 を Y₀ に渡す (β(M)-group via Malpha_isPiGroup+α=β)。
- 2026-06-14 (Lane F, /loop 続き¹⁴): **🎉 gap3_assembly (GAP 3 最終矛盾) landed (12 blocks)**。
  ### 🛑 残り 13.8 は「genuine elision + 非自明 machinery」のみ — quick win 無し (inflection)
  調査結果:
  - **GAP 3 head/elisions = genuine textbook elision + handle 欠如**:
    - coprime `[Q,P]=Q` (Q⊆M'∩M*') — repo に直接 handle 無し (Ch04 operator-group 形のみ)。
    - Frattini `M=N_M(Q)M_α` — `Sylow.normalizer_sup_eq_top` はあるが QM_α⊲M (Thm 10.2 + nilpotent
      normal Sylow + subtype) の sub-elision 付き。
    - (iii) PR を Hall E へ共役 + Thm 13.4 / (iv) `[M_α∩M*,Q]⊆M*_α` (M*'/M*_α 経由) = 行間。
    ⟹ **ユーザー手法 (ChatGPT 再構成) を使う。プロンプト `s13_8_chatgpt_prompt.md` の GAP 3 (3a/3b/3c)
    は精密に既存** (head/iii/iv カバー)。ユーザーが GAP 1+2 のみ返答 → **GAP 3 part 未実行**。要依頼。
  - **dispatch (WLOG s∈β(M)/β(M*))**: `hall_C` (Hall 共役) はあるが、`fittingInG` の同型不変性
    (π(F(H))=π(F(H*))) が repo に無く要構築 (Fitting functoriality under MulEquiv + card)。
    elision でなく純粋形式化ゆえ並行で自力構築可。
  - **方針**: GAP 3 elisions は ChatGPT 回答待ち (依頼済) → 検証後 formalize。並行で dispatch の
    Fitting-functoriality-under-conj helper を自力構築。
- 2026-06-14 (Lane F, /loop 続き¹⁵): **dispatch 基盤 3 補題 landed (15 blocks)**:
  `opCore_map_le_of_mulEquiv`/`opCore_map_of_mulEquiv`/`fitting_card_eq_of_mulEquiv` (Fitting 同型不変性,
  汎用) + `fittingInG_primeFactors_eq_of_isHall_subgroupOf` (Hall 共役→同 F-primes, dispatch 核)。
  ### 🔑 訂正: head は grindable (ChatGPT 待ち不要、(iv) のみ genuine)
  - **head `Q=[Q,P]⊆M'∩M*'`**: `Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot`
    (S08:1424; B≤N(Y), coprime, Y⊓C(B)=⊥ → Y≤⁅B,Y⁆) で Q≤⁅P,Q⁆; ⁅P,Q⁆≤⁅M,M⁆=derivedInG M。✅
  - **head Frattini `M=N_M(Q)M_α`**: `S13_Lemma131.exists_sylow_frattini_decomp` (:204) が同型の
    Frattini 分解 (M=opiCoreInG(β∪{q})(M')⊔(M⊓N_G(Y))) を既に提供。同パターンで導出可。✅(要 adapt)
  - **(ii) R-existence / (iii) PR→E+Thm13.4**: grindable (coprime action / Hall 共役 + Thm 13.4)。
  - **(iv) `[M_α∩M*,Q]⊆M*_α`**: 唯一 genuine な不確実点 (M*'/M*_α 経由の議論)。impasse なら ChatGPT。
  - **改訂方針**: head + (ii) + (iii) は自力 grind (handle 判明)。(iv) は試行 → 詰まれば ChatGPT。
    GAP 3 ChatGPT 回答が来れば iii/iv 一括検証。次イテレーション = head `Q=[Q,P]⊆M'∩M*'` を landing。
- 2026-06-14 (Lane F, /loop): main ff-merge で hub の split (`S13_PrimeActionTransition.lean`) 取込。
  式番号 (13.2)(13.3)(13.4) を PDF で確定。helper 2 本 landed (✅ sorry-free, leaf 緑):
  `actsPrimeOn_inf_centralizer_eq_bot` (step 5c) + `actsPrimeOn_of_prime_order_le` (step 4 reduction)。
  witness 抽出 API (`zpowers _ ∈ elemAbelianOfRank`) 確認済。
- 2026-06-14 (Lane F, /loop 続き): **equal-case crux 完成** — helper 計 4 本 landed:
  `le_normalizer_fixedBy` + **`actsPrimeOn_sup_of_eq_centralizer`** (13.7 equal case)。
  Sylow 不要、Peterfalvi (2.1) `exists_mem_centralizer_conj` で coset collapse → c=1 forcing。
  `coe_mul_of_right_le_normalizer_left` で product 分解、`SemiconjBy.orderOf_eq` で共役 ord 不変。
  次 = **13.7 body 組立**: step 1 (witness 抽出, `¬ActsRegularlyOn E₃ E₁` → P,R) + step 2
  (Thm 13.4 `centralizer_le_centralizer_of_tau1` → C_N(E₁)≤C_N(E₃)) + step 5 (背理法で ¬strict,
  H1 `actsPrimeOn_inf_centralizer_eq_bot` + Cor 13.2(b)(c) `tau13_pSubgroup_centralizes` +
  Thm 13.5 を M* に + Lem 12.1 C_{E₃}(E)=1 + Cor 12.6(d) τ₂ empty) ⟹ C_N(E₁)=C_N(E₃) →
  `actsPrimeOn_sup_of_eq_centralizer` で 13.7 完成。その後 13.8。
  ⚠ helper の hcop は `Nat.Coprime (Nat.card E₁) (Nat.card E₃)` 形 — body で SubgroupESetup から
  E₁/E₃ の位数互素を出す (τ₁ vs τ₃ disjoint + Hall)。
- 2026-06-14 (Lane F, /loop 続き²): **step 1 完成** — `exists_elemAbelian_centralizing_of_not_regular`
  (helper 計 5 本)。`actsRegularlyOn_iff`+push_neg で witness、local `key` で素数べき部分群、
  `pow_mem` は SetLike-implicit (`Subgroup.pow_mem` は H explicit)。残 = **13.7 body**:
  - **prereq**: `hnorm := h.E₁_le.trans (h.E3_normal hG)` (E3_normal: `E ≤ normalizer ↑E₃`),
    `hN3`: E₃≤E≤M≤normalizer(Msigma M) [M≤normalizer は S10_LocalLemmasCore:500 の構成
    `rw[Msigma]; exact le_normalizer_opiCoreInG (sigma M) M` を再現 or 公開補題探す],
    **`hcop` (E₁/E₃ card 互素) は未確認 TODO** — τ₁∩τ₃=∅ + Hall から導出 (要 τ disjoint 補題)。
  - **step 2**: `centralizer_le_centralizer_of_tau1` (Thm 13.4, S13_Theorem134) → C_N(P)≤C_N(R)。
    prime action `E1_actsPrime`/`cyclicSylow_actsPrime.2` で C_N(P)=C_N(E₁), C_N(R)=C_N(E₃)
    (P=zpowers, C(zpowers gen)=C({gen})) → C_N(E₁)≤C_N(E₃)。
  - **step 5** (¬strict, `eq_of_le_of_not_lt` で hD 完成。最大の塊 ~70行):
    `intro hlt` (fixedBy E₁ < fixedBy E₃) → False。
    (a) R cyclic で C_{M_σ}(R)=C_{M_σ}(r_elt)≠⊥ + `elemAb_normal_in_E_of_tau2` の component
       `∀x∈E₃#, M_σ⊓C{x}=⊥` の対偶 → τ₂(M) empty → E₂=⊥ → E=E₁⊔E₃ (要 E=E123 補題)。
    (b) `exists_subgroupESetup hG hM*mem` で M*∈𝓜(N_G(R)) の SubgroupESetup。E⊆M*、
       `[C_N(R),P]⊆[M_σ⊓M*,E₁]` 非自明 (strict から P が C_N(R) 非中心化)。
    (c) `actsPrimeOn_inf_centralizer_eq_bot` (H1) → C_{E₁}(M_σ⊓M*)=⊥。
    (d) `tau13_pSubgroup_centralizes .2.1` (Cor 13.2b, P:=R, r∈τ₃M) → π(E₁)⊆τ₁(M*)。
    (e) `.2.2` (Cor 13.2c) → r∈σ(M*) → R⊆M*_σ。
    (f) E₁≤E₁*(Hall τ₁M*), `E1_actsPrime` on M* → E₁* prime on M*_σ、P⊆C_{E₁*}(R) → E₁ が R 中心化。
    (g) E=E₁⊔E₃ + E₁,E₃ が R 中心化 → R⊆C_G(E)。`subgroupE_basic` の `centralizer E⊓E₃=⊥`
       (=C_{E₃}(E)=1) と R≤E₃,R≠⊥ で矛盾。
- 2026-06-14 (Lane F, /loop 続き³): **13.7 body prereqs + step 1/2 完成** (helper 計 6 本)。
  + `fixedBy_eq_of_elemAbelian_one` (C_N(P)=C_N(X), prime action)。step 1 helper に primality 出力追加。
  body 確定パターン: hcop=τ₁∩τ₃=∅ (`not_mem_tau3_of_mem_tau1`) + Hall `.1` + `subgroupOfEquivOfLe`
  card; hnorm=`h.E₁_le.trans (h.E3_normal hG)`; hN3=`(h.E₃_le.trans h.E_le).trans
  (by rw[S10.Msigma]; exact le_normalizer_opiCoreInG (S10.sigma M) M)`; step2=`fixedBy_eq` ×2 +
  `centralizer_le_centralizer_of_tau1`; dichotomy=`rcases lt_or_eq_of_le hle`。
  **残 = step 5 のみ** (`exfalso` 後の内側 sorry 1 個; hlt : fixedBy E₁ < fixedBy E₃ から False)。
  step 5 の詳細手順 (a)-(g) は上記マップ参照。次イテレーションで step 5 を書いて 13.7 完成。
- 2026-06-14 (Lane F, /loop 続き⁴): **🎉 13.7 (E1E3_actsPrime) body COMPLETE・sorry-free**。
  step 5 を named lemma `strict_centralizer_config_false` (docstring に (a)-(g) plan) へ隔離。
  **残り Lane F の 13.7 work = この 1 lemma の証明のみ** (sorry-neutral)。
  ### step 5 grind 戦略 (次イテレーション〜)
  step 5 は BG 13.4 (`S13_Theorem134.lean` の per_q_centralizes / alpha_fixed_le_fixed) の
  M* 論法を mirror するのが近道 — 共通ツール: `maximalSubgroupsContaining (N_G ·)` 抽出
  (`actsPrimeOn_Msigma_of_mem_tau13` の coatom パターン)、Cor 13.2 `tau13_pSubgroup_centralizes`、
  Lem 12.18、`exists_subgroupESetup` (M*用)。**要 handle 調査 (まだ未確定)**:
  - **R⊲E** (E≤normalizer R): R∈ℰ_r¹(E₃) は cyclic E₃ の唯一の位数 r 部分群 ⟹ char ⟹
    E≤norm E₃ から E≤norm R。cyclic-unique-subgroup 補題が要。
  - **τ₂(M) empty → E₂=⊥ → E=E₁⊔E₃** (step a→g 接続): `elemAb_normal_in_E_of_tau2` の
    component `∀x∈E₃#, M_σ⊓C{x}=⊥` の対偶で「∃p∈τ₂,A∈ℰ_p²」を排除 → E₂=⊥。E=E123 補題 + E₂ Hall。
  - **r∈σ(M*) → R≤M*_σ**: `opiCoreInG_singleton_le_Msigma_of_mem_sigma` 系 (S10_HallStructure:744)。
  - **E₁ ⊆ Hall τ₁(M*)**: π(E₁)⊆τ₁M* + E₁≤M* → Hall に埋め込む (`exists_conj_smul_le_hallPiece` 系?)。
  これらが揃えば (a)-(g) を直線的に書ける。1-2 iteration 見込み。
- 2026-06-14 (Lane F, /loop 続き⁵): **step 5 を committable sub-lemma へ分解開始** (2 本 landed):
  - **(a) `E_eq_sup_of_E3_centralizer`**: x∈E₃#,C_{M_σ}(x)≠1 ⟹ E=E₁⊔E₃ (`SubgroupESetup.eq_sup` +
    τ₂ empty via `exists_elemAb_rank_two_le_E_of_tau2` + `elemAb_normal_in_E_of_tau2 .2.2.2.1`)。
  - **(b 補助) `E_le_normalizer_of_le_E3`**: R≤E₃ ⟹ E≤N_G(R) (`characteristic_of_subgroup_of_isCyclic`
    + `mem_normalizer_map_subtype_of_characteristic`; S13_PrimeAction:324-331 の zpowers 版を一般化)。
  ### 残 M*-core (strict_config 本体、steps b-g)
  M* 抽出 = S13_PrimeAction:333-347 を mirror (normalizer≠⊤ via simple+maximal + coatom +
  `maximalSubgroupsContaining`; E⊆M* = `E_le_normalizer_of_le_E3` ∘ hNxM)。
  - **step c** (H1): [C_{M_σ}(R),P]≠⊥ (strict から P が C_{M_σ}(R) 非中心化) ⊆ [M_σ⊓M*,E₁]
    (C_{M_σ}(R)⊆M_σ⊓M*) ⟹ `actsPrimeOn_inf_centralizer_eq_bot` で C_{E₁}(M_σ⊓M*)=⊥。
  - **step d** (Cor 13.2(b)): `tau13_pSubgroup_centralizes hG h (hp:r∈τ₃M) hRM hRne hRp hMstarMem |>.2.1`
    で π(E₁)⊆τ₁M*。
  - **step e** (R⊆M*_σ): r∈σ(M*) (Cor 13.2(c) `.2.2`) + **`sigma_subgroup_le_Msigma_of_isHall`**
    (`Msigma_isHall hG hM*`, R≤M*, R は σ(M*)-群) ⟹ R≤M*_σ。✅handle 確定。
  - **🔑 step f** (E₁ が R 中心化、最難): E₁ を含む Hall τ₁(M*) `E₁*` が M*_σ に prime 作用
    (Thm 13.5 を M* の setup に + **prime action の M*-共役不変性** が要 — step 4 同様の難所)。
    P≤E₁≤E₁*, R⊆M*_σ, P が R 中心化 ⟹ `fixedBy_eq` (C_{M*_σ}(P)=C_{M*_σ}(E₁*)) で E₁* (ゆえ E₁) が R 中心化。
    ⚠ ActsPrimeOn の共役不変補題が未整備 → 次イテレーションで要対応 (新 helper か exists_subgroupESetup
    の E₁* に E₁ を合わせ込む)。
  - **step g**: E=E₁⊔E₃ ((a)) + E₁,E₃ が R 中心化 ⟹ R⊆C_G(E₁⊔E₃)=C_G(E) (centralizer_sup)、
    `subgroupE_basic` の C_G(E)⊓E₃=⊥ + R≤E₃,R≠⊥ で矛盾。
- 2026-06-14 (Lane F, /loop 続き⁶): step f を精査。**E1_actsPrime の `key` (S13_PrimeAction:442-520)
  は Thm 13.4 `centralizer_le_centralizer_of_tau1` を使い、これは `R ≤ E`(setup の補群)を要求** ⟹
  一般 cyclic K≤M* (K⊄E*) への generalize は不可。step f は **prime-action 共役不変性 + Hall 共役**が必要。
  - ✅ landed: `ActsPrimeOn.of_le_right` (anti-mono: X prime, X'≤X ⟹ X' prime)。
  - **step f assembly path** (次イテレーション):
    1. M*∈𝓜(N_G(R)) の setup (exists_subgroupESetup)、E₁* = Hall τ₁(M*) prime (E1_actsPrime on M*)。
    2. **Hall 共役**: E₁ は τ₁(M*)-subgroup (π(E₁)⊆τ₁M*) ⟹ `E₁ ≤ w • E₁*` (w∈M*)
       (`exists_conj_smul_le_hallPiece` / `exists_conj_eq_of_isHall_subgroupOf` 系)。
    3. **conj-inv** (要 new helper `ActsPrimeOn.conj`: X prime on N, g∈normalizer N ⟹ g•X prime on N;
       pointwise smul + C_N(gxg⁻¹)=g·C_N(x)·g⁻¹): `w•E₁*` prime on M*_σ。
    4. `E₁ ≤ w•E₁*` + anti-mono ⟹ E₁ prime on M*_σ。
    5. P∈ℰ_p¹(E₁), P が R 中心化, R⊆M*_σ ⟹ `fixedBy_eq` で R⊆C_{M*_σ}(P)=C_{M*_σ}(E₁) ⟹ E₁ が R 中心化。
  - ⚠ conj-inv の pointwise-smul (`MulAut.conj g • X`, `mem_pointwise_smul_iff_inv_smul_mem`) が fiddly。
    次イテレーションの最初の標的。これが landing すれば step f → strict_config → 13.7 完全完成。
- 2026-06-14 (Lane F, /loop 続き⁷): **🎉 step f 完成 `E1_centralizes_R_of_hall_tau1`** (conjugation crux)。
  conj-inv を回避 — R・P を M* の setup frame へ共役。`exists_conj_smul_le_hallPiece` で w•E₁≤E₁*、
  P 生成元の共役 z∈E₁*# が w•R 中心化、E1_actsPrime + prime 作用で E₁* が w•R 中心化、共役戻し。
  fiddle 知見: `Ch03.Subgroup.IsPiGroup` (namespace)、`Subgroup.smul_mem_pointwise_smul_iff.mpr`、
  `(MulAut.conj w).injective` で z≠1、`hwMsig` は `le_normalizer_opiCoreInG`、commute は calc+group。
  **⚠ leaf build の errcount grep が再び stale-green に騙された** (rm .olean + tail で真の error 確認必須)。
  ### 残 = strict_config 本体の組立のみ (sub-lemma 出揃った)
  - M* 抽出: S13_PrimeAction:333-347 mirror (R≠⊥, E≤N_G(R)=`E_le_normalizer_of_le_E3`, coatom)。
  - step c: `actsPrimeOn_inf_centralizer_eq_bot` (H1) で C_{E₁}(M_σ⊓M*)=⊥
    ([C_{M_σ}(R),P]≠⊥ ← strict; ⊆[M_σ⊓M*,E₁])。
  - step d: `tau13_pSubgroup_centralizes .2.1` (Cor 13.2b) → π(E₁)⊆τ₁M*。
  - step e: `.2.2` (Cor 13.2c) → r∈σ(M*); `sigma_subgroup_le_Msigma_of_isHall` → R⊆M*_σ。
  - step f: **`E1_centralizes_R_of_hall_tau1`** で E₁ が R 中心化。✅
  - step g: `E_eq_sup_of_E3_centralizer` (5a, E=E₁⊔E₃) + E₁,E₃ が R 中心化 → R⊆C_G(E) →
    `subgroupE_basic` の C_G(E)⊓E₃=⊥ + R≠⊥ で False。
  これらを strict_config の `by` に組めば 13.7 完全完成。次イテレーションの標的。
