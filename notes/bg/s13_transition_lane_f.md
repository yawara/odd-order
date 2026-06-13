# BG §13 後半 (Lemma 13.7–13.13) — Lane F 作業ノート

> 正本ファイル = `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeActionTransition.lean` (Lane F 所有)。
> 上流 `S13_PrimeAction.lean` (定義 + 13.1–13.6) は **Lane G 領域、cite のみ**。
> mmd `references/bg/local-analysis.mmd` L3596–3780 / PDF book pp.100–104 (**PDF page = book page + 13**)。

## 着手順 (13.6 非依存を先に)

- **13.7 `E1E3_actsPrime`** — 13.6 非依存。**現フロンティア**。
- **13.8 `forbidden_config_impossible`** — 13.6 非依存。13.7 の次。
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

## 進捗

- 2026-06-14 (Lane F, /loop): main ff-merge で hub の split (`S13_PrimeActionTransition.lean`) 取込。
  式番号 (13.2)(13.3)(13.4) を PDF で確定。step 5c helper
  `actsPrimeOn_inf_centralizer_eq_bot` を landed (✅ sorry-free)。次 = 13.7 step 4 同値補題 →
  step 1/5 配線 → 13.7 完成 → 13.8。
