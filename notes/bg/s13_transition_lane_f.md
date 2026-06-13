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

## 進捗

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
