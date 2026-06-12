# BG §13: Prime Action — per-section 調査ノート

## 2026-06-12 Lane G session 1: STATEMENT AUDIT — 🛑 BLOCKER (issue 8000)

**結論: §13 は現状の §12 surface では着工不能。根の Lemma 13.1 が BG Cor 12.16(a)(b) を要し、
その statement が repo に存在しない。** LAUNCH.md 手順 3 (着工前必須 audit) の所見。

### 環境
- `git merge --ff-only main` 成功 (`aa5231be`→`f1408227`; S10 分割 4 ファイル取り込み)。
- `lake build …S13_PrimeAction` 緑 (3067 jobs, scaffold 実 sorry 11)。
- mmd 実行番号は notes 旧記載とズレ: §13 = **L3526-3739** (Lem 13.1 = L3528, notes 旧 L3498 は古い抽出)。
  §12 cited: Thm 12.13=L3377, Cor 12.14=L3399, Prop 12.15=L3417, Cor 12.16=L3453, Lem 12.17=L3478,
  Lem 12.18=L3484, Lem 12.19=L3510。

### audit 結果 (4 指定 statement + 周辺)
| BG | Lean (S12) | faithful? | 備考 |
|---|---|---|---|
| Thm 12.13 | `nonabelian_pgroup_isUniquelyMaximal` (S12_E:49) | ✅ | 完全一致 |
| Cor 12.14 | `maximalContaining_centralizer_eq_singleton` (S12_E:57) | ⚠ 不完全 | `ℳ(C_G(X))={M}` のみ。原典 `ℳ(P)={M}` (P=Sylow p of M_σ) を**脱落**。Lemma 13.6 が `ℳ(S)` に要する → 13.6 着工時に要対応 |
| Prop 12.15 | `sigma_subgroup_maximal_interaction` (S12_E:458) | ✅ | (a)-(e) 全 faithful。`complement` は `M*_σ⊓(M⊓M*)=⊥ ∧ ⊔=M*` |
| **Cor 12.16(a)(b)** | **存在しない** | 🛑 | `sigma_subgroup_conj_into_Msigma` (S12_E:64) は docstring が「12.16(a)」だが**実体は前置節「Y conj into M_σ」のみ**。rank bound `r_p(N_H(Y))≤1` (a) と π-bound `p∈τ₁⟹p∉π(N_H(Y)')` (b) **未述**。S12_E:29 も「12.16(b) deferred」と自認 |

### なぜ全 §13 が gate されるか
- §13 は **Lemma 13.1 を根とする DAG**: Cor 13.2 は「follows directly from Lemma 13.1」(mmd L3554)、
  以降 13.3/13.4/…/13.11 は全て 13.2 か 13.4 経由。独立に着工できる §13 結果は無い。
- Lemma 13.1 (3 結論) の証明は **3 つとも Cor 12.16(a) を要する**:
  - (b) `p∉τ₂(M*)`: `r_p(N_{M*}(Y))=2` (12.1(g)) vs `≤1` (12.16(a)) の矛盾 (mmd L3538)。
  - (c) `p∈τ₁(M)⟹p∈β(G)`: 12.16(b) の対偶 (mmd L3540)。
  - (a) centralization: `p∈σ(M*)∪τ₃(M*)` (= (b) で τ₂ 除外) 経由で Sylow `S⊆M*'` を取るので (b) 依存。

### 在庫 OK な §12/§10 依存 (cite 可)
12.1(d) E₁/E₃ cyclic (S12_ECore:835,910) ✅ / 12.1(g) `isMaximalElementaryAbelian_of_mem_tau2`
(S12_ECore:490; ただし `¬idealPrime`=「p∉β(G)」部分のみ直接, 「r_p(N_{M*}(Y))=2」は別途要導出) /
12.2(a) (S12_ECore:1218) ✅ / 12.5 (S12_Theorem125:94) ✅ / 12.6(a)(b)(c) (S12_Corollary126) ✅ /
12.13/12.15/12.18(a) (S12_Lemma1218) ✅ / 12.17 (S12_E:74, **実証明済**) ✅ /
10.8 (S10_BetaRadicalCore) ✅ / 10.12(a) `disjoint_of_not_conj` (S10_LocalLemmasCore:1200) ✅。
未再確認 (13.6/13.7/13.9 着工時に): 12.5(d), 12.6(d), 12.6(f)。

### 解消パス (要 hub/ユーザー裁可 — session 1 末で提示)
1. **(推奨) hub/Lane F が S12_E へ Cor 12.16(a)(b) の sorry'd statement を追加** → G が cite。
   architecture 最善 (statement は §12 に属す)。issue 8000 に drop-in 署名あり。G は短時間待機。
2. ユーザー承認のもと G が §13 helper で 12.16(a)(b) を **forward axiom** 宣言 → 即着工、後で de-axiom。
3. G が 12.16(a)(b) を §13 側で **実証明** (sorry 無し, sorry'd Prop 12.15 引用) → idle/axiom 無しだが
   §12 仕事を G レーンで抱える + 合流時 relocate (~150-250 行, 非推奨)。

→ 詳細・署名は **issue 8000** (`issues/8000-s13-blocked-cor1216ab.md`)。

### session 1 進捗 (forward axiom path 採択後)

- **forward axiom インフラ確立** (commit `c8080f87`): 新 leaf `S13_Lemma131.lean` に
  `cor1216_pRank_normalizer_le_one` (a) / `cor1216_not_mem_primeFactors_derived_of_tau1` (b)
  を provisional axiom 宣言、root 配線、full build 3792 緑。
- **Lemma 13.1 step 1 着地** (sorry-free): `Msigma_commutator_M_le` (`⁅M_σ,M⁆≤M_σ`, 再利用可) +
  `exists_sigma_prime_dvd_derived_Mstar` (mmd L3534: `⁅M_σ∩M*,M∩M*⁆≠1` ⟹ `∃q∈σ(M)∩π(M*')`)。

### Lemma 13.1 残 step plan (mmd L3534-3546; scaffold `pSubgroup_centralizes_of_interaction` は
S13_PrimeAction に sorry'd で残置、全 step 着地で migrate)

- **step 2 (Frattini) ✅ COMPLETE (2026-06-12 session 1, commit `a93636c5`)**:
  `exists_sylow_frattini_decomp` (sorry-free) = `q∉β(M*) ∧ q∣|M*'| ⟹ ∃ Y, Y≠⊥ ∧ IsPGroup q Y ∧
  Y≤M*' ∧ Mstar = O_{β(M*)∪{q}}(M*') ⊔ (Mstar ⊓ N_G(Y))`。核 `M*_β Q ◁ D` =
  `S10.normal_sup_sylow_of_quotient_nilpotent` (D/M*_β nilpotent) → O_{β∪q}(D) に押込 (char in D⊴M*
  ⟹ K⊴M*)、Frattini = `Sylow.ofCard`+`Sylow.normalizer_sup_eq_top`+subtype transport (S10 Cor 10.9
  機構縮約)。~100 行・4 build iteration で着地。helper `Mbeta_le_derived` も land。
  🔑 **M*_β でなく K=O_{β∪q}(M*') を使うのが鍵** (K は M*' に characteristic ⟹ K⊴M* が無料)。
- **step 3 = (b) `p∉τ₂(M*)` ✅ COMPLETE (2026-06-12 session 2, axiom 初使用)**:
  `not_mem_tau2_of_interaction` (sorry-free; `#print axioms` = `[propext, Classical.choice,
  Quot.sound, cor1216_pRank_normalizer_le_one]` — forward axiom のみ, sorryAx 無し)。
  p∈τ₂(M*) 仮定→矛盾。実装の要:
  - q∉β(M*): `(S10.disjoint_of_not_conj hG hMstar h.mem_maximal hnc').1.2`
    (= `alpha Mstar ∩ sigma M = ∅`, hnc' = conjugacy 対称化を inline 2 行) + β⊆α。
  - **r_p(N_{M*}(Y))=2 は τ₂ witness 不要**: 直接 `tau2_pRank_eq_two hpτ2` (=pRank M*=2) を
    新 helper `pRank_le_of_factorization_card_eq` (N≤H ∧ v_p|H|=v_p|N| ⟹ pRank H≤pRank N;
    N の Sylow p を `Sylow.ofCard` で H の Sylow p と同定 → `pRank_sylow_eq`) で N へ transfer。
    v_p|M*|=v_p|N| は積公式を **↥M* 内**で (`card_HK_mul_card_inf_eq_card_mul_card` +
    `Subgroup.normal_mul` (KM⊴⟹↑KM·↑NM=↑(KM⊔NM)) + `SetLike.coe_sort_coe`+`Subgroup.card_top`,
    subgroupOf cards は `subgroupOfEquivOfLe`) → `|M*|·|K⊓N|=|K|·|N|`, 両辺 factorization_p:
    v_p|K|=v_p|K⊓N|=0 (`p∤|K|`) ⟹ v_p|M*|=v_p|N|。p∤|K| = K {β∪q}-group ∧ p∉β(M*)
    (τ₂⟹p∉σ⊇β) ∧ p≠q (`h.not_mem_sigma_of_mem_primeFactors` で p∉σ(M), q∈σ(M))。
  - **r_p(N_{M*}(Y))≤1**: `cor1216_pRank_normalizer_le_one hG h hYne hYpi hpE hpβG hHY hnc`。
    hpβG=`(isMaximalElementaryAbelian_of_mem_tau2 ... hpτ2 hAM hA).2` (witness A は
    `exists_mem_elemAbelianOfRank_two_le_of_tau2`, S12_Lemma1211 を新規 import)。
    hYpi: Y は q-group + q∈σ(M)。hHY: `mem_maximalSubgroupsContaining.mpr ⟨IsCoatom, Y≤M*⟩`。
    `rw [← hNdef] at hle1` で N に fold して omega。
  - 🔑 **import 知見**: S12_E の closure は S12_ECore のみ (S12_E は branch-A leaf)。proven §12
    結果は別 leaf: `exists_mem_elemAbelianOfRank_two_le_of_tau2`=S12_Lemma1211 (branch B, 要 import),
    `not_conj_symm`=S12_ExceptionalBridge (branch A, inline で回避),
    `not_mem_sigma_of_mem_primeFactors`=S12_ECore の **`SubgroupESetup` namespace 内**
    (dot 記法 `h.not_mem_sigma_of_mem_primeFactors hG hpE`)。§13 後続も同様に leaf を選んで import。
  - 🔑 **新 helper 2 個** (axiom-clean, 再利用可, S13_Lemma131 冒頭): `pRank_eq_of_mulEquiv`
    (≃* 不変), `pRank_le_of_factorization_card_eq` (上記)。step 4/5 でも使える見込み。
  - **AxiomsCheck island assert は step 6 (assembly) で**: 現状 AxiomsCheck は S13_Lemma131 を
    import せず (per-name `#assert_only_allowed_axioms` のみ) ⟹ full build 緑・gate pass。
- **step 4 = (c) `p∈τ₁(M)⟹p∈β(G)` ✅ COMPLETE (2026-06-12 session 2)**:
  `mem_idealPrime_of_tau1_of_interaction` (sorry-free; `#print axioms` = forward axiom
  `cor1216_not_mem_primeFactors_derived_of_tau1` のみ + 標準, sorryAx 無し)。
  🔑 **当初の心配 (Burnside Sylow⊆M*') は不要だった** — injection 論法は `p∈π(M*')` (full
  Sylow でなく p∣|M*'|) だけでよい。再利用 helper 4 個 (全 axiom-clean):
  - `derivedInG_le_sup_of_normal` (M*=K⊔N, K⊴M* ⟹ M*'≤K⊔N'; ↥M* 内 quotient `φ=mk' KM` で
    `map φ commutator(↥M*)=map φ ⁅NM,NM⁆` → `comap_map_eq` → 下降 `map_subtype_commutator`)。
  - `card_normal_sup_mul_card_inf` ((b) の積公式を一般 sup へ; |K⊔L|·|K⊓L|=|K|·|L|)。
  - `mem_primeFactors_derived_of_not_tau1_tau2` (`p∈π(M*)∖τ₁∖τ₂ ⟹ p∈π(M*')`: σ は
    Sylow⊆M_σ⊆M*' [`sigma_subgroup_le_Msigma_of_isHall`+`Msigma_le_derived`]、p∉σ は rank≤2
    [`mem_alpha_iff`]∧≠2[τ₂]⟹=1∧p∉τ₁⟹p∈π(M*'); `one_le_pRank_of_mem_primeFactors` で rank≥1)。
  - `pRank_eq_of_mulEquiv` / `pRank_le_of_factorization_card_eq` (step 3 由来)。
  証明: by_contra ¬idealPrime → p∉β(M*) (β⟹idealPrime) → setup 再利用 (p∤|K|) →
  hpMstarDeriv (p∈π M*') → hpNderiv (p∈π N': M*'≤K⊔N', |M*'|∣|K|·|N'|, p∤|K| で Euclid) →
  axiom `cor1216(b)` の `p∉π(N')` と矛盾。⚠ setup ~30 行が (b) と重複 (将来 factor 候補)。
- **step 5 = (a) centralization (NEXT; forward axiom 不要・純 structural ~80 行; 精査 session 2)**:
  goal = `∀ P ≤ M⊓M*, IsPGroup p P → P ≤ C_G(M_σ∩M*)`。論法 (mmd L3542):
  `P⊆K_a` (K_a=O_{α(M*)∪{p}}(M*') ⊴ M*, σ(M)'-group) → `[M_σ∩M*,P]⊆M_σ⊓K_a=⊥`。詳細:
  1. **K_a⊴M***: char in M*'⊴M* (step 2 の hKnorm と同型: `le_normalizer_opiCoreInG_of_le_normalizer`
     + `S10.le_normalizer_derivedInG`)。
  2. **P⊆K_a**: ⚠ **要 `P⊆M*'`** (K_a⊆M*' ゆえ P⊆K_a⟹P⊆M*')。これが (c) と違い **full Sylow⊆M*'
     を要する** (cardinality でなく subgroup 包含)。**σ(M*)**: Sylow p⊆M_σ⊆M*'
     (mem_primeFactors_derived の σ-branch を subgroup 版に流用)。**🛑 τ₃(M*)**: Sylow p of M* =
     Sylow p of E* (p∉σ) ⊆ E*'⊆M*' — template = **private `sylow_le_derived_of_mem_tau3`
     (S12_ECore:548, E 専用, Burnside 論法 ~40 行)**。**de-private (S12_ECore=Lane F 域→hub 依頼)
     か S13 で再証明が必要 — これが (a) の唯一の hard 依存**。P⊆M*' 後: M*'/M*_α nilpotent
     (`derivedQuotientMbeta_isNilpotent` + `nilpotent_of_surjective`(`QuotientGroup.map id`, Mβ⊆Mα)
     で導出可、確認済) ⟹ M*_α·(Sylow p) ⊴ M*' (`normal_sup_sylow_of_quotient_nilpotent`) ⊆ K_a、
     K_a は Sylow p を含む normal ⟹ 全 p-subgroup を含む ⟹ P⊆K_a。
  3. **M_σ⊓K_a=⊥**: coprime (`Subgroup.inf_eq_bot_of_coprime`; |M_σ| σ-num, |K_a| {α∪p}⊆σ'-num
     [α(M*)∩σ(M)=∅ via `S10.disjoint_of_not_conj` 10.12(a) swapped, p∉σ(M) via
     `h.not_mem_sigma_of_mem_primeFactors`])。
  4. **[M_σ∩M*,P]⊆M_σ⊓K_a**: ⊆M_σ (`Msigma_commutator_M_le` 流用) ∧ ⊆K_a (P⊆K_a⊴M*,
     M_σ∩M*⊆M*, `commutator_le_left`/`commutator_mono`) ⟹ =⊥ ⟹ `commutator_eq_bot_iff_le_centralizer`。
  🔑 **(a) 着工の判断点**: τ₃ の Sylow⊆M*' (Burnside) が de-private/再証明を要する ⟹ hub に
  `sylow_le_derived_of_mem_tau3` の de-private (public 化, S12_ECore) を依頼するのが最善
  (issue 起票 base 8000)。または S13 で Burnside transfer 再証明。
- **step 6 = assembly**: (a)(b)(c) を束ねて `pSubgroup_centralizes_of_interaction`
  (S13_PrimeAction scaffold) を S13_Lemma131 で証明 → scaffold migrate (削除)。
  hyp: (a)=`not_mem_tau2_of_interaction` の派生不要、(b)=`not_mem_tau2_of_interaction`、
  (c)=`mem_idealPrime_of_tau1_of_interaction` (要 hpMstar, hpτ1Mstar, hpτ2Mstar[=(b)])。
  完了後 **AxiomsCheck に island assert** (`#assert_axioms_island pSubgroup_centralizes_of_interaction
  expecting [cor1216_pRank_normalizer_le_one, cor1216_not_mem_primeFactors_derived_of_tau1]`) +
  S13_Lemma131 を AxiomsCheck import に追加 (full build)。

surface map (Explore 2026-06-12): `commutator_mono`/`commutator_le_left` (mathlib),
`S10.Msigma_isPiGroup`/`Msigma_le_derived`, `Sylow.normalizer_sup_eq_top'`, `pRank_mono_of_le`,
`isHall_Mbeta` (full bundle: Hall + nilpotent quotient + normal p-complement),
`tau2 M={p∉σ ∧ pRank=2}`/`tau2_pRank_eq_two`, `S10.disjoint_of_not_conj` (10.12)。

---

## 2026-06-02 B7 foundation checkpoint

Lean file: `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean`.

Concrete surfaces now present:
- Definitions: `fixedBy` (`C_N(X)`), `fixedByElement` (`C_N(g)`), `ActsPrimeOn`, and `ActsRegularlyOn`.
- Basic API: definitional rewrites for the centralizer predicates, `fixedBy_le_fixedByElement`, `ActsRegularlyOn.toActsPrimeOn`, monotonicity in the acted-on subgroup for both regular and prime action, and bottom-subgroup constructors.

Current Lean inventory: 11 theorem-level `sorry`s remain in §13. The two action predicates and their basic API are sorry-free.

Main proof blockers: BG Lemma 10.8, Corollary 12.16(a), Lemma 12.18/12.19, §10 beta-complement/normalizer gates, and the remaining §12 tau/E structural results. These remain explicit theorem dependencies rather than fields on `ActsPrimeOn`.

**スコープ**: BG §13 (pp.97-104 in PDF), mmd L3484-3739, **7 主要結果**.
**形式化先 (予定)**: `OddOrder/BG/Ch3_MaximalSubgroups/S13_PrimeAction.lean`
**ROADMAP 上の位置**: Phase 2a 第 4 波 (§12 完成必須)
**役割**: prime action 構造定理. E の derived series に基づく Thompson 風の作用理論. §14 (Type 𝒫 Counting) と §15 (M_F structure) への橋渡し.
**難度**: ★★★★☆ (§12 より軽いが，Thompson 作用による高度な局所制御が必要)

---

## TL;DR: Prime Action = 素数別作用制御の精密構造

§13 は **maximal subgroup M 内で，complement E が M_σ に対して特定素数 p に対してのみ作用する** という prime action の概念を導入・確立. 

**核心結果**:
1. **Lemma 13.1**: 異なるmaximal M* との prime 相互作用 → p-centralizer の制御
2. **Corollary 13.3**: cyclic Sylow, E₃ は prime action (定義確認)
3. **Theorem 13.4**: τ₁(M) の element と他素数 element との derived series 制御 (most intricate)
4. **Theorem 13.5**: E₁ は prime action (cyclic Sylow consequence)
5. **Lemma 13.6**: E₁ の作用下での M_σ の maximal family 一意性
6. **Lemma 13.7**: E₁E₃ 同時作用の prime 性 (conditional)
7. **Lemma 13.8–13.10**: 相互作用制約と §14 への transition

形式化では **800-1200 行** Lean 予想（proof density は §12 より低い）.

---

## §13 全 7 結果（精密リスト）

| # | 名前 | 型 | 行範囲 | 概要 | 証明長 | 依存 |
|----|------|-----|--------|------|--------|------|
| 1 | **Lemma 13.1** | Lemma | 3498-3516 | 異 maximal M* との p 相互作用 → p-centralization | 19行 | §12 (Cor12.16), §10 (Thm10.2) |
| 2 | **Corollary 13.2** | Corollary | 3518-3524 | τ₁∪τ₃ の element: p-centralizer, τ₁' 作用 | 7行 | Lemma 13.1 |
| 3 | **Corollary 13.3** | Corollary | 3526-3534 | cyclic Sylow p-subgroup & E₃ は prime on M_σ | 9行 | Cor 13.2 |
| 4 | **Theorem 13.4** | Theorem | 3536-3568 | **τ₁ element P & other R: C_{M_σ}(P) ⊆ C_{M_σ}(R)** | 33行 | Cor 13.2, §12 (Lemma 12.18) |
| 5 | **Theorem 13.5** | Theorem | 3570-3572 | E₁ は prime on M_σ | 3行 | Cor 13.3, Thm 13.4 |
| 6 | **Lemma 13.6** | Lemma | 3574-3595 | E₁ 作用下 M_σ Sylow の maximal family 一意性 | 22行 | Thm 13.5, §12 (Cor 12.6, Lemma 12.17), Thm 13.4 |
| 7 | **Lemma 13.7** | Lemma | 3596-3628 | E₁E₃ 同時作用が prime (E₁ が E₃ を非正則作用でない場合) | 33行 | Thm 13.5, Cor 13.3, Thm 13.4, Lemma 13.6, Cor 12.6 |
| * | **Lemma 13.8–13.10** | Auxiliary | 3630-3695 | 相互maximal の禁止configuration + Theorem 13.10 (Conclusion) | 66行計 | Lemma 13.6, 13.8, §12全般 |

**計**: 主結果 7 個, 補助 3 個 (Lemma 13.8, 13.9 = Thm実質, Cor 13.11 etc.)
**合計 mmd**: 256 行 (§12 の 460 行より compact)
**主要証明**: Thm 13.4 (33行, Thompson 風)，Lemma 13.7 (33行, mutual action), Lemma 13.8 (32行, contradiction)

---

## Prime Action の定義と由来

### 素数 p ∈ σ(M) に対する prime action

X ⊆ G (nonidentity p-subgroup, p 素数) が **M_σ に対して prime に作用する** ⟺

**定義1 (original)**:
$$C_{M_\sigma}(g) = C_{M_\sigma}(X) \text{ for all } g \in X^\#$$

**定義2 (elementary part版)**:
$$C_{M_\sigma}(P) \subseteq C_{M_\sigma}(X) \text{ for all } P \in \mathcal{E}^1(X)$$

**補注**: この定義は **1 つの素数 p のみに relative**. X が multiple primes を contain すれば，その product への "prime" status は定義されず，むしろ **各素因子ごとに separately** prime か否かを判定.

### Regular action との対比

- **regular**: C_{M_σ}(g) = 1 for all g ∈ X^# (最も制限的)
- **prime**: C_{M_σ}(g) = C_{M_σ}(X) for all g ∈ X^# (中程度制限)
- **general**: no constraint

§13 の主戦場は **regular と prime の中間** に落ちる coprime-action scenarios.

---

## 7 結果の構造と証明梗概

### Group I: 初等的 prime action (結果 1-5, Lemma 13.1 – Theorem 13.5)

#### **Lemma 13.1** (L3498-3516)

**主張**:
- M* ∈ ℳ, p ∈ π(E) ∩ π(M*), p ∉ τ₁(M*), [M_σ ∩ M*, M ∩ M*] ≠ 1, M* ≄ M に対して:
  1. Every p-subgroup of M ∩ M* centralizes M_σ ∩ M*
  2. p ∉ τ₂(M*)
  3. (if p ∈ τ₁(M)) then p ∈ β(G)

**数学的意味**:
- 異なるmaximal M, M* 間の p-相互作用で，**p-subgroup は M* 側を stabilize するのに十分に大きい** ことが imply される.
- この補題は "maximal family の disjointness" 方向への第一歩で，§12 の Proposition 12.15 (σ(M) disjointness) を踏台にして，**complement E の側面** から p の exclusivity を示す.

**証明スケッチ** (L3505-3516):
1. [M_σ ∩ M*, M ∩ M*] ≠ 1 から，∃q ∈ σ(M) ∩ π(M*').
2. Y = Sylow q-subgroup of M*'. Lemma 10.8 (M_β' structure) + Frattini で M* = N_{M*}(Y)M_β.
3. If p ∈ τ₂(M*): then r_p(N_{M*}(Y)) = 2 (Lemma 12.1(g)) ⟹ p ∉ β(G) (Cor 12.16(a) contradiction) ⟹ p ∉ τ₂(M*).
4. p ∈ σ(M*) ∪ τ₃(M*) なので，M* の Sylow p ⊆ M*'. P を M ∩ M* の p-subgroup とすると，P ⊆ M*_α S (S = Sylow p of M*).
5. M*_α S は σ(M)'-group ⟹ [M_σ ∩ M*, P] = 1.

**キーテクニック**: Frattini argument + lemma 10.8 (β-radical nilpotency) の合成.

**形式化見積**: 80-120 行.

---

#### **Corollary 13.2** (L3518-3524)

**主張**:
- p ∈ τ₁(M) ∪ τ₃(M), P = nonidentity p-subgroup of M, M* ∈ ℳ(N_G(P)) に対して:
  1. Every p-subgroup of M ∩ M* centralizes M_σ ∩ M*
  2. Every τ₁(M*)'-subgroup of E ∩ M* centralizes M_σ ∩ M*
  3. (if [M_σ ∩ M*, M ∩ M*] ≠ 1) then p ∈ σ(M*), and (if p ∈ τ₁(M)) p ∈ β(M*)

**証明**: Lemma 13.1 を p ∈ τ₁(M) ∪ τ₃(M) の場合に apply. Lemma 12.2(a) で p ∈ σ(M*) ∪ τ₂(M*) を ensure.

**役割**: Lemma 13.1 の **τ₁(M), τ₃(M) specialization**. 以下の Corollary 13.3 の土台.

**形式化見積**: 40-60 行.

---

#### **Corollary 13.3** (L3526-3534)

**主張**:
1. Every nontrivial cyclic Sylow p-subgroup of E acts **prime** on M_σ.
2. The group E₃ acts **prime** on M_σ.

**数学的意味**: 
- E₁ は cyclic (Lemma 12.1(d)), τ₁(M) に属す → Corollary 13.3(a) で cyclic Sylow は prime.
- E₃ は cyclic normal (Lemma 12.1(d)), τ₃(M) に属す → Corollary 13.3(b) で prime.
- **これが Theorem 13.5 (E₁ is prime) の first step**.

**証明** (L3530-3534):
1. (a): P = cyclic Sylow p of E, p ∈ τ₁(M) ∪ τ₃(M). Take M* ∈ ℳ(N_G(P)).
   - Cor 13.2(a): Every p-subgroup of N_E(P) centralizes C_{M_σ}(P) ⟹ P prime on M_σ.
2. (b): E₃ cyclic normal in E, Lemma 12.1(d) ⟹ E₃ ⊆ E'. So E ⊆ N_G(Q) (Q Sylow 3 of E₃), E₃ ⊆ E' ⊆ M*.
   - Cor 13.2(b) で E₃ 는 centralizer.

**形式化見積**: 50-70 行.

---

#### **Theorem 13.4** (L3536-3568) — Main Theorem

**主張** (L3538):
- p ∈ τ₁(M), P ∈ ℰ_p¹(E), r ∈ π(E), R ∈ ℰ_r¹(C_E(P)) に対して:
$$C_{M_\sigma}(P) \subseteq C_{M_\sigma}(R)$$

**数学的意味**:
- τ₁(M) の element P と，それを centralize する他素数 element R の interaction.
- **Derived series との緊密な coupling**: τ₁(M) は p ∉ π(M'), rank 1 → rank small.
- R が C_E(P) 内の元素的 r-subgroup なら，R の M_σ への作用は P より「弱い」.
- これは **Thompson の作用論** の中核: "小さい element が大きい element の centralizer に dominant".

**証明** (L3540-3568, 28 行):

1. **仮定**: [S, R] ≠ 1 (where S = PR-inv Sylow q-subgroup of C_{M_σ}(P), q ∈ σ(M)).
   
2. **Step 1** (L3544-3550): Take M* ∈ ℳ(N_G(P)).
   - [S, R] ⊆ [M_σ ∩ M*, R] (by construction).
   - Cor 13.2 ⟹ p ∈ β(M*), r ∈ τ₁(M*).

3. **Step 2** (L3552-3556): 
   - S = C_S(R) × Q (Q = [S, R], S abelian by Thm 12.13).
   - Lemma 12.18(a) (with r, R, M* in place of p, P, M) ⟹ ℳ(N_G(Q)) = {M*}.
   - Cannot have Prop 12.15(e) because P ⊆ M ∩ M*_σ ⟹ q ∈ σ(M*).
   - Prop 12.15(d) ⟹ M_α ≠ 1, r ∈ π(E) ∩ τ₁(M*) ⊆ τ₁(M).

4. **Step 3** (L3558-3567):
   - From [S, R] ≠ 1 and Lemma 12.18: C_{M_α}(P) ⊆ C_{M_α}(R) and C_{M_α}(R) ⊆ C_{M_α}(P).
   - So C_{M_α}(P) = C_{M_α}(R).
   - But ℳ(N_G(Q)) ≠ {M} ⟹ Lemma 12.18(a) yields C_{M_α}(R) ≠ C_{M_α}(RQ).
   - **Contradiction** ⟹ [S, R] = 1 ⟹ R centralizes S ⟹ C_{M_σ}(P) ⊆ C_{M_σ}(R).

**キーテクニック**: 
- **Maximal family の一意性 (Lemma 12.18)** と **derived series の abelian structure (Thm 12.13)** の合成.
- Proposion 12.15 の case analysis (5 cases: (a)-(e)) で，4 cases を eliminate し，1 case (d) に絞る.
- **最後の矛盾**: C_{M_α}(RQ) の identity vs. non-identity の対比.

**数学的インサイト**: 
- Theorem 13.4 は「τ₁ element P のみ作用を制限すれば，他素数 R の作用は P に dominated される」という **prime action の証明の心臓部**. 
- これは Thompson 1966 論文の "fixed point theorem" の local incarnation.

**形式化見積**: 200-300 行 (proof が multi-case).

---

#### **Theorem 13.5** (L3570-3572)

**主張**: E₁ ≠ 1 ⟹ E₁ acts prime on M_σ.

**証明** (L3572, 1 行!): 
- E₁ cyclic (Lemma 12.1(d)) ⟹ Cor 13.3(a) + Thm 13.4 で E₁ prime.

**簡潔性の理由**: Corollary 13.3 + Theorem 13.4 が all work; no additional case analysis needed.

**形式化見積**: 20-30 行.

---

### Group II: Prime Action の extended analysis (結果 6-7, Lemma 13.6–13.7)

#### **Lemma 13.6** (L3574-3595) — Maximal Uniqueness

**主張** (L3574-3576):
- 1 ⊂ P ⊆ E₁, q ∈ σ(M), X ∈ ℰ_q¹(C_{M_σ}(P)), S = Sylow q-subgroup of M_σ に対して:
$$\mathscr{M}(C_G(X)) = \mathscr{M}(S) = \{M\}$$

**数学的意味**:
- E₁ の nontrivial subgroup P に対して，C_{M_σ}(P) の元素的 q-part は **G 全体において M にのみ maximal に contain される**.
- **M の一意性の再確認**: E₁ acting via derived series → maximal family の整合性.

**証明** (L3578-3594, 17 行):

1. **仮定の簡略化** (L3578-3582):
   - Cor 12.14 ⟹ q ∉ β(M), X ⊄ M_σ' と仮定可（否，M(C_G(X)) = {M} 自動).
   - Thm 13.5 ⟹ C_{M_σ}(P) = C_{M_σ}(E₁) (P ⊆ E₁ なので).

2. **Hall structure** (L3584-3586):
   - Thm 12.13: q ∉ β(M) ⟹ E' centralizes some Sylow q of M_σ.
   - Prop 1.5 (A-invariant Hall): E normalizes S, assume X ⊆ S ⊆ C_{M_σ}(E').

3. **E₂ ≠ 1 確認** (L3588):
   - Lemma 12.17 ⟹ C_{M_σ}(E) ⊆ M_σ'.
   - X ⊄ C_{M_σ}(E) ⟹ E₁E' ≠ E ⟹ E₂ ≠ 1 (E = E₁E₂E₃).

4. **τ₂ case の推論** (L3590-3594):
   - Take p ∈ τ₂(M), Q ∈ ℰ_p²(E).
   - A = Q ⊲ E (Cor 12.6(a)), C_{M_σ}(A) = 1 (Thm 12.5(d)).
   - Thm 13.4: A₀ = C_A(E₁) ⊆ A centralizes X (by 13.4).
   - A = A₀ × [A, E₁] ⟹ A centralizes X, contradiction to C_{M_σ}(A) = 1.

**キーテクニック**: 
- **Thm 12.5(d)** (τ₂ case で C_{M_σ}(A) = 1) と **Thm 13.4** (C_{M_σ}(P) ⊆ C_{M_σ}(A)) の矛盾から，maximal family を force.

**形式化見積**: 120-150 行.

---

#### **Lemma 13.7** (L3596-3628) — Simultaneous E₁E₃ Action

**主張** (L3596):
- E₁ ≠ 1, E₁ does not act regularly on E₃ に対して:
$$E_1 E_3 \text{ acts prime on } M_\sigma$$

**数学的意味**:
- E₁ と E₃ は coprime order (τ₁ ⊥ τ₃), 両者ともcyclic, normal relations あり.
- "E₁ が E₃ に**非正則** (not regularly)" = ∃ P ∈ ℰ_p¹(E₁), R ∈ ℰ_r¹(E₃) with P centralizes R.
- ⟹ E₁E₃ (their product) は prime on M_σ.
- **物理的意味**: 2 つの cyclic-coprime actions が "anti-regular" なら，product も prime 性を保つ.

**証明** (L3598-3628, 31 行):

1. **Initial reduction** (L3598-3604):
   - P ∈ ℰ_p¹(E₁) centralizes R ∈ ℰ_r¹(E₃) (non-regular assumption).
   - Thm 13.4: C_{M_σ}(P) ⊆ C_{M_σ}(R).
   - Thm 13.5, Cor 13.3(b): E₁, E₃ prime on M_σ, coprime order.
   - If C_{M_σ}(P) = C_{M_σ}(R) ⟹ E₁E₃ prime (by abelian formula on coprime actions).

2. **Main case: C_{M_σ}(P) ⊂ C_{M_σ}(R)** (L3608-3628):
   - Assume strict inequality (otherwise done).

3. **Step 1** (L3614-3616):
   - C_{M_σ}(R) ≠ 1 ⟹ Cor 12.6(d): τ₂(M) = ∅.
   - So E = E₁E₃ (no E₂).

4. **Step 2** (L3618-3627):
   - R ⊲ E (E₃ normal cyclic), take M* ∈ ℳ(N_G(R)).
   - E ⊆ M*, E₃ ⊆ M* ⟹ 1 ⊂ P ⊆ C_{E₁}(M_σ ∩ M*) (from L3620).
   - By Cor 13.2(b): E₁ ⊆ Hall τ₁(M*), apply Thm 13.5 to M*: E₁* prime on M*_σ.
   - Thus E₁* centralizes R.

5. **Step 3** (L3622-3628):
   - So E₁ centralizes R ⟹ R ⊆ Z(E) (by properties of E₃, Lemma 12.1(d)).
   - But Lemma 12.1(d): C_{E₃}(E) = 1 ⟹ **contradiction**.

**キーテクニック**: 
- **Thm 13.5 の iteration** (M* で apply) + **Lemma 12.1 の normalization**: E₃ ⊲ E, but Z(E₃) small.
- **Maximal family の uniqueness (Lemma 13.6)** を暗黙的に使用 (M* ∈ ℳ(N_G(R)) の selection).

**数学的インサイト**: 
- Lemma 13.7 は "prime action は 2 つ-coprime factors の product で preserve される" というabelian factorization 的な stability. これが §14 での "type P maximal の全体 family" の consistency を guarantee.

**形式化見積**: 200-250 行.

---

### Group III: 相互制約と Transition (補助 Lemma 13.8–13.10)

#### **Lemma 13.8** (L3630-3660) — Forbidden Configuration

**主張** (L3630-3636):
**不可能な configuration** の 5 条件:
1. M* ∈ ℳ, M* ≄ M
2. p ∈ τ₁(M) ∩ τ₁(M*), P ∈ ℰ_p¹(M ∩ M*)
3. Q, Q* = P-invariant Sylow subgroups (possibly distinct primes)
4. C_Q(P) = 1, C_{Q*}(P) = 1
5. N_G(Q) ⊆ M*, N_G(Q*) ⊆ M

⟹ **Contradiction** (no such config exists).

**数学的意味**:
- τ₁ element P が 2 つの異なる Sylow に対して "regular に作用" すれば，その両者の normalizers が定義上異なるmaximal に belong → contradiction.
- **Maximal の一意性の deeper incarnation**: Proposition 12.15 等での σ disjointness に続く強化版.

**証明** (L3638-3660, 23 行):
- Assume config exists. By (3)-(5), Q = nonidentity Sylow of M for prime q ∉ α(M).
- M = N_M(Q)M_α (Frattini + Thm 10.2 hierarchy).
- Lemma 12.18 ⟹ C_{M_β}(P) ≠ 1, C_{M_β}(PQ) = 1, etc.
- Hall construction (H = Hall β(M) ∪ β(M*) subgroup of C_G(P)) and Prop 10.14(d)
  (`S10.normalizer_le_of_nontrivial_beta_subgroup`) ⟹ M = M^g ⊇ H.
- Then r ∈ β(M*) ∩ π(H) ⟹ R ⊆ N_M(Q), so R ⊆ N_G(Q) ⊆ M*.
- Thm 13.4 ⟹ C_{M_σ}(P) ⊆ C_{M_σ}(R), but then [X, Q] = 1 for X ∈ C_{M_σ}(P).
- **最終矛盾**: [X, Q] ⊆ M_α by careful subgroup analysis, but X ⊆ C_{M_α}(PQ) = 1 (Lemma 12.18) ⟹ contradiction.

**形式化見積**: 150-200 行.

---

#### **Theorem 13.9** (L3662-3670) — σ Disjointness for non-conjugate Maximal

**主張**:
- M* ∈ ℳ, M* ≄ M ⟹ σ(M) ∩ σ(M*) = ∅

**簡潔性**: これは **Corollary 12.6(f)** の再確認; §12 で既に established.

**証明**: Lemma 13.6 (maximal uniqueness) + Lemma 13.8 (forbidden config) を合成. Assume q ∈ σ(M) ∩ σ(M*). Thm 13.5 で E₁ prime ⟹ C_S(P) = 1 (where S = E-inv Sylow q of M_σ). Lemma 13.1(a) ⟹ p ∈ τ₁(M*). Then Lemma 13.8 (Q = Q* = S) ⟹ contradiction.

**役割**: Corollary 12.6(f) のprime action 視点からの confirmation. §14–§15 への transfer continuity.

**形式化見積**: 80-100 行.

---

#### **Theorem 13.10** (L3672-3695) — E₁ Action on E₃

**主張**:
- Some P ∈ ℰ_p¹(E₁) does not centralize E₃ ⟹
  1. (a) E₁ does not act regularly on E₃ (contrapositive of regularity).
  2. (b) C_{M_σ}(E₃) = 1 (unless other cases).
  3. (c) ∃ P ⊆ E₁, C_{M_σ}(P) ≠ 1, C_{M_σ}(PQ) = 1 for Sylow Q of E₃.

**数学的意味**:
- E₁ が E₃ に作用するときの "regularity vs. centraization" tradeoff.
- (a) → Lemma 13.7 の条件を satisfy → E₁E₃ prime.
- (c) → Lemma 13.6 の maximal uniqueness via Lemma 12.18.

**証明** (L3674-3695, 22 行):
- P acts regularly on Sylow Q of E₃ (by non-centralization assumption) ⟹ Q = [Q, P] ⊆ E'.
- Take M* ∈ ℳ(N_G(Q)). Lemma 12.2(b) ⟹ M* ≄ M.
- Lemma 12.18 ⟹ C_{M_α}(P) ≠ 1, C_{M_α}(PQ) = 1 ⟹ (c).
- (a) follows from non-regularity. (b): If C_{M_σ}(E₃) ≠ 1, then by (c) and Lemma 13.6, M(C_G(Q*)) ≠ {M}; Prop 10.14(d) handles the `q*∈β(M)` branch, while the other branch is the definition of σ(M). This contradiction gives (b).

**形式化見積**: 100-120 行.

---

#### **Corollary 13.11** (L3696-3698) — E₃ Action Summary

**主張**:
- E₃ ≠ 1, E₃ does not act regularly on M_σ ⟹
  1. (a) τ₂(M) = ∅
  2. (b) τ₁(M) ≠ ∅, τ₃(M) ≠ ∅
  3. (c) E₁E₃ prime on M_σ
  4. (d) E₁ centralizes E₃

**役割**: Theorem 13.10 + Lemma 13.7 のcorollary. §14 への "type P maximal" の setup.

**形式化見積**: 50-70 行.

---

## Prime Action の Thompson 背景

### Thompson 1966 "Nonsolvable Finite Groups" との接続

Thompson のこの論文は **p-局所群の derived series に基づく action theory** を開発. その中核は:

- **p-element への作用が，derived series階層で層別化される**.
- **Prime action**: 単一素数 p での制限的作用 (Thompson の"standard form").
- **Counting arguments**: prime action の family に基づく global constraints.

§13 は **solvable G における Thompson 風作用** の local realization:
- E₁, E₃ (cyclic, coprime) の prime action.
- Lemma 13.4 (τ₁-element の centralizer制御) = Thompson fixed-point idea の local version.
- Lemma 13.7 (simultaneous action) = Thompson の "prime action は products で preserve" の再現.

### Feit-Thompson 本文での位置づけ

§13 は **BG 内では standalone** だが，**Feit-Thompson Theorem の "final steps"** に属する:
- §14 (Type P Counting) は prime action family の cardinality を count.
- §15 (M_F Structure) は prime action に基づく maximal subgroup factorization.
- App.C (Final Contradiction) は global contradiction を prime action inconsistency から derive.

---

## §12 からの継承と explicit dependency

### §12 結果の direct quotations

| §13 Lemma/Thm | 引用 §12 結果 | 役割 |
|---|---|---|
| Lemma 13.1 (a) | Cor 12.16(a) | p ∉ τ₂(M*) の保証 |
| Cor 13.2 | Lemma 13.1, Lemma 12.2(a) | τ-specialization |
| Cor 13.3 | Lemma 12.1(d) | E₁, E₃ cyclicity |
| Thm 13.4 | Lemma 12.18(a), Prop 12.15 | τ₁-centralizer control |
| Lemma 13.6 | Thm 12.5(d), Cor 12.6(a), Lemma 12.17, Thm 13.4 | maximal uniqueness |
| Lemma 13.7 | Thm 13.5, Cor 13.3(b), Lemma 12.1(d), Cor 12.6(d) | E₁E₃ simultaneous |
| Lemma 13.8 | Lemma 12.18, Prop 10.14(d), Thm 13.4 | forbidden config |
| Thm 13.9 | Cor 12.6(f), Lemma 13.6, Lemma 13.8 | σ disjointness |
| Thm 13.10, Cor 13.11 | Lemma 12.2(b), Lemma 12.18, Lemma 13.6, Lemma 13.7 | E₁E₃ interaction |

**計**: §13 全 7 結果中，**13 spots** で §12 を引用. §12 の 19 結果のうち，**8–9 個** が §13 で essential.

### §10 β/σ-prime gate audit (2026-06-02)

**Direct §13 gates**:
- `S10.normalizer_le_of_nontrivial_beta_subgroup` = Prop 10.14(d). Used explicitly in
  Lemma 13.8 and Theorem 13.10 where β-subgroup normalizers must be forced back into the
  corresponding maximal subgroup.
- `S10.disjoint_of_not_conj` = Lemma 10.12. Used in Lemma 13.8 for the final
  `M_α ∩ M*_α = 1` contradiction.
- `S10.isHall_Msigma_Malpha` = Theorem 10.2 surface. Lemma 13.8 still needs the deferred
  quotient nilpotence tail `M'/M_α` from the original theorem; do not replace that by a
  new §13 hypothesis.

**§12-mediated §10 gates now visible in Lean**:
- `S10.beta_complement_normalizer_derived_contains_sylow` = Cor 10.9(a)(3). This is the
  derived-normalizer Sylow containment needed for β-complement Frattini/fusion steps.
- `S10.beta_factorization_of_sylow_normalizer_in_intersection` = Cor 10.9(b). This feeds
  the §12 maximal-interaction branch used before Theorem 13.4 / Lemma 13.8.
- `S10.sigma_complement_commutator_cyclic_normal` = Prop 10.11(d). This is used earlier
  in the §11/§12 exceptional and τ₂ machinery consumed by §13; keep it as an upstream
  proof gate rather than a field of `SubgroupESetup`.

---

## 形式化の dependency graph

```
§10 (M_α, M_σ)
  ↓
§11 (Exceptional, Hypothesis 11.1)
  ↓
§12 (Subgroup E)
  │ ├─ Lemma 12.1 (E structure)
  │ ├─ Thm 12.5 (τ₂ nilpotency)
  │ ├─ Cor 12.6 (A normality in E)
  │ ├─ Thm 12.7 (nonabelian Sylow)
  │ ├─ Cor 12.10 (summary)
  │ ├─ Lemma 12.18 (τ₁ & M_α)
  │ └─ Lemma 12.17, 12.19 (embedding)
  ↓
★ §13 (Prime Action) ← THIS SECTION
  ├─ Lemma 13.1–13.3 (초등적)
  ├─ Thm 13.4–13.5 (Thompson-style)
  ├─ Lemma 13.6–13.7 (extended)
  └─ Lemma 13.8–13.10 (transition)
  ↓
§14 (Type P Counting)
  │ ├─ Prop 14.2: uses Thm 13.5, Thm 13.9
  │ └─ Thm 14.3–14.6: uses Cor 13.3, Lemma 13.6
  ↓
§15 (M_F Structure)
  │ └─ Thm 15.2: uses Lemma 13.6, Thm 13.9
  ↓
App.C (Final Contradiction)
```

---

## §14–§15 への橋渡し役割

### §14 (Type P Counting) への interface

**Proposition 14.2** (mmd 추정 L3745~):
- τ₂(M) ≠ ∅ (exceptional prime p) に対して，M_σ nilpotent (Thm 12.5(a)) + E₁ prime (Thm 13.5) ⟹ prime action family에 based한 maximal counting.

**Theorem 14.3–14.6**:
- Cor 13.3 (E₃ prime), Lemma 13.6 (maximal uniqueness) ⟹ family の full cardinality.

### §15 (M_F Structure) への connection

**Theorem 15.2**:
- Lemma 13.6 + Thm 13.9 (σ disjointness) ⟹ M_F의 maximal family over M_σ.

---

## mathlib カバレッジ

| 概念 | mathlib status | 新規実装 | 引用箇所 |
|------|---|---|---|
| Prime action (정의) | ✗ (새로운 개념) | O | 전체 |
| Derived series, cyclic p-groups | ◐ | § 12 참조 | Cor 13.3, Thm 13.4 |
| Coprime action with normalization | ◐ (basic) | ● (A-invariant) | Lemma 13.6–13.7 |
| Sylow transfer, Focal subgroup | ◐ | ● (§10 via Lemma 13.6) | Lemma 13.6, 13.8 |
| Frattini argument | ◐ | ● (§1 Prop 1.6) | Lemma 13.1 proof |
| Maximal subgroup uniqueness (𝒰) | ◐ (§9) | ● | Lemma 13.6, 13.8, 13.9 |

**新規 정의**:
- `PrimeAction M_σ X` (X acts prime on M_σ)
- `RegularAction M_σ X` (X acts regularly)
- Helper lemmas for cyclic Sylow / E₁, E₂, E₃ interactions.

---

## Phase 2a 형식화 計画

### 예상 일정

**§13 단독** (in parallel with §12 completion):
- Week 1: Lemma 13.1–13.3, Thm 13.5 (elementary, 150 행)
- Week 2: Thm 13.4 (main, 250 행, proof intricate)
- Week 3: Lemma 13.6–13.7 (extended analysis, 250 행)
- Week 4: Lemma 13.8–13.10, Thm 13.9 (transition, 150 행)

**합계**: 3-4 주 (1 person), **800–1100 행 Lean 예상**.

### Dependency 체크리스트

- [ ] §10 (M_α, M_σ, Thm 10.2, Lemma 10.8–10.12) ✓
- [ ] §11 (Hypothesis 11.1, Thm 11.3, 11.5, 11.7) ✓
- [ ] §12 (Lemma 12.1, Thm 12.5, Cor 12.6, Lemma 12.18) ✓
- [ ] Prop 1.5 (A-invariant Hall), Prop 1.6(d) (Frattini + coprime)
- [ ] Thm 12.13 (nonabelian Sylow uniqueness)
- [ ] Prop 12.15 (σ(M) case analysis in other maximal)
- [ ] Lemma 12.17 (C_{M_σ}(E) structure)
- [ ] Thm 9.6 (Uniqueness Theorem for 𝒰)

---

## 미해결 / TODO

### 수학적 정정사항

1. **Theorem 13.4 의 symmetry**: τ₁(M) 내 P와 다른 소수 R 간의 asymmetry. 만약 R도 τ₁이면 대칭적인가? (현재 정리 statement는 r ∈ π(E) 일반적, 하지만 τ₁에 제한되지 않음.) 이 generality가 §14 counting에 필수인지 확인 필요.

2. **Lemma 13.7 의 "non-regular" 가정**: "E₁ does not act regularly on E₃" ⟺ ∃ P ∈ ℰ_p¹(E₁), R ∈ ℰ_r¹(E₃) with C_R(P) ≠ 1. 역방향도 성립하는가? (현재 정리는 forward only로 보임.)

3. **Lemma 13.8 의 completeness**: 5 조건 (1)–(5)에서 (1)–(4)만 주면 (5)는 derived되는가? 아니면 (5)는 독립적 가정인가? mmd L3633-3636 의 원문 다시 읽기.

4. **Cor 13.11 (c) "E₁E₃ prime"**: Lemma 13.7의 contrapositive인가? 아니면 별도의 statement인가? Corollary와 Lemma의 statement 정확성 차이 재확인.

### 형식화 시 주의사항

1. **τ notation의 Lean 표현**: τ₁(M), τ₂(M), τ₃(M)을 record type vs. function vs. set으로 정의할지. Lean 4에서의 관례에 맞게.

2. **Prime action의 unfolding**: 정의 1 (centralizer equality) vs. 정의 2 (elementary part)의 equivalence를 early lemma로 증명.

3. **Proof automation**: Lemma 13.1, 13.2 의 Frattini+rank 계산은 어느 정도 `omega`, `decide` 등으로 자동화 가능한가.

4. **LTE reference**: Lean Feit-Thompson project의 "local analysis" 부분 (수학적으로 비슷한 부분이 있을 수 있음)과 notation 일치성 확인.

---

## 참고문헌 (섹션 내부)

- **Lemma 12.1**: E의 기본 구조 (cyclic E₁, E₃; nilpotent E')
- **Theorem 12.5**: τ₂ 경우의 M_σ nilpotency
- **Corollary 12.6**: τ₂ 시 A ⊲ E, C_G(A) ⊆ E
- **Lemma 12.18**: τ₁ & M_α interaction
- **Theorem 12.13**: Nonabelian p-subgroup의 uniqueness
- **Proposition 12.15**: σ(M)의 다른 maximal에서의 작용
- **Corollary 12.10**: τ-summary
- **Theorem 13.4**: 핵심 Thompson-style 정리 (τ₁ centralizer control)
- **Lemma 13.6**: Maximal family uniqueness
- **Lemma 13.7**: E₁E₃ simultaneous prime action

---

## 현재 상태 (2026-05-22)

**형식화 준비 상태**: Ready for Phase 2a 제 4 파 (§12 complete 후)

**전제 완성**:
- ✓ §1–§9 foundational theory
- ✓ §10 (M_α, M_σ)
- ✓ §11 (Exceptional)
- ✓ §12 (Subgroup E) — currently completing
- ⏳ §13 (Prime Action) — **PENDING**
- ⏳ §14–§15 (Counting & M_F)

**주요 insight 정리됨**:
1. Prime action = 단일 소수 p에 대한 제한적 작용 (정의 embedded in mmd L3486-3492)
2. Theorem 13.4 = 핵심, Thompson 방식의 derived series 제어
3. Lemma 13.6–13.7 = "prime action은 family 전체에서 consistent" 확인
4. Transition (13.8–13.10) = §14 으로의 smoothing

---

## 완성 예상

**형식화 착수**: §12 완성 직후 (est. Week 4 of Phase 2a)  
**형식화 기간**: 3–4 주 (1 person, ~1000 행 Lean)  
**병렬화 가능**: §14–§15 와 partially parallel (§13 early results 후)  
**§14–§15 시작**: Lemma 13.6, Thm 13.5 완성 후

---

*작성: 2026-05-22*  
*출처: BG local-analysis.mmd L3484–3739 (256 행), PDF pp.97-104*  
*참고: §12 부분군 E, §14 Type 𝒫 Counting, §15 M_F Structure, App.C Final Contradiction*  
*Peterfalvi 1984 "Non-solvable finite groups" (Thompson 작용론 기반)*
