# BG §12: 部分群 E — 大規模節の形式化ロードマップ

## ✅ 2026-06-10 Lemma 12.1 COMPLETE (issue 5002 closed)

**`subgroupE_basic` (a)-(g) 全 conjunct sorry-free、unconditional・axiom-clean**
(standard 3 のみ; keystone forward-axiom にすら非依存)。AxiomsCheck
`#assert_only_allowed_axioms` 登録、full build 3613 green。commits 9f1d22c4 → 0107bdf2。

下記レシピからの実装上の差分 (handoff 用):
- **(b)(f) は Frattini でなく Burnside 再編で実装**: `W = N_E(P)`、SZ-補群 `K`、
  mathlib **`Sylow.commutator_eq_bot_or_commutator_eq_self`** (cyclic Sylow の
  ⁅K,P⁆ = ⊥ ∨ P dichotomy — Prop 1.6(d) + 鎖論法のパッケージ!) で分岐し、
  ⊥ 枝は `W ≤ C_E(P)` → Burnside normal p-complement ⊇ E' が `p ∣ |E'|`
  (`dvd_card_derived_of_mem_tau3`) と矛盾。P 枝が `P = ⁅K,P⁆ ≤ E'`。
  (f) は P 枝で Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`) +
  **conjugation bridges** (`actionCommutator_conj_map_subtype` = ⁅P,K⁆,
  `fixedPointsOfMulAut_conj_map_subtype` = C(K)⊓P) で `C_P(K) = ⊥`。
- **E∩M' ≤ E'** (`inf_derivedInG_le_derivedInG`): mk' M_σ 商へ写し complement が
  derived を運ぶ (`Subgroup.map_commutator` + ker 差吸収)。`p∈τ₃ ⟹ p∣|E'|` は
  `M' ≤ M_σ(E⊓M')` 分解 (IsComplement'.existsUnique) + p∤|M_σ|。
- **(e) E₂⊴E₁₂** は新 field `E₁₂_hall` 経由: commutator ↥(E₁⊔E₂) の素因子は
  (τ₁∪τ₂)∩(τ₂∪τ₃) = τ₂ ⟹ Hall τ₂ = E₂ に `normal_le_hall` で吸収 ⟹
  `normal_of_commutator_le`。E₂ の Hall-in-J 化は `relIndex_mul_relIndex` tower。
- **(e) E=E₁E₂E₃**: join の subgroupOf index が τ-分割の各 Hall index を割る ⟹ 1。
- **E₃ ⊴ E**: E₃ = `opiCoreInG τ₃ E'` (nilpotent E' の `oPiCore_isHall_of_isNilpotent` +
  Hall card 同定) → `le_normalizer_opiCoreInG_of_le_normalizer`。
- 技法メモ: ⁅g,x⁆ element bracket をソースに直接書くと `Bracket Γ Γ` 不能
  (scoped notation)。`Subgroup.commutator_mem_commutator` + `commutatorElement_def` rw で回避。
  `(... : Subgroup _)` の型穴は normalizer 系で解決不能 → private abbrev
  (`sylowNormalizerE`/`sylowSelfE`) で明示。`set W := ...` を rcases 後の枝でやると
  既存変数を分裂させる (S09 の罠と同根) → obtain/rcases の前に固定。
- 再利用資産: `one_le_pRank_of_mem_primeFactors` (Cauchy→pRank≥1)、
  `isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one`、conjugation bridges、
  τ-partition 基本層、`isPiGroup_tau23_derived`。public 化:
  `S10.isCyclic_of_pRank_le_one`、`S10.le_of_coprime_card_index`。

**▶ 次 frontier** (着手可能残): **12.2(a)** (Lem 10.5 のみ・軽)、**12.19** (Cor 10.9(a)
のみ・軽)、**12.17** (Lem 6.3(a) 第 2 結論 `C_H(K)≤H'` の §6 補完が必要)、**12.18** (大物:
Thm 1.13 + Thm 3.7 + 式 (12.5)-(12.7))。残り 14 件は 10.13 ブロック (下記 triage)。

## 2026-06-10 D-lane triage (issue 5002): §11 依存 vs 着手可能の定理単位分類

mmd L3023-3483 全 19 結果の証明を精読して依存を確定 (再 triage 不要)。
**ブロッカーの根 = Thm 11.7 / Lem 10.13 (どちらも Lemma 10.13 = c-bg-s10 委任領域)**。

### 着手可能 (§11 非依存) — 5 件

| 結果 | Lean name | 依存 (mmd 確認済) |
|---|---|---|
| **Lem 12.1** | `subgroupE_basic` | Thm 10.2 (`isHall_Msigma_Malpha`), Lem 4.5(a) (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` の対偶), Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`), Lem 10.4(c) (`alpha_criterion`.2) |
| **Lem 12.2(a)** | `prime_mem_sigma_or_tau2` | Lem 10.5 のみ ((b) 非共役 clause が Thm 10.1(b) — Lean surface は (a) のみ) |
| **Lem 12.17** | `Msigma_E_relations` | Lem 6.3(a) のみ。`[M_σ,E]=M_σ` は landed (`commutator_eq_self_of_isComplement'_le_commutator`); `C_{M_σ}(E)⊆M_σ'` は Lem 6.3(a) **第 2 結論** (未 landed、§6 で証明可能・keystone 非依存) |
| **Lem 12.19** | `derivedE_centralizes_betaComplement` | Cor 10.9(a) (✅ landed) + 互いに素 |
| **Lem 12.18** | `tau1_Malpha_interaction` | Lem 12.2(a) + Thm 1.13 + Thm 3.7 (✅ landed) + Thm 10.2(d) + Uniqueness + Cor 10.9(a)(2) + 式 (12.5)-(12.7)。§11 非依存だが大物 |

### ブロック (Thm 11.7 = Lem 10.13 経由) — 14 件

- **Lem 12.3** (`elemAb_centralizes_meet`): 証明が **Thm 11.7 を直接使用** ("it follows from
  Theorem 11.7 that M*_σA ⊴ M*") + Cor 11.4 + Lem 10.12(a) + Lem 12.2(b)。
- **Prop 12.4** ← 12.3。 **Thm 12.5** ← 12.4 + **Thm 11.3/11.5/11.7 + Cor 11.6 直接**。
- τ₂-case cascade: **Cor 12.6** ← 12.5; **Thm 12.7** ← 12.5/12.6 + **Lem 10.13(b)(c) 直接**;
  **Lem 12.8** ← 12.7(a); **Cor 12.9** ← 12.8(e)/12.7(c); **Cor 12.10** ← 12.5(b)/12.7(a)/12.8(a);
  **Lem 12.11** ← 12.6/12.5/12.10(c)/12.7(d); **Thm 12.12** ← 12.7/12.8/12.6(c)/12.5(f)/12.11(c)。
- σ-side: **Thm 12.13** ← 12.10(a)(d)/12.4 + Cor 10.7(b); **Cor 12.14** ← 12.13;
  **Prop 12.15** ← 12.10(d)/12.2/12.5(e)/12.6; **Cor 12.16** ← 12.15/12.5(e)/12.6(f)。

⟹ forward-axiom 化はしない (LAUNCH.md の方針どおり §11 ブロック分は素通し)。10.13 が
解ければ §11 (11.5/11.6/11.7) → 12.3 → cascade が一斉に開く。

### ⚠ scaffold statement 訂正 (2026-06-10): 12.1(e) `E₂ ⊴ E₁⊔E₂` は旧 setup で偽

原文は **`E₁₂` を Hall τ₁∪τ₂-subgroup として固定し、`E₁`,`E₂` をその内部の Hall** に取る
(mmd L3029)。旧 `SubgroupESetup` は E₁/E₂ を E の独立な Hall とし `E12 := E₁ ⊔ E₂` と
再定義していたため、E₁ だけ共役でずらすと `E₂ ⋪ E₁⊔E₂` の反例が組める
(例: E = (C₃₁⋊C₁₅)×C₅, τ₁={3}, τ₂={5}, τ₃={31}; E₁ = ⟨a y a⁻¹⟩ (a∈C₃₁) に対し
⁅E₁,E₂⁆ が C₃₁ 成分を持ち E₁⊔E₂ = E ⊉ normalizer E₂)。
**修正 = `SubgroupESetup` に field `E₁₂_hall : IsHallSubgroup (tau1 M ∪ tau2 M)
((E₁ ⊔ E₂).subgroupOf E)` を追加** (原文 faithful 化)。producer 義務は §13 活用時に
12.1(e) と同じ論法 (E₁₂' ≤ O_{τ₂}(E₁₂) ≤ E₂ ⟹ E₂ ⊴ E₁₂ ⟹ |E₁E₂|=|E₁₂|) で果たせる
(非 vacuous)。S12/S13 に constructor 使用なし ⟹ 波及ゼロ。

### Lem 12.1 実装レシピ (確定)

- **(a) E' nilpotent**: 原文の Thm 10.2「M'/M_σ nilpotent」は repo 未収載 (docstring「追加予定」)。
  **Thm 4.20(a) `derived_le_fitting_of_rank_fitting_le_two` で代替** (issue 5001(b) と同じ手):
  E は σ'-群 (M_σ Hall σ の補群) ⟹ π(E)∩α=∅ ⟹ rank E ≤ 2 ⟹ E' ≤ F(E) nilpotent。
  rank≤2 論法は issue 5001 part(a) Step 2 のコードがテンプレート。
- **(d) E₁ cyclic**: E₁∩M' = ⊥ (π(E₁)⊆τ₁, π(M') 排反, card 論法) ⟹ E₁' = ⊥ abelian;
  各 Sylow cyclic (Lem 4.5(a) 対偶 + r_p(M)=1); abelian + 全 Sylow cyclic ⟹ cyclic
  (nilpotent π-分解 or `IsZGroup`)。E₃ cyclic は (b) E₃ ⊆ E' nilpotent + Sylow cyclic で同様。
- **(b)(f)**: p∈τ₃ ごと P = Sylow p of E。E' nilpotent ⟹ O_p(E')⊴E は P に入り
  O_{p'}(E')⊴E ⟹ **N⊔P_G ⊇ E' ⟹ N⊔P_G ⊴ E** (N = O_{p'}(E); quotient 回避、derived を含む
  部分群は normal)。Frattini (`Sylow.normalizer_sup_eq_top`) ⟹ E = N·N_E(P)。SZ で
  K = complement of P in N_E(P)。[P,K]=1 と仮定 ⟹ E' ≤ N⊔K' (commutator calculus,
  P abelian) ⟹ E' ≤ NK p'-群 ⟹ P∩E'=⊥、p∈π(E') に矛盾 ⟹ [P,K]≠1。
  Prop 1.6(d) (`fixedPoints_isComplement_actionCommutator_of_abelian`, φ = conj action) ⟹
  P = C_P(K) × [P,K]、P cyclic p-群の部分群束は鎖 ⟹ C_P(K)=⊥ ∧ [P,K]=P ⊆ E'。
  (f) は C_{E₃}(E) の p-part ⊆ C_P(K) = ⊥。
- **(e)**: π(E') ⊆ τ₂∪τ₃ (E'≤M'∩E, τ₁∩π(M')=∅) ⟹ E' ≤ E₂⊔E₃
  (`Subgroup.IsPiGroup.normal_le_hall`; E₂⊔E₃ = E₂E₃ Hall τ₂∪τ₃, card = |E₂||E₃| via E₃⊴E)
  ⟹ E₂⊔E₃ ⊴ E (⊇ derived)。E = E₁⊔(E₂⊔E₃) は card。E₂ ⊴ E₁₂ は新 field `E₁₂_hall` 経由で
  E₁₂'( ≤ E'∩E₁₂ τ₂-群 normal) ≤ O_{τ₂}(E₁₂) ≤ E₂。
- **(c)**: E ≠ ⊥ (M_σ ≤ M' ⊊ M, solvable nontrivial M ⟹ E ≅ M/M_σ ≠ 1)。E₂=E₁=⊥ なら
  (e) で E = E₃ ⊆ E' ⟹ perfect ⟹ E 可解と矛盾。
- **(g)**: `alpha_criterion`.2 直接 (p.Prime は `mem_primeFactors_card_of_pos_pRank` 経由)。

## 2026-06-02 B7 foundation checkpoint

Lean file: `OddOrder/BG/Ch3_MaximalSubgroups/S12_E.lean`.

Concrete surfaces now present:
- Definitions: `tau1`, `tau2`, `tau3`, and `SubgroupESetup` for `E` complement data and Hall `E₁/E₂/E₃`.
- New API: membership rewrites for `tau1`/`tau2`/`tau3`, `tau_i ⊆ sigma(M)'` projections, rank/derived-prime projections for `tau_i`, disjointness helpers between `tau1` and `tau3`, named joins `E12`, `E23`, `E123`, and `SubgroupESetup` projection lemmas (`E_complement`, `E1_le_M`, `E2_le_M`, `E3_le_M`, `E12_le_E/M`, `E23_le_E/M`, `E123_le_E`).

Current Lean inventory: 19 theorem-level `sorry`s remain in §12, matching the 19-result scaffold.

Main proof blockers: §10 Hall/fusion/beta results, §11 exceptional maximal endpoints, BG Lemma 4.5/Thm 4.20, Proposition 1.6(d), Theorem 1.13, Theorem 3.7, and the Uniqueness Theorem. The `SubgroupESetup` fields intentionally do not include any of these hard conclusions.

**スコープ**: BG §12 (pp.83–96), mmd L3023-3483, **19 結果** (そのうち主要 15 個).  
形式化先 (予定): `OddOrder/BG/Ch3_MaximalSubgroups/S12_SubgroupE.lean` (2 ファイル分割の可能性大)  
ROADMAP 上の位置: Phase 2a 第 4 波 (§10-§11 完成必須)  
役割: 部分群 E の構造定理と共役性、§13 Prime Action の前提  
難度: **★★★★★** (本文最大級、460 行で 15 主要結果、局所解析特有概念)

---

## TL;DR: §12 は単独で小章相当の大規模構造理論

§12 は **最大部分群 M の補集合 E (≅ M/M_σ) の精密構造** を 460 行かけて確立する本文最大級の節. 典型的には小規模な lemma chain だが、ここでは:

1. **E の基本構造** (12.1): E' nilpotent, r(E) ≤ 2, すべての Sylow 部分群 abelian
2. **τ₂(M) ≠ ∅ の場合** (12.5–12.12): 最も複雑な subsection (8 主要結果群)
3. **σ(M) 側の埋め込み** (12.13–12.19): nonabelian p-subgroup の一意性と M_σ の埋め込み制御

形式化では **2000+ 行の Lean 予想**. 単一ファイルは避けるべき. むしろ conceptual chunks に分割:
- `S12A_Structure.lean`: 12.1–12.4 (基本構造)
- `S12B_Tau2.lean`: 12.5–12.12 (τ₂ case 中心)
- `S12C_Sigma.lean`: 12.13–12.19 (σ(M) / embedding)

---

## §12 全 19 結果の精密リスト

| No. | 名前 | 型 | L範囲 | 概要 | 主キーワード |
|-----|------|-----|------|------|-------------|
| 1 | **Lemma 12.1** | Lemma | 3035–3060 | E' nilpotent, E₁ cyclic, E₃ ◁ E, C_{E₃}(E)=1 | Structure of E, cyclic radicals, kernel relations |
| 2 | **Lemma 12.2** | Lemma | 3062–3069 | p-subgroup X の normalizer の maximal subgroup 分類 | Maximal containment, τ-notation |
| 3 | **Lemma 12.3** | Lemma | 3071–3093 | A ∈ E_p²(M ∩ M*) が M_σ ∩ M* を centralize | Coprime action on p'-subgroups |
| 4 | **Prop 12.4** | Proposition | 3095–3126 | A ∈ E_p²(M) ⟹ C_G(A) ⊆ M (かつ condition on hypothesis 11.1) | Exceptional maximal existence |
| 5 | **Thm 12.5** | Theorem | 3129–3148 | τ₂(M) ≠ ∅ ⟹ M_σ nilpotent, abelian Sylow p, M_σA ◁ M | Main τ₂ case, nilpotent control |
| 6 | **Cor 12.6** | Corollary | 3150–3169 | τ₂(M) ≠ ∅, A ∈ E_p²(E) ⟹ A ◁ E, C_G(A) ⊆ E | Normality in E, centralizer bounds |
| 7 | **Thm 12.7** | Theorem | 3171–3220 | Nonabelian Sylow p, τ₂(M) ≠ ∅ ⟹ τ₂(M) singleton, A₀ ∈ E^1(A), E₀ complement | Abelian vs. nonabelian Sylow split |
| 8 | **Lemma 12.8** | Lemma | 3223–3259 | Abelian Sylow p, τ₂(M) ≠ ∅ ⟹ E₂ abelian Hall τ₂-subgroup | Abelian case structure, exponent preservation |
| 9 | **Cor 12.9** | Corollary | 3260–3269 | [A,Q] ≠ 1 (A ∈ E_p², Q ∈ E_q¹) ⟹ decomposition A = A₀ × A₁ | Conjugacy non-isomorphism |
| 10 | **Cor 12.10** | Corollary | 3270–3283 | (a) nilpotent σ(M)'-subgroup abelian, (b) E₂, E' abelian | Nilpotency & abelianity summary |
| 11 | **Lemma 12.11** | Lemma | 3284–3305 | M* ∈ M(N_G(A)) ⟹ τ₂(M) ⊆ σ(M*) - β(M*) | τ₂ transfer to other maximal |
| 12 | **Thm 12.12** | Theorem | 3306–3344 | C_{M_σ}(e)=1 ∀(τ₁∪τ₃)-element e ⟹ A₀ abelian normal, E₀ Frobenius complement | Frobenius structure existence |
| 13 | **Thm 12.13** | Theorem | 3347–3368 | Nonabelian p-subgroup ⟹ p ∈ U (一意性集合) | Nonabelian p-group uniqueness |
| 14 | **Cor 12.14** | Corollary | 3369–3384 | p ∈ σ(M), X ∈ E_p¹(M), p ∈ β(M) or X ⊆ M_σ' ⟹ M(C_G(X)) = {M} | σ(M) side maximal uniqueness |
| 15 | **Prop 12.15** | Proposition | 3385–3422 | q ∈ σ(M), X nonid q-subgroup ⟹ conditions on M* ∈ M(N_G(X)) | σ(M) containment in other maximal |
| 16 | **Cor 12.16** | Corollary | 3423–3447 | σ(M)-subgroup Y ⟹ Y conjugate to M_σ subgroup | σ(M)-subgroup conjugacy |
| 17 | **Lemma 12.17** | Lemma | 3448–3453 | C_{M_σ}(E) ⊆ M_σ', [M_σ,E] = M_σ, M_σ ∩ M^g cyclic β(M)'-group | Embedding M_σ in G via E action |
| 18 | **Lemma 12.18** | Lemma | 3454–3479 | p ∈ τ₁(M), P ∈ E_p¹, Q P-inv q-subgroup, C_Q(P)=1, M(N_G(Q)) ≠ {M} ⟹ control of M_α | τ₁ & σ interaction |
| 19 | **Lemma 12.19** | Lemma | 3480–3482 | E' centralizes Hall β(M)'-subgroup of M_σ | Derivedrator & β partition |

**集計**: 3 Theorem + 5 Corollary + 11 Lemma + 1 Proposition = **19 結果**.  
**主要度**: 12.1–12.4 (基礎), 12.5–12.11 (τ₂ case の中核, 8 結과), 12.13–12.19 (σ(M) uniqueness & embedding)

---

## E の精密定義

### E の導入と記法 (L3023–3032)

**Hypothesis**: M は maximal subgroup of G. **E は M_σ の M 内での complement** = $E \cong M/M_σ$ with $M = E \ltimes M_σ$ (semidirect product, 単なる product ではない).

**π(E) = τ₁(M) ∪ τ₂(M) ∪ τ₃(M)** に分割:

- **τ₁(M)** = {p ∈ σ(M)' | p ∉ π(M'), r_p(M) = 1}
  - p は σ(M) に属さず、M' に出現せず、rank 1
  - r_p(E) = 1 でもあり
  
- **τ₂(M)** = {p ∈ σ(M)' | r_p(M) = 2}
  - σ(M) に属さず、rank 2
  - **最も複雑な case** (12.5–12.12 の中核)
  
- **τ₃(M)** = {p ∈ σ(M)' | p ∈ π(M'), r_p(M) = 1}
  - σ(M) に属さず、M' に出現、rank 1

### Hall subgroup decomposition

E_{12}, E_1, E_2, E_3 は対応する Hall subgroups of E or E_{12}:

- **E_{12}** = Hall (τ₁ ∪ τ₂)-subgroup of E
- **E_1** = Hall τ₁-subgroup of E_{12}
- **E_2** = Hall τ₂-subgroup of E_{12}
- **E_3** = Hall τ₃-subgroup of E

重要な関係:
- **E = E₁E₂E₃** (coprime order product)
- **E₁₂ = E₁E₂**
- **E₂E₃ ◁ E** (Lemma 12.1(e))
- **E₂ ◁ E₁₂** (Lemma 12.1(e))

---

## 15 結果のグループ化と依存構造

### Group A: E の基本構造 (結果 1–4, 12.1–12.4, L3023–3126)

**概要**: E の抽象的構造定理. τ notation 導入, Hypothesis 11.1 への bridge.

**主要定理**:
- **12.1**: E' is nilpotent, E₁ & E₃ cyclic, E₃ ◁ E, C_{E₃}(E)=1
- **12.2**: p-subgroup X の normalizer での maximal subgroup の τ 分類
- **12.3**: A-centralization lemma (preparation for 12.4)
- **12.4**: A ∈ E_p²(M) ⟹ C_G(A) ⊆ M + exceptional maximal existence condition

**数学的流れ**:
1. Thm 10.2 (M'/M_σ nilpotent) ⟹ E' nilpotent (12.1(a))
2. Frattini argument & rank argument ⟹ E₁, E₃ cyclic (12.1(d))
3. τ partition の閉性確認 (12.2 via rank calculation)
4. C_G(A) ⊆ M の基本的なことが従う (12.4(a), Thm 11.1 hypothesis setup)

**形式化予想**: 150–200 行 (per-result 15–25 行, proof のみ).

**依存**: §10 (τ notation 定義), §11 (Hypothesis 11.1), Lemma 4.5 (cyclic p-group rank 1), Frattini argument (Proposition 1.6(d)), Thm 10.2.

---

### Group B: τ₂(M) ≠ ∅ の詳細構造 (結果 5–12, 12.5–12.12, L3127–3344)

**概要**: τ₂(M) が非空のとき (= rank 2 prime case) の最複雑な局所解析. **最も厚い subsection** (218 行, 8 主要結果).

**文脈**: §11 Hypothesis 11.1 がここで activate される.

**主要定理**:

1. **Thm 12.5**: τ₂(M) ≠ ∅ ⟹
   - M_σ is nilpotent
   - Sylow p-subgroups of M abelian, Ω₁(P) = A (= M_σA ◁ M)
   - C_{M_σ}(A) = 1
   - M_σ ∩ M* = 1 for M* ∈ M(A) - {M}

   **Thm 11.5, 11.7 の直接的応用**, ただし A は E 側 (not M_σ 側).

2. **Cor 12.6**: τ₂(M) ≠ ∅, A ∈ E_p²(E) ⟹
   - A ◁ E (because M_σA ◁ M by 12.5(c) + M = M_σE)
   - C_G(A) ⊆ N_M(A) = E
   - M(C_G(X)) = {M} for certain X ∈ E_p¹(E)

   **Key implication**: τ₂ prime の元素的abelian 2-group A は E 内で normal + centralizer bound.

3. **Thm 12.7**: Sylow p-subgroup nonabelian case ⟹
   - τ₂(M) = {p} (singleton)
   - A₀ = C_A(M_σ) has order p, F(M) = M_σ × A₀
   - E₀ = complement to A₀ in E

   **Technical peak**: Sylow p-subgroup が nonabelian の場合の最精密な factorization.

4. **Lemma 12.8**: Sylow p-subgroup abelian case ⟹
   - E₂ abelian ◁ E
   - E₂ Hall τ₂(M)-subgroup of G
   - S ⊆ N_G(S)' ⊆ F(E) ⊆ C_G(S) ⊆ E
   - N_G(A) = N_G(S) = N_G(E₂) = ... (many equalities)

   **Abelian Sylow case での simplification**.

5. **Cor 12.9**: [A,Q] ≠ 1 (A ∈ E_p², Q ∈ E_q¹, q ∈ τ₁(M)) ⟹
   - A = A₀ × A₁ (decomposition)
   - A₀ = [A,Q] ∈ E¹(A) with N_G(A₀) = M
   - A₁ conjugate と non-isomorphic in G
   - C_G(A₁) ⊄ M

   **Interaction between τ₂ & τ₁**.

6. **Cor 12.10**: Summary corollaries:
   - (a) Nilpotent σ(M)'-subgroup abelian
   - (b) E₂, E' abelian
   - (c) E₂E₃ ⊆ C_E(A) ◁ E, π(E/C_E(A)) ⊆ τ₁(M)
   - (d) Noncyclic p-subgroup P ∈ σ(M) ⟹ N_G(P) ⊆ M
   - (e) x ∈ E with π(⟨x⟩) ⊆ τ₂(M), C_{M_σ}(x) ≠ 1 ⟹ M(C_G(x)) = {M}

   **Corollary anthology**, §13 で多用.

7. **Lemma 12.11**: M* ∈ M(N_G(A)), τ₂(M) ≠ ∅, A ∈ E_p²(E) ⟹
   - τ₂(M) ⊆ σ(M*) - β(M*)
   - π(E/C_E(A)) ⊆ τ₁(M*) ∪ τ₂(M*)
   - Condition on q ∈ π(E/C_E(A)) ∩ π(C_E(A))

   **τ₂ from M transfer to other maximal**.

8. **Thm 12.12**: "Frobenius condition" (C_{M_σ}(e)=1 for all (τ₁∪τ₃)-elements e) ⟹
   - ∃ abelian normal A₀ with C_E(x) ⊆ A₀ ∀ x ∈ M_σ#
   - ∃ E₀ of same exponent as E, E₀M_σ is Frobenius group kernel M_σ

   **Richest structural theorem**: 12.12 は 5 page proof (L3306–3344) で case splitting on C_E(S) ⊆ E か否か.

**数学的highlight**: 12.5–12.8 で τ₂ case の abelian vs. nonabelian Sylow split を完全に解決. 12.9–12.12 では other maximal への transfer と Frobenius factorization.

**形式化予想**: 600–800 行 (per-result 50–80 行, proofs が thick).

**依存**: §11 (Hypothesis 11.1 + Thm 11.3, 11.5, 11.7), §10 (Corollary 10.9, Lemma 10.10, 10.12, 10.13), Prop 1.5, 1.6 (A-invariant, Frattini), Lemma 4.5 (cyclic), Maschke (1.5).

---

### Group C: σ(M) の埋め込みと一意性 (結果 13–19, 12.13–12.19, L3345–3482)

**概要**: nonabelian p-group と σ(M) の側面. M_σ の G への埋め込み制御, τ₁ との相互作用.

**主要定理**:

1. **Thm 12.13**: Nonabelian p-subgroup ⟹ p ∈ U (unique maximal set)

   **最も簡潔な一意性定理**. Corollary 12.10(d) + cyclic vs. nonabelian Sylow split.

2. **Cor 12.14**: p ∈ σ(M), X ∈ E_p¹(M), p ∈ β(M) or X ⊆ M_σ' ⟹
   - M(C_G(X)) = {M}

   **σ(M) side での C_G(X) uniqueness**.

3. **Prop 12.15**: q ∈ σ(M), X nonid, M* ∈ M(N_G(X)) - {M} ⟹
   - M* ≄ M
   - N_G(S) ⊆ M (S = Sylow q-subgroup of M ∩ M*)
   - Case split on q ∈ σ(M*): (d) q ∈ σ(M*) + (e) q ∉ σ(M*)

   **Most general σ(M) interaction**, Corollary 12.6(f) の σ disjointness 確立.

4. **Cor 12.16**: σ(M)-subgroup Y ⟹
   - Y conjugate to subgroup of M_σ
   - For p ∈ π(E) ∩ β(G)', H ∈ M(Y) not conjugate to M: r_p(N_H(Y)) ≤ 1, etc.

   **σ(M)-subgroup の conjugacy class**.

5. **Lemma 12.17**: Embedding relations
   - C_{M_σ}(E) ⊆ M_σ'
   - [M_σ, E] = M_σ
   - M_σ ∩ M^g cyclic β(M)'-group (g ∈ G - M)

   **Intersection structure** across conjugates.

6. **Lemma 12.18**: τ₁ & M_α interaction
   - p ∈ τ₁(M), P ∈ E_p¹(M), Q P-inv q-subgroup, C_Q(P)=1, M(N_G(Q)) ≠ {M}
   - ⟹ (a) M_α ≠ 1 & q ∉ α(M) ⟹ C_{M_α}(P) ≠ 1 & C_{M_α}(PQ) = 1
   - ⟹ (b) Q Sylow ⟹ α(M) = β(M) (key: β = α characterization)

   **Delicate τ₁ argument**, 引用頻度が高い (§13 の 3 spots).

7. **Lemma 12.19**: E' centralizer
   - E' centralizes Hall β(M)'-subgroup of M_σ

   **Coprime order product** (E' と M_σ が互いに素).

**数学的highlight**: Group C は Group B (τ₂ case) の completion. 12.13 で nonabelian p-group の一意性を secured. 12.15–12.17 で σ(M) の family across conjugates の structure. 12.18–12.19 は more specialized interactions.

**形式化予想**: 300–400 行 (per-result 30–50 行).

**依存**: Thm 12.13 (nonabelian uniqueness), Corollary 12.10 summary, Group A & B prior results, Lemma 10.12 (β-related), §9 Uniqueness Theorem (maximal comparison).

---

## 下流での引用と接続

### §13 Prime Action での §12 利用

§13 (L3484–3739) は "Prime Action" = derived series with Thompson-style actions. **§12 の 13 spots から引用**:

- **Thm 13.1–13.9**: §12 から Cor 12.6(d), Lemma 12.18 (a), Thm 12.7, Thm 12.13 などを multi-step composition で利用
- **Key dependency**: 12.18 は 13 で 3+ spots で引用 (τ₁ & M_α の interaction)
- **Frobenius factorization**: Thm 12.12 が Lemma 14.1 で引用 (§14 での type-P maximal の Frobenius family への応用)

### §14–§15 への cascade

- **Prop 14.2**: Thm 12.5(a) (M_σ nilpotent) を前提に counting argument 展開
- **Thm 14.3–14.6**: Cor 12.6, 12.10 summary に依存して maximal family counting
- **Thm 15.2**: Lemma 12.19 (E' ∩ Hall β(M)') を使用

---

## Peterfalvi との関係

**BG App.C "Final Contradiction" との重複**: App.C は Peterfalvi 1984 paper の改訂版. その論文は **Peterfalvi 本体 §9 (04.9_*.mmd)** と論理的に同一.

**§12 と Peterfalvi §9 の接続**:
- Peterfalvi §9 は **type-I group (non-existence) の証明** で global counting / Frobenius family argument を展開
- BG §12 の **Thm 12.12 (Frobenius structure)** + Thm 12.13 (nonabelian uniqueness) が Peterfalvi §9 の local prerequisites
- Phase 2b で Peterfalvi §9 を形式化するとき、§12 の Thm 12.12–12.13 + Cor 12.10 は **既に mathlib に integrated** な状態が理想

**BG独自性**: BG §12 の Group A (12.1–12.4) は Peterfalvi には explicit に出現せず. これは **BG の local setup の汎用性** を示す (complement definition, τ notation などが Peterfalvi 以外の contexts でも出現).

---

## mathlib カバレッジ

### 既存 (high)
- **Solvable**: Group theory, solvable series, derived series API
- **Sylow**: Sylow subgroup existence, conjugacy
- **Nilpotent**: Fitting subgroup (Phase 1 で実装予定)
- **Coprime action**: Basic `CoprimeAction` API (mathlib 既存)
- **Frattini argument**: (mathlib にはないが §1 で BG が定義, Phase 2a で実装)

### 一部 / 新規 (mid)
- **A-invariant Hall theory**: Basic Hall は mathlib にあるが、coprime action 下の A-invariant completion は **新規** (§1 Prop 1.5)
- **p-group rank**: Basic rank function は mathlib にあるが、Blackburn rank ≤ 2 decomposition は新規
- **Cyclic p-group characterization**: Lemma 4.5 (rank 1) — 新規

### 完全新規 (low)
- **τ₁, τ₂, τ₃ notation & partition**: §12 独自の fine partition. mathlib には無い
- **E の定義**: complement of M_σ in M — 新規 structure (group extension theory で後に generalize 可)
- **Thm 11.1 Hypothesis**: Exceptional maximal の machinery — §11 で新規
- **Group A–C の 19 結果全て**: 新規証明体系

### Phase 2a での実装ボリューム

- **§12 alone**: 2000+ 行 Lean 予想
  - Lemma 12.1 proof: 100+ 行 (Frattini, rank calculation multi-case)
  - Thm 12.5 proof: 150+ 行 (Thm 11.5, 11.7 composition)
  - Thm 12.7 proof: 200+ 行 (Sylow abelian vs. nonabelian split, exponent preservation)
  - Thm 12.12 proof: 250+ 行 (case C_E(S) ⊆ E, regular action on M_σ)
  - Thm 12.13 proof: 100+ 行 (generator-relation argument, focal subgroup)
  - Remaining (12.2, 12.3, 12.4, 12.6, 12.8–12.11, 12.14–12.19): 800–1000 行

- **合計 mathlib additions**: §12 dedicated + §10–§11 adjacent = **5000+ 行 Lean code** (cf. §12 mmd 460 行)

---

## 形式化規模と 2 ファイル分割の検討

### なぜ分割が必要か

単一の `S12_SubgroupE.lean` では:
- **2000+ 行 threshold**: IDE navigation, compilation time の悪化
- **Conceptual boundary**: Group A (structure), Group B (τ₂ case), Group C (σ & uniqueness) は論理的に distinct
- **Reusability**: Group A だけ import する downstream module があり得る (§13 では主に Group C 引用)

### 提案分割スキーム

**Option 1: 3 ファイル分割 (推奨)**

```
OddOrder/BG/Ch3_MaximalSubgroups/
  └─ S12_SubgroupE/
     ├── A_Structure.lean          (12.1–12.4, ~200 行)
     ├── B_Tau2Case.lean           (12.5–12.12, ~800 行)
     └── C_Sigma_Embedding.lean    (12.13–12.19, ~300 行)
  └─ S12_SubgroupE.lean            (aggregate, ~50 行 = imports + docstring)
```

**利点**:
- Group A は independent-ish (12.1–12.3 は pure structure, 12.4 は Hypothesis 11.1 bridge のみ)
- Group B は heaviest, most intricate (sub-section として隔離価値大)
- Group C は Group A だけに depend, Group B には weak dependency

**欠点**: Lean 4 では subdirectory の import convention が要注意 (relative imports, module hierarchy).

**Option 2: 2 ファイル分割**

```
OddOrder/BG/Ch3_MaximalSubgroups/
  ├── S12A_Structure.lean       (12.1–12.4, ~200 行)
  └── S12B_MainTheorems.lean    (12.5–12.19, ~1200 行)
```

**利点**: Module hierarchy が simpler.  
**欠点**: S12B が重過ぎる (1200 行は IDE 限界手前).

### 推奨: Option 1 (subdirectory 分割)

Lean 4 module convention にて:

```lean
namespace OddOrder.BG.Ch3.S12

-- In A_Structure.lean
theorem lemma_12_1 : ... := ...
theorem prop_12_4 : ... := ...

-- In B_Tau2Case.lean
import .A_Structure
theorem thm_12_5 : ... := ...
theorem thm_12_12 : ... := ...

-- In C_Sigma_Embedding.lean
import .A_Structure
theorem thm_12_13 : ... := ...
theorem lemma_12_19 : ... := ...

-- In S12_SubgroupE.lean (aggregate)
import .A_Structure
import .B_Tau2Case
import .C_Sigma_Embedding
```

---

## Phase 2a 形式化着手順

### Timeline (estimate)

**Phase 2a 第 4 波** = §10–§13 parallel completion

1. **§10 M_α/M_σ** (2 week, 1500 行): prerequisite
2. **§11 Exceptional** (1 week, 500 行): prerequisite
3. **§12 Subgroup E** (4 week, 2000 行, **this section**)
   - Week 1: Group A (structure, 200 行)
   - Week 2: Group B (τ₂ case, 800 行) ← **heaviest**
   - Week 3: Group B continued (proofs refinement, type-checking)
   - Week 4: Group C (σ & embedding, 300 行)
4. **§13 Prime Action** (2 week, 800 行): depends on §12, parallel possible

### Intermediate milestones

- **After Group A**: Can export structure definitions (E₁, E₂, E₃, τ-partition) for downstream
- **After Thm 12.5**: Core τ₂ machinery ready. Thm 12.13 starts becoming provable
- **After Thm 12.12**: Frobenius structure availability, early §14 lemmas can start

### Dependency verification checklist

- [ ] §10 (M_α, M_σ) fully formalized
- [ ] §11 (Exceptional) fully formalized
- [ ] Hypothesis 11.1 Lean definition + characterization
- [ ] Prop 1.5 (A-invariant Hall) available in §1
- [ ] Prop 1.6(d) (Frattini + coprime) available in §1
- [ ] Lemma 4.5 (cyclic p-group) available in §4
- [ ] Maschke / Schur-Zassenhaus available (mathlib)
- [ ] Thm 10.2, Corollary 10.7, Lemma 10.12, 10.13 ready (§10)
- [ ] Thm 11.3, 11.5, 11.7 ready (§11)

---

## 未解決 / TODO

### 数学的な精査

1. **Thm 12.7 vs. 12.8 の completeness**: nonabelian vs. abelian Sylow p の split が complete か確認. 原文 L3217 "By (a)" の implicit case coverage を explicit に.

2. **Thm 12.12 の case analysis**: `C_E(S) = E` vs. `C_E(S) ≠ E` の分岐が exhaustive か. Proof では Q/Q₀ acting regularly on S の condition が critical だが、逆方向 (not regular) の処理が clear か.

3. **Cor 12.9 の非同型性**: "A₀ is not conjugate to A₁ in G" (12.9(b)) の証明が rank argument だが、nonabelian p-subgroup の existence が guaranteed される context を確認.

4. **τ₁ & τ₃ の interaction**: Lemma 12.18 は τ₁(M) に限定. τ₃(M) ≠ ∅ の場合の similar statement はあるか? L3454 では τ₁ only.

### Formalization-specific

1. **Naming convention**: τ₁, τ₂, τ₃ を Lean identifier に (e.g., `tau₁ M`, `Tau2_set M`). mmd での `\tau_{i}(M)` notation を Lean に上げる方法.

2. **Group A–C の import graph**: Subdirectory 分割の際、A_Structure → B_Tau2Case → C_Sigma の dependency が **linear chain か DAG か** を確認. DAG の場合 B & C の parallel formalization 可.

3. **Proof automation**: Lemma 12.1, 12.2 は rank calculation が repetitive. `omega` or `decide` で partial automation 可か.

4. **LTE との比較**: Lean Feit-Thompson project (2012–) での この section に対応部分があるか, notation/approach の参照価値.

### 下流への影響

1. **§13 前提の early validation**: Cor 12.10 (summary) が 13 で heavily used. 12.10 の formalization 後 early sanity check で §13 の first lemma を try-formalize.

2. **Thm 12.12 & §14 の timing**: Thm 12.12 (Frobenius) は Lemma 14.1 で引用. 14 の formalization 開始前に 12.12 の completeness check.

3. **App.C との sync**: Phase 2b Peterfalvi 開始時に, §12 の Thm 12.12–12.13 と App.C の correspondence を docstring で明文化.

---

## 統計サマリー

| 項目 | 数値 |
|------|------|
| mmd 行数 | 460 |
| 主要結果数 | 15 (+ 4 sub-corollaries = 19 total) |
| 群分け | A (4), B (8), C (7) |
| 予想 Lean 行数 | 2000–2200 |
| 平均 per-result | 100–140 行 |
| 推定 formalization 期間 | 4 week (1 person) |
| mathlib 新実装 | τ-partition, E definition, Thm 11.1 machinery |
| 下流引用 spots | §13 (13+), §14 (5+), §15 (2+) |
| ファイル数 (推奨) | 4 (3 modules + aggregate) |

---

## まとめ

BG §12 "The Subgroup E" は **局所解析の中核** で、M の complement E の精密構造を 460 行で確立する本文最大級の定理群. τ₂ case (12.5–12.12) が最重要で、そこで abelian vs. nonabelian Sylow p の split、M_σ の nilpotency、maximal subgroup の family structure などが secured される.

形式化では **2000+ 行 Lean** が予想され、3 ファイル分割 (A_Structure, B_Tau2Case, C_Sigma_Embedding) で conceptual clarity と module reusability を両立. Phase 2a 第 4 波の center piece として §10–§11 の直後に着手し、§13 と部分的に並列化可.

数学的には §12 単独で **局所解析教科書の 1 章相当** の深さを持つ. 形式化者は proof の key idea (Frattini, rank calculation, coprime action の clever use) を理解した上での implementation が critical.

---

*作成日: 2026-05-22*  
*出典: BG local-analysis.mmd L3023–3483, PDF pp.83–96*  
*参考: BG §10 (M_α, M_σ), §11 (Exceptional), §13 (Prime Action), App.C (Peterfalvi)*

