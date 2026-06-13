# BG §14 — Maximal Subgroups of Type P and Counting

> Lane F mini-roadmap. 正本ファイル = `OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting.lean`。
> mmd `references/bg/local-analysis.mmd` L3787–4158 (pp. 105–116)。

## 現状 (2026-06-14)

- **Lemma 14.1 = `msigma_structure_of_notMem_sigma_kappa` COMPLETE** (sorry-free + axiom-clean,
  commit `f84b42c6`)。S14 sorry **10 → 9**。
- 残り 9 = Prop 14.2 / Cor 14.3 / Thm 14.4 / Lemma 14.5 / Thm 14.7 / Cor 14.9 / Cor 14.10 /
  Cor 14.12 / Lemma 14.13。**すべて §13 (Lane G) に gate** (下記)。

## 依存マップ (なぜ 14.1 以外が止まるか)

§14 は BG Chapter IV の counting capstone で、§10–§13 のほぼ全結果に乗る。各結果の実依存:

| §14 結果 | 主依存 | 状態 |
|---|---|---|
| **14.1** (done) | Thm 12.5(a)(d) [§12 ✅] + Thm 3.7 [`S03c` ✅] | **無条件可 → 着地済** |
| 14.2 Prop | Lem 12.1, **Cor 13.11**, **Thm 13.5**, **Lem 13.12**, **Lem 13.7**, **Lem 13.13**, **Lem 13.6**, Thm 10.1(a), Cor 12.16, **Lem 14.1**, Thm 3.10(a), Lem 12.19, Lem 12.17 | **gated** |
| 14.3 Cor | **Prop 14.2(b)(c)**, Lem 14.1, Cor 12.10(e), Lem 12.11(a) | gated (14.2) |
| 14.4 Thm | **Thm 13.9**, Thm 10.1(b), Prop 12.15, **Cor 14.3**, Cor 12.6 | gated (13.9, 14.3) |
| 14.5 Lemma | **Thm 14.4**, **Thm 13.9** | gated (14.4) |
| 14.6 Lemma | Cor 14.3, Thm 14.4(c)(e), **Thm 13.9** | gated + **hard core** (missing-page 組合せ論) |
| 14.7 Thm | Prop 14.2, **Thm 13.9**, Cor 14.3, Lem 14.5, **Lem 14.6**, counting 不等式 | gated + hard |
| 14.9 Cor | Lem 14.5(b), Lem 14.6, Thm 14.7 | gated |
| 14.10 Cor | Lem 14.5, Thm 14.7, Cor 14.9 | gated |
| 14.12 Cor | Prop 14.2, **Thm 13.9**, Lem 14.11, Thm 14.7, Lem 14.1, Thm 12.5(e) | gated |
| 14.13 Lemma | Thm 14.4, **Thm 13.9**, Cor 12.14, Thm 14.7, Cor 12.9, Lem 12.1(g) | gated |

**funnel**: 14.3→14.13 はすべて **Prop 14.2** を経由する (14.4 は Cor 14.3 経由、Cor 14.3 は
Prop 14.2(b)(c) を直接使う)。さらに全結果が **Thm 13.9** (`sigma_disjoint_of_nonconjugate`,
S13 で sorried) に推移依存。

## ブロッカーの正体 (§13 = Lane G 領域)

§14 が依存する §13 結果の repo 状態 (`S13_PrimeAction.lean`):

- **sorried scaffold (存在・cite 可)**: Thm 13.5 (`E1_actsPrime`), Lem 13.6
  (`maximalContaining_eq_singleton_of_E1`), Lem 13.7 (`E1E3_actsPrime`), Lem 13.8
  (`forbidden_config_impossible`), **Thm 13.9** (`sigma_disjoint_of_nonconjugate`),
  Thm 13.10 (`E1_regular_on_E3_of_noncentralize`), Cor 13.11 (`E3_not_regular_consequences`)。
- **未記述 (statement すら無い)**: **Lemma 13.12**, **Lemma 13.13**。
  - **13.12** (mmd L3745): `p∈τ₁(M), P∈ℰ_p¹(E), q∈τ₂(M), A∈ℰ_q²(E), C_A(P)≠1 ⟹ C_{M_σ}(P)=1`。
    証明 = Thm 13.4 [✅] + Cor 12.6(a)(c)(e) [✅] + Lem 12.11 [✅] + Thm 12.5(e) [✅] +
    **Lem 13.6** [sorried]。
  - **13.13** (mmd L3765): `p∈τ₁∪τ₃(M), P∈ℰ_p¹(E), C_{M_σ}(P)≠1 ⟹ ∀M*∈𝓜(N_G(P)), p∈σ(M*)`。
    証明 = Lem 12.2 + **Thm 13.9** + **Cor 13.11** + **Lem 13.6** + Cor 12.10(c) + Cor 12.9(c) +
    **Lem 13.12**。
- 着地済 (sorry-free): Lem 13.1, Cor 13.2, Cor 13.3, Thm 13.4。

⟹ scaffold-cite で Prop 14.2 を書くにも **13.12/13.13 の statement が無い** ため、新規
forward axiom (hub/ユーザー承認制) を入れない限り着手不能。`LAUNCH.md` の「S13_* は編集禁止
(cite のみ)」も効く。

## 次手の選択肢 (ユーザー裁可待ち)

- **(A) §14 を pause、Lane G の §13 完成を待つ**。14.1 は merge 済。Lane F は別タスクへ。
  推奨理由: §14 の hard part (14.6 counting / 14.7 duality) は §13 全体に乗るので、§13 が
  axiom-clean になってから §14 を載せる方が faithful 検証が楽。
- **(B) forward-axiom scaffold-cite**。13.5–13.13 を Lane-F-local に axiom 化 (13.12/13.13 含む)
  + sorried 13.5–13.11 を cite して、Prop 14.2 → … → 14.7/14.10 の counting 本体を形式化。
  §13 完成時に de-axiom で unconditional 化。**新規 axiom はユーザー承認必須**。高労力・高構造価値、
  ただし結果は当面 not-axiom-clean。
- **(C) Lane G と調整** して 13.12/13.13 を G が先に追加 (S13 は G 領域)。

## Lemma 14.1 の faithful 化メモ (再利用)

- 旧 scaffold `not_typeP1_basic` は (i) `p∉σ`/`p∉κ` 仮説欠落で conclusion 偽、(ii) A を rank-1
  固定で τ₂ case (rank 2) を落としていた → unfaithful。
- 新 `msigma_structure_of_notMem_sigma_kappa`: 仮説 `hpπ : p∈piSet M`, `hpσ : p∉σ M`,
  `hpκ : p∉kappa M`、`A ∈ elemAbelianOfRank G p (pRank ↥M p)` (両 rank case 捕捉)。
  `|A| = p^{r_p}` ゆえ `|A|≤p² ⟺ r_p≤2` (§12 `pRank_M_le_two`)。BG の `M∉𝓜_{P₁}` は p の存在
  保証のみで proof 不要ゆえ drop。
- τ-case: `r_p=2 → p∈τ₂ → Thm 12.5(a)(d)`; `r_p=1 → p∈τ₁∪τ₃ → p∉κ で C=⊥ + 素数位数 A の
  FPF (A=⟨r⟩, 核は C_{M_σ}(A)=1) → Thm 3.7 `isNilpotent_of_normalizing_primeOrder_fixedPointFree``。
- 再利用技法: `A 可換 (IsElementaryAbelian) → A ≤ centralizer(A)` で Disjoint(M_σ,A) を hC から無料;
  `A = zpowers r` は `card_dvd_of_le` + `eq_of_le_of_card_ge`; FPF は `Commute.zpow_left`
  (hcomm は `Commute r n` 型で宣言、Eq だと dot-notation が Eq.zpow_left に落ちる)。
