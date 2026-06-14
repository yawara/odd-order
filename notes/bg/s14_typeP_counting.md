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

## 決定 (2026-06-14, ユーザー裁可) — **§14 PAUSE**

ユーザー裁可: **§14 を pause、Lemma 14.1 で区切る**。Lane G が §13 (13.5–13.13) を完成させて
から、axiom-clean な土台の上で §14 を再開する。forward-axiom scaffold-cite は採らない
(§14 の hard part 14.6/14.7 を未証明 §13 axiom の塔に載せるのを避け、faithful 検証を容易に保つ)。

**§14 再開の前提条件 (Lane G の §13)**:
- sorried 13.5 / 13.6 / 13.7 / 13.8 / 13.9 / 13.10 / 13.11 の discharge
- **未記述の Lemma 13.12 / 13.13 の追加** (statement = 上記「ブロッカーの正体」、証明依存も明記済)

これらが揃えば §14 再開時は **Prop 14.2 → Cor 14.3 → Thm 14.4 → Lemma 14.5/14.6 →
Thm 14.7 → Cor 14.9/14.10 → Cor 14.12/Lemma 14.13** の順で実証明できる (依存マップ参照)。
Lemma 14.6 (missing-page 組合せ論) と Thm 14.7 の counting 不等式
(|𝒞_G(Ẑ)| > ½|G|, mmd L4031–4045) が hard core。

(検討した代替案: (B) forward-axiom scaffold-cite / (C) Lane F を §13 へ再配置 — 不採用。)

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

## Lane H faithfulness 検証 + §13 非依存 API (2026-06-14)

H 再配置後の (a) faithful 化 + (b) §13 非依存補題のパス。mmd L3787–4158 と Lean surface を照合:

- **定義は完全 faithful** (BG L3805): `kappa` = {p∈τ₁∪τ₃ | ∃P∈ℰ_p¹(M), C_{M_σ}(P)≠1}、
  `IsTypeF`=κ空、`IsTypeP1`=κ=π(M)−σ(M)、`IsTypeP2`=κ≠π(M)−σ(M)。一致。
- **§13 非依存 API 追加** (commit `8e2f26e1`, sorry-free): 述語版 `isTypeP_iff_isTypeP1_or_isTypeP2` /
  `not_isTypeP1_and_isTypeP2` / `isTypeF_iff_not_isTypeP` 他 + 族版 `maximalTypePFamily_eq_union` /
  `…disjoint…` / `maximalTypeFFamily_eq_diff`。⟹ **M_P = M_P1 ⊔ M_P2、M_F = 𝓜 ∖ M_P** (§15/§16 の型場合分け基盤)。
- **定理 surface (14.2–14.13) は全て BG の TRUE partial consequence** (false なものは無し → Lean 修正不要):
  - 14.2/14.7/14.12: 多部分定理の部分 surface (true)。14.7(e) の `IsTISubset Ẑ Z` は
    **faithful** (IsTISubset A L = ∀g,(∃a∈A,gag⁻¹∈A)→g∈L = G 内 TI, 正規化 bound L=Z; BG「Ẑ TI of G, N_G(Ẑ)=Z」と一致)。
    14.7 は counting 不等式 |𝒞_G(Ẑ)|>½|G| と (a)(h) を surface から省略 (証明時に補完)。
  - **14.4 が最も divergent**: Lean surface は N(x)+型(f)= (IsTypeF N∨IsTypeP2 N) を束ね、
    **BG headline「R(x) は C_G(x) の normal Hall で ℳ_σ(x) に sharply transitive」を落としている**。
    この headline 内容は §16 の `RData`/`ConjSharplyTransitiveOn` + Theorem D に存在。
    ⟹ §13 着地後に 14.4 を証明する際、headline を 14.4 へ戻すか §16 と相互参照する設計判断が要る (要相談)。
  - 14.3: 結論を κ/τ₂ メンバシップ split で表現 — BG L3852 の 2-case (π(⟨x'⟩)⊆κ ∧ C_G(x)⊆M / τ₂分岐) と
    厳密一致か証明時に再確認 (C_G(x)⊆M が surface に無い)。
- **結論**: §14 surface は faithful-as-partial、false 無し、現時点で Lean 修正不要。実証明は §13 gate (pause 継続)。

### §15/§16 も照合完了 (2026-06-14, a→b→c の (a) 完了)
- **§15** (mmd L4166–4320): Lemma 15.1 / Thm 15.2 (1⊂M_F⊆M_σ⊆M'⊂M + M_F≠M_σ⟹P1 構造) / Cor 15.3–15.6 /
  Thm 15.7 (F(M) not TI ⟹ 3-case) / Thm 15.8 (FT) / Cor 15.9 — **全て BG の true surface (false 無し)**、
  多部分は partial。実証明は §14 経由で §13 gate。
- **§16** (mmd L4340–4562): Thm A–E + **Prop 16.1** + Thm I, II 照合。
  - **Prop 16.1 `proposition_type_classification` は faithful**: I↔𝓕, II↔𝓟₂, III∨IV↔(𝓟₁∧M_F≠M_σ),
    V↔(𝓟₁∧M_F=M_σ), (e)¬I↔M'=UM_σ, (f)M_F=M_σ↔I∨II∨V — BG L4478 と一致。
  - **🔑 14.4 headline の所在判明**: BG **Theorem D(3)** = 「C_M(x) は C_G(x) の Hall、normal complement R(x)
    が {M^g|x∈M^g} に sharply transitive」= §16 `RData`/`ConjSharplyTransitiveOn` に存在。
    ⟹ §14.4 surface が落とした headline は §16 Thm D に保持されており **lost ではない**。
    §13 着地後の設計判断 = 14.4 を Thm D 経由で cite するか headline を 14.4 に戻すか (機能的には D で足りる)。
  - **重要 (再調査不要)**: Type I–V は `GroupTheory.MaximalSubgroupType` で **Peterfalvi data (TypeIData 等) ベース定義**
    ⟹ Prop 16.1 / Thm I,II は BG-taxonomy ↔ Pf-type の実質 bridge であり **§13 非依存に proof 不可** (full §14–16 要)。
- **(b) §13 非依存 API 評価**: §14 = 型分類 API 着地済 (`8e2f26e1`)。**§15/§16 は §14 のような述語間関係構造を持たず**
  (FittingIsTI / MF / hatMsigma / RData / piStar はほぼ notation)、clean な §13 非依存 API は無し (trivia のみ)。
- **▶ 総括 (a→b→c)**: (a) §14–16 surface = 全て faithful・false 無し・Lean 修正不要 (検証完了)。
  (b) §13 非依存 API = §14 型分類のみ (§15/§16 は無)。 (c) 実証明 = 全て §13 (Lane F/G) gate。
  ⟹ **H の §13 非依存 runway は実質枯渇**。次の実質前進は §13 着地待ち。
