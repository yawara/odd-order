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

## ⚠ Faithfulness 再監査 (2026-06-14 cont., Lane H) — 上の (a)「false 無し」を**訂正**

上記 (a) の結論「§14 surface は全て faithful・false 無し」は **不正確**だった。BG mmd L3783–4160
(14.1–14.13 全文) と Lean surface を**逐 conjunct**照合した結果、複数の defect を検出。`sorry` 群は
build を通すので false statement でも検出されず、prior audit は part-level に留まり conjunct-level の
矛盾を見逃していた。**§15/§16 (Lane G) は §14 の sorried 定理を 0 cite (定義のみ使用) ゆえ、定理
statement の修正は G に波及しない** (grep 確認済) — ただし**定義 `sigmaSharp` は G が 9 箇所で使用**。

### 検出 defect 一覧 (重大度順)

1. **[高・cross-lane] `sigmaSharp` ≠ BG `M̃`**: `sigmaSharp M = sharpSubgroup M_σ = M_σ^#` (ℓ_σ=1 核)。
   BG `M̃ = {xx' | x∈M_σ^#, x'∈R(x)}` は R(x) (Thm 14.4) を要し ℓ_σ=2 twisted 元を含む = **未形式化**。
   旧 docstring は `sigmaSharp` を「M_tilde」と誤記。**G の §15/§16 が 9 refs で `sigmaSharp` を使用** ⟹
   G が M̃ のつもりで使っていれば subtle に不正。**R(x)/M̃ の形式化が §14 着地後の必須課題**。
   → docstring を実体 (M_σ^#) + M̃ 未形式化の警告に訂正済 (def は不変・G 非破壊)。

2. **[中] 14.2 `typeP_structure` に false conjunct**: `Msigma M ≤ normalizer (Kstar)` (= K*◁M_σ) は
   BG 7 部分 (a)–(g) に無く、**一般に偽**。反例: K=C_q が Heisenberg M_σ=p^{1+2} に a↦aʳ,b↦b,c↦cʳ で
   作用 → K*=C_{M_σ}(K)=⟨b⟩、aba⁻¹=bc∉⟨b⟩ ゆえ ⟨b⟩ 非正規 (prime action だけからは出ない)。
   → **除去済** (commit, 本セッション)。残 conjunct は (a)/(b1)/(c前半)/(d前半)/(g) の faithful partial。

3. **[中] 14.9 `nonidentity_covered_by_sigma_pieces` は as-stated で偽**: `sigmaConjugacySaturation =
   𝒞_G(M_σ^#)` で G^# を被覆と主張するが、BG は `𝒞_G(M̃)` で被覆。M_σ^# ⊊ M̃ ゆえ ℓ_σ=2 元
   (xx', x'∈R(x)^#) が**どの `𝒞_G(M_σ^#ⱼ)` にも入らず取りこぼし** → 被覆失敗。faithful 化は M̃ (gated) 必須。
   → docstring に「as-is で証明するな」と明記。

4. **[中] 14.3 `sigma_diagnostic` garbled**: (i) 仮説 `x'∈M` は BG では `x'∈C_M(x)` (centralize 欠落)。
   (ii) 分岐(1)の body `x'∈M_σ⊓C_G(x)` は、x' が σ'-元ゆえ σ-群 M_σ に入れず**矛盾** = BG の `x∈C_{M_σ}(K)`
   (i.e. `x∈M_σ⊓C_G(x')`) の **x↔x' 取り違え**、かつ `C_G(x)⊆M` を drop。(iii) 分岐(2)は `ℓ_σ(x')=1` と
   `𝓜(C_G(x'))={M}` を drop。→ 要再定式化 (証明時, gated)。docstring に明記。

5. **[低中] 14.4 `sigmaLength_one_centralizer_structure`**: headline (R(x) が C_G(x) の normal Hall・
   𝓜_σ(x) に sharply transitive) と (a)–(e) を drop。さらに part (f) (N∈𝓜_F∪𝓜_{P₂}) の
   **`|𝓜_σ(x)|>1` guard を落として無条件主張** ⟹ single-max + type-P₁ の場合に過剰主張の恐れ。
   headline は §16 Thm D (`RData`/`ConjSharplyTransitiveOn`) に保持。→ docstring 訂正 + 証明時に guard 再検討。

6. **[低中] 14.12 `typeP2_neighbor_is_typeF` 仮説過弱**: 任意 `U≤M, R≤U, R≠⊥` を取るが BG は
   U=Prop 14.2(a) の Hall (κ∪σ)'-factor、R=その U の Sylow。任意 U,R では結論 (M∩H=UK 等) 不成立。
   → docstring に正しい仮説を明記 (tighten は証明時)。

### faithful なもの (修正不要・確認済)
- **14.13** (a) は faithful partial ((a) 捕捉, (b) defer); **14.7** statement は OK (counting 不等式
  `|𝒞_G(Ẑ)|>½|G|` は kernel `half_lt_one_sub_inv_mul` に分離・証明で使用、TI 条項は faithful);
  **14.10** OK; **`zTilde`** = Ẑ = Z−(K∪K*) faithful (K⊔K*=K×K*=Z, coprime); 14.1 (done) faithful;
  型分類 API (isTypeP_iff_… 等) faithful。

### 本セッションの修正 (commit) — docstring + 1 statement
- 14.2: false conjunct 除去 (statement); 14.2/14.3/14.4/14.5/14.9/14.12 + `sigmaSharp` docstring を
  BG 逐 conjunct 照合の正確版に。leaf build green (3095 jobs, sorry 警告のみ)。
- **gated ゆえ未修正 (要 §13 着地 + 設計判断)**: M̃/R(x) 形式化 (→14.5(a)(c)/14.7(e)/14.9 を M̃ で再定式)、
  14.3 再定式化、14.12 仮説 tighten、14.4 headline 復元 vs §16 cite。**M̃ 形式化が §14→§15/§16 の
  faithfulness の要** ⟹ hub/G と要調整 (`sigmaSharp` 共有のため)。
