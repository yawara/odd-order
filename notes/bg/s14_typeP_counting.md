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
| 14.5 Lemma | **Thm 14.4**, **Thm 13.9** | **Lean M_σ# 版は ✅ 13.9 cite で実証明 (2026-06-14)**; BG 全 (a)(c) は 14.4 gate |
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

## 🔓 13.9 単独で解禁される §14 結果 (2026-06-14, Lane H)

「13.9 (`sigma_disjoint_of_nonconjugate`) **だけ**が landing したら何ができるか」の精査:

- **✅ Lemma 14.5 = `sigmaConjugacy_disjoint_of_nonconjugate` — 本セッションで実証明済** (13.9 cite)。
  鍵: Lean の 14.5 は弱い **M_σ# 版** (`sigmaConjugacySaturation = 𝒞_G(M_σ#)`) ゆえ、M̃/R(x) 機構不要で
  **σ(M)∩σ(N)=∅ (13.9) だけ**で出る。証明 = g が t∈M_σ#・s∈N_σ# 両方の共役なら t~s ⟹ orderOf 一致 ⟹
  素因子 p∈σ(M)∩σ(N)=∅ 矛盾 (`Msigma_isPiGroup` で M_σ が σ-group, `SemiconjBy.orderOf_eq` で共役不変)。
  S14 に `S13_PrimeActionTransition` import 追加 (13.9 は upstream PrimeAction でなく Transition 在)。
  ⟹ F が 13.9 を埋めれば 14.5 は**自動 unconditional**。S14 genuine sorry **9 → 8**。
- **それ以外は 13.9 単独では不可**: 14.2 は 13.11/13.12/13.13 (13.12 未記述) に直接依存; 14.3→14.13 は
  全て **14.2 経由** (14.4 も Cor 14.3→14.2)。⟹ 13.9 の次は **13.11 + 13.12/13.13** が揃って初めて 14.2 解禁、
  そこから funnel 全体が動く。**13.9 単独の戦果は 14.5 一本** (それでも genuine sorry を 1 減らし de-risk)。

### 本セッションの修正 (commit) — docstring + 2 statement (1 除去 + 14.5 実証明)
- 14.2: false conjunct 除去 (statement); 14.2/14.3/14.4/14.5/14.9/14.12 + `sigmaSharp` docstring を
  BG 逐 conjunct 照合の正確版に。leaf build green (3095 jobs, sorry 警告のみ)。
- **gated ゆえ未修正 (要 §13 着地 + 設計判断)**: M̃/R(x) 形式化 (→14.5(a)(c)/14.7(e)/14.9 を M̃ で再定式)、
  14.3 再定式化、14.12 仮説 tighten、14.4 headline 復元 vs §16 cite。**M̃ 形式化が §14→§15/§16 の
  faithfulness の要** ⟹ hub/G と要調整 (`sigmaSharp` 共有のため)。

## ✅ Faithful reformulation 着地 (2026-06-15, Lane H)

§13 gate 待ちの holding-pattern として、上記「gated ゆえ未修正」のうち **§13 非依存 + §14 内で完結する 3 件**
を BG 原文 (mmd L3852/L3869/L4107) 逐条照合で faithful 化 (statement のみ; proof は §13 gate 継続で sorry 維持)。
3 定理とも **下流 0 cite** (grep 確認) ゆえ安全。full build green (3813 jobs, AxiomsCheck OK)。S14 実 sorry **8 で不変**。

- **14.3 `sigma_diagnostic`** (garbled → faithful): `x ↔ x'` 取り違え修正 (旧 branch 1 は `x'∈M_σ` という不能を主張)、
  欠落していた「x' が x を中心化」仮説 (`hx'cent`) + `x'≠1` 追加、結論を BG 通り
  `(π⟨x'⟩⊆κ(M) ∧ C_G(x)⊆M) ∨ (π⟨x'⟩⊆τ₂(M) ∧ ℓ_σ(x')=1 ∧ 𝓜(C_G(x'))={M})` に。
  `ℓ_σ(x')` は `D : SigmaDecompositionData` の `D.length x'=1` で carry (14.4/14.13 と同 convention、新 D 引数追加)。
  `𝓜(C_G(x'))={M}` = `maximalSubgroupsContaining (centralizer {x'}) = {M}`。
- **14.4 `sigmaLength_one_centralizer_structure`** (over-claim 除去): N/型構造を **`1 < (𝓜_σ x).ncard` で guard**
  (single-max 時は R(x)=1・N(x) 無し ⟹ 旧無条件主張は過剰)。`R(x)=C_{N_σ}(x)=M_σ(N)⊓C_G(x)` を具体化 (part a)、
  `∃! N` (一意)、parts (a)(c)(d)(e)(f) を `∀ M∈𝓜_σ(x)` 込みで記録。
  **§16 へ defer**: headline「R(x) は C_G(x) で normal・𝓜_σ(x) に **sharply transitive**」+ part (b) は
  §16 `RData`/`ConjSharplyTransitiveOn`/Thm D に verbatim 保持 ⟹ 証明時に §16 cite (§14→§16 import は循環ゆえ restate せず)。
- **14.12 `typeP2_neighbor_is_typeF`** (仮説 tighten): 旧「任意 U≤M, R≤U, R≠⊥」→ BG 通り
  `U` = Prop 14.2(a) の **abelian Hall (κ(M)∪σ(M))'-factor** (`hU`+`hUab`)、`R` = U の **Sylow r-subgroup**
  (`IsHallSubgroup {r}`, `r∈π(U)`)。結論は faithful partial 維持 (H∈𝓜_F, U⊆H_σ, M⊓H=U⊔K; 残条項 defer)。

**§14 で faithful 化できなかった残**:
- **14.9 `nonidentity_covered_by_sigma_pieces`**: faithful 化に BG `M̃` が必須だが `M̃`=§16 `tildeM M R`
  (R carrier 付き) に既存 ⟹ §16 が §14 を import するため §14 側で `M̃` 参照は **循環で不可**。
  faithful 版 (M̃ 被覆) は §16 領域 (Lane G) で書くべき。現 §14 surface は docstring で「as-is で証明するな」と警告済 (不変)。
- 14.2/14.7: 多部分定理の TRUE partial surface (false 無し)、reformulation 不要。`Subgroup.IsCommutative` は
  mathlib に無く `∀ a∈U,∀ b∈U, a*b=b*a` で可換性を表現 (再利用メモ)。

## 🟢 Thm 13.9 landed → Lemma 14.5 green + Prop 14.2 funnel prep (2026-06-15, Lane H)

**Thm 13.9 (`sigma_disjoint_of_nonconjugate`) が §13 (Lane F) で landed** (S13_PrimeActionTransition
の残 sorry は @2344=13.10 / @2355=13.11 のみ、13.9@2224 は sorry-free)。⟹ 13.9 を cite して証明済の
**Lemma 14.5 (`sigmaConjugacy_disjoint_of_nonconjugate`) が自動 unconditional 化**。
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (sorryAx 無し) を確認 → **AxiomsCheck 登録**
(commit `b6c02d4f`, 14.1 の隣)。**14.1 に続く 2 つ目の green な §14 結果**。

### §13 各結果の axiom 状態 (#print axioms で実測, 2026-06-15)
- **axiom-clean (sorryAx 無し)**: 13.5 `E1_actsPrime` / 13.6 `maximalContaining_eq_singleton_of_E1` /
  13.7 `E1E3_actsPrime` / 13.9 `sigma_disjoint_of_nonconjugate` / `cyclicSylow_actsPrime`。
- **残 sorry**: 13.10 `E1_regular_on_E3_of_noncentralize` (@2344, 着地間近) / 13.11
  `E3_not_regular_consequences` (@2355) / S13_PrimeAction @411 (13.4 per-q core の **orphan**, 14.2 path 外) /
  **13.12 / 13.13 (statement 未記述)**。

### Prop 14.2 依存マップ (mmd L3821-3850 の証明を逐条分解) — 次の §14 keystone
14.2 が landing すれば 14.3→14.13 funnel 全体が動く。各 part の cite と repo 状態:

| 14.2 part | BG 証明の cite | repo 状態 |
|---|---|---|
| setup | Lem 12.1 (E,E₁,E₂,E₃; E₂E₃◁E, E₁ cyclic) | ✅ `exists_subgroupESetup` |
| (a)(b1) E₃≠1 非regular 分岐 | **Cor 13.11** (`E3_not_regular_consequences`) | ⏳ sorry @2355 |
| (a)(b1) κ⊆τ₁ 分岐 | **Thm 13.5**✅ + **Lem 13.12**❌ + **Lem 13.7**✅ + Cor 12.10(b)✅ | **13.12 未記述** |
| (b2)(c) | **Lem 13.13**❌ + **Lem 13.6**✅ | **13.13 未記述** |
| (d) | (c) + **Thm 10.1(a)**✅ | (c) gate |
| (e) | (b2) + **Lem 13.6**✅ | (b2) gate |
| (f) | (d) + Cor 12.16✅ | (d) gate |
| (g) IsTypeP2 | Lem 14.1✅ + Thm 3.10(a)✅ + Lem 12.19✅ + Lem 12.17✅ | setup(a) gate |

### 結論: §14 funnel の真の gate = **13.11 + 13.12 + 13.13**
- 非-§13 依存 (§12/§10/§3/14.1) は **全て repo に存在・利用可** ⟹ 13.11/13.12/13.13 が揃えば 14.2 は
  純 **§13-cite assembly** (新規 §12 等の API 整備は不要)。
- **13.12 / 13.13 が long pole**: statement 未記述 (F の S13 領域, mmd L3745/L3765 に spec, 上「ブロッカー
  の正体」参照)。これが無いと 14.2 の**どの part も書けない** (全 part が setup(a)=13.12 経由 or (b2)(c)=13.13 に
  entangle、部分先行も不可)。
- 13.10 着地間近 → corollary 13.11 も近い。**13.11 単独では 14.2 不可** (κ⊆τ₁ 分岐が 13.12 gate)。

### H の次手
1. **現状**: 13.9 landing の戦果 (14.5 green) を回収済。これ以上の §14 proof は 13.11+13.12+13.13 待ち。
2. 13.12/13.13 landing 後: 上記マップ通り 14.2 assemble → 14.3 (faithful 化済) → 14.4 → … funnel 駆動。
3. ⚠ 13.12/13.13 は **F 領域** (H は cite のみ)。long-pole 認識を hub/ユーザーに共有 (本セッション)。

## 🧩 §14 signature interface 完成 (2026-06-15, Lane H) — Lane G の §15/§16 unblock 用

ユーザー指示: G が §15/§16 を §14 に対して書けるよう、H の §14 **signature を先に完成** (proof は sorry のまま)。
BG §14 全結果 (14.1–14.13) と S14 surface を照合し、**欠けていた signature を補完**。full build green (3816 jobs)。

### 追加した signature (faithful, sorry, §14-statable = R(x) 不要)
- **Cor 14.8 `typeP1_conjugate_and_typeP_twoClasses`** (mmd L4065): 𝓜_{P₁} は全共役 + 𝓜_𝓟 非空なら丁度
  2 共役類。型分類 (§16 Prop 16.1 / Thm I,II) が要する。Thm 14.7(f)(g) から従う (gated)。
- **Lem 14.11 `exists_maximal_of_typeF_notMem_fitting`** (mmd L4086): M∈𝓜_F, E=M_σ complement, q∈π(E),
  Q∈ℰ_q¹(E), Q⊄F(E) ⟹ ∃M* [(q∈τ₂(M*) ∧ 𝓜(C_G(Q))={M*}) ∨ (q∈κ(M*) ∧ M*∈𝓜_{P₁})]。Cor 14.12 が使う。
  `F(E)` = `OddOrder.BG.Ch2.S08.fittingInG E` (Fitting を G 内 Subgroup で取る版; 再利用メモ)。

### §14 に**追加しなかった** = §16 (Lane G) 領域 (R(x)/M̃ gated)
- **Lem 14.6 `各 g∈G^# は 2 条件の exactly one`** (mmd L3945): 条件(1)が `g=xx', x'∈R(x)` で **R(x) 必須**
  ⟹ 14.9 と同じく §14 では循環不可、faithful 版は §16 `tildeM` に対して書く。**issue 2005 に 14.6 も追記**。
- 14.5(c) (count `|𝒞_G(M̃)|=(|M_σ|−1)|G:M|`) も R(x) 要 ⟹ §16 (Thm E が cite)。

### §14 signature interface の現状 (G が cite 可能な surface)
14.1✅(proved) / 14.2✅ / 14.3✅(faithful) / 14.4✅(faithful) / 14.5✅(b, proved) / **14.6→§16** /
14.7✅ / **14.8✅(new)** / 14.9✅(surface; faithful版→§16) / 14.10✅ / **14.11✅(new)** / 14.12✅(faithful) / 14.13✅。
⟹ **§16 が直接 cite する 14.2/14.4/14.5/14.7/14.9/14.12 は全て present**、加えて型分類用 14.8 も present。
G は §14 を sorried cite して §15/§16 を unblock 可能 (§14 proof landing で自動 unconditional 化)。

## 🚧 Prop 14.2 実装プラン (2026-06-15, Lane H) — 13.12/13.13 landing 後の funnel keystone

**unblock 完了** (commit `6409a53e`): F が 13.12/13.13 statements を landing (issue 2006, 私の draft 採用) +
13.10/13.11 complete (S13_PrimeActionTransition 残 sorry = 13.12/13.13 本体のみ) + ユーザー裁可 scaffold-cite
ポリシー。さらに 14.2 の WLOG 前提を整備: `kappa_subset_tau1_union_tau3` (S14) + `exists_subgroupESetup_with_le`
public 化 (S12, K≤E な setup を与える)。⟹ **14.2 を scaffold-cite で書ける状態**。

### ⚠ 署名 subtlety (要修正 — 着手時 first)
現 `typeP_structure` の `hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)` は **K≤M を強制しない**
(`K.subgroupOf M` = K⊓M を ↥M 内で見たもの)。BG では K は M の Hall κ-subgroup ⟹ **`(hKM : K ≤ M)` 仮説を
追加**するか、`K⊓M` で進める。`hU` の U も同様。下流 0 cite ゆえ署名追加は安全。

### 証明アーキテクチャ (BG mmd L3832-3850 → Lean)
```
classical
-- K は σ'-subgroup (Hall κ, κ⊆τ₁∪τ₃⊆σ')
have hK_pi : IsPiSubgroup (sigma M)ᶜ K := ...  -- IsHallSubgroup→IsPiSubgroup + kappa_subset + tau⊆σ'
obtain ⟨E,E₁,E₂,E₃, hsetup, hKE, hE_pi⟩ := exists_subgroupESetup_with_le hG hM hKM hK_pi  -- K≤E
by_cases hτ3 : (kappa M ∩ tau3 M).Nonempty
· -- E₃≠1 ∧ E₃ non-regular ⟹ Cor 13.11: E₁≠1, E=E₁E₃, ActsPrimeOn M_σ E, ∀X∈ℰ¹(E) ◁E。K=E (U=1)
· -- κ⊆τ₁ ⟹ κ=τ₁ (E₁ prime, Thm 13.5)。WLOG K=E₁。K regular on U=E₂E₃ (Lem 13.12+13.7)。U=[U,K]=E' abelian (12.10b)
```
**conjunct → cite map**:
| conjunct | cite |
|---|---|
| (1) `ActsPrimeOn M_σ K` | case-τ₃: Cor 13.11(c); case-τ₁: Thm 13.5 (`E1_actsPrime`) + WLOG K=E₁ |
| (2) `Kstar≠⊥` | K prime-not-regular on M_σ ⟹ Lem 13.13 (`mem_sigma_of_tau1_tau3_centralize`)+13.6 |
| (3) `N_M(X)=K⊔Kstar` (b1) | Lem 13.6 (`maximalContaining_eq_singleton_of_E1`) + 13.13 |
| (4) `Kstar⊓M^g=⊥` (d) | (c) + Thm 10.1(a) |
| (5) IsTypeP2⟹σ=β,|K|=q,TI (g) | Lem 14.1 + Thm 3.10(a) + Lem 12.19 + Lem 12.17 |

### ❗ 要 transport machinery (case-τ₁ の WLOG K=E₁)
K (Hall κ=τ₁ of M) と E₁ (Hall τ₁ of E) は M 内共役 (K=E₁^m, m∈M)。`ActsPrimeOn` 等を E₁→K へ transport 要:
- **`ActsPrimeOn` conjugation-invariance** (`ActsPrimeOn M_σ E₁ → ActsPrimeOn M_σ (E₁^m)` for M_σ◁M, m∈M)
  = `def ActsPrimeOn N X = ∀g∈X#, fixedByElement N g = fixedBy N X` の共役不変性。§13-independent、新規補題。
- Hall τ₁ subgroup の M 内共役 (`hall_conjugate` / IsHallSubgroup conjugacy)。
- あるいは `exists_subgroupESetup_with_le` が **E₁=K** を直接与えるよう精査 (K≤E + K Hall τ₁ of E ⟹ E₁=K の取り方)。

### 着手順序 (次セッション)
1. 署名修正 (K≤M, U≤M 追加)。2. `hK_pi` (K σ'-subgroup) 補題。3. setup 取得 + case split (compile)。
4. case-τ₃ 分岐 (Cor 13.11 直 cite、WLOG 不要) を先に完成。5. ActsPrimeOn-conj 補題 → case-τ₁。6. conjunct 2-5。

### 進捗 (2026-06-15 loop): opening COMPLETE + 核補題の特定
- **✅ 1-3 着地** (commit `3fb80769`): 署名に K≤M 追加 + `kappa_subset_sigmaCompl` + `hK_pi` +
  `exists_subgroupESetup_with_le` で setup 取得 + κ∩τ₃ case split が compile。残 = 2 branch sorry。
- **✅ 14.7(h) 露出** (commit `1243d4c6`, issue 8006): G の §15 cascade unblock。
- **F status (同期済)**: **Lemma 13.12 proof COMPLETE** (`c3860c52`, sorry-free)。13.13 のみ残 sorry。
  ⚠ **F が 13.12/13.13 に `[Fact p.Prime]` (13.12 は `[Fact q.Prime]` も) 追加** (tau1/tau2 が
  pRank ベースで素数性を含まないため)。**14.2 case-τ₁ から cite 時は τ-prime の Fact 供給要** (π(...) 由来)。
- **🔑 両 branch の共通核 = `C_{M_σ}(P)` の M-共役不変性** (`Msigma M ⊓ C(P^m) ≠ ⊥ ↔ … ⊓ C(P) ≠ ⊥`,
  m∈M): κ の ∃→∀ upgrade (BG L3807「all such P conjugate」) + case-τ₃ の E₃-非regular 導出
  (κ-witness を E₃ へ) + case-τ₁ の WLOG K=E₁ の全てに要る。**API map**: `smul_inf` (Pointwise:513) ✓ /
  `le_normalizer_opiCoreInG (sigma M) M` (M≤N(M_σ)) ✓ / `MulAut.conj m • M_σ = M_σ` (m∈N, MulAut版
  normalizer-fixes 要特定) / `centralizer (conj m • P) = conj m • centralizer P` (要特定) /
  `conj m • X = ⊥ ↔ X=⊥`。**pin 済 API**: `conj_smul_eq_self_of_mem_normalizer` (GroupTheory/
  AInvariantPiSubgroups:120, m∈N→conj m•H=H) / `centralizer_map_conj` (S03f_Prelim:818,
  `centralizer(K.map conj g)=（centralizer K).map conj g`) / `le_normalizer_opiCoreInG (sigma M) M`
  (M≤N(M_σ)) / `Subgroup.smul_inf` (Pointwise:513) / bot は injectivity (`conj m⁻¹•(conj m•X)=X`)。
  **⚠ form bridge**: `centralizer_map_conj` は `.map (conj g).toMonoidHom` 形、`smul_inf` は `•` 形 →
  `MulAut.conj m • P = P.map (conj m).toMonoidHom` の bridge (rfl か要 `pointwise_smul` 補題) で統一要。
  次イテレーションで `Msigma_inf_centralizer_conj_ne_bot` を建てる → 両 branch tractable に。
- **8004/8005 = G 領域** (H 非該当); 8004(i) は 14.7(h) 露出で迂回不要に。

### ⚠ 核補題 `Msigma_inf_centralizer_conj_ne_bot` の friction (2026-06-15 loop, attempt 1 → revert)
**両アプローチとも pointwise-conjugation の form friction で loop fragment 内では未完。dedicated pass 推奨。**
- **pointwise approach (blocked)**: `hcentconj : centralizer(↑(conj m•P)) = conj m • centralizer P` を
  `rw [pointwise_smul_def, pointwise_smul_def, S03f.centralizer_map_conj]` で狙うが、`pointwise_smul_def` は
  `S.map (toMonoidEnd _ _ a)` 形、`centralizer_map_conj` は `K.map (conj g).toMonoidHom` 形で **syntactic 不一致**
  (defeq だが rw 不可)。`toMonoidEnd (MulAut G) G (conj m) = (conj m).toMonoidHom` の bridge 補題が要る。
- **membership approach (推奨・API 特定済)**: `Subgroup.ne_bot_iff_exists_ne_one.mp h` で x∈M_σ⊓C(P), x≠1 を取り、
  `m*x*m⁻¹` が M_σ⊓C(conj m•P) の非自明元と示す。3 sub-goal:
  (1) `m*x*m⁻¹∈M_σ`: `(Subgroup.mem_normalizer_iff.mp hmN x).mp hxMσ` (hmN=`le_normalizer_opiCoreInG (sigma M) M hmM`)。
  (2) `m*x*m⁻¹∈C(conj m•P)`: `mem_centralizer_iff` → y∈↑(conj m•P) を
  `Subgroup.mem_pointwise_smul_iff_inv_smul_mem` で m⁻¹*y*m∈P に落とし、hxC で x が中心化 → group 代数で
  `(m*x*m⁻¹)*y=y*(m*x*m⁻¹)`。(3) `m*x*m⁻¹≠1`: x≠1 + conj 単射。残 friction = (2) の group 代数 + (3)。
- **判断**: 14.2 の深い conjugacy 内部 (両 branch) は loop 25min fragment では API friction で非効率。
  **opening (3fb80769) + 14.7(h) 露出は landing 済**。深い branch proof は **dedicated focused session** か、
  まず membership 版核補題を 1 本完成させてから fragment 駆動が良い。
- **✅ 核補題 landing (084533cd)**: `Msigma_inf_centralizer_conj_ne_bot` 完成 (membership 版; バグは
  ≠1 sub-goal の循環 rw、MulAut API は inv_smul_eq_iff/conj_apply で通った)。§13 funnel 全 complete
  (13.5-13.13, S13 sorry 0) ⟹ 14.2 完成時 unconditional。

### 🗺 case-τ₃ / case-τ₁ branch 詳細プラン (2026-06-15) — dedicated session 向け
**両 branch とも深い Sylow/Hall/conjugacy machinery を要す (loop fragment 非効率と確認)。** 構造:

**共通の鍵 = κ の ∃→∀ upgrade** (BG L3807): `p∈κ(M) ⟹ ∀P∈ℰ_p¹(M), C_{M_σ}(P)≠1`。
証明 = p∈κ⊆τ₁∪τ₃ で `r_p(M)=1` → **cyclic Sylow p** (odd, rank 1) → 各 Sylow の order-p 部分群一意 →
全 ℰ_p¹(M) は M-共役 → 核補題 `Msigma_inf_centralizer_conj_ne_bot` で C 不変 → 全 P で C≠1。
**要 machinery**: `r_p=1 ⟹ cyclic Sylow` (§12 τ-classification?) + `cyclic Sylow ⟹ order-p subgroup 一意`
+ Sylow 共役。**未特定の repo helper** = ここが最大の friction。

**case-τ₃** (`(kappa M ∩ tau3 M).Nonempty`):
1. `E₃≠⊥`: p∈τ₃ ⟹ p∣|E| (E=σ'-complement, p∈σ') ⟹ p∣|E₃| (E₃ Hall τ₃) ⟹ ≠⊥。要 E-setup card facts。
2. `E₃ 非regular on M_σ`: κ∩τ₃ の p の witness P (∃→∀ upgrade で E₃ 内 rank-1 に転送) ⟹ ∃z∈E₃#, C_{M_σ}(z)≠1。
   **逆向き (E₃ 非reg ⟹ κ∩τ₃) は EASY** (z∈E₃ 直接 κ-witness, 共役不要) — 等価性 lemma 化なら逆向き活用。
3. `Cor 13.11` (`E3_not_regular_consequences` hG hsetup hE3 hreg) → E=E₁⊔E₃, ActsPrimeOn M_σ E, ∀X∈ℰ¹(E)◁E。
4. `K=E`: E₂=1 (13.11 の E=E₁⊔E₃ から) ⟹ κ=τ₁∪τ₃=π(M)−σ(M) ⟹ K(Hall κ)=E。要 Hall 一意性。
5. conjunct 1 (ActsPrimeOn K) = 13.11 の ActsPrimeOn E + K=E。他 conjunct も K=E で。

**case-τ₁** (`¬(kappa M ∩ tau3 M).Nonempty` ⟹ κ⊆τ₁):
1. `κ=τ₁`: κ⊆τ₁ + (E₁ prime on M_σ by Thm 13.5 `E1_actsPrime`) で τ₁⊆κ。
2. WLOG `K=E₁`: K(Hall κ=τ₁) と E₁(Hall τ₁ of E) は M-共役 → 核補題等で conclusion 転送。
3. `K=E₁ regular on U=E₂E₃` (Lem 13.12 `Msigma_centralizer_eq_bot_of_tau1_tau2` + Lem 13.7 `E1E3_actsPrime`)。
4. `U=[U,K]=E'` abelian (Cor 12.10(b))。conjuncts。

**▶ 推奨**: branch proof は cyclic-Sylow/Hall-共役 helper の特定が要で multi-hour。loop は clean piece
(opening/核補題/14.7(h)/kappa helpers) を抽出済。**dedicated session で ∃→∀ upgrade を起点に駆動**が効率的。

### ✅ K=E の正しい根拠を BG 原文で確定 + 土台 helper landing (2026-06-15 loop)
**`K=E` は BG mmd L3838 が verbatim で "Then K=E" と明示** (case-τ₃)。当初「P1 限定では?」と疑ったが
**誤り**で、case-τ₃ では常に K=E。**cyclic-Sylow machinery は K=E にも不要**(上記旧プランの「最大の friction」
は霧消)。正しい chain (原文の "(a) and (b1) are clear" を展開):
1. **C_{M_σ}(E) ≠ 1**: E prime on M_σ (Cor 13.11) ＋ E₃≤E 非regular ⟹ ∃ x∈E₃#, C_{M_σ}(x)≠1。
   prime作用で全 g∈E# に `C_{M_σ}(g)=C_{M_σ}(E)` ⟹ C_{M_σ}(E)≠1。
   **✅ landing 済 (helper `Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular`, S14)**: 引数
   `(hEprime: ActsPrimeOn (Msigma M) E) (hE3le: E₃≤E) (hreg: ¬ActsRegularlyOn (Msigma M) E₃)` →
   `Msigma M ⊓ C(E) ≠ ⊥`。証明 = by_contra/push_neg で witness 抽出 + `hEprime x` の等式 + `fixedBy_def`。
   (これは **Kstar≠1 conjunct そのもの** にもなる: K=E 後 Kstar=C_{M_σ}(K)=C_{M_σ}(E)。)
2. **π(E) ⊆ κ(M)** (= κ⊇π(E)): 各 p∣|E| につき rank-1 P=⟨g⟩≤E (order p) を取り、prime作用で
   `C_{M_σ}(P)=C_{M_σ}(g)=C_{M_σ}(E)≠1` ⟹ κ-witness 成立。p∈τ₁∪τ₃ は **E₂=⊥ ⟹ r_p(M)≠2** から
   (p∣|E|⟹r_p∈{1,2}; E₂=⊥ で τ₂ 排除 ⟹ r_p=1 ⟹ τ₁ or τ₃)。
3. **E₂=⊥**: hEeq `E=E₁⊔E₃` ＋ E₂ Hall τ₂(M) of E。π(E₁⊔E₃)⊆τ₁∪τ₃ (E_i は τ_i-group) ＋ τ₂ 互いに素
   ⟹ |E₂| の素因数なし ⟹ E₂=⊥。**(注: Cor 13.11 内部 `hE2:E₂=⊥` は return されないので S14 で再導出要)**。
4. **E は Hall κ(M) of M**: π(E)⊆κ (step 2) ＋ [M:E]=|M_σ| が σ-number で κ⊆σ' ゆえ κ と互いに素
   ⟹ `E.subgroupOf M` が Hall κ(M)。
5. **K=E**: K≤E (setup) ＋ K,E とも Hall κ(M) ⟹ |K|=|E| ⟹ `Subgroup.eq_of_le_of_card_ge` 等で K=E。
6. **U=1** (原文 "let U=1"): a/b1 の U は trivial。conjunct (a) の "regular on U" は U=⊥ で自明。

**▶ 次 fragment 順**: (3) E₂=⊥ helper → (2) π(E)⊆κ (helper, step1 helper を消費) → (4) E Hall κ →
(5) K=E。各 build-green の verified step。K=E 後は 5 conjuncts を Cor 13.11 出力 + K=E で組立
(conjunct1=hEprime+K=E, conjunct2=step1 helper, 他は §13 cite)。**landing 済 = step1 helper のみ; 残 5 step**。

### ✅✅ K=E (case-τ₃) COMPLETE + conjunct (a)/(K*≠1) landing (2026-06-15 loop, K=E milestone)
**case-τ₃ の linchpin `K=E` を verified** (commit 後述)。**E₂=⊥ の明示導出は不要だった** — 当初プランの
step4「E Hall κ」は **既存 `IsHallSubgroup.card_dvd_of_isPiGroup`(Isaacs Ch03 Main:1582) で card 経路に短絡**:
- step2 `mem_kappa_of_mem_primeFactors_card_E` で `π(E)⊆κ(M)` ⟹ `E.subgroupOf M` は `Ch03.Subgroup.IsPiGroup (kappa M)`。
- `hK.card_dvd_of_isPiGroup hEpi` : `|E.subgroupOf M| ∣ |K.subgroupOf M|` ⟹ (card_congr で) `|E| ∣ |K|`。
- `K≤E` (setup hKE) ⟹ `|K| ∣ |E|` ⟹ `Nat.dvd_antisymm` で `|E|=|K|` ⟹ `Subgroup.eq_of_le_of_card_ge hKE` で **K=E**。
- ⟹ **正規性不要・Hall 共役不要・E₂=⊥ 明示不要**。witness x は hreg から by_contra/push_neg で抽出。
- **conjunct (a)** ActsPrimeOn K = `rw[K=E]; exact hEprime`。**conjunct K*≠1** = `rw[hKstar,K=E]` + step1 helper。
- **残 = conjunct (b1)/(d)/(g) + case-τ₁** (各 scoped sorry, BG lemma 明記):
  - (b1) `N_M(X)=K⊔Kstar` (∀X∈ℰ¹(K)): BG「clear」だが Lemma 13.13/13.6 wiring 要。
  - (d) `Kstar∩M^g=⊥` (g∉M): Theorem 10.1(a)。
  - (g) TypeP2 ⟹ σ=β/|K|素数/M_σ nilpotent TI: Thm 3.10(a)/Lem 12.19/12.17。
  - case-τ₁: κ=τ₁, WLOG K=E₁ (F の issue-7000 ∃→∀ upgrade leaf 着地後に cite), Lem 13.12/13.7, Cor 12.10(b)。
- **hub LAUNCH (2026-06-15) と整合**: 「Prop 14.2 = 既存 machinery の assembly」を実証。F の issue-7000 leaf は
  case-τ₁ の WLOG 用 (case-τ₃ は本ループで自己完結)。

### ✅ conjunct (d) COMPLETE + 🛑 残 conjunct の obstacle 確定 (2026-06-15 loop)
- **✅ (d) `Kstar∩M^g=⊥` landing** (commit `4af679bc`): (c) helper
  `maximalContaining_centralizer_of_le_Msigma_centralizer_E` + **Theorem 10.1(e)**
  (`OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma` の `.2.2.2.2`: X≤M ∧ C_G(X)≤M ∧ conj g⁻¹•X≤M ⟹ g⁻¹∈M)。
  rank-1 X は Cauchy で抽出、X≤M^g ⟹ conj g⁻¹•X≤M は `pointwise_smul_le_pointwise_smul_iff`+smul 合成。
  ⚠ motive-not-type-correct (w が Kstar 依存) は等式 `hKstarE : Kstar=M_σ⊓C(E)` を作って `▸` で回避。
- **case-τ₃ 現況**: K=E ✓ / (a) ✓ / (K*≠1) ✓ / (d) ✓。**残 = (b1), (g)**。full build green 3817 jobs。

🛑 **残 conjunct は quick win でない (obstacle 確定、要方針判断)**:
- **(g) `IsTypeP2 M → …`**: case-τ₃ では M は P1 ゆえ **vacuous のはず**だが、¬P2 = `κ=sigmaComplementPrimes`
  の証明が **定義的ギャップでブロック**。`kappa`/`tau1`/`tau3` は `p : ℕ` 全体を渡る (素数制限なし)。
  `pRank M p` 定義 (PRank.lean:374) = `⨆ A:{IsElementaryAbelian p}, log p (card A)` で **素数性を強制しない**
  (`rank` の docstring が「composite exponents を防ぐため prime に制限」と明記＝pRank 単体は防がない)。
  ⟹ `p∈τ₁ (pRank=1)` から `p 素数` が出ず、**κ⊆sigmaComplementPrimes (=piSet∖σ, 素数のみ) が形式上未証明**
  (κ が composite p を含みうる)。**選択肢**: (i) 実 (g) 内容を証明 (Thm 3.10(a)/Lem 12.19/12.17、multi-lemma)、
  (ii) `kappa`/`tau` 定義に素数性を付加 (faithfulness fix だが下流 lemma 影響大)、(iii) κ-witness が素数を強制する
  補題を別途証明 (`IsElementaryAbelian p` + nontrivial ⟹ p 素数 が要るが現状未確認)。
- **(b1) `∀ X≤K, X≠⊥ → N_G(X)⊓M = K⊔Kstar`**: BG (b1) は **`X∈ℰ¹(K)` (rank-1) 限定**だが Lean goal は
  **∀X≤K (over-broad)** ⟹ **statement faithfulness 要確認** (現 goal が真かBG通り ℰ¹(K) に絞るべきか)。
  証明自体も hard normalizer 計算 (N_M(X)=K×K*) で Lemma 13.13/13.6 wiring 要。
- **case-τ₁**: F の issue-7000 ∃→∀ upgrade leaf 未着地 ⟹ gated。

**⟹ case-τ₃ の core (K=E + 3/5 conjunct) は完了。残 2 conjunct + case-τ₁ は要方針判断 (上記)。**

### ✅✅ faithfulness fix 群 + (g)/(b1) 進捗 (2026-06-15 loop, ユーザー方針「faithfulness を先に」)
ユーザー裁可で faithfulness を先に整備:
- **✅ kappa primality 化** (commit `bb844d42`): `kappa` def に `p.Prime` 追加 (BG の κ は素数集合)。tau(§12)
  不変、S14 内に閉じる。`prime_of_mem_kappa` helper + 全 site 更新。G は kappa を Set cite のみで不変。
- **✅ (g) COMPLETE** (commit `ba911f75`): kappa primality 化で **κ=sigmaComplementPrimes** が証明可能に
  ⟹ case-τ₃ は P1 ⟹ `IsTypeP2 M` 矛盾で (g) vacuous 解決。κ⊆: witness P≤M で p|M + tau⊆σ'。
  ⊇: p∈piSet∖σ ⟹ p|E (card_Msigma_mul_card_E) ⟹ mem_kappa(step2)。
- **✅ (b1) statement faithful 化 + ⊇ 方向** (commit 後述): goal を BG 通り
  `∀ p prime, ∀ X∈ℰ_p¹, X≤K → N(X)⊓M=K⊔Kstar` に修正 (旧 `∀X≤K` は over-broad/偽)。
  **⊇ 証明済**: K=E≤N_G(X) (Cor 13.11 hEnorm) + K*=C_{M_σ}(K)≤C_G(X)≤N_G(X), K*≤M_σ≤M。
  **⊆ のみ sorry** (BG「clear」だが M=M_σ⋊E semidirect 構造 + N_M(X)=K×K* に要・hard)。

**case-τ₃ 現況: K=E + (a)+(K*≠1)+(d)+(g) 完成、(b1) は statement faithful + ⊇ 済・⊆ のみ sorry。**
**残 = (b1)-⊆ [M=M_σ⋊E 構造] + case-τ₁ [F issue-7000 gated]。full build green 3817 jobs。**

### 🎉🎉 case-τ₃ COMPLETE — (b1)-⊆ landing (2026-06-15 loop)
**Prop 14.2 の case-τ₃ 全 5 conjunct 完全証明** (typeP_structure の sorry は case-τ₁ 1 本のみに)。
(b1)-⊆ `N_M(X) ≤ K⊔K*` を「難所回避しない」方針で正面突破:
- **n=s·e 分解**: M_σ は G で非正規 (mem_sup/mem_sup_of_normal は不可) ⟹ **↥M で分解**。
  `M_σ.subgroupOf M` は ↥M で Normal、`(M_σ⊔E).subgroupOf M = ⊤` (subgroupOf_sup+E_compl_sup+subgroupOf_self)
  ⟹ `mem_sup_of_normal_left` で ⟨n,hnM⟩=a*b、s:=(a:G)∈M_σ, e:=(b:G)∈E。
- **交換子**: g∈X#, y':=ege⁻¹∈E#。`s·y'·s⁻¹ = ngn⁻¹ ∈ X≤E` (mem_normalizer_iff)。
  `[s,y']=s·y'·s⁻¹·y'⁻¹ ∈ M_σ` (M≤N(M_σ), le_normalizer_opiCoreInG) `∩ E ⟹ =1` (E_compl_inf)
  ⟹ s が y' を中心化。
- **prime 作用**: `s∈C_{M_σ}(y')=C_{M_σ}(E)=K*` (hEprime y')。e∈E=K ⟹ n=s·e∈K⊔K*。
- 技法: y'≠1 = `MulAut.conj.map_eq_one_iff`、commute 導出 = `mul_inv_eq_iff_eq_mul∘mul_inv_eq_one`、
  algebra は `group`。**[Fact p.Prime] を intro 直後に補充** (ne_bot_of_mem_elemAbelianOfRank_one 用)。

**⟹ Prop 14.2 残 = case-τ₁ のみ (F の issue-7000 ∃→∀ upgrade leaf 着地待ち・gated)。**
**case-τ₃ + faithfulness fix 群で本セッション §14 funnel 入口をほぼ攻略。full build green 3817 jobs。**

### 🟢 case-τ₁ を H が巻き取り — 確認済み machinery + 実行プラン (2026-06-15 ユーザー指令)
**F が機能停止 ⟹ ユーザー指令で case-τ₁ (旧 issue-7000 support 含む) を H が S14 内で自前実装** (両 LAUNCH 修正済)。
**全 machinery が repo に存在確認済 (新規 theory 不要、case-τ₃ パターンの再利用)**:
- `SubgroupESetup.conj'`(S13_PrimeAction:811): `(h)(hc:c∈M) ⟹ SubgroupESetup M (conj c•E)(conj c•E₁)…`。
  c∈E で WLOG (conj c•E=E は `conj_smul_eq_self_of_mem_normalizer`+`le_normalizer`)。
- `E1_actsPrime`(S13_PrimeAction:424)=Thm 13.5: `(hG)(h)(hE1ne) ⟹ ActsPrimeOn (Msigma M) E₁`。
- `exists_conj_smul_le_hallPiece`(S12_Lemma1211:267): π-subgroup を Hall piece へ M-共役 (witness を E₁ へ)。
- `Ch1.S06.exists_conj_eq_of_isHall_subgroupOf`(S12_Lemma1211:287 使用): Hall 共役 **equality** (K=conj e₀•E₁ 用)。
- `Msigma_inf_centralizer_conj_ne_bot`(S14:150, 既 landing): witness の C_{Mσ}≠1 を共役で転送。
- conj-commute: `centralizer_conj_smul`(S12_ExceptionalBridge:273) + `conj_smul_eq_self_of_mem_normalizer` +
  `Subgroup.smul_inf` ⟹ `M_σ⊓C(conj m•S)=conj m•(M_σ⊓C(S))` (ActsPrimeOn 共役不変性に要、必要なら)。

**実行プラン (methodical, 次フラグメント〜)**:
1. **κ=τ₁**: κ⊆τ₁ (case hyp ¬(κ∩τ₃) + kappa_subset_tau1_union_tau3)。τ₁⊆κ: κ nonempty の witness P を
   exists_conj_smul_le_hallPiece で E₁ へ共役 → Msigma_inf_centralizer_conj_ne_bot で C_{Mσ}(E₁)≠1
   (E₁ non-regular) → 各 p∈τ₁ に prime 作用 (E1_actsPrime) で C_{Mσ}(P)=C_{Mσ}(E₁)≠1 ⟹ p∈κ。
   (case-τ₃ の E3_not_regular_of_mem_kappa_tau3 + step2 のミラー。)
2. **WLOG K=E₁**: K Hall τ₁ of E (κ=τ₁) + E₁ Hall τ₁ of E ⟹ ∃e₀∈E, conj e₀•E₁=K
   (exists_conj_eq_of_isHall) → `hsetup.conj' (e₀∈M)` で新 setup (新 E₁=K, E は conj e₀•E=E に rw)。
3. **conjuncts** (新 setup で): (a) ActsPrimeOn K=E1_actsPrime + regular on U=E₂E₃ (Lem 13.12+13.7) /
   (K*≠1)=C_{Mσ}(E₁)≠1 (step1) / (b1) case-τ₃ (b1) のミラー / (d) case-τ₃ (d) のミラー /
   **(g) ⚠ case-τ₁ では vacuous でない** (κ=τ₁⊊σ'∩π(M) があり得る ⟹ M が P2 可能) ⟹
   **実 type-P2 内容 (σ=β/|K|素数/M_σ nilp TI) を Thm 3.10(a)/Lem 12.19/12.17 で証明要 = hard core**。
**⟹ case-τ₁ は ~150 行・(g) が hard core。κ=τ₁ から methodical に。case-τ₃ helper を最大限再利用。**

### ✅ case-τ₁ 進捗 — 基盤 + WLOG + (a)/(K*≠1) (2026-06-15 loop)
- ✅ `E1_not_regular_of_mem_kappa_tau1` (E3 ミラー) + `mem_kappa_of_mem_primeFactors_card_E1` (coverage)。
- ✅ **WLOG K=E₁ COMPLETE** (commit `6174fff1`): κ⊆τ₁ (case hyp) + **E₁ Hall κ(M)** (coverage .1 +
  `hsetup.E₁_hall.2`/κ⊆τ₁ で .2 → `hallPiece_isHall_in_M`) + K Hall κ(M) (hK) →
  `OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf hMsolv … : ∃w∈M, conj w•E₁=K` →
  `SubgroupESetup.conj' hsetup hwM` + `rw[hw]` で新 setup `h'` (E₁'=K)。
  **🔑 技法: 共役後 h' に E1_* helper 直接適用 (conj-invariance 不要)** — `E1_not_regular_of_mem_kappa_tau1 hG h'`
  ⟹ K≠⊥/非regular、`E1_actsPrime hG h'` ⟹ (a)、`Msigma_inf_centralizer_E_ne_bot_…` ⟹ (K*≠1)。
  ⚠ `conj'` は dot 記法不可 (S13 namespace) → `SubgroupESetup.conj' hsetup hwM`。
- 🔲 **残 case-τ₁ = (b1)/(d)/(g)。case-τ₃ の単純ミラーでない (K=E₁'⊊E' 構造)**:
  - **(d)**: case-τ₃ (d) は (c)-helper `maximalContaining_centralizer_of_le_Msigma_centralizer_E` が
    X≤M_σ⊓C(E)[σ'-complement] を要するが、case-τ₁ は X≤Kstar=M_σ⊓C(K)=M_σ⊓C(E₁')。**C(E₁') 版 (c)-helper**
    (Lemma 13.6 を P=E₁'=K で直適用、X≤M_σ⊓C(E₁) を直接取る変種) を作れば Thm 10.1(e) で同様に。**最も tractable**。
  - **(b1)**: case-τ₃ (b1)-⊆ は K=E ゆえ y'=ege⁻¹∈E=K で prime 作用可。case-τ₁ は e∈E'⊋K で y'∉K の恐れ
    ⟹ 直接ミラー不可。**K cyclic (E₁ cyclic) で ⊇ は K≤C(X)≤N(X) から容易**、⊆ は要再設計
    (M=M_σ⋊E' の K-部分の扱い)。
  - **(g)**: case-τ₁ では M が P2 可能ゆえ **vacuous でない** ⟹ 実 type-P2 内容 (σ=β/|K|素数/M_σ nilp TI、
    Thm 3.10(a)/Lem 12.19/12.17) = **hard core**。
**⟹ 次 = (d) [C(E₁') 版 (c)-helper] → (b1) [⊆ 再設計] → (g) [hard]。**

### ✅ case-τ₁ (d) DONE + 残 (b1)/(g) hardness 確定 (2026-06-15 loop)
- ✅ **(d) landing** (commit `c140797e`): C(E₁) 版 (c)-helper `maximalContaining_centralizer_of_le_Msigma_centralizer_E1`
  (X≤M_σ⊓C(E₁) 直取り、Lemma 13.6 P=E₁) + case-τ₃ (d) ミラー (h' + hKstar + Thm 10.1(e))。
- **case-τ₁ 現況: WLOG + (a) + (K*≠1) + (d) = 4/5。残 = (b1)/(g) (genuinely hard)。**
- 🛑 **(b1) hard**: K=E₁'⊊E' ⟹ case-τ₃ (b1)-⊆ の prime 作用が破綻 (n=s·e, y'=ege⁻¹∈E'∖E₁',
  prime 作用は K=E₁' のみ ⟹ s∈C_{Mσ}(y') から s∈C_{Mσ}(K) が出ない)。**Frobenius 構造 E'=K⋉U'
  (K regular on U'=E₂'E₃') での N_M(X)=N_M(K)=K×K* 論法**が要る。⊇ は K cyclic で容易 (K≤C(X)≤N(X))。
- 🛑 **(g) hard + cite-gap**: case-τ₁ で M が P2 可能 ⟹ vacuous でない。BG (g) (mmd L3850) = E Frobenius
  kernel U=E₂E₃ → **Lem 14.1**(C_{Mσ}(U)=1 + M_σ nilp) → **Thm 3.10(a)**(K prime on M_σ ⟹ |K| 素数) →
  U=[U,K]=E' → **Lem 12.19**(E' centralizes Hall β' of M_σ, ✅ S12_E:269) → β=σ → **Lem 12.17**(M_σ∩M_σ^g
  β'-group ⟹ TI)。**⚠ cite-gap**: Lem 14.1 Frobenius 形 (repo の 14.1=`msigma_structure_of_notMem_sigma_kappa`
  は別部分) + Lem 12.17 (repo S12_E:72=`C_{Mσ}(E)⊆M_σ'∧[M_σ,E]=M_σ`、TI 部分と別命題) は**未形式化の可能性** →
  要調査/形式化。IsTypeP2→U≠1 (κ≠σ'∩π(M)⟹E₂'E₃'≠1) も step。
**⟹ 両者 multi-fragment hard。(b1)=Frobenius 構造、(g)=cite-assembly+gap。focused work 推奨。**

### ✅✅ case-τ₁ (b1) COMPLETE — Frobenius normalizer 論法 (2026-06-15 loop)
**Prop 14.2 の `typeP_structure` は case-τ₁ (g) **1 本のみ** に縮小** (case-τ₃ 全 5 + case-τ₁ の
WLOG/(a)/(K\*≠1)/(b1)/(d) 完了)。(b1) は「E₁ が U=E₂E₃ に regular 作用 (E=E₁⋉U Frobenius)」を
repo machinery の assembly で構成し、Frobenius normalizer 論法で攻略 (sorry-free・axiom-clean、
`#print axioms` = `[propext, Classical.choice, Quot.sound]`、full build green 3817 jobs ~59s)。

新規 helper (S14、すべて SubgroupESetup パラメトリック・case-τ₁ 専用):
- `actsRegularlyOn_E3_E1_of_kappa_inf_tau3_empty` (E₁ reg on E₃): κ∩τ₃=∅ で **Lem 13.7 の対偶** —
  E₁ が E₃ に非regular なら E₁E₃ が M_σ に prime 作用 ⟹ 任意 x∈E₃# で C_{M_σ}(x)=C_{M_σ}(E₁)=K\*≠1
  ⟹ κ∩τ₃ witness で矛盾。
- `actsRegularlyOn_E2_E1_of_actsPrime` (E₁ reg on E₂): **Lem 13.12 の対偶** — g∈E₁# が y'∈E₂# (位数
  q∈τ₂) を中心化すると、E₂ abelian (Cor 12.10b) の q-torsion `omega1OfAbelian E₂ q` が rank-2
  A∈ℰ_q²(E) で y'∈A ⟹ C_A(⟨g₀⟩)≠1 ⟹ Lem 13.12 で C_{M_σ}(⟨g₀⟩)=1、prime action の K\*≠1 と矛盾。
- `pRank_eq_of_le_of_not_dvd_index` (S12_Corollary1216 の private 版を S14 に複製) +
  `exists_elemAb_rank_two_le_E_mem_of_tau2` (r_q(E₂)=r_q(E)=r_q(M)=2 を index-coprime 2 段で、
  card(Ω₁)=q² を q²∣card ∧ log≤pRank=2 で)。
- `actsRegularlyOn_E23_E1_of_caseTau1` (E₁ reg on U=E₂E₃): E₃⊴E (12.1b) + E₁≤N(E₂) (12.1e) +
  E₂⊓E₃=⊥ で u=u₃u₂ 分解 (↥E, mem_sup_of_normal_left)、各因子が g-不変 ⟹ u=1。
- `normalizer_inf_E_le_E1_of_caseTau1` (N_G(X)⊓E≤E₁): e=u·k 分解 (E₂E₃⊴E)、E₁ abelian で kgk⁻¹=g
  ⟹ ugu⁻¹=ege⁻¹∈X≤E₁ ⟹ [u,g]∈E₁⊓(E₂E₃)=⊥ ⟹ u∈C_{E₂E₃}(g)=1。

(b1) 本体 assembly: n=a·b (a∈M_σ, b∈E') ⟹ [a,bgb⁻¹]∈M_σ⊓E'=1 ⟹ ngn⁻¹=bgb⁻¹ ⟹ s':=b⁻¹n が g
中心化 ⟹ s'∈C_{M_σ}(K)=K\* (prime action)、b=n·s'⁻¹∈N_G(X)⊓E'≤K (Helper) ⟹ n=b·s'∈K⊔K\*。

🛑 **残 = case-τ₁ (g) のみ — BG Thm 3.10 + Lem 12.17 TI 形が repo 未形式化で gated**:
- (g) chain (mmd L3850): U≠1 ⟹ E Frobenius/kernel U → **Lem 14.1**(C_{M_σ}(U)=1, M_σ nilp; repo 14.1
  は単一 Sylow の Ω₁ 形 ⟹ π(U) の 1 素数を選び A_p≤U で橋渡し可) → **Thm 3.10(a)**(K prime on M_σ ⟹
  |K| 素数; **repo 未形式化** = solvable Frobenius 群が nilpotent 群に作用する §3 定理) → U=[U,K]=E' →
  **Lem 12.19**(E' が Hall β' を中心化, ✅) → β=σ → **Lem 12.17**(M_σ∩M_σ^g が β'-group ⟹ TI;
  **repo 12.17 = `Msigma_E_relations` は C(E)⊓M_σ≤M_σ'∧[M_σ,E]=M_σ のみ、TI 部分は未形式化**)。
- ⟹ (g) は §3 (Thm 3.10) + §12 (12.17 TI 拡張) の 2 新規形式化に gated。**§14 単独では解禁不可** ⟹
  hub に報告 + issue 化推奨。case-τ₁ の他 4 conjunct + case-τ₃ 全 5 は完了。

## ✅✅✅ Prop 14.2 COMPLETE — case-τ₁ (g) 着地 (2026-06-15, lane-h)

**`typeP_structure` (Prop 14.2) 全体が sorry-free + axiom-clean** (commit `f031f7bc`;
`#print axioms = [propext, Classical.choice, Quot.sound]`)。前項末尾「§14 単独では解禁不可」は
**解消** — Thm 3.10(a) は `S03g_Thm310.prime_card_complement_of_frobenius_conj` で既に repo 在、
Lem 12.17 TI は新 leaf `S12_Lemma1217.Msigma_inf_conj_isBetaCompl` で形式化 (commit `35b06ac8`)。

### (g) の実装 (3 helper + assembly、すべて S14)
- **Lem 12.17 β'-clause** (新 leaf `S12_Lemma1217`): g∉M で M_σ∩M^g は β(M)′-group。
  rank-1 X≤M_σ∩M^g (Cauchy) → Thm 10.1(b) `fusion_control_of_mem_sigma` の transitivity で
  C_G(X)⊄M → ℳ(C_G(X))≠{M} → Cor 12.14 (`maximalContaining_centralizer_and_someSylow_eq_singleton`)
  の対偶で p∉β。**配置**: Cor 12.14 が S12_Theorem1213→S12_E を推移 import ⟹ S12_E 不可 (循環)、
  downstream leaf 化 (12.13/12.14/12.15/12.16 と同パターン)。cyclic + M_σ' trivial 部分 (§15/§16 用) は deferred。
- **`E23_ne_bot_of_isTypeP2_caseTau1`**: IsTypeP2 ⟹ E₂E₃≠⊥。対偶 = E₂E₃=⊥ ⟹ E=E₁ (eq_sup) ⟹
  κ=π−σ (case-τ₃ (g) の κ=sigmaComplementPrimes ミラー: ⊇ は mem_kappa_of_…_card_E1) ⟹ M は P₁ で P₂ 矛盾。
- **`sigma_eq_beta_and_prime_card_E1_of_caseTau1`** (Frobenius core): generic setup パラメトリック。
  - |K|素数: `isFrobeniusGroup_E_of_caseTau1` + `Msigma_centralizer_E23_eq_bot_of_caseTau1`
    (C_{Mσ}(U)=⊥ + M_σ nilp) + coprime |E||M_σ| (Hall) + ActsPrimeOn→hcond3 + solvable
    → `prime_card_complement_of_frobenius_conj` (Thm 3.10(a))。
  - σ=β: **U≤E'** = `le_commutator_of_coprime_inf_centralizer_eq_bot` (B=E₁,Y=U; coprime は
    Frobenius `coprime_card_kernel_complement`、FPF は `actsRegularlyOn_E23_E1_of_caseTau1`) → ⁅E₁,U⁆≤⁅E,E⁆=E'
    → U abelian (E' abelian = Cor 12.10b `.2.1.2`) [これが Thm 3.10(a) の hUab も供給] →
    Lem 12.19 `derivedE_centralizes_betaComplement` の W (Hall β' of M_σ, E'≤C(W)) で W≤C_{Mσ}(U)=⊥
    → π(M_σ)⊆β → σ⊆β (σ⊆π(M_σ) は Hall index 論法); β⊆σ は `alpha_subset_sigma∘beta_subset_alpha`。
  - **🔑 訂正**: 「U abelian = E₂E₃ abelian standalone」は不要 — U≤E' + E' abelian で取得。
- **`isTISubset_sigmaSharp_of_sigma_eq_beta`** (generic): σ=β。g が M_σ^# の overlap を作るとき、
  g∈M なら g∈N_G(M_σ) (M≤N(M_σ)); g∉M なら Lem 12.17 β'-clause で M_σ∩conj g•M_σ は β'=σ'-group
  かつ ≤M_σ (σ-group) ⟹ ⊥、overlap≠1 と矛盾 ⟹ TI。
- 補助: `msigma_centralizer_eq_bot_of_elemAb_le` / `Msigma_centralizer_E23_eq_bot_of_caseTau1` を
  M_σ nilpotent も返すよう augment (Lem 14.1 `msigma_structure_of_notMem_sigma_kappa` の第3連言)。

### ⟹ 次 = §14 funnel (Prop 14.2 解禁後)
- 14.3 `sigma_diagnostic`: Prop 14.2(b)(c) + Cor 12.10(e) + Lem 12.11(a) で書ける。
- 14.4 → 14.7 `typeP_duality` (§15/§16 が consume する唯一の §14 結果, call sites
  S15_MF:785/795/1976・S16_MainResults:437) → 14.9/14.10/14.12/14.13。
- Lem 14.6 (missing-page counting) と 14.7 の counting 不等式 (|𝒞_G(Ẑ)|>½|G|) が hard core。

### 📋 §14 funnel post-14.2 assessment (2026-06-15, lane-h) — 次セッション/hub 向け
Prop 14.2 着地後の funnel 各結果の gating を精査:
- **14.3 `sigma_diagnostic`**: BG Cor 14.3 (mmd L3852) は branch 1 で **Prop 14.2(c)** =
  「K*≠1 ∧ ∀X∈ℰ¹(K*), ℳ(C_G(X))={M}」を使う (x∈C_{Mσ}(K)=K* に適用→C_G(x)⊆M)。
  **現 `typeP_structure` surface は (c) の後半 (ℳ(C_G(X))={M}) を落としている** (conjunct 2 は K*≠1 のみ)。
  ⟹ 14.3 を埋めるには **Prop 14.2(c) を typeP_structure に追加 or 別 helper 化** が前提。
  (c) の BG 証明 = 「K prime not regular ⟹ K*≠1; (b2)/(c) は **Lem 13.13 + Lem 13.6** から」(両者 §13 landed)。
  branch 1 の C_M(X)⊆K×K* は Prop 14.2(b1) (現 surface 在) + C_G(X)≤N_G(X)。branch 2 = Cor 12.10(e) + Lem 12.11(a)。
- **14.7 `typeP_duality`**: 🛑 **§16 cross-lane gated**。∃! Mstar (dual partner 存在) は global counting
  (|𝒞_G(Ẑ)|>½|G|, kernel `half_lt_one_sub_inv_mul` 在) + **Lem 14.6 (missing-page, S14 未記述)** に依存し、
  Lem 14.6 は R(x)/M̃ (§16 `tildeM`、Lane G) 必須 (循環ゆえ §14 で書けない、issue 2005)。§15 は hcyc を
  Mstar bundle から取る (S15:795) ので部分証明も不可。⟹ **14.7 は §16 R(x)/M̃ landing 後** (Lane G 待ち)。
- ⟹ H の §14 自力 runway = **Prop 14.2(c) 追加 → 14.3 → 14.4** (14.4 も R(x) headline は §16 だが N(x)/型 surface は §13 cite 可)。
  14.7 は G の §16 と合流が要る。hub に cross-lane 調整を報告推奨。
