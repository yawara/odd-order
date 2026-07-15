# BG §14 — Maximal Subgroups of Type P and Counting

> ## ❄ FROZEN (2026-07-02)
> §14 全結果 landed。残 sorry = **14.9 `nonidentity_covered_by_sigma_pieces` / 14.13
> `sigmaLength_one_frobenius_type` の 2 点のみ** (両方 do-not-prove mis-encoding、off-spine =
> memory [[ft-settled-findings]])。PAUSE 裁定 (2026-06-14)・L1769 残リスト
> (14.8/14.10/14.11/14.12 は証明済)・旧 lane 名 (D/F/G/H) は全て履歴。
>
> **2026-07-15 更新**: 上記 2 宣言は consumer 0 の **frozen historical surfaces**。
> in-place で証明・修理しない。14.9 の faithful `Mtilde`/`zTilde` covering APIs と 14.13 の
> `S16.non_disjoint_signalizer_frobenius` は実装済みで、新 consumer はそちらを使う。

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

### 🔧 Cor 14.3 `sigma_diagnostic` 実装レシピ (2026-06-15, lane-h) — 次セッション向け詳細
**Prop 14.2(c) 露出済** (`typeP_structure` 第6 conjunct, commit `4283fad8`) ⟹ branch 1 の C_G(x)⊆M が書ける。
14.3 = 2-branch、各 branch が独立の deep chain (~150 行)。前提 API:
- `piSet (closure {x'}) = (orderOf x').primeFactors` (closure {x'}=zpowers x', Nat.card_zpowers)。
- σ'-prime の τ-partition: hx'sigma で全 p∈π(⟨x'⟩) は σ' ⟹ τ₁∪τ₂∪τ₃ (mem_tau_union 系)。
- `by_cases`: ∃ p₀∈π(⟨x'⟩), p₀∈(τ₂ M)ᶜ (= τ₁∪τ₃) [branch 1] / 全 p∈τ₂ [branch 2]。

**branch 1** (∃ p₀∈π(⟨x'⟩)∩(τ₁∪τ₃)): goal = `π(⟨x'⟩)⊆κ ∧ C_G(x)⊆M`。
1. X₀:=ℰ_{p₀}¹(⟨x'⟩) (Cauchy で order-p₀, ≤⟨x'⟩≤M)。x centralizes x'⟹centralizes X₀; x∈M_σ ⟹ ⟨x⟩≤C_{M_σ}(X₀)≠1。
   ⟹ p₀∈κ(M) (κ def: p₀∈τ₁∪τ₃ ∧ ∃P∈ℰ¹, C_{M_σ}(P)≠1)。⟹ M type-P (hP)。
2. K:=Hall κ(M) of M **⊇ X₀** (要 Hall-containment: M solvable + X₀ κ-subgroup ⟹ `exists_isHallSubgroup_ge`/
   Hall E定理; repo の Ch03 Hall API 要特定)。U:=Hall (κ∪σ)' of M (同様)。Kstar:=M_σ⊓C(K)。
3. `typeP_structure hG hM hP hKM hK hKstar hU` で (b1) [N_M(X₀)=K⊔Kstar] と (c) [ℳ(C_G(Y))={M} for Y∈ℰ¹(Kstar)] 取得。
4. C_M(x')⊆C_M(X₀)⊆N_M(X₀)=K⊔Kstar=K×Kstar (K σ', Kstar σ)。x' σ'-elt ⟹ x'∈K ⟹ π(⟨x'⟩)⊆π(K)=κ (第1連言)。
5. x∈C_{M_σ}(X₀)⊆M_σ∩(K×Kstar)=Kstar。⟨x⟩∈ℰ¹(Kstar) ⟹ (c): ℳ(C_G(x))={M} ⟹ C_G(x)⊆M (第2連言)。

**branch 2** (全 p∈π(⟨x'⟩)⊆τ₂): goal = `π(⟨x'⟩)⊆τ₂ ∧ ℓ_σ(x')=1 ∧ ℳ(C_G(x'))={M}`。
1. π(⟨x'⟩)⊆τ₂: branch 仮定。
2. ℳ(C_G(x'))={M}: x' τ₂-elt, C_{M_σ}(x')⊇⟨x⟩≠1 ⟹ **Cor 12.10(e)** =
   `(nilpotent_sigmaComplement_abelian hG hsetup).2.2.2.2 x' hx'M hx'1 (π(⟨x'⟩)⊆τ₂) (C_{M_σ}(x')≠1)`。要 E-setup。
3. ℓ_σ(x')=1 = `(D.length_one_iff x').mpr ⟨hx'1, hne⟩`, hne:`(maximalSigmaSubgroupsOfElement x').Nonempty`
   = ∃M*, x'∈M*_σ。chain: q∈π(⟨x'⟩)⊆τ₂(M), A∈ℰ_q²(E), M*∈ℳ(N_G(A)) ⟹ **Lem 12.11(a)**
   `tau2_prime_mem_sigma_diff_beta` で q∈σ(M*) ⟹ ⟨x'⟩ σ(M*)-group ⟹ **Cor 12.16**
   `sigma_subgroup_conj_into_Msigma` で ∃g∈M*, conj g•⟨x'⟩≤M*_σ ⟹ x'∈(M*^{g⁻¹})_σ
   (要 σ-core conjugation-equivariance: (conj g•M)_σ = conj g•M_σ ∧ σ(conj g•M)=σ(M))。⟹ M*^{g⁻¹}∈maximalSigmaSubgroupsOfElement x'。

**要特定 API**: (a) Hall κ ⊇ X₀ 存在 (Ch03 solvable Hall containment), (b) σ-core/σ conjugation-equivariance,
(c) E-setup reconstruction (`exists_subgroupESetup` で M から)。**branch 1 が Prop 14.2 full 適用 (K/U/Kstar 3 producer)、
branch 2 が Lem 12.11(a)+Cor 12.16+ℓ_σ chain。各 ~60-80 行。** → 14.4 は Cor 14.3 + Thm 13.9 (R(x) headline は §16 defer)。

### ⚠ 14.3 の真の gate = Hall-containment (Hall-D) + branch-2 ℳ-piece landed (2026-06-15, lane-h)
14.3 着手で判明:
- **branch 1 は Hall-D (Wielandt: π-subgroup ⊆ Hall π in solvable) に gate** — repo は hall_E/hall_C
  (存在+共役) のみで **containment 未形式化** (Lane D notes「Cor 10.9 — needs Hall-D, ~250 行」と同じ gap)。
  branch 1 は K=Hall κ ⊇ X₀ (κ-witness) を要し、これが Hall-D そのもの。Sylow 経由の workaround
  (X₀≤Syl_{p₀}≤Hall κ) は「Syl_p ⊆ Hall π for p∈π」+ Sylow 共役で可能だが fiddly (~30-40 行) +
  その後 typeP_structure full 適用 (K/U/Kstar 3 producer) で更に setup 重い。
- **✅ branch-2 ℳ-piece landed**: `maximalContaining_centralizer_eq_singleton_of_tau2_element`
  (x' τ₂-elt + C_{M_σ}(x')≠1 ⟹ ℳ(C_G(x'))={M}) = Cor 12.10(e) + E-setup、sorry-free。
  残 branch 2 = ℓ_σ(x')=1 (Lem 12.11(a)+Cor 12.16+σ-core conj-equivariance `sigma_conj` ✅ で
  maximalSigmaSubgroupsOfElement 非空)。
- ⟹ **14.3 完成には Hall-D (or Sylow-workaround) が前提**。14.4 も R(x) headline は §16 gate。
  **推奨: Hall-D を Ch03 に形式化してから 14.3 branch 1**(Hall-D は Cor 10.9 等でも要る汎用 lemma)、
  または 14.3 を Hall-D landing 待ちで保留し別 FT-path タスクへ。hub に cross-cutting Hall-D 需要を報告。

### ✅ 14.3 infra COMPLETE — hall_D 発見で branch 1 unblock (2026-06-15, lane-h)
**🔑 訂正: `Ch03.hall_D` (Isaacs 3C.1 Wielandt, π-subgroup ⊆ Hall π in solvable) は形式化済**
(`Main.lean:1486`)。前項「Hall-D 未形式化」「Sylow workaround 要」は **stale** — hall_D 直用で branch 1 の
Hall-containment が unblock。14.3 が要する infra は全 landing:
- ✅ `exists_isHallSubgroup_kappa_ge` (κ-subgroup ≤ Hall κ of M, hall_D 経由, commit `6263b1d6`)。
- ✅ `maximalContaining_centralizer_eq_singleton_of_tau2_element` (branch-2 ℳ-piece, `3e702d74`)。
- ✅ Prop 14.2(c) (typeP_structure 第6 conjunct, `4283fad8`)。
**残 = 14.3 assembly のみ** (2-branch、各 deep だが infra 揃い):
- **branch 1** (∃ p₀∈π(⟨x'⟩)∩(τ₁∪τ₃)): X₀=order-p₀ in ⟨x'⟩ (Cauchy) → x∈C_{Mσ}(X₀)≠⊥ → p₀∈κ →
  `exists_isHallSubgroup_kappa_ge` で K⊇X₀ + U=Hall(κ∪σ)' (hall_E_exists+map) → typeP_structure(K) の
  (b1)+(c) → **x'∈K** [C_M(x')⊆N_M(X₀)=K⊔Kstar=K×Kstar (K∩Kstar=1 coprime, [K,Kstar]=1 since
  Kstar=C_{Mσ}(K)); x' σ'-elt の σ'-projection で K-part のみ ⟹ x'∈K; ~20 行 fiddly] →
  π(⟨x'⟩)⊆π(K)⊆κ; x∈Kstar (=C_{Mσ}(X₀)⊆Mσ⊓(K⊔Kstar)) → X₁=order-p in ⟨x⟩ ∈ℰ¹(Kstar) → (c) →
  ℳ(C_G(X₁))={M} → C_G(x)⊆C_G(X₁)⊆M。
- **branch 2** (∀p∈π(⟨x'⟩), p∈τ₂): ℳ-part ✅ (ℳ-piece, C_{Mσ}(x')≠⊥ は x∈Mσ⊓C(x'))。
  残 **ℓ_σ(x')=1** = `(D.length_one_iff x').mpr ⟨hx'1, hne⟩`, hne=(maximalSigmaSubgroupsOfElement x').Nonempty
  = ∃M', x'∈M'_σ。chain: q∈π(⟨x'⟩)⊆τ₂(M), A∈ℰ_q²(E), M*∈ℳ(N_G(A)) → Lem 12.11(a)
  `tau2_prime_mem_sigma_diff_beta` で q∈σ(M*) → ⟨x'⟩ σ(M*)-group → **要 ⟨x'⟩≤M*** (x'∈M だが M* は別)
  → Cor 12.16 一般形 (σ(M*)-subgroup of G は M*_σ に共役) + σ-core conj-equivariance (`sigma_conj`✅)。
  **⚠ ℓ_σ が最深** (⟨x'⟩→M* の取り込み + Cor 12.16 一般形 [repo `sigma_subgroup_conj_into_Msigma` は Y≤M* 要])。
- ⟹ **assembly 2 件 (x'∈K σ'-projection [~20行] + ℓ_σ chain [~40行]) が 14.3 完成の残**。infra は全部 repo 在。

### ✅✅ Cor 14.3 branch 1 COMPLETE — 残 ℓ_σ のみ (2026-06-16, lane-h, commit aa001ecf)
**`sigma_diagnostic` は branch 1 全証明 + branch 2 ℳ-part 完了、残 sorry = branch 2 の ℓ_σ(x')=1 のみ**
(S14 sorry 数不変 9 — opaque 1 sorry を branch1-proven+branch2-ℳ+局所 ℓ_σ に置換)。
- branch 1: σ'-prime witness → X₀ → p₀∈κ → `exists_isHallSubgroup_kappa_ge` (hall_D) で Hall κ K⊇X₀ →
  typeP_structure(K) (b1)/(c) → **K⊔K*=K×K* の σ'/σ-projection** (hdecomp via mem_sup_of_normal_left;
  x' σ'⟹x'∈K [orderOf 論法: (k·s)^N=1⟹k^N=s^{-N}∈K∩M_σ=⊥]; x∈M_σ⟹x∈K* [K∩M_σ=⊥]) →
  π(⟨x'⟩)⊆κ + C_G(x)⊆C_G(X₁)⊆M。全 build green。
- **残 ℓ_σ(x')=1** = `(D.length_one_iff x').mpr ⟨hx'1, hne⟩`, hne=(maximalSigmaSubgroupsOfElement x').Nonempty
  = **∃M', x'∈M'_σ**。🛑 **要 general Cor 12.16** = 「multi-prime σ(M*)-subgroup of G (cyclic ⟨x'⟩, **NOT ≤M***)
  → M*_σ 共役」。repo の不足: `sigma_subgroup_conj_into_Msigma` (multi-prime だが Y≤M 要) /
  `exists_conj_smul_le_Msigma_of_pSubgroup` (Y≤G だが single-prime)。`exists_char_qSubgroup` は char-q 還元のみ
  (pRank bound 用、conjugation 非露出)。chain: Lem 12.11(a) `tau2_prime_mem_sigma_diff_beta` で
  τ₂(M)⊆σ(M*) → ⟨x'⟩ σ(M*)-group → **general Cor 12.16** で ∃g, conj g•⟨x'⟩≤M*_σ → x'∈(conj g⁻¹•M*)_σ
  (要 Msigma conj-equivariance + maximal 保存)。
- **▶ ℓ_σ の sub-project = general Cor 12.16(a) を建てる** (BG 原文の char-q + Prop 12.15/M*=(M∩M*)K 構造、
  ~50-80 行、focused session 向き) or `exists_conj_smul_le_Msigma_of_pSubgroup` を multi-prime/cyclic へ拡張。
  これが ℓ_σ → 14.3 完成 → 14.4 の gate。**14.3 の他は全部済**。

### ✅✅ general Cor 12.16(a) headline COMPLETE — ℓ_σ blocker解除 (2026-06-16, lane-h, commit 24ce5d0f)
**`S12.sigma_subgroup_conj_into_Msigma_general`** (S12_Corollary1216.lean): 非自明 σ(M)-subgroup
`Y < ⊤` of G は M_σ へ G-共役 (`∃g, conj g•Y ≤ Msigma M`)。**sorry-free + axiom-clean (AxiomsCheck
登録済) + full build green (97s, S12 downstream cascade)**。これが notes 前項「▶ ℓ_σ の sub-project =
general Cor 12.16(a)」の解。BG mmd L3453/L3474 の (a) headline (= L3801「every σ(M)-element is
conjugate to an element of M_σ」)。

新 helper (Cor1216 namespace, private):
- `exists_conj_smul_le_of_index_isPiCompl`: generic Hall E-C-D 系 (可解群で π-subgroup は π'-index
  部分群へ共役)。polymorphic。
- `exists_conj_smul_le_of_relIndex_isPiCompl`: G-level 版 (可解 N 内、共役元 ∈ N)。↥N→G transfer =
  `map_subtype_conj_smul` (S10/S12_Prop1215 の private copy)。
- `exists_Mstar_factorization_sigma`: Prop 12.15 factorization M*=(M⊓M*)⊔K で **K を σ(M*)-group
  として返す** (σ-disjoint ⟹ σ(M)')。nonconjugacy (h1215.1) も返す。E-setup 不要 (hM のみ)。
- `exists_conj_qSubgroup_le_Msigma`: Sylow Step-1 抽出 (σ-prime q-group → M_σ)。

**🔑 設計**: σ-disjointness (Thm 13.9 = `sigma_disjoint_of_nonconjugate`, S13 downstream) は import
cycle 回避のため **hypothesis `hσdisj` でパラメータ化**。§14 caller が discharge (Thm 13.9 は landed)。
S12 は unowned (F retired)。

### ▶ 残: Cor 14.3 ℓ_σ wiring (S14:2123, branch 2) — 次の作業
`D.length x' = 1` を `(D.length_one_iff x').mpr ⟨hx'1, hne⟩` で。hne = (maximalSigmaSubgroupsOfElement
x').Nonempty = ∃ M' max, x'∈M'_σ。chain:
1. q₀ ∈ π(⟨x'⟩) (x'≠1 ゆえ nonempty)。π(⟨x'⟩)⊆τ₂(M) (hτ2)。
2. **A ∈ ℰ_{q₀}²(E)**: `exists_mem_elemAbelianOfRank_two_le_of_tau2` は A≤M しか返さない →
   **push-in to E が要る** (`exists_conj_smul_le_hallPiece` 経由、Lem 12.11 proof line 412 と同型)。
   ⟹ **要 helper or inline push-in**。
3. Mstar ∈ ℳ(N_G(A)) (maximalSubgroupsContaining nonempty)。
4. `tau2_prime_mem_sigma_diff_beta` (Lem 12.11a): ∀ q∈τ₂(M), q∈σ(Mstar)。⟹ π(⟨x'⟩)⊆σ(Mstar)、
   即ち `IsPiSubgroup (σ Mstar) (zpowers x')`。
5. `sigma_subgroup_conj_into_Msigma_general hG hMstar_mem hzpne hzplt hx'piMstar
   (fun h h' => sigma_disjoint_of_nonconjugate hG hMstar_mem h h')` → ∃g, conj g•⟨x'⟩ ≤ Msigma Mstar。
   (hzplt: zpowers x' < ⊤ — G non-abelian ゆえ cyclic ≠ ⊤。)
6. **Msigma conj-equivariance** (要 helper, S14): `Msigma (conj g • M) = conj g • Msigma M`
   (= sigma set conj-invariance [sigma_conj 両方向] + opiCoreInG conjugation
   [conj_smul_opiCoreInG, S07 private → replicate])。⟹ x' ∈ Msigma (conj g⁻¹•Mstar)。
7. M' = conj g⁻¹•Mstar maximal (`isCoatom_conj_smul`)。⟹ ⟨M', _, _⟩。
**要新 helper ×2**: (i) ℰ_q²(E) push-in (step 2)、(ii) Msigma conj-equivariance (step 6)。各 moderate。

### ✅✅✅ Cor 14.3 sigma_diagnostic COMPLETE (2026-06-16, lane-h, commit de81606d)
`sigma_diagnostic` (BG Cor 14.3) は **fully sorry-free + axiom-clean** (AxiomsCheck 登録、full build
green 65s)。branch-2 ℓ_σ(x')=1 を general Cor 12.16(a) で wire 完了。新 S14 helper: `sigma_conj_smul_eq`
(σ(Mᵍ)=σ(M)) / `conj_smul_opiCoreInG'` (O_π conj、S07 private replicate) / `Msigma_conj_smul`
((Mᵍ)_σ=(M_σ)ᵍ)。S14 sorry 9→8。**§16-independent §14 dependency cluster (Prop 14.2 / Cor 14.3 /
general Cor 12.16(a)) は全完了** — これらは 14.7 の証明が要する piece。

### 📋 残 §14 sorry 8 件の gating 評価 (2026-06-16, lane-h) — 次セッション/hub 向け
remaining: 14.4 `sigmaLength_one_centralizer_structure`(2461) / **14.7 `typeP_duality`(2563)** /
Cor14.8 `typeP1_conjugate_and_typeP_twoClasses`(2583) / `nonidentity_covered_by_sigma_pieces`(2603) /
`exists_sigmaDecomposition_length_le_two`(2617) / `exists_maximal_of_typeF_notMem_fitting`(2628) /
14.12 `typeP2_neighbor_is_typeF`(2651) / 14.13 `sigmaLength_one_frobenius_type`(2665)。
- **14.7 = binding long pole**(S15:785/795/1976・S16:437 が consume)。§16-independent = M* construction
  (conjuncts (1)ℳ(C_G(X))={M*} /(2)K* Hall /(3)K=C_{M*σ}(K*)・κ=τ₁ /(4)Z cyclic /(6)type-P2 /(8)M'
  complement); **§16-gated = (5) counting |𝒞_G(Ẑ)|>½|G| + (7) global conjugacy**(Lem 14.6 = R(x)/M̃、
  Lane G §16、issue 2005)。⟹ M* construction (~300-500 行) は今や着手可(Cor 14.3 + general Cor 12.16(a)
  揃った)、(5)(7) を named residual に残す skeleton 戦略推奨。
- **14.4 R(x) headline §16-gated**; Cor 14.8 は 14.7 gated; 14.9 covering は M̃ §16 必須。
- **14.12/14.13 は §13 landed (F 完了) で再評価要** — 旧 notes「§13 gate」は §13 完了で解けた可能性。
  次セッション最初の一手 = 14.12/14.13 の dep を grep して unblocked か確認(small win 候補)、その後 14.7
  M* construction skeleton。

### 🔭 14.7 pre-position 開始 (2026-06-16, lane-h, ユーザー裁可) — step 0 = Prop 14.2(b2) DONE
ユーザー判断: 14.7 の §16-independent machinery (M_i/Z setup) を sorry-free lemma で pre-position
(typeP_duality 自体は counting (5)(7) = Lane G §16 gated のまま)。**確定: §14 で FT critical path 上は
14.7 のみ** (他 7 結果 = §15/§16 参照 0)。14.7 の conjuncts (4)(6)(8) も counting 経由ゆえ §16-gated;
§16-independent = M_i/Z setup (BG L3973-4015) のみ。
- ✅ **step 0 = Prop 14.2(b2)** `typeP_elemAbelian_le_neighbor_Msigma` (commit 5e02b11b): X∈ℰ¹(K),
  C_{Mσ}(X)≠1 ⟹ X⊆M*_σ。Lem 13.13 + σ-subgroup→Msigma。**typeP_structure に欠けていた (b1) のみ carry**
  ⟹ standalone 化。
- ▶ **step 1 (次)** = neighbor basic lemma: X∈ℰ¹(K), M_i∈ℳ(N_G(X)) ⟹ ¬conj(M,M_i) ∧ K⊔Kstar≤M_i ∧
  X⊆M_{iσ} ∧ (∀p∈π(Kstar), p∈κ(M_i)) ∧ (∀X*∈ℰ¹(Kstar), N_G(X*)≤M)。deps: Prop 14.2(b1)[conj 3]+(b2)[step0]
  +(c)[conj 6] / Cor 14.3 (sigma_diagnostic, ✅) / Thm 13.9 (✅)。BG L3977-3991。
  - ¬conj(M,M_i): π(X)⊆κ(M)⊆σ(M)' ∧ X⊆M_{iσ}⊆σ(M_i) ⟹ もし conj なら σ 一致で矛盾 (or Lem 12.2(b))。
  - Z⊆M_i: typeP_structure(b1) N_M(X)=K⊔Kstar ≤ M、但し M_i 側は X⊆M_i から K,Kstar⊆? 要精査 (BG「Prop
    14.2(b)」が Z⊆M_i を直接与える — 実は (b1) は N_M、Z⊆M_i は別。BG 原文再確認要)。
  - π(K*)⊆κ(M_i): X*∈ℰ¹(K*)、C_{M_iσ}(X*)⊇X⊃1 ⟹ Cor 14.3 branch 1 で π(⟨X*⟩)⊆κ(M_i)。
- step 2/3 = K_i×K_i*=Z, Z=∏K_i* decomposition (BG L3993-4015)。step 4+ = counting (§16 gated, Lane G)。

### 🔑 訂正 + 発見 (2026-06-16, lane-h): Thm 14.4 (R(x)) は Lane H で provable
14.7 pre-position step 1b (typeP_neighbor_kappa) 完了後の精査で判明:
- **`sigmaLength_one_centralizer_structure` (Thm 14.4) の Lean statement は §16-circular 部分
  (sharply-transitive headline + part (b)) を DROP 済** (docstring 明記)。残る内容 = ∃! N +
  (a)(c)(d)(e)(f) は **§13-gated**: BG proof (L3880-3904) は Thm 13.9 ✓ / Thm 10.1(b)
  (=`S10.fusion_control_of_mem_sigma`, repo 在) / Prop 12.15 ✓ / **Cor 14.3 ✓ (完了済)** /
  Cor 12.6 のみ。§16/Lemma 14.6 に**非依存**。⟹ **14.4 は今 provable**。旧 notes/memory の
  「14.4 R(x) headline §16-gated」は **DROP された headline 部分のみ**の話で、Lean statement 本体は
  unblocked。
- **R(x) = Msigma N ⊓ C_G(x)** は §16 の Lemma 14.6/tildeM が要する foundation。14.4 を Lane H が
  証明すれば §16 (Lane G) に R(x) を供給できる(但し §16 は現状 parameterized R ゆえ Lane G の wiring 要)。
- ⟹ **14.4 は M_i/Z setup (sorried machinery) より良い target**: closeable sorry + R(x) foundation。
  但し大 (~250-350 行, ∃! N + sharply-transitive 周辺の reasoning), Thm 10.1(b) の exact form 要確認。

### ⚠ §16 (Lane G) 停滞 — Lane H の FT 接続が gated
recent merge log = 全て lane-h 自身の commit (Lane G/F/B の合流無し)。S16_MainResults は parameterized
`R : G → Subgroup G` + sorry 多数 (R(x)/tildeM/Lemma 14.6 未構築)。⟹ Lane H の §14 machinery
(Prop 14.2 / Cor 14.3 / gen Cor 12.16(a) / 14.7 steps 0-1b) は揃ったが、**binding result 14.7 は
§16 counting gated のまま、FT 接続は Lane G の §16 進展待ち**。merge cron 稼働状況も要確認。

### ✅✅✅ Thm 14.4 `sigmaLength_one_centralizer_structure` COMPLETE (2026-06-16, lane-h loop)
**sorry-free + axiom-clean + AxiomsCheck 登録済** (`#assert_only_allowed_axioms` 通過, full build green 1:05)。
§16 の R(x) foundation を供給する §14 構造定理。証明構成 (~700 行):
- setup: x(ℓ_σ=1, |𝓜_σ(x)|>1) から M·q·g·X 選択; |𝓜_σ(x)|≥2 で M'≠M (13.9 共役) + transitivity (10.1b) ⟹ N≠M, C_G(x)≤N.
- **hRx (R(x)=N_σ∩C_G(x)≠1)**: BG u-construction — c=v·a (↥N 分解, N_σ⊴N) ⟹ conj v•M=M', v≠1; x⁻¹vx=v は v⁻¹(x⁻¹vx)∈N_σ∩N_G(M)=⊥.
- **Hall**: R'.index=(N_σ).relIndex C ∣ (N_σ).relIndex N ∣ (N_σ).index[σ(N)' by Msigma_isHall] (relIndex_subgroupOf + relIndex_dvd_index_of_normal).
- **hπτ2 + uniqueness**: sigma_diagnostic(Cor14.3) を (N, w∈N_σ^#, x) で適用, κ-branch を pRank で排除.
- **(f)**: κ(N)⊆τ₁∪τ₃, q∈τ₂(N) ⟹ N∉𝓜_{P₁}.
- **∀M (c)(d)(e)**: 各 M₂ で Prop 12.15(e) 再適用 (N≠M₂ は x∉N_σ から); (c)=Cor 12.6 + `exists_subgroupESetup_with_le` (E_N⊇M₂∩N, A∈ℰ_p²⊴E_N, x が正規化, p∈τ₂M₂⟹N_{M₂σ}(A)=⊥ で矛盾).
- crux helper `Msigma_inf_normalizer_eq_bot_of_tau2` (14.4 直前): A∈ℰ_p²(E),p∈τ₂(M) ⟹ N_G(A)⊓M_σ=⊥ (Cor12.6(b)+E_compl_inf).

### 🐛 faithfulness 発見 (2026-06-16): repo `tau2` def は素数制限を欠く
`tau2 M = {p | p∉σ M ∧ pRank M p = 2}` は **prime 条件 (p∈π(M)) を欠く**。`IsElementaryAbelian p` の定義
`(abelian ∧ ∀x, x^p=1)` は p 素数を強制しない ⟹ **素数べき r²（Sylow-r=(ℤ/r²)² なら IsElementaryAbelian r²,
log_{r²}(r⁴)=2 ⟹ pRank=2, r²∉σ）等の非素数が τ₂ に入りうる**。BG は τ₂(M)⊆π(M)（素数）。
- ⟹ 14.4 の (c) は当初 `tau2 N ⊆ sigma M`（偽）→ **`tau2 N ∩ piSet N ⊆ sigma M`** に修正（piSet N=素因数で
  BG の τ₂(N)⊆π(N) を回復, = BG faithful）。consumer 0 ゆえ安全。
- **⚠ hub 注意**: `tau2` def 自体が latent unfaithful。他の `tau2 ⊆ …` 形 statement があれば同様の素数制限要
  （大半の使用は [Fact p.Prime] 付きで無害）。将来 τ₂ def に `p∈π(M)` を足すリファクタも検討余地（広域影響）。

### ✅ Thm 14.7 §16-independent partner existence + ⚠ part(h) 再評価 (2026-06-16, lane-h loop)
**`exists_typeP_partner` COMPLETE** (commit `9c69d433`, sorry-free + axiom-clean + AxiomsCheck 登録):
14.7 の nonconjugate partner `M*` の存在 + basic neighbour data (type-P / ¬conj / `K⊔K*≤M*` /
`X≤M*_σ` / `π(K*)⊆κ(M*)`)。step 1a/1b (`typeP_neighbor_embed` + `typeP_neighbor_kappa`) を組立。
`∃!` の existence 半分を供給 (cyclic Z / TI / P₂ / covering は §16-gated)。

**✅ P1 reduction lemma `commutator_eq_sup_commutator_of_isComplement'` COMPLETE** (commit `acffa2ab`,
一般群論, sorry-free + axiom-clean): `N⊴H` complement `E`, `N≤H'` ⟹ `H' = N ⊔ ⁅E,E⁆`。
⟹ **`M' = M_σ ⊔ E'` uniform** (case 分析・regular action 不要; `M_σ≤M'`=Thm 10.2c + `E'=[E,E]≤[M,M]=M'`)。

**⚠⚠ part(h) は LAUNCH/issue-2008 の「§16-independent・~50-100行」評価が誤り (要訂正)**:
P1 で part(h) `IsComplement'(M') K` は **E-内部の `IsComplement'(E') K` (= `E = K ⋉ E'`) に還元**
(`M'∩K = E'∩K`, `M'K=M ⟺ E'K=E`)。これは **`E' = κ'-Hall(E)`** と同値で:
- **case τ₁** (K=E₁): `E' = E₂E₃` = deferred Prop 14.2(a) の **regular action `[E₂E₃,E₁]=E₂E₃`**
  (BG L3840, Lem 13.12+13.7 assembly — `typeP_structure` も deferred 済, 露出無し)。E₃≤E' は
  Lem 12.1 在だが E₂≤E' が regular action 要。**実質 ~150-250 行の assembly**。
- **case τ₃** (K=E, κ-group): `κ'-Hall(E)=1` ⟹ `E'=1` 要だが **Lem 12.1 で `E₃≤E'` かつ E₃≠1**
  ⟹ `E'≠1` の **緊張**。⟹ part(h) は case-τ₃ 生 configuration で偽に見え、BG part(8) は
  **§16 counting (n=1 collapse, Z cyclic) で configuration を制約してから**成立 = **§16-gated**。
  (BG L4061 の "K cyclic" は L4041 の Z=K×K* cyclic 由来 = post-counting。)
- ⟹ **part(h) を §16-independent な standalone sorry-free lemma に切り出して S15:785 を un-taint する
  ことは不可** (part(h) 自体が §16/counting に依存)。S15 の part(h) 消費は inherently §16-gated
  (Lane G が §15+§16 両方所有ゆえ問題なし)。
- **P1 は正しい foundation** として landing 済 (将来 part(h) を §16 と共に証明する際に使う)。
- **次の H 候補**: (a) 14.7 M_i/Z combinatorial setup (BG L3993-4015, §16-indep, exists_typeP_partner
  上に構築) / (b) case-τ₃ faithfulness 精査 (part(h) statement が全 type-P M で真か, E cyclic 必須か) /
  (c) §16 counting 自体 = Lane G 領域。**要ユーザー/hub 判断** (part(h) gating で frontier 再選定)。

### 🔑🔑 2026-06-16 (lane-h loop) — frontier 再診断: 「§16-gated」は誤り、真の long pole = 14.4 sharp transitivity

**前節 (part(h) §16-gated) の結論を訂正する。** BG 原文 (L3962-4063) を再精読した結果:

**14.7 の "K cyclic"(part h の要)は §16 でなく 14.7 *自身の* internal counting (L4031-4045) 由来。**
- L4061 part(8): "since K is cyclic, UM_σ = M′"。"K cyclic" = part(4) "Z cyclic" の subgroup。
- L4041: Z cyclic は **n=1** 強制から(`Z=K_i×K_i*`, `K_i*⊆M_iσ` nilpotent rank-1 ⟹ cyclic)。
- n=1 は L4031-4039 の **counting 矛盾**(全 M_i が P₁ なら `|G^#|≥|G|`)から。この counting は
  §16 でなく **Thm 14.7 の証明本体**(`half_lt_one_sub_inv_mul` 8/15>½ kernel は既に repo L3244 在)。
- ⟹ 前節「§16 counting が configuration を制約」は **§14-internal counting の誤認**。§16 は §14 の *下流*
  (S16→S15→S14 の DAG; S16:530 が `typeP_duality` を consume)。§14→§16 依存は存在しない。

**真の gate chain(すべて §14-internal、§15/§16 非依存):**
```
14.7 typeP_duality
├─ Prop 14.2 (a)-(g) ............................. ✅ DONE (typeP_structure, sorry-free)
├─ Lem 12.17 clause3 (β′-group) ................. ✅ DONE (Msigma_inf_conj_isBetaCompl, S12_Lemma1217)
├─ Cor 14.3 sigma_diagnostic ..................... ✅ DONE (sorry-free)
├─ Thm 13.9 ..................................... ✅ (cited)
├─ half_lt_one_sub_inv_mul (8/15>½ kernel) ...... ✅ DONE (L3244)
├─ Lem 14.5(b) sigmaConjugacy_disjoint .......... ✅ DONE (sorry-free)
├─ **Thm 14.4 sharply-transitive R(x) + part(b)** ❌ DEFERRED (S16 Theorem D = sorry!) ← LONG POLE
├─ **M̃ = {xx′ | x∈M_σ^#, x′∈R(x)}** ............. ❌ 未定義 (現 sigmaConjugacySaturation は M_σ^# のみ=過小)
├─ **Lem 14.5(a)** xR(x)∩yR(y)=∅ ................ ❌ 未着手 (M̃ 要)
├─ **Lem 14.5(c)** |𝒞_G(M̃)|=(|M_σ|-1)|G:M| ..... ❌ 未着手 (sharp transitivity の二重数え)
└─ **Lem 14.6** dichotomy ........................ ❌ 未着手 (R(x)/σ-decomp/Cor14.3)
```

**核心発見: Thm 14.4 の "sharply transitive R(x)" headline + part(b) は repo が §16 に defer したが、その
BG 証明(L3896-3900)は §12/§13/§14 のみ使用(Thm 13.9, Thm 10.1(b), Prop 12.15, Cor 14.3, Cor 12.6)で
§15/§16 を一切使わない。** ⟹ deferral comment「importing §16 here would be circular」は *packaging* の話
(RData の def が §16 に在る)で *math* の循環ではない。S16 Theorem D
(`theoremD_msigma_conjugacy_and_centralizers`, L281)は **sorry**(L307)ゆえ sharp transitivity は現状 repo の
どこにも証明が無い。Lem 14.5(c) の二重数え「各 x∈𝒞_G(M_σ^#) は丁度 |R(x)| 個の M^g に属す」(BG L3937)が
sharp transitivity を要するため、14.7 完全証明には **§14 で 14.4 sharp transitivity を証明する**のが唯一の道
(§16 を import できない=cycle)。これで S16 Theorem D の sorry も §14 cite で消せる(bonus, Lane G 領域)。

**実装方針(lane-h, head-on):**
1. **Thm 14.4 sharp transitivity / regular action**(新 standalone theorem, §14)。`sigmaLength_one_centralizer_structure`
   は AxiomsCheck 以外 consumer 0 ゆえ拡張/併設自由。14.4 conclusion が `IsComplement'(N_σ, M∩N in N)` を
   expose ⟹ `M∩N_σ=1` + `(M∩N)N_σ=N` 取得可。X/fusion setup(L2742-2789)+ orbit-stabilizer
   (regular action: ∀M,L∈𝓜_σ(x) ∃! r∈N_σ∩C_G(x), L=M^r)を再構成。~100行見込。
2. **R(x) 関数化 + M̃ 定義**(R: G→Subgroup G via ∃! N の choice; M̃ = ⋃_{x∈M_σ^#} xR(x))。
3. **Lem 14.5(a)** then **(c)**(Finset.sum 二重数え; 難)。
4. **Lem 14.6** dichotomy(難)。
5. **Thm 14.7** 本体(M_i setup L3993-4015 + T の TI + counting 矛盾 + covering + part h)。

**見積もり訂正**: memory の「~2-3.5 session」は楽観的。14.4 sharp transitivity だけで 1-2 session、
全 chain で realistically 5-10 session。これが FT critical path の真の long pole。

### ✅ 14.4 sharp transitivity DONE + 🔬 σ-decomposition は必須前提と判明 (2026-06-16 lane-h loop 続き)

**✅ Thm 14.4 sharp transitivity COMPLETE** (commit `74bc9678`, sorry-free + axiom-clean, full build 3832 jobs):
`sigmaLength_one_centralizer_structure` に **4th per-M conjunct** = 正則作用を追加。N (14.4 の ∃!) と
R(x)=N_σ∩C_G(x) に対し、∀L∈𝓜_σ(x) ∃! r∈R(x) で `conj r•M = L`。証明は既存 ∃!N+補群(hsigmaInf₂/hsigmaSup₂)
を再利用し hRx の v-construction を任意 L へ一般化 (fusion Thm10.1b → c=v·a 分解 → conj(x⁻¹vx)•M=conj v•M
+ freeness)。**これは §16 Theorem D の sorry だった部分を §14 で証明したもの。**

**🔬 次の必須前提 = σ-decomposition theory (BG §1, L3791-3795) — repo 未形式化:**
- BG def: σ(M) (conj-class reps) が π(G) を分割 → {σ_1,...,σ_s}。各 g∈G は **一意に** g=g_1⋯g_s
  (pairwise commuting σ_i-elements, g_i∈⟨g⟩) と書ける = **巡回群 ⟨g⟩ の σ-分割による Hall 分解**。
  ℓ_σ(g) = 非自明 g_i の個数。
- repo 現状: `SigmaDecompositionData` は `length`+`length_one_iff` のみ (実分解なし)。L2615 に dummy D 構成あり。
  **downstream (S15/S16/AppC/Pf) は SigmaDecompositionData を一切構成しない** (grep 確認)。
- **しかし 14.7 (`typeP_duality`, D 引数なし) の証明は counting (14.5c/14.6) を要し、それらは σ-decomposition を
  要する。14.7 の signature は consumer (S15:785/795/2170, S16:530) で固定ゆえ D 引数追加不可
  ⟹ 14.7 証明内で実 σ-decomposition (D) を構成せねばならない。scaffold 退避不可。**
- ⟹ **σ-decomposition は FT critical path の必須前提**。mathlib に element π-decomposition の既製補題なし
  (`Nat.factorization`/`ZMod` CRT から構築要)。~1-2 session 見込。

**改訂 gate chain (14.4 sharp transitivity 後):**
```
σ-decomposition theory (BG §1) ← 次の必須前提 (NEW, repo 未形式化)
  ├─ σ-class partition of π(G) (Thm 13.9 disjoint + every-prime-in-some-σ(M))
  ├─ element decomposition g=∏g_i (Hall components of ⟨g⟩) + uniqueness
  └─ ℓ_σ def + SigmaDecompositionData の length とのbridge
→ R(x) function (via 14.4 ∃!N choice) + M̃ = ⋃_{x∈M_σ^#} xR(x)
→ Lem 14.5(a) xR(x)∩yR(y)=∅ (σ-decomp uniqueness) + (c) count (sharp transitivity 二重数え)
→ Lem 14.6 dichotomy (σ-decomp + Cor14.3 + 14.4c)
→ Thm 14.7 typeP_duality (counting 矛盾 n=1 + covering + part h)
```
realistically 6-10 session。memory「~2-3.5 session」は σ-decomposition 前提を見落としていた。

### ✅ π-part 元分解 DONE + 14.5(a) reduction 設計 (2026-06-16 lane-h loop 続き²)

**✅ `OddOrder/GroupTheory/PiElementDecomposition.lean` COMPLETE** (commit `bd2f8aff`, sorry-free +
axiom-clean, full build 3833 jobs): 巡回 ⟨g⟩ の 2-block (π, π') Hall 分解 = σ-decomposition の基礎 primitive。
- `IsPiElement π g` := `∀ p ∈ (orderOf g).primeFactors, p ∈ π`。
- `exists_isPiElement_mul`: `∃ a b, a*b=g ∧ Commute a b ∧ IsPiElement π a ∧ IsPiElement πᶜ b ∧ a,b∈zpowers g`
  (CRT 指数 `Nat.chineseRemainder` で a=g^e, b=g^f; a^nπ=1 via nπ'|e で gcd 回避)。
- `isPiElement_mul_unique`: 両分解一致 (a,a'∈⟨g⟩ から u=a'⁻¹a が π かつ π'-element ⟹ orderOf u=1)。
- helper: `coprime_orderOf_of_isPiElement` / `isPiElement_mul_of_commute` / `commute_of_mem_zpowers` /
  `mem_zpowers_of_mul_eq` / `natPiPart` + mul/coprime/primeFactors。

**🔑 14.5(a) は full s-part σ-decomposition 不要、2-part tool + 13.9 + σ-class partition で可** (設計):
- g = x·x' (x'∈R(x)⊆N_x,σ): x' は σ(N_x)-elt, σ(N_x)∩σ(M_x)=∅ (13.9) ⟹ x' は σ(M_x)'-elt ⟹
  **x = σ(M_x)-part of g** (2-part uniqueness, π=σ(M_x))。同様 x = σ(N_x)'-part, x' = σ(N_x)-part。
- g ∈ yR(y) ⟹ g = y·w (w∈R(y)): primes(g)=primes(x)∪primes(x')⊆σ(M_x)∪σ(N_x)。y≠1 は σ(M_y)-part of g
  ⟹ σ(M_y) は g の nontrivial class ⟹ σ(M_y)∩(σ(M_x)∪σ(N_x))≠∅ ⟹ **σ(M_y)=σ(M_x) or σ(N_x)**
  (partition: 13.9 disjoint + `sigma_conj` [S10_HallStructureCore:619] で conjugate⟹σ equal)。
  - σ(M_y)=σ(M_x): y=σ(M_x)-part=x, x≠y 矛盾。
  - σ(M_y)=σ(N_x): y=σ(N_x)-part=x' ⟹ y=x'。同様 w=x。x∈R(y)⊆..., y=x'∈R(x)⊆N_x,σ ⟹
    y∈M∩N_σ=1 矛盾 (BG L3923)。
- ⟹ **σ-class partition の "equal-or-disjoint" + `sigma_conj` があれば s-part 構築は回避可能**。

**次の H 作業 (順に)**:
1. **σ-class equal-or-disjoint helper** (13.9 `sigma_disjoint_of_nonconjugate` + `sigma_conj`):
   `σ(M)∩σ(M')≠∅ → σ(M)=σ(M')` (M,M'∈𝓜)。small。
2. **R(x) function** (`Rsub hG D x` via 14.4 ∃!N の Classical.choice; |𝓜_σ(x)|=1 で ⊥) + **M̃**。
3. **Lem 14.5(a)** (上記 reduction) → **(c)** count (sharp transitivity 二重数え) → **14.6** → **14.7**。

### ✅ 14.5(a) gap SOLVED — 14.4(e) で contradiction (ChatGPT 不要, 2026-06-16 lane-h loop³)

**BG L3923 の terse "y∈N_σ∩M=1" を完全再構成** (key = 14.4(e) complement、my 14.4 conclusion に在る):

設定: g ∈ xR(x) ∩ yR(y), x≠y, ℓ_σ(x)=ℓ_σ(y)=1。g = x·x' (x'∈R(x)) = y·y'' (y''∈R(y))。
R(z)⊆C_G(z) ゆえ x'·x=x·x', y''·y=y·y'' (commute)。

**Case |𝓜_σ(x)|=1** (R(x)=⊥, x'=1, g=x): g=x=y·y''。
- |𝓜_σ(y)|=1: y''=1, x=y 矛盾。
- |𝓜_σ(y)|>1: x=y·y'', y σ(M_y)-elt, y'' σ(M_y)'-elt (y''∈N(y)_σ, σ(N(y))∩σ(M_y)=∅) ⟹ y=σ(M_y)-part of x。
  x は σ(M_x)-elt: σ(M_x)=σ(M_y) なら x=y 矛盾; 違えば x の σ(M_y)-part=1=y, y≠1 矛盾。
**Case |𝓜_σ(y)|=1**: 対称。
**Main case |𝓜_σ(x)|>1 ∧ |𝓜_σ(y)|>1**:
- 14.4 for x → N(x), R(x)=N(x)_σ∩C_G(x); for y → N(y), R(y)=N(y)_σ∩C_G(y)。
- **factor matching** (2-part tool `isPiElement_mul_unique` + σ-class helper `sigma_eq_of_mem_sigma_of_mem_sigma`):
  x,x',y,y''∈⟨g⟩ (mem_zpowers_of_mul_eq, coprime commute)。π=σ(M_y) で y=σ(M_y)-part of g。
  g=x·x' の σ(M_y)-part: x σ(M_x)-elt, x' σ(N(x))-elt (x'∈R(x)⊆N(x)_σ), σ(M_x)∩σ(N(x))=∅。
  partition で σ(M_y)∈{σ(M_x),σ(N(x))}: σ(M_x) なら y=x 矛盾; ⟹ **σ(M_y)=σ(N(x)), y=x'**。
  commute cancel: x·x'=y·y''=x'·y'' ⟹ (x' で消去) **x=y''**。
- ⟹ **y=x'∈R(x)⊆N(x)_σ** & **x=y''∈R(y)⊆N(y)_σ**。
- ⟹ **N(y)∈𝓜_σ(x)** (x∈N(y)_σ)。**14.4(e) for x with M=N(y)**:
  `IsComplement'(N(x)_σ.subgroupOf N(x), (N(y)⊓N(x)).subgroupOf N(x))` ⟹ N(x)_σ ⊓ (N(y)⊓N(x)) = ⊥。
- y∈N(x)_σ (⊆N(x)) ∧ y∈N(y) (y∈C_G(y)⊆N(y)) ⟹ y∈N(x)_σ ⊓ (N(y)⊓N(x)) = ⊥ ⟹ **y=1 矛盾**。

**⟹ ChatGPT 不要。14.4(e) が "N_σ∩M=1" の正体。** 全 case 矛盾 ⟹ xR(x)∩yR(y)=∅。formalize は
~150-250 行 (4-case + factor matching が bulk)。my 14.4 conclusion に (e) + sharp + (c) すべて在る。

### 14.5(a) building blocks DONE + 残 assembly 設計詳細 (2026-06-16 lane-h loop³ 続き)

**✅ committed** (`d87e7d79`): `exists_neighbor_eq_Rsub` (14.4 出力 package: N, R=N_σ∩C_G, π(⟨z⟩)⊆τ₂N, (e))
+ `isPiElement_sigmaCompl_of_mem_Rsub` (r∈R(z) は σ(M)'-elt, M∈𝓜_σ(z))。+ `Rsub_le_centralizer`,
`Rsub_eq_inf`, `sigma_eq_of_mem_sigma_of_mem_sigma`, `Mtilde`, π-part decomposition (別 leaf)。

**残 = 14.5(a) assembly (`xRsub_disjoint`), nested 4-case (~200行, 機械的, gap なし)**:
g=x·x'=y·y'' (x'∈R(x), y''∈R(y))。M_x∈𝓜_σ(x) (x∈M_x,σ, x は σ(M_x)-elt), M_y 同。
x' は σ(M_x)'-elt (building block), x' commute x (Rsub_le_centralizer)。同 y''。
- **case σ(M_x)=σ(M_y)**: x σ(M_y)-elt, x' σ(M_y)'-elt ⟹ g=x·x' (σ(M_y),σ(M_y)')-split;
  g=y·y'' も。`isPiElement_mul_unique` ⟹ x=y, hxy 矛盾。
- **case σ(M_x)∩σ(M_y)=∅** (helper の contrapositive):
  - **|𝓜_σ(x)|>1**: `exists_neighbor_eq_Rsub` for x → N(x), x'∈N(x)_σ ⟹ primes(x')⊆σ(N(x)) (single class)。
    x' を π=σ(M_y) で split (x'=a·b, exists_isPiElement_mul): g=x·x'=a·(x·b) (x σ(M_y)'-elt), uniqueness
    vs y·y'' ⟹ y=a=σ(M_y)-part of x'。y≠1 ⟹ σ(M_y)∩σ(N(x))≠∅ ⟹ σ(M_y)=σ(N(x)) ⟹ x' σ(M_y)-elt ⟹
    **x'=y**。commute cancel ⟹ **x=y''**。⟹ x=y''∈R(y)⊆N(y)_σ ⟹ **N(y)∈𝓜_σ(x)** ⟹ `exists_neighbor`
    (e) for x with M=N(y): N(x)_σ⊓(N(y)⊓N(x))=⊥; y∈N(x)_σ(=x'∈R(x)) ∧ y∈N(y)(C_G(y)) ∧ y∈N(x) ⟹
    y∈⊥ ⟹ **y=1 矛盾**。
  - **|𝓜_σ(x)|=1** (x'=1, g=x): g=x σ(M_x)-elt = y·y''。σ(M_x)-part: y σ(M_x)'-elt ⟹ x=σ(M_x)-part of y''。
    |𝓜_σ(y)|=1 ⟹ y''=1, x=y 矛盾; |𝓜_σ(y)|>1 ⟹ y''∈N(y)_σ single class, 対称に x=y'' ⟹ g=x=y·x ⟹ y=1 矛盾。
- helper 名: `isPiElement_mul_unique`/`exists_isPiElement_mul` (PiElementDecomposition),
  `exists_neighbor_eq_Rsub`/`isPiElement_sigmaCompl_of_mem_Rsub`/`commute_of_mem_zpowers`。

### ✅✅ 14.5(c) COMPLETE — |𝒞_G(M̃)| = (|M_σ|−1)·[G:M] (2026-06-16 lane-h loop⁴, commit b9a7031b)

**`sigmaConjugacySaturation_Mtilde_ncard` sorry-free + axiom-clean** (AxiomsCheck 登録、full build
3838 jobs ~65s)。Part A (`sigmaSaturation_Rsub_count`, 既 landing) + 新 Part B (cover) で締め。

**Part B = cover `𝒞_G(M̃) = ⊔_{x∈𝒞_G(M_σ^#)} xR(x)`。核心 = R-同変性 `R(gxg⁻¹)=(conj g)•R(x)`。**
Classical.choice の literal tracking は不要 — **「N(x) = C_G(x) を含む唯一の極大」characterization**
経由 (uniqueness で choose(xᵍ)=choose(x)ᵍ):
- `exists_neighbor_Rsub_singleton`: 14.4 spec から N(x) + 𝓜(C_G(x))={N(x)} (Cor 14.3
  `maximalContaining_centralizer_eq_singleton_of_tau2_element` に spec data を供給)。
- `maximalSigmaSubgroupsOfElement_conj`: 𝓜_σ(gxg⁻¹) = (conj g)•𝓜_σ(x) (image)。R の if-条件
  (length via length_one_iff, ncard via image bijection) が共役不変 ⟹ 両 branch 整合。
- `Rsub_conj`: N(x)ᵍ は C_G(gxg⁻¹) を含む極大 ⟹ singleton で = N(gxg⁻¹); N_σ∩C_G が共役。
  道具 = `Msigma_conj_smul`/`smul_centralizer_singleton`(S14_Prop142Support, import 追加)/`Subgroup.smul_inf`。
- `conjClassSet_Mtilde_eq_biUnion`: cover 集合等式 (両包含、Rsub_conj + g=(xᵍ)(x'ᵍ) factoring)。
- 最終 count: `Set.Finite.ncard_biUnion` (14.5a disjoint) + `Set.ncard_smul_set` (|xR(x)|=|R(x)|) + Part A。

**🔑 重要: 14.5(c) は full σ-decomposition を回避** (Part B は R-同変性 + 2-block で済んだ)。
**しかし 14.6 は回避不可** (下記)。

### ▶ 次 = Lemma 14.6 dichotomy — **σ-decomposition の length-1 factor 抽出が必須前提**

**BG Lem 14.6** (mmd L3945): g∈G^# は排他的に 2 条件の一方を満たす:
1. g=xx', ℓ_σ(x)=1, x'∈R(x)  (= g ∈ 何らかの xR(x))
2. g=yy', ℓ_σ(y)=1, y' は C_M(y) の非自明 κ(M)-element (∃M∈𝓜_P(y))

**証明が要する σ-decomposition (回避不可)**: ℓ_σ(g)>1 のとき「g の σ-decomposition の σ-length-1 factor x
を取る」(g=xx', x∈⟨g⟩, x'∈⟨g⟩ commute, x は σ(M)-elt for M∈𝓜_σ(x))。これは 2-block tool では不足 —
**「σ(M)-element a≠1 が ℓ_σ(a)=1 をもつ (=∃ maximal M', a∈M'_σ)」が要**。⟹ σ(M)-部分群が
M_σ-conjugate に入る Hall 論法 (`sigma_subgroup_le_Msigma_of_isHall` 系) が核。
14.6 proof のその他 deps = Cor 14.3 / Thm 14.4(c)(e) / Thm 13.9 / R(x)=C_{M_σ}(x') — repo 在。

**改訂 gate chain:**
```
✅ Prop 14.2 / Lem 12.17 / Cor 14.3 / Thm 13.9 / half_lt / Thm 14.4 sharp / M̃ /
   14.5(a) xRsub_disjoint / 14.5(b) Mtilde_disjoint / 14.5(c) ncard  ← 全 DONE
σ-decomposition existence (length-1 factor 抽出) ← 次の必須前提 (新 leaf 候補)
  └─ 「σ(M)-elt a≠1 ⟹ ℓ_σ(a)=1」(a∈⟨g⟩, ⟨a⟩ σ(M)-group ≤ M_σ^conj)
→ Lem 14.6 dichotomy (上記 + Cor14.3/14.4(c)(e)/13.9)
→ Thm 14.7 typeP_duality (M_i setup L3993-4015 + Ẑ TI + counting 矛盾 n=1 + covering + part h)
   = FT-critical (S15:785/795/2170, S16:530 consume)
```
realistically 14.6=1-2 session (σ-decomp leaf 込)、14.7=2-3 session。

### ✅ σ-decomposition keystone DONE + foundation-2/factor-extraction 設計 (2026-06-16 loop⁴ 続き, commit d24bdd7f)

**✅ `length_one_of_isPiElement_sigma` COMPLETE** (sorry-free + axiom-clean + AxiomsCheck): 非自明
σ(M)-element x ⟹ ℓ_σ(x)=1。⟨x⟩ は非自明 proper σ(M)-subgroup (proper = G 非可解⟹非巡回,
`isSolvable_of_comm` で htop 矛盾) → `sigma_subgroup_conj_into_Msigma_general` で M_σ-conjugate →
conj g⁻¹•M ∈ 𝓜_σ(x)。**14.6 の length-1 factor 抽出の核。**

**▶ 次 (Lemma 14.6 への残り、順に):**

**Foundation 2 = 「全素数 p||G| ∈ 或る σ(M)」** (BG §1 明記, `exists_mem_sigma_of_prime_dvd_card`):
構成 = Sylow p P of G → N_G(P)<⊤ (P≠⊥ ∵ p||G|; P◁G なら G simple と矛盾 ∵ ⊥≠P≠G[G 非 p-group]) →
maximal M ⊇ N_G(P) → P は M の Sylow p (P≤M, |P|=p-part|G|) → `mem_sigma_iff` (p||M| ∧ ∃Q:Sylow p ↥M,
N_G(Q-image)≤M; Q=P, image=P, N_G(P)≤M ✓)。~50-80行 (Sylow/simplicity)。helper = maximal-containing-proper
(`exists_le_maximal` 系 / S08 `exists_maximalSubgroup_containing_normalizer...`), Sylow-of-M restriction。

**Factor extraction** (`exists_length_one_factor`): g≠1 → prime p||g| → p∈σ(M) [Found.2] →
2-block split g=x·x' (`exists_isPiElement_mul`, π=σ(M)) → x=σ(M)-part≠1 (p||x|) → ℓ_σ(x)=1 [lemma A] →
x,x'∈⟨g⟩ commute, x' σ(M)'-elt。~40行。

**Lemma 14.6 dichotomy** (`sigmaDecomposition_dichotomy`, ~120-180行, intricate):
排他的 (1) g=xx', ℓ_σ(x)=1, x'∈R(x) / (2) g=yy', ℓ_σ(y)=1, y'=非自明 κ(M)-elt of C_M(y), M∈𝓜_P(y)。
- 排他性 (1∧2→⊥): 2-block uniqueness (`isPiElement_mul_unique`) で y∈{x,x'} → Cor14.3 + 14.4(c) →
  y=x' → 13.9 で M,N conjugate → κ(M) vs τ₂(N) 矛盾。
- 全域性 (¬1∧¬2→⊥): ℓ_σ(g)>1 (¬1), length-1 factor x [extraction], g=xx', M∈𝓜_σ(x), N∈𝓜(C_G(x))。
  g∈M なら x' σ(M)'∧¬κ(M) → Cor14.3 ℓ_σ(x')=1,𝓜(C_G(x'))={M} → x∈C_{Mσ}(x')=R(x') → (1) 矛盾。
  g∉M → C_G(x)⊄M → g σ(N)'-elt of N → 14.4(e) complement → g∈(M∩N)^a → g∈M^a, x∈M_σ^a → M^a 選べた → g∉M 矛盾。
  deps = Cor14.3/14.4(c)(e)/13.9/R(x)=C_{Mσ}(x') 全 repo 在。
**14.6 着地で 14.7 へ。新 leaf 化 (S14_SigmaDecomposition) は 14.6 規模で hub prefix-split 推奨 (S14 既 4175行)。**

### ✅✅ σ-decomposition existence 機構 COMPLETE (2026-06-16 loop⁴ 続き², commits d24bdd7f + a0bbfefa)

**3 lemma すべて sorry-free + axiom-clean + AxiomsCheck:**
- `length_one_of_isPiElement_sigma` (keystone): σ(M)-element x≠1 ⟹ ℓ_σ(x)=1。
- `exists_mem_sigma_of_prime_dvd_card` (foundation 2): 全素数 p||G| ∈ 或る σ(M)。Sylow P non-normal
  (G 非可解⟹非 p-group, `IsPGroup.isNilpotent`+`IsNilpotent.to_isSolvable`) → N_G(P) ≤ maximal M
  (`eq_top_or_exists_le_coatom`) → P = M の Sylow p (p-parts 一致, `Sylow.ofCard`+factorization) →
  `mem_sigma_iff`。鍵 API: `Sylow.ne_bot_of_dvd_card`/`Sylow.card_eq_multiplicity`/`subgroupOf_map_subtype`。
- `exists_length_one_factor` (extraction): g≠1 → p||g| → σ(M) → 2-block split (`exists_isPiElement_mul`) →
  σ(M)-part x が ℓ_σ=1。返り = (x,x',M, g=xx', commute, x,x'∈⟨g⟩, ℓ_σ(x)=1, M maximal, x σ(M)-elt, x' σ(M)'-elt)。

**⟹ 14.6 の「σ-length-1 factor 抽出」前提は完全に揃った。残りは 14.6 dichotomy proof 本体。**

**▶ 次 = Lemma 14.6 dichotomy 本体** (intricate, 14.7 消費形と結合設計要):
- statement: g∈G^# は排他的に (1) g=xx', ℓ_σ(x)=1, x'∈R(x) / (2) g=yy', ℓ_σ(y)=1, y'=非自明
  `IsPiElement (kappa M) y'` ∈ C_M(y), M∈𝓜_σ(y)∩IsTypeP。**14.7 が要するのは exclusivity 方向**
  (type-2 ⟹ ¬type-1 = g∉H̃; "T∩H̃ empty" L4021)。exhaustivity は "exactly one" 完全性用。
- 定義は全在: `kappa`/`IsTypeP`/`maximalSigmaSubgroupsOfElement`/`Rsub`/`Mtilde`。𝓜_P(y)=`{M∈𝓜_σ(y)|IsTypeP M}` inline。
- 排他性 proof: 2-block uniq (`isPiElement_mul_unique`) で y∈{x,x'} → Cor14.3(`sigma_diagnostic`)+14.4(c) →
  y=x' → x'∈R(x)⊆N_σ, y∈M∩N_σ → 13.9 で M,N conj → κ(M) vs τ₂(N) 矛盾。~60-80行。
- 全域性 proof: ℓ_σ(g)>1 [¬1], `exists_length_one_factor` で x, g=xx', M∈𝓜_σ(x), N∈𝓜(C_G(x))。
  g∈M → x' σ(M)'∧¬κ(M) → Cor14.3 ℓ_σ(x')=1, 𝓜(C_G(x'))={M} → x∈C_{Mσ}(x')=R(x') → (1) 矛盾。
  g∉M → C_G(x)⊄M → g σ(N)'-elt of N → 14.4(e) complement → g∈(M∩N)^a → x∈M_σ^a → M^a 選べた → 矛盾。~100-150行。
- 推奨: **14.7 が consume する exclusivity を named lemma 化**してから full "exactly one"。新 leaf S14_SigmaDecomposition
  (S14 既 4250行) へ移すなら hub prefix-split (issue 0069)。

### ✅✅✅ BG Lemma 14.6 exclusivity COMPLETE (2026-06-16 loop⁴ 続き³, commit a1519e5b)

**`not_type1_of_type2` sorry-free + axiom-clean + AxiomsCheck** (~180行 factor-matching, 一発 green
+ namespace 1 修正のみ): type-2 (g=y·y', y∈M_σ^#, y'=非自明 κ(M)-elt of C_M(y)) ⟹ ¬type-1
(g=x·x', ℓ_σ(x)=1, x'∈R(x))。**14.7 が "T∩H̃=∅" として消費する FT-critical 方向。**
証明 = 14.5(a) factor-matching (`isPiElement_mul_unique`+σ-partition) を σ-decomposition existence
機構で駆動。x'≠1 → |𝓜_σ(x)|>1 → N (π(⟨x⟩)⊆τ₂(N), 𝓜(C_G(x))={N})。
- equal σ(M_x)=σ(M): x=y, Cor14.3 (C_G(y)⊆M, τ₂枝は κ∩τ₂=∅[rank 1 vs 2]で排除)+singleton → M=N →
  x∈M_σ が τ₂(M)-elt = 矛盾。
- disjoint: factor-match y=x', y'=x; M,N conj (13.9); x=y' は κ(M)[pRank 1] & τ₂(N)[pRank 2],
  pRank 共役不変 (`pRank_eq_of_mulEquiv` + `equivMapOfInjective`+`MulEquiv.subgroupCongr`) で 1=2 矛盾。
新 API 発見: `tau1/tau3_subset_sigma_compl`, `tau{1,2,3}_pRank_eq_{one,two}`, `pRank_eq_of_mulEquiv`(S13)。

**⟹ Lemma 14.6 は FT 的に done** (14.7 は exclusivity のみ要; exhaustivity = "exactly one" 完全性は
14.7 非依存ゆえ後回し可)。

### ▶ 最終 §14 FT-critical ピース = Theorem 14.7 `typeP_duality` (S14:4475, sorry)
**全依存 green**: 14.5(c)✅ 14.5(b)✅ 14.6 exclusivity✅ Prop14.2✅ half_lt✅ Thm14.4✅。
statement (既存, faithful): (h) M'=derivedInG M が K を complement + coprime ∧ ∃! Mstar
[maximal∧typeP∧¬conj∧Hall κ∧cyclic(K⊔Kstar)∧TI(zTilde)∧(P2 M∨P2 Mstar)∧covering]。
**proof = §14 最大の counting** (mmd L3993-4063, ~200行超):
- M_1..M_n = 𝓜(N_G(X_i)) for X_i∈ℰ¹(K); Prop14.2(b) で Z=K×Kstar⊆M_i, X_i⊆M_iσ。
- T=Z-⋃K_i*; **14.6 exclusivity で T∩H̃=∅** → 𝒞_G(T) ⊥ 𝒞_G(M̃_i); |𝒞_G(T)|=|T||G:Z| (TI, Prop14.2d)。
- 全 M_i type-P1 仮定 → **14.5(c)** |𝒞_G(M̃_i)|=(|M_iσ|-1)|G:M_i| + 14.5(b) pairwise disjoint →
  |G^#|≥|𝒞_G(T)|+Σ → ≥|G| 矛盾 → ∃ M_i type-P2 → Prop14.2(g) n=1, Z cyclic, T=Ẑ →
  **half_lt** |𝒞_G(Ẑ)|>½|G| → covering (∀ type-P H, 𝒞_G(S_H)>½|G| ⟹ 交差 ⟹ H~M or M*)。
- part(h): M_σ⊆M' (Thm10.2c) + K cyclic + Prop14.2(a) normal complement UM_σ → UM_σ=M' → κ=τ₁。
realistically 2-4 session (counting infra + ∃! covering assembly)。新 leaf S14_Theorem147 推奨 (hub split)。

### ✅ Theorem 14.7 着手 — TI saturation count COMPLETE (2026-06-16 loop⁴ 続き⁴, commit b53d8c6c)

**`ncard_conjClassSet_of_isTISubset` sorry-free + axiom-clean + AxiomsCheck**: TI-subset A
(stabilized by normalizer-bound L) ⟹ |𝒞_G(A)|=|A|·[G:L]。conjugates を G⧸L で index
(L-stab で well-def, Quotient.lift)、TI で pairwise disjoint、各 ncard |A| (`Set.ncard_smul_set`)、
`Set.ncard_iUnion_of_finite`+`finsum_eq_sum_of_fintype` で合計。**14.7 step 5 (|𝒞_G(T)|=|T||G:Z|) の核。**
鍵 API: `Set.ncard_iUnion_of_finite`, `finsum_eq_sum_of_fintype`(to_additive), Quotient.lift+`change (leftRel L)`。
再利用可: Peterfalvi TI-subset counting にも (現状 S14 内、upstream 候補=TISubset.lean)。

**▶ 14.7 残ピース** (順に、新 leaf S14_Theorem147 推奨):
1. **M_i family setup** (~100行, 最 intricate): X_i∈ℰ¹(K) → M_i=𝓜(N_G(X_i)); Prop14.2(b) で Z⊆M_i,
   X_i⊆M_iσ; M_i 非conj-to-M; K_i=Hall κ(M_i), K_i*=C_{M_iσ}(K_i); N_{M_i}(X*)=K_i×K_i*。
2. **density arithmetic** (~50行): |𝒞_G(T)|=(1+n/z-Σ1/k_i)|G| [TI count] + (全P1) 14.5(c) Σ → |G^#|≥|G| 矛盾。
3. **∃! covering** (~80行): n=1, T=Ẑ, half_lt >½|G|, S_H 交差 → H~M or M*。
4. **part(h)** (~50行, §16-indep): M_σ⊆M'(Thm10.2c)+Prop14.2(a) UM_σ+K cyclic → UM_σ=M', κ=τ₁。
これらを組んで `typeP_duality` (S14:4475 sorry) を close → §15/§16 (Lane G) 全下流 unblock。

### ✅ Z=K⊔K* 直積 foundation + 🔑 part(h) gating 訂正 (2026-06-16 loop⁵, commit 87e8a77d)

**✅ `Z=K⊔K*` 内部直積 foundation COMPLETE** (8 lemma, sorry-free + axiom-clean, full build 3838/~66s):
`kappaHall_isPiSubgroup_sigmaCompl` (K=σ'群) / `Kstar_isPiSubgroup_sigma` (K*≤Mσ=σ群) /
`coprime_card_kappaHall_Kstar` (`Coprime |K||K*|`, L4027) / `kappaHall_inf_Kstar_eq_bot` (K⊓K*=⊥) /
`commute_kappaHall_Kstar` (K*≤C_G(K)) / `kappaHall_prod_Kstar_mulEquiv` (↥K×↥K*≃*↥(K⊔K*),
noncommCoprod, S13 の inj+range recipe 再利用) / `card_kappaHall_sup_Kstar` (`|Z|=|K||K*|`, L4029=z) /
`isCyclic_kappaHall_sup_Kstar_of_cyclic` (両 cyclic⟹Z cyclic via `Group.isCyclic_prod_iff`, conjunct d)。
K=Hall κ + K*=C_{Mσ}(K) のみ依存 (counting 非依存)。density 式 (L4031-4045) と cyclic conjunct の土台。

**🔑🔑 訂正: 上記「4. part(h) §16-indep」は誤り** — part(h) は **14.7 の最終ステップで、独立抽出不可**:
- τ₁/τ₃ 定義 (`tau1={p∉σ∧p∉π(M')∧rank1}`, `tau3=同 but p∈π(M')`, S12_ECore:51) ⟹ `κ=τ₁ ⟺ Coprime |K||M'|`。
  part(h) の `M'=UM_σ ⟹ κ=τ₁` は BG L4061 で **「K cyclic」を消費**、K cyclic は L4174 明記どおり
  14.7(d) = **14.7 自身の counting collapse (n=1, L4041, r(K)=r(K*)=1)** 由来。§16 ではないが counting の後。
- **Prop 14.2(a) の「UM_σ は K の normal complement」は repo 未パッケージ**: E-setup 断片
  (`SubgroupESetup`, `isFrobeniusGroup_E_of_caseTau1` E=U⋊E₁ [U=E₂E₃], `actsRegularlyOn_E23_E1_of_caseTau1`)
  のみ存在、assembled「UM_σ normal complement of K in M」は無 (case κ⊆τ₁ vs κ∩τ₃≠∅[K=E,U=1] で split)。
  part(h) には **先に Prop 14.2(a) packaging** が要る (missing prerequisite)。
- ⟹ **14.7 全体が 1 つの interlocked counting**: conjunct d/cyclic/part h/covering すべて n=1 collapse
  から。Lane G (S15:806 part h consume, S15:816 cyclic consume) は 14.7 landing まで gated。
- 次の最有力 = M_i family setup (crux=swap 論法 L3999-4001 `Z=K_i×K_i*`) → density → covering →
  Prop 14.2(a) packaging → part(h)。新 leaf S14_Theorem147 は hub split (issue 0069)。

### ✅✅ M_i family setup — swap 論法 COMPLETE + pairwise disjoint K_i* (2026-06-16 loop⁶, 4 commits)

**✅ swap 論法 `Z = K⊔K* = K_i⊔K_i*` COMPLETE** (mmd L3999-4001、M_i family setup の最 intricate 部、
sorry-free + axiom-clean、full build 3838/~66s)。7 新定理:

- `typeP_normalizer_inf_eq` — **Prop 14.2(b1) を neighbor 用に packaging**: `N_G(X) ⊓ Mi = Ki ⊔ C_{Miσ}(Ki)`
  (Mi type-P, Ki Hall κ(Mi), X∈ℰ¹ ≤ Ki)。Hall (κ∪σ)' は `hall_E_exists` で内部生成 ⟹ caller は Ki,X のみ供給。
- `typeP_swap_Z_le` — **swap 方向 ⊆**: `K⊔K* ≤ Ki⊔Ki*`。K-part = K が X*(≤K*) を centralize ⟹ K≤N_G(X*)⊓Mi。
  K*-part (**swap 本体**) = K* は κ(Mi)-群ゆえ ∃ Hall κ(Mi)-subgroup Ki'⊇K*、`N_G(X*)⊓Mi=Ki'⊔Ki'*=Ki⊔Ki*`
  は Hall 選択に非依存 ⟹ K*≤Ki'≤Ki⊔Ki*。
- `normalizer_le_of_maximalSubgroupsContaining_centralizer` — **N_G(X) ≤ M** (mmd L3992「M⊇N_G(X*)」、§13非依存
  一般補題): `𝓜(C_G(X))={M}` (Prop 14.2c) ⟹ g∈N_G(X) は C_G(X) を共役固定 ⟹ Mᵍ も C_G(X) 含む極大 ⟹ Mᵍ=M
  (singleton) ⟹ g∈N_G(M)=M (極大自己正規化)。再利用 API = `map_centralizer_eq_of_bijective` /
  `conj_smul_eq_self_of_mem_normalizer` (OddOrder.GroupTheory, set-normalizer↔conj-fix bridge) /
  `isCoatom_conj_smul` (S12) / `pointwise_smul_le_pointwise_smul_iff` / `normalizer_eq_self_of_mem_maximalSubgroups`。
  **🔑 注: このmathlib版は `Subgroup.normalizer : Set G → Subgroup G` (set-normalizer)**。
- `le_centralizerFactor_of_le_sup_of_le_Msigma` — **σ-projection** (mmd L3999「Xi⊆Ki*」): 直積 Ki×Ki* (Ki=σ'群)
  内の σ(Mi)-群 X は σ-因子 Ki* に落ちる。`hxKstar` idiom (L2480) の一般化、decomposition x=a·b + a∈Ki⊓Mσ=⊥。
- `typeP_swap_Z_eq` — **完全等式 K⊔K*=Ki⊔Ki*** (capstone)。⊆=swap_Z_le、⊇=役割交換 (M,K,X*)↔(Mi,Ki,Xi) で
  swap_Z_le 再適用。⊇ の3前提: (A) Ki⊔Ki*=N_G(X*)⊓Mi≤M [N_G(X*)≤M 経由] / (B) π(Ki*)⊆κ(M)
  [`typeP_neighbor_kappa`: M は Mi の X* 経由 partner] / (C) Xi⊆Ki* [σ-projection]。

**✅ pairwise disjoint K_i* COMPLETE** (mmd L4005「Prop 14.2(c) applied to each M_i ⟹ K_i*∩K_j*=1」):
- `typeP_centralizer_singleton` — **Prop 14.2(c) packaging**: Y∈ℰ¹(K*) ⟹ `𝓜(C_G(Y))={M}` (Hall 内部生成)。
- `typeP_neighbor_Kstar_inf_eq_bot` — **Mi≠Mj type-P ⟹ C_{Miσ}(Ki)⊓C_{Mjσ}(Kj)=⊥**。共通元 → Cauchy で
  line Y∈ℰ¹(K_i*⊓K_j*) → {Mi}=𝓜(C_G(Y))={Mj} ⟹ Mi=Mj 矛盾。

**▶ 14.7 残ピース** (順に):
1. **family indexing** (mmd L4003-4015) — Z=K_0*×K_1*×…×K_n* (各 ℰ¹(Z) の line が或る K_i* に居る) +
   K_i=∏_{j≠i}K_j*。**design lift**: 相異な neighbor M_i の有限族 (K の line 上を走る 𝓜(N_G(X_i)) の distinct ones)
   を Finset で index 化。swap (`typeP_swap_Z_eq`) + pairwise disjoint (`typeP_neighbor_Kstar_inf_eq_bot`) が building block。
2. **density arithmetic** (L4031-4045) — T=Z−⋃K_i*、`ncard_conjClassSet_of_isTISubset`(済)+14.5(c)+`half_lt_one_sub_inv_mul`(済)
   → 全 P1 矛盾 → ∃ P2。
3. **∃! covering** (L4049-4059, n=1) → typeP_duality close → §15/§16 unblock。
4. **part(h)** (Prop 14.2(a) packaging + K cyclic、最終)。

### ✅ density 算術背骨 COMPLETE (2026-06-17 loop⁷, 2 commits) — 次 = family indexing (design lift)

**✅ inclusion-exclusion + |T| count** (BG mmd L4031、sorry-free + axiom-clean):
- `ncard_biUnion_subgroup_add_card` — 単位元のみで交わる n+1 部分群の和集合: `|⋃Sᵢ| + |s| = Σ|Sᵢ| + 1`
  (各 Sᵢ が |Sᵢ|−1 個の非単位元 [pairwise disjoint] + 共有単位元 1個)。`Finset.Nonempty.cons_induction`、
  cons step = `ncard_union_add_ncard_inter` + (Sₐ ∩ ⋃ₜ = {1}) + omega。
- `ncard_sdiff_biUnion_subgroup` — `|Z−⋃Sᵢ| + Σ|Sᵢ| + 1 = |Z| + |s|` (= BG `|T| = z + n − Σk_i*`、s.card=n+1)。
  inclusion-exclusion + complement `|Z−⋃|+|⋃|=|Z|` (`ncard_diff_add_ncard_of_subset`)。

⟹ **density 算術 (|T| の式) 完成**。Theorem 14.7 step (mmd L4031-4045 の `|𝒞_G(T)|=(z+n−Σk_i*)|G:Z|`) に直結。

### ▶▶ family indexing 設計プラン (次セッションの主タスク、math は完全に詰め済)

**目標**: 族 {M_0=M, M_1,…,M_n} (相異 maximal) + 各 K_i* ≤ Z を Finset 化し、`z = ∏k_i*` / `K_i = ∏_{j≠i}K_j*`
/ n=1 collapse を確立。building blocks 全て landing 済 (swap=`typeP_swap_Z_eq`, pairwise=`typeP_neighbor_Kstar_inf_eq_bot`,
density=`ncard_sdiff_biUnion_subgroup`)。

**族モデル**: ℱ : Finset (Subgroup G) = {M} ∪ {𝓜(N_G(X)) : X ∈ ℰ¹(K)} の distinct 群。各 M_i ∈ ℱ に
K_i* := Z の Hall σ(M_i)-subgroup (= C_{M_iσ}(K_i)、swap で一致、normal in Z ゆえ unique)。choice-heavy
(各 neighbor で K_i = Hall κ(M_i) ⊇ K*-line を選ぶ) — ここが design lift。

**crux facts (詰め済)**:
- (α) 各 K_i* = σ(M_i)-Hall of Z: swap `z=|K_i||K_i*|` (K_i=σ(M_i)', K_i*=σ(M_i)) ⟹ |K_i*|=σ(M_i)-part of z。
- (β) σ(M_i) pairwise disjoint (13.9、nonconjugate)。
- (γ) coverage: ∀ p|z, p∈σ(M_j) for some j。 p|z=|K||K*|: p|K*⟹p∈σ(M_0); p|K⟹p∈κ(M)⟹line X∈ℰ_p¹(K)の
  partner M_i で p∈σ(M_i) (`typeP_neighbor_embed`: X≤M_iσ)。
- ⟹ **z = ∏ k_i*** (pairwise coprime [β] normal Hall pieces、∏|K_i*| = ∏(σ(M_i)-part of z) = z [γ]) +
  **⊔K_i* = Z** (|⊔|=z)。**K_i = ∏_{j≠i}K_j*** (両方 σ(M_i)'-Hall of Z = unique normal)。

**n=1 collapse**: 全 P1 仮定 → density 不等式 |G^#|≥|𝒞_G(T)|+Σ|𝒞_G(M̃_i)|≥|G| 矛盾 (14.5(c)+`half_lt`+
`ncard_sdiff_biUnion_subgroup` + T TI [`ncard_conjClassSet_of_isTISubset`、要 N_G(T)=Z]) → ∃ P2 →
Prop14.2(g): |K_i| 素数 = ∏_{j≠i}k_j* (各 k_j*≥3 odd) ⟹ 単一因子 ⟹ n=1。

**残ピース** (次セッション、順に):
1. **族 Finset 構築** + per-member K_i* (choice、最も intricate)。
2. **z = ∏k_i*** + **K_i = ∏_{j≠i}K_j*** (coprime Hall 分解、要 internal product cardinality)。
3. **T = Z−⋃K_i* が TI + N_G(T)=Z** (Prop 14.2(d) + σ-decomp、`ncard_conjClassSet_of_isTISubset` に接続)。
4. **density 不等式** → n=1 collapse → Mstar 構築 + covering (`half_lt`)。
5. **part(h)** (Prop 14.2(a) packaging + K cyclic)。
- ⟹ `typeP_duality` close → §15/§16 (Lane G) 全下流 unblock。

mechanics: 新 leaf S14_Theorem147 推奨 (hub split issue 0069)。本 loop⁷ landing 10 定理 (swap 7 + density 3)
は S14 内、すべて sorry-free + axiom-clean + AxiomsCheck 登録。

### ✅ z=∏ ツール + 🔑 canonical K_i* 簡約 (2026-06-17 loop⁷ cont., 2 commits)

**✅ `card_iSup_of_pairwise_commute_coprime`** (z=∏k_i* の核): pairwise commute + pairwise coprime な
有限部分群族 ⟹ `|⊔Hᵢ| = ∏|Hᵢ|`。mathlib `independent_of_coprime_order` + `noncommPiCoprod`(inj) +
`ofInjective` + `Nat.card_pi`。⚠ `[Fintype ι]` 必須 (`∏ i`=Finset.univ ゆえ; `[Finite ι]` だと統合失敗)。

**🔑🔑 canonical K_i* = Z ⊓ M_σ(N) (`typeP_neighbor_Kstar_eq_Z_inf_Msigma`) — family を大幅単純化**:
swap `Z=K_N⊔K_N*` (K_N*=C_{Nσ}(K_N)) の下で **K_N* = (K⊔Kstar) ⊓ M_σ(N)** (=Z の σ(N)-part)。
⊆: K_N*≤Z (factor) ∧ K_N*≤M_σ(N)。⊇: Z⊓M_σ(N)=(K_N⊔K_N*)⊓M_σ(N) は σ(N)-群 in 直積 ⟹ σ-projection で K_N*。
⟹ **family の K_i* は N↦Z⊓M_σ(N) で choice-free に定義可** (per-neighbor の Hall κ(N) 選択を index から除去)。
- pairwise coprime: σ(N)∩σ(N')=∅ (13.9) から直接 (typeP_neighbor_Kstar_inf_eq_bot 不要に簡約可)。
- pairwise commute: K_i* ⊴ Z (normal、direct factor) から (要 per-neighbor swap)。
- ⟹ z=∏k_i* (card_iSup) + coverage (∀p|z, p∈σ(M_j)) で ⊔K_i*=Z。

### ▶ family Finset 構築 = 次の主タスク (tools 全て landing、canonical 簡約で de-risk 済)

残り = **族 ℱ ⊆ Finset(Subgroup G) の構築 + per-neighbor swap の threading** (normality 用):
- ℱ = {M} ∪ {N type-P neighbor}; K_i* := Z⊓M_σ(N) (canonical)。
- per-neighbor swap package: 各 neighbor N (line X_i∈ℰ¹(K) 由来) で typeP_swap_Z_eq → Z=K_N⊔K_N* → K_N*⊴Z。
  ⚠ typeP_swap_Z_eq は X_i (K の line、N 生成) と X*(Kstar の line) 両方要 ⟹ 族は K の line で index 化が自然。
- coverage: p|z ⟹ p∈σ(M_j) (p|K*→σ(M); p|K→κ(M)→line の partner で σ(N)、`typeP_neighbor_embed`)。
- ⟹ card_iSup で z=∏k_i*、inclusion-exclusion で |T|、TI で |𝒞_G(T)|、density 不等式 → n=1 → Mstar+covering。

本 loop⁷ 累計 12 定理 (swap 7 + density/tools 5: incl-excl, |T|, card_iSup, canonical-K_i*, +)、全 S14 内
sorry-free + axiom-clean + AxiomsCheck。

### ✅ per-neighbor swap package landing (2026-06-17 loop⁷ cont.²) — family の gateway

**✅ `exists_neighbor_kappaHall_swap`**: type-P M + line X∈ℰ¹(K) + maximal N⊇N_G(X) ⟹ ∃ Hall κ(N)-subgroup
K_N で **Z=K⊔K*=K_N⊔K_N*** + **canonical K_N*=Z⊓M_σ(N)**。組立 = `typeP_neighbor_embed`/`_kappa` (neighbor
data) + Cauchy で X*∈ℰ¹(K*) + Hall K_N⊇X* + `typeP_swap_Z_eq` + `typeP_neighbor_Kstar_eq_Z_inf_Msigma`。
⟹ **per-neighbor の swap + canonical K_N* が 1 call で出る**。族 Finset の各メンバーで呼ぶ foundation。

**▶ 残り family Finset assembly (per-neighbor package で大幅 de-risk)**:
1. **族 ℱ = {M} ∪ {distinct type-P neighbors}** を Finset 化 (Subgroup G の有限性)。K_i* := Z⊓M_σ(N) (canonical)。
   各 neighbor で `exists_neighbor_kappaHall_swap` → swap + K_i*⊴Z (direct factor から)。
2. **coverage** ∀p|z: p|K*→σ(M); p|K→κ(M)→line の partner N で p∈σ(N)。⟹ ⊔K_i*=Z。
3. **z=∏k_i*** = `card_iSup_of_pairwise_commute_coprime` (commute=⊴Z, coprime=σ-disjoint[13.9], ⊔=Z[coverage])。
4. **T=Z−⋃K_i* TI** (Prop14.2(d)) → `ncard_conjClassSet_of_isTISubset` で |𝒞_G(T)| → density 不等式
   (`ncard_sdiff_biUnion_subgroup`済) → n=1 collapse → Mstar+covering → `typeP_duality` close。
5. **part(h)**。

本 loop⁷ 累計 **13 定理** (swap 7 + density/tools 5 + per-neighbor package 1)、全 S14 内 sorry-free +
axiom-clean + AxiomsCheck。typeP_duality 残 = family Finset assembly + T-TI + collapse + part(h)。

### ✅ coverage primitive landing (2026-06-17 loop⁷ cont.³) — 14 定理目、family の最後の foundation

**✅ `exists_typeP_neighbor_mem_sigma`**: p prime, p|K ⟹ ∃ type-P neighbor N (¬conj, Z≤N) with **p∈σ(N)**。
line X∈ℰ_p¹(K) (Cauchy in K) → partner N (`exists_typeP_partner`) → X≤Msigma N → p∈σ(N)。M 自身 (σ-prime 側)
と合わせて **coverage ⋃σ(M_i)⊇π(Z)** ⟹ ⊔K_i*=Z。

**▶ 残り = family Finset assembly (1 大統合) — 全 foundation 揃った**:
14.7 の残務は本質的に **1 つの大きな統合証明**:
1. 族 ℱ={M}∪{neighbors} の Finset 化 (Fintype(Subgroup G)+DecidablePred、または Set.Finite.toFinset)。
2. per-member K_i*=Z⊓M_σ(N): `exists_neighbor_kappaHall_swap` で swap → K_i*⊴Z (commute); σ-disjoint で coprime;
   `exists_typeP_neighbor_mem_sigma`+M で coverage ⊔K_i*=Z。
3. **z=∏k_i*** = `card_iSup_of_pairwise_commute_coprime` (commute+coprime、⊔=Z)。
4. **T=Z−⋃K_i* TI** (Prop14.2(d)) → `ncard_conjClassSet_of_isTISubset` で |𝒞_G(T)| → density 不等式
   (`ncard_sdiff_biUnion_subgroup`+14.5(c)+`half_lt`) → **n=1 collapse** (Prop14.2(g): |K_i| 素数=∏_{j≠i}k_j*) →
   Mstar+covering → `typeP_duality` close。
5. **part(h)**。

**本 loop⁷ 累計 14 定理** (swap 7 + density/tools 5 + per-neighbor package 1 + coverage 1)、全 S14 内 sorry-free +
axiom-clean + AxiomsCheck。**14.7 の building block は全て landing**、残りは family Finset の組立統合のみ。

### ✅ pairwise nonconjugate + integration helpers (2026-06-17 loop⁷ cont.⁴) — 18 定理目

**✅ `typeP_family_nonconjugate`** (mmd L4015、族 M_i は pairwise nonconjugate ⟹ 14.5(b) disjoint):
conjugate なら σ(M₁)=σ(M₂)、Z₁,Z₂ は Z の disjoint normal τ-Halls、z₁z₂∣z=k₁z₁ ⟹ z₂∣k₁ (τ-number ∣
τ'-number) ⟹ Z₂=⊥ 矛盾。helper: `card_sup_of_commute_of_disjoint` (|H⊔K|=|H||K|, noncommCoprod) +
`commute_of_le_normalizer_of_disjoint` (A,B⊴Z, ⊓=⊥ ⟹ commute via [x,y]∈A⊓B) + `sup_le_normalizer_inf_of_commute`
(因子 normality)。

**🔑 整理 (density 論法の精査で判明)**:
- **n=1 collapse は z=∏ 不要**: |K_i| 素数 + K_i⊴Z (σ(M_i)'-Hall) + K_j*≤K_i (σ(M_i)'-subgroup が normal
  Hall に入る、π'-subgroup→π-quotient trivial) + coprime ⟹ 高々1つの j≠i ⟹ n=1。(card_iSup は off-path)
- **coverage (⊔K_i*=Z) も density に不要**: |T|=z+n−Σk_i* は pairwise ⊓=⊥ + ⋃⊆Z のみ (⊔=Z 不要)。
  covering 結論 (∀ type-P H ~ M or Mstar) は half_lt (>½|G|) の交差論法で、prime-coverage 不要。

**▶ 残り = typeP_duality の最終統合 (大きい、intricate)**:
1. **族 ℱ Finset** = {M}∪{distinct neighbors}; 各 N で swap (exists_neighbor_kappaHall_swap) + K_N*=Z⊓Msigma N
   + K_N*⊴Z; pairwise nonconjugate (typeP_family_nonconjugate)。M は i=0 (K_M*=Kstar, canonical bridge)。
2. **T=Z−⋃K_i* TI + N_G(T)=Z** (Prop14.2(d) + 14.6 で T∩M̃_i=∅) → `ncard_conjClassSet_of_isTISubset` で |𝒞_G(T)|。
3. **density 不等式** (`ncard_sdiff_biUnion_subgroup` |T| + swap z=k_i k_i* + 14.5(c) + 14.5(b) disjoint +
   14.6 で 𝒞_G(T)⊥𝒞_G(M̃_i)) → 全 P1 矛盾 → ∃ P2。
4. **n=1 collapse** (normality + K_j*≤K_i + coprime) → Mstar。
5. **covering** (half_lt 交差) + **part(h)** (Prop14.2(a) + K cyclic)。

**本 loop⁷ 累計 18 定理**、全 S14 内 sorry-free + axiom-clean + AxiomsCheck。typeP_duality の building block +
integration helper は全て landing、残りは族 Finset 上の counting 統合 (最終 endgame、~200行)。

### ✅ 族インフラ完成 (2026-06-17 loop⁷ /loop自走、26 定理+1def) — 残り = counting endgame

**/loop dynamic mode で 8 イテレーション自走、全 green + axiom-clean (一発通過多数)**:
- per-neighbor: `exists_neighbor_kappaHall_swap_normal` / `exists_neighbor_full` / `exists_neighbor_data`
  (raw swap + canonical K_N*=Z⊓Msigma N + ⊴Z + type-P + K_N*≠⊥ を 1 call)
- M (i=0): `typeP_self_member` (K_M*=Kstar、同形)
- **族述語 + 統一データ**: `IsZFamilyMember M K N` (def) + `typeP_family_member_data` (∀メンバーの統一データ)
- **pairwise 非共役**: `neighbor_pair_nonconjugate` (per-pair) + `typeP_family_pairwise_nonconjugate` (∀メンバー)
- collapse helper: `le_of_coprime_index` (N⊴G, |H| coprime [G:N] ⟹ H≤N)
- factor normality `sup_le_normalizer_inf_of_commute` / `card_sup_of_commute_of_disjoint` /
  `commute_of_le_normalizer_of_disjoint`

**▶ 残り = counting endgame (intricate, 相互依存)**:
1. **族 Finset** (Set.Finite.toFinset, IsZFamilyMember から) — 軽い wrapping。
2. **T=Z−⋃K_i* TI + N_G(T)=Z** — 🔴 hard: 各 i で Z=K_i×K_i* (swap) の per-i decomposition + Prop14.2(d)。
   t∈T ⟺ ∃i, t=y y' (y∈K_i*#, y'∈K_i#)。σ-decomposition の per-i 構造が要。
3. **|M_i|≥2z** — Z<M_i (proper) を要す: Msigma M_i ⊋ K_i*=Z⊓Msigma M_i (σ(M_i) が π(z) に収まらない)。要論証。
4. **density 不等式** — |𝒞_G(T)|=|T|[G:Z] (TI count) + |𝒞_G(M̃_i)|=(|M_iσ|−1)[G:M_i] (14.5c済) +
   14.5(b)済 disjoint + 14.6 (T∩M̃_i=∅) で 𝒞_G(T)⊥𝒞_G(M̃_i) → Σ≥|G| 矛盾 (算術は 1+(n−1)/(2z)≥1、trivial)。
5. **n=1 collapse** (le_of_coprime_index + |K_i| 素数 [Prop14.2(g)] + pairwise coprime) → Mstar。
6. **covering** (half_lt 交差) + **part(h)** (Prop14.2(a) + K cyclic)。

⚠ endgame は helper grinding と違い相互依存・σ-decomposition が subtle。loop で進めるが blocker は document。

### ✅ counting endgame foundations: |T| fix + hstab + Prop 14.2(d)-second (2026-06-17 lane-h, 3 commits)

**全 green + axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`)。** 本セッションは
TI-of-T への土台 3 件を landing:

1. **🐛 `typeP_family_T_count` の broken state を修正 (commit 645cb2c4)**: 前 loop の未コミット版は
   build-RED だった。原因 = **⋃ の body の coercion バグ** — `((K⊔Kstar)⊓Msigma N : Set G)` という型注釈が
   式全体を `Set G` レベルで解釈させ `⊔`/`⊓` が **Set 演算**化 (`(↑K ∪ ↑Kstar) ∩ ↑(Msigma N)`、部分群 join ≠
   集合和ゆえ別物)。修正 = `(((K⊔Kstar)⊓Msigma N : Subgroup G) : Set G)`。加えて `refine` の `isDefEq`
   heartbeat timeout を `(s:=)(Z:=)(S:=)` named-arg pin で解消。⚠ **教訓: `(expr : Set G)` で部分群演算を
   書くと Set-lattice に落ちる — 必ず `((expr : Subgroup G) : Set G)`。**
2. **`typeP_family_member_normal` + `typeP_family_Z_normalizes_T` (commit a3f9d1a1)** = TI count の `hstab`:
   各メンバーの canonical factor `Z⊓Msigma N ◁ Z` (case N=M=`typeP_self_member` / neighbor=`exists_neighbor_full`)
   → conj l (l∈Z) が `T=Z−⋃K_i*` を固定 (`Set.smul_set_sdiff`/`smul_set_iUnion₂` + `conj_smul_eq_self_of_mem_normalizer`)。
   ⟹ `ncard_conjClassSet_of_isTISubset` の 2nd hyp。
3. **🔑 `typeP_kappaHall_inf_conj_eq_bot` = Prop 14.2(d) 第2主張 (commit f4af9259)**: `K∩K^g=1 for g∈M−Z`。

**🔑🔑 TI-of-T の正確な依存が確定 (mmd L4027 精読)**: BG の "by Prop 14.2(d), g∈K_i×K_i*" は
**(d)-first AND (d)-second の両方**を使う:
- (d)-first `K*∩M^g=1 (g∉M)` = `typeP_structure` conjunct 4 (`.2.2.2.1`) で**既存**。
  → `y^g∈K_i*` から `g∈M_i`。
- (d)-second `K∩K^g=1 (g∈M−Z)` = **本セッションで landing**。→ `y'^g∈K_i` から `g∈Z`。
- repo `typeP_structure` には (d)-first しか無く (d)-second は**欠落していた**。これが TI-of-T の隠れた前提。

**(d)-second の証明レシピ** (BG「K is a Z-group ゆえ容易」を `IsZGroup K` パッケージ無しで):
nontrivial `x∈K∩K^g` (order p) → `X=⟨x⟩≤K`, `Y=⟨g⁻¹xg⟩≤K` (ℰ¹) → (b1) で `N_G(X)⊓M=N_G(Y)⊓M=Z`
ゆえ K が両方を正規化 → `g∈M ∧ g∉Z ⟹ g∉N_G(X) ⟹ conj g⁻¹•X≠X ⟹ X≠Y` → 異なる正規 order-p 2 個は
`X⊔Y=ℤ/p×ℤ/p ≤M` 生成 → `pRank ↥M p≥2` (`le_pRank` + subgroupOf transport)、しかし
`p∈π(K)⊆κ(M)⊆τ₁∪τ₃` で `pRank ↥M p=1` (`tau1/tau3_pRank_eq_one`) 矛盾。
鍵 API: `mem_normalizer_of_conj_smul_eq_self`, `commute_of_le_normalizer_of_disjoint`,
`IsElementaryAbelian.sup_of_le_centralizer`, `card_sup_of_commute_of_disjoint`,
`MonoidHom.map_zpowers` (conj smul of zpowers), `Nat.log_pow`。

**▶ TI-of-T の残り唯一の hard core = σ-decomposition coverage**:
`t∈T ⟺ ∃i, t=yy' (y∈K_i*#, y'∈K_i#)` の ⟹ 方向に `Z=∏K_i*` (= `⋃σ(M_i)⊇π(z)`) が要る。
理由: t∈Z=K_i×K_i* (swap, per-i) で t=a_i·b_i (a_i∈K_i, b_i∈K_i*)。t∉⋃K_j* ⟹ ∀i, a_i≠1。
∃i,b_i≠1 を出すには「b_i=1 ∀i ⟹ t∈⋂K_i={1}」が要り、⋂K_i={1} ⟺ ⋃σ(M_i) が z の全素数を覆う (coverage)。
coverage 素材は **既存**: `exists_typeP_neighbor_mem_sigma` (p|K→neighbor with p∈σ(N)) + p|K*→p∈σ(M)。
組立 = Fintype on Finset + Hall-part 算術 (`card_iSup_of_pairwise_commute_coprime`済) で `⊔K_i*=Z`。これが次の主タスク。
⟹ 揃えば TI-of-T (hstab済 + (d)both済 + coverage) → `ncard_conjClassSet_of_isTISubset` で |𝒞_G(T)| →
density 不等式 (|T| count済 + 14.5c済 + 14.6済) → n=1 collapse → covering → part(h)。

### ✅✅ σ-decomposition coverage `⊔Kᵢ*=Z` COMPLETE (2026-06-17 lane-h loop⁸ cont., 4 commits)

**TI-of-T の flagged "sole remaining hard core" を解消。全 green + axiom-clean。** 本 cont. の landing:

1. **`typeP_family_Kstar_coprime` + `typeP_family_Kstar_commute`** (31e2406f, 838717e7) =
   `card_iSup_of_pairwise_commute_coprime` の両入力 (coprime=σ-disjoint via 13.9, commute=◁Z+disjoint)。
2. **`typeP_family_sigma_covers`** (79e6200d) = coverage primitive: ∀p|z, ∃N∈family, p∈σ(N)。
   p|k*→σ(M) (Kstar σ(M)-group); p|k→neighbor N via `exists_typeP_partner` (IsZFamilyMember witness を保持、
   `exists_typeP_neighbor_mem_sigma` は捨てていた)。
3. **`typeP_family_prime_pow_dvd_Kstar`** = Kᵢ*=Z⊓Msigma N は σ(N)-Hall of Z: p∈σ(N), pᵏ|z ⟹ pᵏ|kᵢ*。
   |Z|=|K_N||Kᵢ*| (`card_kappaHall_sup_Kstar` を N の swap data に適用) + K_N σ(N)'-group ⟹ pᵏ⊥|K_N| ⟹ pᵏ|kᵢ*。
4. **🔑 `typeP_family_iSup_Kstar_eq`** (94e4aa42) = **`⊔_{N∈family}(Z⊓Msigma N)=Z`**: ⊔≤Z は自明、
   Z≤⊔ は |Z| ∣ |⊔| を prime-pow ごとに (`Nat.dvd_iff_prime_pow_dvd_dvd`): pᵏ|z → coverage で N → pᵏ|kᵢ* | |⊔|。
5. **`typeP_family_isPiElement_mem_Kstar`** (1a6f1911) = σ(N)-元 a∈Z ⟹ a∈Kᵢ*: ⟨a⟩ は N の σ(N)-部分群
   ⟹ ⟨a⟩≤Msigma N (`sigma_subgroup_le_Msigma_of_isHall`)。**t=yy' の σ(N)-part 側 half。**

**▶ 残り = TI-of-T assembly (次の distinct unit, ~120 行)**。全 building block は揃った:
- **σ(N)′-part 側** `b∈Z σ(N)'-元 ⟹ b∈K_N` (未): K_N は swap で **Z の σ(N)'-Hall** (|K_N|=σ(N)'-part of |Z|,
  Z=K_N×Kᵢ* 直積ゆえ K_N◁Z)。`isPiGroup_le_of_normal_isHallSubgroup` を ↥Z で適用 (subgroupOf-Z plumbing 要、~40 行)。
  ⚠ K_N は member_data の existential (choice) ゆえ、TI proof 内で obtain して使う。
- **TI proof** `IsTISubset T Z` (~80 行): t∈T (t∉⋃Kᵢ*), t^g∈Z。π-decompose t (`exists_isPiElement_mul`):
  coverage + t∉⋃Kᵢ* ⟹ ∃N, σ(N)-part y≠1 ∧ σ(N)'-part y'≠1。y∈Kᵢ*(済 helper), y'∈K_N(上記)。
  y^g∈Kᵢ* (σ-part of t^g∈Z) → **(d)-first** [typeP_structure conjunct 4 for N] ⟹ g∈N。
  y'^g∈K_N → **(d)-second** [`typeP_kappaHall_inf_conj_eq_bot` for N] ⟹ g∈Z (by_contra g∉Z で K_N∩K_N^g=⊥ vs y'^g≠1)。
- TI-of-T 後: hstab(済) + `ncard_conjClassSet_of_isTISubset` で |𝒞_G(T)|=|T|[G:Z] → density 不等式
  (|T| count済 + 14.5c済 + 14.6済) → n=1 collapse (`le_of_coprime_index`+Prop14.2(g)) → covering (half_lt) → part(h)。

### ✅✅✅ TI-of-T COMPLETE + dummy-D finding (2026-06-17 lane-h loop⁸ /loop自走, ~10 commits)

**`/loop` dynamic mode で自走。TI-of-T (long pole の最難関構造的核心) を完全形式化。全 green + axiom-clean。**

landing 群 (依存順):
- `isPiElementCompl_mem_left_of_commute` (一般): Z=A⊔B 直積 (B≤C(A)), A=πᶜ群, B=π群 ⟹ πᶜ-元∈A。
  ↥Z で `isPiGroup_le_of_normal_isHallSubgroup` (A=normal Hall πᶜ; `normal_subgroupOf_iff_le_normalizer`
  + `card_mul_index`)。⟹ σ(N)′-part∈K_N。
- `typeP_family_member_dData` (包括 producer): family member N の K_N + swap + `Kᵢ*≤C(K_N)` (hcent) +
  `IsPiSubgroup (σN)ᶜ K_N` + (d)-first + (d)-second を 1 call。hU は `hall_E_exists` (N solvable) で内部構築。
  TI proof の唯一ソース (choice 一意性のため member_data 単一 obtain)。
- `typeP_family_exists_sigmaPart`: t∈Z, t≠1 ⟹ ∃N∈family で σ(N)-part≠1 (coverage 矛盾)。
- 🔑🔑 **`typeP_family_T_isTI`**: `IsTISubset T (K⊔Kstar)`。t∈T, t^g∈Z → exists_sigmaPart で N →
  π-分解 t=y·y' (`exists_isPiElement_mul`) → y∈Kᵢ*/y'∈K_N (両≠1) → y^g,y'^g は t^g∈Z の powers ゆえ∈Z →
  y^g∈Kᵢ*∩N^g で **(d)-first ⟹ g∈N** → y'^g∈K_N∩K_N^g で **(d)-second ⟹ g∈Z**。conj bookkeeping は
  `MulAut.conj`/`map_eq_one_iff`/`conj g•H=H.map(conj g).toMonoidHom`(rfl)。
- `typeP_family_conjClass_T_count`: **|𝒞_G(T)|=|T|·[G:Z]** (`ncard_conjClassSet_of_isTISubset` +
  T_isTI + Z_normalizes_T)。

**🔑🔑🔑 dummy-D 発見 (density 論法の feasibility を解決)**: density 論法が使う `Mtilde`/14.5(c)/14.6 は
すべて **D-parametric** で、`Rsub hG D x` は D を `D.length x=1` 経由でのみ使う。これは構造体公理
`SigmaDecompositionData.length_one_iff` (`length x=1 ↔ x≠1 ∧ (maximalSigmaSubgroupsOfElement x).Nonempty`)
で**全 D で同一述語**に固定。14.4 (`sigmaLength_one_centralizer_structure`) の ∃!N も
`maximalSigmaSubgroupsOfElement x` (D-independent) について。⟹ **dummy D** (line 2617 の `length:=if … then 1 else 0`
carrier、構成可能) で 14.5(c)/14.6 がそのまま使え、density 論法に **true σ-decomposition theory は不要**。
⟹ 旧 flag「σ-decomposition theory=必須前提」は density 部分には**当たらない** (true length は不要、length=1 述語のみ)。

**▶ 残り = density 不等式 → n=1 collapse → covering → part(h) → typeP_duality close** (intricate, multi-iteration):
1. **|M_i|≥2z** (Z⊊M_i proper): M_iσ⊋K_i*=Z⊓M_iσ (K_i prime-action on M_iσ ⟹ C_{M_iσ}(K_i)⊊M_iσ)。要 prime-action 補題。
2. **conjClass 互いに素**: 𝒞_G(M̃_i) pairwise disjoint (14.5b の M̃_i disjoint + nonconjugate ⟹ conjClass disjoint、要補題) +
   𝒞_G(T)⊥𝒞_G(M̃_i) (14.6 T∩M̃=∅ ⟹ conjClass disjoint)。
3. **density 不等式**: dummy D で 14.5(c) → |𝒞_G(M̃_i)|=(|M_iσ|−1)[G:M_i]≥(1/k_i−1/2z)|G|。
   |G^#|≥|𝒞_G(T)|+Σ|𝒞_G(M̃_i)|≥(1+(n−1)/2z)|G|≥|G| 矛盾 ⟹ ∃M_i type-P2。(14.9 不要、disjoint+card のみ)
4. **n=1 collapse** (`le_of_coprime_index`+Prop14.2(g): |K_i| 素数=∏_{j≠i}k_j*) → Mstar。
5. **covering** (half_lt) + **part(h)** (Prop14.2(a) + K cyclic)。

### ✅✅ density 不等式 COMPLETE (2026-06-17 lane-h 再開, 2 commits) — step 7 着地、ℕ で omega 締め

**`exists_typeP2_member` (BG 14.7 step 7, mmd L4031-4045) を green+axiom-clean で landing。endgame で最難の
counting 部分。** 全論法を **ℕ で完結**(ℚ 不要、`omega` で締まる)できると判明 — これが鍵だった。

**🔑 ℕ-only density 論法の構造** (notes 旧記述の「(1+(n−1)/2z)|G|」を ℕ-omega 化):
- A := |𝒞_G(T)| = |T|·[G:Z], B := Σ|𝒞_G(M̃ᵢ)|, S := Σ[G:Mᵢ], P := Σ([G:Z]·kᵢ*), zi := [G:Z], c := |𝓕|=n+1, g := |G|。
- **T-additive** (hmul): A + Σ(kᵢ*·zi) + zi = g + c·zi (hT_card×zi + hT_count + card_mul_index)。
- **M̃-additive** (per P1 member): |𝒞_G(M̃ᵢ)| + [G:Mᵢ] = [G:Z]·kᵢ* ⟹ B + S = P。
  ← `(|N_σ|−1)·[G:N] + [G:N] = |N_σ|·[G:N] = [G:Z]·kᵢ*` (`Nat.sub_one_mul`+omega+per-member 恒等式)。
- **bound** (hbound): A + B ≤ g−1 (`density_pieces_ncard_le`、disjoint+⊆G^#)。
- **key** (hkey): S ≤ (c−1)·zi。← 2·[G:Mᵢ]≤zi (|Mᵢ|≥2z) ⟹ 2S ≤ c·zi ≤ 2(c−1)·zi (c≤2(c−1) ∵ c≥2) ⟹ **omega が 2S≤2X ⟹ S≤X を処理**。
- **expansion** (hexp): c·zi = (c−1)·zi + zi (omega が nonlinear 積 c·zi, (c−1)·zi を hexp で橋渡し)。
- **final omega**: A=AT, hmul: A+P+zi = g+c·zi = g+(c−1)·zi+zi ⟹ A+P = g+(c−1)·zi; B+S=P ⟹ A+B+S=g+(c−1)·zi;
  S≤(c−1)·zi ⟹ A+B≥g; hbound A+B≤g−1 ⟹ g≤g−1 矛盾 (g≥1)。**全 linear、omega 一発。**

**landing 群** (commit `5634f28c`、AxiomsCheck 登録、full build 3817/64s):
- `typeP1_card_eq` (前 commit `4d4851a5`): **P1 ⟹ |N|=|N_σ|·|K_N|** (σ-part 一意性: m·j=|N|=a·j', m,j' σ-数 ∧ a,j σ'-数 ⟹ a=j、coprime+dvd_antisymm; j'⊆σ のみ P1 使用 [κ=π−σ])。
- `typeP1_member_Msigma_index_eq`: **|N_σ|·[G:N] = [G:Z]·kᵢ*** (×|K_N| して |N|=|N_σ|·k_N + z=k_N·k_N* [`card_kappaHall_sup_Kstar`] + Lagrange、`Nat.eq_of_mul_eq_mul_right`)。**cancellation crux**。
- `typeP_member_two_mul_index_le`: 2·[G:N]≤[G:Z] (|N|≥2z ×[G:N]、z で約分)。
- `ZFamilyFinset_one_lt_card`: **n≥1** (M + 非共役 neighbor `exists_typeP_partner`、|𝓕|≥2)。
- `one_not_mem_conjClassSet` (汎用): 1∉A ⟹ 1∉𝒞_G(A) (MulAut.conj 単射)。
- `one_not_mem_Mtilde`: **1∉M̃** (x'=x⁻¹ は x∈Nσ ゆえ σ(N)-元、だが `isPiElement_sigmaCompl_of_mem_Rsub` で σ(N)'-元 ⟹ 矛盾)。
- `density_pieces_ncard_le`: **Σ|𝒞_G(·)| ≤ |G|−1** (𝒞_G(T) ⊔ ⋃𝒞_G(M̃ᵢ) pairwise disjoint ⊆ G^#;
  `Set.Finite.ncard_biUnion`[↑𝓕 Set-coe]+`finsum_mem_coe_finset`+`Set.ncard_union_eq`+`Set.ncard_le_ncard`)。

⚠ **技法メモ**: (i) `rw [hswap]` は goal 全体の `K⊔Kstar` を書き換える (RHS 内も) → `rw [← hswap] at h1` で hypothesis 側に逃がす。
(ii) `obtain ⟨p,hpκ⟩ := hP` は hP を消費 → `have hPe := hP; obtain := hPe` で温存。
(iii) `Nat.le_of_mul_le_mul_left` は k metavar 化で omega 不能 → `2S≤2X ⟹ S≤X` は omega が直接できる。
(iv) ncard biUnion は **↑𝓕 (Set-coe) で回す**と `Finite.ncard_biUnion`+`finsum_mem_coe_finset` で Finset.sum に落ちる (Finset-membership の `⋃ N ∈ 𝓕` 形は使わない)。

**▶ 残り (typeP_duality の残務、step 8-11 + ∃! 組立)**:
1. **n=1 collapse** (step 8): exists_typeP2_member の M_i に Prop14.2(g) [|K_i|=q 素数] → 各 K_j*(j≠i) は σ(M_i)'-群 (13.9)
   ⟹ K_j*≤K_i (=σ(M_i)'-Hall of Z, `le_of_coprime_index`) ⟹ K_j*=K_i (|K_i| 素数) ⟹ pairwise disjoint で高々1 ⟹ **n=1**。
   ⟹ 族={M, Mstar} (2 メンバー)、Z=K_i×K_i* cyclic (両 rank1)。⚠ K_i⊴Z の確立要 (swap 直積、`sup_le_normalizer_inf_of_commute`)。
   ⚠ Prop14.2(g) 適用には M_i の full setup (hU_{M_i}=Hall(κ∪σ)' 構築要)。
2. **covering** (step 10): H type-P, S_H=L×L*−(L∪L*), |𝒞_G(S_H)|>½|G| (half_lt) ⟹ 𝒞_G(T)∩𝒞_G(S_H)≠∅ ⟹ T∩S_H≠∅
   ⟹ L*∩K_i*≠1 ⟹ Prop14.2(c) で {H}=𝓜(C_G(Y))={M_i} ⟹ H~M_i。
3. **part(h)** (step 11): M_σ⊆M', Prop14.2(a) の UM_σ=K の normal complement ⊆M', K cyclic ⟹ UM_σ=M'。
   ⚠ Prop14.2(a) の normal complement UM_σ は repo 未パッケージ (要構築)。`coprime_card_derived_kappaHall_of_isComplement'` で coprime は free。
4. **∃! Mstar 組立**: Mstar = 一意 neighbor (n=1)。uniqueness は 𝓜(C_G(X))={Mstar} (X∈ℰ¹(K)) で pin。
   parts (2)(3): K* Hall κ(M*), M∩M_1=Z。

### ✅✅✅ n=1 collapse COMPLETE (2026-06-17 lane-h 再開 cont., 2 commits) — step 8 着地、|𝓕|=2

**`family_card_eq_two` (BG 14.7 step 8, mmd L4047): 型-P 族 {M}∪{neighbors} は丁度 2 メンバー。** structural keystone。

**論法** (density の type-P2 member を起点):
- exists_typeP2_member で M_i∈𝓕 type-P2 → member_data で KN_i (Hall κ(M_i)) + swap Z=KN_i⊔K_i* (K_i*=Z⊓M_iσ)。
- **|KN_i|=q 素数**: M_i に Prop14.2(g) 適用 (hall_E_exists で M_i の Hall(κ∪σ)' を構築 → `typeP_structure ... .2.2.2.2.1 hMiP2`)。
- **各 member M_j≠M_i: K_j*=KN_i**: K_j*=Z⊓M_jσ は σ(M_i)'-群 (σ(M_j)∩σ(M_i)=∅ via 13.9 nonconj) ⟹ K_j*≤KN_i
  (`isPiSubgroup_le_left_of_commute`: KN_i=σ(M_i)'-Hall of Z); K_j*≠⊥ + |KN_i|=q 素数 ⟹ K_j*=KN_i (`eq_of_le_of_card_ge`)。
- **≤1 neighbor**: 異なる M_a,M_b≠M_i は K_a*=KN_i=K_b* だが pairwise disjoint (`typeP_family_Kstar_disjoint`) ⟹ KN_i=⊥、矛盾 (q≥2)。
  `Finset.card_le_one` on erase Mi + `Finset.card_erase_of_mem` + omega。

**新 helper `isPiSubgroup_le_left_of_commute`**: `isPiElementCompl_mem_left_of_commute` の部分群版 (Z=A×B 直積、A=πᶜ群、
B=π群、L≤Z πᶜ群 ⟹ L≤A; A.subgroupOf Z=normal Hall πᶜ via `isPiGroup_le_of_normal_isHallSubgroup`)。

commit `4aed1736` (+`isPiSubgroup_le_left`), AxiomsCheck 登録、full build 3817/65s。
⚠ **技法**: member_data の `∃ KN` witness を `-` で捨てると後続 (hcanon/hne が KN 参照) が壊れる → KN 命名要。

### ▶▶ typeP_duality 残務 (step 9-11 + ∃! 組立) — 密結合した最終 assembly (次の大単位)

`family_card_eq_two` (|𝓕|=2) ⟹ 族={M, Mstar}。Mstar = 一意 neighbor (`Finset.card_eq_two` で抽出可)。残り:
1. **IsCyclic (K⊔Kstar)**: `isCyclic_kappaHall_sup_Kstar_of_cyclic` は **[IsCyclic K][IsCyclic Kstar] instance 要**。
   K,Kstar cyclic は collapse の prime-order 構造から (type-P2 member の Hall κ=prime ⟹ cyclic; 他因子 rank1)。
   ⚠ K (=M の Hall κ) cyclic は **どちらが type-P2 か**で分岐 (M か Mstar)。BG L4049「Z=K_i×K_i*=K_j*×K_j cyclic ∵ K_i*⊆M_iσ ∧ r(K_i*)=r(K_j)=1」。
2. **covering** (step 10, mmd L4053): H type-P, S_H=L×L*−(L∪L*), |𝒞_G(S_H)|>½|G| (`half_lt_one_sub_inv_mul`)
   ⟹ 𝒞_G(T)∩𝒞_G(S_H)≠∅ ⟹ T∩S_H≠∅ ⟹ L*∩K_i*≠1 ⟹ Prop14.2(c): {H}=𝓜(C_G(Y))={M_i} ⟹ H~M_i。
   ⚠ T=Ẑ=zTilde 同定 (n=1 で T=Z−(K∪K*)) + |𝒞_G(T)|=(1−1/k)(1−1/k*)|G|>½|G| 要 (density count を n=1 特殊化)。
3. **part(h)** (step 11, mmd L4061): M_σ⊆M' (`Msigma_le_derived`)、Prop14.2(a) の UM_σ=K の normal complement ⊆M'、
   K cyclic ⟹ UM_σ=M'。⟹ `IsComplement' (derivedInG M).subgroupOf M (K.subgroupOf M)`。
   coprime は `coprime_card_derived_kappaHall_of_isComplement'` で free。
   ⚠⚠ **Prop14.2(a) の normal complement UM_σ は repo 未パッケージ** (E-setup 断片のみ; 要構築 = part(h) の前提障壁)。
4. **∃! Mstar 組立**: witness=Mstar (n=1 neighbor)、uniqueness=𝓜(C_G(X))={Mstar} (X∈ℰ¹(K)) で pin。
   parts: Hall κ(Mstar) Kstar (BG (2): K*=Hall κ(M*) of M*) + IsTISubset zTilde Z + (P2 M∨P2 Mstar) + covering。
   ⚠ 多数の conjunct を Mstar について同時証明 = 最大の組立労力。

**現在地サマリ (2026-06-17)**: typeP_duality endgame の **counting/structural 核 3 件 (typeP1_card_eq + density 不等式 + n=1 collapse) 完了**。
残り = cyclicity + covering + part(h) + ∃! 組立 = 密結合した最終 assembly (新規の大単位、Prop14.2(a) packaging が part(h) gate)。

### 🤝 引き継ぎ (2026-06-17 再開セッション + /loop 自走、計 11 feature commit) — typeP_duality assembly 進行中

**typeP_duality の counting/structural 核 + 3 conjunct を landing。全 green+axiom-clean、AxiomsCheck 登録済、full build 3817/~65s。**
working tree clean。typeP_duality 本体 (FT consume sorry) は**未 discharge** — 機械は大半揃い、残り = >½|G| count + covering + cyclic + part(h) + ∃! 組立。

**本セッション landing 群** (依存順、すべて `S14_TypePCounting.lean`):
1. **`typeP1_card_eq`** (`4d4851a5`): P1 ⟹ |N|=|N_σ|·|K_N| (σ-part 一意性)。
2. **`exists_typeP2_member`** (`5634f28c`, step 7): density 不等式 → ∃ type-P2 member。**ℕ-only omega**。helper 6:
   one_not_mem_Mtilde / one_not_mem_conjClassSet / typeP1_member_Msigma_index_eq / typeP_member_two_mul_index_le /
   ZFamilyFinset_one_lt_card / density_pieces_ncard_le。
3. **`family_card_eq_two`** (`4aed1736`, step 8): n=1 collapse → |𝓕|=2。helper `isPiSubgroup_le_left_of_commute`
   (πᶜ-subgroup ≤ Z=A×B の A factor)。
4. **`exists_partner`** (`4a861bd2`): |𝓕|=2 → 一意 partner Mstar (∀N member→N=M∨N=Mstar; Finset literal 回避で predicate 形)。
5. **`isTypeP2_or_isTypeP2_partner`** (`225a93de`, 14.7(f)): IsTypeP2 M ∨ IsTypeP2 Mstar。
6. **🔑 `partner_canonical_eq`** (`1f85d1ab`, **keystone**): **Z⊓Mstar_σ = K**。helper `kappaHall_primes_subset_sigma_partner`
   (line X∈ℰ_p¹(K)→partner=Mstar→p∈σ(Mstar))。両 inclusion (isPiSubgroup_le_left + sigma_subgroup_le_Msigma)。
7. **`typeP_zTilde_isTI`** (`a1718a1c`, 14.7(e) conjunct): IsTISubset (zTilde K Kstar) (K⊔Kstar)。
   ⋃_{N∈𝓕}(Z⊓N_σ)=K∪Kstar (partner_canonical_eq + typeP_self_member.1) ⟹ zTilde=family-T ⟹ typeP_family_T_isTI。
8. **`zTilde_ncard_eq`** (`59121a09`): |zTilde|=(|K|−1)(|K*|−1)。helper `nat_mul_sub_kl_identity` (k·l−(k+l−1)=(k−1)(l−1))。

**▶▶ 残り (typeP_duality 完成までの assembly)** — 依存順:
1. **>½|G| count `Nat.card G < 2·(conjClassSet (zTilde K Kstar)).ncard`** (次の最有力, cyclicity 不要):
   - **union collapse を `family_inf_msigma_union_eq` に factor out** (typeP_zTilde_isTI の hunion を再利用 lemma 化; ⋃_{N∈𝓕}(Z⊓N_σ)=↑K∪↑Kstar)。
   - |𝒞_G(zTilde)|=|𝒞_G(family-T)| (zTilde=family-T)=|family-T|·[G:Z] (typeP_family_conjClass_T_count)=|zTilde|·[G:Z]=(|K|−1)(|K*|−1)·[G:Z]。
   - 算術: |G|=|Z|·[G:Z]=|K||K*|·[G:Z]、需 |K||K*|<2(|K|−1)(|K*|−1)。oddness=`hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)` で |K|,|K*| odd ≥3、coprime (coprime_card_kappaHall_Kstar) で not both 3 ⟹ max≥5。(k−2)(l−2)>2 ⟺ kl<2(k−1)(l−1)。
2. **covering** (step 10, mmd L4053): H type-P, S_H=L×L*−(L∪L*), |𝒞_G(S_H)|>½|G| (上記を H に適用) + |𝒞_G(T)|>½|G|
   ⟹ 𝒞_G(T)∩𝒞_G(S_H)≠∅ (sum>|G|, both ⊆G) ⟹ WLOG T∩S_H≠∅ ⟹ L*∩K_i*≠1 (∃ common elt) ⟹ Y∈ℰ¹(L*∩K_i*),
   Prop14.2(c) {H}=𝓜(C_G(Y))={M_i} ⟹ H~M_i (=M or Mstar)。⚠ 大きい (S 機構 + 交差論法 + Prop14.2(c) 適用)。
3. **cyclic `IsCyclic(K⊔Kstar)`** (deep stack): isCyclic_kappaHall_sup_Kstar_of_cyclic は [IsCyclic K][IsCyclic Kstar] instance 要。
   K,Kstar cyclic は: type-P2 member の prime |K_i| + 他 factor rank-1 nilpotent。**M_σ nilpotent (Lemma 14.1 = msigma_structure_of_notMem_sigma_kappa、要 (π−σ)−κ の素数 p + max-rank elemAbelian A 構成) → Z nilpotent → rank-1 Sylow cyclic** の stack。⚠ max-rank elemAbelian 構成 helper 未特定 (Ω₁(Sylow))。
4. **part(h)** (step 11): IsComplement' (derivedInG M).subgroupOf M (K.subgroupOf M) + Coprime。
   M_σ⊆M' (`Msigma_le_derived`) + Prop14.2(a) の UM_σ=K normal complement ⊆M' + K cyclic ⟹ M'=UM_σ。
   coprime は `coprime_card_derived_kappaHall_of_isComplement'` で free。**⚠⚠ Prop14.2(a) の UM_σ normal complement は repo 未パッケージ = part(h) の gate (要構築)**。
5. **∃! Mstar 組立**: witness=Mstar (exists_partner)、uniqueness は Mstar' も partner ⟹ 𝓜(C_G(X))={Mstar} (X∈ℰ¹(K)) で pin
   (or: covering で Mstar'~Mstar かつ both nonconj M ⟹ ... 要検討、∃! は equality ゆえ conj では不足、𝓜(C_G(X)) singleton 経由)。
   conjuncts: maximal/typeP/¬conj M (exists_partner+member_data) / Hall κ(Mstar) Kstar (BG(2): Kstar=Hall κ(M*) of M* —
   要証明, Kstar=Z⊓Mstar_σ=K_{Mstar}* が Hall κ(Mstar)?) / IsCyclic [上記3] / IsTISubset [済 typeP_zTilde_isTI] /
   P2 dichotomy [済] / covering [上記2]。⚠ 「Kstar が Hall κ(Mstar)」conjunct も要 (Kstar は M_σ-part だが Mstar 視点で κ(Mstar)-Hall)。

**技法メモ (本セッション)**:
- ℕ subtraction の積を含む等式は generic-variable helper に切り出す (`rw [ha : Nat.card K = a+1]` は product atom を split し omega 不能; lemma param なら `obtain ⟨a,rfl⟩` subst 可)。
- `{M, Mstar}` Finset literal は statement で DecidableEq (Subgroup G) 要 → predicate 形 `∀N,…→N=M∨N=Mstar` で回避。
- member_data の `∃KN` witness を `-` で捨てると後続 (hcanon/hne が KN 参照) 壊れる → KN 命名。
- `Nat.card_coe_set_eq (s:Set) : Nat.card ↥s = s.ncard` + `Nat.card_congr (Equiv.refl _)` で subgroup-coe ↔ subtype card 橋渡し。

### ✅✅ >½|G| density bound COMPLETE (2026-06-17 lane-h 再開セッション², commit `b2fc3c18`) — counting heart 着地、🛑 残り = 設計判断 3 件

**LAUNCH GATE objective (VERDICT=LOOP_THEN_STOP) を 1 iteration で完遂。両 deliverable sorry-free + axiom-clean + AxiomsCheck 登録、full build green 3838/67.5s。GATE の stop-when (typeP_duality 本体組立の前で停止) に正確に到達 → 🛑 STOP。**

**landing 群** (`S14_TypePCounting.lean`):
1. **`family_inf_msigma_union_eq`** (14.7(e) 補題抽出): `⋃_{N∈𝓕}(Z⊓N_σ)=↑K∪↑Kstar`。`typeP_zTilde_isTI` の `hunion` 証明を standalone 化 (typeP_self_member + partner_canonical_eq)。`typeP_zTilde_isTI` を cite 形に refactor。
2. **`typeP_zTilde_conjClass_gt_half`** (density bound, mmd L3975/L4051): **`Nat.card G < 2·(conjClassSet (zTilde K Kstar)).ncard`**。
   - chain: `|𝒞_G(Ẑ)|=|Ẑ|·[G:Z]` (`ncard_conjClassSet_of_isTISubset` + `typeP_zTilde_isTI` + hstab[Ẑ=T 経由で `typeP_family_Z_normalizes_T` 転送]) = `(k−1)(k*−1)·[G:Z]` (`zTilde_ncard_eq`); `|G|=k·k*·[G:Z]` (`card_kappaHall_sup_Kstar`+`card_mul_index`); reduces to ℕ ineq `k·k*<2(k−1)(k*−1)`。
   - **`card_kkstar_lt`** (private ℕ arith): coprime odd k,l>1 ⟹ k·l<2(k−1)(l−1)。`Odd` で `k=2a+1,l=2b+1` subst → `2a+2b+1<4ab` を `2≤a∨2≤b` で casing + `Nat.mul_le_mul`+omega (ab を atom 扱い) → `nlinarith [key]`。唯一失敗の odd pair ≥3 は k=l=3 (coprime `by decide` 排除 ⟹ 一方 ≥5)。
   - 入力: `k=|K|>1` = prime p∈κ(M) ∣ |K| (typeP 展開, typeP_family_Z_lt_member ミラー); `k*=|K*|>1` = `typeP_structure ….2.1` (K*≠⊥); coprime = `coprime_card_kappaHall_Kstar`; odd = `hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)`。

**技法メモ**: (i) `mul_lt_mul_of_pos_right harith hidx_pos` で `(K⊔Kstar).index` を両辺に乗せ `mul_assoc` で締め。(ii) hstab は zTilde を `rw [hzeq]` で family-T 形に直してから `typeP_family_Z_normalizes_T` (zTilde 用 normalizer 補題を新設不要)。(iii) `IsTypeP M` = `(kappa M).Nonempty`; `p∈kappa M` 展開 = `p.Prime ∧ p∈τ₁∪τ₃ ∧ ∃P∈ℰ¹, P≤M ∧ Mσ⊓C(P)≠⊥`。

**🛑🛑 残り = typeP_duality 本体組立 (FT consume sorry S14:7160) = 設計判断 3 件 (sorry 退避せず STOP, [[feedback-no-avoiding-hard-parts]])**:
1. **`IsCyclic (K⊔Kstar)` の根拠** — `isCyclic_kappaHall_sup_Kstar_of_cyclic` は `[IsCyclic K][IsCyclic Kstar]` instance 要。K,Kstar cyclic は type-P2 member の prime |K_i| + 他 factor rank-1 nilpotent。**⚠ max-rank elemAbelian (Ω₁ of Sylow) 構成 helper 未特定** = M_σ nilpotent (Lem 14.1)→Z nilpotent→rank-1 Sylow cyclic の stack の起点。**設計判断 = この Ω₁ helper をどう建てるか (BG §1/§12 由来の rank-1⟹cyclic 経路)。**
2. **part(h) `IsComplement' (derivedInG M).subgroupOf M (K.subgroupOf M)`** — M_σ⊆M' (`Msigma_le_derived`) + **Prop14.2(a) の UM_σ=K normal complement** ⊆M' + K cyclic ⟹ M'=UM_σ。**⚠⚠ Prop14.2(a) の UM_σ normal complement は repo 未パッケージ** (E-setup 断片のみ; 要構築) = part(h) の gate。coprime は `coprime_card_derived_kappaHall_of_isComplement'` で free。**設計判断 = Prop14.2(a) packaging を S14 に建てるか別 leaf か。**
3. **∃! Mstar 一意性の出どころ** — witness=Mstar (`exists_partner`); covering (step 10, mmd L4053: S_H=L×L*−(L∪L*), |𝒞_G(S_H)|>½|G| [本 commit の bound を H に適用] + |𝒞_G(Ẑ)|>½|G| ⟹ 𝒞 交差≠∅ ⟹ Prop14.2(c)) で global conj。uniqueness は equality ゆえ conj では不足 → `𝓜(C_G(X))={Mstar}` (X∈ℰ¹(K)) で pin。**設計判断 = uniqueness の正確な pin (covering ＋ 𝓜-singleton の組合せ)。** + conjunct「Kstar が Hall κ(Mstar)」も要 (Kstar=Z⊓Mstar_σ が κ(Mstar)-Hall?)。
- **density bound (本 commit) は covering の左辺 (|𝒞_G(Ẑ)|>½|G|) を供給済。covering は本 bound を H(任意 type-P)に適用するだけ** — 設計判断は uniqueness の組立方。

### ✅ covering building blocks landing (2026-06-17 再開² cont., commit `dcb31fcc`, ユーザー裁可で covering 着手) — 次 = covering 核 (~150-200 行, multi-iteration)

**ユーザーが AskUserQuestion で「covering 論法」を選択 → bottom-up で再利用部品 3 件を landing (green + axiom-clean + AxiomsCheck)。**
- `dummySigmaDecomposition` (def): `exists_partner` が要求する length-1 carrier (G explicit、`open Classical in`)。再利用可。
- `ncard_inter_nonempty_of_two_mul_gt`: 有限群で `2|A|>|G| ∧ 2|B|>|G| ⟹ A∩B≠∅` (incl-excl、`Set.ncard_union_add_ncard_inter`+`Set.ncard_univ`+omega)。
- `exists_zTilde_conjClass_gt_half_of_isTypeP`: **任意 type-P H に L=Hall κ(H)/L*=C_{Hσ}(L)/`|𝒞_G(Ẑ_H)|>½|G|`** (BG「we also have」)。H の Hall は `Ch03.hall_E_exists (G:=↥H)` で L', U' を取り `.map H.subtype` + `subgroupOf` 往復 (`comap_map_eq_self_of_injective`); partner data は `exists_partner hG (dummySigmaDecomposition G) …`; 本体は `typeP_zTilde_conjClass_gt_half`。

**▶▶ covering 核 (typeP_duality (g) conjunct = ∀ H type-P, H~M ∨ H~Mstar) の残り — 3 sub-step、密結合**:
1. **intersection → 共役** (~40 行, conjugation tracking が摩擦): `exists_zTilde_…(M)` + `…(H)` で両 `|𝒞_G(Ẑ)|>½` → `ncard_inter_nonempty_of_two_mul_gt` で `𝒞_G(Ẑ_M)∩𝒞_G(Ẑ_H)≠∅` → 共通元 u が `u~t (t∈Ẑ_M)` かつ `u~s (s∈Ẑ_H)` → `t~s` → `∃c, t=c•s` → `t∈Ẑ_M ∩ Ẑ_{c•H}` (c•Ẑ_H=Ẑ_{c•H}, c•L/c•L* は c•H の Hall κ data)。**⚠ conjClassSet membership ↔ ∃conj の往復 + `c•Ẑ_H=Ẑ_{c•H}` の保存 (Hall/centralizer/sup/sdiff の pointwise smul) を要する**。
2. **🔑 matching `t∈Ẑ_M ∩ Ẑ_{H'} ⟹ L'*⊓K≠⊥ ∨ L'*⊓Kstar≠⊥`** (~60 行, 数学は明快): t∈Ẑ_{H'}=L'×L'*−(L'∪L'*) ⟹ t∉L' ⟹ **σ(H')-part w:=`exists_isPiElement_mul (σ H') t` の π-part ≠1, w∈L'*** (σ(H')-元 of Z_{H'}=L'×L'*); w∈⟨t⟩⊆Z_M=K×Kstar ⟹ `exists_isPiElement_mul (σ M) w` で `w=a·b` (a=σ(M)-part∈Kstar, b=σ(M)'-part∈K, **両 ∈⟨w⟩⊆L'***); w≠1 ⟹ a≠1∨b≠1 ⟹ `L'*⊓Kstar≠⊥ ∨ L'*⊓K≠⊥`。
   - membership: **b∈K = `isPiElementCompl_mem_left_of_commute (A:=K)(B:=Kstar)(π:=σ M)`** (clean: K=σ(M)ᶜ群=`kappaHall_isPiSubgroup_sigmaCompl`, Kstar=σ(M)群=`Kstar_isPiSubgroup_sigma`, hcent=`hKstar▸inf_le_right`)。**a∈Kstar = 同 lemma の dual** (A:=Kstar,B:=K,π:=(σM)ᶜ; `compl_compl` massaging 要、or 小 dual helper 新設が clean)。
3. **double Prop 14.2(c) → H'=M ∨ M*** (~40 行): Y∈ℰ¹(L'*⊓K_i*) → ① M-side `maximalContaining_centralizer_eq_singleton…` (`typeP_structure ….2.2.2.2.2`: X∈ℰ¹(Kstar)⟹{M}; X∈ℰ¹(K)⟹{Mstar} via 14.7(1)/`exists_typeP_partner`) ② H'-side (Y≤L'*=Hσ' の Kstar' ⟹ {H'}) → `{H'}={M_i}` ⟹ H'=M∨Mstar ⟹ **H~H'=M∨Mstar**。**⚠ n=1 collapse 後の K_i*={K,Kstar} ラベリングと、`{H}` vs `{M_i}` の singleton 同定が要**。
- **見積: covering 核 = ~150-200 行 multi-iteration。摩擦点 = step1 の conjugation-invariance + step2 の dual membership。** matching の数学は worked out (上記)。次 iteration はこの順で。

**技法メモ (本 commit)**: `open Classical in` は docstring の**前**に置く (docstring→open は parse error); `hall_E_exists (G:=↥H) π` → `.map H.subtype` + `comap_map_eq_self_of_injective` 往復で `subgroupOf H` 形へ; `nlinarith [key]` は内部で "ring failed" trace を出すが成功 (error でない)。

### ✅ covering step 2 (matching) COMPLETE (2026-06-17 再開² cont., commit `05acdba0`) + 🔑 architectural finding: K-case = 14.7(1) = partner symmetry

**ユーザー指示「3 sub step」→ step 2 (matching の数学核) を green+axiom-clean で landing。** step 1/3 を深掘りして **covering の真の残依存 = partner symmetry (14.7(1))** を確定。
- **`isPiElement_mem_right_of_commute`** (dual helper): `isPiElementCompl_mem_left_of_commute` の A/B/π↔πᶜ swap 版 (`compl_compl` + commute 対称)。
- **🔑 `exists_inf_ne_bot_of_mem_zTilde_inter`** (matching, generic πM/πH): t∈Ẑ_M∩(L⊔Lstar), t∉L ⟹ `Lstar⊓K≠⊥ ∨ Lstar⊓Kstar≠⊥`。σ(H)-part w∈Lstar (≠1), w∈⟨t⟩⊆K⊔Kstar, σ(M)-/σ(M)'-part (∈⟨w⟩⊆Lstar) が Kstar/K に着地。数学は完全 worked out。

**🔑🔑 architectural finding (step 1/3 深掘り) — covering の残依存を確定**:
1. **step 1 (conjugation) は σ(H) 直接使用で軽量化可** — H を conjugate して Ẑ_{c•H} を作る必要なし。`𝒞_G(Ẑ_M)∩𝒞_G(Ẑ_H)≠∅` から t∈Ẑ_M, s∈Ẑ_H, t=c•s → t∈Ẑ_M ∩ ((c•L)⊔(c•Lstar)), t∉c•L。matching を **πH:=σ(H), L':=c•L, Lstar':=c•Lstar** で適用 (IsPiSubgroup は conj で order 不変ゆえ σ(H) のまま転送、**Msigma/kappa equivariance 不要**)。要 helper 3: `IsPiSubgroup π (c•N) ↔ IsPiSubgroup π N` (card 不変)、`c•zTilde L Lstar = zTilde (c•L)(c•Lstar)` (smul over sup/sdiff)、`𝓜(C_G(c•X))=c•𝓜(C_G(X))` (singleton 転送)。
2. **step 3 Kstar-case は clean** — Y∈ℰ¹(Lstar'⊓Kstar): Y≤Kstar ⟹ `𝓜(C_G(Y))={M}` (14.2(c)/M = `typeP_structure….2.2.2.2.2`); Y≤c•Lstar ⟹ `𝓜(C_G(Y))={c•H}` (14.2(c)/H + 𝓜-equivariance) ⟹ M=c•H ⟹ **H~M**。
3. **🛑 step 3 K-case = 14.7(1) = partner symmetry** — Y∈ℰ¹(Lstar'⊓K): Y≤K ⟹ 要 `𝓜(C_G(Y))={Mstar}` = **BG 14.7(1)**, repo 未証明。**= 14.2(c) for Mstar** (Mstar's Kstar = K): 要 **14.7(2) Kstar=Hall κ(Mstar) + 14.7(3) K=C_{Mstar_σ}(Kstar)** = partner symmetry `M∩Mstar=Z`。BG 14.7 証明末尾の論法 (Hall σ(M)-subgroup Y of Mstar containing Kstar → 14.2(f) Y⊆Mσ → [Y,X₁]⊆Mσ∩Mstar_σ=1 → Y⊆C_{Mσ}(X₁)=Kstar → Kstar=Mσ∩Mstar ◁ M∩Mstar → 14.2(b1) for Mstar: N_{Mstar}(Kstar)=Kstar×K → M∩Mstar=Z)。**~80-100 行 substantial co-proved 前提** (14.2(f)/14.2(b1) for Mstar は repo 在)。

**▶▶ 次 (covering 完成までの残り、依存順)**:
1. **partner symmetry** `M∩Mstar=Z` + 14.7(2) (Kstar Hall κ(Mstar)) + 14.7(3) (K=C_{Mstar_σ}(Kstar)) → 14.7(1) (𝓜(C_G(Y))={Mstar} for Y∈ℰ¹(K))。**lynchpin、~80-100 行、∃! bundle conjuncts も discharge**。
2. **step 1 equivariance helpers** ×3 (上記、~50 行 clean)。
3. **assembly `typeP_covering`**: 任意 type-P H → exists_zTilde_…(M)+(H) で両 bound → ncard_inter → matching → Kstar/K-case 双方で 14.2(c) double → H~M∨Mstar (~60 行)。
- **正本 = この節。matching は landed、partner symmetry が次の lynchpin。**

### ✅✅✅ partner symmetry 14.7(1)(2)(3) COMPLETE (2026-06-17 再開² cont., commits `0fbd151e` `e55a93d5`) — covering lynchpin 突破、残り = 機械的 assembly のみ

**🎉 BG 末尾の長い「Hall σ(M)-subgroup of Mstar」論法を回避する近道を発見。family 機構が既に partner 構造を encode していた。** covering の真のボトルネックだった partner symmetry を sorry-free + axiom-clean で landing。
- **`typeP_sigma_subgroup_le_Msigma`** (14.2(f), `0fbd151e`): σ(M)-subgroup Y<⊤ で Y⊓K*≠⊥ ⟹ Y≤Mσ。Cor 12.16 (`sigma_subgroup_conj_into_Msigma_general`, σ-disjoint gate=Thm13.9) + (d) で conjugator∈M。[結局 assembly では未使用 — 近道が判明したため。だが Prop 14.2(f) として独立価値+登録済]
- **🔑 `typeP_partner_structure`** (14.7(2)(3), `e55a93d5`): **Kstar=Hall κ(Mstar) ∧ K=C_{Mstar_σ}(Kstar)**。`typeP_family_member_data` が Mstar の Hall κ(Mstar)-subgroup KN + swap Z=KN⊔C_{Mstar_σ}(KN) を与え、`partner_canonical_eq` が Z⊓Mstar_σ=K。**KN=Kstar は双方向 `isPiSubgroup_le_left_of_commute` (π=σ(Mstar): K=σ(Mstar)-part, KN/Kstar=σ(Mstar)'-part) で card 不要**。一発 green。
- **🔑 `typeP_partner_centralizer_singleton`** (14.7(1), `e55a93d5`): **𝓜(C_G(Y))={Mstar} for Y∈ℰ¹(K)**。partner_structure で K=Mstar's Kstar-role ⟹ 14.2(c) for Mstar (`typeP_structure ….2.2.2.2.2`, U_Mstar は hall_E_exists)。covering K-case 解禁。

**▶▶ 残り = `typeP_covering` assembly のみ (機械的, ~100 行, 新数学ゼロ)** — 全 math piece 揃った:
1. M-bound (`typeP_zTilde_conjClass_gt_half`) + H-bound (`exists_zTilde_conjClass_gt_half_of_isTypeP`) → `ncard_inter_nonempty_of_two_mul_gt` → 共通元 u。
2. `mem_conjClassSet` (= `∃t∈A,∃g, g*t*g⁻¹=u`) 展開 → t∈Ẑ_M, s∈Ẑ_H, **t=c•s** (c=a⁻¹b)。
3. matching (`exists_inf_ne_bot_of_mem_zTilde_inter`, πM=σ(M), L'=c•L, Lstar'=c•Lstar) → **(c•Lstar)⊓K≠⊥ ∨ (c•Lstar)⊓Kstar≠⊥**。
4. rank-1 Y∈ℰ¹(交差) (`exists_prime_orderOf_dvd_card'`+zpowers、typeP_kappaHall_inf_conj_eq_bot のパターン) → double 14.2(c):
   - Kstar-case: Y≤Kstar→𝓜(C_G(Y))={M} (14.2(c)/M); Y≤c•Lstar→c⁻¹•Y≤Lstar→𝓜(C_G(c⁻¹•Y))={H} (14.2(c)/H, U_H 要再構成)→ c•H⊇C_G(Y) (centralizer_conj_smul) ∧ c•H maximal → c•H∈{M} → **c•H=M → H~M**。
   - K-case: Y≤K→𝓜(C_G(Y))={Mstar} (**14.7(1)=typeP_partner_centralizer_singleton**); 同様 → **c•H=Mstar → H~Mstar**。
- **要 equivariance 配線 (5)**: `conj_smul_mem_elemAbelianOfRank`(public✓) / `centralizer_conj_smul`(✓) / `isCoatom_conj_smul`(✓) / `mem_maximalSubgroups_of_isConjugateSubgroup`(✓) / **card_conj_smul (private×2 → inline 再証明要: `Nat.card_congr (L.equivMapOfInjective (conj c).toMonoidHom (conj c).injective)`)** + maximalSubgroupsContaining conj-singleton は inline (mem + isCoatom + centralizer_conj_smul で)。
- **IsConjugateSubgroup A B = ∃g, conj g•B=A** (g=1 で refl, line 6131)。c•H=M ⟹ H=c⁻¹•M ⟹ ∃g=c⁻¹, conj g•M=H ⟹ IsConjugateSubgroup H M。
- 正本 = この節。**partner symmetry 突破済 ⟹ typeP_covering は機械的 assembly のみ**。次セッションで完遂可。

### ✅✅✅✅ covering 14.7(7) COMPLETE (2026-06-18, commit `90651d52`) — ユーザー指示「3 sub-step」全完遂

**`typeP_covering` (BG 14.7(7)): ∀ H type-P, H~M ∨ H~Mstar。sorry-free + axiom-clean + AxiomsCheck。** step 1+2+3 を一気に assemble (新数学ゼロ、conjugation 配線のみ)。covering ボトルネックだった partner symmetry を先に突破済ゆえ機械的に完遂。
- 両 Ẑ の >½|G| (M-bound + `exists_zTilde_…of_isTypeP` [U も返すよう拡張]) → `ncard_inter_nonempty_of_two_mul_gt` → 共通元 → **t=c•s** (`MulAut.conj`/group tactic で c=a⁻¹b)。
- matching (`exists_inf_ne_bot_of_mem_zTilde_inter`, πM=σ(M)/πH=σ(H)) → Y≤c•Lstar が K/Kstar に当たる。
- double singleton: Y≤Kstar→{M} (14.2(c)); Y≤K→{Mstar} (14.7(1)); c⁻¹•Y∈ℰ¹(Lstar)→{H} (14.2(c)/H) → **c•H=M∨Mstar → H~M∨Mstar**。
- equivariance: `conj_smul_mem_elemAbelianOfRank`(public) / `centralizer_conj_smul` / `isCoatom_conj_smul` / `Subgroup.card_map_of_injective (conj c).injective` (=card_conj_smul inline) / cancel 補題 `conj c⁻¹•(conj c•X)=X` (`← map_mul`+inv_mul_cancel+map_one+one_smul、map_inv が LHS も書き換える罠を回避)。
- **🔑 技法**: `IsConjugateSubgroup M N = ∃g, conj g•M=N` (向き注意; `⟨c, hcHN⟩` 直接、conj c•H=N がそのまま witness)。`mem_maximalSubgroupsContaining.mp (hsing.symm ▸ Set.mem_singleton H)` で H∈𝓜 抽出。

**🛑 STOP — GATE「残 2 設計判断到達で停止」に到達**: typeP_duality ∃! bundle の covering/Hall κ(Mstar)/TI/P2/¬conj conjunct は全て in hand。残り typeP_duality 完成 = **(1) IsCyclic(K⊔Kstar) [Ω₁(Sylow) helper] (2) part(h) [Prop 14.2(a) UM_σ packaging]** の 2 設計判断のみ + uniqueness 組立。これらは原 AskUserQuestion の残 2 obligation でユーザー裁可待ち。
- **§14 funnel 進捗サマリ (2026-06-18)**: density bound + 14.7(e)(f) + partner symmetry 14.7(1)(2)(3) + **covering 14.7(7)** 全 landing。残 = 14.7(d) cyclic + 14.7(8) part(h) → typeP_duality close → §15/§16 unblock。正本 = この節。

### ✅ 14.7(d) cyclicity engine landing (2026-06-18, commit `7d56d199`) — IsCyclic の概念的核心、残り = Mσ-nilpotent-for-P2 + assembly

**ユーザー「難しいほう=IsCyclic」を選択。「Ω₁ helper 未特定」は誤りと判明 — `isCyclic_of_odd_of_isNilpotent_of_forall_pRank_le_one` (S12_ECore:461) が既存。**
- ✅ **`isCyclic_kappaHall_of_le_nilpotent`** (`7d56d199`): Hall κ(N)-subgroup K'≤N, K'≤W (nilpotent) ⟹ IsCyclic K'。pRank K' p≤1 (p∈π(K')⟹κ(N)⟹τ₁∪τ₃⟹pRank N p=1 via `tau1/tau3_pRank_eq_one`+`pRank_le_of_injective`; p∤card⟹0 via `mem_primeFactors_card_of_pos_pRank`) + nilpotent (`nilpotent_of_mulEquiv (subgroupOfEquivOfLe)`) + odd → helper。S12_ECore:849 パターン踏襲。**IsCyclic の "rank-1 nilpotent⟹cyclic" 核心。**

**▶ 残り IsCyclic (typeP_Z_isCyclic) = 2 piece (~90行, 機械的だが card 細部あり)**:
1. **`msigma_isNilpotent_of_isTypeP2`** (P2 ⟹ Mσ nilpotent, ~50行): P2 ⟹ `kappa M ⊊ sigmaComplementPrimes M` (kappa⊆sigmaComplementPrimes [κ⊆piSet∧⊆σᶜ] + IsTypeP2.2 [≠]) → `Set.exists_of_ssubset` で **p∈π(M)−(σ∪κ)** → max-rank A → **Lemma 14.1 `msigma_structure_of_notMem_sigma_kappa` .2.2**。
   - **max-rank A 構成** (crux): `exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G:=↥M)(p)(n:=pRank ↥M p) (hpos=one_le_pRank_of_mem_primeFactors hpπ) (le_refl)` → B:Subgroup ↥M, log_p|B|≥pRank; `le_pRank B hB_ea : log_p|B|≤pRank ↥M p` ⟹ log_p|B|=pRank; **card 細部** = `Nat.card B = p^(pRank)` (B elem-ab-p ⟹ |B|=p^(log_p|B|)、IsPGroup card 経由)。A:=B.map M.subtype, `IsElementaryAbelian.map`+`card_map_of_injective`。
2. **`typeP_Z_isCyclic`** (~40行): `isTypeP2_or_isTypeP2_partner` で M/Mstar P2 を case。
   - M P2: |K|=prime (typeP_structure (g) `.2.2.2.2.1 hM2`→⟨_,q,hq,hKq,_⟩) ⟹ `isCyclic_of_prime_card`; Kstar=Hall κ(Mstar) (partner_structure) ⊆ Mσ (nilpotent via piece-1) ⟹ `isCyclic_kappaHall_of_le_nilpotent (N:=Mstar)(K':=Kstar)(W:=Mσ)`; → `isCyclic_kappaHall_sup_Kstar_of_cyclic`。
   - Mstar P2: 対称 — |Kstar|=prime (Mstar's Hall κ); K=C_{Mstar_σ}(Kstar)⊆Mstar_σ (nilpotent) ⟹ `isCyclic_kappaHall_of_le_nilpotent (N:=M)(K':=K)(W:=Mstar_σ)`; → `isCyclic_kappaHall_sup_Kstar_of_cyclic hKstarMstar hKstar_hall hK_eq` で IsCyclic(Kstar⊔K)→sup_comm。
- **正本=この節。cyclicity engine 済 ⟹ 残り機械的。part(h) は IsCyclic 着地後 (K cyclic を要する)。**

### ✅✅✅ 14.7(d) IsCyclic COMPLETE (2026-06-18 lane-h 再開, commit `7de9ef75`) — Mσ-nilpotent + Z cyclic、残り = part(h) + ∃! uniqueness

**両 helper sorry-free + axiom-clean + AxiomsCheck 登録、full build green 3838 jobs ~65s、sorry 141 不変。** 上記「残り IsCyclic」2 piece を計画どおり一発 landing (`id hp` で obtain 後の hp 保持の 1 修正のみ)。
- ✅ **`msigma_isNilpotent_of_isTypeP2`**: P2 ⟹ Mσ nilpotent。`hsub : kappa M ⊆ sigmaComplementPrimes M` (witness P≤M, |P|=p ⟹ p∣|M|; `kappa_subset_sigmaCompl`) + `ssubset_of_subset_of_ne … hP2.2` + `Set.exists_of_ssubset` → p∈π−(σ∪κ); max-rank `B.map M.subtype` (`exists_isElementaryAbelian_log_card_ge` + `le_pRank` squeeze + `IsPGroup.exists_card_eq`/`Nat.log_pow`) → Lemma 14.1 `.2.2`。
- ✅ **`typeP_Z_isCyclic`**: `IsCyclic (K⊔Kstar)`。`typeP_partner_structure` で M* data → `isTypeP2_or_isTypeP2_partner` で M/M* case。**🔑 engine の N/W 分離が鍵**: `isCyclic_kappaHall_of_le_nilpotent` の N(Hall構造)と W(nilpotency)は別群可 — M-P2 case で N:=Mstar(Kstar=Hall κ(Mstar)), W:=Mσ M(nilpotent via piece-1 on M)。M*-P2 case は M*'s U を `hall_E_exists`(solvable ↥M*)で構成 → typeP_structure(M*) (g) で |Kstar| prime → sup_comm。
- **技法**: `obtain := id hp` で hp 保持; `hKstar.le.trans inf_le_left` で K≤Mσ (▸ より頑健); `rw [sup_comm]` は `IsCyclic ↥(·)` 下でも OK。

**▶▶ 残り = typeP_duality close = 2 piece (両 FT path 上 — §15 Cor 15.6/Lem 15.1 が part(h)、§15/§16 が ∃! を consume)**:
1. **∃! uniqueness assembly** (`typeP_partner_existsUnique` 推奨 standalone): existence の **8 conjunct すべて in hand** (maximal/typeP/¬conj=`typeP_family_pairwise_nonconjugate` / Hall κ(M*)=partner_structure / **IsCyclic=本commit** / TI=`typeP_zTilde_isTI` / P2-dichotomy / covering=`typeP_covering`)。witness=`exists_partner`。**uniqueness pin が intricate** (~100-150行): covering(Mstar0)を H:=Mstar' に適用 → Mstar'~Mstar0 (conjugate); ¬conj M Mstar' で ~M を排除。equality へは Hall-conjugacy (Kstar=Hall κ(Mstar0)=Hall κ(Mstar') の両方; c•Kstar も Hall κ(c•Mstar0) ⟹ ∃m∈Mstar', d:=mc∈N_G(Kstar) で d•Mstar0=Mstar') → **d∈Mstar0 を示す段が要設計** (N_G(Kstar) 関連の containment; 14.7(1)+`normalizer_le_of_maximalSubgroupsContaining_centralizer` は N_G(X)≤Mstar0 for X∈ℰ¹(K) を与えるが Kstar 側は別途)。
2. **part(h)** `IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)`: **Prop 14.2(a) の UM_σ normal complement が repo 未パッケージ = §13-gated 構築 gate** (S14:1657 docstring「(a) regular action on U / normal complement U M_σ … Deferred to proof time, gated on §13」)。building blocks = κ⊆τ₁ case の `Msigma_centralizer_E23_…`(525/676/767, E₃/E₂/E₁-half regular action)。M'=UM_σ には UM_σ◁M complement + K cyclic(本commit済)⟹ M/(UM_σ)≅K abelian。coprime conjunct は `coprime_card_derived_kappaHall_of_isComplement'` で free。**substantial/multi-session。**
- **正本=この節。** 次の選択 = uniqueness(self-contained, intricate)か part(h)(§13 構築 gate, longer)か。

### ✅✅✅ 14.7 ∃! partner COMPLETE + statement faithfulness fix (2026-06-18 lane-h 再開 cont., commit `023b2d36`) — 残り typeP_duality = part(h) のみ

**ユーザー「両方を順に (フル close)」を選択 → ∃! を先に完遂。`typeP_partner_existsUnique` sorry-free + axiom-clean + AxiomsCheck。full build green 3838 jobs ~56s、sorry 141。**

**🐛🐛 重大発見: 旧 typeP_duality の ∃! は証明不可能 (偽) だった** — uniqueness を精査して 2 つの statement bug を発見・修正:
1. **`hKM : K ≤ M` 欠落**: helper 全て (typeP_structure 等) が要求するが、`IsHallSubgroup (kappa M) (K.subgroupOf M)` 単独からは導けない (`K.subgroupOf M = K ⊓ M` が Hall でも K≤M は出ない)。hypothesis に追加。
2. **partner-symmetry conjunct 欠落**: `K = C_{Mstar_σ}(Kstar)` (BG 14.7(3)/appendix(4)) が無いと **反例**: `Mstar' := (Mstar)^d` (d∈N_{Mσ}(Kstar)∖Kstar、Mσ nilpotent[M P2 で normalizer condition]で存在) が他 conjunct を全て満たす (Hall κ(Mstar') Kstar は d∈N_G(Kstar) で保存、¬conj/covering/P2 は conjugacy 不変) のに Mstar'≠Mstar ⟹ ∃! 偽。**conjunct 4 を BG-appendix(4) 三つ組 `Kstar ≤ Mstar ∧ Hall κ(Mstar) Kstar ∧ K = C_{Mstar_σ}(Kstar)` に bundle** (§15/§16 consumer は pos 4 が `_` ゆえ pair/triple を吸収、pos 5-8 不変で無傷)。

**uniqueness の clean な核** (partner-sym があれば): competitor Mstar' に対し `K = C_{Mstar'_σ}(Kstar)` が **K を Mstar' の Kstar-role に**する ⟹ typeP_structure(Mstar') の last conjunct で `𝓜(C_G(X))={Mstar'}` (X∈ℰ¹(K))、これが `{Mstar}` (14.7(1)=`typeP_partner_centralizer_singleton`) に等しい ⟹ Mstar'=Mstar。**conjugation→equality の困難 (d∈N_G(K) gap) を完全回避**。line X は κ(M) nonempty → p∈κ → Hall で p∣|K| (`hK.2` で p∉index) → `exists_prime_orderOf_dvd_card'`。
- consumer 更新: hKM 渡す (S15 ×3 = hKM param、S16 ×1 = `Subgroup.map_subtype_le K'`)。

**▶▶ 残り = part(h) のみ** `IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M)` (typeP_duality の唯一 sorry `S14:7748`)。coprime conjunct は `coprime_card_derived_kappaHall_of_isComplement'` で free。

**part(h) = §13-gated 構築 (Prop 14.2(a) U M_σ normal complement、repo 全体で未構築 — `typeP_auxiliary_structure_gated` S15:721 の sorry も同 gap)**。BG L4061 経路:
- **M' = U M_σ** が核心:
  - **M_σ ⊆ M'** (Thm 10.2(c) = `Msigma_le_derived hG hM` ✓ 在)。
  - **U ⊆ M'**: Frobenius `E = E₁⋉U` (κ⊆τ₁ case = `isFrobeniusGroup_E_of_caseTau1` ✓) で **[E₁,U]=U** (coprime fixed-point-free `actsRegularlyOn_E23_E1_of_caseTau1` ✓ → `[A,N]=N`) ⊆ [M,M]=M'。case κ∩τ₃≠∅ は K=E (typeP_structure 第1枝の `hKEeq`) ⟹ U=1、U M_σ=M_σ。
  - **M' ⊆ U M_σ**: U M_σ ◁ M (K normalizes U[U◁E] + M_σ) + M/(U M_σ)≅K cyclic abelian ⟹ M'⊆ker=U M_σ。
- **K complements M'=U M_σ**: U M_σ ◁ M、K∩U M_σ=1 (K=κ群, U M_σ=κ'群[U=(κ∪σ)', M_σ=σ]), |K||U M_σ|=|M| (M=M_σ⋊E, E=K⋉U) → `IsComplement'`。
- building blocks 在: `E_complement`/`isComplement'_subgroupOf`/`card_Msigma_mul_card_E` (S12_ECore:192/229/243), `exists_subgroupESetup_with_le` (K≤E), `commutator_eq_self_of_isComplement'_le_commutator` (S06)。
- **摩擦点**: (i) 与えられた K (Hall κ)・U (Hall(κ∪σ)') を E-setup の E₁・E₂E₃ に matching (typeP_structure の proof が前例)、(ii) case split (κ∩τ₃ vs κ⊆τ₁) を mirror、(iii) coprime `[A,N]=N`、(iv) normal complement → IsComplement' API。**~150-250 行、multi-step。**
- 正本=この節。次セッション = part(h) 構築 (`derivedInG_eq_U_sup_Msigma` を核 lemma に切り出すのが推奨)。

### ✅✅✅✅ part(h) COMPLETE — typeP_duality fully proved + axiom-clean (2026-06-18 lane-h 再開³, commit `5272515f`)

**§14 long pole 完遂。`typeP_duality` の唯一残 sorry (part(h)) を埋め、`#print axioms` で `[propext, Classical.choice, Quot.sound]` のみ確認。full build green 3838 jobs、AxiomsCheck に 4 新エントリ登録・全通過。**

**🎯 設計の鍵 = 既存補題 2 本の発見**（LOOP GATE の「crux `[U,K]=U` 補題未発見」は誤りだった）:
1. **`OddOrder.BG.Ch2.S08.le_commutator_of_coprime_inf_centralizer_eq_bot`** (S08:1424): coprime FPF action `B≤N(Y)`, `Coprime|B||Y|`, `Y⊓C(B)=⊥` ⟹ `Y ≤ ⁅B,Y⁆`。これが `U=[K,U]` を与える(`sigma_eq_beta_and_prime_card_E1_of_caseTau1` S14:1521-1530 に `U≤derivedInG E` のパターン完成済だった)。
2. **`commutator_eq_sup_commutator_of_isComplement'`** (S14:79, 既存): `N◁H` complement `E`, `N≤commutator H` ⟹ `commutator H = N ⊔ ⁅E,E⁆`。統一補題そのもの。

**実装 (3 新補題、すべて sorry-free + axiom-clean、typeP_duality 直前に配置)**:
- **`derivedInG_eq_Msigma_sup_derivedInG_complement`** (統一, case-free): 任意 E-setup で `M' = M_σ ⊔ E'`。⊇ = `Msigma_le_derived`+`commutator_mono`; ⊆ = `↥M` 内で `x=a·b` 分解 (`a∈M_σ`,`b∈E`)、`b=a⁻¹x∈M'`、`b∈E⊓M' ≤ E'` (`inf_derivedInG_le_derivedInG` S12_ECore:318 = `E⊓M'≤E'`、quotient 論法済)。**`inf_derivedInG_le_derivedInG` が ⊆ を一撃で clean 化。**
- **`typeP_derivedInG_complement_of_eq_complement`**: 退化 `K=E` case (Prop 14.2(a) で U=1)。`IsCyclic K ⟹ E'=⊥ ⟹ M'=M_σ`、`h.isComplement'_subgroupOf` で締め。
- **`typeP_derivedInG_isComplement_kappaHall`** (part(h) 核、`[IsCyclic K]` 仮説): E-setup → `by_cases (κ∩τ₃).Nonempty`。
  - κ∩τ₃≠∅: typeP_structure の machinery (`E3_not_regular…`/`hEpi`/`hEdvdK`) を mirror → `K=E` → 退化 sub-lemma。
  - κ⊆τ₁: typeP_structure と同じく共役 (`exists_conj_eq_of_isHall_subgroupOf`) で `K=E₁'`。`by_cases Ebar₂⊔Ebar₃=⊥`:
    - =⊥: `Ebar=K` (eq_sup) → 退化 sub-lemma。
    - ≠⊥: Frobenius (`isFrobeniusGroup_E_of_caseTau1`)。`hfrob.isComplement` で `U⋊K=Ebar`、`hfrob.coprime_card_kernel_complement` で coprime。`U≤derivedInG Ebar` (le_commutator) + `commutator_eq_sup…` + K cyclic ⟹ `derivedInG Ebar = U`。`M'=M_σ⊔U`。complement = `isComplement'_of_disjoint_and_mul_eq_univ`: disjoint は `M'⊓K ≤ E'⊓K = U⊓K = ⊥` (coprime, `inf_derivedInG`)、univ は `M'` normal (`= commutator ↥M`) + `normal_mul` + `M'⊔K=M` (`U⊔K=Ebar`, `M_σ⊔Ebar=M`)。**card 積を完全に回避** (disjoint+univ 経路)。

**typeP_duality 配線**: `IsCyclic K` は counting collapse 由来 — `exists_partner`→`typeP_Z_isCyclic` (`IsCyclic(K⊔K*)`)→`Subgroup.subgroupOfEquivOfLe(le_sup_left).isCyclic.mp inferInstance` で K へ降下 (subgroup of cyclic は instance `Subgroup.isCyclic`)。

**⟹ §14 Type-P duality long pole DONE。§15/§16 (Lane G) の `typeP_duality` cite 群 (S15_MF:785/795/2170, S16:530) が実証明上に。** 残 S14 sorry = Cor 14.8 (`typeP1_conjugate_and_typeP_twoClasses`, 14.7(f)(g) から従う・未着手)、Cor 14.9 (faithful には gated M̃ 要・"do not prove as-is")、Cor 14.10 (`exists_sigmaDecomposition_length_le_two` = ℓ_σ≤2、**σ-decomposition theory [BG §1, 未形式化] が必須前提**)、Lem 14.11/Cor 14.12 (§13 gated)。**いずれも part(h) 経路外**; Cor 14.10 は FT-critical だが σ-decomp gate で別の大物。
- ⚠ **再調査するな**: crux `[U,K]=U` は `le_commutator_of_coprime_inf_centralizer_eq_bot` (S08) で既存。統一補題は `commutator_eq_sup_commutator_of_isComplement'` (S14) で既存。両方とも repo 内既出だった。
