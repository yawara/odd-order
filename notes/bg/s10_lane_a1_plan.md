# Lane A1 (S10_LocalLemmas) 実行プラン (2026-06-07)

worktree `/home/ywr/odd-order-bg-s10-leaves`, branch `bg-s10-leaves`, `ODD_ISSUE_BASE=2000`。
対象 = `OddOrder/BG/Ch3_MaximalSubgroups/S10_LocalLemmas.lean` の 7 sorry。

## 進捗 (2026-06-07)

- ✅ **10.11(d) `sigma_complement_commutator_cyclic_normal` DONE** (commit `eb6cc10`)。
  sorry-free・full build green (3586 jobs)。axiom 依存 = `propext/Classical.choice/Quot.sound` +
  `sorryAx`(後者は **10.11(c) `sigma_complement_rank_le_one` の transitive 依存のみ**;
  (d) は (c)+Thm 3.7 への正当な還元で、(c) が landing すれば自動 discharge)。
  - レシピ全 6 step を原文 (book p.78, mmd L2856) どおり: ①Isaacs Ch05 `fitting_coprime_abelian_decomp`
    で `K=C_K(P)×[K,P]` ②③積分解 (`coe_mul_of_left_le_normalizer_right` + `K₀⊓Mσ=⊥` の一意性) で
    `P` の FPF ④BG Thm 3.7 (`S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree`) で
    `K₀⊔Mσ` nilpotent ⑤新ヘルパ `commute_of_coprime_orderOf_of_isNilpotent`
    (`Sylow.directProductOfNormal` で成分分解) で `K₀≤C(Mσ)` ⑥(c) cite + cyclic 一意性。
  - 追加した private ヘルパ 3 個: `commute_of_coprime_orderOf_of_isNilpotent`,
    `cyclic_subgroup_eq_of_card_eq` (S10_BetaRadical の private 複製 → lane 合流時に
    S10_HallStructure へ hoist 推奨), `conjSmul_eq_map`。

- ⚠ **PDF offset 校正完了: `book page = PDF page − 13`** (PDF 102–105 = book 89–92 で確認)。
  当初プランの「10.12 = book p.92」「10.3/10.4/10.5 = p.87」は **誤り** (book p.85–92 は §12
  "The Subgroup E"; 10.3/10.4/10.5 は §10 内なのでもっと前)。正しい §10 範囲:
  - §10 = **book 76–79 = PDF 89–92**, §11 = book 80–84, §12 = book 85–92。
  - **Lemma 10.12: 文 = book p.78 (PDF 91 末), 証明 = book p.79 (PDF 92 冒頭)。**
  - **Lemma 10.13: book p.79–80 (PDF 92–93), 証明あり (mmd で欠落していた本体)。**
  - 10.3/10.4/10.5 は §10 前半 (book p.76 以前 = PDF 88 以前) を要再読込で位置確定。

### 10.12 `disjoint_of_not_conj` 証明 (book p.79 冒頭, PDF 92 で回収)

(Nougat 単独ページ再OCR `-p 92 --no-skipping` で確実に回収。私の最初の手読みは誤りだった —
"not abelian"→**"not normal in `M`"**、`N_G(S)⊆M`→**`N_G(S)⊆H^g`**、末尾は「`p∉α(M)` **かつ
`M_σ` は nilpotent でない**」が**結論**。訂正後は行間ゼロの完結した3文証明。)

> Proof. Suppose `p ∈ σ(M) ∩ σ(H)`. Then some Sylow `p`-subgroup `S` of `G` lies in `M`
> and in some conjugate `H^g` of `H`. By the **Uniqueness Theorem**, `r(S) ≤ 2` because
> `H^g ≠ M`. Furthermore, `S` is not normal in `M` because `N_G(S) ⊆ H^g`. This shows that
> `p ∉ α(M)` and that `M_σ` is not nilpotent. Now we are done because
> `π(M_α ∩ H_σ) ⊆ α(M) ∩ σ(H) ⊆ σ(M) ∩ σ(H)` and `π(M_σ ∩ H_σ) ⊆ σ(M) ∩ σ(H)`.

- **核心 (任意の `p ∈ σ(M)∩σ(H)`)**: 共通 Sylow `S ≤ M ∩ H^g` を取る (∵ `p∈σ(M)` で
  `N_G(P)⊆M` な Sylow-of-`M` `P` は Sylow-of-`G`; 同様に `p∈σ(H)`; 2 つの Sylow-of-`G` は共役)。
  - `r(S) ≤ 2` (Uniqueness, `S ≤ M ∩ H^g`, `M ≠ H^g`) ⟹ `r_p(M) ≤ 2` ⟹ **`p ∉ α(M)`**。
  - `N_G(S) ⊆ H^g ≠ M` ⟹ `S` は `M` で非正規 (正規なら `M ⊆ N_G(S) ⊆ H^g`, 極大性で `M=H^g` 矛盾)。
    `p∈σ(M)` で `S ≤ M_σ` (Hall σ)。`M_σ` nilpotent なら Sylow `S` が `M_σ` で characteristic、
    `M_σ ⊴ M` ゆえ `S ⊴ M` で矛盾 ⟹ **`M_σ` not nilpotent**。
- **(a)** `α(M)∩σ(H)=∅` (∵ `p∈α(M)∩σ(H)⊆σ(M)∩σ(H)` → `p∉α(M)` 矛盾); `M_α∩H_σ=1` は
  `π(M_α∩H_σ)⊆α(M)∩σ(H)=∅`。**(b)** `M_σ` nilpotent ⟹ `σ(M)∩σ(H)=∅` (∵ さもなくば
  `M_σ` not nilpotent 矛盾); `M_σ∩H_σ=1` 同様。
- **依存**: §9 Uniqueness (`S ≤ 2 distinct maximals ⇒ r(S)≤2`, repo `S09_*` 要確認),
  `p∈σ(M)` で Sylow-of-`M` が Sylow-of-`G` (N_G⊆M argument), Sylow 共役 (mathlib),
  `M_σ`=Hall σ + nilpotent⇒Sylow char⇒正規, `π(A⊓B)⊆π(A)∩π(B)` + `π(M_α)⊆α(M)` 等。
  **行間は無い**; ブロッカーは無し。

- ✅ **10.12 DONE** (commit `95a313c`)。core lemma `mem_sigma_inter_sigma_imp` 経由で上記証明を
  そのまま形式化、**axiom-clean** (sorryAx 無; §9 Uniqueness が axiom-clean なので)。
  使った主要部品: 新 public base lemma `exists_sylow_le_normalizer_le_of_mem_sigma`
  (S10_HallStructure; 既存 private `isSylow_sylowMap_of_mem_sigma` +
  `normalizer_sylow_map_le_of_mem_sigma` の packaging), replicate `sylow_subgroupOf_of_le`
  (S07 private の複製), `S09.isUniquelyMaximal_of_three_le_rank_of_lt_top`,
  `pRank_sylow_eq`+`pRank_le_rank`, `Msigma_isHall`, `Sylow.coe_subgroup_smul`+
  `map_normalizer_eq_of_bijective`, `AppB.normalizer_le_normalizer_map_of_characteristic`,
  `inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl`。

### 残り §10 leaves: 証明回収済 + 依存マップ (2026-06-07, Nougat `-p N --no-skipping` 再OCR)

旧 MISSING_PAGE を全回収。10.3/10.4 = **PDF 87 (book p.74)**, 10.5 proof = mmd L2767-2774 (既存),
10.13 = **PDF 92-93 (book p.79-80)**。以下、原文証明と Lean 形式化の依存。

#### ✅ 10.4 `alpha_criterion` DONE (commit `cd5e10b`, axiom-clean) — scaffold バグ修正済

statement を本 10.4(a)(c) (`p∉σ(M)` 版) に修正 + 証明。`#print axioms` = 標準3つ (sorryAx 無)。
`sylow_le_derived_of_mem_sigma` を public 化、`sylow_subgroupOf_of_le` を leaf 先頭へ移動 (10.5/10.12 共有)。
以下は修正前の経緯記録:

#### ⚠⚠ (経緯) `alpha_criterion` (10.4) の旧 Lean statement は **原文と不一致 (scaffold バグ)**

回収した **本 Lemma 10.4**: (a) `p ∣ |M/M'| ⇒ p∉σ(M)`; (b) `p∉σ(M), M_α≠1 ⇒ ∃x∈Ω₁(Z(P))#:
ℳ(C_G(x))≠{M} ∧ C_{M_α}(x) Z-group` (Lean は省略); (c) `p∉σ(M), r_p(M)=2 ⇒ p not ideal ∧
ℰ_p²(M)⊆ℰ_p*(G)`。**Lean `alpha_criterion` は (a) を `p∉α(M)` (弱い; α⊆σ で従う) に、(c) の仮定を
`p∈α(M)` に誤記**。`p∈α(M)` は `3≤pRank` を含むので `pRank=2` と矛盾 → **Lean (c) は vacuous**
(p∈α ∧ pRank=2 から False を出せば sorry-free に「証明」できてしまうが中身ゼロ)。
`alpha_criterion` は **downstream 未使用** (grep 確認済) なので、**statement を本 10.4(a)(c) に修正
(`p∉σ(M)` 版) してから証明するのが正しい**。修正せず vacuous proof で埋めるのは scaffold-sorry-free
≠ proved の典型的な罠なので避ける。本 (a) proof = Thm 10.2(c) (`sylow_le_derived_of_mem_sigma`,
private) 即時; 本 (c) proof = 「A∈ℰ_p²(M), A∉ℰ_p*(G) ⇒ Uniqueness で A∈𝒰 ⇒ N_G(P)⊆M ⇒ p∈σ 矛盾」。

#### 10.3 `centralizer_isUniquelyMaximal_of_two_le_rank` (statement OK, 本と一致)

本 proof (PDF 87): r_p(C_{M_α}(X))≥2 な p, B∈ℰ_p(C_{M_α}(X)) max order。X は M_α を coprime に
正規化 → **Prop 1.5** (`Ch04.exists_aInvariant_sylow`) で X が B⊇ な M_α の Sylow p `P` を正規化。
B∉𝒰 と仮定 → Uniqueness で r(C_P(B))≤2 → |B|=p² ∧ Ω₁(C_P(B))=B⊆C_P(X) → **Cor 1.12** (要特定:
coprime + Ω₁ 固定 ⇒ 全固定の剛性) で C_P(X)=P → r(C_M(X))≥r(P)≥3 (p∈α) → Uniqueness で 𝒰。
依存: `exists_aInvariant_sylow`, **Cor 1.12 (未特定)**, uniquenessTheorem, α-rank, max-order B。中規模。

#### 10.5 `pRank_eq_two_of_normalizer_le` (statement OK; **§11 Hyp 11.1 を解除する高価値**)

本 proof (mmd L2767-2774, 既存): α⊆σ ⇒ p∉α ⇒ r_p(M)≤2。P=Sylow p of M ⊇X。r_p=1 なら
**Lemma 4.5** で P cyclic → X=Ω₁(P), N_G(P)⊆N_G(X)⊆M ⇒ p∈σ 矛盾 → r_p(M)=2。X≠Ω₁(Z(P)) ⇒
A:=XΩ₁(Z(P))∈ℰ²(P)⊆ℰ_p²(G) ∋X。p not ideal = **本 10.4(c)**。
依存: `alpha_subset_sigma`, Lemma 4.5 (r_p=1⇒cyclic, **未特定** — 逆向き `exists_..._not_isCyclic_of_two_le_pRank`
は有), σ-intro (N_G(Sylow)⊆M ⇒ p∈σ; `mem_sigma_iff` 逆), Ω₁(Z(P)) of cyclic, **10.4(c)**, idealPrime def。

#### 10.13 `nonabelian_pSubgroup_rankTwo_elemAbelian_structure` (statement OK)

本 proof (PDF 92-93): S⊇P Sylow p of G, Z₁=Ω₁(Z(S))。(10.4)(10.5)(10.6) 経由で
r(S)=2 / r(S)≥3 の場合分け、**Thm 5.3** (narrow) + Cor 10.7(b) を使い C_S(A)=A₀×Y (Y cyclic)。
(c): x∈N_P(A)−C_P(A) が位数 p の自己同型を誘導、Z₀ 中心化 → A の p-部分群を transitive 置換。
依存: §5 narrow p-群構造 (Thm 5.3, Cor 10.7(b)), Ω₁(Z(·)), ℰ¹/ℰ² API。§5 重め。

**総括**: 4 leaf とも原文回収済・依存マップ済だが、各 100-200 行規模の本格証明 (+ 10.4 は statement 修正要)。
着手順推奨: 10.4 (statement 修正 + 短い proof) → 10.5 (10.4(c) 利用, §11 解除) → 10.3 (Cor 1.12 特定後) →
10.13 (§5 重)。Cor 1.12 と Lemma 4.5 (cyclic) の repo 内特定が次の前提作業。

## ⚠ 依存の実態 (BG 原文を読んで判明 — 当初の docstring ベース map は楽観的すぎた)

| leaf | BG# | 実依存 | A1 で独立に可? |
|---|---|---|---|
| `sigma_complement_rank_le_one` | 10.11(a)(b)(c) | (a) Thm 4.20+base; **(b) Prop 10.10 (spine!)**; (c)←(b) | ✗ (b)(c) が spine 待ち |
| `sigma_complement_commutator_cyclic_normal` | 10.11(d) | **Thm 3.7** + (c) + coprime 分解 | ✅ **DONE** (eb6cc10, (c) 還元) |
| `disjoint_of_not_conj` | 10.12 | Uniqueness Thm (§9, 証明済) | ✅ **DONE** (95a313c, **axiom-clean** sorryAx 無) |
| `centralizer_isUniquelyMaximal_of_two_le_rank` | 10.3 | Uniqueness | 要 PDF 再読込 (§10 前半, ≈book p.76 以前=PDF≤88) |
| `pRank_eq_two_of_normalizer_le` | 10.5 | §7 Prop 7.5 等 | 要 PDF 再読込 (§10 前半) |
| `alpha_criterion` | 10.4(a)(c) | (a) def+§4; (c) Thm 5.3/ideal | 要 PDF 再読込 (§10 前半) |
| `nonabelian_pSubgroup_rankTwo_elemAbelian_structure` | 10.13 | p-群構造 | 証明回収済 (book p.79–80=PDF 92–93) |

**教訓**: §10 leaf は spine (Prop 10.10/Cor 10.7) と絡む or 旧 MISSING_PAGE (PDF 回収で解決)。
当初の「6-7 完全独立」+「page 番号」推定は誤り。正しい offset = `book = PDF − 13`。

## 最良ターゲット: 10.11(d) `sigma_complement_commutator_cyclic_normal` (Thm 3.7 シナジー)

BG 原文 (L2856 proof (d)): 「K₀=[K,P], K=K₀×C_K(P) (K abelian p'-group), P が K₀M_σ に作用し
C_{K₀M_σ}(P)=C_{K₀}(P)C_{M_σ}(P)=1。**∴ Theorem 3.7 で K₀M_σ nilpotent**。ゆえに K₀ は M_σ を
中心化し、(c) より K₀ は M の cyclic normal 部分群」。

### Lean 実装レシピ (推定 ~120-150 行)
1. **coprime 分解** `K = C_K(P) × [K,P]`: `OddOrder.Isaacs.Ch05.fitting_coprime_abelian_decomp`
   (P:=K abelian, K:=P acting; `hK_norm` = P ≤ N(K) from `hPN`; coprime = |P|=p ∤ |K| (K is p'));
   返り値 `(C_K(P) ⊓ K) ⊓ ⁅K,P⁆ = ⊥ ∧ (C_K(P)⊓K) ⊔ ⁅K,P⁆ = K`。
2. **K₀:=⁅K,P⁆ の基本性質**: ≤K (P normalizes K), ≤M', p'-group, abelian (≤K)。
   `C_{K₀}(P) = K₀ ⊓ C_K(P) = ⊥` (decomp の交わり)。
3. **N:=K₀ ⊔ M_σ の FPF**: `C_N(P)=⊥`。coprime action で C of product = product of C's
   (`C_{K₀}(P)=⊥` + `C_{M_σ}(P)=⊥` from `hCP`)。要: P normalizes N (P≤M≤N(M_σ), P normalizes K₀),
   disjoint(N,P) (N is p', P is p), |P|=p prime (`hP : P∈ℰ_p¹` → card=p), IsSolvable ↥N (≤M proper)。
4. **Thm 3.7 適用**: `OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree`
   (N:=K₀M_σ, R:=P) → `Group.IsNilpotent ↥(K₀ ⊔ M_σ)`。
5. **K₀ centralizes M_σ** (infra 全て特定済・未知ゼロ): nilpotent K₀M_σ で K₀ (σ' Hall) と
   M_σ (σ Hall) は coprime。M_σ ⊴ N は自明 (M_σ⊴M⊇N)。K₀ ⊴ N は nilpotent から:
   `OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent` (各 Sylow 正規) → σ'-Sylow 積 = K₀ 正規、
   or `Sylow.directProductOfNormal` (nilpotent → Sylow 直積) で σ'-Hall=K₀ を取り出す。
   両正規 + disjoint (K₀⊓M_σ=⊥, coprime order) →
   `Subgroup.commute_of_normal_of_disjoint` で `⁅K₀,M_σ⁆=⊥` (or `commutator_le_inf` で
   ⁅K₀,M_σ⁆≤K₀⊓M_σ=⊥)。⇒ K₀ ≤ C_G(M_σ)。
6. **cyclic normal**: `sigma_complement_rank_le_one hG hM hKM hKpi` の (c) (= `C_K(M_σ)⊓M'` cyclic
   normal Z) を cite。K₀ ≤ C_K(M_σ) (step5) ∧ K₀ ≤ M' → K₀ ≤ Z。subgroup of cyclic = cyclic;
   cyclic の subgroup は characteristic → Z⊴M ⇒ K₀⊴M。
   ⇒ **10.11(d) は 10.11(c) + Thm 3.7 に還元** (c が landing すれば完全 discharge)。

### 注意
- `sigma_complement_rank_le_one` (c) を cite する = (d) 本体は sorry-free だが推移的に (c)=sorry に依存。
  これは正当な還元 (scaffold-sorry-free ≠ proved の原則下、(d)→(c)+Thm3.7 の reduction は実内容)。
- step 5 の nilpotent-Hall-normal が mathlib に無ければ自作 (中規模)。ここが最大の未知。

## MISSING_PAGE 系 (10.3/10.4/10.5/10.12/10.13)
PDF `references/bg/local-analysis.pdf` の該当ページを `Read pages=N` で読込 (book p.87/p.92/p.79;
PDF page offset 要校正)。10.12 は Cor 11.4 を解除する高価値だが Uniqueness 経由の本格証明。

## 推奨着手順
1. 10.11(d) (Thm 3.7 シナジー, infra 既存) ← step5 の nilpotent-Hall だけ確認すれば最短
2. 10.12 (PDF 読込 → Uniqueness 証明, 高価値)
3. 残 MISSING_PAGE は PDF 読込後
