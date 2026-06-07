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

#### 10.3 `centralizer_isUniquelyMaximal_of_two_le_rank` (statement OK; **残=本体のみ, Cor 1.12 解決済**)

**PDF 87 (book p.74) 逐語回収 (2026-06-07)**:
> Take a prime `p` for which `r_p(C_{M_α}(X)) ≥ 2` and choose a group `B ∈ ℰ_p(C_{M_α}(X))` of
> maximal order. Now `X` normalizes `M_α` and has order relatively prime to `|M_α|`. By
> Proposition 1.5, `X` normalizes some Sylow `p`-subgroup `P` of `M_α` that contains `B`.
> Clearly we can assume that `B ∉ 𝒰`. By the Uniqueness Theorem, `r(C_P(B)) ≤ 2`. Hence
> `|B| = p²` and `Ω₁(C_P(B)) = B ⊆ C_P(X)`. By Corollary 1.12, `C_P(X) = P`. Therefore
> `r(C_M(X)) ≥ r(P) ≥ 3` because `p ∈ α(M)`. By the Uniqueness Theorem, `C_M(X) ∈ 𝒰`. □

**Lean 組み立てプラン + API 対応**:
1. `2 ≤ rank C_{M_α}(X)` ⇒ `∃ p prime, 2 ≤ pRank C_{M_α}(X) p`。← **要 helper**(rank=⨆_p pRank の
   sup≥2 ⇒ ある項≥2; `le_ciSup` + 有限性で構成、~10 行)。
2. max-order `B ∈ ℰ_p(C_{M_α}(X))`: `Finite` ゆえ最大位数 elem-ab を選べる(`exists_maximalElementaryAbelian_ge`
   = `NarrowPGroup:151`、または card-argmax)。`|B| ≥ p²`。
3. X が M_α を coprime 正規化 + B を含む A-不変 Sylow P: **Prop 1.5** = `Ch04.aInvariant_pSubgroup_le_aInvariant_sylow`
   (`ForwardFromCh03:554`、A-不変 p-部分群 ⊆ A-不変 Sylow) ✅。
4. **case B∈𝒰**: `IsUniquelyMaximal.of_le_of_lt_top`(`B ≤ C_M(X) < ⊤`)で即 `C_M(X)∈𝒰`(line 67 で使用例)。
   ⇒ 以降 B∉𝒰 と仮定。
5. **✅ 核心ステップ解決 (2026-06-07)**: `B∉𝒰 ⇒ r(C_P(B)) ≤ 2`。対偶: `r(C_P(B))≥3` を仮定。
   `C_P(B)<⊤` ゆえ `isUniquelyMaximal_of_three_le_rank_of_lt_top` で **`C_P(B)∈𝒰`**。さらに
   `B ≤ C_G(C_P(B))`(C_P(B) は B を中心化 ⇒ 対称に B も C_P(B) を中心化)かつ `rank B ≥ 2`
   ゆえ `isUniquelyMaximal_of_le_centralizer_of_two_le_rank`(L=C_P(B), K=B)で **`B∈𝒰`** ⇒ 矛盾。
   ∴ `r(C_P(B))≤2`。**両 Uniqueness 補題は既存・難所解消**。
6. `|B|=p²`: `r(B)=log_p|B|≤r(C_P(B))≤2` かつ `|B|≥p²` ⇒ `=p²`(易)。`Ω₁(C_P(B))=B`: `B≤Z(C_P(B))`
   (B abelian, C_P(B) が B 中心化)で `r(Z(C_P(B)))=2`; rank-2 p-群が非可換なら中心 cyclic(**BG Thm 4.16
   = §4 `S04f_Blackburn`, spine ではない**)ゆえ `C_P(B)` 可換 ⇒ `Ω₁(C_P(B))` = rank-2 elem-ab = B。
   **step 6 は §4 Thm 4.16 で A1 内完結(Cor 10.7(b) spine 経由不要)**。
7. `Ω₁(C_P(B))=B ⊆ C_P(X)`: B≤C_{M_α}(X)⊆C_G(X) so B⊆C_P(X); X が C_P(B) の Ω₁=B を全固定。
8. **Cor 1.12** = `S01c.actsTrivially_of_fixes_omega1_centralizer` ✅ (今回実装) で `C_P(X)=P`
   (E=B, group=P, A=X; X が C_P(B)⊇C_P(?) の order-p を固定 ⇒ X trivial on P)。
9. `r(C_M(X)) ≥ r(P) ≥ 3` (p∈α(M) ⇒ r_p(M)=r_p(M_α)=r(P)≥3, P=Sylow p of M_α; P≤C_M(X))。
10. **最終**: `isUniquelyMaximal_of_three_le_rank_of_lt_top`(`S09_Lemma95:2799`)+ `C_M(X)<⊤`。

依存総括: Prop 1.5 ✅, Cor 1.12 ✅(S01c), 最終 Uniqueness ✅, of_le_of_lt_top ✅; **未=step1 helper +
step5 の Uniqueness corollary 特定 + max-order B**。最重・~150 行。Cor 1.12 が解決したので残るは本体組立。

**🚧 進捗 (2026-06-07, uncommitted WIP in worktree)**: 10.3 の **math core 完成・compiling**。
DONE (sorry-free): 設定 (CMX<⊤) + step1 (`exists_pRank_ge_of_pos_le_rank`) + step2 (B: log≥2,
`exists_isElementaryAbelian_log_card_ge` を map up) + step4 (`hBU.of_le_of_lt_top`) + **step5 (難所:
`isUniquelyMaximal_of_three_le_rank_of_lt_top` + `isUniquelyMaximal_of_le_centralizer_of_two_le_rank`)**
+ `|B|=p²` 導出 (`rank_le_of_injective` + `log_card_le_pRank`) + **step6 (rank-3 矛盾: g∉B order p ⇒
`B⊔⟨g⟩` elem-ab order>p², `sup_of_le_centralizer`+`Commute.zpow_left`)** + step10。
- **max-order B は不要だった** (rank-2 B で step6 の rank 引数が回る)。step6 は Thm 4.16 不要。

残 3 sorry (= plumbing のみ、math 不確定ゼロ):
- **step3** `∃ P ≤ M_α, IsPGroup, X≤N(P), B≤P, pRank↥M p ≤ pRank↥P p`: X の M_α 上共役作用 →
  X-不変 Sylow。template = **S11:480-510** (`MulDistribMulAction.compHom`+`toMulAut`) +
  coprime = **10.11d:649-654** idiom (`Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl`,
  hXpi + `Malpha_isPiGroup`) + `le_normalizer_opiCoreInG (alpha M) M` (X≤N(M_α)) +
  `aInvariant_pSubgroup_le_aInvariant_sylow (G:=↥M_α)`。B は X-fixed (B≤C_G(X)) ゆえ A-inv。
  pRank↥P p=pRank↥M p は **`sylow_le_Malpha_of_mem_alpha_of_isHall`** + `pRank_sylow_eq` + `Malpha_isHall`。
- **step7** `P ≤ C_G(X)`: X の P 上共役作用 + **S01c `actsTrivially_of_fixes_omega1_centralizer`**
  (E=B.subgroupOf P, X が `C_P(B)` の order-p 元=Ω₁(C_P(B))=B (step6 hOmega) を固定 (B≤C_G(X)))。
- **step9** `3 ≤ rank↥(C_G(X)⊓M)`: P≤C_G(X)(step7)∧P≤M ⇒ rank ≥ rank↥P ≥ pRank↥P p ≥ pRank↥M p ≥3
  (`hpα` = p∈α via p∣|M_α| + `Malpha_isPiGroup`; `mem_alpha_iff`)。`rank_le_of_injective` で rank mono。

**✅ Cor 1.12 チェーン DONE (2026-06-07, `S01c_Omega1Rigidity.lean`, axiom-clean)**: BG **Cor 1.12**
(mmd L457) = 「p odd, G p-群, E elem-ab ≤G, A は p'-operator 群で `C_G(E)` の位数 p の元を全固定
⇒ A は G に trivial に作用」。実装した §1 結果:
- **BG Thm 1.11** (mmd L453, Gorenstein 5.3.10): `actsTrivially_of_fixes_omega1`(抽象 `MulAut P` 版)
  + `actsTrivially_on_of_fixes_omega1`(A-不変部分群版)。**既存エンジン `CriticalSubgroup.isPGroup_autFixerOfOrderP`**
  (`C_{Aut P}(Ω₁)` は p-群) から短く導出: `φ a ∈ autFixerOfOrderP`(p-群)ゆえ `orderOf(φ a)` は p-冪、
  かつ `∣|A|`(p と互いに素)⇒ `=1`。**当初「非可換版が未形式化」と判断したが engine が既にあった**。
- **BG Prop 1.10** (mmd L445): `S01_Solvable.coprime_nilpotent_acts_trivially_of_centralizer_self`
  として**既に存在**(当初「未パッケージ」は誤り)。
- **Cor 1.12** = `actsTrivially_of_fixes_omega1_centralizer`: E≤C=C_G(A) → C_G(C)⊆C_G(E) → Thm 1.11 で
  C_G(C)⊆C → Prop 1.10。全て `φ : A →* MulAut G` 形式。
⇒ **残るは 10.3 本体のみ**: PDF 87 の正確な proof 回収 + 組み立て(Prop 1.5 `exists_aInvariant_sylow`
+ Uniqueness + max-order B + Cor 1.12)。A1 lane で続行可。

#### ✅ 10.5 `pRank_eq_two_of_normalizer_le` DONE (axiom-clean; **§11 Hyp 11.1 を解除**)

2026-06-07 完成・sorry-free・`#print axioms` = 標準3つ (sorryAx 無)。本文 (mmd L2767-2774) を直訳。
新規 leaf-private helper 2 個:
- `isCyclic_of_pRank_le_one` (= **Lemma 4.5 の逆**): odd p-群 pRank≤1 ⇒ cyclic。既存
  `exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic` の対偶 + `le_pRank`。
- `normalizer_le_normalizer_omega1CenterInG`: `N_G(P) ≤ N_G(Ω₁(Z(P)))`。inner `omega1OfAbelian ↥P (center) p`
  の characteristic を `CriticalSubgroup.omega1Center.characteristic` の複製で示し
  `AppB.normalizer_le_normalizer_map_of_characteristic` 適用。

実装メモ: `PM : Sylow p ↥M`, `P := (PM:Subgroup↥M).map M.subtype` で `pRank ↥P = pRank ↥M`
(`pRank_le_of_injective` 双方向 + `pRank_sylow_eq`)。σ-introduction は σ-def の witness `⟨hpπ, PM, _⟩` を
直接供給 (**Uniqueness 不使用**)。(iii) は `A = X ⊔ Ω₁(Z(P))` を `↥P` 内で構成 (`sup_of_le_centralizer`,
`omega1OfAbelian_isElementaryAbelian`, `Z'≠⊥` は `exists_mem_omega1_center_of_normal_ne_bot` N=⊤)、
`|A|=p²` を `pRank ↥P=2` 上限 ∧ `X'⊊A'` 下限で挟み `P.subtype` で `G` へ push。leaf 内で
`alpha_criterion`/`cyclic_subgroup_eq_of_card_eq` の後ろへ移動 (forward-ref 回避)。

(以下は着手前の回収メモ。)
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

**総括 (2026-06-07 更新)**: A1 lane で着手可能だったのは 10.11(d)/10.12/10.4/10.5 の 4 つ → **全て DONE・axiom-clean**。
残りは 10.3 (Cor 1.12 未特定)、10.13 (§5 narrow 重)、10.11(a)(b)(c) (spine `Prop 10.10` 待ち=A1 不可)。
着手順推奨 (残り): 10.3 (Cor 1.12 = coprime+Ω₁ 固定 ⇒ 全固定 の repo 内特定が前提) → 10.13 (Thm 5.3/Cor 10.7(b))。

## ⚠ 依存の実態 (BG 原文を読んで判明 — 当初の docstring ベース map は楽観的すぎた)

| leaf | BG# | 実依存 | A1 で独立に可? |
|---|---|---|---|
| `sigma_complement_rank_le_one` | 10.11(a)(b)(c) | (a) Thm 4.20+base; **(b) Prop 10.10 (spine!)**; (c)←(b) | ✗ (b)(c) が spine 待ち |
| `sigma_complement_commutator_cyclic_normal` | 10.11(d) | **Thm 3.7** + (c) + coprime 分解 | ✅ **DONE** (eb6cc10, (c) 還元) |
| `disjoint_of_not_conj` | 10.12 | Uniqueness Thm (§9, 証明済) | ✅ **DONE** (95a313c, **axiom-clean** sorryAx 無) |
| `centralizer_isUniquelyMaximal_of_two_le_rank` | 10.3 | Cor 1.12 ✅(S01c)+ Prop 1.5 + Uniqueness | ⏳ 本体のみ残(PDF 87 回収+組立) |
| `pRank_eq_two_of_normalizer_le` | 10.5 | σ-def + Lemma 4.5逆 + Ω₁(Z) + 10.4(c) | ✅ **DONE** (axiom-clean; §11 解除) |
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
