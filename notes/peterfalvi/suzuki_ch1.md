# Peterfalvi Part II (A Theorem of Suzuki) — Ch. I §1 frontier

正本ソース = `references/peterfalvi/05.3_pp_100_107_General_Properties_of_G.mmd`
(pp. 100–107, "General Properties of G")。Coq crib は**無い** (math-comp/odd-order
は Part I のみ)。行間は本文 PDF + ChatGPT。

ファイル: `OddOrder/Peterfalvi/Appendices/Suzuki/` (hub `Suzuki.lean` は pure re-export)。
- `Basic.lean` — 仮説 (A1)–(A3) `Hypothesis` 構造 + 記法 `K,V,W` + dictionary
  (`qRegularEquiv`: Q regular on Ω−{H}, `card_G_eq`) + **Prop 1 (a)–(e)**。
- `InvolutionClass.lean` — **Prop 2 (a)–(d)** (involution 単一共役類ほか) + **Prop 3**
  (`|K|=|H∩I|`, `s^K=H∩I`)。`image_conj_KSet_eq_involutions_H` が K↔H∩I 全単射。
- `CanonicalForm.lean` — **Prop 4 (a)** (canonical form `g=xty` 一意)。
- `DistinguishedInvolution.lean` — **Prop 4 (b)** (distinguished involution `s` +
  structure equation `tst=r⁻¹tr` 一意) + **Prop 4 (c)** (`𝒩(G)=C_D(Q)=1`)。

## 重要な設計事実: (A2) faithful ⇒ 𝒩(G)=1

`Hypothesis` は (A2) = `faithful : FaithfulSMul G Ω` を standing で持つ (book 通り、
05.1 mmd L13)。ゆえに `𝒩(G)=⋂_x H^x = normalCore H = ker(action) = 1`。Prop 4(c) の
「Ḡ=G/𝒩(G) が (A1) を満たす」等は自明に潰れ、**実質内容は `C_D(Q)=1`** のみ
(`centralizer_Q_inf_D_eq_bot`)。book の一般 quotient 構成 (Ch.II–IV の induction で
非faithful な部分群作用に適用) は、その時点で G/𝒩 に Hypothesis を instantiate して回収する
(4(c) docstring 参照)。⇒ **一般化債務ではない** (一般版は (A2) を Hypothesis から外す必要が
あり、それは Ch.III induction 到達時の設計判断)。

## 次の frontier (文書順)

0. ✅ **Lemma (a) 完了** — `InvertedProduct.lean` (一般群補題、M,t,X 抽象、hyp 非依存)。
   `invertedProdEquiv : Y × Z ≃ X` (explicit-inverse: `x↦(xz⁻¹,z)`, `z=w^{(|X|+1)/2}`,
   `w=(t x⁻¹ t)x`) + `card_eq_card_centralizer_mul_ncard_invertedBy : |X|=|Y||Z|`。
   奇数位数 squaring 素材 (`sq_pow_half`/`pow_half_sq`/`pow_card_eq_one_of_mem`) も汎用で内包。
   - **⚠ Lemma (b) `⟨Z⟩ ⊴ X` は未** (Prop 5 に不要ゆえ後回し)。証明: `Y` は `Z` を正規化
     (`y∈Y,z∈Z ⇒ yzy⁻¹∈Z`: `t(yzy⁻¹)t=(tyt)(tzt)(ty⁻¹t)=y z⁻¹ y⁻¹=(yzy⁻¹)⁻¹`)、
     `Z⊆⟨Z⟩`、`X=YZ` (Lemma a) より `X` が `⟨Z⟩=closure(invertedBy X t)` を正規化。
1. ✅ **Prop 5 (p.101) 完了** — `V=C_D(s)` + `W=C_D(H∩I)`。
   - `DistinguishedInvolution.lean`: `distinguishedInvolution`, `structureConjugator`,
     `structure_equation`, `eq_distinguishedPair_of_structure` (一意性)。
   - `CentralizerStructure.lean`: `V_eq_centralizer_distinguishedInvolution` (counting は
     `orbit_distinguishedInvolution_eq` + Lemma(a) `|D|=|V||K|` + Prop 3 + orbit-stab) /
     `W_eq_centralizer_involutions_H` (`W = D ⊓ centralizer (H∩I involutions set)`;
     ⊇ は `conj_mem_KSet_of_mem_V` (V normalizes K) + `injOn_conj_KSet` で `wkw⁻¹=k`)。
   - `InvolutionClass.lean`: Prop 3 injectivity を `injOn_conj_KSet` として公開 lemma 化。
2. ✅ **Prop 6 (p.101–102) 完了** — 新 leaf `FixedPointCentralizer.lean`
   (`Ω_X = MulAction.fixedPoints X Ω`, X : Subgroup G, hXD : X ≤ D):
   (a) `cQRegularEquiv` (C_Q(X) ≃ Ω_X−{basept}) + `ncard_fixedPoints`
       (|Ω_X|=|C_Q(X)|+1) + `cQ_mul_cD_eq_cH`/`card_cH_eq` (C_H(X)=C_Q(X)⋊C_D(X)) +
       `exists_mem_centralizer_smul_pair` (二重可移、elementwise 形)。対称側は
       **`Hypothesis.symm`** (Basic.lean: basept↔t•basept 入替、H'=H^t/Q'=Q^t/D'=D) 経由。
   (b) `even_card_cQ`: pair-swap 元 c (basept↔t•basept) は偶数位数 → involution
       u=c^k ∈ C_G(X) → 単一共役類+C_G(u₀)≤H で固定点 ω'∈Ω_X → 可移性で C_H(X) へ共役。
   (c) `exists_conj_mem_D_map_le_V`: C_Q(X) の involution u=s^k (Prop 3) → X^k ≤ V。
   - bundled `IsMultiplyPretransitive` (induced action) は使用点 Ch.I §3 で導出予定。
   - Basic に汎用 helper: `even_card_of_sq_eq_one_mem` / `exists_sq_eq_one_of_even_card`。
3. ✅ **Lemma (b) `⟨Z⟩◁X` 完了** (InvertedProduct.lean): `conj_mem_of_mem_centralizer`
   (Y normalizes Z) + `closure_invertedBy_le` + `conj_mem_closure_invertedBy` /
   `closure_invertedBy_subgroupOf_normal` (X=YZ 分解 + MonoidHom.map_closure)。
   **→ Ch.I §1 (pp.100–102) 全結果 formalized。**
4. ✅ **§2 Prop 1 完了** — 新 leaf `QStructure.lean`:
   (a) `Q_inf_centralizer_eq_bot_of_mem_KSet` (C_Q(x)=1; Prop 6(b)+Prop 3 injectivity
       → 固定点 pair → C_H(x)≤D)。
   (b) `isNilpotent_Q`: ⟨x⟩ 共役作用 = IsFrobeniusAction → **Thompson = Isaacs Thm 6.24
       (repo 済 `isNilpotent_of_isFrobeniusAction`)**。|K|>1 は (A3) 四元群経由
       (`exists_ne_one_mem_KSet`)。
   (c) `exists_involution_mem_center_Q` (nilpotent Sylow-2 normal + Isaacs Ch04
       `exists_mem_center_of_normal_ne_bot_of_isNilpotent` + Cauchy) →
       `involutions_H_subset_centralizer_Q` (H∩I ⊆ Z(Q)) → **`Q0 : Subgroup G`**
       ({x∈H | x²=1}) + elementary abelian API (`commute_of_mem_Q0` 等)。
5. **§2 Prop 2 進行中** — K は D の cyclic normal 部分群 (p.103)。新 leaf `KCyclic.lean`。
   - ✅ **基盤完了**: `conjQ0`/`ker_conjQ0` (核=W=C_D(H∩I))/`Dbar`=D/W/`conjQ0bar`
     faithful/`conjQ0bar_transitive` (Q₀^# 可移, §1 Prop 3)/`odd_card_Dbar`→
     `IsSolvable Dbar` (FT 本体)/`fitting_Dbar_cyclic_fpf_abelian` (**App I Prop 1 適用**)。
   - ✅ **誘導自己同型 τ**: `tauD`/`tauHom`/`tau : MulAut Dbar` (t が D̄ 上に誘導、
     W 上恒等ゆえ商へ降りる、involutive)。
   - ✅ **§1 Lemma (a) endo 形** (`InvertedProduct.map_eq_inv_of_forall_fixed_eq_one`):
     奇位数 X 上の involutive endo σ が 1 のみ固定 ⟹ σ 全反転 (τ は outer なので要)。
   - **⚠ App I Prop 1 gate = `Huppert.fitting_cyclic_fixedPointFree` は当初 axiom-clean と
     誤報告したが実は sorried** (`pGroup_cyclic_fixedPointFree` の non-cyclic case、
     `#print axioms` で `sorryAx` 確認)。→ 上流優先で gate を進めた (下記)。
   - **次**: C_D̄(τ)=V̄ → C_Ā(τ)=1 (V≤C_D(s) f.p.f.) → Ā⊆J (Lemma(a) endo) →
     Fitting で Ā=J → A=KW → |Ā|=|K| → K cyclic (§1 Lemma(b) で K◁D)。
   - **上流成果 (2026-07-18、gate 掘り下げ)**: App I Prop 1 の sorry = **Gorenstein 5.4.10
     (odd p) = BG Lemma 4.5(a)** を証明 (issue 2004 完了):
     `BG.Ch1.S04.exists_normal_isElementaryAbelian_card_prime_sq_of_not_isCyclic` +
     新 leaf `GroupTheory/NormalElementaryAbelianPrimeSq.lean` (不変部分空間補題 +
     cyclic-selfcent⟹metacyclic)。**Huppert sorry の残り** = Schur⟹Z(P) cyclic + coprime
     Z_p×Z_p 分解 = **issue 2005** (これが埋まれば App I Prop 1 gate が axiom-clean 化)。
6. §2 Cor (S abelian or Suzuki 2-group; gate: App III Def 1) → §2 Prop 3 (𝓛(F_q,A)
   同型; gate: App I Prop 2) → §3 (induction hypothesis 適用開始)。
   §3 以降は PSL(2,q)/Sz(q)/PSU(3,q) の具体構造 (mathlib 未整備) に gate される項が増える。

survey per-unit 表 = `notes/meta/three_books_full_survey_2026_07_16.md` L568–605。
