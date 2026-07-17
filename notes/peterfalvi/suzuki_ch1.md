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
1. **Prop 5 (p.101)** — `V=C_D(s)` かつ `W=C_D(H∩I)`。
   - **specialization identity (重要)**: `hyp.KSet = invertedBy hyp.D hyp.t` は**定義的に一致**
     (両者 `{x | x∈D ∧ t*x*t=x⁻¹}`)、`hyp.V = hyp.D ⊓ centralizer {t}` も一致。ゆえに Lemma(a) を
     `X:=hyp.D, t:=hyp.t` で適用 → `Nat.card D = Nat.card V * KSet.ncard` (= `|D|=|V||K|`)。
     hyp 引数: `ht=t_sq(→t*t=1)`, `hodd=D_odd`, `hnorm` = `t_conj_mem_D`+`t_inv_eq` (`t*x*t∈D`)。
   - **distinguished involution `s` の naming が必要**: Prop 4(b) は `existsUnique_...` で提供。
     Prop 5 では `s` を `Classical.choose` 等で固定 (or `s`,`r` を `Hypothesis` の派生 def として
     用意) → `V⊆C_D(s)`: `v∈V` に structure eq `tst=r⁻¹tr` を conjugate し 4(b) 一意性で `s^v=s`。
   - 等号: `|K|=|s^D|` (Prop 3 `image_conj_KSet_eq_involutions_H` の `s^K=H∩I` + `|K|=|H∩I|`)
     と `|s^D|=|D:C_D(s)|` (orbit-stabilizer, mathlib `MulAction`/`Subgroup.card_eq_card_quotient…`)
     から `|D:V|=|K|=|D:C_D(s)|` → `V=C_D(s)` (V⊆C_D(s) と index 一致)。
   - `W=C_D(H∩I)`: `W=C_V(K)` (定義) = `C_D(s)∩C_D(K)` = `H∩I` を中心化する `D` の元
     (Prop 3 `k↦s^k` が `K→H∩I` 全単射、`V` normalizes `K`)。
2. **Prop 6 (p.101–102)** — `X⊆D` で `|Ω_X|≥3` の下での構造 (Prop 1(a) 型二重推移)。
3. 以降 Ch.I §2 (`Cor`: S abelian or Suzuki 2-group) → §3 (Prop 1 trichotomy, Lemmas)。
   §3 以降は PSL(2,q)/Sz(q)/PSU(3,q) の具体構造 (mathlib 未整備) に gate される項が増える。

survey per-unit 表 = `notes/meta/three_books_full_survey_2026_07_16.md` L568–605。
