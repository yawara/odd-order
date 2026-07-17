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

1. **Lemma (p.101)** — 一般群補題: `M` 有限群、`t` 位数2、`X≤M` 奇数位数で `t` 正規化、
   `Y=C_X(t)`、`Z={x∈X | x^t=x⁻¹}`。(a) `(y,z)↦yz`, `(y,z)↦zy` は `Y×Z→X` 全単射
   (∴ `|X|=|Y||Z|`); (b) `⟨Z⟩ ⊴ X`。
   - **証明戦略 (explicit-inverse 版; book の counting より Lean 向き)**: `x∈X` に対し
     `w:=(x^t)⁻¹x = t x⁻¹ t x ∈ X` は `twt=w⁻¹` を満たす (∈Z 型)。奇数位数ゆえ一意平方根
     `z:=w^{(|X|+1)/2}` (`z²=w`, `z∈Z`)、`y:=xz⁻¹∈Y` (`tyt=y` を `txt=xw⁻¹` から検算)。
     これが `Y×Z≃X` の逆写像 → 直接全単射。一意性は `z²=(x^t)⁻¹x` (x=yz なら) + 奇数位数
     squaring 単射。奇数位数 squaring の素材は既に `DistinguishedInvolution.lean` に汎用で
     ある: `sq_pow_half_orderOf` (存在), `eq_of_sq_eq_of_odd_orderOf` (一意) — import 再利用可
     (現在 `Hypothesis` namespace 内だが hyp 非依存の汎用 lemma)。
   - 配置: 一般群補題ゆえ `Suzuki/` 内の新 leaf (例 `InvertedProduct.lean`) に M,t,X 抽象で。
     mixed-type (Y=subgroup, Z=set) の bijection に注意。
2. **Prop 5 (p.101)** — `V=C_D(s)` かつ `W=C_D(H∩I)`。V⊆C_D(s) は Prop 4(b) 一意性から
   (`ts^v t=(r⁻¹)^v t r^v` ⇒ `s^v=s`)。等号は Lemma(a) `|D|=|V||K|` + Prop 3
   `|K|=|s^D|=|D:C_D(s)|` で index 一致。
3. **Prop 6 (p.101–102)** — `X⊆D` で `|Ω_X|≥3` の下での構造 (Prop 1(a) 型二重推移)。
4. 以降 Ch.I §2 (`Cor`: S abelian or Suzuki 2-group) → §3 (Prop 1 trichotomy, Lemmas)。
   §3 以降は PSL(2,q)/Sz(q)/PSU(3,q) の具体構造 (mathlib 未整備) に gate される項が増える。

survey per-unit 表 = `notes/meta/three_books_full_survey_2026_07_16.md` L568–605。
