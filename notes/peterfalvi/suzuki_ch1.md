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
1. **Prop 5 (p.101)** — `V=C_D(s)` ✅ / `W=C_D(H∩I)` 未。
   - ✅ **`s`/`r` naming 完了** (`DistinguishedInvolution.lean`): `distinguishedInvolution`,
     `structureConjugator` (`existsUnique_...`.exists.choose)、`structure_equation`、
     `eq_distinguishedPair_of_structure` (一意性)。
   - ✅ **`V=C_D(s)` 完了** (`CentralizerStructure.lean`): `V_le_centralizer_distinguishedInvolution`
     (⊆) + `V_eq_centralizer_distinguishedInvolution` (=)。counting は `orbit_distinguishedInvolution_eq`
     (`sᴰ=H∩I`) + Lemma(a) `|D|=|V||K|` + Prop 3 `|K|=|H∩I|` + orbit-stab (ConjAct, stabilizer=C_D(s))。
     specialization identity `hyp.KSet = invertedBy hyp.D hyp.t` は定義的一致で Lemma(a) 直接適用。
   - **⚠ `W=C_D(H∩I)` 未 (次)**: `W:=V⊓centralizer KSet = C_V(K)` (定義)。`V=C_D(s)` より
     `W = D ⊓ centralizer {s} ⊓ centralizer KSet`。目標 `W = D ⊓ centralizer (H∩I set)`。
     - ⊆: s,K を中心化 ⇒ 各 `s^k=k⁻¹sk` を中心化 (積)。容易。
     - ⊇ (要点): `d∈D` が `H∩I` を中心化 ⇒ `d` は `s∈H∩I` を中心化 ⇒ `d∈C_D(s)=V` (V=C_D(s) 使用)
       ⇒ `V` は `K` を正規化 (`v∈V,k∈K ⇒ vkv⁻¹∈K`: `t(vkv⁻¹)t=(tvt)(tkt)(tv⁻¹t)=v k⁻¹ v⁻¹`,
       v は t と可換 tvt=v) ⇒ `dkd⁻¹∈K` かつ `s^{dkd⁻¹}=s^k` (d が s^k と s を中心化) ⇒
       **Prop 3 の `k↦s^k` 単射性**で `dkd⁻¹=k` ⇒ `d∈C_D(K)`。
     - **要 exposure**: Prop 3 injectivity は `image_conj_KSet_eq_involutions_H` 内部の `hinjK`
       (未公開)。`InvolutionClass.lean` に `injOn_conj_KSet` 等で公開 lemma 化 or 再導出が必要。
       V normalizes K も新 lemma (`vkv⁻¹∈K`) で用意。
2. **Prop 6 (p.101–102)** — `X⊆D` で `|Ω_X|≥3` の下での構造 (Prop 1(a) 型二重推移)。
3. 以降 Ch.I §2 (`Cor`: S abelian or Suzuki 2-group) → §3 (Prop 1 trichotomy, Lemmas)。
   §3 以降は PSL(2,q)/Sz(q)/PSU(3,q) の具体構造 (mathlib 未整備) に gate される項が増える。
4. **Lemma (b) `⟨Z⟩◁X` 未** (InvertedProduct.lean, Prop 5 に不要で後回し; §0 参照)。

survey per-unit 表 = `notes/meta/three_books_full_survey_2026_07_16.md` L568–605。
