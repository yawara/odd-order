# Peterfalvi Part II (A Theorem of Suzuki) — Ch. I §3 frontier

Peterfalvi 正本ソース =
`references/peterfalvi/pdftotext/05.3_pp_100_107_General_Properties_of_G.txt` +
`references/peterfalvi/pdf/05.3_pp_100_107_General_Properties_of_G.pdf`。
Nougat `.mmd` は使わない。Coq crib は **無い** (math-comp/odd-order は Part I のみ)。
引用元の Higman 証明は `references/higman/suzuki-2-groups.pdf`、保持済み
`pdftotext` とページ画像を正本とし、Lean 本体は `OddOrder/Higman/Suzuki2Groups/**` に置く。

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
   - ✅ **Prop 1 後の standing notation `Q=S×Q₁`** — 新 leaf
     `SylowDecomposition.lean`。`Q₁` を free field にせず、`Q` の冪零性から一意な正規
     `2`-補群として実構成。任意の `S : Sylow 2 Q` について complement、characteristic、
     odd order、および multiplication による `S × Q₁ ≃* Q` を axiom-clean で証明。
5. ✅ **§2 Prop 2 完了** — K は D の cyclic normal 部分群 (p.103)。leaf `KCyclic.lean`。
   - ✅ **基盤完了**: `conjQ0`/`ker_conjQ0` (核=W=C_D(H∩I))/`Dbar`=D/W/`conjQ0bar`
     faithful/`conjQ0bar_transitive` (Q₀^# 可移, §1 Prop 3)/`odd_card_Dbar`→
     `IsSolvable Dbar` (FT 本体)/`fitting_Dbar_cyclic_fpf_abelian` (**App I Prop 1 適用**)。
   - ✅ **誘導自己同型 τ**: `tauD`/`tauHom`/`tau : MulAut Dbar` (t が D̄ 上に誘導、
     W 上恒等ゆえ商へ降りる、involutive)。
   - ✅ **§1 Lemma (a) endo 形** (`InvertedProduct.map_eq_inv_of_forall_fixed_eq_one`):
     奇位数 X 上の involutive endo σ が 1 のみ固定 ⟹ σ 全反転 (τ は outer なので要)。
   - ✅ **App I Prop 1 gate axiom-clean**:
     `Huppert.pGroup_cyclic_fixedPointFree` の irreducible non-cyclic case を、正規
     type-`(p,p)` 部分群の order-`p` fixed spaces による `P`-permuted direct
     decomposition で閉じた。従って `fitting_Dbar_cyclic_fpf_abelian` も axiom-clean。
   - ✅ **C_D̄(τ)=V̄** (`tau_mk_eq_iff_mem_V`): τ-固定コセット = V-コセット。w=(tdt)⁻¹d∈W
     は t と可換 (W≤V) ⟹ w²=1、D 奇位数 ⟹ w=1 ⟹ tdt=d ⟺ d∈V。helper
     `sq_inverted_eq_one` (a²=1⟹(ab⁻¹ab)(b⁻¹aba)=1)。axiom-clean。
   - ✅ **C_Ā(τ)=1** (`tau_fixed_fitting_eq_one`): τ-固定 Fitting 元は 1。V̄ に属す⟹s∈Q₀^#
     固定 (V≤C_D(s), Prop 5)、Ā は Q₀ 上 f.p.f. (App I gate) ⟹ 矛盾。
     App I gate closure により axiom-clean。
   - ✅ **Ā⊆J** (`fitting_subset_inverted`): τ が Ā 全元を反転。Ā characteristic ⟹ τ|_Ā は
     involutive endo で 1 のみ固定 (C_Ā(τ)=1) ⟹ Lemma(a) endo 形で全反転。
   - ✅ **J⊆Ā / Ā=J** (`inverted_mem_fitting` / `mem_fitting_iff_tau_eq_inv`):
     D̄/Ā の τ-反転元部分群を引き戻した正規部分群 B̄ を構成。τ-固定元は奇位数商で
     自明となって Ā に入り、C_Ā(τ)=1 で消える。Lemma (a) により τ は B̄ を全反転、
     よって B̄ は abelian・nilpotent、`nilpotent_normal_le_fitting` で B̄≤Ā。逆包含と
     合わせて Ā=J。axiom-clean。
   - ✅ **K⊆A / A∩V=W** (`mem_fittingPreimage_of_mem_KSet` /
     `fittingPreimage_inf_V`): A を D→D̄ の F(D̄) の full preimage として構成。K の
     元は商で τ-反転されるため Ā=J に入り、A∩V の像は Ā 内で τ-固定なので 1、従って
     A∩V=W。axiom-clean。
   - ✅ **A=KW / |Ā|=|K|** (`fittingPreimageInG_eq_KSet_mul_W` /
     `card_fitting_Dbar_eq_ncard_KSet`): A の ambient-group model に §1 Lemma (a) を適用。
     `A∩V=W` と inverted locus `=K` から A=KW を得て、full-preimage の位数公式で
     `|F(D̄)|=|K|`。axiom-clean。
   - ✅ **K=⟨k⟩ cyclic / K◁D** (`exists_KSet_generator` / `coe_K` /
     `K_isCyclic` / `K_normal`): cyclic Ā の generator の representative `d∈A` を
     A=KW で `d=kw` と分解して `k∈K` を lift。`|Ā|=|K|` と `⟨k⟩⊆K` から
     `K=⟨k⟩`。`K := closure KSet` の carrier を同定し、§1 Lemma (b) で D 内正規性。
     axiom-clean。**→ §2 Prop 2 完了。**
   - ✅ **App I gate closure (2026-07-18)**: BG Lemma 4.5(a) の正規 type-`(p,p)`
     prerequisite と Huppert の order-`p` fixed-space decomposition の双方が
     sorry-free で着地 (issue 2004 / 2040 完了)。
6. ✅ **§2 Cor 完了** — 新 leaf `SylowTwo.lean`。任意の `S : Sylow 2 Q` は
   commutative または honest な Suzuki 2-group (`sylowTwo_isMulCommutative_or_isSuzuki2Group`)。
   - App III Definition 1 を `IsPGroup 2` + 非可換 + 異なる involution 2 個 +
     cyclic `A ≤ MulAut S` の regular action として de-scaffold。faithful 性は subgroup inclusion に内蔵。
   - `Q` nilpotent ⟹ `S` normal/characteristic、`conjQByK` を `S` へ制限し `A := range φ`。
   - `s^K = H∩I` (`image_conj_KSet_eq_involutions_H`) で transporter の存在、
     `injOn_conj_KSet` で一意性。全 endpoint axiom-clean。
7. ✅ **§2 Prop 3 完了** — `SemilinearModel.lean`/`SemidirectReassociation.lean`/
   `SemilinearRealization.lean`。
   - App I Prop 2(a) から同じ有限体 `F` 上で `|F|=|Q₀|`、`F(D̄) ≃* Fˣ` を実構成。
     推移性と `sQ0 ≠ 1` で scalar map の全射性まで証明。
   - Prop 2(b) を `V̄` に適用して faithful `ν : V̄ →* RingAut F` を構成し、
     `V̄ ≃* range ν`、semilinearity、`V̄` 共役と scalar action の整合性を証明。
   - `D̄ = F(D̄) ⋊ V̄` を外部半直積へし、三重半直積を座標を保って再結合。
     `exists_semilinear_equiv` は `Q₀ ≃* F_add`、`F(D̄) ≃* Fˣ`、
     `V̄ ≃* A ≤ RingAut F` と三作用の同変性、`Q₀ ⋊ D̄ ≃* 𝓛(F,A)` を返す。
   - finite-field automorphism group の cyclicity から `V̄` cyclic。全 endpoint axiom-clean。
     `Kbar_eq_fitting` により本文の `K̄ ↔ Fˣ` と一致。**→ §2 全結果 formalized。**
8. **Section 3 Lemma 1: conditional core and PSL(2,q) target complete**.
   - `InductionHypothesis.lean` proves the target-independent group-theoretic core:
     `Q` is a 2-group and `L = primeComplementResidual 2 G = sup_g Q^g` from the concrete degree
     formula, simplicity, normality, and odd index.
   - `InductionHypothesisPSL.lean` supplies those inputs for a finite characteristic-two
     field `F` with `2 < |F|`, a concrete group isomorphism from `L` to `PSL(2,F)`, and an equivariant
     bijection from `Omega` to the standard projective line. It derives
     `|Omega| - 1 = |F| = 2^n` and transports the existing Isaacs Ch08 PSL simplicity.
   - Shared support is `GroupTheory/PrimeComplementResidual.lean`; issue 9112 is closed.
9. ✅ **Section 3 Lemma 1, concrete Sz(q) and PSU(3,q) targets complete**.
   - Shared leaf `GroupTheory/SpecificGroups/Suzuki/Field.lean` constructs the field
     of order `q = 2^(2m+1)` and the Tits twist `theta(x) = x^(2^(m+1))`.
   - The leaf proves the full Frobenius period, `theta^(-1)(x) = x^(2^m)`, and
     `theta(theta(x)) = x^2`; these are the concrete identities used by the standard
     root-group and torus formulas.
   - `GroupTheory/SpecificGroups/Suzuki/RootGroup.lean` now constructs the nonabelian
     root group `S(q,theta)` in ovoid coordinates, proves its explicit inverse, square,
     exponent-four law, central involution line, exact order `q^2`, and `2`-group property.
   - `GroupTheory/SpecificGroups/Suzuki/Ovoid.lean` proves the anisotropic norm
     `N(x,y) = x^2*theta(x) + x*y + theta(y)`, its reciprocal identity for the Weyl
     map, and constructs the infinity-plus-affine ovoid carrier of exact size `q^2 + 1`.
   - `GroupTheory/SpecificGroups/Suzuki/StandardGenerators.lean` constructs faithful
     root and torus permutation homomorphisms, the regular affine root action, the
     root-torus conjugation formula, and the norm-controlled Weyl involution.
   - `GroupTheory/SpecificGroups/Suzuki/GeneratedAction.lean` takes the closure of
     the full root and torus images together with the Weyl involution, internalizes the
     three generator families in that concrete finite permutation group, and proves its
     standard action doubly transitive via the regular affine root action and the
     infinity-origin Weyl swap.
   - `GroupTheory/SpecificGroups/Suzuki/Borel.lean` realizes the root-torus subgroup
     as a faithful semidirect product, proves unique root-times-torus normal form, shows
     that it fixes infinity, and computes its exact order `q^2 * (q - 1)`.
   - `GroupTheory/SpecificGroups/Suzuki/Bruhat.lean` derives the explicit Weyl--torus
     and nontrivial Weyl--root identities from the anisotropic norm, proves the two-cell
     decomposition `B ∪ B w B`, identifies `B` with the infinity stabilizer, and computes
     the exact group order `q^2 * (q^2 + 1) * (q - 1)`.  This construction exists
     for every `m`; the simplicity target below uses `0 < m`, so `q >= 8`.
   - Shared `GroupTheory/GroupAction/PerfectQuasiprimitive.lean` proves that a
     faithful quasiprimitive nontrivial perfect group with a solvable point stabilizer
     is simple, by mapping the stabilizer onto every nontrivial normal quotient.
   - `GroupTheory/SpecificGroups/Suzuki/Simplicity.lean` proves torus displacement
     surjectivity via a fixed-point-free automorphism, places every root, torus, and
     Weyl generator in the derived subgroup, proves the standard Borel solvable, and
     concludes `IsSimpleGroup (standardPermGroup m)` for `0 < m`.
   - `Peterfalvi/Appendices/Suzuki/InductionHypothesisSuzuki.lean` transports the
     concrete ovoid degree and simplicity across an equivariant target identification,
     then applies the target-independent core to prove that `Q` is a `2`-group and
     identify both the `2`-complement residual and the join of the conjugates of `Q`.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/Field.lean` constructs the
     canonical quadratic extension `GF(q^2)/GF(q)`, installs q-Frobenius as the
     nontrivial star involution, and proves exact fixed-field and Hermitian trace-fiber
     cardinalities `q`.  This is the common field layer for the unitary target.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/RootGroup.lean` constructs the
     Hermitian root group with its explicit coordinate multiplication, proves all group
     laws, exact order `q^3`, and `2`-group property, then constructs the infinity-plus-
     affine unital carrier of exact degree `q^3 + 1`.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/StandardGenerators.lean` constructs
     the faithful regular affine root action, the full diagonal action, and its faithful
     determinant-one torus restriction.  It proves that the `SU(3)` diagonal parameter
     `t` has root weight `star(t)^2 / t = t^(2q-1)` and computes the exact torus order.
   - Peterfalvi uses right actions and writes `F(x,y) = (x/y,1/y)`.  Lean uses
     left root translations and therefore identifies its affine coordinate with the
     inverse source coordinate.  The same leaf retains `F` as `reciprocal` and uses
     the transported Weyl map `J F J(x,y) = (x/star(y),1/y)` as
     `weylReciprocal`. It proves involutivity and both root--torus and Weyl--torus
     conjugation formulas on the concrete unital.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/GeneratedAction.lean` takes the
     honest closure of the root, determinant-one torus, and Weyl permutations inside
     the finite symmetric group.  It internalizes the three generator families with
     faithful root and torus maps and both conjugation relations.
   - Root regularity on the affine chart together with the infinity--origin Weyl swap
     proves transitivity, affine transitivity of the infinity stabilizer, and hence
     `IsMultiplyPretransitive ... 2` on the exact `q^3 + 1` carrier.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/Borel.lean` constructs the
     faithful semidirect product of the root group by the determinant-one torus.
     Evaluation at the affine origin gives injectivity and a unique root--torus
     normal form; every Borel element fixes infinity.
   - Its exact order is `q^3 * ((q^2 - 1) / gcd(q + 1, 3))`.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/BruhatCoordinates.lean`
     constructs the determinant-one Hua parameter `b / star(b)^2` and proves
     the origin, pole, and generic affine coordinate identities. This is the
     left-action transport of Peterfalvi Chapter IV §3 Proposition (4)--(5),
     not a change to the source reciprocal map.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/Bruhat.lean` proves the
     concrete Weyl--root permutation relation, the two-cell decomposition
     corresponding to Chapter I §1 Proposition 4(a), and the reverse stabilizer
     inclusion. Hence the standard Borel is exactly the infinity stabilizer.
   - The same leaf computes the exact full-group order
     `q^3 * (q^3 + 1) * ((q^2 - 1) / gcd(q + 1, 3))`; all endpoints are included
     in `AxiomsCheck` and the full project build.
   - `GroupTheory/SpecificGroups/ProjectiveUnitary/Simplicity.lean` supplies
     Peterfalvi Chapter I §3 Lemma 1’s externally cited Huppert II.10.13 input.
     For the exact source range `q = 2^n > 2` (`1 < n`), it proves root, Weyl,
     and determinant-one torus generator membership in the derived subgroup,
     perfectness, Borel solvability, and finally
     `IsSimpleGroup (standardPermGroup n)`. The exceptional `n = 1` group of
     order 72 is correctly excluded.
   - `Peterfalvi/Appendices/Suzuki/InductionHypothesisPSU.lean` transports the
     unital degree for `0 < n` and simplicity for the exact source range
     `q = 2^n > 2` (`1 < n`) across the target identifications. Its combined
     endpoint proves that `Q` is a `2`-group and identifies `L` with both the
     `2`-complement residual and the join of the conjugates of `Q`.
   - Together with the PSL and Suzuki target leaves, all three target cases in
     Peterfalvi Chapter I §3 Lemma 1 are now formalized without opaque target
     hypotheses. **→ §3 Lemma 1 complete.**
10. ✅ **§3 Prop 1(a) complete** — new leaf `CentralizerInduction.lean`.
   - For `X ≤ V`, it equips `L = C_G(X)` with the induced action on
     `Ω_X = fixedPoints X Ω` and proves the three source points `H`, `H^t`,
     and `H^{ts}` are distinct. Peterfalvi uses right actions; the Lean
     left-action representative of `H^{ts}` is `s • (t • H)`.
   - `HypothesisA1` contains exactly all fields of source hypothesis (A1),
     including the stabilizer, `Q D = H`, parity, and the distinguished
     involution data. It deliberately excludes faithfulness (A2) and the
     2-rank condition (A3), because the restricted centralizer action need not
     be faithful.
   - `centralizerHypothesisA1` constructs this honest carrier from §1 Prop 6;
     `normalCore_cH_eq_restrictedAction_ker` identifies the intrinsic core in
     `L`, and `normalCore_cH_eq_centralizer_cQ` proves the exact source formula
     `𝒩(L) = C_{L ∩ D}(L ∩ Q)`.
   - `normalCore_cH_le_cV` proves `𝒩(L) ≤ L ∩ V` using §1 Prop 5
     (`V = C_D(s)`) and `s ∈ L ∩ Q`. The source assumption `1 ≠ X` is not
     needed for part (a); it remains available for the strict-order induction
     in the later clauses.
11. ✅ **§3 Prop 1(b) complete** — new leaf `CentralizerNormalizer.lean`.
   - Double transitivity on `Ω_X` gives the source first factorization
     `N_G(X) = C_G(X) N_D(X)`.  Peterfalvi writes right actions; with the
     Lean left action the correcting centralizer element is multiplied on
     the left.
   - Applying §1 `invertedProdEquiv` to an inverse element of
     `N_D(X)` preserves the source order and proves
     `N_D(X) = N_K(X) N_V(X)`, where every normalizer is the ambient
     intersection with `N_G(X)`.
   - `V_inf_K_eq_bot` follows because `t` centralizes `V`, inverts
     `K`, and `D` has odd order.  Since `K ◁ D`, the commutator of
     `N_K(X)` with `X` lies in `X ∩ K ≤ V ∩ K = 1`; hence
     `N_K(X) ≤ C_G(X)` and the final endpoint is
     `N_G(X) = C_G(X) N_V(X)`.
   - The source assumption `1 ≠ X` is not needed for part (b).
12. ✅ **§3 Prop 1(c) complete** — leaves `CentralizerResidual.lean`,
    `CentralizerQuotient.lean`, and `CentralizerInductionBridge.lean`.
   - ✅ The standing factor `Q₁` is the actual normal `2`-complement from
     `SylowDecomposition.lean`, not an added hypothesis.
   - ✅ `Q1_inf_centralizer_eq_bot_of_isPGroup`: if `C_Q(X)` is a
     `2`-group, its intersection with the odd-order `Q₁` is trivial,
     giving the source clause `C_{Q₁}(X)=1`.
   - ✅ `normalCore_subgroupOf_normalClosure_cQ_eq_center` proves the
     classification-independent source identity
     `𝒩(L) ∩ ⟨C_Q(X)^L⟩ = Z(⟨C_Q(X)^L⟩)`. The reverse inclusion uses
     the opposite root group `C_{Q^t}(X)` (the source OCR prints `Q′`),
     exactly as in SS1 Proposition 1(b).
   - ✅ `card_centralizer_eq` and `exists_sylow_two_eq_cQ_of_isPGroup`
     formalize the source's A1 step: the structure equation makes `C_Q(X)`
     a Sylow `2`-subgroup as soon as Lemma 1 supplies its `IsPGroup` proof.
   - ✅ `centralizerResidualQuotientEquiv` then combines that constructed
     witness, the center equality, and the shared surjective-map API to give
     `O^{2′}(L) / Z(O^{2′}(L)) ≃* O^{2′}(L / 𝒩(L))`.
   - ✅ `CentralizerQuotient.lean` constructs the actual action of
     `L/𝒩(L)` on `Ω_X`.  The exact action kernel gives faithfulness (A2);
     the images of `C_H(X)`, `C_Q(X)`, `C_D(X)`, and `t` satisfy every A1
     field; and `𝒩(L) ≤ C_D(X)` with odd order preserves an elementary
     abelian four-subgroup (A3).  Thus `centralizerQuotientHypothesis`
     returns the complete honest `Hypothesis` required by induction.
   - ✅ `card_centralizerActionQuotient_lt` proves from `X ≠ 1` that
     `|C_G(X)/𝒩(C_G(X))| < |G|`: otherwise `X ≤ Z(G)`, and normality plus
     faithfulness would force `X ≤ core_G(H) = 1`.
   - ✅ `TheoremAConclusion` records exactly the source conclusion of Suzuki's
     Theorem A: a normal subgroup of odd index and one of the three concrete
     standard actions.  The carrier retains the equivariant PSL/Sz/PSU
     coordinates needed later, but does not posit simplicity or the
     degree-minus-one calculation; `Q_and_residual` derives those through the
     existing target endpoints.
   - ✅ `centralizerQQuotientEquiv` proves the source identification
     `C_Q(X) ≃ Q̄` from `𝒩(L) ≤ C_D(X)` and `C_Q(X) ∩ C_D(X) = 1`.
     `centralizer_cQ_isPGroup_of_induction` applies the exact induction
     hypothesis to the strictly smaller quotient and transports Lemma 1 back,
     closing the missing `IsPGroup 2 C_Q(X)` input.
   - ✅ `CentralizerPSLRoot.lean`, `CentralizerSuzukiRoot.lean`, and
     `CentralizerPSURoot.lean` identify `C_Q(X)` with each concrete root group
     and transport the exact field/cardinality data.  The Suzuki branch also
     constructs Appendix III Definition 2 type-A data with the target parameter.
   - ✅ `CentralizerPSLDistinguished.lean`,
     `CentralizerSuzukiDistinguished.lean`, and
     `CentralizerPSUDistinguished.lean` retain the ambient Sylow pair, normalize
     it to the standard root/Weyl pair, and prove `orderOf(st) = 3/5/3`.
   - ✅ `CentralizerTrichotomy.lean` assembles the common residual conclusions
     and the exact matching PSL/Sz/PSU branch.  The PSU conclusion is precisely
     a Suzuki `2`-group of order `ℓ^3`; it does not assert the later type-B
     conclusion.  Target build, Suzuki hub, `OddOrder.AxiomsCheck`, and full
     `lake build OddOrder` all pass with only the three allowed axioms.
13. ✅ **§3 Proposition 2** (pp. 106–107) is formalized in
    `InductionNonSimple.lean`.
    - The proof constructs the source subgroup `L = ⟨I⟩` as a proper normal
      subgroup and follows the literal factorization `k = t(tk)`.
    - The map `x ↦ [x,k]` is injective from `C_Q(k) = 1`, hence bijective on
      finite `Q`, proving `Q ≤ L` without a posited carrier.
    - The action and (A1)--(A3) are restricted honestly to `L`; double
      transitivity gives `G = LD` and `[G : L]` odd.
    - The induction result in `L` is lifted to `G`; the implicit final source
      step is made explicit by proving its normal odd-index subgroup contains
      every involution and therefore equals `L`.
    - The leaf build, Suzuki hub, `OddOrder.AxiomsCheck`, and full
      `lake build OddOrder` pass with only the three allowed axioms.
14. ✅ **§3 Lemma 2** (p. 107) is formalized in `ConjugacyInV.lean`.
    - The statement retains the source's full generality: `X` and `Y` are
      arbitrary subsets of `V`, not subgroups.
    - `K` and `V` are constructed as honest complements in `D`; the resulting
      semidirect-product projection `dToV : D →* V` is proved to fix `V`.
    - For an ambient conjugator `g`, Proposition 1(a) applied to `closure Y`
      supplies a centralizing correction.  Under Lean's left action convention
      the source element written `gh` becomes `h * g`, which lies in `D`.
    - Applying `dToV` pointwise to the corrected conjugation equality produces
      the required conjugator in `V` without a free carrier or extra axiom.
    - The leaf, Suzuki hub, `OddOrder.AxiomsCheck`, and full
      `lake build OddOrder` pass with only the three allowed axioms.
15. ✅ **§3 Lemma 3** (p. 107) is formalized in `StronglyReal.lean`.
    - `IsStronglyReal x` is the source definition: `x` is a product of two
      nonidentity involutions.
    - Distinctness of their fixed points is proved from SS2 Proposition 1(c),
      and double transitivity together with the `K`-orbit on involutions in
      `H` supplies the source's transitivity on triples `(H₁,H₂,v)`.
    - The resulting conjugator sends `x` to `u * t` with an honestly proved
      `u ∈ Q₀#`; no normal-form carrier or conjugacy hypothesis is posited.
    - If `C_G(x)` had even order, its nontrivial involution lies in
      `N_G(⟨x⟩)`.  The two source cases `y ∈ H` and `y ∉ H` use the existing
      odd-dihedral conjugacy theorem inside that normalizer and normality of
      `C_G(⟨x⟩)` to contradict `x ^ 2 ≠ 1`.
16. ✅ **§3 Lemma 4** (p. 107) is formalized in exactly two leaves,
    `OrderThreePSL.lean` and `OrderThreePSLInduction.lean`.
    - `OrderThreePSL.lean` derives the braid relation `tst = sts` from
      `orderOf (s * t) = 3`, proves closure of the two Bruhat cells, and
      identifies the carrier of `⟨Q₀,K,t⟩` with
      `Q₀K ∪ Q₀KtQ₀`.
    - The printed inclusion `tQ₀t ⊂ Q₀KtQ₀` is missing a sharp: it is false
      at `1 ∈ Q₀`. The formalization proves the source calculation for
      `tQ₀#t`, sends the unit to the small cell, and thereby obtains the
      correct unit-inclusive two-cell inclusion without asserting the false
      literal statement.
    - `OrderThreePSLInduction.lean` uses the orbit of the generated subgroup to
      construct the exact (A1)--(A3) hypothesis. Its `Q₀` action is regular
      away from the base point, hence the action is doubly transitive. A
      kernel element lies in `K`, while fixing the distinguished-involution
      orbit point makes it centralize `s ∈ Q₀`; the theorem
      `Q ∩ C_G(k) = 1` for nontrivial `k ∈ K` then kills the kernel. Thus
      faithfulness is proved rather than assumed.
    - `V ≠ 1` makes the generated subgroup proper. Theorem A induction is
      applied to that concrete subgroup and promoted to the whole generated
      subgroup. The Suzuki and PSU branches contradict commutativity of
      `Q₀`, leaving an existential finite characteristic-two field `F` with
      `|F| = |Q₀|` and `⟨Q₀,K,t⟩ ≃ PSL(2,F)`.
    - Independent comparison with the source proof confirms the braid,
      two-cell, properness, induced-action, induction, and classification
      steps, with the missing sharp as the only textual correction. After the
      single pre-commit `main` synchronization, `lake build OddOrder` exits 0
      over 4453 jobs: `OrderThreePSL`, `OrderThreePSLInduction`, the Suzuki
      hub, `OddOrder.AxiomsCheck`, and `OddOrder` all build, and the axiom
      checks pass.
    - **Higman source frontier (issue 2048):** Lemmas 4--11 と Lemma 12 冒頭 reduction は完了。
      Lemma 10 は原文冒頭の power-map gcd 二分法を `higmanPowerMapGcd` として保持し、
      full endpoint は trace 式を underlying `𝔽₂`-空間上の twisted quadratic map とみなして
      Chevalley--Warning を適用した。公開 endpoint `higmanLemmaTen` は proper odd-degree
      finite field extension、任意の `r : ℤ`, `ε` に対し、負の Frobenius 反復も含めて
      非零 `α` と `Tr(α · Frob^r(α) · ε) = 0` を exact に結論する。
      source-neutral な次元論は `OddOrder/Algebra/ChevalleyWarning.lean`、Higman 固有の
      算術・特殊化は `HigmanFiniteFieldTrace.lean` に分離した。Lemma 11 は元 actor
      `Y` と §6 の prime-support 仮定を保った `higmanLemmaEleven` で、actual Singer
      basis、anchored trace、proper-extension 排除を接続し、honest な `IsTypeA P`
      を証明する。複数 involution は明示仮定から第二層次数 `n ≥ 2` を導き、
      type-A automorphism の奇数位数は degree-one 後の primitive shift から導出する。
      Lemma 12 は `HasXiLengthThree` を actual normal actor-invariant poset 上に置き、
      `frattini_isElementaryAbelian_of_xiLengthThree` で `Φ(P)` の
      elementary-abelian reduction を閉じた。さらに `Φ(P)` を三段組成列の第一項と
      同定し、`P / Φ(P)` の induced actor を ξ-length `2` に落とした。Maschke で得た
      complementary invariant summands の preimage `X, Y` は normal / invariant で、
      `X ∩ Y = Φ(P)`, `X ⊔ Y = P`; 両 restricted actor range も ξ-length `2` である。
      `LengthTwoModels.lean` は可換 branch `A(n,1) = C₄ⁿ` も含む inclusive な
      `XiLengthTwoTypeAData` を構成した。非可換 factor は Lemma 11、可換 factor は
      homocyclic exponent-four 分類、actual `A/A² ≃ A²` square equivalence、
      inverse Frobenius finite-field coordinates から honest model を得る。したがって
      各 proper invariant preimage は可換性の分岐を残さず `A(n,φ)` と同定済みである。
      `TypeAModel` の involution を有限体の非零元と同定して
      `|Inv(A(n,φ))| = 2^n - 1` を証明した。両 preimage は ambient の全 involution
      を含むため、その個数から二つの parameter が一致し、複数 involution から
      共通値 `n ≥ 2` も従う。この source step は
      `XiLengthThreeTypeAFactorData` にまとめた。等しいのは parameter `n` であり、
      原典どおり二つの automorphism `θ, φ` の一致は主張しない。次の source frontier は
      `MixedCommutators.lean` へ進んだ。各 actual `A(n,θ)` model 内の canonical な
      非自明 involution とその平方根を構成し、actor transitivity によって任意の ambient
      involution の平方根を各 invariant factor 内に輸送する。これを左右因子へ適用し、
      `X ∩ Y = Φ(P)` と elementary-abelian `Φ(P)` を使って、Higman p. 90 の
      nonzero mixed-commutator step を actual witness `⁅x,y⁆ ≠ 1` として閉じた。
      続く `AmbientCentralExtension.lean` では、非自明 actor-invariant derived subgroup が
      全 involution を含むことから `[P,P] = Φ(P)` を証明し、同じ involution argument で
      `Φ(P) ≤ Z(P)` を得た。従って `γ₂(P)=Φ(P)`, `γ₃(P)=1` であり、
      ambient squares の生成部分群も `Agemo P 2 1 = Φ(P)` と同定した。
      elementary-abelian kernel の square subgroupも消えるため、二つの actual
      lower-central layers は `L₀ = P/Φ(P)`, `L₁ = Φ(P)` であり、
      `lowerCentralLayerKernel P 1 = ⊥` まで同定済みである。
      同 leaf で各 inclusive type-A model の concrete quadratic extension 全体を
      factor へ輸送し、short exact sequence の quotient projection の核を
      `(Φ(P)).subgroupOf S` と同定した。実際の左右 factor はともに `Φ(P)` を含むため、
      両 kernel field を同じ ambient `Φ(P)` へ移す group equivalence と、そこから得る
      左右 kernel 間 transition も構成済みである。これは honest な additive/group-level
      共通中心座標だが、field multiplication や actor action との整合性はまだ主張しない。
      これを任意な field transition へ昇格するのではなく、原典 p. 89 の順序どおり
      ambient `Φ(P)` の実際の restricted actor representation に Singer theorem を直接
      適用した。共通 generator `c`、primitive scalar `ν`、`Φ(P) ≃ₗ GF(2,n)`、
      Frobenius eigenbasis を一括して構成し、複数 involution から `n ≥ 2`、左右
      type-A factor の既存 parameter との一致も証明した。
      また p. 89 の基底調整を支える twisted norm `u ↦ u·θ(u)` が、有限体上で
      `orderOf θ` が odd なら全単射であることを証明した。従って可換 branch
      `θ = 1` も含め、prescribed common kernel basis の任意の非零 scaling を
      quotient basis 側で吸収できる。
      anchored-trace から得る kernel coordinate が Frobenius shift される場合も、その
      shift を quotient coordinate の counter-shift に移して prescribed kernel coordinate
      自体を固定する normal-form 補題を証明した。さらに square map の実際の
      actor-equivariance から、固定した kernel eigenvalue と quotient eigenvalue が
      `ν = λ·θ(λ)` を満たすことを直接導いた。
      既存 normalization chain が shift を隠さないよう、`PairGap` の正規化については
      第2層 coordinate が original coordinate の何乗 Frobenius shift かを exact equality
      付きで返す strong sibling theorem を追加し、従来 API はその projection とした。
      `ProperExtension` の anchored-trace construction 内で加わる第2の shift も exact
      equality 付き strong sibling で公開し、従来 API は projection とした。さらに
      二つの shift を一つの Frobenius automorphism に合成し、type-A Frobenius power と
      可換することも証明した。relative degree 1 の trace formula は quotient coordinate
      だけを kernel field 側へ移して prescribed kernel coordinate を固定した normal form
      に変換でき、残る nonzero coefficient も twisted norm の全射性により quotient
      coordinate の rescaling だけで 1 にできる。これら二段階は
      `PrescribedFactorCoordinates.lean` の
      `exists_typeAQuotientCoordinates_of_prescribedKernel` に束ね、quotient actor
      compatibility と `ν = λ·θ(λ)` も同時に保持する公開 API とした。
      Lemma 11 の finite-field model も、内部で任意の generator を選び直す形に加えて
      caller-prescribed generator を受け取る版を証明した。同じ ambient generator は
      invariant factor への restricted action の faithful range でも generator のまま
      なので、左右 factor と共通 centre で `c` を一貫して固定できる。
      noncommutative factor についてはさらに `Φ(S)=Φ(P).subgroupOf S` を actual
      involution subgroup から証明し、第2 lower-central layer から ambient `Φ(P)` への
      canonical な `ZMod 2` 線形同値を構成した。この同値は factor の restricted action
      と ambient Frattini action を intertwine する。従ってこの branch では共通 Singer
      座標を factor kernel へ作用同変に渡せる。これを caller-prescribed generator 版
      Lemma 11 の tracked field endpointへ接続し、二つの Frobenius shiftを quotient 側で
      戻した後に係数を 1 へ吸収した。公開定理
      `exists_noncommutativeFactorCoordinates_of_ambientFrattiniSinger` は、実際の invariant
      factor `S` に対し ambient の同じ `c`, `ePhi`, `ν` を受け取り、kernel coordinate を
      `factorLayerOneLinearEquivAmbientFrattini.trans ePhi` そのものに固定したまま quotient
      coordinate、actor compatibility、係数 1 の square normal form、
      `ν = λ·θ(λ)` を返す。commutative `A(n,1)` branch でも、
      square subgroup を ambient `Φ(P)` と identity-on-values で同一視し、共通 Singer
      座標を kernel へ移した。商座標は canonical square equivalence と inverse Frobenius
      から従属的に構成され、kernel eigenvalue `ν` に対する quotient eigenvalue が
      `Frob⁻¹(ν)` であることまで actor-equivariantly 証明した。
      さらに上記の noncommuting mixed-factor witness を actual ambient
      `lowerCentralCommutatorBilinear` の非零値へ接続し、左右 factor に属する代表元の
      provenance も保持した。したがって原典 p. 90 の固有値比較へ入る非零 pairing は
      coordinate-free な形ですでに確立している。
      原典 p. 81 の B/C/D 定義表と pp. 90--92 の case proof も再監査し、p. 91 の
      type-C square formula は mixed term の係数 `ε` が脱落した誤植であることを、
      p. 81 の表と直前の commutator formula から確認した。抽出画像は
      `references/higman/pages/suzuki-2-groups-p081.png` および p090--p092 に保持した。
      同じ ambient Singer datum を二つの非可換 factor に一度ずつ適用する lossless
      bundle `NoncommutativeFactorCoordinateData` と paired endpoint も構成した。さらに
      commutative `A(n,1)` branch を `CommutativeFactorCoordinateData` に束ね、branch 固有の
      Agemo quotient / lower-central quotient を保った tagged bundle
      `FactorCoordinateData` を構成した。`exists_factorCoordinates_of_ambientFrattiniSinger`
      は一因子の両 branch を、`exists_factorPairCoordinates_of_xiLengthThree` は左右の
      全四組合せを、同じ `c`, `ePhi`, `ν` 上で返す。最後に
      `exists_complementaryFactorCoordinates_of_xiLengthThree` が actual complementary
      `XiLengthThreeTypeAFactorData` と左右の tagged coordinates を同梱するので、
      `left ⊓ right = Φ(P)`、`left ⊔ right = P`、および
      `ν = λ·θ(λ) = μ·φ(μ)` が同じ endpoint に揃った。
      さらに新 leaf `HigmanLemmaTwelve/MixedEigenweights.lean` で、この左右座標を
      共通 ambient `F ⊗ (P/Φ(P))` 内の Frobenius eigenvector 族に変換し、原典 p. 90 の
      固有値制約 `λ^(2^i) μ^(2^j) = ν^(2^k)` を導いた
      (`exists_mixedFrobeniusWeightEquation_of_xiLengthThree`, axiom-clean)。
      両 factor branch (可換 = Agemo 商 / 非可換 = lower-central layer) は
      actor-equivariant な inclusion `quotientToAmbientLayerZero` で `P/Φ(P)` に落とし、
      非零 mixed bracket (`exists_mixed_lowerCentralCommutatorBilinear_ne_zero`) を
      base change して weight equation を読み取る。中心 `Φ(P)` は
      `ambientCenterCoordinate` で Singer 座標に同定し、固有値 `ν^(2^k)` を得る。
      shared な線形代数核 (等変双線形写像の weight 一致) は
      `OddOrder/GroupTheory/RepresentationTheory/BilinearEigenweight.lean` に置き、
      Lemma 11 の private 版 `eigenvalue_eq_of_basis_repr_ne_zero` を dedup した (issue 9317)。
      次の source frontier は、`θ = 1` / `φ = 1` / 両方非自明の分岐から原典
      pp. 90--92 の type B/C/D case split を実行し、`B(n,θ,ε)` / `C(n,ε)` / `D(n,θ,ε)`
      を確定することである。
    - **Peterfalvi frontier:** §3 Lemma 5 (p. 107) の cyclicity / `|W| ∣ q+1` /
      type-B 結論は、Higman Lemmas 8--12 と actual two-summand split の完成後に
      接続する。

survey per-unit 表 = `notes/meta/three_books_full_survey_2026_07_16.md` L568–605。

## 2026-07-21 lane b: Lemma 12 B/C/D case split の frontier 設計 (Unit A 完了後)

**Unit A 完了** (`3866a67da`): 型 C/D の quadratic-extension モデル + honest carrier
(`OddOrder/Higman/Suzuki2Groups/HigmanTypesCD.lean`)。原典 p.81 定義表の C/D 行を実体化。
`typeCQuadraticMap θ ε = α·θ(α) + ε·(α^{1/2}·(2θ)(β)) + β²` (2θ²=1)、
`typeDQuadraticMap θ ε = α·θ(α) + ε·(θ³(α)·θ(β)) + β·θ²(β)` (θ⁵=1,θ≠1)。
`TypeCData`/`TypeDData`/`IsTypeC`/`IsTypeD` + `ofExtension` (kernel=F, quotient=F×F の
GroupExtension から carrier を組む) + `map_sq`/`quadraticMap_anisotropic` 等の標準 API。
4 型すべて原典 ζ と一致検算済 (case 1: B(n,1,ε), case 2: B(n,θ,ε), case 3: C(n,ε), case 4: D(n,θ,ε))。

**残 gap (Explore agent 2026-07-21 の inventory)**:
1. **F×F 座標** `Additive(lowerCentralLayer P 0) ≃ₗ[ZMod 2] F × F` — 未構築。現状は
   `quotientToAmbientLayerZero` で各 factor を別々に L₀ へ落とす map + span 被覆のみ。
2. **P の F×F 上 GroupExtension** — 未構築。`TypeC/DData.ofExtension` が要求する形。
   道具 = `GroupExtension.ofNormalSubgroupCoordinates Φ(P) (left:Mult F ≃* Φ(P)) (right:P/Φ ≃* Mult(F×F))`。
3. **組立て済 square 恒等式** `q_P(α,β)=q_X(α)+q_Y(β)+mixed` — 部品 `lowerCentralSquareMapAdditive_add`
   (sq(u+v)=sq(u)+sq(v)+`lowerCentralCommutatorBilinear`) + factor の `square_normal` (noncomm β·θ(β)/comm β²) は存在。
4. `TypeBData.ofExtension` — C/D にはあるが B には無い (case 1/2 用に追加要)。
5. **case 4 の 4項算術** `2^{a₁}+…+2^{a₄}≡2^{b₁}+…+2^{b₄} (mod 2ⁿ-1)` — 未。3項=2項
   (`three_distinct_frobeniusWeight_not_modEq_pairWeight` @ HigmanLowerCentralSpectrum) は完備、
   4項は同じ `Finset.geomSum_injective` スタイルで新規。

**Unit B (次) = F×F 座標 + GroupExtension**。設計 = **群レベル surjective+injective ルート**
(finrank 回避): 各 factor から `factorInclusion : F →ₗ[ZMod 2] Additive L₀`
(= `quotientToAmbientLayerZeroLinear f hK0 hf ∘ eQuot.symm`) を作り、
`combined = coprod fI_left fI_right : F×F →ₗ Additive L₀` を
- **surjective**: x∈left⊔right を `Subgroup.mul_normal` で x=a·b 分解 → layerZeroClass 加法性 →
  range(fI_left)+range(fI_right)。`sup_eq_top` 使用。
- **injective**: `fI_left a = fI_right b` → 共通値 w∈mk(left)⊓mk(right)、Φ≤left,right から
  `mk(left)⊓mk(right)=⊥` (group argument、`inf_eq_frattini` 使用) → w=0 → a=b=0 (fI injective)。
- fI 単射は各 branch の exactness `f g∈Φ(P)→g∈N` から (comm: `data.hN`, noncomm: `data.hterm`+`hSq`)。
branch dispatch は FactorCoordinateData の comm/noncomm を `exists_factorFamily_of_*` と同様に処理。
`LinearEquiv.ofBijective` → Multiplicative 変換 → `right : P/Φ ≃* Mult(F×F)`。
kernel 側 `left : Mult F ≃* Φ(P)` は `exists_ambientFrattiniSingerCoordinates`(:424) の ePhi から。

**Unit C 以降**: 各 case の固有値算術で mixed 項を確定 → typeB/C/D quadratic map に一致 → ofExtension。
case 3 の 3項=2項算術は既存、case 4 の 4項算術は Unit で新規。

### 2026-07-21 lane b: Unit B Stage 1+2 完了 (F×F 加法座標)

**完了** (`c8ca0a851`): `HigmanLemmaTwelve/AmbientProductCoordinate.lean` に
`ambientProductEquiv : F × F ≃ₗ[ZMod 2] Additive (lowerCentralLayer P 0)` を構築
(surjective = `mul_normal` 分解、injective = ⊓=Φ group argument + fI 単射)。sorry 0。
- 罠: `open OddOrder.RepresentationTheory` 等が **`GL` を notation 予約**するので型変数
  `GL`/`GR` は使えない (→ `HL`/`HR` に改名)。
- `Additive (lowerCentralLayer P 0)` の module instance は `local instance` 3 本
  (`CommGroup`/`Module`/`IsMulCommutative`) を自ファイルで宣言する必要がある
  (MixedEigenweights の同名は `local` で export されない)。

**次 = Stage 3: Multiplicative 版 + GroupExtension** (`ofNormalSubgroupCoordinates` へ)。
必要な bridge は特定済:
1. `right : P ⧸ frattini P ≃* Multiplicative (F × F)`:
   - `P ⧸ frattini P ≃* lowerCentralLayer P 0` を `QuotientGroup.congr (frattini P)
     (lowerCentralLayerKernel P 0) (termZeroEquivAmbient P).symm he` で作る。
     `termZeroEquivAmbient P : lowerCentralTerm P 0 ≃* P` =
     `(MulEquiv.subgroupCongr (by simp [lowerCentralTerm])).trans Subgroup.topEquiv`
     (TypeAConclusion:422 `lowerCentralTermZeroEquivAmbient` が private ⟹ de-privatize
     するか自ファイルで再定義)。`he : (frattini P).map (termZeroEquivAmbient P).symm =
     lowerCentralLayerKernel P 0` は hK0 (frattini 形) を使い TypeAConclusion:430 の
     `lowerCentralTerm_one_map_zeroEquiv_symm` と同型に証明。
   - `.trans (AddEquiv.toMultiplicativeRight ambientProductEquiv.symm.toAddEquiv)`
     (`AddEquiv.toMultiplicativeRight : (Additive G ≃+ H) → (G ≃* Multiplicative H)`,
     mathlib `Algebra/Group/Equiv/TypeTags.lean:59`)。
2. `left : Multiplicative F ≃* frattini P` (F = GaloisField 2 n):
   - Singer 座標 `ePhi : Additive (frattini P) ≃ₗ GaloisField 2 n`
     (`exists_ambientFrattiniSingerCoordinates_of_xiLengthThree`, AmbientCentralExtension:424)
     から `AddEquiv.toMultiplicativeLeft (ePhi.symm.toAddEquiv) : Multiplicative F ≃* frattini P`
     (`AddEquiv.toMultiplicativeLeft : (G ≃+ Additive H) → (Multiplicative G ≃* H)`)。
3. `GroupExtension.ofNormalSubgroupCoordinates (frattini P) left right :
    GroupExtension (Multiplicative F) P (Multiplicative (F × F))` +
   centrality (`hcentral` from `frattini P ≤ Z(P)` = `commutator_eq_frattini_and_frattini_le_center`)。

**Stage 4 (square map 分解)** = `q_P(α,β) = q_X(α)+q_Y(β)+mixed`。`lowerCentralSquareMapAdditive_add`
(sq(u+v)=sq(u)+sq(v)+`lowerCentralCommutatorBilinear`) を F×F 座標に落とし、factor の
`square_normal` (β·θ(β)/β²) と mixed bilinear を接続。これが各 case で typeB/C/D quadratic
map に一致することを示し `ofExtension` へ。

### 2026-07-21 lane b: Unit B Stage 3 完了 (ambient central extension)

**完了** (`c42459818`): `AmbientProductCoordinate.lean` に
`ambientProductExtension hK0 e ePhi : GroupExtension (Mult F) P (Mult (F×F))`
+ 支える座標 (`frattiniQuotientEquivLayerZero` / `layerZeroProductMulCoordinate` /
`frattiniSingerKernelCoordinate`) + `_inl_range`。sorry 0。TypeAConclusion の
`lowerCentralTermZeroEquivAmbient` を de-privatize して再利用。**Unit B 完了**
(F×F 加法座標 → 乗法 extension)。これで `TypeC/DData.ofExtension` の `S` 引数が揃った。

**次 = Stage 4: square map 分解 (case 依存の核心)**。`ofExtension` の
`hsq : ∀ x, x² = S.inl (ofAdd (q_BCD θ ε (S.rightHom x).toAdd))` を埋める。
`(S.rightHom x).toAdd = (α,β)` は F×F 座標、`S.inl (ofAdd v)` は Singer 座標 v の Φ(P) 元。
⟹ `hsq ⟺ (x² の ePhi-座標) = q_BCD(α,β)`。LHS = ambient square map を F×F/F 座標に
落とした `q_P(α,β)`。

- **4a (case 共有)**: `q_P(α,β) = q_X(α) + q_Y(β) + mixed(α,β)`。道具 =
  `HigmanSquareMap.lean:307 lowerCentralSquareMapAdditive_add`
  (sq(u+v)=sq(u)+sq(v)+`lowerCentralCommutatorBilinear`), u=fI_left(α), v=fI_right(β)。
  `q_X(α) = q_P(fI_left α)` を factor の `square_normal` (noncomm β·θ(β)/comm β²) に接続
  するのが要 (ambient square map の factor 制限 = factor 自身の square map)。
  mixed = `lowerCentralCommutatorBilinear (fI_left α) (fI_right β)` を ePhi-座標で読む。
- **4b–4e (各 case の mixed 項)**: eigenvalue 制約
  `λ^(2^i)μ^(2^j)=ν^(2^k)` (endpoint `exists_mixedFrobeniusWeightEquation_of_xiLengthThree`
  が供給) + `ν=λθ(λ)=μφ(μ)` から mixed を確定:
  - case 1 (θ=φ=1): i≠jで[xᵢ,yⱼ]=0、mixed=εαβ ⟹ typeB θ=1
  - case 2 (θ=φ≠1): base-change正規化、mixed=εαβ^{2^r} ⟹ typeB
  - case 3 (θ≠1,φ=1): 3項=2項算術(既存
    `three_distinct_frobeniusWeight_not_modEq_pairWeight`)⟹2r+1≡0,n奇、
    mixed=εα^{1/2}β^{2^{r+1}} ⟹ typeC
  - case 4 (両≠1非同型): **4項=4項算術 (新規、gap 5)** ⟹5r=0,s=2r、
    mixed=εα^{2^{3r}}β^{2^r} ⟹ typeD
  各 case で `q_P` を typeB/C/D quadratic map に一致させ `TypeB/C/DData.ofExtension`
  (B は ofExtension 未実装 = 追加要) → `IsTypeB ∨ IsTypeC ∨ IsTypeD`。
- **`TypeBData.ofExtension` を追加** (C/D と同型、`Types.lean`、case 1/2 用)。

**endpoint 目標**: `higmanLemmaTwelve (hP hncomm hmulti hxi hlen hprime) :
IsTypeB.{uP,0} P ∨ IsTypeC.{uP,0} P ∨ IsTypeD.{uP,0} P`。
