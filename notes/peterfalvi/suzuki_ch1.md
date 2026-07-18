# Peterfalvi Part II (A Theorem of Suzuki) — Ch. I §3 frontier

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
12. 🔄 **§3 Prop 1(c) in progress** — leaves `CentralizerResidual.lean`,
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
   - **Next frontier:** use the retained standard-action coordinates to identify
     the quotient root subgroup in each PSL/Sz/PSU model, then transport its
     structure, cardinality, distinguished involution, and
     `orderOf(st) = 3/5/3` through `centralizerQQuotientEquiv`.

survey per-unit 表 = `notes/meta/three_books_full_survey_2026_07_16.md` L568–605。
