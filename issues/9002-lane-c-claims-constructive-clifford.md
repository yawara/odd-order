---
id: 9002
slug: lane-c-claims-constructive-clifford
title: "lane c claims 構成的 Clifford (issue 0026 subsume): typeI_induced_char_constituents 一般ケース"
created: 2026-07-02
---

# lane c claims 構成的 Clifford (issue 0026 subsume): typeI_induced_char_constituents 一般ケース

> **CLAIM (lane c=γ, hub 再裁定 issue 9001 2026-07-02)**: 構成的 Clifford correspondence
> (Ind_H^L θ の構成要素分解 = Isaacs 6.2/6.11 + Pf 1.7) を lane c が build。**coherence 非依存の
> generic char 補題**。consumer = lane b (12.14 M-side) + lane c (deep char) の両方 = shared infra。
> **他レーンは着手前に本 issue を scan、cite (再構築しない)**。issue 0026 を subsume。

## 現状 (2026-07-02 精査、issue 0026 は 2026-05-30 更新で stale)

**⚠ 重要: 一般 module-core (BLOCKER B) は既に landing 済**。issue 0026 が「残る唯一の hard blocker =
module-theoretic Clifford core (orbit transitivity)、3-5 セッション」としたものは**その後 sorry-free 化**:
- `CliffordSingleOrbit.lean:122` `restrictionConstituentsSingleOrbit_of_isIrreducible` — Clifford
  (Isaacs 6.5) 第1節「Res^G_H χ の既約構成要素は単一 G-orbit」= **sorry-free landed**。
- 同 `:175` `apply_one_eq_restrictionMultiplicity_mul_index_inertia` — degree formula
  `χ(1)=⟨Res χ,θ₀⟩·[G:I]·θ₀(1)` = landed。
- `InducedIrreducible.lean`: `card_mul_inner_self_induce_eq_card_inertia` (⟨Ind θ,Ind θ⟩=[I:H])、
  `card_conjByOrbit_eq_index_inertia`、`induce_eq_induce_iff_conj`、`inner_induce_eq_zero_of_not_conj`
  = induction-side Clifford (Frobenius 相互律 + inertia orbit) landed。
- `CliffordMultiplicityOne.lean`: `restriction_isSimpleModule` (BG 2.2(a) mult-one) + conj semilinear
  端末 landed。**全 Clifford*.lean = 0 sorry**。

**∴ hub の「構成的 producer なし」前提は stale。** 一般 Clifford 核は在庫。残 gap は **assembly**。

## 残 gap = `typeI_induced_char_constituents` (S14_MaximalI.lean:389, sorry S14:398) 一般ケース

- **Frobenius ケースは proven**: `frobenius_typeI_induced_char_constituents` (S14:465, sorry-free) —
  L が Frobenius (kernel H) なら Ind_H^L θ は既約 → singleton {χ}。docstring 明記「(12.16) witness-side
  R(χ)/(12.3)/(12.4) が実消費するのは Frobenius ケース」。witness L は Frobenius ゆえこちらで足りる。
- **一般ケース (sorried)**: 一般 type-I maximal L で χ=Ind_H^L θ (θ∈Irr H∖{1}) が **等次数・非実・
  A(L)∪{1} 台の既約構成要素の mult-one 和**。body = §8 type-F Clifford:
  - Pf (1.7) **cyclic inertia quotient I_L(θ)/H → mult-one 等次数 Ind 分解** (核心、要精査で
    landed 有無確認)。
  - (8.2.c) `I(θ)∩U⊆U₁` inertia bound (§8 specific)。
  - (1.5.a) `(Res_H φ,1_H)=0` + (1.2) → 台 A(L)∪{1}。
  - 非実 = 奇数位数 (`not_isReal_of_ne_trivial_of_odd_card'` 既存)。

## 精査確定 (2026-07-02): landed vs missing の正確な境界

**landed (在庫、cite 可)**:
- `CliffordSingleOrbit.restrictionConstituentsSingleOrbit_of_isIrreducible` (Res χ 構成要素=単一 orbit)。
- `InducedIrreducible.isIrreducibleCharacter_induce_of_inertia_eq` ([Is] 6.34: I(θ)=H → Ind θ 既約)。
- `InducedIrreducible.card_mul_inner_self_induce_eq_card_inertia` (⟨Ind θ,Ind θ⟩=[I:H])。
- `InducedIrreducible.{sum_div_normSq_induce_image_eq, apply_one_eq_sum_restrictionMultiplicity_mul,
  card_filter_induce_eq_index_inertia}` (Pf (6.2) orbit-count/degree apparatus)。
- `S14.typeF_inertia_inf_le_U1` (8.2.c: I(θ)∩U⊆U₁, proven)。`frobenius_induce_char_singleton` (Frobenius 既約)。

**missing (generic char、要 build — Isaacs §6/§11、repo 未収録)**:
- **(G1) 指標拡張**: θ∈Irr H を I=I_L(θ) に拡張 (I/H cyclic ⟹ 拡張存在、[Is] 6.28/11.22 coprime 版)。
- **(G2) Gallagher** ([Is] 6.17): θ が I 上拡張 θ̃ を持てば Irr(I|θ)={θ̃·β: β∈Irr(I/H)}、⟨Res_H(θ̃β),θ⟩=β(1)。
- **(G3) mult-free 判定**: I/H **abelian** ⟹ Ind_H^L θ は multiplicity-free、構成要素は [I:H] 個・全て
  等次数 [L:I]·θ(1) (Clifford correspondence [Is] 6.11 で Irr(I|θ)↔Irr(L|θ) + G2 で β(1)=1)。

## 進捗 (2026-07-02)

- [x] **慣性商 abelian 前提の中核**: `S14.typeF_inertia_inf_U_isMulCommutative` (generic, sorry-free,
      commit `e6f0dbd9`) — (8.2.c) + `U₁` abelian ⟹ `I(θ)∩U` abelian。
- [x] **慣性商 abelian 完成** (2026-07-02, cont.³): `S14.typeF_inertia_commutator_le` (sorry-free) —
      `Γ=HU` (`H⊔U=⊤`) + `H≤I(θ)` の Dedekind 分解 `s=h·u` (`h∈H`, `u=h⁻¹s∈I(θ)∩U`) を `Γ⧸H` に落とし、
      `I(θ)∩U` abelian ⟹ `⁅s,t⁆∈H` ⟹ **`⁅I(θ),I(θ)⁆ ≤ H`** = 「`I(θ)/H` abelian」証明書
      (`ClassFunction.inertiaQuotient`)。これが (1.7)(b) hypothesis そのもの。**残 = 生成的 char (G1)-(G3)**。
- **⚠ 訂正 (stale 検出)**: **induction-in-stages は既に landed** = `S08_CaseBCoherence2.induce_induce_subgroupOf`
      (sorry-free, `Ind^M_H(Ind^H_{K.subgroupOf H}(ψ∘e)) = Ind^M_K ψ`、`inner_compHom_of_mulEquiv` 経由)。
      下記 cont.² の「Lean 未実装 (foundational)」は誤り → cite するだけ。**再構築禁止** ([[verify-port-state-by-number-not-coq-name]])。

## Coq-confirmed 経路 + missing pieces の精密化 (2026-07-02, cont.²)

Coq PFsection1 (1.7) の経路を確認 (`constt_Inertia_bijection` + `cfIndInd`)。一般ケースの proof は:
1. **induction-in-stages** `Ind_H^L θ = Ind_I^L (Ind_H^I θ)` (Coq `cfIndInd`)。**Lean 未実装**:
   `ClassFunction.induce (H : Subgroup G)` は **ambient G へのみ**誘導 (中間 I への stage なし)。
   → `induce I (induce (H.subgroupOf I) θ') = induce H θ` を build (coset 二重和の再添字、要 subgroupOf iso)。
2. **Clifford correspondence 全単射** `Ind_I^L : Irr(I|θ) ≃ Irr(L|θ)` (Isaacs 6.11)。**Lean は degree 形のみ landed**
   (`CliffordSingleOrbit.lean:222-360`)、全単射本体は未。
3. **local mult-free at I**: I 上で θ-invariant のとき `Ind_H^I θ` の mult-free ⟹ Gallagher (Isaacs 6.17)
   + 拡張 (Isaacs 6.28/11.22)。**両方 Lean 未実装**。

**✅ 設計点 解決 (Coq PFsection1.v:437-523 精読、2026-07-02)**: **abelian で十分、cyclic 不要**。
Coq (1.7)(b) `cfInd_central_Inertia` の hypothesis は `abelian (T/H)` (T=I(θ))。結論:
- ∃ e∈ℕ (e≠0)、`∀t∈calA, e_t = e` (全構成要素が**一様 multiplicity e**)。
- `Ind_G θ = e · ∑_{j∈calB} χ_j` (distinct 構成要素の e 倍和)。
- `|calB| = [T:H]/e²`、**`∀i∈calB, χ_i(1) = [G:T]·e·θ(1)`** (全**等次数**)。
- 機構: T/H abelian → `Irr(T/H)` は linear chars → `LtoT j = (χ_j %% H)·psi1` が calA を parametrize
  (Gallagher 型)、`Res_H psi1 = e·θ` (Clifford)。

**∴ 私の `typeF_inertia_inf_U_isMulCommutative` (I(θ)/H abelian) が (1.7)(b) hypothesis そのもの、正しく on-route。**
**mult-one (e=1)** は θ が T へ**拡張**するとき: type-I では `H=L_F` が Hall で `[T:H]` coprime `|H|`
⟹ coprime 拡張 (Isaacs 6.28/8.16) で θ 拡張 → e=1。equal-degree/non-real/台と合わせ typeI_induced_char_constituents。

## やること (bottom-up、generic は shared leaf)

- [x] **Pf (1.7)/(8.2.c) 原文精読** — 設計点解決 commit `0482afa0` (abelian で十分、cyclic 不要)。
- [x] **induction-in-stages** — **既に landed** (`S08_CaseBCoherence2.induce_induce_subgroupOf`)。cite のみ。
- [x] **慣性商 abelian 完成** — `S14.typeF_inertia_commutator_le` (`⁅I(θ),I(θ)⁆ ≤ H`, sorry-free, cont.³)。
- [x] **✅ (G1) 拡張 lemma COMPLETE (2026-07-03)** — 下記 (v-a)〜(v-d) 全 landed で
      `IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq` (Isaacs 8.16) が使用可能。
      coprime Hall (H=L_F normal Hall) の下で θ を I に拡張 (Isaacs *Character
      Theory* 6.28/8.16、coprime extension via 決定行列式)。**⚠ 注意: proof は Isaacs *CT* book (=project .mmd 外)**。
      **infra build 開始 (cont.¹³-¹⁴)**: `RepresentationDeterminant.{representationDeterminant, _comp}`
      (det∘ρ : G→*ℂˣ + `det(Res χ)=Res(det χ)`, sorry-free)。
      **具体 build plan (cont.¹⁴、cyclic route = cohomology 回避)**: Isaacs 11.22 の cyclic extension
      (H⊴K, K/H cyclic, θ K-invariant ⟹ θ extends) を build → abelian I/H は composition series で iterate。
      **Schur infra 在庫**: `SchurCenterBound.schur`/`center_isScalar`/`classFunctionIntertwiner`。
      pieces: (i) invariant θ の intertwiner P (θ^g=θ ⟹ ρ_θ≅ρ_θ^g、同 char⟹同型 from completeness)、
      (ii) P^n scalar (Schur)、(iii) n-th root 調整で P'^n=ρ_θ(g^n)、(iv) `ρ_χ(g^i h)=P'^i ρ_θ(h)` 拡張 +
      既約性、(v) abelian で iterate (invariance propagation が要注意点)。**genuine multi-session、正面から engage**。
      - [x] **(i)-(iv) + char wrapper 完成 (2026-07-02 cont.¹⁵, commits `fbe9b0a4`+`e2309b54`)** —
        新 shared leaf `GroupTheory/RepresentationTheory/CyclicCharacterExtension.lean` (全 sorry-free,
        axiom-clean, full build 3898 jobs green)。**Isaacs CT 11.22 (cyclic case) end-to-end**:
        `IsIrreducibleCharacter.exists_extension_of_conjBy_eq` — H⊴K 有限, ⟨gH⟩=K/H, θ∈Irr(H),
        θ^g=θ ⟹ ∃χ∈Irr(K), Res_H χ = θ。機構: units-group 定式化 (`(Module.End ℂ V)ˣ` で全代数)、
        (i) `nonempty_equiv_conjRep_of_character_eq` (char_orthonormal)、(ii) `exists_smul_id_of_forall_mul_comm`
        (Schur commutant) + `conjugation_unit_zpow_comm`、(iii) `exists_normalized_conjugation_unit`
        (`P^t=ρ(g^t)` ∀t: g^t∈H — any-exponent 正規化が well-definedness の鍵)、(iv) `cyclicExtension`
        (`Units.coeHom`∘hom、Res=ρ on the nose、既約性は `isIrreducible_of_isIrreducible_comp` (任意 f で
        既約性 ascend、新規 generic) で無料)。派生 API: `conjRep`/`conjByMulEquiv_{one,mul}` (Inertia.lean)。
      - [x] **(v-a) 完成** (cont.¹⁶, commit `b7efdc17`): `nonempty_equiv_of_character_eq` (**強形**:
        σ 側の既約性仮定なし — dim Hom=1 via `card_inv_mul_sum_char_mul_char_eq_finrank` + Schur、
        nonzero intertwiner の ker が既約 ρ に対し ⊥、次数一致で bijective) +
        `Representation.IsIrreducible.of_equiv` (Equiv along irreducibility transport)。
        CharacterCompleteness.lean に配置。
      - [x] **(v-b) 完成** (cont.¹⁶, 同 commit): 新 shared leaf `ExtensionLinearTwist.lean`
        `exists_linearClassFunction_mul_of_restrict_eq_restrict` — Res_H χ₁ = Res_H χ₂ (irreducible)
        ⟹ ∃β:K→*ℂˣ trivial on H, χ₂ = χ₁·(linearClassFunction β)。transportRep で同一空間に正規化 →
        S(y)=ρ₂'(y)ρ₁(y)⁻¹ が Res commutant (normality) → Schur scalar → β multiplicative、trace で
        χ₂=χ₁β。sorry-free, axiom-clean。
        **(v-c)** canonical extension (prime-cyclic step): [N':N]=p, gcd(p, o(φ)φ(1))=1 ⟹ ∃! 拡張 χ with
        p∤o(χ) (かつ o(χ)=o(φ))。(v-b) 分類 + det 調整 (det(χβ)=det(χ)·β^{χ(1)}, `LinearMap.det_smul`;
        o の p-part 消去は cyclic ⟨det χ'⟩ の primary 分解)。char-level det の well-definedness は (v-a)
        (同 char⟹同型⟹同 det)。
        **✅ 進捗 (cont.¹⁷, commits `10cf2443`/`96136160`/`99363888`/`115b41c3`)**: (c1) `twistRep`
        + char/det 公式、(c2) `IsIrreducibleCharacter.determinant` + `determinant_spec` (rep 非依存)
        + `determinant_restrict` (RepresentationDeterminant.lean)、新 leaf
        **CanonicalCharacterExtension.lean** に `determinant_mul_linearClassFunction`
        (det(χ·lcfβ)=β^d·detχ)、`determinant_conjBy` (conj-equivariance)、
        `pow_index_eq_one_of_forall_coe_eq_one` ([K:H]-torsion)、
        **(c4) `extension_unique_of_not_dvd_orderOf_determinant` 完成** (p'-det-order 拡張の一意性、
        sorry-free axiom-clean)。`mul_linearClassFunction_one` (CharacterProduct)。
        **✅ (v-c) COMPLETE (2026-07-03 cont.¹⁸, commit `cab41e67`)**: (c3) 存在
        `IsIrreducibleCharacter.exists_extension_not_dvd_orderOf_determinant` (抽象 Bézout
        補題 `exists_mem_zpowers_pow_mul_pow_eq_one` — CommGroup で (x^o)^p=1, gcd(o,p)=gcd(d,p)=1
        ⟹ ∃β∈zpowers(x^o), (β^d·x)^o=1 — + 11.22 拡張 χ' の det 調整 twist) + (c5)
        `orderOf_determinant_eq_of_restrict_eq_of_not_dvd` (p ∤ o(χ) なる任意拡張で o(χ)=o(θ))。
        全 sorry-free axiom-clean。
        **具体 bricks (cont.¹⁶ 精密化)**:
        (c1) `twistRep ρ β := y ↦ β(y)•ρ(y)` (rep instance + character = β·χ + det = β^{finrank}·det ρ
        via `LinearMap.det_smul`) — χ·lcf(β) の affording rep。
        (c2) `IsIrreducibleCharacter.determinant : K→*ℂˣ` (choose 経由) + spec「χ = χ_σ なる任意の σ で
        = representationDeterminant σ」((v-a) 強形: affording rep は自動的に ρ と Equiv ⟹ det 一致は
        `LinearMap.det_conj`)。派生: det∘restrict 互換 (`representationDeterminant_comp`)、conj-equivariance
        ((χ^y).det = χ.det ∘ conj_y)。
        (c3) **存在の Bézout 調整**: 11.22 で χ' 取得、λ':=det χ'、λ:=det θ (o:=o(λ) coprime p)。
        λ'|_H=λ ⟹ λ'^o trivial on H ⟹ λ'^{op}=1。1=ao+bp と置き γ:=(λ'^o)^{-a} (trivial on H, γ^p=1):
        λ'γ = λ'^{bp} = (λ'^p)^b は p'-order ((λ'^p)^o=1)。β := γ^{θ(1)⁻¹ mod p} で χ:=χ'β が
        det = λ'γ = p'-order。
        (c4) **一意性**: χ₂=χ₁β ((v-b))、det 比 β^{θ(1)} は p'-order (両 det p'-order) かつ p-torsion
        (β trivial on H, K/H order p ⟹ β^p=1) ⟹ β^{θ(1)}=1 ⟹ β=1 (gcd(θ(1),p)=1) ⟹ χ₂=χ₁·lcf(1)=χ₁
        (要 mul_one 型 API: lcf(trivial)=trivialClassFunction + χ·triv=χ)。
        (c5) o(χ)=o(φ) 付随 (iterate の不変量維持): o(φ) | o(χ) (restriction) + o(χ)/o(φ) | p + p'
        ⟹ =。
        **(v-d)** iterate: **✅ COMPLETE (2026-07-03 cont.¹⁸, commit `b7cba75f`)** —
        `IsIrreducibleCharacter.exists_extension_of_forall_conjBy_eq` (**Isaacs CT 8.16 abelian
        case / 6.28**): H⊴K finite, K/H abelian (`∀ x y, ⁅x,y⁆ ∈ H` 形), θ∈Irr(H) K-invariant,
        gcd([K:H], o(θ)·θ(1))=1 ⟹ ∃χ∈Irr(K), Res_H χ = θ ∧ o(χ)=o(θ)。強帰納法 engine
        `exists_extension_of_forall_conjBy_eq_aux` (∀-形, [H.Normal] を telescope 内 instance 束縛)。
        設計どおり: Cauchy (minFac + `exists_prime_orderOf_dvd_card`) → N₁=comap mk' ⟨xbar⟩
        ([N₁:H]=p は `relIndex_comap`+`relIndex_bot_left`+`Nat.card_zpowers`) → subgroupOfEquivOfLe
        transport (`compHom_of_surjective` 既約性 + 新 `determinant_compHom`/`orderOf_monoidHom_comp_of_surjective`
        で det order) → (v-c3) canonical χ₁ → (v-c4) uniqueness で K-invariance → recurse。
        全 sorry-free axiom-clean, full build 3898 jobs green。
        type-I 適用は H=L_F Hall ⟹ o(θ)θ(1) | |H| coprime [I:H] で前提充足。
- [x] **char-product infra (Gallagher 前提)** — `RepresentationTheory/CharacterProduct.lean` (新 leaf, sorry-free,
      axiom-clean, cont.⁴): `ClassFunction` に pointwise `Mul` + `IsCharacter.mul` (χ·ψ = char of `tprod`,
      `Representation.char_tensor` 経由) + `mul_mem_ZIrr` (ZIrr は積で閉じる=部分環)。Gallagher の
      「χ·Inf(β) は character」(linear twist が norm 保存 → 既約) の核心前提。
- [x] **norm 保存 (twist の核)** — `CharacterProduct.inner_mul_self_eq_of_star_mul_self_eq_one` (cont.⁶,
      sorry-free): `∀g, lam g·conj(lam g)=1` (unit-norm) ⟹ `⟨χ·lam, χ·lam⟩ = ⟨χ,χ⟩`。linear char で twist しても
      norm 不変 → 既約保存の核。
- [x] **twist-既約 (Gallagher の既約性エンジン)** — `CharacterProduct` (cont.⁷, sorry-free, axiom-clean):
      - bridge (A) `IsIrreducibleCharacter.inner_self_eq_one` (`⟨χ,χ⟩=1`、bundled `irreducibleCharacter_inner_eq_ite` から)。
      - bridge (B) `IsIrreducibleCharacter.exists_apply_one_eq_pos_natCast` (`χ(1)=正整数`)。
      - **`isIrreducibleCharacter_mul_of_unit_norm`**: `χ∈Irr` + `lam` genuine char + unit-norm (`∀g,lam g·conj=1`) +
        `lam(1)=1` ⟹ `χ·lam ∈ Irr`。(norm 保存 + `isIrreducibleCharacter_of_inner_self_one_of_apply_one_pos`)。
- [x] **twist by linear char 完成** — `CharacterProduct` (cont.⁸, sorry-free, axiom-clean):
      - `linearClassFunction_mul_star_self_eq_one`: 有限群で `linearClassFunction (χ:H→*ℂˣ)` は unit-norm
        (`(χ h)^|H|=χ(h^|H|)=1` root-of-unity → `norm_eq_one_of_pow_eq_one` → `RCLike.inv_eq_conj`)。
      - **`isIrreducibleCharacter_mul_linearClassFunction`**: `χ∈Irr` × `χlin:G→*ℂˣ` ⟹ `χ·linearClassFunction χlin ∈ Irr`。
        = Gallagher の「χ·Inf(β) 既約」(Inf(β)=linearClassFunction of quotient hom)。
- [x] **decomposition 準備 (multiplicativity + lies-over)** — `CharacterProduct` (cont.⁹, sorry-free):
      `restrict_mul`/`compHom_mul` (積が Res/pullback と可換) + `restrict_mul_of_apply_eq_one`
      (`lam` が H 上 1 ⟹ `Res_H(χ·lam)=Res_H χ` = 「χ·Inf(β) は θ 上に lie」)。これで
      `⟨Ind_H^I θ, χ·Inf β⟩ = ⟨θ, Res_H χ⟩ = ⟨θ,θ⟩=1` (χ extends θ の下) が出せる。
- [x] **decomposition capstone** — `CharacterProduct.eq_sum_of_inner_eq_one_of_inner_self_eq_card`
      (cont.¹¹, sorry-free, axiom-clean): `S⊆Irr` の各 χ が `⟨φ,χ⟩=1` かつ `⟨φ,φ⟩=|S|` ⟹ `φ=∑_{χ∈S} χ`
      (Parseval `⟨φ,φ⟩=∑|⟨φ,χ⟩|²` + normSq≥0 で S 外係数消失、Fourier 展開を collapse)。任意の類関数で成立
      (ZIrr 仮説不要と判明)。「[I:H] 個 mult-1 constituents が norm² を尽くす ⟹ Ind_H^I θ = それらの和」を出す capstone。
- [x] **✅ (G2) Gallagher 本体 COMPLETE (2026-07-03 cont.¹⁸, commit `09a13625`)** — 新 shared leaf
      **`GallagherDecomposition.lean`**: `induce_eq_sum_mul_linearClassFunction` (Isaacs 6.17
      の coprime abelian 特殊化): H⊴K finite, K/H abelian, θ∈Irr(H) K-invariant, deg d,
      gcd([K:H],d)=1, χ∈Irr(K) 拡張 ⟹ **`Ind_H^K θ = Σ_{β∈Hom(K/H,ℂˣ)} χ·Inf(β)`** (mult-one,
      [K:H] 個 distinct)。単射性 = det 論法 (coprime; 一般 Gallagher 6.17 不要と確定)、counting =
      mathlib 有限 abelian 自己双対 (`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity`) +
      新 instance `Finite (G →* Mˣ)`、norm = inertia 公式、collapse = capstone。sorry-free
      axiom-clean。**Lean 教訓: 商の CommGroup instance は letI (haveI だと .toGroup が opaque
      になり ambient Quotient.group と defeq 切れで下流全滅)**。
- [ ] **type-F 適用**: `typeF_inertia_commutator_le` (I(θ)/H abelian) を (G3) に投入。
- [ ] **(1.5.a)/(1.2) 台**: 各構成要素 φ の台 ⊆ A(L)∪{1}。非実 = 奇数位数 (`not_isReal_of_ne_trivial_of_odd_card'`)。
- [ ] `typeI_induced_char_constituents` (S14:472) を上記 cite で sorry-free 化。lane b (12.14) は cite。

## 次の frontier + 判明した真の上流 bottleneck (2026-07-02 cont.³; 更新 2026-07-03 cont.¹⁸)

**✅ (G1) 6.28/8.16 extension と (G2) 6.17-coprime Gallagher は完結** (2026-07-03)。
**残る唯一の深い上流 = Clifford correspondence の既約性 (Isaacs 6.11)**:
`ψ ∈ Irr(I|θ) ⟹ Ind_I^L ψ ∈ Irr(L)` (I = I_L(θ) **非正規**)。既存 norm 機構
`InducedIrreducible.card_mul_inner_self_induce` / `card_smul_restrict_induce` は **`[H.Normal]`
前提** (`induceTerm_of_mem_normal` 経由) ゆえ慣性群 `I` に直接使えない。選択肢:
(i) **一般 (非正規) Mackey 公式** を build して norm 計算、または (ii) **Isaacs 6.11 の
θ-part 論法** (Mackey 回避: Res_H (Ind_I^L ψ) の θ-成分の multiplicity を直接比較 —
⟨Res_H Ind ψ, θ⟩ = ⟨Res_H ψ, θ⟩ を single-orbit + degree count で挟む)、または (iii) Coq
PFsection1 `constt_Inertia_bijection` の経路を精読して最短路を採る。
これが埋まれば: Ind_H^L θ = Ind_I^L (Ind_H^I θ) [induction-in-stages 済] = Σ_β Ind_I^L(χ̃·Infβ)
[(G2) 済] で各項既約 [6.11] → (1.7)(b) の等次数 [L:I]·d・mult-one 分解が完成、残りは
台 (1.5.a)/(1.2) + 非実 + S14 assembly のみ。

### 6.11 の設計確定 (2026-07-03 cont.¹⁸ 精査 — route (ii) θ-part 論法採用、一般 Mackey 不要)

**在庫が予想以上に厚い** (CliffordSingleOrbit / InducedCharacter):
- `apply_one_eq_restrictionMultiplicity_mul_index_inertia`: **ξ(1) = ⟨Res_H ξ,θ⟩·[G:I(θ)]·θ(1)** (等式!)。
- `apply_one_le_induce_apply_one_of_liesOver`: **χ(1) ≤ (Ind_I^G ψ)(1)** (構成要素 degree bound)。
- `coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`: χ over ψ + Ind ψ 既約 ⟹ χ = Ind ψ。
- `induce_apply_one`: (Ind ψ)(1) = [G:I]·ψ(1)。

**Isaacs 6.11 の Lean 化 (θ-part 勘定)**: H⊴G, T=I_G(θ) (hypothesis: `inertia θ ≤ T` + `T`-invariance
は transport)、ψ∈Irr(T) lies over θ' (T-level transport 形 `compHom e θ`)。χ := 任意の Irr 構成要素
of Ind_T^G ψ、m := ⟨Ind ψ, χ⟩ = ⟨Res_T χ, ψ⟩ ≥ 1。
1. ψ(1) = e·θ(1) where e := ⟨Res_{H'} ψ, θ'⟩ — single-orbit degree 等式を (T, H.subgroupOf T) で
   適用 (θ' の T-inertia = ⊤: (v-d) の hinv₁ transport idiom 再利用)。
2. **key 下界 e_χ := ⟨Res_H χ, θ⟩ ≥ m·e**: ⟨Res_H χ, θ⟩ = ⟨Res_{H'}(Res_T χ), θ'⟩ [唯一の
   inner-transport = `inner_compHom_of_mulEquiv`] = Σ_{ρ∈Irr(T)} ⟨Res_T χ,ρ⟩·⟨Res_{H'} ρ, θ'⟩
   [Fourier + inner 線形性] ≥ m·e [全項非負]。
3. 次数勘定: χ(1) = e_χ·[G:T]·θ(1) [1. の等式、I_G(θ)=T] ≥ m·e·[G:T]·θ(1) = m·(Ind ψ)(1)、
   一方 χ(1) ≤ (Ind ψ)(1) → **m = 1 ∧ χ(1) = (Ind ψ)(1)**。
4. **degree-exhaustion**: ⟨Ind ψ, χ⟩ = 1 + (Ind ψ)(1) = χ(1) + Ind ψ = Σ_η ⟨,η⟩η (係数∈ℕ≥0)
   ⟹ Ind ψ = χ 既約。(capstone 類似の新 helper。)

**blocker → issue 9005 起票済**: `inner_compHom_of_mulEquiv` / `induce_induce_subgroupOf` /
`induce_eq_sum_inner_restrict_smul` が **S08_CaseBCoherence2.lean (lane b 所有) 内の generic 宣言**
— shared 化の prefix-split を hub に依頼 (GroupTheory/** から Pf leaf への import 逆流は不可)。
lane c は relocate 非依存部品 (4. degree-exhaustion、1./2. の骨格) を先行 build。
なお stages (`induce_induce_subgroupOf`) は 6.11 本体には不要 — (1.7)(b) 最終 assembly (Pf leaf 側,
S08 import 可) でのみ使用。

**性質**: genuine multi-session char build (G1-G3 は Isaacs §6/§11 の generic char theory で repo 未収録)。
Frobenius sub-case は proven ゆえ witness (12.16) 経路は現状も通る; 本 issue は一般 (12.14) 用の shared infra。

## 完了条件

`typeI_induced_char_constituents` (S14:398) sorry-free、`lake build` 緑。generic Clifford 部が shared leaf
で lane b から cite 可能な signature。

## 参照

- 親 issue: 0026 (peterfalvi-clifford-core、subsume)、0023 (clifford-decomposition)
- hub 再裁定: issue 9001「HUB 再裁定 (2026-07-02) — σ-theory-dual 撤回 + lane c に構成的 Clifford 再配分」
- landed 核: `CliffordSingleOrbit.lean` / `InducedIrreducible.lean` / `CliffordMultiplicityOne.lean` /
  `Clifford.lean` / `Inertia.lean`
- consumer: `S14_MaximalI.lean:389` (lane c) / Pf (12.14) M-side (lane b)
- Pf 原文: 03 §3 (1.5)/(1.7)、04.8 §8 (8.2.c)

## ⚠ HUB 裁定 (2026-07-02, cron tick) — 範囲逸脱: S14 でなく shared leaf に置くこと

**検出**: lane c が `typeF_inertia_inf_U_isMulCommutative` (S14:391) + `typeF_inertia_commutator_le`
(S14:417) を **`S14_MaximalI.lean` (= lane b 所有) に追加** = 範囲逸脱 (3 レーンマップ: c の所有は
S15_SAndT_Setup/S15_SAndT/S16 + Clifford は **shared leaf**)。⟹ **lane c は今 tick 合流せず** (a/b は合流済)。

**裁定 (benign・明快ゆえ hard-STOP でなく relocate 指示)**:
- 2 lemma は generic (`{Γ : Type*}` 抽象、FT の G に非依存) = **shared inertia/Clifford leaf に置く**。
  既存 **`Inertia.lean`** (issue 9002 landed 核) or GroupTheory/** の Clifford leaf が正位置。**S14 に置かない**。
- 既存 S14 `typeF_inertia_inf_le_U1` (S14:364、generic だが lane b file に grandfather 済) を depend するなら
  **cross-file cite** (citing ≠ editing、逸脱でない)。将来 shared 化するなら hub prefix-split で対応 (lane b 調整)。
- consumer 側の wiring が lane b の S14 内 (issue 9002 が言う ":389") に要るなら、それは **lane b が cite** する
  (lane c は shared lemma を供給、lane b が S14 で消費)。lane c は S14 を編集しない。

**lane c への指示**: 次 sync で本裁定を拾い、2 lemma を S14 から shared leaf へ **relocate** (S14 の追加を revert +
shared leaf に再配置)。relocate 後は通常合流。**relocate まで hub は c を skip** (a/b は継続監視、loop は止めない)。

**⚠ 逸脱の再発防止**: lane c の Clifford (9002) は **必ず shared leaf** で build (S14/他レーン file を編集しない)。
generic Clifford/inertia は `Inertia.lean`/`Clifford*.lean`/GroupTheory/** に置き、各 consumer が cite。

### ✅ RELOCATE 完了 (lane c, 2026-07-02 cont.⁵ — 本裁定を拾って対応)

裁定に従い、2 lemma を S14 から **新 shared leaf** `OddOrder/GroupTheory/RepresentationTheory/InertiaAbelianQuotient.lean`
へ relocate。S14 からは両 lemma を削除 (`typeF_inertia_inf_le_U1` は grandfather 済ゆえ S14 に残置・不触)。
hub 指示どおり **generic 化** (`{Γ}`+`{k}` 抽象、8.2.c の `hle`/abelian を仮説化 → S14 非依存で GroupTheory/** 上流に置ける):
- `ClassFunction.inertia_inf_isMulCommutative_of_le`: `I(θ)∩U ≤ U₁` + `U₁` abelian ⟹ `I(θ)∩U` abelian。
- `ClassFunction.commutator_inertia_le_of_sup_eq_top`: `H⊔U=⊤` + `I(θ)∩U` abelian ⟹ `⁅I(θ),I(θ)⁆ ≤ H`。

両 sorry-free、`lake build` 緑 (leaf 1085 jobs / S14 除去後も 3855 jobs green)。type-F 特殊化 (8.2.c=`typeF_inertia_inf_le_U1`
を cross-file cite して `hle` 供給) は **consumer 側** (S14 の `typeI_induced_char_constituents` を埋める時、lane b or
lane c の新 Pf leaf) が実施 — lane c は S14 を編集しない。以後 Clifford は必ず shared leaf で build。

## 📌 HUB watch note (2026-07-02, ユーザー委任レビュー)

lane-role review で確認: claim・relocate 対応・周辺 infra (~15 補題 sorry-free: CharacterProduct /
RepresentationDeterminant / InertiaAbelianQuotient) はすべて正当・on-role。**watch item = (G1)
extension 本体**: 直近 3 commits は小さい周辺 brick (rep-det 系 8–40 行) で、(G1) の core pieces
(i) invariant-θ intertwiner / (ii) Schur scalar / (iii) n-th root 正規化 / (iv) 拡張構成 / (v) abelian
iterate は未着手。次回 hub レビューで (i)–(iii) が landing し始めているかを確認する — 周辺 brick の
追加が続くだけなら難所回避シグナルとして flag ([[feedback-no-avoiding-hard-parts]])。multi-session
なのは想定内 (slow discharge ≠ stall)。
