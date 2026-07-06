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
- [x] **type-F 適用**: `typeF_inertia_inf_le_U1` / `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le`
      を S14 に投入済み (lane b loop¹¹⁴)。
- [x] **(1.5.a)/(1.2) 台**: support は
      `S03b_Vanishing.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`、非実は
      `forall_mem_not_isReal_of_induce_eq_sum_of_odd` で discharge 済み。
- [x] `typeI_induced_char_constituents` (current S14:L442) を上記 cite で sorry-free 化済み (lane b loop¹¹⁴)。

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

### ✅ 6.11 + (1.7)(b) core assembly COMPLETE (2026-07-03 cont.¹⁹)

- **✅ Isaacs 6.11 完結** (commit `105200e0`, `CliffordCorrespondence.lean`):
  `isIrreducibleCharacter_induce_of_liesOver_of_inertia_eq` — H⊴G, inertia θ = T, ψ∈Irr(T)
  over θ (transport 形 hover) ⟹ Ind_T^G ψ 既約。θ-part 論法 (Mackey 不要) 設計どおり:
  `restrictionMultiplicity_mul_le_restrictionMultiplicity` (θ-mult 下界、
  `inner_compHom_of_mulEquiv` は **hub が issue 9005 で InducedTransport.lean に shared 化済**) +
  single-orbit degree 等式×2 + 構成要素 degree bound + degree exhaustion。
- **✅ (1.7)(b) core assembly 完結** (commit `488308f2`, 新 leaf `CliffordDecomposition.lean`):
  `exists_extension_induce_eq_sum_induce_mul` — H⊴L, inertia θ = T, T/H abelian,
  gcd([T:H], o(θ)·d)=1 ⟹ ∃χ∈Irr(T) 拡張, **`Ind_H^L θ = Σ_{β∈Hom(T/H,ℂˣ)} Ind_T^L(χ·Infβ)`
  ∧ 各項既約** (次数 [L:T]d は induce_apply_one で自明)。(G1)+(G2)+(G3)+stages の純合成。
  全 sorry-free axiom-clean、full build 3905 jobs green。

### 次 frontier: mult-one packaging → type-I 適用 (設計固定 2026-07-03)

**S14 consumer の必要形** (`typeI_induced_char_constituents`, S14:418 sorry): `∃ S : Finset (Irr ↥L),
Nonempty ∧ chi = Σ_{φ∈S} φ ∧ 等次数 ∧ 非実 ∧ conj-distinct (φ.conj ∉ S 対) ∧ 台 ⊆ A(L)∪{1}`。

**(a) mult-one/distinctness packaging (generic, CliffordDecomposition.lean に追加)**:
norm count 論法。c_χ := ⟨Ind_H^L θ, χ⟩ ∈ ℕ (`inner_induce_coe_eq_restrictionMultiplicity`+natCast)。
(i) Parseval Σ_χ c_χ² = ⟨Ind θ, Ind θ⟩ (capstone hpars 手法) = [T:H] (inertia norm 公式
`card_mul_inner_self_induce_eq_card_inertia`: |H|·⟨,⟩=|T|、|T|=[T:H]·|H| は index_mul_card at ↥T +
card_congr subgroupOfEquivOfLe)。(ii) c_χ = Σ_β [η_β = χ] (`irreducibleCharacter_inner_eq_ite`、
η_β := Ind_T(χ̃β) 既約) ⟹ Σ_χ c_χ = |Hom| = [T:H] (fiber counting)。(iii) Σc² = Σc (ℕ) ⟹
∀χ c_χ ≤ 1 ⟹ **β ↦ η_β injective** (fiber ≤ 1)。S := image、card = [T:H]、sum_image で
`Ind_H^L θ = Σ_{χ∈S} ↑χ`、∀χ∈S ∃β 生成形。
**(b) type-I 適用 (Pf-side 新 leaf、S08/S14 import 可)**: hinertia は typeF_inertia 系 +
`commutator_inertia_le_of_sup_eq_top` (I(θ)/H abelian 証明書) から I(θ) = T の同定; coprime は
H = L_F Hall (o(θ)·d | |H|, gcd(|H|,[T:H])=1); 非実 = `not_isReal_of_ne_trivial_of_odd_card'`
(χ ≠ 1 は ⟨Ind θ, 1⟩ = ⟨θ, 1⟩ = 0); conj-distinct: φ̄ も S 型構成要素で φ̄ = Ind(χ̃β)-bar …
(1.2)/(1.5.a) 台: 各 η_β は H の外で… Frobenius ケースの `frobenius_typeI_induced_char_constituents`
(S14 landed) の bookkeeping を一般化。

### ✅ (a) mult-one packaging COMPLETE + (b) 部分着地 (2026-07-03 cont.²⁰)

全て **shared leaf `CliffordDecomposition.lean` / `CharacterProduct.lean`** に配置 (S14 非依存 ⟹
将来 `typeI_induced_char_constituents` から import cycle なしで cite 可)。全 sorry-free axiom-clean、
full build 3906 jobs green。

- **✅ (a) mult-one/distinctness packaging** (commit `63ba174e`, main merged `41f65558`):
  - `injective_of_sum_inner_self_eq_card` (CharacterProduct): 族 `η:ι→Irr(G)` の和が
    `⟨∑ηᵢ,∑ηⱼ⟩=|ι|` ⟹ 単射。設計の fiber-count でなく **「equal-value pair 集合 = 対角線」**
    論法 (⟨,⟩ = |{(i,j):ηᵢ=ηⱼ}| via 直交、対角線が |ι| を尽くす)。より短い。
  - `exists_finset_eq_sum_of_sum_inner_self_eq_card` (CharacterProduct): 上を Finset S=image に包装。
  - `exists_extension_induce_eq_sum_distinct_irreducible` (CliffordDecomposition): (1.7)(b) 仮説下で
    `Ind_H^L θ = Σ_{φ∈S} φ` (S nonempty, |S|=[T:H], 相異), 等次数 `[L:T]·d`, 各 φ=Ind_T(χ·Inf β)。
    norm-count = `card_mul_inner_self_induce_eq_card_inertia` + `card_monoidHom` + injective 補題。
- **✅ (b-inertia) type-F 特殊化** (commit `f6cd8258`, main merged): 
  `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le` — 抽象 `hab` を (8.2.c) 具体データ
  (`H⊔U=⊤` + `I(θ)∩U≤U₁` + U₁ abelian) に差し替え、`inertia_inf_isMulCommutative_of_le` +
  `commutator_inertia_le_of_sup_eq_top` で `⁅I,I⁆≤H` 導出 → packaging。
- **✅ (b-非実) 非実性** (commit `84b37663`): `forall_mem_ne_trivial_of_induce_eq_sum` (⟨Ind θ,1⟩=0
  ⟹ 各構成要素 ≠1) + `forall_mem_not_isReal_of_induce_eq_sum_of_odd` (奇数位数で非実)。

**残 (b) — S14 consumer が cite で組む (lane b wiring or lane c の S14-import leaf)**:
- ~~**conj-distinct**~~ **✅ COMPLETE (cont.²¹, commit `a42db267`)**: 全 generic・shared leaf・
  sorry-free axiom-clean。θ̄≁θ も **奇数位数から generic に証明済** (gate でなかった):
  - `conj_induce`: `(Ind θ)̄ = Ind θ̄` (star が induce 和に分配)。
  - `conjBy_ne_conj_of_odd`: θ^g=θ̄ ⟹ θ^{g²}=θ ⟹ g²∈I(θ); g 奇数位数 ⟹ ⟨g⟩=⟨g²⟩
    (g=(g²)^{(o+1)/2}、**I の正規性不要**) ⟹ g∈I(θ) ⟹ θ=θ̄ 実 ⟹ θ=1 矛盾。
  - `forall_mem_conj_ne_of_odd`: θ̄≁θ ⟹ ⟨Ind θ,Ind θ̄⟩=0 ⟹ pair-count {(φ,φ'):φ=φ'̄}=0。
- ~~**非実**~~ **✅ COMPLETE (cont.²⁰, commit `84b37663`)**: `forall_mem_not_isReal_of_induce_eq_sum_of_odd`。
- **台 ⊆ A(L)∪{1}** (残): 各 φ (=Ind_T(χ·Inf β)) は normal H の外で消える (Ind from normal) ⟹ supp⊆H#。
  H# ⊆ A(L) (typeIA) を確認して `supportInSubgroup ambientA L ∪{1}` に落とす (Frobenius 版 `frobenius_typeI_induced_char_constituents`
  の support bookkeeping を一般化)。Frobenius 版は `induceSum_eq_zero_of_not_conjugatesInto` 使用。
- **Hall coprimality wiring** (残): [T:H']|[L:H']=|U'| (complement) + o(θ')·d | |H'| + Coprime|H'||U'|
  (`IsHallSubgroup.coprime_index`, L_F=maxNilpotentNormalHall Hall) ⟹ hcop。
- **hcent bridge** (残): type-F `centralizer_le_U1` (G-level `U⊓C_G(x)≤U1`) → `typeF_inertia_inf_le_U1`
  の ↥L-level `hcent` (centralizer subgroupOf 移送)。
- これらが揃えば `typeI_induced_char_constituents` (S14:429 sorry) を cite で sorry-free 化。

**shared leaf 在庫まとめ (cont.²¹ 時点、全 sorry-free axiom-clean、CliffordDecomposition/CharacterProduct)**:
packaging (`exists_extension_induce_eq_sum_distinct_irreducible`) + type-F inertia 特殊化
(`..._of_inertia_inf_le`) + 非実 2 本 + conj-distinct 3 本 + generic injective/finset 2 本。
S14 consumer が必要とする 6 clause 中 4 (nonempty/decomp/等次数/非実/conj-distinct) は cite 可能。
残 = 台 + coprimality/hcent の type-F→↥L wiring (S14-import 側で組む)。

### ✅ coprimality COMPLETE (cont.²² 2026-07-03, commit `5e81d626`)

`coprime_index_orderOf_determinant_mul_of_coprime_index` (CliffordDecomposition.lean, sorry-free
axiom-clean): `H⊴L` Hall (`gcd(|H|,[L:H])=1`) + θ∈Irr(H) 次数 d ⟹ `Coprime [T:H] (o(det θ)·d)`
(任意 H≤T≤L)。**Ito 定理は既に repo にあった** (`IsIrreducibleCharacter.exists_natDegree_charValue_one_dvd_card`
= `finrank_dvd_card`, ZIrr.lean) → `d∣|H|`; `o(det θ)∣|H|` (linear char |H|-torsion);
`[T:H]∣[L:H]` (`relIndex_mul_index`); Hall で分離。**gate でなかった** ([[feedback-dont-mislabel-formalization-as-research]])。

これで glue `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le` の全入力
(hinertia/hHU/hbound/hU1comm/hcop/hd) が shared/type-F データから供給可能。

## consumer assembly レシピ (S14-import 側 = lane b or 次 lane c session)

**残 = `typeI_induced_char_constituents` (S14:429) の組み立てのみ。generic 核は全在庫。** 手順:
1. `chi ∈ hyp.Sset` を unpack → `θ' : Irr(H')`, `θ'≠1`, `chi = Ind_{H'} θ'` (H' = (L_F).subgroupOf L)。
2. `T := inertia θ'`; `hinertia := rfl`。instances (`(H'.subgroupOf T).Normal` = `subgroupOf_inertia_normal`
   等、`Invertible (Nat.card : ℂ)` = char 0 finite、`Fintype (Hom)`) を letI/haveI 供給。
3. **glue 入力**: `hHU` = type-F complement (`data.complement.sup_eq_top` を subgroupOf 化);
   `hbound` = `typeF_inertia_inf_le_U1` (S14 grandfather、↥L で apply — 要 hcent bridge: G-level
   `data.centralizer_le_U1` → ↥L-level centralizer、+ hUHcop = Hall); `hU1comm` = `data.U1_commutative`
   subgroupOf 化; `hcop` = **`coprime_index_orderOf_determinant_mul_of_coprime_index`** + Hall
   (`(maxNilpotentNormalHall).subgroupOf` の `IsHallSubgroup.coprime_index`); `hd` = θ'(1) の nat 値。
4. glue → S (nonempty/card/decomp/等次数/witness)。
5. **非実** = `forall_mem_not_isReal_of_induce_eq_sum_of_odd hodd θ' hθ'ne hSsum` (hodd = L 奇数位数)。
6. **conj-distinct** = `forall_mem_conj_ne_of_odd hodd θ' hθ'ne hSsum`。
7. **台 ⊆ A(L)∪{1}** (唯一の type-I 固有・要 build): 各 φ=Ind_T(χ·Inf β) の台。Frobenius 版
   `frobenius_typeI_induced_char_constituents` は `induceSum_eq_zero_of_not_conjugatesInto` (normal H の外で消滅)
   使用だが、**一般 T>H では constituent は個別に H 外で消えない** (T\H で非零可) ゆえ Pf (1.2)/(1.5.a)
   の type-I 論法が要る。A(L)=typeIA の構造 + (1.5.a) `(Res_H φ,1_H)=0` から台を絞る。要原文精読。

**⟹ 残る genuine build は台 (1.2)/(1.5.a) のみ。他は全 cite。** hcent bridge は centralizer subgroupOf 移送
(機械的だが要注意)。lane b が S14 で消費 (lane c は S14 非編集の shared 供給完了)。

### 6.11 の設計確定 (2026-07-02 cont.¹⁸ 精査 — route (ii) θ-part 論法採用、一般 Mackey 不要)

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

## 🔎 lane b 精査 (2026-07-04, loop¹¹²) — (8.2.c) consumer は cite-assembly と確認、残 gap = (1.2) support + 調整要

lane b が上流優先で S14 最上流 sorry `typeI_induced_char_constituents` (S14:429) に着手する前に
本 issue を scan (claim-before-build)。**lane c の 9002 infra は essentially complete と確認**:
`CliffordDecomposition.lean` = 0 sorry、`exists_extension_induce_eq_sum_distinct_of_inertia_inf_le`
(decomposition + 等次数) / `coprime_index_orderOf_determinant_mul_of_coprime_index` (Hall coprimality) /
`forall_mem_not_isReal_of_induce_eq_sum_of_odd` (非実) / `forall_mem_conj_ne_of_odd` (conj-distinct) 全 landed。
∴ (8.2.c) general は **cite-assembly** (rebuild でない) と確定。

**残 S14-side wiring (recipe cont.²¹ の「残」を精査)**:
1. **(1.2) support `supp φ ⊆ A(L)∪{1}`** = **genuine gap (未形式化)**。recipe は「Ind from normal で
   supp⊆H#」とするが、general case (T=I(θ)⊋H) の構成要素 φ=Ind_T(χ·Infβ) は **H の外で消えない**
   (Frobenius singleton と違い、χ は T∖H で非零; 個々の φ は χ=Σφ が H 外で消えても個別には消えない)。
   真の target は A(L)∪{1} (⊇H^#) で、Pf **(1.2)** (H⊄Ker φ ⟹ supp⊆A(L)∪{1}, Dade domain の
   台結果) を要す。repo に (1.2)-型 support lemma 不在 (`escaping_supported_of_A1_conj_mem_typeIA`
   は escaping 特化で別物)。**これが実質的な残 hard piece**。
2. **`H⊔U=⊤` 同定**: type-F の L=L_F·complement 構造 (TypeFData の U が full complement か要確認;
   `frobeniusData over H⊔U0` は U0⊆U で別); 主 lemma の hHU 引数。
3. **hcent bridge**: TypeFData.`centralizer_le_U1` (G-level `U⊓C_G(x)≤U1`) → 主 lemma の ↥L-level
   `hbound = inertia θ ⊓ U ≤ U1` (subgroupOf 移送 + `typeF_inertia_inf_le_U1`)。
4. coprimality/hd/inertia=T は cite/rfl。

**⚠ 調整要 (lane b→lane c/hub)**: 主 lemma 群は landed だが最終 S14 assembly は recipe が
「**lane b wiring OR lane c の S14-import leaf**」と両論併記 → 所有が曖昧。かつ (1.2) support は
9002 constructive-Clifford の一部か S14-consumer の別作業か不明。**質問**: (a) 最終 S14 assembly は
lane b (file owner) が cite で組んでよいか? (b) (1.2) support は lane c が 9002 で closingするか、
lane b/別 leaf か? lane b は衝突回避のため本裁定待ちの間 (8.2.c) は触らず別 target (type-P engine /
S10 §8) に回す。lane c が S14-import leaf 済 or 進行中なら本 issue に追記を。

## ✅ HUB 裁定 (2026-07-04, cron tick — loop¹¹² の (a)/(b) 調整に回答)

所有ルールから一意に決まるため hub が裁定 (b は docs-only・別 target へ自己管理中ゆえ STOP でない):

- **(a) (8.2.c) `typeI_induced_char_constituents` (S14:429) の最終 assembly = lane b**。S14_MaximalI は
  b 所有ファイルゆえ、b が **c の 9002 shared infra (`CliffordDecomposition.lean` = GroupTheory/**,
  0 sorry, essentially complete) を cite で assemble** する。recipe の「lane b wiring OR lane c の
  S14-import leaf」両論併記は解消 → **lane c は S14 を import しない** (c 所有は S15/S16; signature-contract
  で c の generic infra を b が下流 cite が正)。

- **(b) (1.2) Dade-domain support `supp φ ⊆ A(L)∪{1}` = lane b が新 shared leaf で build**。理由:
  (1.2) は c の 9002 constructive-Clifford (extension/decomposition) とは別物の一般 support 結果ゆえ
  **complete な 9002 に足さない**。consumer は b、canonical home の Pf §1 は名目 a の S03 territory だが
  a は §7 に集中中 → **b が consumer として未所有 shared leaf (`OddOrder/GroupTheory/**` または
  Peterfalvi-general、a の S03 は触らない) に claim-before-build で建てる** (policy: 未所有 leaf 新設は
  consumer が他レーンでも in-scope)。着手前に repo 再 grep で既存 (1.2)-型 support の不在を再確認
  (b の loop¹¹² grep = 不在、`escaping_supported_of_A1_conj_mem_typeIA` は escaping 特化で別物)。
  claim は 9000 系 issue を起票 (a の §1-3 σ-tail と衝突しないか a は cite で回避)。

⟹ lane b は本裁定で (8.2.c) assembly + (1.2) leaf を自レーン/shared で進めてよい (hub 承認)。
**⚠ (b) 半分は下記 lane b loop¹¹³ 訂正で上書き** — (1.2) は既 formalized ゆえ新 leaf 不要。(a) は据置。

## ✏️ lane b 訂正 (loop¹¹³) — (1.2) support は既に形式化済、(8.2.c) は FULLY cite-assembleable

loop¹¹² で「(1.2) support = 未形式化 gap」としたのは**誤り**。Pf (1.2) (「H⊴G, χ∈Irr(G),
H⊄Ker χ, C_H(g)=1 ⟹ χ(g)=0」) は **`S03b_Vanishing.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`
(既 landed)** で形式化済。∴ (8.2.c) の support clause も cite (A(L)=typeIA={y≠1:C_{L_F}(y)≠1} +
(1.2) の対偶: φ(x)≠0,x≠1 ⟹ C_{H}(x)≠⊥ ⟹ x∈typeIA)。

**∴ (8.2.c) general は FULLY cite-assembleable** (全 6 clause 部品 landed)。残る lane-b wiring は
純機械的: (i) `H⊔U=⊤` (type-F L=L_F·U)、(ii) hcent bridge (TypeFData.centralizer_le_U1 の ↥L 移送)、
(iii) 各構成要素の H⊄Ker (φ over θ≠1 から)。**lane b は本 wiring を自 S14 file で進める** (recipe の
「lane b wiring」path; 衝突回避で lane c に通知: lane c が S14-import leaf 進行中なら本 issue に追記を)。

## 🚧 lane b WIP (loop¹¹³) — (8.2.c) full assembly 執筆済 (notes に保存)、残 = set-unification + 2 sub-proof

(8.2.c) `typeI_induced_char_constituents` の全 assembly を執筆 (~130 行、
`notes/peterfalvi/s14_typeI_induced_assembly_wip.txt` に保存)。math + API map は正しく、lane c 部品を
cite: `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le` (decomp+等次数) /
`coprime_index_orderOf_determinant_mul_of_coprime_index` (Hall) / `forall_mem_not_isReal_of_induce_eq_sum_of_odd` /
`forall_mem_conj_ne_of_odd` / (1.2) `S03b.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`。
type-F wiring: `complement.symm.index_eq_card` (card U=[L:K]) / `complement.sup_eq_top` (H⊔U=⊤) /
`typeF_inertia_inf_le_U1` + ↥L-hcent bridge / `isMulCommutative_of_mulEquiv (subgroupOfEquivOfLe).symm`。

**残 3 点 (fresh session で 1-2 cycle、marathon tail の plumbing friction を回避)**:
1. **import 追加**: `import OddOrder.GroupTheory.RepresentationTheory.CliffordDecomposition` を S14 へ
   (現状 S14 は lane-c leaf を未 import ゆえ全 cite が unknown)。
2. **`set K` 回避**: θ は Sset から raw `↥((L_F).subgroupOf L)` 型で obtain される。`set K := ...` 後の
   θ は raw のままで `trivialIrreducibleCharacter ↥K` と unification mismatch、`rw [← hKdef]` は
   dependent motive で失敗。→ **`set K/Usub/U1sub` を使わず** raw `(hyp.typeI.typeF.H).subgroupOf L`
   を直接使う (θ 型と一致) か、obtain 前に generalize。
3. **2 sub-proof**: (a) `hHker` (K⊄Ker φ) の inner-induce=0 step = Frobenius `inner_induce_eq_inner_restrict`
   (S14:1905 `constituents_not_inHKernel` を mirror)。(b) `centralizerInSubgroup K x = ⊥` を
   (x:G)∉typeIA={y≠1:C_{L_F}(y)≠1} から (`mem_centralizerInSubgroup` unfold)。
4. hG を `character_decomposition_and_dade_domain` (S14:546, 既 _hG) に thread。

**API 確定名**: `ClassFunction.subgroup_le_inertia` / `hKnormal.comap T.subtype` / `hθirr.determinant`
(先に `have hθirr : IsIrreducibleCharacter (θ:CF) := θ.isIrreducible`) / lane-c lemma は
`OddOrder.RepresentationTheory.` 修飾。

## ✅ lane b 完了 (loop¹¹⁴) — (8.2.c) `typeI_induced_char_constituents` 実証明・landed

前 iter の WIP assembly を fresh session で landing (S14 sorries 11→10、full build 3910+ green)。
`set K` unification 回避 (raw `(typeF.H).subgroupOf L` 形) + `open scoped FiniteInduce`
(chi/Sset と instance 一致、instance-diamond 解消) + import `CliffordDecomposition` で解決。
全 6 clause = lane c 9002 infra + Pf (1.2) の pure cite-assembly:
- decomp+等次数 = `exists_extension_induce_eq_sum_distinct_of_inertia_inf_le`
  (type-F data: `complement.sup_eq_top`/`complement.symm.index_eq_card`/`typeF_inertia_inf_le_U1`+↥L-hcent/
  `isMulCommutative_of_mulEquiv`/`coprime_index_orderOf_determinant_mul_of_coprime_index`)。
- 非実 = `forall_mem_not_isReal_of_induce_eq_sum_of_odd`、conj-distinct = `forall_mem_conj_ne_of_odd`。
- 台 ⊆ A(L)∪{1} = Pf (1.2) `S03b.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`
  (K⊄Ker φ from mult-one + C_K(x)=⊥→typeIA)。
hG thread → `character_decomposition_and_dade_domain`。**一般 type-I maximal の (12.2.a) carrier が
sorry-free 化 → 非-Frobenius N の (12.3)/(12.4)/(12.15) が un-gate**。s14_typeI_induced_assembly_wip.txt 削除。

## ✅ HUB CLOSURE (2026-07-06 夕, c FOLD 裁定 wf_00a0db07) — 完了条件 met、closed

分担監査 (4-agent) で確定: 構成的 Clifford core は全 sorry-free landed
(CliffordSingleOrbit/CliffordCorrespondence/CliffordDecomposition/GallagherDecomposition/CharacterProduct/
CyclicCharacterExtension)、consumer `typeI_induced_char_constituents` (S14_MaximalI:442) は **body sorry-free**
(台 clause ⊆A(L)∪{1} = Pf(1.2) で in-place 証明済、lane b が landed)。唯一の transitive sorryAx =
`typeF_inertia_inf_le_U1` = (8.2.c) = **lane-b の §8 grandfather bound** (本 issue の Clifford 範囲外)。
⟹ 9002 の deliverable (cite-ready 構成的 Clifford signature) は **達成**。closed へ。
