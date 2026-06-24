# Pf (5.7) standalone constant-degree coherence producer — lane-c relane #8 (issue 4012)

> 割当: 2026-06-23 relane #8 (issue 4012 RESOLVED)。lane-c = Pf §5 (5.7) coherence producer。
> lane-h relane #7 (§6 (6.2)/(6.3)) と対 = **C:§5 (5.7) / H:§6 (6.2)/(6.3)** で §13 を上流から unblock。
> consumer = lane-c 自所有 S13 `HC_le_secondDerived` (11.5)。

## 0. タスク

**Pf (5.7)** の standalone 形を生産する:

> **(5.7)** Assume Hypothesis (5.2) and that `χ(1)` is independent of `χ` for `χ ∈ S`. Then `S` is
> coherent. (`references/peterfalvi/04.7_pp_25_29_Coherence.mmd:107`)

consumer の (11.5) は「`M'/M''` abelian ⟹ `S(M'')` coherent」として (5.7) を使う (等次数は abelian quotient
から従う)。⟹ 生産する standalone = **Hypothesis (5.2) + 等次数 ⟹ `Nonempty (IsCoherent τ S A)`**。

## 1. 🟢 重要: building block は全て repo に在る (= (5.7) は assembly、missing-machinery でない)

S01 notes の「(5.7)-(5.9) 完全欠落」は **(5.7) が定理として未 STATE/未組立**の意味で、構成部品は
`S07_Coherence.lean` に揃っている (本セッション scoping で確認):

| Pf | repo (S07_Coherence.lean) | 役割 |
|---|---|---|
| (5.1) coherence def | `IsCoherent` (:1557) — extension / inner_eq / extends_on_supported / mem_ZIrr | **target** |
| (5.2) Hypothesis | `Hypothesis` (:1665) — tau / tau_isometry / conjugate_closed / no_real_characters / pairwise_orthogonal / difference_image (5.2.d) / difference_images_orthogonal (5.2.e) | **input** |
| (5.2.d) | `CharacterDifferenceImage` / `difference_image` field | R(χ) |
| (5.4) decomposition | `CharacterPsiDecomposition` (:1163付近) — X / Y / tau1 / imageFamily | (χ−ψ)^{τ₁}=X−Y |
| (5.4.a) ‖X‖²≥‖χ‖² | `CharacterPsiDecomposition.X_norm_ge` 系 (:1378) | |
| (5.4.b) | `norm_eq_and_X_eq_sum_of_norm_Y_ge` (:1460) | ‖Y‖²≥‖ψ‖² ⟹ ‖X‖²=‖χ‖², X=∑_E α |
| **(5.5)** ψ=0 版 | `eq_sum_of_psi_eq_zero` (:1522) | Y=0, χ^{τ₁}=X=∑_E α, \|E\|=‖χ‖² |
| (5.6.3) 構成 engine | `retarget_isCoherent_of_decomposition`(:3737) / `_decompositions`(:3911) / `_and_memberFamily`(:3979) | **IsCoherent を組む constructor** |

⟹ (5.7) = これらの **assembly**。深い char core は既に landed (lane-h の (6.2) が h62 oracle を要したのと
違い、(5.7) の (5.4)/(5.5) は完全に repo 内)。

## 2. (5.7) 証明設計 (Pf 原文 04.7:107-118)

- **base case `|S|=2`** (S={χ,χ̄}): (5.2.d) `difference_image` が直接 R(χ) を与え coherent。
- **inductive `|S|≥4`**: S = S₁ ∪ {χ,χ̄}, S₁ ⊥ {χ,χ̄}。各 χ₁∈S₁ で:
  - (χ−χ₁)^τ = X − X₁ + Y 分解、(5.4.a)+(5.4.b) で ‖X‖²=‖χ‖², Y=0, X=∑_{E}α (E⊆R(χ))。
  - X が χ₁ に独立 (`|E|=‖χ‖²=(χ−χ₁,χ−χ₂)=(X,X')=|E∩E'|` ⟹ E=E')。
  - τ₁: χ^{τ₁}=X, χ₁^{τ₁}=X−(χ−χ₁)^τ。等長性を ‖X‖²=‖χ‖² + 生成系で。
- **repo 経路**: 各 member の `CharacterPsiDecomposition` を ψ=0 ((5.5)) で建て、X=χ^{τ₁} を得て
  `retarget_isCoherent_of_decompositions[_and_memberFamily]` に渡し `IsCoherent` を構成。

**🔍 open question (次セッションで解決)**: (5.7) 原文の「χ(1) independent」が証明本体のどこで効くか未特定
(読んだ範囲は orthogonality 主体)。repo の `IsCoherent` は degree を持たないので、等次数仮説が
(a) retarget engine の前提に必要 / (b) member ごとの ‖χ‖² 一致に必要 / (c) Pf の他箇所での (5.7) 用途
(等次数 family) 由来で本 assembly には不要、のどれか。**実装時に retarget engine の前提を読み確定**。
faithful には signature に含める (Pf が STATE)。

## 3. 生産先 + signature (本セッションで skeleton 設置)

**新 leaf = `OddOrder/Peterfalvi/S07_CoherenceConstantDegree.lean`** (import `S07_Coherence`、既存 S07-S08
本体は触らず cite のみ — lane-b dormant 領域の衝突回避)。standalone:

```lean
-- namespace OddOrder.Peterfalvi.S07
theorem coherent_of_constant_degree
    (hyp : Hypothesis (L := L) (G := G) S A)
    (hconst : ∀ χ ∈ S, ∀ ψ ∈ S, χ 1 = ψ 1)        -- (5.7) 等次数
    (hne : ∃ φ : ClassFunction L ℂ, φ ∈ zSupportedSpan S A ∧ φ ≠ 0) :
    Nonempty (IsCoherent hyp.tau S A)
```

(degree `χ 1` の正確な綴り = ClassFunction 評価、実装時確認。)

## 4. consumer wiring (S13 (11.5)、別ステップ)

`HC_le_secondDerived` (11.5) は `Nonempty (IsCoherent hyp.base.tau (hyp.SOf M'') hyp.base.A0)` を要する。
(5.7) を使うには **S(M'') に対する `Hypothesis (5.2)` instance の構成**が要る (Dade τ / R(χ) (5.2.d) /
orthogonality)。これは §13/§4 Dade machinery で、(5.7) producer とは別の consumer-side 仕事。(5.7) landing
後に S13 側で組む (lane-c 自所有)。等次数は M'/M'' abelian から (S(M'') の characters が linear lift)。

## 6. 実装 deep-dive (本セッション続行で engine 経路を確定)

retarget engine を精読し、(5.7) 実装の正確な経路と労力を確定:

**🔑 engine は完全 inductive、repo に base case 無し**:
- `retarget_isCoherent` (core, S07:3262) / `retarget_isCoherent_of_decomposition` (:3737) /
  `_of_decompositions` (:3911) / `_and_memberFamily` (:3979) は**全て `hS₁ : IsCoherent τ S₁ A` を要求** =
  「coherent な S₁ に共役ペア `{χ,χ̄}` を 1 つ足す」inductive step。
- ∴ (5.7) 実装は **(I) base case (single-pair coherence を scratch から) + (II) induction wrapper +
  (III) per-step hypothesis discharge** の 3 部。repo は (II)(III) の step engine は持つが (I) base case と
  full-induction wrapper は**無い** (lane-h の (6.2)/(6.3) と同様、producer が新規に組む)。

**🔑 等次数の役割 = `a=1`**: engine の `Da : CharacterPsiDecomposition τ χ (a • chi1)` の `a` は次数比
`χ(1)/χ₁(1)`。**等次数 ⟹ a=1** ⟹ `χ - a•χ₁ = χ - χ₁`、`hY : Da.Y = a•Da.tau1 χ₁` が `Y = χ₁^{τ₁}` に
簡約。これが Pf (5.7) が等次数を使う箇所 (open question 解決)。member は irreducible (`‖χ‖²=1`、engine の
`hχχ : inner χ χ = 1`) を要し、consumer の `S ⊆ Irr L` ((5.3.a)) が供給する ⟹ signature に
`hirr : ∀ χ ∈ S, inner χ χ = 1` (or `S ⊆ Irr L`) を足すのが faithful + provable。

**(I) base case = single-pair coherence (次セッション最初の sub-goal、構成は確定)**:
`IsCoherent τ {χ,χ̄} A` を `CharacterDifferenceImage hχ` (5.2.d) から構成。
**🔑 `IntegralCharacterMap L G = ClassFunction L ℂ →ₗ[ℤ] ClassFunction G ℂ` (ただの ℤ-linear map、S07:301)**
ゆえ heavy bundle でない。repo に既存の **`innerLeftℤ η` (= `φ ↦ ⟨φ,η⟩` の ℤ-linear functional, S07:2631)**
+ `LinearMap.smulRight` で extension を直接構成:
- `extension := (innerLeftℤ χ).smulRight (hχ.sign • (hχ.mu : ClassFunction G ℂ))`
  `        + (innerLeftℤ χ̄).smulRight (hχ.sign • (hχ.nu : ClassFunction G ℂ))`
  (i.e. `φ ↦ ⟨φ,χ⟩•(ε•μ) + ⟨φ,χ̄⟩•(ε•ν)`, ε=sign)。検算: `χ↦ε•μ`, `χ̄↦ε•ν`、
  `(χ-χ̄)↦ε•(μ-ν)=τ(χ-χ̄)` (`image_eq`) ✓ (要 ‖χ‖²=1, χ⊥χ̄)。
- `nonzero` = `χ-χ̄` (`chi_sub_conj_mem_zSpan_support` S07:1315 で supported、≠0 by (5.2.a) χ̄≠χ)。
- `extension_mem_ZIrr` = `μ,ν ∈ ZIrr` (`hχ.mu.mem_ZIrr`) の ℤ-combo (`Submodule.smul_mem`/`add_mem`、
  S07:907 パターン)。
- `extension_inner_eq` (isometry) = orthonormal-basis Parseval: φ,ψ∈`zSpan{χ,χ̄}`=`span_ℤ{χ,χ̄}` を
  `Submodule.mem_span_pair` で `φ=aχ+bχ̄` 表現 → `⟨φ,ψ⟩=⟨φ,χ⟩conj⟨ψ,χ⟩+⟨φ,χ̄⟩conj⟨ψ,χ̄⟩`
  (χ⊥χ̄,‖χ‖²=1) と ext の Gram (`⟨εμ,εμ⟩=ε²=1`,`⟨εμ,εν⟩=0`) が一致。
- **⚠ `extends_on_supported` subtlety (本セッション発見)**: ext は **χ-χ̄ 上でのみ** τ と一致 (χ,χ̄ 個別の τχ は
  `image_eq` から不明)。∴ `zSupportedSpan{χ,χ̄}A ⊆ span_ℤ{χ-χ̄}` が要る。これは `Hypothesis (5.2)` が **A を
  constrain しない** (構造体に A field 無し) ゆえ **追加 hypothesis or 導出が必要** — repo engine も同型の制御を
  `hgen` (`zSupportedSpan(S₁∪{χ,χ̄})A ⊆ span(… ∪ {χ-χ̄,…})`) で要求。base-case lemma に
  `hsupp : zSupportedSpan{χ,χ̄}A ⊆ Submodule.span ℤ {χ-χ̄}` を足す (Pf 設定では A=L^#, χ(1)≠0 ゆえ
  a+b=0 強制で成立; standalone では hyp 化)。**⟹ base-case signature に `hsupp` 追加が必要**。
- `extension_mem_ZIrr` = ℤ-combo of μ,ν∈ZIrr。容易。
- **~100-130 行、本 producer の core 労力** (extension 構成は確定、isometry は Parseval、supported は hsupp 制御)。

**(II)(III) induction**: S の共役ペア集合上で `Finset.induction`、各 step で `retarget_isCoherent_of_
decompositions_and_memberFamily` を a=1 で適用。per-step discharge (D₀/Da 構成、hY collapse、member family
orthogonality) が (III)、各々 (5.4)/(5.5) helper で組む。

**⟹ 労力見積 = lane-h (6.2)/(6.3) 級の focused implementation session** (base plumbing + induction +
discharge)。本セッション (resume + (11.6) win + relane + (5.7) deep scoping) は容量大ゆえ、(I) base case の
IntegralCharacterMap 構成から次セッションで着手。建てた signature は cite-ready (sorried、[[feedback-cite-sorried-lemmas-if-signature-correct]])。

## 5. 状態

- ✅✅✅ **(5.7) producer COMPLETE (sorry-free + axiom-clean、AxiomsCheck 登録)** — `coherent_of_constant_degree`
  本体まで完遂。**設計を engine 反復 (II)(III) から「Peterfalvi 原文どおり一発構成」に切替**: (5.7) 原文は
  inductive な `retarget` chain でなく、補助等長 `τ₁` を **χ₀↦β, χⱼ↦β−(χ₀−χⱼ)^τ** で一発に建てる。等次数ゆえ
  差は全 supported → `tau1=τ` (固定 Dade 写像) で全分解が建ち、running-extension/Gram–Schmidt 残差は不要。
  ⟹ engine (`retarget_isCoherent_of_*`) は **不使用**、代わりに既存 `coherentEqualDegree` (= (1.1)+(1.4)
  等次数 coherence) に X-family を投入。
- 実装 (S07_CoherenceConstantDegree.lean):
  - **base case** `isCoherent_pair_of_differenceImage` (single pair、(5.2.d))。
  - **H1** `pairDecomp`/`pairDecomp'` (DiffPair 版、`ofProjection` tau1=τ) + `inner_X_X'_eq_zero`。
  - **H2** `pairDecomp_two_sided` (最難所): 異ペア χ,ζ で `‖D.X‖²=1 ∧ D.Y=D'.X` を正定値性で実証明
    ((5.4.b) 両側、Bessel/CS 不要)。
  - **H3** `commonImage` (β = R(χ₀)-射影、基準 ζ₀) + (A) `commonImage_self` `⟨β,β⟩=1` + (B)
    `commonImage_inner` `∀ζ≠χ₀, ⟨β,(χ₀−ζ)^τ⟩=1` (独立性 4 ケース: χ̄₀/ζ₀/ζ̄₀/第3ペア)。
  - **H4** `xFamily_inner` `⟨Xᵢ,Xⱼ⟩=⟨χᵢ,χⱼ⟩` (τ₁ 等長) + `CharacterPsiDecomposition_X_mem_ZIrr`。
  - **H5** `coherent_of_constant_degree`: 単一ペア→base case / |S|≥4→Fin n 列挙+commonImage+coherentEqualDegree。
- **faithful signature**: `(hyp : Hypothesis S A)(hSfin)(hcard:2≤S.ncard)(hirr:S⊆Irr)(hZIrr:τ supported diff
  →ℤ[Irr G])(hconst:等次数)(hdeg0)(h1A:1∉A)(hsuppdiff)`。Dade-side の hZIrr/hsuppdiff/h1A は **§13 consumer が
  discharge** (= base map が ℤ[S,L^#]→ℤ[Irr G]、Pf 設定で自明)。`hne` は不要 (coherentEqualDegree/base が内部供給)。
- 🔑 **engine deep-dive (§6) の (II)(III) 路線は不採用** — engine は running-extension を tau1 に要求し
  Gram–Schmidt 残差で重い。一発構成は tau1=τ で軽量、これが原文に忠実かつ Lean で最短だった。
- ⏭ **次 = consumer wiring (S13 (11.5) `HC_le_secondDerived`)**: `S(M'')` に対する `Hypothesis (5.2)`
  instance を §13/§4 Dade machinery で構成し (Dade τ / R(χ) (5.2.d) / orthogonality + 上記 Dade-side hyp)、
  (5.7) を cite。等次数は M'/M'' abelian から (S(M'') の linear lift)。producer とは別の consumer-side 仕事。
- 関連: lane-h `S08_Theorem62_63_Standalone.lean` (template)、issue 4012 (relane #8, RESOLVED 条件達成)、
  issue 2018 ((11.5) gate)、S13 `HC_le_secondDerived`。
