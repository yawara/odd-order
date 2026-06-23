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

## 5. 状態

- ✅ 本セッション (scoping): 框組確認 + 設計 + scoping note + standalone signature skeleton 設置。
- ⏭ 次セッション (実装): `coherent_of_constant_degree` を retarget engine + (5.5) で実証明
  (base case → inductive member 分解 → retarget)。open question (等次数の用途) を engine 前提で確定。
- 関連: lane-h `S08_Theorem62_63_Standalone.lean` (template、h62 oracle pattern)、
  issue 4012 (relane #8)、issue 2018 ((11.5) gate)、S13 `HC_le_secondDerived`。
