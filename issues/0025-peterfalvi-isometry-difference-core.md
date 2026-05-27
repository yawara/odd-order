---
id: 25
slug: peterfalvi-isometry-difference-core
title: "Peterfalvi Part I: isometry difference-pair の combinatorial core を証明する"
created: 2026-05-25
---

# Peterfalvi Part I: isometry difference-pair の combinatorial core を証明する

## 背景

`issues/0024-peterfalvi-isometry-difference-pair.md` から分割した proof core。
`isometry_difference_pair_structure` の statement と §7 coherence 側 interface は
整ったが、証明本体は以下の 2 層をまだ必要とする。

1. `IrreducibleCharacter G` を finite orthonormal index として使い、second
   orthogonality から class-function basis coefficient を取り出す層。
2. `τ (χ_i - χ_0)` の integer coefficients と norm/inner-product constraints
   だけを使って、全ての差分が同じ符号 `ε • (μ_i - μ_0)` になることを示す
   finite combinatorial induction 層。

この issue は後者の core を独立させ、前者の character-theory API と混ぜずに
証明できる形へ切る。

## やること

- [x] integer coefficient vector 用の小さな structure / predicate を決める。
- [x] **statement-level gap を埋める**: `IsometryDifferenceImagesAreVirtual τ χ` predicate を
      `IsometryDifferenceImagesVanishAtOne` と並べて追加し,
      `isometry_difference_pair_structure` に `h_image_virtual` 仮説を組み込んだ。
      これで Peterfalvi 原文 (1.4) の `τ : ℤ[X, H^#] → ℤ[Irr G]` 条件が
      Lean statement に表現される。S07 consumer 側の patch は invoke 時点で行う
      (現状 invoke 無し)。
- [x] **prerequisite lemma 1 (層 1b 完了)**:
   `IrreducibleCharacter.inner_self = 1` と `inner_eq_zero_of_ne` の bridge.
   → `characterTableRowOrthogonality` (`RowOrthogonality.lean`) で証明し、
   IsometryDifferencePair / S07 の inner-product helper を全て無条件化した。
- [ ] **prerequisite lemma 2 (層 2)**:
   `ZIrr G` Fourier 基底展開: 各 `φ ∈ ZIrr G` は `∑ c_χ · χ` 唯一展開で
   `c_χ = ⟨φ, χ⟩` (`ZIrr.lean:46-47` の TODO に該当, ~100-200 LOC).
   全張る性 (spanning) は不要、orthonormality + 一次独立で済む (handoff 参照)。
- [ ] `n = 2` の norm `2` case を証明する.
- [ ] `n = 3` の common component 共有 case を証明する.
- [ ] induction step で uniform sign が崩れる `e₂ + e₃` case を degree 条件で排除する.
- [ ] core lemma を `isometry_difference_pair_structure` に戻して `sorry` を消す.

合計推定: ~400-750 LOC of new bridges + combinatorial induction.
**`column_orthogonality_cases` (#27) は不要** (row orthogonality だけで済む).

## 2026-05-26 update

- `SignedIrreducibleDifferenceFamily G n` を追加し、結論側の
  `μ : Fin n → Irr(G)` と uniform sign `ε = ±1` を structure 化した。
- `isometry_difference_pair_structure` の input/output を raw `ClassFunction`
  tuple から `IrreducibleCharacter` index と `SignedIrreducibleDifferenceFamily`
  に揃えた。
- `SignedIrreducibleDifferenceFamily.classFunction_injective`,
  `classFunction_ne`, `classFunction_irreducible` を追加した。
- §7 の `CharacterDifferenceImage` も `mu`, `nu` を raw `ClassFunction` ではなく
  `IrreducibleCharacter G` として持つ形に揃えた。
- `SignedIrreducibleDifferenceFamily.difference` と `signedDifference` を追加し、
  基準成分 `μ_i - μ_0`、符号付き差分、`difference_ne_zero`,
  `sign_ne_zero`, `sign_mul_self` を名前付き API にした。
- `signedDifference_ne_zero` と `signedDifference_eq_zero_iff` を追加し、結論側の
  signed target difference が `i = 0` でのみ消えることを `sorry` なしで使えるようにした。
- `difference_injective`, `signedDifference_injective`,
  `signedDifference_eq_signedDifference_iff`, `signedDifference_ne` を追加し、
  §3 (1.4) の結論側 target tuple が符号付き差分に移った後も index の区別を
  失わないことを `sorry` なしで使えるようにした。
- `difference_eq_zero_iff`, `signedDifference_eq_difference_or_neg`, and
  `sign_smul_signedDifference` を追加し、uniform sign を外す後続計算を
  unfold なしで進められるようにした。
- `ClassFunction.innerSum_sub_left/right` と `inner_sub_left/right` を追加し、
  `χ_i - χ_0` 型の差分内積を後続 proof core で直接展開できるようにした。
- `SignedIrreducibleDifferenceFamily.classFunction_inner_eq_if`,
  `difference_inner_self_of_ne_zero`, `difference_inner_of_ne_zero_of_ne`,
  `signedDifference_inner_signedDifference`,
  `signedDifference_inner_self_of_ne_zero`, and
  `signedDifference_inner_of_ne_zero_of_ne` を追加し、row orthogonality input
  の下で target side の norm `2` と distinct nonzero difference inner product
  `1` を unfold なしで取り出せるようにした。
- `irreducibleCharacter_inner_eq_if`,
  `irreducibleCharacter_difference_inner_self_of_ne_zero`, and
  `irreducibleCharacter_difference_inner_of_ne_zero_of_ne` を追加し、input side
  の `χ_i - χ_0` についても同じ norm `2` / inner `1` values を named API
  として取り出せるようにした。
- §7 の two-element `CharacterDifferenceImage` 側にも `difference`,
  `signedDifference`, `image_eq_signedDifference`,
  `difference_inner_self`, `signedDifference_inner_self`,
  `image_conjugateDifference_inner_self`, and
  `Orthogonal.image_conjugateDifference_inner_eq_zero` を追加し、(5.2.d/e)
  の image norm `2` と image-set 直交性を hypothesis carrier から直接使える
  ようにした。
- `irreducibleCharacterDifference` と `isometryDifferenceImage` を追加し、
  §3 (1.4) の source difference とその `τ` image を名前付きにした。
  `isometryDifferenceImage_inner_self_of_ne_zero` と
  `isometryDifferenceImage_inner_of_ne_zero_of_ne` により、`h_isom` と source
  row orthogonality から image 側 norm `2` / mutual inner `1` を直接取り出せる。
  `isometry_difference_pair_structure` の statement もこの named interface へ寄せた。
- `irreducibleCharacterDifference_apply_one_of_same_degree`,
  `IsometryDifferenceImagesVanishAtOne`, and
  `SignedIrreducibleDifferenceFamily.signedDifference_apply_one_eq_zero_iff` を追加した。
  §3 (1.4) の `e₂ + e₃` 除外で使う degree-zero 条件を明示し、
  `isometry_difference_pair_structure` には image 側 `τ(χ_i-χ_0)(1)=0` 仮定を追加した。
- `IsometryDifferencePairNumerics` を追加し、zero row, degree-zero, nonzero
  difference norm `2`, distinct nonzero mutual inner `1` を finite combinatorial
  core 用の単一 predicate にまとめた。
  `isometryDifferencePairNumerics_of_isometryDifferenceImage` で `h_isom` と source
  row orthogonality から image 側 numerics を作り、
  `SignedIrreducibleDifferenceFamily.numerics_of_signedDifference_vanishAtOne` で
  target signed family から同じ numerics を取り出せる。
- proof core は引き続き `n = 2`, `n = 3`, induction step の finite
  combinatorial argument。

## 2026-05-28 progress: 層 1a 完了 (CharacterConjugate)、1b が次 — HANDOFF

**Branch**: `peterfalvi-s09` (本作業は §9 → §3 経由の前提として同ブランチで進行中).

### 全体の層構造 (bottom-up, ユーザー合意の攻め順)

`isometry_difference_pair_structure` (`IsometryDifferencePair.lean:674` の sorry) を埋めるには:

- **層 1a** `χ(g⁻¹) = conj(χ(g))` — ✅ **完了** (commit `d9330fa`).
  `OddOrder/GroupTheory/RepresentationTheory/CharacterConjugate.lean`,
  `theorem OddOrder.RepresentationTheory.character_inv`. sorry-free, OddOrder に wiring 済.
  証明: 固有値を使わず **行列 S-ユニタリ・トリック** (基底で `Mₕ=toMatrix(ρ h)`,
  `S=∑ₕ MₕᴴMₕ` PosDef, `Mᴴ S M=S`, `M⁻¹=S⁻¹MᴴS`, trace 巡回 + `trace_conjTranspose`).
- **層 1b** orthonormality discharge — ⬜ **次の着手点** (recipe 下記).
- **層 2** ZIrr Fourier/係数 API — ⬜.
- **層 3** combinatorial core (n=2/3/帰納) — ⬜.
- → §3 (1.4) `isometry_difference_pair_structure` の sorry 解消.

### 層 1b 着手 recipe (orthonormality discharge)

**目標**: `CharacterTableRowOrthogonality (G := G)` (`SecondOrthogonality.lean:668`) を
*仮説でなく定理として* 証明 → S07 / IsometryDifferencePair の `hrow` 仮説を全て discharge.

`CharacterTableRowOrthogonality` = `(∀ χ, characterTableRowPairing χ χ = 1) ∧ (∀ χ ψ, χ≠ψ → ... = 0)`.
`characterTableRowPairing χ ψ = ⅟(card:ℂ) * ∑ g, (χ:CF) g · star((ψ:CF) g)` (`_eq_inv_card_sum`, L656).

```lean
-- 配置案: 新ファイル RowOrthogonality.lean (CharacterConjugate + SecondOrthogonality を import)
--   ※ SecondOrthogonality.lean 本体に足すと CharacterConjugate→…→循環の恐れ要確認
theorem characterTableRowOrthogonality {G} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] : CharacterTableRowOrthogonality (G := G) := by
  refine ⟨fun χ => ?_, fun χ ψ hχψ => ?_⟩
  · -- 対角 = 1
    obtain ⟨V,_,_,_, ρ, hρ, hχ⟩ := χ.isIrreducible
    haveI : Representation.IsIrreducible ρ := hρ
    -- pairing を ⅟card·∑ ρ.char g · star(ρ.char g) に直し、
    -- character_inv で star(ρ.char g)=ρ.char g⁻¹、char_orthonormal ρ ρ で =1。
  · -- 非対角 = 0
    obtain ⟨Vχ,_,_,_, ρ, hρ, hχ⟩ := χ.isIrreducible
    obtain ⟨Vψ,_,_,_, σ, hσ, hψ⟩ := ψ.isIrreducible
    haveI := hρ; haveI := hσ
    -- char_orthonormal ρ σ で if Nonempty(σ.Equiv ρ) then 1 else 0。
    -- Equiv σ ρ → σ.character=ρ.character (Representation.char_iso) → (ψ:CF)=(χ:CF) → χ=ψ で矛盾 → 0。
```

**使う mathlib 補題**:
- `Representation.char_orthonormal [IsIrreducible ρ] [IsIrreducible σ] [Fintype G] [Invertible (Nat.card G:ℂ)] [IsAlgClosed ℂ] : (Nat.card G:ℂ)⁻¹ * ∑ g, ρ.character g * σ.character g⁻¹ = if Nonempty (σ.Equiv ρ) then 1 else 0` — `Mathlib/RepresentationTheory/Character.lean:230`.
- repo `character_inv ρ g : ρ.character g⁻¹ = star (ρ.character g)` (層 1a) — `star ↔ g⁻¹` の橋渡し.
- `Representation.char_iso (φ : ρ.Equiv σ) : ρ.character = σ.character` — `Character.lean:171` (非対角の矛盾用).
- `characterTableRowPairing_eq_inv_card_sum` — `SecondOrthogonality.lean:656`.
- `⅟(card:ℂ) = (card:ℂ)⁻¹`: `invOf_eq_inv`.

**型/インスタンスの注意 (1a で踏んだ罠の再掲)**:
- `IrreducibleCharacter G := {φ : ClassFunction G ℂ // IsIrreducibleCharacter φ}` (`IrrIndexing.lean:28`).
  `χ.isIrreducible : IsIrreducibleCharacter (χ:CF)`,
  `IsIrreducibleCharacter φ := ∃ V _ _ _ (ρ : Representation ℂ G V), Representation.IsIrreducible ρ ∧ (φ:G→ℂ)=ρ.character`.
  `(χ:CF) g = ρ.character g` は `hχ` を `congrFun`/funext で適用.
- `char_orthonormal` は `[IsIrreducible ρ]` を **instance** 要求 → `haveI : Representation.IsIrreducible ρ := hρ`.
- `[Invertible (Nat.card G:ℂ)]`: `CharacterTableRowOrthogonality` 仮説に既出 → 定理にも同仮説で OK. 常時 discharge したいなら `invertibleOfNonzero` で構成.
- `[IsAlgClosed ℂ]` を char_orthonormal が要求 → 適切な import (`Mathlib.Analysis.SpecialFunctions.Complex.Circle` 系か `Complex.isAlgClosed`).
- `χ ≠ ψ` (Subtype) → `(χ:CF) ≠ (ψ:CF)`: `fun h => hχψ (Subtype.ext h)`.
- **ℂ 一般の罠 (1a で判明)**: `open scoped ComplexOrder` は順序/PosDef 用 (1b では不要のはず); `RCLike ℂ` インスタンスは `Mathlib.Analysis.Complex.Basic` 由来 (RCLike.Basic でない).

**進め方**: まず `characterTableRowOrthogonality` 定理単体を green + commit. その後、`hrow` を取る箇所 (S07 (5.x) / numerics / 最終的に (1.4)) に供給して仮説を消すのは段階的に.

### mathlib ギャップ (層 2-3 で再燃する確認済み事実)
- mathlib に「既約指標が類関数の基底」「#Irr=#共役類」は **無い**. ただし **層 2 (ZIrr Fourier) は orthonormality + 一次独立で済み、全張る性 (spanning) は不要** (`v_i ∈ ZIrr` の span membership のみ使う) — これは朗報.
- 「trace=固有値和 (重複度付)」「spectral mapping」「trace_adjoint」「群平均ユニタリ化」も mathlib 不在 (層 1a はこれらを S-ユニタリ行列トリックで回避).

### このセッションの commit (peterfalvi-s09 ブランチ、いずれも未 push)
- `39a3ccb` docs: §9 ノート訂正 (§9 は character-theoretic、App.C 内容との混同を除去)
- `72a9864` Peterfalvi S09: (7.10)/(7.11) statements; (7.11) を (7.10) modulo で sorry-free 証明
- `d9330fa` CharacterConjugate: `χ(g⁻¹)=conj χ(g)` (層 1a)

## 2026-05-28 progress (cont.): 層 1b 完了 — 層 2 が次

**層 1b (orthonormality discharge) を完了**した (3 commit、`peterfalvi-s09`、未 push):

- `893a502` `characterTableRowOrthogonality` を *定理として* 証明
  (新ファイル `OddOrder/GroupTheory/RepresentationTheory/RowOrthogonality.lean`)。
  recipe 通り: mathlib `Representation.char_orthonormal` (引数 `σ.char g⁻¹` 形) を
  `character_inv` (層 1a, `star ↔ g⁻¹`) で Peterfalvi の複素共役内積
  `characterTableRowPairing` に橋渡し。対角 `1` は `Representation.Equiv.refl`、
  非対角 `0` は `Equiv σ ρ` から `char_iso` で両指標 (→指標 index) が一致して矛盾。
  RowOrthogonality は **leaf** (SecondOrthogonality + CharacterConjugate のみ import、
  循環なし)、`OddOrder.lean` に wiring 済。
- `c9ab339` `IsometryDifferencePair.lean` の 13 inner-product helper から `hrow`
  仮説を除去 (定理を内部で invoke、`(G:=G)`/`(G:=H)` 両方 OK、`Finite` は `Fintype`
  から derived)。norm `2` / mutual-inner `1` の numeric API が無条件化。
- `3599d95` `S07_Coherence.lean` の 4 つの `CharacterDifferenceImage` norm helper
  からも `hrow` を除去。

**注意 (scope)**: `SecondOrthogonality.lean:1044`
(`column_orthogonality_cases_ofRowOrthogonality`) 等の `hrow` は **column
orthogonality (#27、本 issue で「不要」と明記) 用なので対象外**。かつ
SecondOrthogonality←RowOrthogonality の依存があるため逆 import は循環で discharge 不可
(正しく conditional のまま残す)。

**層構造の現状**: 1a ✅ / 1b ✅ / 層 2 (ZIrr Fourier) ⬜ / 層 3 (combinatorial core) ⬜。

### 層 2 着手 recipe (ZIrr Fourier 係数 API) — 次の着手点

**目標**: `φ ∈ ZIrr G` を既約指標の `ℤ`-一次結合に一意展開し、係数を内積
`c_χ = ⟨φ, χ⟩` で取り出す API。これで `τ(χ_i-χ_0)` (∈ `ZIrr G`, `h_image_virtual`)
の各既約成分の整数係数を取り出せ、層 3 の combinatorial core に渡せる。

- `characterTableRowOrthogonality` が **使える前提**になった (層 1b の成果):
  `ClassFunction.inner χ ψ = δ` を無条件に使える。
- **spanning は不要**: `v_i ∈ ZIrr` の span membership から得る有限台の
  `ℤ`-結合 (`Submodule.span` の `mem_span` 展開) に対し、orthonormality で
  係数 = 内積を取り出すだけ。`#Irr = #conjclasses` や「既約が類関数の基底」は不要
  (mathlib にも無い、handoff 参照)。
- 配置案: `ZIrr.lean` に Fourier 係数補題を足す or 新ファイル。
  `ZIrr.lean:46-47` の TODO 参照。

## 完了条件

- `OddOrder.RepresentationTheory.isometry_difference_pair_structure` の proof core が
  独立 lemma として statement 化される、または同 theorem から `sorry` が消える。
- `lake build OddOrder.GroupTheory.RepresentationTheory.IsometryDifferencePair` が通る。
- `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` が通る。

## 参照

- parent: `issues/0024-peterfalvi-isometry-difference-pair.md`
- depends on: `issues/closed/0021-peterfalvi-second-orthogonality.md`
- depends on: `issues/0027-peterfalvi-column-orthogonality-core.md`
- `OddOrder/GroupTheory/RepresentationTheory/IsometryDifferencePair.lean`
- `OddOrder/GroupTheory/RepresentationTheory/IrrIndexing.lean`
- `OddOrder/GroupTheory/RepresentationTheory/SecondOrthogonality.lean`
- `notes/peterfalvi/s03_preliminary_character.md`
- `notes/peterfalvi/s07_coherence.md`
