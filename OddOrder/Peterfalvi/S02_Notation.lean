/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S01_Introduction

/-!
# Peterfalvi §2: Notation

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Chapter §2 (pp. 3-4, mmd 40 行) の Lean 化.

**結果数**: 0 (本節は記号定義のみ. 番号付き結果なし.)

形式化先 (本ファイル): `OddOrder/Peterfalvi/S02_Notation.lean` — 記号対応表 (docstring)
+ mathlib alias notation. 実体定義の大半は §3 以降または Wave 1a shared modules で.

ROADMAP 位置: **Phase 2b 第 1 波** (前提なし, BG 並行可).

## §2 の役割

Peterfalvi §2 は本書全 16 節 + 5 付録の **記号・用語の統一辞書**. 指標論・加群・
部分群構造に関わる 40+ の記号を定義. 本ファイルは:

1. **記号対応表** (Peterfalvi ↔ mathlib v4.29.1 ↔ 本プロジェクト Wave 1a) を提示
2. **直接対応可能な notation alias** を提供 (mathlib API が揃っている場合のみ)
3. **新規定義は Wave 1a shared modules または §3 以降に委ねる** (定義 location 統一)

## 記号対応表 — 指標論

⚠️ audit 訂正 (2026-05-23): 旧 per-section ノートの「mathlib 既存」評価は
overstated. 以下は実状況:

### 既約指標集合 `Irr(G)` / `IrrG`

```
Peterfalvi: Irr(G) := { χ : G → ℂ | χ is irreducible character }
```

- **mathlib v4.29.1**: `FDRep k G` (有限次元表現), `character` (`FDRep k G → G → k`)
  はあるが、**`Irr G` を 1 つの Finset/型として明示する API は限定的**.
- **Wave 1a**: `OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean`
  + `ZIrr.lean` で整備予定.

### 類関数空間 `CF(G)` / `CF(G, A)`

```
Peterfalvi:
  CF(G) := { φ : G → ℂ | φ is class function }
  CF(G, A) := { φ ∈ CF(G) | Supp(φ) ⊆ A }   -- A-supported class functions
```

- **mathlib v4.29.1**: ⚠️ audit 訂正 (旧記載「`ClassFunction G` 既存」は誤り):
  conj-invariant submodule としての `ClassFunction G` 型は **完全に不在**.
  `FDRep.character : G → k` という個別関数のみ.
- **Wave 1a**: `OddOrder/GroupTheory/RepresentationTheory/ClassFunction.lean` (~150 LOC)
  で新規定義予定 (§3-§8 全節で使用).

### 内積 `(α, β)_G`, ノルム `‖α‖²`

```
Peterfalvi:
  (α, β)_G := (1/|G|) Σ_{g ∈ G} α(g) · β(g)̄
  ‖α‖² := (α, α)
```

- **mathlib v4.29.1**: `char_orthonormal` (`irreducible のみ`) はあるが、
  CF 全体への inner product extension は **要 Wave 1a**.
- **Wave 1a**: `ClassFunction.lean` の一部.

### 仮想指標 `Z[Irr G]`, `Z[Irr G, A]`

```
Peterfalvi:
  ℤ[Irr G] := ℤ-線形結合 of Irr(G) (virtual character lattice)
  ℤ[Irr G, A] := ℤ[Irr G] ∩ CF(G, A)
```

- **mathlib v4.29.1**: ⚠️ audit 訂正: **完全不在**. `Submodule ℤ ...` で組めるが
  Peterfalvi 流名前空間で統一されていない.
- **Wave 1a**: `OddOrder/GroupTheory/RepresentationTheory/ZIrr.lean` (~80 LOC).

### 誘導指標 `Ind_H^G χ` / `Res_H^G ψ`

```
Peterfalvi:
  Ind_H^G χ (g) := (1/|H|) Σ_{x ∈ G : x⁻¹gx ∈ H} χ(x⁻¹gx)  -- classical formula
  Res_H^G ψ := ψ |_H                                          -- restriction
```

- **mathlib v4.29.1**: ⚠️ audit 訂正 (旧「Induced character 既存」は誤り):
  `Mathlib/RepresentationTheory/Induced.lean` は **categorical `IndV` (coinvariants)**
  のみ. classical numerical formula は **不在**.
- **Wave 1a**: `OddOrder/GroupTheory/RepresentationTheory/InducedCharacter.lean`
  (~200 LOC) で classical formula + numerical Frobenius reciprocity 整備.

### 慣性群 `I_G(θ)`

```
Peterfalvi: I_G(θ) := { g ∈ G | θ^g = θ }  for θ ∈ Irr(H), H ≤ G
```

- **mathlib v4.29.1**: 不在. (Clifford theory 一式が mathlib 未整備のため.)
- **Wave 1a**: `OddOrder/GroupTheory/RepresentationTheory/Inertia.lean` (~100 LOC).

## 記号対応表 — 群論

### Frobenius 構造記号

```
Peterfalvi:
  H ⋊ K : Frobenius group with kernel H, complement K
  H^# := H \ {1} : non-identity elements
```

- **mathlib v4.29.1**: `SemidirectProduct H K φ` は既存だが Frobenius 構造 (固定点自由
  作用) の明示 predicate は限定的. Isaacs Ch.6 (Phase 1) で形式化中.

### Fitting 系記号

```
Peterfalvi:
  F(G) : Fitting subgroup
  O_p(G), O_{p'}(G) : maximal normal p-(p'-)subgroup
```

- **mathlib v4.29.1**: `Subgroup.piCore` (= O_{π'}) はある. `Fitting subgroup`
  そのものは Phase 1 Isaacs Ch.2 で実装中.

### TI-subset

```
Peterfalvi: A ⊂ G が TI ⟺ ∀ g ∈ G, A^g ∩ A ≠ ∅ ⟹ g ∈ N_G(A)
```

- **mathlib v4.29.1**: ⚠️ audit 訂正: `MulAction.IsBlock.IsTrivialBlock` は別概念.
  TI-subset 概念は **完全不在**.
- **Wave 1a**: [`OddOrder.GroupTheory.IsTISubset`](../GroupTheory/TISubset.lean)
  ✅ **新規実装完了** (本 commit / 別 commit) — Phase 2b 第 1 波最初の shared module.

## 記号対応表 — 新規 Peterfalvi 概念

### Dade isometry `τ` (§4)

§4 (2.5) で定義される map `τ : CF(L, A^#) → ClassFunction G` (実体は §4 で形式化).
mathlib v4.29.1 完全未収載. Phase 2b 第 2 波の山場.

### Coherence (§7)

§7 (5.1) で定義. `τ` の `Z[S]` 全体への isometric 拡張存在性. mathlib v4.29.1 完全
未収載. ⚠️ audit 訂正: 旧記載「(5.1) 定義に character difference rider」は誤り
(rider は (5.9.b) の結論). 詳細: [`notes/peterfalvi/s07_coherence.md`](../../notes/peterfalvi/s07_coherence.md).

## 本ファイルでの notation 提供方針

**現状**: mathlib v4.29.1 で対応 API が薄いため、本ファイルでは alias 定義を
最小限に留め、Wave 1a shared modules + §3 以降の実体定義に委ねる. notation 統一は
Wave 1a 完成後に再着手予定.

将来予定の notation:

```lean
-- 後日 Wave 1a 完成後に追加予定:
-- notation "CF(" G ")" => ClassFunction G ℂ
-- notation "CF(" G "," A ")" => ClassFunction.support_subset G A
-- notation "ℤ[Irr " G "]" => ZIrr G
-- notation "Ind_" H "^" G χ => InducedCharacter H G χ
-- notation "(" α ", " β ")_" G => inner_class_function α β G
```

## 関連ノート

- 全体: [`notes/peterfalvi/_overview.md`](../../notes/peterfalvi/_overview.md)
- §1+§2 詳細: [`notes/peterfalvi/s01s02_intro_notation.md`](../../notes/peterfalvi/s01s02_intro_notation.md)
- §3-§8 audit (mathlib 対応訂正): [`notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md`](../../notes/meta/peterfalvi_phase2b_wave1_audit_2026_05_23.md)
- Wave 1a 計画 (上記 audit §6.1): 11 modules ~1100 LOC, `OddOrder/GroupTheory/RepresentationTheory/` 配下に逐次配置中
-/

namespace OddOrder.Peterfalvi.S02

-- §2 は記号定義のみ. 形式化対象は notation alias と若干の helper.
-- 現状 mathlib API が薄いため、本ファイルでは alias 定義なし.
-- Wave 1a 完成後に再着手予定.

end OddOrder.Peterfalvi.S02
