/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Solvable

/-!
# Schur-Zassenhaus conjugacy (axiom)

mathlib v4.29.1 は `Subgroup.exists_right_complement'_of_coprime` (任意 normal Hall 部分群
の complement 存在) を public で提供するが, **complement の N-共役性は abelian case のみ**
(`Subgroup.exists_smul_eq` via `QuotientDiff` action, `SchurZassenhaus.lean:100`).

本ファイルは general SZ conjugacy を **暫定 axiom** として記載する.

## 使用箇所

* `OddOrder/GroupTheory/CoprimeAction.lean` Lemma 3.24 Glauberman (本 axiom が必須)
* `OddOrder/Isaacs/Ch03_SplitExtensions.lean` Thm 3.12 (complement conjugacy), Thm 3.14 Hall-C

## 実装 TODO

mathlib `SchurZassenhausInduction` (step1-step7, `SchurZassenhaus.lean:125-256`) を mirror
して conjugacy 版 induction を書く. abelian base case は `Subgroup.exists_smul_eq` を使用.
全体 ~100-200 LOC 予想. `notes/meta/forward_dep_policy.md` の "暫定 axiom" 規則に従い,
owner chapter (mathlib gap fill) 完成時に theorem 化.

## Statement

`Subgroup.IsComplement'.exists_conj_of_coprime`: `N ⊴ G` normal, `(|N|, |G:N|) = 1`, `K, K'`
complements to `N` in `G` ⇒ ∃ `n ∈ N`, `n K n⁻¹ = K'`.
-/

namespace Subgroup

/-- **Schur-Zassenhaus conjugacy** (axiom): Any two complements to a normal Hall subgroup
are conjugate by an element of the normal subgroup, **assuming `N` or `G/N` is solvable**.

mathlib v4.29.1 has only the abelian case (`Subgroup.exists_smul_eq`); general case is
open as `OddOrder/Mathlib` gap fill.

形式: `K.map (MulAut.conj n).toMonoidHom = K'` は `{n x n⁻¹ : x ∈ K} = K'` と同値, 即ち
`n K n⁻¹ = K'`.

**Solvability hypothesis**: 古典 SZ conjugacy は `N` または `G/N` のいずれかが可解
であることを要する (Feit-Thompson に頼らない). 仮定 `IsSolvable N ∨ IsSolvable (G ⧸ N)`
を明示することで, 本 axiom が Feit-Thompson より強くならないようにする. -/
axiom IsComplement'.exists_conj_of_coprime {G : Type*} [Group G] [Finite G]
    {N K K' : Subgroup G} [N.Normal]
    (_hN : Nat.Coprime (Nat.card N) N.index)
    (_hSolv : IsSolvable N ∨ IsSolvable (G ⧸ N))
    (_hK : IsComplement' N K) (_hK' : IsComplement' N K') :
    ∃ n : G, n ∈ N ∧ K.map (MulAut.conj n).toMonoidHom = K'

end Subgroup
