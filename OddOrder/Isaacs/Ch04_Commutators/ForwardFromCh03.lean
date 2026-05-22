/-!
# Ch.4 → Ch.3 forward dependencies

このファイルは **Isaacs FGT Ch.3 §3E (Coprime action)** の定理群が Ch.4 §4C-§4D
(`[G,A]` 構造 + coprime action machinery + Thompson P×Q + Fitting decomposition) に依存
するための placeholder. owner chapter (Ch.4) ディレクトリに配置.

## このファイルに将来実装される内容

### Isaacs Thm 3.23 (a, b) — A-不変 Sylow ⭐ FT クリティカル

```lean
theorem exists_aInvariant_sylow {A : Type*} [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, IsAInvariant φ (P : Subgroup G)
```
A coprime action ⇒ 任意素数 p で A-不変 Sylow p-部分群が存在 (3.23a).
二つの A-不変 Sylow は `C_G(A)` で共役 (3.23b).

**証明戦略** (Isaacs p.96-98):
* 標準 coprime action 議論 + Schur-Zassenhaus existence.
* IsPGroup + Sylow + A の作用での固定軌道解析.
* 共役性は Glauberman lemma (3.24) を経由.

### Isaacs Lemma 3.24 — Glauberman fixed-point ⭐ FT クリティカル

```lean
theorem glauberman_fixed_point ...
```
A coprime + A solvable + G transitive on Ω + A action compatible
⇒ A-fixed 点 ω ∈ Ω 存在.

**証明戦略** (Isaacs p.98):
* `G ⋊ A` で stabilizer 議論.
* A solvable の induction で reduce to A abelian, さらに A cyclic.
* Thompson P×Q (Thm 4.31) or Cor 4.35 (Ch.4 §4D) で fixed-point 存在.

### Isaacs Thm 3.25-3.34 — Coprime action 系

A-不変部分群と商の対応, A-不変 Sylow と `C_G(A)` の Sylow の対応, 軌道構造
(Hartley-Turull, orbit-size 主張), `[G,A,A] = [G,A]` (Three-Subgroup Lemma 経由) 等.

## 実装スケジュール

* **Phase**: Phase 2 (Ch.4 完成後).
* **工数**: ~8-12 週の大規模作業.
* **前提**:
  - Ch.4 §4C `[G,A]` 機構 (Lemma 4.20, 4.21, Thm 4.22-4.27).
  - Ch.4 §4D Thm 4.31 (Thompson P×Q), Cor 4.35.
  - mathlib coprime action API の活用.

## 関連ノート

- [`notes/isaacs/ch03_split.md`](../../../notes/isaacs/ch03_split.md) §3E セクション.
- [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md) §4C-§4D.
- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md).
-/

namespace OddOrder.Isaacs.Ch04
-- 意図的に空. 上記 docstring 参照. Ch.4 §4C-§4D 完成後にここで実装.
end OddOrder.Isaacs.Ch04
