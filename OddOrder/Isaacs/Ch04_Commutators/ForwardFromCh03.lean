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

### Isaacs Cor 3.28 — Coprime quotient fixed-points ⭐ FT クリティカル (transitive blocker)

```lean
theorem coprime_fixedPoints_quotient {A : Type*} [Group A] [Finite A] [Finite G]
    (φ : A →* MulAut G) {N : Subgroup G} [N.Normal]
    (hN : IsAInvariant φ N) (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (hSolv : IsSolvable A ∨ IsSolvable N) :
    -- C_{G/N}(induced A action) = image of C_G(A) in G/N
    sorry
```

**2026-05-22 audit 発見**: Cor 3.28 は Ch.4 多数定理 (4.26, 4.28-30, 4.34-36, 4.38) の
transitive 前提. 既存配置に明示 placeholder が無く, **明示追加が必要**.

**2026-05-23 audit 訂正**: Cor 3.28 自体は Lem 3.24 + Thm 3.27 のみ依存. Schur-Zassenhaus +
§3A SemidirectProduct (mathlib + Ch.3 §3A 既存 ✅) で完結. ⇒ **Tier 1 (下記) で実装可**,
Ch.4 §4C-§4D を待つ必要無し.

## 実装スケジュール (2026-05-23 Ch.3 audit で Tier 分割)

### Tier 1 (~1-2 週, Ch.4 §4C-§4D を待たず実装可)

- **Lem 3.24 Glauberman** — Γ = G ⋊ A + Schur-Zassenhaus, ~80 LOC
- **Thm 3.27** (A-不変 coset = C_G(A) 含む coset) — 3.24 経由, ~20 LOC
- **Cor 3.28** — 3.27 経由, **~15 LOC**
- (任意) Thm 3.23 (a/b), Cor 3.25, Cor 3.29, Cor 3.30 — 同じ infrastructure で追加 ~80 LOC

**前提**: §3A SemidirectProduct (✅), Sylow (mathlib ✅), Schur-Zassenhaus existence (mathlib ✅),
Frattini (mathlib ✅). **Ch.4 不要**.

### Tier 2 (~6-8 週, Hartley-Turull 系)

- Thm 3.26 (A-inv 共役類 ↔ C 共役類 bijection) — ~40 LOC
- Thm 3.31 Hartley-Turull — ~150 LOC. **BG/Peterfalvi 名前引用 0 件**, Phase 4 までも skip 可
- Lem 3.32, 3.33, Thm 3.34 — ~60-100 LOC each. 同上, Phase 4 候補

**前提**: Tier 1 + Ch.4 §4C `[G,A]` 機構 (Lemma 4.20, 4.21, Thm 4.22-4.27), Ch.4 §4D Thm 4.31
(Thompson P×Q), Cor 4.35.

## 関連ノート

- [`notes/isaacs/ch03_split.md`](../../../notes/isaacs/ch03_split.md) §3E セクション.
- [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md) §4C-§4D.
- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md).
-/

namespace OddOrder.Isaacs.Ch04
-- 意図的に空. 上記 docstring 参照. Ch.4 §4C-§4D 完成後にここで実装.
end OddOrder.Isaacs.Ch04
