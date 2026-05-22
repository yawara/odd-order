/-!
# Ch.7 → Ch.3 forward dependencies

このファイルは **Isaacs FGT Ch.3 §3C の 2 定理** (Thm 3.15, Thm 3.17) が Burnside
`p^a q^b` 定理 (Ch.7 で証明予定) に依存するための placeholder. owner chapter (Ch.7)
ディレクトリに配置.

## このファイルに将来実装される内容

### Isaacs Thm 3.15 — p-complement 存在 ⇒ G solvable

```lean
theorem solvable_of_pcomplement_exists [Finite G]
    (h : ∀ p : ℕ, p.Prime → ∃ H : Subgroup G, IsHallSubgroup {q | q ≠ p} H) :
    IsSolvable G
```

**証明戦略** (Hall's converse):
* `|G|`-induction. p, q を `|G|` を割る相異なる素数とし, H_p, H_q の p-, q-complement
  を取る. H_p ∩ H_q は {p,q}'-Hall に相当.
* 商と部分群の solvability を組み合わせる.
* **Burnside 依存**: Isaacs p.84 で「Thm 3.15 in full generality は Burnside を仮定すれば
  容易」と明言.

### Isaacs Thm 3.17 — Wielandt の 3 部分群定理

```lean
theorem solvable_of_three_subgroups [Finite G] {H K L : Subgroup G}
    (h12 : Nat.Coprime H.index K.index)
    (h13 : Nat.Coprime H.index L.index)
    (h23 : Nat.Coprime K.index L.index)
    [IsSolvable H] [IsSolvable K] [IsSolvable L] :
    IsSolvable G
```

**証明戦略** (Wielandt 1971):
* `|G|`-induction. 最小反例 G, minimal normal M.
* G/M は IH で solvable. M も `(H ∩ M)`, `(K ∩ M)`, `(L ∩ M)` 部分群経由で IH より solvable.
* G simple の場合 (M = G): **Burnside `p^a q^b` 必須**.

## 実装スケジュール

* **Phase**: Phase 4 (Ch.4-Ch.7 全完成後 ~4-6 ヶ月).
* **前提**:
  - Ch.7 Burnside `p^a q^b` 完成. (中核理論)
  - 部分群・商の solvability 補題 (mathlib + Ch.1-Ch.3 完成済).

## 関連ノート

- [`notes/isaacs/ch03_split.md`](../../../notes/isaacs/ch03_split.md) §3C セクション.
- [`notes/isaacs/ch07_burnside.md`](../../../notes/isaacs/ch07_burnside.md) (新規予定).
- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md).
-/

namespace OddOrder.Isaacs.Ch07
-- 意図的に空. 上記 docstring 参照. Ch.7 Burnside 完成後にここで実装.
end OddOrder.Isaacs.Ch07
