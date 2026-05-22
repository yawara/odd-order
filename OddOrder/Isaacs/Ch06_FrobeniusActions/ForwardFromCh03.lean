/-!
# Ch.6 → Ch.3 forward dependencies

このファイルは **Isaacs FGT Ch.3 §3D Thm 3.21 (Hall-Higman 1.2.3)** が Ch.6
(Frobenius p-nilpotence, P×Q lemma) に依存するための placeholder. owner chapter (Ch.6)
ディレクトリに配置.

## このファイルに将来実装される内容

### Isaacs Thm 3.21 — Hall-Higman 1.2.3 ⭐ FT クリティカル

```lean
theorem hall_higman_1_2_3 [Finite G] (π : Set ℕ) (hπsep : IsPiSeparable π G)
    (hPiPrime : oPiCore πᶜ G = ⊥) :
    Subgroup.centralizer (oPiCore π G : Set G) ≤ oPiCore π G
```

`G` π-separable + `O_{π'}(G) = ⊥` ⇒ `C_G(O_π(G)) ≤ O_π(G)`.

**証明戦略** (Isaacs p.94):
* π-separable normal series に沿った induction.
* F* (一般化 Fitting) 経由, または Bender 法:
  - `C := C_G(O_π(G))` の極小反例.
  - `C ⊓ O_π(G) = Z(O_π(G))` の解析.
  - `C O_π(G) ⊴ G` の構造.
* Ch.6 の Frobenius p-nilpotence + Thompson P×Q lemma を内部使用.

## 実装スケジュール

* **Phase**: Phase 2 (Ch.6 着手後).
* **工数**: ~100-200 行 (Ch.6 infrastructure 完成後).
* **前提**:
  - Ch.6 § Frobenius p-nilpotence の core 補題.
  - Ch.4 §4D Thm 4.31 (Thompson P×Q lemma).
  - Ch.4 §4D Thm 4.33 (p-solvable + p-local).

## 関連ノート

- [`notes/isaacs/ch03_split.md`](../../../notes/isaacs/ch03_split.md) §3D セクション.
- [`notes/isaacs/ch06_frobenius_actions.md`](../../../notes/isaacs/ch06_frobenius_actions.md).
- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md).
-/

namespace OddOrder.Isaacs.Ch06
-- 意図的に空. 上記 docstring 参照. Ch.6 完成後にここで実装.
end OddOrder.Isaacs.Ch06
