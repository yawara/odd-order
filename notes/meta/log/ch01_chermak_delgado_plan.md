# Isaacs §1G Chermak-Delgado 実装計画 (2026-05-23)

ユーザ決定 (2026-05-23): **§1G Thm 1.41-1.46 を将来 mathlib upstream のために実装する**.
本ドキュメントは [`ch01_audit_2026_05_23.md`](ch01_audit_2026_05_23.md) を踏まえた具体的
**Lean 実装計画書**. 着手前に必要な調査は完了済 (本ファイルがその統合出力).

## 1. ファイル配置 (決定提案)

mathlib upstream 想定なので **`OddOrder/Mathlib/` 配下** が convention:

```
OddOrder/Mathlib/
  Subgroup.lean                    ★ NEW — H1, H2 helpers (汎用)
OddOrder/GroupTheory/
  ChermakDelgado.lean              ★ NEW — §1G 本体
OddOrder/Isaacs/Ch01_Sylow/Main.lean    既存 §1G stub → 軽い再 export に置換 (or 削除)
```

理由:
- `OddOrder/Mathlib/Subgroup.lean`: H1 (`card_HK_mul_inf = card_H · card_K`) と H2
  (`le_centralizer_centralizer`) は **mathlib 汎用 helper**. 章特定でなく, Ch.2+ や BG でも
  独立に使う可能性高い. `OddOrder/Mathlib/` は「mathlib に出すべき gap fill」の慣用 dir
  (`OddOrder/Mathlib/SchurZassenhausConj.lean` と同じパターン).
- `OddOrder/GroupTheory/ChermakDelgado.lean`: Chermak-Delgado 概念 (`chermakDelgadoMeasure`,
  `chermakDelgadoSubgroup`) は **Isaacs §1G 主題でもあり mathlib upstream 概念でもある**.
  `OddOrder/GroupTheory/` は「将来 mathlib upstream 視野の shared concept」(`IsElementaryAbelian`,
  `Subgroup.thompsonJ` と同じパターン).
- `Ch01_Sylow/Main.lean`: 既存 §1G stub (L3196-3215) は本実装後, **`import` + 1 行 re-export +
  docstring** に置換. これで 1 章 = 1 ファイル規約も保たれる.

## 2. `OddOrder/Mathlib/Subgroup.lean` 内容

### H1: `Subgroup.card_HK_mul_card_inf_eq_card_mul_card`

```lean
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Set.Card

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- **Classical**: `|HK| · |H ∩ K| = |H| · |K|` for subgroups `H, K` of a finite group `G`.
The set product `↑H * ↑K : Set G` is **not** generally a subgroup.

mathlib v4.29.1 不在. mathlib upstream 候補. -/
theorem card_HK_mul_card_inf_eq_card_mul_card (H K : Subgroup G) :
    Nat.card (↑H * ↑K : Set G) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  sorry  -- 標準証明: (h, k) ↦ hk の (H × K) → HK 同値類は H ∩ K-orbit
         -- mathlib `Subgroup.quotientEquivProdOfLE` 系 + `Nat.card_prod` + `Set.ncard_image2`

end Subgroup
```

**証明スケッチ** (~30 LOC):
- `(h, k) ↦ h * k : H × K → ↑H * ↑K` の preimage は `(h, k) ~ (hd⁻¹, dk) for d ∈ H ∩ K`.
- これは `H ∩ K`-orbit (左作用 `d • (h, k) := (h·d, d⁻¹·k)`).
- `Nat.card (H × K) = |H ∩ K| · |HK|`.

候補 API:
- `Nat.card_eq_card_quotient_mul_card_subgroup` (もう 1 つの方向の counting)
- `Set.ncard_image2` (mul の image)
- `MulAction.orbitEquivQuotientStabilizer` 経由で書ける可能性あり

### H2: `Subgroup.le_centralizer_centralizer`

```lean
/-- `H ≤ C_G(C_G(H))` for any subgroup `H` of `G`. 古典的 Galois connection の系.

mathlib v4.29.1 不在 (既存 `Subgroup.le_centralizer` は `IsMulCommutative H` 仮定が必要).
mathlib upstream 候補. -/
theorem le_centralizer_centralizer (H : Subgroup G) :
    H ≤ centralizer (centralizer H : Set G) :=
  Subgroup.le_centralizer_iff.mpr le_rfl
```

**証明: 2 行** (Galois connection `le_centralizer_iff (H ≤ centralizer K ↔ K ≤ centralizer H)`
の応用).

### H3 (補): `Subgroup.centralizer_centralizer_centralizer`

```lean
/-- `C_G(C_G(C_G(H))) = C_G(H)` (Galois closure). -/
theorem centralizer_centralizer_centralizer (H : Subgroup G) :
    centralizer (centralizer (centralizer H : Set G) : Set G) = centralizer (H : Set G) := by
  apply le_antisymm
  · exact centralizer_le (le_centralizer_centralizer H : H ≤ _)
  · exact le_centralizer_centralizer _
```

Cor 1.45 の `C_G(M) ∈ ℒ(G)` で使用. ~3 行.

### (任意) `Subgroup.centralizer_sup_eq_inf_centralizer`

```lean
/-- `C_G(H ⊔ K) = C_G(H) ⊓ C_G(K)`. mathlib `Subalgebra` 版あり (`Subalgebra.centralizer_sup`,
`Algebra/Subalgebra/Centralizer.lean:19`) だが Subgroup 版は不在. -/
theorem centralizer_sup (H K : Subgroup G) :
    centralizer ((H ⊔ K : Subgroup G) : Set G)
      = centralizer (H : Set G) ⊓ centralizer (K : Set G) := by
  sorry  -- (H ⊔ K).carrier ⊇ H ∪ K で `centralizer_le` の単調性 + 各 element の commute 性
```

§1G では Lem 1.43 で `C_J = C_H ∩ C_K` (J = ⟨H, K⟩) を使う. ~10 LOC.

## 3. `OddOrder/GroupTheory/ChermakDelgado.lean` 内容

### Definitions

```lean
import OddOrder.Mathlib.Subgroup

namespace Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- **Chermak-Delgado measure** of a subgroup. `m_G(H) = |H| · |C_G(H)|`. -/
noncomputable def chermakDelgadoMeasure (H : Subgroup G) : ℕ :=
  Nat.card H * Nat.card (centralizer (H : Set G) : Subgroup G)

/-- The set of subgroups attaining the maximum Chermak-Delgado measure (Thm 1.44 の `ℒ(G)`). -/
def chermakDelgadoLattice (G : Type*) [Group G] [Finite G] : Set (Subgroup G) :=
  {H | ∀ K : Subgroup G, K.chermakDelgadoMeasure ≤ H.chermakDelgadoMeasure}

/-- **Chermak-Delgado subgroup** `M`: the minimum (intersection) of `ℒ(G)`. -/
noncomputable def chermakDelgadoSubgroup (G : Type*) [Group G] [Finite G] : Subgroup G :=
  ⨅ H ∈ chermakDelgadoLattice G, H

end Subgroup
```

設計判断:
- `noncomputable`: `Nat.card` が `Finite G` 必要 + classical 取り扱い.
- `chermakDelgadoLattice` は `Set (Subgroup G)`: mathlib `Sublattice` 構造体は `Lattice α` の
  Sublattice 抽象だが, ここでは「最大値 attain」を述語で書く方が direct. Thm 1.44 が
  `ℒ ⊆ Subgroup G` の Sublattice 性 (sup-closed + inf-closed) を証明する.

### Per-定理

```lean
/-- **Isaacs Lemma 1.42**: `m_G(H) ≤ m_G(C_G(H))`, 等号成立は `H = C_G(C_G(H))` のとき. -/
theorem chermakDelgadoMeasure_le_centralizer (H : Subgroup G) :
    H.chermakDelgadoMeasure ≤ (centralizer (H : Set G) : Subgroup G).chermakDelgadoMeasure := by
  -- |H| · |C_G(H)| ≤ |C_G(H)| · |C_G(C_G(H))|, since H ⊆ C_G(C_G(H))
  -- H1 で `H ≤ C_G(C_G(H))` 経由, `Nat.card_le_of_le`
  sorry

/-- **Isaacs Lemma 1.43**: `m(H) · m(K) ≤ m(D) · m(J)`. -/
theorem chermakDelgadoMeasure_mul_le (H K : Subgroup G) :
    H.chermakDelgadoMeasure * K.chermakDelgadoMeasure
      ≤ (H ⊓ K).chermakDelgadoMeasure * (H ⊔ K).chermakDelgadoMeasure := by
  -- |J| ≥ |HK| = |H|·|K|/|H∩K|, and |C_D| ≥ |C_H · C_K| = |C_H|·|C_K|/|C_J|
  -- H1 (card_HK_mul_card_inf) を 2 回使用 (subgroup pair (H, K) と (C_H, C_K))
  sorry

/-- **Isaacs Thm 1.44 (a)**: `ℒ(G)` is closed under intersections and joins. -/
theorem chermakDelgadoLattice_inf_mem {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊓ K ∈ chermakDelgadoLattice G := by sorry

theorem chermakDelgadoLattice_sup_mem {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    H ⊔ K ∈ chermakDelgadoLattice G := by sorry

/-- **Isaacs Thm 1.44 (b)**: `H, K ∈ ℒ ⇒ ⟨H, K⟩ = HK`. -/
theorem chermakDelgadoLattice_sup_eq_mul {H K : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) (hK : K ∈ chermakDelgadoLattice G) :
    ((H ⊔ K : Subgroup G) : Set G) = ↑H * ↑K := by sorry

/-- **Isaacs Thm 1.44 (c)**: `H ∈ ℒ ⇒ C_G(H) ∈ ℒ ∧ C_G(C_G(H)) = H`. -/
theorem chermakDelgadoLattice_centralizer_mem {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    (centralizer (H : Set G) : Subgroup G) ∈ chermakDelgadoLattice G := by sorry

theorem chermakDelgadoLattice_centralizer_centralizer {H : Subgroup G}
    (hH : H ∈ chermakDelgadoLattice G) :
    centralizer ((centralizer (H : Set G) : Subgroup G) : Set G) = (H : Set G) := by sorry

/-- **Isaacs Cor 1.45**: `M = chermakDelgadoSubgroup G` is abelian + contains Z(G). -/
theorem chermakDelgadoSubgroup_mem_lattice :
    chermakDelgadoSubgroup G ∈ chermakDelgadoLattice G := by sorry

theorem chermakDelgadoSubgroup_isCommutative :
    IsMulCommutative (chermakDelgadoSubgroup G) := by sorry

theorem center_le_chermakDelgadoSubgroup :
    Subgroup.center G ≤ chermakDelgadoSubgroup G := by sorry

instance chermakDelgadoSubgroup_characteristic :
    (chermakDelgadoSubgroup G).Characteristic := by sorry

/-- **Isaacs Thm 1.41 (Chermak-Delgado)**: ∃ characteristic abelian N with
`|G : N| ≤ |G : A|² ∀ A abelian`. -/
theorem chermakDelgado [Nonempty G] :
    ∃ N : Subgroup G, N.Characteristic ∧ IsMulCommutative N ∧
      ∀ A : Subgroup G, IsMulCommutative A →
        (N.index : ℚ) ≤ (A.index : ℚ) ^ 2 := by
  refine ⟨chermakDelgadoSubgroup G, ?_, ?_, ?_⟩ <;> sorry

/-- **Isaacs Cor 1.46**: `|H| · |C_G(H)| > |G|` ⇒ G not nonabelian simple. -/
theorem not_isSimpleGroup_of_chermakDelgadoMeasure_gt {H : Subgroup G}
    (h : H.chermakDelgadoMeasure > Nat.card G) :
    ¬ (IsSimpleGroup G ∧ ¬ IsMulCommutative G) := by sorry

end Subgroup
```

設計判断:
- **Thm 1.41 statement**: index 不等式は ℚ-cast で `Nat.div` 回避 (古典的 `|G:N| ≤ |G:A|²`
  は実は `|G:N| · |A|² ≤ |G|²` の方が integer-safe; どちらでも書けるが ℚ 版は読みやすい).
- **`IsMulCommutative` vs `IsAbelian`**: mathlib では `Subgroup.IsMulCommutative H` が abelian
  subgroup の標準形 (`Centralizer.lean:89` 等). `IsCommutative` 削除済 (mathlib 最近の rename).

## 4. 既存 §1G stub (`Ch01_Sylow/Main.lean:3196-3215`) の処理

選択肢 A: **削除** (file 分離, §1G 内容は `OddOrder.GroupTheory.ChermakDelgado` で完結).
選択肢 B: **import + re-export** (1 章 = 1 ファイル規約整合):

```lean
import OddOrder.GroupTheory.ChermakDelgado

namespace OddOrder.Isaacs.Ch01
section /- 1G: Chermak-Delgado (pp. 41-44) -/

/-! ### §1G 実装は `OddOrder/GroupTheory/ChermakDelgado.lean` に分離

mathlib upstream 視野のため shared module 化. 本 section は re-export と参照のみ.
詳細は `notes/meta/log/ch01_chermak_delgado_plan.md`. -/

export Subgroup (chermakDelgadoMeasure chermakDelgadoLattice chermakDelgadoSubgroup
  chermakDelgado not_isSimpleGroup_of_chermakDelgadoMeasure_gt)

end -- 1G
end OddOrder.Isaacs.Ch01
```

**推奨: 選択肢 B** (1 章 = 1 ファイル trace + import pulls in the content for downstream Ch.1
users).

## 5. 実装順序

```
Step 1 [~30 LOC]  OddOrder/Mathlib/Subgroup.lean 新設
                  - H1 card_HK_mul_card_inf_eq_card_mul_card (主作業)
                  - H2 le_centralizer_centralizer (2 行)
                  - (任意) H3 centralizer_centralizer_centralizer
                  - (任意) centralizer_sup (10 行)

Step 2 [~30 LOC]  OddOrder/GroupTheory/ChermakDelgado.lean 新設
                  - chermakDelgadoMeasure def
                  - chermakDelgadoLattice def
                  - chermakDelgadoSubgroup def
                  - Lemma 1.42 (H2 経由, ~10 LOC)

Step 3 [~40 LOC]  Lemma 1.43 (H1 経由 + centralizer_sup 経由 + 計算)
Step 4 [~30 LOC]  Thm 1.44 (a), (b), (c)
Step 5 [~30 LOC]  Cor 1.45 + characteristic instance
Step 6 [~20 LOC]  Thm 1.41 (Cor 1.45 から index 計算)
Step 7 [~20 LOC]  Cor 1.46
Step 8 [~5 LOC]   Ch01_Sylow/Main.lean §1G stub を re-export 形に書き換え

Step 9 (任意)     mathlib upstream PR 準備 (Phase 1 完成後)
```

**Total**: ~200 LOC (見積もり 150 + helper 30 + buffer 20). **~2 日工数**.

## 6. 着手前の最終確認事項

- [ ] `IsMulCommutative` の正確な mathlib 名 (現 v4.29.1; v4.30+ で rename された可能性)
- [ ] `Subgroup G` の `CompleteLattice` instance での `⨅ H ∈ S, ...` 構文 — `Lattice.lean:239` の
  パターンを参照. `chermakDelgadoSubgroup` の `⨅ H ∈ chermakDelgadoLattice G, H` が型推論で
  通るか実装時確認 (恐らく `id` を挟む).
- [ ] `Set.ncard` vs `Nat.card` の使い分け — `↑H * ↑K : Set G` は `Set.ncard` が自然だが
  `Nat.card` で書ける場合は統一推奨 (mathlib `Subgroup.index_mul_card` 慣用).
- [ ] mmd L920 の typo "Cor 1.39" は実は "Cor 1.45" (Isaacs 誤植) — docstring に注記.

## 7. mathlib upstream に向けたメタ

- **PR 候補ファイル**:
  - `Mathlib/GroupTheory/Subgroup/Centralizer.lean` 拡張: H2 (`le_centralizer_centralizer`),
    H3, `centralizer_sup`.
  - `Mathlib/GroupTheory/Subgroup/Lattice.lean` or `Coset/Card.lean` 拡張: H1
    (`card_HK_mul_card_inf_eq_card_mul_card`).
  - `Mathlib/GroupTheory/ChermakDelgado.lean` 新規: §1G 全体.
- **証明スタイル**: mathlib 慣用 (`refine ... <;> sorry` 等の最小化, `simp only` 使用, term-style
  優先).
- **`to_additive` 適用可否**: `Subgroup.centralizer` は `@[to_additive]` 付き (`Centralizer.lean:24`).
  H1, H2, H3 も `@[to_additive]` 付けて加法群版を自動生成可. Chermak-Delgado 自体は乗法群限定
  (商体的に意味なし).

## 8. 関連ノート

- 元 audit: [`ch01_audit_2026_05_23.md`](ch01_audit_2026_05_23.md)
- 元 ch.1 note: [`../isaacs/ch01_sylow.md`](../../isaacs/ch01_sylow.md)
- §1F (Brodkey, Chermak-Delgado の corollary): `Ch01_Sylow/Main.lean:2900-3195` 既実装
  (`exists_pair_inf_eq_opCore_of_abelian`, `index_opCore_le_index_sylow_sq`)
- mathlib 配置慣用: [`forward_dep_policy.md`](../forward_dep_policy.md),
  [`chapter_investigation_framework.md`](../chapter_investigation_framework.md) §6.3

---

*本計画書をもって §1G 実装着手前の調査は完了. 上記 Step 1 → Step 8 の順で実装可能.*
