import OddOrder.Isaacs.Ch02_Subnormality

/-!
# Ch.4 → Ch.2 forward dependencies

このファイルは **Isaacs FGT Ch.2 §2D Thm 2.20 (Lucchini)** を完全形式化する場所.
論理的には Ch.2 の定理だが, **K = ⊥ case の証明が Ch.4 §4A-§4B (lower central series
加法性) に依存**するため, owner chapter (Ch.4) ディレクトリに置く.

## このファイルの構造

1. `lucchini_K_bot_aux` — Lucchini の K = ⊥ case (narrower **axiom**).
   Ch.4 §4A-§4B 完成後に theorem 化される予定. 具体的に必要な補題は:
   * Isaacs Thm 4.11 系: `[γᵢ(F), γⱼ(F)] ⊆ γᵢ₊ⱼ(F)` (lcs 加法性).
   * 補題「minimal normal `E ⊆ F(G)` ⇒ `E ⊆ Z(F(G))`」 (lcs 加法性 + minimal 性).
   詳細は [`notes/isaacs/ch04_commutators.md`](../../../notes/isaacs/ch04_commutators.md)
   の「逆引き: Ch.2 §2D Lucchini K = ⊥ case」セクション.

2. `lucchini_aux` — `|G|`-induction wrapper (private).
   * K = ⊥ branch: `lucchini_K_bot_aux` を呼ぶ.
   * K > ⊥ branch: Ch.2 の `lucchini_K_pos_reduction` (subgroup correspondence のみ)
     + IH on G/K.

3. `lucchini_index_normalCore_lt_index` — **Isaacs Thm 2.20 本体** (theorem).
   `lucchini_aux (Nat.card G) le_rfl ...` で呼ぶ.

## namespace 設計

書籍上は Ch.2 の定理だが, Lean 上は物理的に Ch.4 dir にいるため
`OddOrder.Isaacs.Ch04` namespace を使う. docstring に book 番号 (Thm 2.20) を明示.

## 関連ノート

- [`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md):
  forward dep の所在規則.
- [`notes/isaacs/ch02_subnormality.md`](../../../notes/isaacs/ch02_subnormality.md):
  Ch.2 内 `lucchini_K_pos_reduction` (構造補題) との分担.
-/

namespace OddOrder.Isaacs.Ch04

variable {G : Type*} [Group G]

/-- **Isaacs Thm 2.20 (Lucchini) K = ⊥ case (narrower axiom)**.

`G` 有限群, `A` cyclic abelian 真部分群, `K = core_G(A) = ⊥` ならば `|A| < |G:A|`.

これは Lucchini の核心部 (induction base). 完全形式化の道筋:
* Cor 2.19 (Ch.2 §2D ✅) で `|A| ≥ |G:A|` を仮定して `A ⊓ F(G) > 1` ⇒ `F(G) > 1` を導出.
* minimal normal `E ⊆ F(G)` を選び, `E ⊆ Z(F(G))` + elementary abelian p.
  この補題は **Ch.4 §4A-§4B** の `lowerCentralSeries` 加法性 (Isaacs Thm 4.11) 経由で得られる.
* `AE < G` (K = ⊥ で), G/E に IH 適用, sub-case 解析で矛盾.

**実装方針**: Ch.4 §4A-§4B 完成後 ~150-200 行で theorem 化. -/
axiom lucchini_K_bot_aux [Finite G] {A : Subgroup G}
    (_hA_proper : A < ⊤)
    (_hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (_hA_isCyclic : ∃ g : G, A = Subgroup.zpowers g)
    (_hK_bot : A.normalCore = ⊥) :
    Nat.card ↥A < A.index

/-- **Lucchini `|G|`-induction wrapper** (private).
* K = ⊥ branch: `lucchini_K_bot_aux` (narrower axiom).
* K > ⊥ branch: Ch.2 `lucchini_K_pos_reduction` + IH on G/K. -/
private theorem lucchini_aux : ∀ n : ℕ,
    ∀ {G : Type*} [Group G] [Finite G] {A : Subgroup G},
      Nat.card G ≤ n →
      A < ⊤ →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∃ g : G, A = Subgroup.zpowers g) →
      (A.normalCore.subgroupOf A).index < A.index := by
  intro n
  induction n with
  | zero =>
    intro G _ _ A hcard _ _ _
    exact absurd hcard (Nat.not_le_of_lt Nat.card_pos)
  | succ n ih =>
    intro G _ _ A hcard hAprop hAab hAcyc
    by_cases hsmall : Nat.card G ≤ n
    · exact ih hsmall hAprop hAab hAcyc
    -- |G| = n+1 exactly.
    set K := A.normalCore with hKdef
    haveI hKnormal : K.Normal := A.normalCore_normal
    have hK_le_A : K ≤ A := Subgroup.normalCore_le A
    by_cases hK_bot : K = ⊥
    · -- K = ⊥ case: use narrower axiom.
      have h_idx : (K.subgroupOf A).index = Nat.card ↥A := by
        rw [hK_bot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
      change (K.subgroupOf A).index < A.index
      rw [h_idx]
      exact lucchini_K_bot_aux hAprop hAab hAcyc hK_bot
    · -- K > ⊥ case: invoke IH on G/K + Ch.2 reduction lemma.
      let f : G →* G ⧸ K := QuotientGroup.mk' K
      have hf_surj : Function.Surjective f := QuotientGroup.mk'_surjective K
      set Ā : Subgroup (G ⧸ K) := A.map f with hĀ_def
      -- Ā < ⊤: from A < ⊤ and K ≤ A.
      have hĀ_proper : Ā < ⊤ := by
        rw [lt_top_iff_ne_top]
        intro h_eq
        have h1 : Subgroup.comap f Ā = ⊤ := by rw [h_eq]; exact Subgroup.comap_top _
        have h2 : Subgroup.comap f Ā = K ⊔ A := by
          rw [hĀ_def, QuotientGroup.comap_map_mk']
        have h3 : K ⊔ A = A := sup_of_le_right hK_le_A
        rw [h2, h3] at h1
        exact ne_of_lt hAprop h1
      -- Ā cyclic.
      have hĀ_cyc : ∃ ĝ : G ⧸ K, Ā = Subgroup.zpowers ĝ := by
        obtain ⟨g, hg⟩ := hAcyc
        refine ⟨f g, ?_⟩
        rw [hĀ_def, hg, f.map_zpowers]
      -- Ā abelian.
      have hĀ_ab : ∀ x ∈ Ā, ∀ y ∈ Ā, x * y = y * x := by
        intro x hx y hy
        obtain ⟨a, haA, hfa⟩ := hx
        obtain ⟨b, hbA, hfb⟩ := hy
        rw [← hfa, ← hfb, ← map_mul, ← map_mul, hAab a haA b hbA]
      -- |G/K| ≤ n.
      have hKnonbot_card : 2 ≤ Nat.card ↥K := by
        haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_bot
        exact Finite.one_lt_card
      have hquot_card : Nat.card (G ⧸ K) ≤ n := by
        have heq : Nat.card G = Nat.card (G ⧸ K) * Nat.card ↥K :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup K
        have h1 : Nat.card (G ⧸ K) * 2 ≤ Nat.card G := by
          rw [heq]; exact Nat.mul_le_mul_left _ hKnonbot_card
        have h2 : Nat.card G ≤ n + 1 := hcard
        omega
      -- Apply IH on G/K with Ā.
      have hIH : (Ā.normalCore.subgroupOf Ā).index < Ā.index :=
        ih hquot_card hĀ_proper hĀ_ab hĀ_cyc
      -- Apply Ch.2 K > ⊥ reduction lemma.
      exact OddOrder.Isaacs.Ch02.lucchini_K_pos_reduction hAprop hK_bot hIH

/-- **Isaacs Thm 2.20 (Lucchini)**: `G` 有限群, `A` cyclic 真部分群, `K = core_G(A)`.
ならば `|A:K| < |G:A|`. 特に `|A| ≥ |G:A|` なら `K > 1`.

書籍 p.62-63 の証明 (induction on `|G|`):
* K > ⊥: G/K に IH 適用 (Ch.2 `lucchini_K_pos_reduction` 経由).
* K = ⊥: `lucchini_K_bot_aux` (narrower axiom; Ch.4 §4A-§4B 完成後に theorem 化).

**この定理は書籍上 Ch.2 だが, Lean 上は Ch.4 dir にいる** — K = ⊥ case が Ch.4 領域に
依存するため. owner chapter 規則による配置. 詳細は
[`notes/meta/forward_dep_policy.md`](../../../notes/meta/forward_dep_policy.md). -/
theorem lucchini_index_normalCore_lt_index [Finite G] {A : Subgroup G}
    (hA_proper : A < ⊤)
    (hA_ab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA_isCyclic : ∃ g : G, A = Subgroup.zpowers g) :
    (A.normalCore.subgroupOf A).index < A.index :=
  lucchini_aux (Nat.card G) le_rfl hA_proper hA_ab hA_isCyclic

end OddOrder.Isaacs.Ch04
