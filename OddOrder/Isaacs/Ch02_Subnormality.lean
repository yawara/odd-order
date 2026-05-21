/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch01_Sylow

/-!
# OddOrder.Isaacs.Ch02 — Subnormality

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 2
"Subnormality" (pp. 45-64) の Lean 化。

## 章のセクション分割

| § | 内容 | Isaacs 番号 | 状態 |
|---|---|---|---|
| 2A | 部分正規性の基本・join 定理・Wielandt の F(G) | 2.1 – 2.11 | 着手中 (基礎ラッパー済) |
| 2B | Baer の定理と Matsuyama の involution 定理 | 2.12 – 2.14 | TODO |
| 2C | p-local 部分群 | 2.15 – 2.17 | TODO |
| 2D | Zenkov と Lucchini | 2.18 – 2.20 | TODO (FT 経路で必要なし) |

## 方針

mathlib `Subgroup.IsSubnormal` (inductive predicate + `isSubnormal_iff` chain 表現 +
`subgroupOf` / `inf` / `trans` / `map` / `comap` ら) を全面利用。Ch.1 の `Subgroup.fitting`
(= F(G)) と Thm 1.26 (`isNilpotent_of_finite_tfae` 経由の NormalizerCondition) を
橋渡しに使う。

新規定義は `IsMinimalNormal` (mathlib 未収載). Thm 2.6 や 2.18 で必須。

ノート: [notes/isaacs/ch02_subnormality.md](../../notes/isaacs/ch02_subnormality.md)
-/

namespace OddOrder.Isaacs.Ch02

section /- 2A: Subnormality basics, joins, Wielandt's F(G) (pp. 45-54) -/

/-! ### mathlib 直接利用 (本ファイル内に wrapper を置かない)

CLAUDE.md `## 開発規約 ### mathlib ラッパー方針` に従い, 以下の Isaacs 結果は
mathlib に直接対応があり, 純粋なリネームラッパーは書かない. 呼び出し側で
直接 mathlib 名を使う:

* **Isaacs Cor 2.4** (`S ∩ T subnormal`): `Subgroup.IsSubnormal.inf`
* (`H ⊴ G ⇒ H ⊴⊴ G`): `Subgroup.Normal.isSubnormal`
* (subnormal の推移律): `Subgroup.IsSubnormal.trans`
* (subnormal の準同型像/逆像/quotient/smul): `.map`, `.comap`, `.quotient`, `.smul`
* (単純群の subnormal は normal): `.normal_of_isSimpleGroup`, `.eq_bot_or_top_of_isSimpleGroup`

下記の wrapper は **適応** または **2 回以上の使用予定** で書く:
* `inf_isSubnormal_subgroupOf` (Thm 2.3): `S ⊓ K |_K = S |_K` への書換を含む
* `commute_of_disjoint_normal` (Lemma 2.7): `Normal` を instance, `M N` を implicit
  に取り直した適応版 (Thm 2.6 等で複数回使う)
-/

variable {G : Type*} [Group G]

/-- **Minimal normal subgroup**: `M` が `G` の非自明正規部分群で、`M` に真に含まれる
`G`-正規部分群は `⊥` のみ。

mathlib 未収載 (`IsAtom` は subgroup lattice 全体に対するもので normal lattice
には対応しない). Isaacs Thm 2.6, 2.18 (Zenkov) で必須。 -/
def IsMinimalNormal (M : Subgroup G) : Prop :=
  M.Normal ∧ M ≠ ⊥ ∧ ∀ N : Subgroup G, N.Normal → N ≤ M → N = ⊥ ∨ N = M

/-- **Isaacs Lemma 2.1, easy direction** (every subgroup subnormal ⇒ nilpotent).

「全ての部分群が部分正規」ならば NormalizerCondition が成立し，Thm 1.26 経由で冪零。
キーは mathlib `Subgroup.IsSubnormal.iff_eq_top_or_exists`: `H` が部分正規かつ `H ≠ ⊤`
ならば `H < K` で `H ⊴ K` となる `K` が存在する。すると `K ≤ N_G(H)` で `H < N_G(H)`。 -/
theorem isNilpotent_of_all_isSubnormal [Finite G]
    (h : ∀ H : Subgroup G, H.IsSubnormal) : Group.IsNilpotent G := by
  refine ((isNilpotent_of_finite_tfae (G := G)).out 1 0).mp ?_
  intro H hHlt
  rcases Subgroup.IsSubnormal.iff_eq_top_or_exists.mp (h H) with hHtop | ⟨K, hHK, _, hKnorm⟩
  · exact absurd hHtop hHlt.ne
  · have hKle : K ≤ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hHK.le).mp hKnorm
    exact lt_of_lt_of_le hHK hKle

/-- **Isaacs Lemma 2.1, hard direction** (nilpotent ⇒ every subgroup subnormal).

`H.index` についての強induction。`H = ⊤` ならば trivially top。さもなくば
NormalizerCondition (Thm 1.26) で `H < N_G(H)`，`N_G(H).index < H.index` なので
帰納仮定 → `N_G(H).IsSubnormal` → `IsSubnormal.step` で `H.IsSubnormal`。

`H` のなかで `H ⊴ N_G(H)` は `Subgroup.normal_subgroupOf_iff_le_normalizer le_normalizer`
で，K = N_G(H) のときは `K = normalizer K` ではないが `H ≤ normalizer H` から
`(H.subgroupOf normalizer H).Normal` が出る。 -/
theorem isSubnormal_of_isNilpotent_finite [Finite G] [Group.IsNilpotent G]
    (H : Subgroup G) : H.IsSubnormal := by
  classical
  -- Strong induction on H.index.
  induction hN : H.index using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hHt : H = ⊤
    · rw [hHt]; exact Subgroup.IsSubnormal.top
    · -- H < ⊤ via hHt; NormalizerCondition gives H < N_G(H).
      have hNC : NormalizerCondition G :=
        ((isNilpotent_of_finite_tfae (G := G)).out 0 1).mp ‹_›
      have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHt
      have hH_lt_N : H < Subgroup.normalizer (H : Set G) := hNC H hHlt
      -- (normalizer H).index < H.index
      have hidx : (Subgroup.normalizer (H : Set G)).index < n := by
        rw [← hN]
        exact Subgroup.index_strictAnti hH_lt_N
      -- Apply induction hypothesis to normalizer H.
      have hSubnN : (Subgroup.normalizer (H : Set G)).IsSubnormal :=
        ih _ hidx _ rfl
      -- H ⊴ normalizer H, i.e., (H.subgroupOf normalizer H).Normal.
      have hNorm : (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.le_normalizer)).mpr le_rfl
      exact Subgroup.IsSubnormal.step _ _ Subgroup.le_normalizer hSubnN hNorm

/-- **Isaacs Lemma 2.1** (full iff). 有限群 `G` について「`G` が冪零」と
「`G` の全ての部分群が部分正規」は同値. -/
theorem isNilpotent_iff_all_isSubnormal [Finite G] :
    Group.IsNilpotent G ↔ ∀ H : Subgroup G, H.IsSubnormal :=
  ⟨fun _ H => isSubnormal_of_isNilpotent_finite H, isNilpotent_of_all_isSubnormal⟩

/-- **Isaacs Lemma 2.3**: `S ⊴⊴ G`, `K ≤ G` ならば `S ∩ K ⊴⊴ K`.

mathlib では `S ∩ K` を `K` の部分群として扱うのに `(S ⊓ K).subgroupOf K` を使う.
`inf_subgroupOf_right` で `(S ⊓ K).subgroupOf K = S.subgroupOf K` に書き換えて
`IsSubnormal.subgroupOf` を適用. -/
theorem inf_isSubnormal_subgroupOf {S : Subgroup G} (hS : S.IsSubnormal) (K : Subgroup G) :
    ((S ⊓ K).subgroupOf K).IsSubnormal := by
  rw [Subgroup.inf_subgroupOf_right]
  exact hS.subgroupOf

/-- **Isaacs Lemma 2.7**: `M, N ◁ G` で `M ∩ N = 1` ならば `M` の元と `N` の元は可換.

mathlib `Subgroup.commute_of_normal_of_disjoint` の **適応版** —
`Normal` を instance, `M N` を implicit に取り直す (Isaacs 流の呼び出し記法).
Thm 2.6 等で複数回使用予定. (CLAUDE.md mathlib ラッパー方針の例外規定に該当.) -/
theorem commute_of_disjoint_normal {M N : Subgroup G} [hM : M.Normal] [hN : N.Normal]
    (hDis : Disjoint M N) {m n : G} (hm : m ∈ M) (hn : n ∈ N) : Commute m n :=
  Subgroup.commute_of_normal_of_disjoint M N hM hN hDis m n hm hn

-- TODO **Isaacs Thm 2.2** (`H ⊆ F(G) ⇔ H` 冪零かつ部分正規).
--   `(⇒)`: H ⊆ F(G) で F(G) 冪零 (Cor 1.28(a), Ch.1 TODO 未済) → H 冪零 (mathlib).
--          F(G) ⊴ G → F(G).IsSubnormal. Lemma 2.1 を F(G) に適用して H ⊴⊴ F(G).
--          IsSubnormal.trans で H ⊴⊴ G.
--   `(⇐)`: H ⊴⊴ G かつ H 冪零 で induction on |G|.  H = G なら G 冪零 = F(G).
--          さもなくば subnormal chain の penultimate term M < G を取り IH で
--          H ≤ F(M) ⊴ G (F(M) 冪零 + 正規) ⇒ H ≤ fitting G (`nilpotent_normal_le_fitting`).
--   Ch.1 Cor 1.28(a) 完成後に着手.

-- TODO **Isaacs Thm 2.5 Wielandt 結合定理** (`S, T ⊴⊴ G ⇒ ⟨S, T⟩ ⊴⊴ G`).
--   Isaacs 流: Thm 2.6 経由で induction on |G|.
--   従って先に Thm 2.6 (minimal normal が subnormal を正規化) を実装する.

-- TODO **Isaacs Thm 2.6** (minimal normal が subnormal を正規化).
--   `S ⊴⊴ G, M minimal normal ⇒ M ⊆ N_G(S)`.  Isaacs Ch.4+ で被引用最多 (4 回).
--   Socle (全 minimal normal の sup) を経由する.

-- TODO Thm 2.8 (permutability ⇒ subnormality), Thm 2.9 Zipper Lemma, Thm 2.10, Thm 2.11.

end -- 2A

end OddOrder.Isaacs.Ch02
