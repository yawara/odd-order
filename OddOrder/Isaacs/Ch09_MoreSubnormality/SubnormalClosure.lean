/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.IsSubnormal

/-!
# Isaacs Ch. 9 — §9D: strong conjugacy と `X^{(G)}` (pp. 289-290)

Isaacs, *Finite Group Theory* (AMS GSM 92), §9D の導入部と **Lemma 9.29**。

⚠ **`.mmd` はこの節の冒頭 (書籍 p.289) を `[MISSING_PAGE_FAIL]` で落としている**ので
定義は PDF から直接取った (PDF page 302 = 書籍 p.289):

> `X, Y ⊆ G` が **strongly conjugate** (強共役) とは, `X` と `Y` が `⟨X, Y⟩` の中で
> 共役であること (同値: 両方を含む**任意の**部分群の中で共役)。強共役は反射的・対称的だが
> **一般には推移的でない** (同値関係ではない)。
>
> `X ⊆ G` の **subnormal closure** `X^{••G}` は `X` を含む最小の subnormal 部分群。
> `X^{••G} ⊆ X^G` で, `X ◁◁ G ↔ X = X^{••G}`。

`X^{(G)}` = `X` の強共役たちが生成する部分群。Bartels の定理 (9.28) は
`X^{(G)} = X^{••G}` を主張する。本ファイルはその手前の Lemma 9.29 までを扱う。

## 実装方針

書籍の `X^{(K)}` (`X ⊆ K ⊆ G` に対し **`K` の中での**強共役が生成する部分群) は、
本実装では `strongClosureIn K X` として `G` の部分群のまま扱う。これは書籍 p.290 の観察

> The strong conjugates of `X` in `K` are exactly those strong conjugates of `X` in `G`
> that are contained in `K`.

を**定義の側で吸収**したもの — 強共役性は「`⟨X, Y⟩` の中で共役」という**内在的**条件なので、
`X, Y ≤ K` である限り周囲の群に依らない。おかげで 9.29(c)(d) が `sSup` の単調性に落ちる。

Lemma 9.29(a) の証明は書籍では `|G|` の帰納だが、ここでも 9.31 と同じく
**`Subgroup.IsSubnormal` の構造帰納**を使う (`Ch09_MoreSubnormality/SylowSubnormal.lean`
と同じ手口)。降りる先の normal 段は「`g ∈ K` なら `g • S = S`」だけなので自明になる。
-/

namespace OddOrder.Isaacs.Ch09

open scoped Pointwise

variable {G : Type*} [Group G]

section /- 9D: strong conjugacy (pp. 289-290) -/

/-- **強共役** (Isaacs p. 289): `X` と `Y` が `⟨X, Y⟩ = X ⊔ Y` の中で共役であること。

反射的・対称的だが**推移的でない** (書籍が明記する通り, 同値関係ではない)。 -/
def IsStronglyConjugate (X Y : Subgroup G) : Prop :=
  ∃ g ∈ X ⊔ Y, ConjAct.toConjAct g • X = Y

theorem IsStronglyConjugate.rfl (X : Subgroup G) : IsStronglyConjugate X X :=
  ⟨1, one_mem _, by simp⟩

theorem IsStronglyConjugate.symm {X Y : Subgroup G} (h : IsStronglyConjugate X Y) :
    IsStronglyConjugate Y X := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨g⁻¹, by rw [sup_comm]; exact inv_mem hg, ?_⟩
  rw [ConjAct.toConjAct_inv, inv_smul_smul]

/-- **`X^{(K)}`** (Isaacs p. 290): `K` の中での `X` の強共役たちが生成する部分群。

強共役性は内在的 (`⟨X, Y⟩` の中で共役) なので, 書籍の「`K` 内の強共役 = `G` 内の強共役で
`K` に含まれるもの」はここでは定義そのもの。 -/
def strongClosureIn (K X : Subgroup G) : Subgroup G :=
  sSup {Y | IsStronglyConjugate X Y ∧ Y ≤ K}

/-- **`X^{(G)}`** (Isaacs p. 290): `X` の強共役たちが生成する部分群。 -/
def strongClosure (X : Subgroup G) : Subgroup G := sSup {Y | IsStronglyConjugate X Y}

theorem strongClosureIn_top (X : Subgroup G) : strongClosureIn ⊤ X = strongClosure X := by
  simp [strongClosureIn, strongClosure]

theorem le_strongClosure (X : Subgroup G) : X ≤ strongClosure X :=
  le_sSup (IsStronglyConjugate.rfl X)

theorem le_strongClosureIn {K X : Subgroup G} (hXK : X ≤ K) : X ≤ strongClosureIn K X :=
  le_sSup ⟨IsStronglyConjugate.rfl X, hXK⟩

theorem strongClosure_le {X S : Subgroup G} (h : ∀ Y, IsStronglyConjugate X Y → Y ≤ S) :
    strongClosure X ≤ S := sSup_le h

theorem strongClosureIn_le_right (K X : Subgroup G) : strongClosureIn K X ≤ K :=
  sSup_le fun _ hY => hY.2

/-! ### Lemma 9.29 -/

/-- **Isaacs Lemma 9.29(a)** (p. 290): `X ⊆ S ◁◁ G` なら `X^{(G)} ⊆ S`.

書籍は `|G|` の帰納だが, `Subgroup.IsSubnormal` が inductive predicate なので
その構造帰納で置き換えられる:
* `top` 段 (`S = ⊤`): 自明。
* `step` 段 (`S ≤ K`, `K ◁◁ G`, `S ◁ K`): 帰納法の仮定で `X^{(G)} ≤ K`, ゆえ
  すべての強共役 `Y = g • X` の共役元 `g` は `X ⊔ Y ≤ K` に属する。`S ◁ K` なので
  `g • S = S`, したがって `Y = g • X ≤ g • S = S`。 -/
theorem strongClosure_le_of_isSubnormal {S : Subgroup G} (hS : S.IsSubnormal) :
    ∀ X : Subgroup G, X ≤ S → strongClosure X ≤ S := by
  induction hS with
  | top => intro X _; exact le_top
  | step S K hle hKsub hSnorm ih =>
    intro X hXS
    -- 帰納法の仮定: `X^{(G)} ≤ K` (X ≤ S ≤ K なので適用できる).
    have hXK : strongClosure X ≤ K := ih X (hXS.trans hle)
    -- `S ◁ K` を normalizer の言葉に直す.
    have hnorm : K ≤ Subgroup.normalizer S :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hSnorm
    refine strongClosure_le ?_
    rintro Y ⟨g, hg, rfl⟩
    -- `g ∈ X ⊔ (g • X) ≤ X^{(G)} ≤ K`.
    have hgK : g ∈ K := by
      refine hXK (sup_le (le_strongClosure X) ?_ hg)
      exact le_sSup ⟨g, hg, rfl⟩
    -- `g` は `S` を正規化するので `g • X ≤ g • S = S`.
    have hgS : ConjAct.toConjAct g • S = S :=
      Subgroup.conjAct_pointwise_smul_eq_self (hnorm hgK)
    calc ConjAct.toConjAct g • X
        ≤ ConjAct.toConjAct g • S := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hXS
      _ = S := hgS

/-- **Isaacs Lemma 9.29(b)** (p. 290): `Y ⊆ X ⊆ G` なら `Y^{(G)} ⊆ X^{(G)}`.

書籍 p.290: `Z = g • Y` が `Y` の強共役 (`g ∈ Y ⊔ Z`) なら, `Y ≤ X` より
`Y ⊔ Z ≤ X ⊔ g • X` なので `g ∈ X ⊔ g • X`, すなわち `g • X` は `X` の強共役。
よって `Z = g • Y ≤ g • X ≤ X^{(G)}`. -/
theorem strongClosure_mono {Y X : Subgroup G} (h : Y ≤ X) :
    strongClosure Y ≤ strongClosure X := by
  refine sSup_le ?_
  rintro Z ⟨g, hg, rfl⟩
  -- `g ∈ Y ⊔ g • Y ≤ X ⊔ g • X`.
  have hsmul : ConjAct.toConjAct g • Y ≤ ConjAct.toConjAct g • X :=
    Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h
  have hgX : g ∈ X ⊔ ConjAct.toConjAct g • X := sup_le_sup h hsmul hg
  exact hsmul.trans (le_sSup ⟨g, hgX, rfl⟩)

/-- **Isaacs Lemma 9.29(c)** (p. 290): `X ⊆ K ⊆ G` なら `X^{(K)} ⊆ X^{(G)}`.

`K` 内の強共役は `G` 内の強共役の部分集合 (本実装では定義そのもの) なので `sSup` の単調性。 -/
theorem strongClosureIn_le (K X : Subgroup G) : strongClosureIn K X ≤ strongClosure X :=
  sSup_le fun _ hY => le_sSup hY.1

/-- **Isaacs Lemma 9.29(d)** (p. 290): `X^{(G)} ⊆ K ⊆ G` なら `X^{(K)} = X^{(G)}`.

`K` が `X` の強共役をすべて含むので, `K` 内の強共役の族と `G` 内の族が一致する。 -/
theorem strongClosureIn_eq_strongClosure {K X : Subgroup G} (hK : strongClosure X ≤ K) :
    strongClosureIn K X = strongClosure X :=
  le_antisymm (strongClosureIn_le K X)
    (sSup_le fun _ hY => le_sSup ⟨hY, (le_sSup hY).trans hK⟩)

/-- **Isaacs Lemma 9.29(d) 系**: `K = X^{(G)}` なら `K = X^{(K)}` (書籍の "in particular")。 -/
theorem strongClosureIn_self (X : Subgroup G) :
    strongClosureIn (strongClosure X) X = strongClosure X :=
  strongClosureIn_eq_strongClosure le_rfl

end

end OddOrder.Isaacs.Ch09
