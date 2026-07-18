/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IsSubnormal
import OddOrder.Isaacs.Ch02_Subnormality.Basic
import OddOrder.Isaacs.Ch09_MoreSubnormality.SylowSubnormal

/-!
# Isaacs Ch. 9 — §9D: strong conjugacy, `X^{(G)}`, Lem 9.29 / 9.30 (pp. 289-291)

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
`X^{(G)} = X^{••G}` を主張する。**本ファイルはその手前の Lemma 9.29 / 9.30 まで**を扱い,
9.28 本体は sibling の `SubnormalClosure.lean` にある (issue 0103 方式の prefix-split)。

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

universe u

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

/-- 部分群の共役 `ConjAct` 作用を `Subgroup.map` で書き換える (以下の計算用). -/
theorem conjAct_smul_eq_map (g : G) (X : Subgroup G) :
    ConjAct.toConjAct g • X = X.map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [Subgroup.pointwise_smul_def, Subgroup.mem_map,
    MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply,
    ConjAct.toConjAct_smul, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]

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

/-! ### 共役との両立 (Isaacs p. 290, 9.29 直前の観察) -/

/-- pointwise 共役作用は部分群の `⊔` と可換。 -/
theorem conjAct_smul_sup (c : ConjAct G) (X Y : Subgroup G) :
    c • (X ⊔ Y) = c • X ⊔ c • Y := by
  simp only [Subgroup.pointwise_smul_def]
  exact Subgroup.map_sup _ _ _

/-- 強共役性は共役で保たれる。 -/
theorem IsStronglyConjugate.conjAct_smul {X Y : Subgroup G} (h : IsStronglyConjugate X Y)
    (c : ConjAct G) : IsStronglyConjugate (c • X) (c • Y) := by
  obtain ⟨a, ha, rfl⟩ := h
  refine ⟨c • a, ?_, ?_⟩
  · rw [← conjAct_smul_sup]
    exact Subgroup.smul_mem_pointwise_smul a c _ ha
  · have hconj : ConjAct.toConjAct (c • a) = c * ConjAct.toConjAct a * c⁻¹ := by
      simp [ConjAct.smul_def, ConjAct.toConjAct_mul, ConjAct.toConjAct_inv]
    rw [hconj, mul_smul, mul_smul, inv_smul_smul]

/-- **Isaacs p. 290 の観察**: `(X^{(G)})^g = (X^g)^{(G)}`. -/
theorem strongClosure_conjAct_smul (c : ConjAct G) (X : Subgroup G) :
    strongClosure (c • X) = c • strongClosure X := by
  -- 片方向を一般に示し, `c⁻¹` と `c • X` に適用して逆向きを得る.
  have key : ∀ (d : ConjAct G) (W : Subgroup G), strongClosure (d • W) ≤ d • strongClosure W := by
    intro d W
    refine sSup_le ?_
    intro V hV
    have hback : IsStronglyConjugate W (d⁻¹ • V) := by
      have := hV.conjAct_smul d⁻¹
      rwa [inv_smul_smul] at this
    calc V = d • (d⁻¹ • V) := (smul_inv_smul d V).symm
      _ ≤ d • strongClosure W :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (le_sSup hback)
  refine le_antisymm (key c X) ?_
  have h2 := key c⁻¹ (c • X)
  rw [inv_smul_smul] at h2
  calc c • strongClosure X ≤ c • (c⁻¹ • strongClosure (c • X)) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h2
    _ = strongClosure (c • X) := smul_inv_smul c _

/-! ### 部分群への制限 (`X^{(K)}` と `↥K` 内の `X^{(G)}` の橋)

Bartels (9.28) の帰納法の仮定は「`G` より小さい**群**」について述べられるので, 書籍が
`X^{(K)}` と書くところを `↥K` の中で計算した `strongClosure (X.subgroupOf K)` に
読み替える必要がある。本実装の `strongClosureIn K X` (= `G` の部分群のまま持つ形) と
それを繋ぐのが以下。 -/

/-- `g ∈ K`, `X ≤ K` なら共役 `X^g` も `K` に含まれる。 -/
theorem conjAct_smul_le_of_mem {K X : Subgroup G} (hXK : X ≤ K) {g : G} (hg : g ∈ K) :
    ConjAct.toConjAct g • X ≤ K := by
  rw [conjAct_smul_eq_map]
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hg (hXK hx)) (inv_mem hg)

/-- 共役は `subgroupOf` と可換 (共役元が `K` に属するとき)。 -/
theorem conjAct_smul_subgroupOf {K X : Subgroup G} (g : ↥K) :
    (ConjAct.toConjAct (g : G) • X).subgroupOf K = ConjAct.toConjAct g • (X.subgroupOf K) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_subgroupOf]
  congr! 1

/-- **強共役性は `K` への制限と両立する** (`X, Y ≤ K` のとき)。

書籍 p.290 の「`K` 内の強共役 = `G` 内の強共役で `K` に含まれるもの」の, 本実装
(`G` の部分群のまま持つ形) と `↥K` の中で計算する形との橋。 -/
theorem isStronglyConjugate_subgroupOf_iff {K X Y : Subgroup G} (hXK : X ≤ K) (hYK : Y ≤ K) :
    IsStronglyConjugate (X.subgroupOf K) (Y.subgroupOf K) ↔ IsStronglyConjugate X Y := by
  constructor
  · rintro ⟨g, hg, hgX⟩
    refine ⟨(g : G), ?_, ?_⟩
    · rw [← Subgroup.subgroupOf_sup hXK hYK, Subgroup.mem_subgroupOf] at hg
      exact hg
    · -- 両辺は `K` に含まれるので `subgroupOf K` の単射性で比較する.
      have hle : ConjAct.toConjAct (g : G) • X ≤ K := conjAct_smul_le_of_mem hXK g.2
      have := (conjAct_smul_subgroupOf (K := K) (X := X) g).trans hgX
      have hmap := congrArg (fun W : Subgroup ↥K => W.map K.subtype) this
      simpa [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_subgroupOf_eq_of_le hYK]
        using hmap
  · rintro ⟨g, hg, rfl⟩
    have hgK : g ∈ K := (sup_le hXK hYK) hg
    refine ⟨⟨g, hgK⟩, ?_, ?_⟩
    · rw [← Subgroup.subgroupOf_sup hXK hYK, Subgroup.mem_subgroupOf]
      exact hg
    · exact (conjAct_smul_subgroupOf (K := K) (X := X) ⟨g, hgK⟩).symm

/-- **`X^{(K)}` の橋**: `X ≤ K` なら `strongClosureIn K X` は `↥K` の中で計算した
`X^{(G)}` の像に一致する。 -/
theorem strongClosureIn_eq_map_strongClosure {K X : Subgroup G} (hXK : X ≤ K) :
    strongClosureIn K X = (strongClosure (X.subgroupOf K)).map K.subtype := by
  refine le_antisymm (sSup_le ?_) ?_
  · rintro Y ⟨hY, hYK⟩
    calc Y = (Y.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hYK).symm
      _ ≤ _ := Subgroup.map_mono
          (le_sSup ((isStronglyConjugate_subgroupOf_iff hXK hYK).mpr hY))
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    intro W hW
    rw [← Subgroup.map_le_iff_le_comap]
    have hWK : W.map K.subtype ≤ K := by
      rintro _ ⟨w, _, rfl⟩; exact w.2
    have hround : (W.map K.subtype).subgroupOf K = W := by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    have hconj : IsStronglyConjugate (X.subgroupOf K) ((W.map K.subtype).subgroupOf K) := by
      rw [hround]; exact hW
    exact le_sSup ⟨(isStronglyConjugate_subgroupOf_iff hXK hWK).mp hconj, hWK⟩

/-! ### Lemma 9.29 の相対版 (`X^{(K)}` 形)

Bartels (9.28) の Step 1-5 は 9.29 を「`G` の中」ではなく「部分群 `K` の中」で
繰り返し使う。本実装では `strongClosureIn` がそのまま `X^{(K)}` なので (c)(d) は
`sSup` の単調性で済み, (a) だけが上の橋を経由する。 -/

/-- **9.29(c) の相対版**: `K ≤ L` なら `X^{(K)} ≤ X^{(L)}`. -/
theorem strongClosureIn_mono_left {K L X : Subgroup G} (hKL : K ≤ L) :
    strongClosureIn K X ≤ strongClosureIn L X :=
  sSup_le fun _ hY => le_sSup ⟨hY.1, hY.2.trans hKL⟩

/-- **9.29(d) の相対版**: `X^{(L)} ≤ K ≤ L` なら `X^{(K)} = X^{(L)}`. -/
theorem strongClosureIn_eq_of_le {K L X : Subgroup G} (hKL : K ≤ L)
    (hLK : strongClosureIn L X ≤ K) : strongClosureIn K X = strongClosureIn L X :=
  le_antisymm (strongClosureIn_mono_left hKL)
    (sSup_le fun _ hY => le_sSup ⟨hY.1, (le_sSup hY).trans hLK⟩)

/-- **9.29(d) の相対版・系**: `X^{(L)}` は自分自身の中で閉じている (`K = X^{(L)}` の場合)。 -/
theorem strongClosureIn_strongClosureIn (L X : Subgroup G) :
    strongClosureIn (strongClosureIn L X) X = strongClosureIn L X :=
  strongClosureIn_eq_of_le (strongClosureIn_le_right L X) le_rfl

/-- **9.29(a) の相対版**: `X ≤ S ≤ K` で `S` が `K` の中で subnormal なら `X^{(K)} ≤ S`.

上の橋 (`strongClosureIn_eq_map_strongClosure`) で `↥K` に降ろし, そこで絶対版
`strongClosure_le_of_isSubnormal` を使う。 -/
theorem strongClosureIn_le_of_isSubnormal {K S X : Subgroup G} (hXS : X ≤ S) (hSK : S ≤ K)
    (hS : (S.subgroupOf K).IsSubnormal) : strongClosureIn K X ≤ S := by
  have hXK : X ≤ K := hXS.trans hSK
  rw [strongClosureIn_eq_map_strongClosure hXK]
  calc (strongClosure (X.subgroupOf K)).map K.subtype
      ≤ (S.subgroupOf K).map K.subtype :=
        Subgroup.map_mono
          (strongClosure_le_of_isSubnormal hS _ (Subgroup.comap_mono hXS))
    _ = S := Subgroup.map_subgroupOf_eq_of_le hSK

section /- 9D: Lemma 9.30 — 商への移行 (pp. 290-291) -/

variable {H : Type*} [Group H]

/-- 共役と準同型像の交換: `f(X^g) = f(X)^{f(g)}`. -/
theorem map_conjAct_smul (g : G) (X : Subgroup G) (f : G →* H) :
    (ConjAct.toConjAct g • X).map f = ConjAct.toConjAct (f g) • (X.map f) := by
  rw [conjAct_smul_eq_map, conjAct_smul_eq_map, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

/-- **Isaacs Lemma 9.30 の easy direction** (書籍 p.291 第 1 段): 強共役は準同型で保たれる。

`Y = X^g` (`g ∈ ⟨X, Y⟩`) なら `f(Y) = f(X)^{f(g)}` かつ
`f(g) ∈ f(⟨X, Y⟩) = ⟨f(X), f(Y)⟩`。 -/
theorem IsStronglyConjugate.map {X Y : Subgroup G} (h : IsStronglyConjugate X Y) (f : G →* H) :
    IsStronglyConjugate (X.map f) (Y.map f) := by
  obtain ⟨g, hg, rfl⟩ := h
  refine ⟨f g, ?_, ?_⟩
  · rw [← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem f hg
  · exact (map_conjAct_smul g X f).symm

/-- **Isaacs Lemma 9.30 の `≤` 方向**: `f(X^{(G)}) ≤ f(X)^{(H)}`.

書籍 p.291 の「`G` 内の強共役は `H` 内の強共役へ写る」の easy half。逆向き (全射 `f` での
等号) は `⟨X, Y⟩` の位数最小性を使う議論 (書籍 p.291 後半)。 -/
theorem strongClosure_map_le (X : Subgroup G) (f : G →* H) :
    (strongClosure X).map f ≤ strongClosure (X.map f) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le ?_
  intro Y hY
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (hY.map f)

/-- **Isaacs Lemma 9.30 の hard direction** (書籍 p.291 後半): 全射 `f` に対し,
`f(X)` の強共役は必ず `X` の強共役の像として得られる。

書籍の議論: `Z` を `f(X)` の強共役とし,
`𝒴 = {Y | Y は X の共役 かつ f(Y) = Z}` の中で `|⟨X, Y⟩|` が最小のものを取る
(`Z` は `f(X)` の共役なので `𝒴` は非空)。`ḡ ∈ ⟨f(X), Z⟩ = f(⟨X, Y⟩)` を
`g ∈ ⟨X, Y⟩` に持ち上げると `Y' = X^g ∈ 𝒴` かつ `⟨X, Y'⟩ ≤ ⟨X, Y⟩` なので
最小性から `⟨X, Y'⟩ = ⟨X, Y⟩`。よって `g ∈ ⟨X, Y'⟩` で `Y'` は `X` の強共役。 -/
theorem exists_isStronglyConjugate_map_eq [Finite G] {X : Subgroup G} (f : G →* H)
    (hf : Function.Surjective f) {Z : Subgroup H}
    (hZ : IsStronglyConjugate (X.map f) Z) :
    ∃ Y : Subgroup G, IsStronglyConjugate X Y ∧ Y.map f = Z := by
  classical
  obtain ⟨gbar, hgbar, hgbarZ⟩ := hZ
  set 𝒴 : Set (Subgroup G) := {Y | (∃ a : G, ConjAct.toConjAct a • X = Y) ∧ Y.map f = Z} with h𝒴
  -- 非空性: `ḡ` を `g₀` に持ち上げれば `X^{g₀} ∈ 𝒴`.
  obtain ⟨g₀, hg₀⟩ := hf gbar
  have hY₀ : ConjAct.toConjAct g₀ • X ∈ 𝒴 := by
    refine ⟨⟨g₀, rfl⟩, ?_⟩
    rw [map_conjAct_smul, hg₀]; exact hgbarZ
  -- `|⟨X, Y⟩|` を最小にする `Y ∈ 𝒴` を選ぶ (ℕ の整列性).
  set S : Set ℕ := {n | ∃ Y, Y ∈ 𝒴 ∧ Nat.card ↥(X ⊔ Y) = n} with hS
  have hSne : S.Nonempty := ⟨_, _, hY₀, rfl⟩
  obtain ⟨Y, hY, hYcard⟩ := Nat.sInf_mem hSne
  have hYmin : ∀ Y' ∈ 𝒴, Nat.card ↥(X ⊔ Y) ≤ Nat.card ↥(X ⊔ Y') := by
    intro Y' hY'
    rw [hYcard]
    exact Nat.sInf_le ⟨Y', hY', rfl⟩
  -- `ḡ ∈ f(X) ⊔ Z = f(X ⊔ Y)` を `g ∈ X ⊔ Y` に持ち上げる.
  have hsup : (X ⊔ Y).map f = X.map f ⊔ Z := by rw [Subgroup.map_sup, hY.2]
  obtain ⟨g, hgmem, hgf⟩ : ∃ g ∈ X ⊔ Y, f g = gbar := by
    have hmem : gbar ∈ (X ⊔ Y).map f := by rw [hsup]; exact hgbar
    exact Subgroup.mem_map.mp hmem
  -- `Y' = X^g` も `𝒴` に属する.
  set Y' : Subgroup G := ConjAct.toConjAct g • X with hY'def
  have hY'mem : Y' ∈ 𝒴 := by
    refine ⟨⟨g, rfl⟩, ?_⟩
    rw [hY'def, map_conjAct_smul, hgf]; exact hgbarZ
  -- `⟨X, Y'⟩ ≤ ⟨X, Y⟩` (g ∈ ⟨X, Y⟩ ゆえ `X^g ≤ ⟨X, Y⟩`).
  have hle : X ⊔ Y' ≤ X ⊔ Y := by
    refine sup_le le_sup_left ?_
    rw [hY'def, conjAct_smul_eq_map]
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hgmem ((le_sup_left : X ≤ X ⊔ Y) hx)) (inv_mem hgmem)
  -- 最小性から等号, ゆえ `g ∈ ⟨X, Y'⟩`.
  have heq : X ⊔ Y' = X ⊔ Y :=
    Subgroup.eq_of_le_of_card_ge hle (hYmin Y' hY'mem)
  exact ⟨Y', ⟨g, heq ▸ hgmem, rfl⟩, hY'mem.2⟩

/-- **Isaacs Lemma 9.30** (p. 290-291): `N ⊴ G`, `Ḡ = G/N` のとき `X^{(G)}` の像は
`X̄^{(Ḡ)}` に等しい (より一般に任意の全射準同型で成立)。 -/
theorem strongClosure_map [Finite G] (X : Subgroup G) (f : G →* H)
    (hf : Function.Surjective f) :
    (strongClosure X).map f = strongClosure (X.map f) := by
  refine le_antisymm (strongClosure_map_le X f) (sSup_le ?_)
  intro Z hZ
  obtain ⟨Y, hY, rfl⟩ := exists_isStronglyConjugate_map_eq f hf hZ
  exact Subgroup.map_mono (le_sSup hY)

end

end OddOrder.Isaacs.Ch09
