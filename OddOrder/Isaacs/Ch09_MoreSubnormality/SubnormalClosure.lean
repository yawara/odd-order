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

/-- **`X^{(K)}` の共役両立性**: `(X^{(K)})^g = (X^g)^{(K^g)}`.

絶対版 `strongClosure_conjAct_smul` の相対版。Bartels Step 3 が
`(Y^h)^{(H)} = (Y^{(H)})^h` (`h ∈ H`) の形で使う。 -/
theorem strongClosureIn_conjAct_smul (c : ConjAct G) (K X : Subgroup G) :
    strongClosureIn (c • K) (c • X) = c • strongClosureIn K X := by
  have key : ∀ (d : ConjAct G) (L W : Subgroup G),
      strongClosureIn (d • L) (d • W) ≤ d • strongClosureIn L W := by
    intro d L W
    refine sSup_le ?_
    rintro V ⟨hV, hVL⟩
    have hback : IsStronglyConjugate W (d⁻¹ • V) := by
      have := hV.conjAct_smul d⁻¹
      rwa [inv_smul_smul] at this
    have hbackL : d⁻¹ • V ≤ L := by
      have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := d⁻¹) |>.mpr hVL
      rwa [inv_smul_smul] at this
    calc V = d • (d⁻¹ • V) := (smul_inv_smul d V).symm
      _ ≤ d • strongClosureIn L W :=
          Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (le_sSup ⟨hback, hbackL⟩)
  refine le_antisymm (key c K X) ?_
  have h2 := key c⁻¹ (c • K) (c • X)
  rw [inv_smul_smul, inv_smul_smul] at h2
  calc c • strongClosureIn K X ≤ c • (c⁻¹ • strongClosureIn (c • K) (c • X)) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h2
    _ = strongClosureIn (c • K) (c • X) := smul_inv_smul c _

/-- `h ∈ K` なら `K` は `h` による共役で不変。 -/
theorem conjAct_smul_self_of_mem {K : Subgroup G} {h : G} (hh : h ∈ K) :
    ConjAct.toConjAct h • K = K :=
  Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hh)

/-- `ConjAct` による共役作用と `MulAut.conj` による共役作用は一致する
(mathlib の `Sylow` は後者を使うので橋が要る)。 -/
theorem conjAct_smul_eq_mulAut_smul (g : G) (X : Subgroup G) :
    ConjAct.toConjAct g • X = MulAut.conj g • X := by
  rw [conjAct_smul_eq_map, Subgroup.pointwise_smul_def]
  rfl

/-- **有限群の `p`-部分群は与えられた Sylow `p`-部分群の中へ共役で送れる**。

mathlib は `IsPGroup.exists_le_sylow` (ある Sylow に入る) と Sylow の共役性を
別々に持つだけなので, その 2 つを繋ぐ。Bartels Step 3 が使う。 -/
theorem exists_conjAct_smul_le_sylow {L : Type*} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup L} (hQ : IsPGroup p Q) (P : Sylow p L) :
    ∃ g : L, ConjAct.toConjAct g • Q ≤ (P : Subgroup L) := by
  obtain ⟨R, hR⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L R P
  refine ⟨g, ?_⟩
  rw [conjAct_smul_eq_mulAut_smul]
  calc MulAut.conj g • Q ≤ MulAut.conj g • (R : Subgroup L) :=
        Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hR
    _ = ((g • R : Sylow p L) : Subgroup L) := Sylow.coe_subgroup_smul.symm
    _ = (P : Subgroup L) := by rw [hg]

/-! ### Bartels Step 3 の部品 — 相対版 (すべて `Subgroup G` のまま)

`↥H` / `↥L` を ambient にすると `Sylow p ↥(L.subgroupOf H)` のような二重 subtype が
出てしまうので, 9.31 と「p-部分群の Sylow 内共役」を `Subgroup G` の言葉に直しておく。
どちらも 9.29(a) 相対版と同じく「↥K に降ろして絶対版を使う」だけ。 -/

/-- **Lem 9.31 の相対版**: `S ≤ K` が `K` の中で subnormal, `P ≤ K` が `K` の Sylow `p`
なら `P ⊓ S` は `S` の Sylow `p` (指数が `p` と互いに素)。 -/
theorem not_dvd_relIndex_inf_of_isSubnormal_in [Finite G] {p : ℕ} [Fact p.Prime]
    {K S P : Subgroup G} (hSK : S ≤ K)
    (hS : (S.subgroupOf K).IsSubnormal) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex K) :
    ¬ p ∣ (P ⊓ S).relIndex S := by
  have hPsub : IsPGroup p ↥(P.subgroupOf K) := hP.comap_subtype
  have hidx : ¬ p ∣ (P.subgroupOf K).index := hPidx
  have habs := not_dvd_relIndex_inf_of_isSubnormal hS (hPsub.toSylow hidx)
  have hinf : P.subgroupOf K ⊓ S.subgroupOf K = (P ⊓ S).subgroupOf K := by
    ext x; simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  rw [hPsub.toSylow_coe hidx, hinf, Subgroup.relIndex_subgroupOf hSK] at habs
  exact habs

/-- **p-部分群の Sylow 内共役, 相対版**: `Y ≤ L` が `p`-群, `Q ≤ L` が `L` の Sylow `p`
なら, ある `h ∈ L` で `Y^h ≤ Q`。 -/
theorem exists_mem_conjAct_smul_le_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {L Y Q : Subgroup G} (hYL : Y ≤ L) (hQL : Q ≤ L) (hY : IsPGroup p ↥Y)
    (hQ : IsPGroup p ↥Q) (hQidx : ¬ p ∣ Q.relIndex L) :
    ∃ h ∈ L, ConjAct.toConjAct h • Y ≤ Q := by
  have hQsub : IsPGroup p ↥(Q.subgroupOf L) := hQ.comap_subtype
  have hidx : ¬ p ∣ (Q.subgroupOf L).index := hQidx
  obtain ⟨g, hg⟩ := exists_conjAct_smul_le_sylow (Q := Y.subgroupOf L) hY.comap_subtype
    (hQsub.toSylow hidx)
  rw [hQsub.toSylow_coe hidx, ← conjAct_smul_subgroupOf] at hg
  refine ⟨(g : G), g.2, ?_⟩
  have hmap := Subgroup.map_mono (f := L.subtype) hg
  rwa [Subgroup.map_subgroupOf_eq_of_le (conjAct_smul_le_of_mem hYL g.2),
    Subgroup.map_subgroupOf_eq_of_le hQL] at hmap

section /- 9D: Bartels Step 2 の部品 — 真部分群による生成 -/

/-- `Nat.Coprime a b` なら `x ∈ ⟨x^a⟩ ⊔ ⟨x^b⟩` (Bezout)。 -/
theorem mem_sup_zpowers_of_coprime {x : G} {a b : ℕ} (h : Nat.Coprime a b) :
    x ∈ Subgroup.zpowers (x ^ a) ⊔ Subgroup.zpowers (x ^ b) := by
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (a : ℤ) * u + (b : ℤ) * v = 1 := by
    refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
    have hg := Nat.gcd_eq_gcd_ab a b
    rw [Nat.Coprime.gcd_eq_one h] at hg
    push_cast at hg ⊢
    linarith
  have hx : x = (x ^ a) ^ u * (x ^ b) ^ v := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, huv, zpow_one]
  have hmem : (x ^ a) ^ u * (x ^ b) ^ v ∈ Subgroup.zpowers (x ^ a) ⊔ Subgroup.zpowers (x ^ b) :=
    mul_mem
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) u))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) v))
  rwa [← hx] at hmem

end

/-- `p ∣ orderOf x`, `p` 素数のとき `⟨x^p⟩` は `⟨x⟩` の真部分群。 -/
theorem zpowers_pow_lt_zpowers [Finite G] {x : G} {p : ℕ} (hp : 1 < p) (hpd : p ∣ orderOf x) :
    Subgroup.zpowers (x ^ p) < Subgroup.zpowers x := by
  have hord : 0 < orderOf x := orderOf_pos x
  have hle : Subgroup.zpowers (x ^ p) ≤ Subgroup.zpowers x :=
    (Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) p)
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hcard : Nat.card ↥(Subgroup.zpowers (x ^ p)) = Nat.card ↥(Subgroup.zpowers x) := by
    rw [heq]
  rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_pow, Nat.gcd_eq_right hpd] at hcard
  have : orderOf x / p < orderOf x := Nat.div_lt_self hord hp
  omega

/-- **Bartels Step 2 の部品**: `p`-群でない有限群 (の部分群) は真部分群たちで生成される。

`x ∈ X` をとり, `⟨x⟩ < X` なら済み。`⟨x⟩ = X` なら `X` は巡回で, `p`-群でないことから
位数は相異なる 2 素数 `p ≠ q` で割れる。`⟨x^p⟩`, `⟨x^q⟩` はいずれも真部分群で,
`Nat.Coprime p q` から `x ∈ ⟨x^p⟩ ⊔ ⟨x^q⟩` (Bezout)。 -/
theorem le_sSup_lt_of_forall_not_isPGroup [Finite G] {X : Subgroup G}
    (h : ∀ p : ℕ, p.Prime → ¬ IsPGroup p ↥X) :
    X ≤ sSup {Y : Subgroup G | Y < X} := by
  intro x hx
  have hCX : Subgroup.zpowers x ≤ X := (Subgroup.zpowers_le).mpr hx
  have hcard0 : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
  rcases lt_or_eq_of_le hCX with hlt | heq
  · have hsub : Subgroup.zpowers x ≤ sSup {Y : Subgroup G | Y < X} := le_sSup hlt
    exact hsub (Subgroup.mem_zpowers x)
  -- `X = ⟨x⟩` (巡回) の場合.
  have hnX : Nat.card ↥X = orderOf x := by rw [← heq, Nat.card_zpowers]
  have hone : Nat.card ↥X ≠ 1 := fun h1 =>
    h 2 Nat.prime_two (IsPGroup.of_card (n := 0) (by simpa using h1))
  obtain ⟨p, hp⟩ : (Nat.card ↥X).primeFactors.Nonempty := by
    refine Nat.nonempty_primeFactors.mpr ?_
    have := Nat.card_pos (α := ↥X)
    omega
  obtain ⟨q, hq, hqp⟩ : ∃ q ∈ (Nat.card ↥X).primeFactors, q ≠ p := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥X → r = p := fun r hr hrd =>
      hcon r (Nat.mem_primeFactors.mpr ⟨hr, hrd, hcard0⟩)
    exact h p (Nat.prime_of_mem_primeFactors hp)
      (IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hcard0
        (fun {r} hr hrd => hall r hr hrd)))
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqq : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hpd : p ∣ orderOf x := hnX ▸ Nat.dvd_of_mem_primeFactors hp
  have hqd : q ∣ orderOf x := hnX ▸ Nat.dvd_of_mem_primeFactors hq
  have hltp : Subgroup.zpowers (x ^ p) < X := by
    rw [← heq]; exact zpowers_pow_lt_zpowers hpp.one_lt hpd
  have hltq : Subgroup.zpowers (x ^ q) < X := by
    rw [← heq]; exact zpowers_pow_lt_zpowers hqq.one_lt hqd
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hpp hqq).mpr (Ne.symm hqp)
  have hsub : Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers (x ^ q)
      ≤ sSup {Y : Subgroup G | Y < X} := sup_le (le_sSup hltp) (le_sSup hltq)
  exact hsub (mem_sup_zpowers_of_coprime (x := x) hcop)

section /- 9D: Theorem 9.28 (Bartels) — Step 1 (p. 291) -/

/-- `X ≤ K` のとき, `X^{(K)}` を `↥K` に降ろすと `↥K` の中の `X^{(↥K)}` に一致する。 -/
theorem strongClosureIn_subgroupOf {K X : Subgroup G} (hXK : X ≤ K) :
    (strongClosureIn K X).subgroupOf K = strongClosure (X.subgroupOf K) := by
  rw [strongClosureIn_eq_map_strongClosure hXK, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective]

/-- 有限群の真部分群は位数が真に小さい。 -/
theorem card_lt_of_ne_top [Finite G] {K : Subgroup G} (hK : K ≠ ⊤) :
    Nat.card ↥K < Nat.card G := by
  have hmul := Subgroup.card_mul_index K
  have hidx : K.index ≠ 1 := fun h1 => hK (Subgroup.index_eq_one.mp h1)
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hpos : 0 < Nat.card ↥K := Nat.card_pos
  have h2 : 1 < K.index := by omega
  calc Nat.card ↥K < Nat.card ↥K * K.index := (Nat.lt_mul_iff_one_lt_right hpos).mpr h2
    _ = Nat.card G := hmul

/-- **Bartels (9.28) の帰納法の仮定**: `G` より真に位数の小さい群では `X^{(H)}` は subnormal。 -/
def BartelsIH (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ (H : Type u) [Group H] [Finite H], Nat.card H < Nat.card G →
    ∀ Y : Subgroup H, (strongClosure Y).IsSubnormal

/-- **Bartels (9.28) Step 1, 片側** (書籍 p. 291): `Y, Z ≤ H` が `Y^{(H)} = Z^{(H)}` を
みたし, `Y^{(G)} ≠ G` なら `Y^{(G)} ≤ Z^{(G)}`.

書籍は `Y, Z` を `X` の共役に取るが, 共役性は `Y^{(G)} < G` を出すためだけに使われる
ので, ここでは `Y^{(G)} ≠ ⊤` を直接の仮定にして一般化した。

**証明** (書籍 p.291): `K = Y^{(G)}`, `U = Y^{(H)} = Z^{(H)}` とおく。
`Z ≤ U ≤ K` で `K < G` なので帰納法の仮定から `Z^{(K)}` は `K` の中で subnormal。
9.29(d) で `U = Z^{(U)}` なので `Y ≤ U = Z^{(U)} ≤ Z^{(K)}` (9.29(c))。
9.29(a) を `K` の中で使って `Y^{(K)} ≤ Z^{(K)}`, 最後に `K = Y^{(K)}` (9.29(d)) と
`Z^{(K)} ≤ Z^{(G)}` (9.29(c)) を繋ぐ。 -/
theorem bartels_step_one_le {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {Y Z H : Subgroup G} (hYH : Y ≤ H) (hZH : Z ≤ H)
    (hU : strongClosureIn H Y = strongClosureIn H Z)
    (hK : strongClosure Y ≠ ⊤) :
    strongClosure Y ≤ strongClosure Z := by
  -- `Z ≤ U ≤ K`  (`U = Y^{(H)}`, `K = Y^{(G)}`).
  have hZU : Z ≤ strongClosureIn H Y := by rw [hU]; exact le_strongClosureIn hZH
  have hUK : strongClosureIn H Y ≤ strongClosure Y := strongClosureIn_le H Y
  have hZK : Z ≤ strongClosure Y := hZU.trans hUK
  -- 帰納法の仮定を `↥K` に適用: `Z^{(K)}` は `K` の中で subnormal.
  have hZKsub :
      ((strongClosureIn (strongClosure Y) Z).subgroupOf (strongClosure Y)).IsSubnormal := by
    rw [strongClosureIn_subgroupOf hZK]
    exact hIH ↥(strongClosure Y) (card_lt_of_ne_top hK) _
  -- `U = Z^{(U)}` (9.29(d) 相対版).
  have hUZ : strongClosureIn (strongClosureIn H Y) Z = strongClosureIn H Y := by
    rw [hU]; exact strongClosureIn_strongClosureIn H Z
  -- `Y ≤ U = Z^{(U)} ≤ Z^{(K)}`.
  have hYZK : Y ≤ strongClosureIn (strongClosure Y) Z :=
    ((le_strongClosureIn hYH).trans hUZ.ge).trans (strongClosureIn_mono_left hUK)
  -- 9.29(a) を `K` の中で適用.
  have hstep : strongClosureIn (strongClosure Y) Y ≤ strongClosureIn (strongClosure Y) Z :=
    strongClosureIn_le_of_isSubnormal hYZK (strongClosureIn_le_right _ Z) hZKsub
  calc strongClosure Y = strongClosureIn (strongClosure Y) Y := (strongClosureIn_self Y).symm
    _ ≤ strongClosureIn (strongClosure Y) Z := hstep
    _ ≤ strongClosure Z := strongClosureIn_le _ Z

/-- **Bartels (9.28) Step 1** (書籍 p. 291): `Y, Z ≤ H` が `Y^{(H)} = Z^{(H)}` をみたし
両者の `^{(G)}` が真部分群なら `Y^{(G)} = Z^{(G)}`. -/
theorem bartels_step_one {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {Y Z H : Subgroup G} (hYH : Y ≤ H) (hZH : Z ≤ H)
    (hU : strongClosureIn H Y = strongClosureIn H Z)
    (hKY : strongClosure Y ≠ ⊤) (hKZ : strongClosure Z ≠ ⊤) :
    strongClosure Y = strongClosure Z :=
  le_antisymm (bartels_step_one_le hIH hYH hZH hU hKY)
    (bartels_step_one_le hIH hZH hYH hU.symm hKZ)

end

/-- **Bartels (9.28) Step 2** (書籍 p. 291): 最小反例の `X` は `p`-群。

書籍の議論: `X` が `p`-群でなければ真部分群たちで生成される。
`U = ⟨Y^{(G)} | Y < X⟩` とおくと `X ≤ U ≤ X^{(G)}` (9.29(b))。`|X|` 最小性から各
`Y^{(G)}` は subnormal なので, Wielandt 結合定理の族版で `U ◁◁ G`。すると 9.29(a) で
`X^{(G)} ≤ U`, 逆包含と合わせて `X^{(G)} = U ◁◁ G` となり `X` が反例であることに矛盾。 -/
theorem bartels_step_two {G : Type u} [Group G] [Finite G] {X : Subgroup G}
    (hXmin : ∀ Y : Subgroup G, Y < X → (strongClosure Y).IsSubnormal)
    (hX : ¬ (strongClosure X).IsSubnormal) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p ↥X := by
  by_contra hcon
  push Not at hcon
  -- `U = ⟨Y^{(G)} | Y < X⟩`.
  set U : Subgroup G := sSup (strongClosure '' {Y : Subgroup G | Y < X}) with hUdef
  -- `X ≤ U` (真部分群で生成され, 各 `Y ≤ Y^{(G)}`).
  have hXU : X ≤ U := by
    refine (le_sSup_lt_of_forall_not_isPGroup hcon).trans (sSup_le ?_)
    intro Y hY
    exact (le_strongClosure Y).trans (le_sSup ⟨Y, hY, rfl⟩)
  -- `U ≤ X^{(G)}` (9.29(b)).
  have hUX : U ≤ strongClosure X := by
    refine sSup_le ?_
    rintro _ ⟨Y, hY, rfl⟩
    exact strongClosure_mono hY.le
  -- `U ◁◁ G` (Wielandt 結合定理の族版 + `|X|` 最小性).
  have hUsub : U.IsSubnormal := by
    refine OddOrder.Isaacs.Ch02.isSubnormal_sSup_of_isSubnormal ?_
    rintro _ ⟨Y, hY, rfl⟩
    exact hXmin Y hY
  -- 9.29(a) で `X^{(G)} ≤ U`, ゆえ `X^{(G)} = U ◁◁ G` で矛盾.
  exact hX (le_antisymm (strongClosure_le_of_isSubnormal hUsub X hXU) hUX ▸ hUsub)

/-- **Bartels (9.28) Step 3** (書籍 p. 291): `Y ≤ H < G` (`Y` は `p`-群) と `H` の
Sylow `p`-部分群 `P` に対し, `Y` の共役 `Z ≤ P` で `Z^{(H)} = Y^{(H)}` となるものが取れる。

書籍の議論: `H < G` なので帰納法の仮定で `L = Y^{(H)}` は `H` の中で subnormal。
Lem 9.31 (相対版) で `P ⊓ L` は `L` の Sylow `p`。`Y` は `L` の `p`-部分群なので
`h ∈ L` があって `Y^h ≤ P ⊓ L`。`h ∈ L ≤ H` より `H^h = H`, `L^h = L` なので
`(Y^h)^{(H)} = (Y^{(H)})^h = L`。

(書籍の結論 `Y^{(G)} = Z^{(G)}` は Step 1 を繋げば出る。) -/
theorem bartels_step_three {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {Y H P : Subgroup G} (hYH : Y ≤ H) (hH : H ≠ ⊤)
    (hY : IsPGroup p ↥Y) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex H) :
    ∃ h ∈ H, ConjAct.toConjAct h • Y ≤ P ∧
      strongClosureIn H (ConjAct.toConjAct h • Y) = strongClosureIn H Y := by
  have hYL : Y ≤ strongClosureIn H Y := le_strongClosureIn hYH
  have hLH : strongClosureIn H Y ≤ H := strongClosureIn_le_right H Y
  -- `Y^{(H)}` は `H` の中で subnormal (帰納法の仮定を ↥H に適用).
  have hLsub : ((strongClosureIn H Y).subgroupOf H).IsSubnormal := by
    rw [strongClosureIn_subgroupOf hYH]
    exact hIH ↥H (card_lt_of_ne_top hH) _
  -- 9.31 相対版: `P ⊓ Y^{(H)}` は `Y^{(H)}` の Sylow `p`.
  have hPL : ¬ p ∣ (P ⊓ strongClosureIn H Y).relIndex (strongClosureIn H Y) :=
    not_dvd_relIndex_inf_of_isSubnormal_in hLH hLsub hP hPidx
  have hPLp : IsPGroup p ↥(P ⊓ strongClosureIn H Y) :=
    hP.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  -- `Y` を `P ⊓ Y^{(H)}` の中へ共役で送る.
  obtain ⟨h, hhL, hhY⟩ :=
    exists_mem_conjAct_smul_le_of_isPGroup hYL inf_le_right hY hPLp hPL
  refine ⟨h, hLH hhL, hhY.trans inf_le_left, ?_⟩
  have hHfix : ConjAct.toConjAct h • H = H := conjAct_smul_self_of_mem (hLH hhL)
  have hLfix : ConjAct.toConjAct h • strongClosureIn H Y = strongClosureIn H Y :=
    conjAct_smul_self_of_mem hhL
  calc strongClosureIn H (ConjAct.toConjAct h • Y)
      = strongClosureIn (ConjAct.toConjAct h • H) (ConjAct.toConjAct h • Y) := by rw [hHfix]
    _ = ConjAct.toConjAct h • strongClosureIn H Y := strongClosureIn_conjAct_smul _ _ _
    _ = strongClosureIn H Y := hLfix

section /- 9D: Bartels Step 4 の道具 — 集合 `𝒦(H)` と共役作用 -/

/-- **`𝒦(H)`** (Isaacs p. 291 の証明中の記法): `H` に含まれる `X` の共役 `Y` たちの
`Y^{(G)}` 全体からなる集合。Step 4 は `G` の `𝒦(M)` への共役作用の stabilizer を見る。 -/
def kappaSet (X H : Subgroup G) : Set (Subgroup G) :=
  {W | ∃ Y : Subgroup G, Y ≤ H ∧ (∃ c : ConjAct G, c • X = Y) ∧ strongClosure Y = W}

theorem mem_kappaSet_self (X : Subgroup G) {H : Subgroup G} (hXH : X ≤ H) :
    strongClosure X ∈ kappaSet X H :=
  ⟨X, hXH, ⟨1, one_smul _ _⟩, rfl⟩

/-- `𝒦` は `H` について単調。 -/
theorem kappaSet_mono {X H K : Subgroup G} (hHK : H ≤ K) : kappaSet X H ⊆ kappaSet X K := by
  rintro W ⟨Y, hYH, hYc, rfl⟩
  exact ⟨Y, hYH.trans hHK, hYc, rfl⟩

/-- **`𝒦` の共役同変性**: `W ∈ 𝒦(H)` なら `W^g ∈ 𝒦(H^g)`。

書籍 p.291 の「`(Y^{(G)})^h = (Y^h)^{(G)}` ゆえ `H` は `𝒦(H)` に共役で作用する」。 -/
theorem mem_kappaSet_conjAct_smul {c : ConjAct G} {X H W : Subgroup G}
    (hW : W ∈ kappaSet X H) : c • W ∈ kappaSet X (c • H) := by
  obtain ⟨Y, hYH, ⟨d, rfl⟩, rfl⟩ := hW
  refine ⟨c • (d • X), Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hYH, ⟨c * d, ?_⟩, ?_⟩
  · rw [mul_smul]
  · exact strongClosure_conjAct_smul c _


/-- 共役は `p`-群性を保つ。 -/
theorem isPGroup_conjAct_smul {p : ℕ} {X : Subgroup G} (hX : IsPGroup p ↥X) (c : ConjAct G) :
    IsPGroup p ↥(c • X) :=
  hX.of_injective (Subgroup.equivSMul c X).symm.toMonoidHom
    (Subgroup.equivSMul c X).symm.injective

/-- **`H` は `𝒦(H)` に共役で作用する** (`h ∈ H` の場合)。 -/
theorem mem_kappaSet_smul_of_mem {X H W : Subgroup G} {h : G} (hh : h ∈ H)
    (hW : W ∈ kappaSet X H) : ConjAct.toConjAct h • W ∈ kappaSet X H := by
  have := mem_kappaSet_conjAct_smul (c := ConjAct.toConjAct h) hW
  rwa [conjAct_smul_self_of_mem hh] at this

/-- **Step 4 の下準備** (書籍 p. 291 「By Step 3, we also have `𝒦(M) = 𝒦(P)`」):
`H < G` と `H` の Sylow `p`-部分群 `P` に対し `𝒦(H) = 𝒦(P)`.

`⊇` は単調性。`⊆` は Step 3 で `Y` を `P` の中へ共役で送り, Step 1 で
`(Y^h)^{(G)} = Y^{(G)}` を得る。 -/
theorem kappaSet_eq_of_sylow {G : Type u} [Group G] [Finite G] (hIH : BartelsIH G)
    {p : ℕ} [Fact p.Prime] {X H P : Subgroup G} (hH : H ≠ ⊤) (hPH : P ≤ H)
    (hXp : IsPGroup p ↥X) (hP : IsPGroup p ↥P) (hPidx : ¬ p ∣ P.relIndex H)
    (hne : ∀ c : ConjAct G, strongClosure (c • X) ≠ ⊤) :
    kappaSet X H = kappaSet X P := by
  refine Set.Subset.antisymm ?_ (kappaSet_mono hPH)
  rintro W ⟨Y, hYH, ⟨c, rfl⟩, rfl⟩
  obtain ⟨h, hhH, hhP, hheq⟩ :=
    bartels_step_three hIH hYH hH (isPGroup_conjAct_smul hXp c) hP hPidx
  have hne' : strongClosure (ConjAct.toConjAct h • (c • X)) ≠ ⊤ := by
    have := hne (ConjAct.toConjAct h * c)
    rwa [mul_smul] at this
  refine ⟨ConjAct.toConjAct h • (c • X), hhP, ⟨ConjAct.toConjAct h * c, (mul_smul _ _ _)⟩, ?_⟩
  exact bartels_step_one hIH (hhP.trans hPH) hYH hheq hne' (hne c)


end

end OddOrder.Isaacs.Ch09
