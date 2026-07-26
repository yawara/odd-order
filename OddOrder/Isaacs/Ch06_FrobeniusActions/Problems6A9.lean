/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.ProblemsTIHypothesis

/-!
# Isaacs Problem 6A.9 の準備 — TI 仮説の下での `X` の構造 (書籍 p. 186)

`A` が `G` で Lemma 6.5 の TI 仮説をみたし `X = notConjugateSet A`, `t ∈ A` を involution とする
(書籍の Note: 6A.9 は **`|A|` が偶数の場合の Frobenius の定理**の証明を与える)。

本ファイルでは 6A.9 の各パートで繰り返し使う構造的な補題を用意する。

* `centralizer_le_of_TI` — 6A.11 の系: `1 ≠ a ∈ A` なら `C_G(a) ≤ N_G(⟨a⟩) ≤ A`。
* `inv_mem_notConjugateSet` / `zpow_mem_notConjugateSet` — `X` は逆元・冪で閉じる。
* `eq_one_of_mem_notConjugateSet_of_mem` — `X ⊓ A = {1}`。
* `conj_mem_iff_of_TI` — `1 ≠ a ∈ A` について `g a g⁻¹ ∈ A ⟺ g ∈ A`。
* **`mem_notConjugateSet_of_conj_eq_inv`** — 鍵: `t` に反転される `A` の外の元は `X` に入る。
  (`x = g a g⁻¹` と共役なら `u := g⁻¹ t g` が `a` を反転するので `u ∈ N_G(⟨a⟩) ≤ A`,
  つまり `t ∈ A ⊓ A^g` で TI から `g ∈ A`, これは `x ∈ A` を与えて矛盾。)
-/

namespace OddOrder.Isaacs.Ch06

open Pointwise

section /- 6A.9 の準備: `X` の構造 (p. 186) -/

variable {G : Type*} [Group G]

/-- `u` が `a` を反転すれば `u` は `⟨a⟩` を正規化する。 -/
theorem mem_normalizer_zpowers_of_conj_eq_inv {a u : G} (h : u * a * u⁻¹ = a⁻¹) :
    u ∈ Subgroup.normalizer (Subgroup.zpowers a) := by
  have hinv : u⁻¹ * a * u = a⁻¹ := by
    have h1 : u⁻¹ * a⁻¹ * u = a := by rw [← h]; group
    have h2 := congrArg (fun z : G => z⁻¹) h1
    simpa [mul_assoc] using h2
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨-n, ?_⟩
    show a ^ (-n) = u * a ^ n * u⁻¹
    rw [← conj_zpow (i := n) (a := u) (b := a), h, zpow_neg, ← inv_zpow]
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨-n, ?_⟩
    show a ^ (-n) = y
    have hcj := conj_zpow (i := n) (a := u⁻¹) (b := a)
    rw [inv_inv] at hcj
    have h2 : u⁻¹ * (a ^ n) * u = y := by rw [hn]; group
    rw [← h2, ← hcj, hinv, zpow_neg, ← inv_zpow]

/-- 6A.11 の系: TI 仮説の下で `1 ≠ a ∈ A` の中心化群は `A` に含まれる。 -/
theorem centralizer_le_of_TI {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {a : G} (ha : a ∈ A) (hane : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≤ A := by
  have hz : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    exact hane (by simpa [h] using Subgroup.mem_zpowers a)
  refine le_trans ?_ (normalizer_le_of_TI hATI hz (Subgroup.zpowers_le.mpr ha))
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hcomm : Commute c a := hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hfix : c * a ^ n * c⁻¹ = a ^ n := by rw [(hcomm.zpow_right n).eq]; group
    rw [hfix]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) n
  · intro hy
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    show a ^ n = y
    have h3 : c⁻¹ * (a ^ n) * c = y := by rw [hn]; group
    rw [← h3, ((hcomm.zpow_right n).inv_left).eq]
    group

/-- `1 ≠ a ∈ A` について `g a g⁻¹ ∈ A ⟺ g ∈ A` (TI 仮説)。 -/
theorem conj_mem_iff_of_TI {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {a : G} (ha : a ∈ A) (hane : a ≠ 1) (g : G) :
    g * a * g⁻¹ ∈ A ↔ g ∈ A := by
  refine ⟨fun h => ?_, fun h => A.mul_mem (A.mul_mem h ha) (A.inv_mem h)⟩
  by_contra hgA
  have hmem : g * a * g⁻¹ ∈ A ⊓ (MulAut.conj g • A) := by
    refine Subgroup.mem_inf.mpr ⟨h, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm (g * a * g⁻¹) ∈ A
    rw [MulAut.conj_symm_apply]
    simpa [mul_assoc] using ha
  rw [hATI g hgA, Subgroup.mem_bot] at hmem
  exact hane (by
    have := congrArg (fun y : G => g⁻¹ * y * g) hmem
    simpa [mul_assoc] using this)

/-- `X` は逆元で閉じる。 -/
theorem inv_mem_notConjugateSet {A : Subgroup G} {x : G} (hx : x ∈ notConjugateSet A) :
    x⁻¹ ∈ notConjugateSet A := by
  intro a ha hane hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  refine hx a⁻¹ (A.inv_mem ha) (by simpa using hane) (isConj_iff.mpr ⟨c, ?_⟩)
  have h2 := congrArg (fun z : G => z⁻¹) hc
  simpa [mul_assoc] using h2

/-- `X ⊓ A = {1}`。 -/
theorem eq_one_of_mem_notConjugateSet_of_mem {A : Subgroup G} {x : G}
    (hx : x ∈ notConjugateSet A) (hxA : x ∈ A) : x = 1 := by
  by_contra hne
  exact hx x hxA hne (isConj_iff.mpr ⟨1, by group⟩)

/-- TI 仮説の下で `X` は冪で閉じる。 -/
theorem zpow_mem_notConjugateSet {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {x : G} (hx : x ∈ notConjugateSet A) (k : ℤ) : x ^ k ∈ notConjugateSet A := by
  intro a ha hane hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hxne : x ≠ 1 := by
    intro h
    rw [h, one_zpow] at hg
    exact hane (by
      have h2 := congrArg (fun y : G => g⁻¹ * y * g) hg
      simpa [mul_assoc] using h2)
  -- `b := g⁻¹ x g` は `a = b^k` と可換なので `b ∈ C_G(a) ≤ A`
  have hab : a = (g⁻¹ * x * g) ^ k := by
    have h1 : (g⁻¹ * x * g) ^ k = g⁻¹ * x ^ k * g := by
      simpa using conj_zpow (i := k) (a := g⁻¹) (b := x)
    rw [h1, ← hg]
    group
  have hbc : g⁻¹ * x * g ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, hab]
    exact ((Commute.refl (g⁻¹ * x * g)).zpow_right k).eq
  have hbA : g⁻¹ * x * g ∈ A := centralizer_le_of_TI hATI ha hane hbc
  have hbne : g⁻¹ * x * g ≠ 1 := by
    intro h
    exact hxne (by
      have h2 := congrArg (fun y : G => g * y * g⁻¹) h
      simpa [mul_assoc] using h2)
  exact hx (g⁻¹ * x * g) hbA hbne (isConj_iff.mpr ⟨g, by group⟩)

/-- **6A.9 の鍵**: `t ∈ A` が involution のとき, `t` に反転される `A` の外の元は `X` に入る。 -/
theorem mem_notConjugateSet_of_conj_eq_inv {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {x : G} (hxA : x ∉ A) (hinv : t * x * t = x⁻¹) : x ∈ notConjugateSet A := by
  intro a ha hane hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have htinv : t⁻¹ = t := by
    rw [← mul_one t⁻¹, ← ht2, ← mul_assoc, inv_mul_cancel, one_mul]
  -- `u := g⁻¹ t g` は `a` を反転する
  have hu : (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ = a⁻¹ := by
    have hstep : (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹
        = g⁻¹ * (t * (g * a * g⁻¹) * t⁻¹) * g := by group
    rw [hstep, htinv, hg, hinv, ← hg]
    group
  -- `u ∈ N_G(⟨a⟩) ≤ A`
  have hz : Subgroup.zpowers a ≠ ⊥ := by
    intro h
    exact hane (by simpa [h] using Subgroup.mem_zpowers a)
  have huA : g⁻¹ * t * g ∈ A :=
    normalizer_le_of_TI hATI hz (Subgroup.zpowers_le.mpr ha)
      (mem_normalizer_zpowers_of_conj_eq_inv hu)
  -- `t ∈ A ⊓ A^g` ⟹ `g ∈ A` ⟹ `x ∈ A` で矛盾
  have hune : g⁻¹ * t * g ≠ 1 := by
    intro hone
    refine htne ?_
    have h2 := congrArg (fun y : G => g * y * g⁻¹) hone
    simpa [mul_assoc] using h2
  have hgA : g ∈ A := (conj_mem_iff_of_TI hATI huA hune g).mp (by simpa [mul_assoc] using htA)
  exact hxA (by rw [← hg]; exact A.mul_mem (A.mul_mem hgA ha) (A.inv_mem hgA))

/-! ### 6A.9(a): `t` に反転される `A` の外の元の個数 -/

/-- **Isaacs Problem 6A.9(a)** (p. 186) ⭐: `t ∈ A` が involution なら, `t` に反転される
`G ∖ A` の元は少なくとも `|G : A| − 1` 個ある。

`f g := (g t g⁻¹) · t` は `t` に反転される元を与え (`s := g t g⁻¹` は involution で
`(f g) t = s`), `f g ∉ A ⟺ g ∉ A`。`f` の fiber は `C_G(t)` の左剰余類なので大きさは
`|C_G(t)| ≤ |A|`, したがって像の大きさは `(|G| − |A|)/|A| = |G:A| − 1` 以上。 -/
theorem card_inverted_notMem_ge [Finite G] {A : Subgroup G}
    (hATI : ∀ x : G, x ∉ A → A ⊓ (MulAut.conj x • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1) :
    A.index - 1 ≤ {x : G | t * x * t = x⁻¹ ∧ x ∉ A}.ncard := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set f : G → G := fun g => (g * t * g⁻¹) * t with hfdef
  set sA : Finset G := Finset.univ.filter (fun g : G => ¬ g ∈ A) with hsAdef
  -- `f g` は `t` に反転され, `g ∉ A` なら `A` の外
  have hmemtarget : ∀ g : G, g ∉ A → f g ∈ {x : G | t * x * t = x⁻¹ ∧ x ∉ A} := by
    intro g hg
    simp only [hfdef]
    refine ⟨?_, ?_⟩
    · have hL : t * ((g * t * g⁻¹) * t) * t = t * g * t * g⁻¹ * (t * t) := by group
      have hR : ((g * t * g⁻¹) * t)⁻¹ = t⁻¹ * g * t⁻¹ * g⁻¹ := by group
      rw [hL, hR, ht2, mul_one, htinv]
    · intro hmem
      refine hg ((conj_mem_iff_of_TI hATI htA htne g).mp ?_)
      have hmul := A.mul_mem hmem (A.inv_mem htA)
      have heq2 : ((g * t * g⁻¹) * t) * t⁻¹ = g * t * g⁻¹ := by group
      rwa [heq2] at hmul
  -- `f` の fiber は `C_G(t)` の左剰余類 ⟹ 大きさ `≤ |A|`
  have hAcard : (Finset.univ.filter (fun g : G => g ∈ A)).card = Nat.card ↥A := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hfiber : ∀ y ∈ sA.image f, (sA.filter (fun g => f g = y)).card ≤ Nat.card ↥A := by
    intro y hy
    obtain ⟨g₀, hg₀mem, hg₀⟩ := Finset.mem_image.mp hy
    rw [← hAcard]
    refine Finset.card_le_card_of_injOn (fun g => g₀⁻¹ * g) ?_ ?_
    · intro g hg
      obtain ⟨hgsA, hgy⟩ := Finset.mem_filter.mp hg
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have heq : g * t * g⁻¹ = g₀ * t * g₀⁻¹ := by
        have h1 : (g * t * g⁻¹) * t = (g₀ * t * g₀⁻¹) * t := by
          have e1 : (g * t * g⁻¹) * t = f g := by simp only [hfdef]
          have e2 : (g₀ * t * g₀⁻¹) * t = f g₀ := by simp only [hfdef]
          rw [e1, e2, hgy, hg₀]
        exact mul_right_cancel h1
      have hcomm : (g₀⁻¹ * g) * t = t * (g₀⁻¹ * g) := by
        have h2 : g₀⁻¹ * (g * t * g⁻¹) * g₀ = t := by rw [heq]; group
        calc (g₀⁻¹ * g) * t = g₀⁻¹ * (g * t * g⁻¹) * g₀ * (g₀⁻¹ * g) := by group
          _ = t * (g₀⁻¹ * g) := by rw [h2]
      exact centralizer_le_of_TI hATI htA htne
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    · intro a _ b _ hab
      exact mul_left_cancel hab
  have hcard := Finset.card_le_mul_card_image (f := f) sA (Nat.card ↥A) hfiber
  -- `|sA| = |G| − |A|`
  have hsplit : Nat.card ↥A + sA.card = Fintype.card G := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset G)) (fun g : G => g ∈ A)
    rw [hAcard, Finset.card_univ] at h
    exact h
  have hGA : Nat.card ↥A * A.index = Nat.card G := Subgroup.card_mul_index A
  have hGcard : Fintype.card G = Nat.card G := (Nat.card_eq_fintype_card (α := G)).symm
  have hApos : 0 < Nat.card ↥A := Nat.card_pos
  -- 像の大きさが `|G:A| − 1` 以上
  have himgge : A.index - 1 ≤ (sA.image f).card := by
    have h1 : Nat.card ↥A * (A.index - 1) ≤ Nat.card ↥A * (sA.image f).card := by
      have h2 : Nat.card ↥A * (A.index - 1) = Nat.card ↥A * A.index - Nat.card ↥A := by
        rw [Nat.mul_sub, mul_one]
      rw [h2, hGA, ← hGcard]
      omega
    exact Nat.le_of_mul_le_mul_left h1 hApos
  -- 像は目標集合に含まれる
  refine le_trans himgge ?_
  have hsub : (↑(sA.image f) : Set G) ⊆ {x : G | t * x * t = x⁻¹ ∧ x ∉ A} := by
    intro z hz
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp (by exact_mod_cast hz)
    exact hmemtarget g (Finset.mem_filter.mp hg).2
  calc (sA.image f).card = (↑(sA.image f) : Set G).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ### 6A.9(b)-(e) -/

/-- **Isaacs Problem 6A.9(b)** (p. 186) ⭐: `t` は `X` の元をすべて反転する。

(a) の `|Inv(t) ∖ A| ≥ |G:A| − 1` と `Inv(t) ∖ A ⊆ X ∖ {1}` (`|X ∖ {1}| = |G:A| − 1`) の
濃度合わせで `Inv(t) ∖ A = X ∖ {1}`。 -/
theorem conj_eq_inv_of_mem_notConjugateSet [Finite G] {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {x : G} (hx : x ∈ notConjugateSet A) : t * x * t = x⁻¹ := by
  classical
  rcases eq_or_ne x 1 with rfl | hxne
  · simpa using ht2
  have hxA : x ∉ A := fun h => hxne (eq_one_of_mem_notConjugateSet_of_mem hx h)
  have hincl : {y : G | t * y * t = y⁻¹ ∧ y ∉ A} ⊆ notConjugateSet A \ {1} := by
    rintro y ⟨hyinv, hyA⟩
    exact ⟨mem_notConjugateSet_of_conj_eq_inv hATI htA ht2 htne hyA hyinv,
      fun h => hyA (by rw [Set.mem_singleton_iff] at h; rw [h]; exact A.one_mem)⟩
  have hXcard : (notConjugateSet A).ncard = A.index := card_notConjugateSet_eq_index A hATI
  have hdiff : (notConjugateSet A \ {1}).ncard = A.index - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (one_mem_notConjugateSet A), hXcard]
  have heq : {y : G | t * y * t = y⁻¹ ∧ y ∉ A} = notConjugateSet A \ {1} :=
    Set.eq_of_subset_of_ncard_le hincl
      (by rw [hdiff]; exact card_inverted_notMem_ge hATI htA ht2 htne) (Set.toFinite _)
  have hmem : x ∈ {y : G | t * y * t = y⁻¹ ∧ y ∉ A} := by
    rw [heq]; exact ⟨hx, hxne⟩
  exact hmem.1

/-- **Isaacs Problem 6A.9(c)** (p. 186): `A < G` のとき `t` は `A` の唯一の involution
(したがって `t ∈ Z(A)`)。

`s ≠ t` がもう一つの involution なら `s` も `X` を反転するので `t s` は `X` の元を中心化する。
`1 ≠ x ∈ X` を取ると `x ∈ C_G(ts) ≤ A` となり `X ⊓ A = {1}` に矛盾。 -/
theorem eq_of_isInvolution_mem [Finite G] {A : Subgroup G} (hAtop : A ≠ ⊤)
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t s : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    (hsA : s ∈ A) (hs2 : s * s = 1) (hsne : s ≠ 1) : s = t := by
  classical
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  -- `1 ≠ x ∈ X` を取る
  have hXcard : (notConjugateSet A).ncard = A.index := card_notConjugateSet_eq_index A hATI
  have h2 : 2 ≤ A.index := by
    have h0 : A.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : A.index ≠ 1 := fun h => hAtop (Subgroup.index_eq_one.mp h)
    omega
  obtain ⟨x, hxX, hxne⟩ : ∃ x ∈ notConjugateSet A, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hsub : notConjugateSet A ⊆ {1} := fun y hy => hcon y hy
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hXcard, Set.ncard_singleton] at hle
    omega
  by_contra hne
  -- `t * s ≠ 1` で `x` と可換
  have htsne : t * s ≠ 1 := by
    intro h
    exact hne (by rw [← htinv, ← inv_eq_of_mul_eq_one_right h])
  have htx := conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne hxX
  have hsx := conj_eq_inv_of_mem_notConjugateSet hATI hsA hs2 hsne hxX
  have h1 : (t * s) * x * (t * s)⁻¹ = x := by
      rw [mul_inv_rev, hsinv, htinv]
      calc t * s * x * (s * t) = t * (s * x * s) * t := by group
        _ = t * x⁻¹ * t := by rw [hsx]
        _ = (t * x * t)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, htinv]; group
        _ = x := by rw [htx, inv_inv]
  have hcomm : x * (t * s) = (t * s) * x := by
    conv_lhs => rw [← h1]
    group
  have hxmem : x ∈ Subgroup.centralizer ({t * s} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hxA : x ∈ A :=
    centralizer_le_of_TI hATI (A.mul_mem htA hsA) htsne hxmem
  exact hxne (eq_one_of_mem_notConjugateSet_of_mem hxX hxA)

/-- **Isaacs Problem 6A.9(d)** (p. 186): `X` の元の位数はすべて奇数。

位数が偶数なら `x` の冪に involution `u` があり, `u ∈ X` (X は冪で閉じる) かつ
`t u t = u⁻¹ = u` から `u ∈ C_G(t) ≤ A`, ゆえに `u ∈ X ⊓ A = {1}` で矛盾。 -/
theorem odd_orderOf_of_mem_notConjugateSet [Finite G] {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {x : G} (hx : x ∈ notConjugateSet A) : Odd (orderOf x) := by
  classical
  rcases Nat.even_or_odd (orderOf x) with heven | hodd
  · exfalso
    obtain ⟨m, hm⟩ := heven
    have hpos : 0 < orderOf x := orderOf_pos x
    have hmpos : 0 < m := by omega
    set u : G := x ^ (m : ℕ) with hudef
    have hu2 : u * u = 1 := by
      rw [hudef, ← pow_add, ← hm]
      exact pow_orderOf_eq_one x
    have hune : u ≠ 1 := by
      intro h
      have hdvd : orderOf x ∣ m := orderOf_dvd_iff_pow_eq_one.mpr h
      have := Nat.le_of_dvd hmpos hdvd
      omega
    have huX : u ∈ notConjugateSet A := by
      have := zpow_mem_notConjugateSet hATI hx (m : ℤ)
      simpa [hudef] using this
    -- `t` は `u` を反転するが `u⁻¹ = u` なので `t` と可換 ⟹ `u ∈ C_G(t) ≤ A`
    have hinv := conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne huX
    have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hcomm : t * u = u * t := by
      have h1 : t * u * t = u := by rw [hinv, huinv]
      have h2 : t * u * (t * t) = u * t := by rw [← mul_assoc, h1]
      rwa [ht2, mul_one] at h2
    have huA : u ∈ A := by
      refine centralizer_le_of_TI hATI htA htne ?_
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm
    exact hune (eq_one_of_mem_notConjugateSet_of_mem huX huA)
  · exact hodd

/-- **Isaacs Problem 6A.9(e)** (p. 186): `x, y ∈ X` で `x y⁻¹ ∈ A` なら `x = y`
(すなわち `X` は `A` の右剰余類とちょうど 1 点ずつ交わる)。 -/
theorem eq_of_mul_inv_mem [Finite G] {A : Subgroup G}
    (hATI : ∀ z : G, z ∉ A → A ⊓ (MulAut.conj z • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {x y : G} (hx : x ∈ notConjugateSet A) (hy : y ∈ notConjugateSet A)
    (hmem : x * y⁻¹ ∈ A) : x = y := by
  classical
  have htx := conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne hx
  have hty := conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne hy
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `b := x⁻¹ y = t (x y⁻¹) t ∈ A`
  have hb : x⁻¹ * y ∈ A := by
    have hstep : t * (x * y⁻¹) * t = x⁻¹ * y := by
      calc t * (x * y⁻¹) * t = (t * x * t) * (t * y⁻¹ * t) := by
            rw [show (t * x * t) * (t * y⁻¹ * t) = t * x * (t * t) * y⁻¹ * t by group, ht2]
            group
        _ = x⁻¹ * y := by
            have hyy : t * y⁻¹ * t = (t * y * t)⁻¹ := by
              rw [mul_inv_rev, mul_inv_rev, htinv]; group
            rw [htx, hyy, hty, inv_inv]
    rw [← hstep]
    exact A.mul_mem (A.mul_mem htA hmem) htA
  by_cases hbne : x⁻¹ * y = 1
  · exact inv_mul_eq_one.mp hbne
  · exfalso
    have hconj : x * (x⁻¹ * y) * x⁻¹ ∈ A := by
      have : x * (x⁻¹ * y) * x⁻¹ = (x * y⁻¹)⁻¹ := by group
      rw [this]
      exact A.inv_mem hmem
    have hxA : x ∈ A := (conj_mem_iff_of_TI hATI hb hbne x).mp hconj
    have hx1 : x = 1 := eq_one_of_mem_notConjugateSet_of_mem hx hxA
    -- `x = 1` なら `y⁻¹ ∈ A ⊓ X = {1}` で `y = 1`, これは `b ≠ 1` に矛盾
    have hyinvX : y⁻¹ ∈ notConjugateSet A := inv_mem_notConjugateSet hy
    have hyinvA : y⁻¹ ∈ A := by rw [hx1, one_mul] at hmem; exact hmem
    have hyi : y⁻¹ = 1 := eq_one_of_mem_notConjugateSet_of_mem hyinvX hyinvA
    have hy1 : y = 1 := by simpa using congrArg (fun z : G => z⁻¹) hyi
    exact hbne (by rw [hx1, hy1]; group)

/-- 6A.9(c) の系: `A` の元で `t` に反転されるのは `1` と `t` だけ
(`a t` は `A` の involution になるので (c) の一意性から `a t ∈ {1, t}`)。 -/
theorem eq_one_or_eq_of_mem_of_conj_eq_inv [Finite G] {A : Subgroup G} (hAtop : A ≠ ⊤)
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {a : G} (haA : a ∈ A) (hinv : t * a * t = a⁻¹) : a = 1 ∨ a = t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsq : (a * t) * (a * t) = 1 := by
    calc (a * t) * (a * t) = a * (t * a * t) := by group
      _ = a * a⁻¹ := by rw [hinv]
      _ = 1 := by group
  by_cases hone : a * t = 1
  · right
    have ha : a = t⁻¹ := by
      have hc := congrArg (fun z : G => z * t⁻¹) hone
      simpa [mul_assoc] using hc
    rwa [htinv] at ha
  · left
    have heq := eq_of_isInvolution_mem hAtop hATI htA ht2 htne (A.mul_mem haA htA) hsq hone
    exact mul_right_cancel (b := t) (by rw [heq, one_mul])

/-- `t` に反転される元全体は `X ∪ {t}` (6A.9(b) + 上の系)。 -/
theorem setOf_conj_eq_inv_eq [Finite G] {A : Subgroup G} (hAtop : A ≠ ⊤)
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1) :
    {x : G | t * x * t = x⁻¹} = notConjugateSet A ∪ {t} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro hinv
    by_cases hxA : x ∈ A
    · rcases eq_one_or_eq_of_mem_of_conj_eq_inv hAtop hATI htA ht2 htne hxA hinv with h | h
      · exact Or.inl (h ▸ one_mem_notConjugateSet A)
      · exact Or.inr h
    · exact Or.inl (mem_notConjugateSet_of_conj_eq_inv hATI htA ht2 htne hxA hinv)
  · rintro (hx | hxt)
    · exact conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne hx
    · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
      rw [hxt, htinv, ht2, one_mul]

/-! ### 6A.9(f): `X` は部分群 -/

/-- TI 仮説は `A` の共役にも遺伝する。 -/
theorem TI_conj {A : Subgroup G}
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥) (g : G) :
    ∀ y : G, y ∉ (MulAut.conj g • A : Subgroup G) →
      (MulAut.conj g • A : Subgroup G) ⊓ (MulAut.conj y • (MulAut.conj g • A)) = ⊥ := by
  intro y hy
  have hy' : g⁻¹ * y * g ∉ A := by
    intro h
    refine hy ?_
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm y ∈ A
    rwa [MulAut.conj_symm_apply]
  have hstep : (MulAut.conj g • A : Subgroup G) ⊓ (MulAut.conj y • (MulAut.conj g • A))
      = MulAut.conj g • (A ⊓ MulAut.conj (g⁻¹ * y * g) • A) := by
    rw [Subgroup.smul_inf, ← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
    congr 2
    group
  rw [hstep, hATI _ hy', Subgroup.smul_bot]

/-- `A` の共役に対する `X` は同じ集合。 -/
theorem notConjugateSet_conj (A : Subgroup G) (g : G) :
    notConjugateSet (MulAut.conj g • A) = notConjugateSet A := by
  have key : ∀ (B : Subgroup G) (h : G) (x : G), x ∈ notConjugateSet B →
      x ∈ notConjugateSet (MulAut.conj h • B) := by
    intro B h x hx a ha hane hconj
    have haB : h⁻¹ * a * h ∈ B := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at ha
      change (MulAut.conj h).symm a ∈ B at ha
      rwa [MulAut.conj_symm_apply] at ha
    refine hx (h⁻¹ * a * h) haB ?_ ?_
    · intro hone
      refine hane ?_
      have h2 := congrArg (fun z : G => h * z * h⁻¹) hone
      simpa [mul_assoc] using h2
    · obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      exact isConj_iff.mpr ⟨c * h, by rw [← hc]; group⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => key A g x hx⟩
  have := key (MulAut.conj g • A) g⁻¹ x hx
  rwa [conj_inv_smul_smul] at this

/-- **Isaacs Problem 6A.9(f)** (p. 186) ⭐: `X` は積で閉じる (したがって部分群)。

`x, y ∈ X` に対し `s := x t`, `r := t y` はともに involution で `x y = s r`。
(d) より `X` の元は奇数位数なので `s ∉ X`, ゆえに `s` はある共役 `A^g` の非単位元。
`A^g` も TI 仮説をみたし `notConjugateSet A^g = X` なので (b)(c) の系
`setOf_conj_eq_inv_eq` が `Inv(s) = X ∪ {s}` を与える。`s (sr) s = (sr)⁻¹` より
`x y ∈ Inv(s)`, そして `x y = s` なら `y = t ∈ X ⊓ A = {1}` で `t = 1` となり矛盾。 -/
theorem mul_mem_notConjugateSet [Finite G] {A : Subgroup G} (hAtop : A ≠ ⊤)
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1)
    {x y : G} (hx : x ∈ notConjugateSet A) (hy : y ∈ notConjugateSet A) :
    x * y ∈ notConjugateSet A := by
  classical
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htx := conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne hx
  have hty := conj_eq_inv_of_mem_notConjugateSet hATI htA ht2 htne hy
  -- `s := x t` は involution
  have hs2 : (x * t) * (x * t) = 1 := by
    calc (x * t) * (x * t) = x * (t * x * t) := by group
      _ = x * x⁻¹ := by rw [htx]
      _ = 1 := by group
  have hsne : x * t ≠ 1 := by
    intro hone
    have hxt : x = t := by
      have hxi : x = t⁻¹ := by
        have hc := congrArg (fun z : G => z * t⁻¹) hone
        simpa [mul_assoc] using hc
      rwa [htinv] at hxi
    exact htne (by rw [← hxt]; exact eq_one_of_mem_notConjugateSet_of_mem hx (hxt ▸ htA))
  -- `r := t y` も involution, そして `x y = (x t)(t y)`
  have hr2 : (t * y) * (t * y) = 1 := by
    calc (t * y) * (t * y) = (t * y * t) * y := by group
      _ = y⁻¹ * y := by rw [hty]
      _ = 1 := by group
  have hxy : x * y = (x * t) * (t * y) := by rw [← mul_assoc, mul_assoc x t t, ht2, mul_one]
  -- `s ∉ X` (X の元は奇数位数)
  have hsX : x * t ∉ notConjugateSet A := by
    intro hmem
    have hodd := odd_orderOf_of_mem_notConjugateSet hATI htA ht2 htne hmem
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [orderOf_eq_prime (by rw [pow_two]; exact hs2) hsne] at hodd
    exact (by decide : ¬ Odd 2) hodd
  -- `s` はある共役 `A^g` の非単位元
  simp only [notConjugateSet, Set.mem_setOf_eq, not_forall, not_not] at hsX
  obtain ⟨a, haA, hane, hconj⟩ := hsX
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hsAg : x * t ∈ (MulAut.conj g • A : Subgroup G) := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj g).symm (x * t) ∈ A
    rw [MulAut.conj_symm_apply, ← hg]
    simpa [mul_assoc] using haA
  have hAgtop : (MulAut.conj g • A : Subgroup G) ≠ ⊤ := by
    intro h
    refine hAtop (le_antisymm le_top fun z _ => ?_)
    have hz : (MulAut.conj g) z ∈ (MulAut.conj g • A : Subgroup G) := by
      rw [h]; exact Subgroup.mem_top _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hz
    change (MulAut.conj g).symm ((MulAut.conj g) z) ∈ A at hz
    rwa [MulEquiv.symm_apply_apply] at hz
  -- `Inv(s) = X ∪ {s}`
  have hInvS := setOf_conj_eq_inv_eq hAgtop (TI_conj hATI g) hsAg hs2 hsne
  rw [notConjugateSet_conj] at hInvS
  have hxyInv : (x * t) * (x * y) * (x * t) = (x * y)⁻¹ := by
    rw [hxy]
    calc (x * t) * ((x * t) * (t * y)) * (x * t)
        = ((x * t) * (x * t)) * (t * y) * (x * t) := by group
      _ = (t * y) * (x * t) := by rw [hs2, one_mul]
      _ = ((x * t) * (t * y))⁻¹ := by
          rw [mul_inv_rev]
          have e1 : (t * y)⁻¹ = t * y := inv_eq_of_mul_eq_one_right hr2
          have e2 : (x * t)⁻¹ = x * t := inv_eq_of_mul_eq_one_right hs2
          rw [e1, e2]
  have hmem2 : x * y ∈ notConjugateSet A ∪ {x * t} := by
    rw [← hInvS]; exact hxyInv
  rcases hmem2 with h | h
  · exact h
  · -- `x y = x t` なら `y = t`, これは `X ⊓ A = {1}` と `t ≠ 1` に矛盾
    exfalso
    rw [Set.mem_singleton_iff] at h
    have hyt : y = t := by
      have h2 := congrArg (fun z : G => x⁻¹ * z) h
      simpa [← mul_assoc] using h2
    exact htne (hyt ▸ eq_one_of_mem_notConjugateSet_of_mem hy (hyt ▸ htA))

/-- **Isaacs Problem 6A.9(f)** (p. 186) ⭐ 仕上げ: `X` を部分群として取り出す。

書籍の Note のとおり, これは **`A` が偶数位数のときの Frobenius の定理** —
すなわち `X` が Frobenius 核になること — の証明を与える。 -/
def frobeniusKernelOfInvolution [Finite G] {A : Subgroup G} (hAtop : A ≠ ⊤)
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1) : Subgroup G where
  carrier := notConjugateSet A
  mul_mem' hx hy := mul_mem_notConjugateSet hAtop hATI htA ht2 htne hx hy
  one_mem' := one_mem_notConjugateSet A
  inv_mem' hx := inv_mem_notConjugateSet hx

@[simp] theorem coe_frobeniusKernelOfInvolution [Finite G] {A : Subgroup G} (hAtop : A ≠ ⊤)
    (hATI : ∀ y : G, y ∉ A → A ⊓ (MulAut.conj y • A) = ⊥)
    {t : G} (htA : t ∈ A) (ht2 : t * t = 1) (htne : t ≠ 1) :
    ((frobeniusKernelOfInvolution hAtop hATI htA ht2 htne : Subgroup G) : Set G)
      = notConjugateSet A := rfl

end

end OddOrder.Isaacs.Ch06
