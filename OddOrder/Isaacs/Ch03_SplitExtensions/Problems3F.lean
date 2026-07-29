/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.QuaternionRecognition
import OddOrder.Isaacs.Ch03_SplitExtensions.CyclicExtensions

/-!
# Isaacs §3F の演習 (書籍 pp. 110-111)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problems 3F (巡回拡大と一般化四元数群)。

書籍は Thm 3.36 (cyclic extension) の応用として一般化四元数群 `Q_n` (位数 `n`, `8 ∣ n`) を
構成する: `N` を位数 `n/2` の巡回群, `a ∈ N` を唯一の位数 2 の元, `σ : x ↦ x⁻¹` として
`m = 2` の巡回拡大を取る。得られる `Q` では `Q ∖ N` の元がすべて位数 4 になる。

mathlib の `QuaternionGroup M` (位数 `4M`) が同じ群なので, `Q_n = QuaternionGroup (n/4)`
として形式化する。

* **3F.1** `nonempty_mulEquiv_quaternionGroup_of_isCyclic_index_two` —
  逆に「指数 2 の巡回部分群 `C` があって `G ∖ C` の元がすべて位数 4」なら `G ≅ Q_n`。
* **3F.2** `isCyclicExtensionTower_top` — 有限可解群は `⊥` から Thm 3.36 (巡回拡大) を
  繰り返して構成できる。
* **3F.3** `quaternionTwo_zpowers_of_orderOf_eq_four` +
  `quaternionTwo_zpowers_pairwise_ne` (`Q_8` の位数 4 の巡回部分群は
  `⟨a 1⟩`, `⟨xa 0⟩`, `⟨xa 1⟩` のちょうど 3 個) と
  `quaternionTwo_exists_mulAut_map_zpowers` (`Aut(Q_8)` が推移的)。
-/

namespace OddOrder.Isaacs.Ch03

open OddOrder.GroupTheory

open scoped commutatorElement

section /- 3F: 巡回拡大の演習 -/

/-- **Isaacs Problem 3F.1** (書籍 p. 110): `|G| = n` が `8` で割り切れ, `G` が指数 2 の
巡回部分群 `C` をもち, `G ∖ C` の元がすべて位数 4 なら `G ≅ Q_n` (位数 `n` の一般化
四元数群 = mathlib の `QuaternionGroup (n/4)`)。

**証明**: `C = ⟨c⟩` とすると `orderOf c = n/2 = 2M` (`M = n/4`)。`a ∉ C` を取ると
任意の `x ∈ C` について `a * x ∉ C` なので `orderOf (a * x) = 4`, すなわち `(a * x)²` は
`C` の位数 2 の元。巡回群の位数 2 の元は一意 (`eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one`)
なので `(a * x)² = c ^ M` が `x` によらず成り立つ。`x = 1` から `a² = c ^ M`,
`x = c` から `(a c)² = a²` すなわち `c a c = a`, したがって `a c a⁻¹ = c⁻¹`。
あとは四元数群の認識定理 (`quaternionIsoOfInverting`) を当てるだけ。 -/
theorem nonempty_mulEquiv_quaternionGroup_of_isCyclic_index_two
    {G : Type*} [Group G] [Finite G] {C : Subgroup G} (hC : IsCyclic ↥C)
    (hidx : C.index = 2) (h8 : 8 ∣ Nat.card G)
    (h4 : ∀ g : G, g ∉ C → orderOf g = 4) :
    Nonempty (G ≃* QuaternionGroup (Nat.card G / 4)) := by
  classical
  obtain ⟨c, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top C).mp hC
  obtain ⟨k, hk⟩ := h8
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hkpos : 0 < k := by omega
  -- `orderOf c = n / 2 = 2 * M`
  have hcard : orderOf c * 2 = Nat.card G := by
    rw [← Nat.card_zpowers c, ← hidx]
    exact Subgroup.card_mul_index _
  have hMdef : Nat.card G / 4 = 2 * k := by omega
  have horder : orderOf c = 2 * (Nat.card G / 4) := by omega
  have hhalf : orderOf c / 2 = Nat.card G / 4 := by omega
  have hMpos : 0 < Nat.card G / 4 := by omega
  -- `C ≠ ⊤` なので `a ∉ C` が取れる
  obtain ⟨a, ha⟩ : ∃ a : G, a ∉ Subgroup.zpowers c := by
    by_contra h
    push Not at h
    rw [(Subgroup.eq_top_iff' _).mpr h, Subgroup.index_top] at hidx
    omega
  -- `x ∈ C` なら `(a * x)²` は `C` の唯一の位数 2 の元
  have key : ∀ x ∈ Subgroup.zpowers c, (a * x) ^ 2 = c ^ (orderOf c / 2) := by
    intro x hx
    have hax : a * x ∉ Subgroup.zpowers c := fun hmem => ha (by
      simpa using Subgroup.mul_mem _ hmem (Subgroup.inv_mem _ hx))
    have hax4 : orderOf (a * x) = 4 := h4 _ hax
    have hsq_mem : (a * x) ^ 2 ∈ Subgroup.zpowers c := Subgroup.sq_mem_of_index_two hidx _
    have hsq_sq : ((a * x) ^ 2) ^ 2 = 1 := by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hax4])
    have hsq_ne : (a * x) ^ 2 ≠ 1 := by
      intro h1
      have : orderOf (a * x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
      rw [hax4] at this
      omega
    exact (eq_pow_half_orderOf_of_mem_zpowers_sq_eq_one c _ hsq_mem hsq_sq hsq_ne).1
  have hasq : a ^ 2 = c ^ (Nat.card G / 4) := by
    have := key 1 (Subgroup.one_mem _)
    rwa [mul_one, hhalf] at this
  have hacsq : (a * c) ^ 2 = a ^ 2 := by
    rw [hasq, ← hhalf]
    exact key c (Subgroup.mem_zpowers c)
  -- `(a c)² = a²` から `c a c = a`, したがって `a c a⁻¹ = c⁻¹`
  have hcac : c * a * c = a := by
    refine mul_left_cancel (a := a) ?_
    have h := hacsq
    rw [pow_two, pow_two] at h
    calc a * (c * a * c) = a * c * (a * c) := by group
      _ = a * a := h
  have hconj : a * c * a⁻¹ = c⁻¹ := by
    calc a * c * a⁻¹ = a * c * (c * a * c)⁻¹ := by rw [hcac]
      _ = c⁻¹ := by group
  exact ⟨quaternionIsoOfInverting c a (Nat.card G / 4) hMpos horder hidx ha hasq hconj⟩

/-! ### Problem 3F.2 — 可解群は自明群から巡回拡大を繰り返して構成できる -/

/-- **Thm 3.36 (巡回拡大) で構成できる部分群のクラス**: `⊥` から出発して
「`H` を正規部分群として含み, 商が巡回」という拡大 (= Thm 3.36 の出力) を有限回
繰り返して得られる部分群。

商の巡回性は quotient 型を避けて **`K = H ⊔ ⟨g⟩` (`g ∈ K`)** で表す — Thm 3.36 の出力が
まさにこの形 (`cyclic_quotient_generator`: `G/N` 巡回 ⟺ ある `g` で `⟨g⟩ ⊔ N = G`)。
正規性も `∀ x ∈ K, ∀ y ∈ H, x y x⁻¹ ∈ H` と要素で書く (`H` は `K` の部分群として
正規であればよく, `G` で正規である必要はない)。 -/
inductive IsCyclicExtensionTower {G : Type*} [Group G] : Subgroup G → Prop
  | bot : IsCyclicExtensionTower ⊥
  | step {H K : Subgroup G} (hconj : ∀ x ∈ K, ∀ y ∈ H, x * y * x⁻¹ ∈ H)
      {g : G} (hg : g ∈ K) (hsup : K = H ⊔ Subgroup.zpowers g)
      (ih : IsCyclicExtensionTower H) : IsCyclicExtensionTower K

/-- `commutator G ≤ H` なら `H` は共役で閉じる (`x y x⁻¹ = ⁅x, y⁆ * y`)。 -/
theorem conj_mem_of_commutator_le {G : Type*} [Group G] {H : Subgroup G}
    (h : _root_.commutator G ≤ H) (x : G) {y : G} (hy : y ∈ H) : x * y * x⁻¹ ∈ H := by
  have hc : ⁅x, y⁆ ∈ H := h (by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  have hrw : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
  rw [hrw]
  exact Subgroup.mul_mem _ hc hy

/-- 3F.2 の帰納本体 (`|K|` に関する強帰納)。 -/
private theorem isCyclicExtensionTower_aux {G : Type*} [Group G] [Finite G] [IsSolvable G] :
    ∀ (n : ℕ) (K : Subgroup G), Nat.card ↥K ≤ n → IsCyclicExtensionTower K := by
  intro n
  induction n with
  | zero =>
    intro K hK
    have hcard : 0 < Nat.card ↥K := Nat.card_pos
    omega
  | succ m ih =>
    intro K hK
    rcases eq_or_ne K ⊥ with rfl | hKne
    · exact .bot
    haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    -- `↥K` の極大部分群 `M ⊇ commutator ↥K`
    obtain ⟨M, hMcoatom, hMle⟩ :=
      (eq_top_or_exists_le_coatom (α := Subgroup ↥K) (_root_.commutator ↥K)).resolve_left
        (IsSolvable.commutator_lt_top_of_nontrivial (G := ↥K)).ne
    obtain ⟨ĝ, hĝ⟩ : ∃ x : ↥K, x ∉ M := by
      by_contra h
      push Not at h
      exact hMcoatom.1 ((Subgroup.eq_top_iff' _).mpr h)
    have hMsup : M ⊔ Subgroup.zpowers ĝ = ⊤ :=
      hMcoatom.2 _ (lt_of_le_of_ne le_sup_left fun hcon =>
        hĝ (hcon ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers ĝ)))
    -- `N := M` を `G` の部分群として見る
    set N : Subgroup G := M.map K.subtype with hN
    have hcardN : Nat.card ↥N = Nat.card ↥M :=
      Nat.card_congr (M.equivMapOfInjective K.subtype Subtype.val_injective).toEquiv.symm
    -- `|N| = |M| < |K| ≤ m + 1`
    have hMlt : Nat.card ↥M < Nat.card ↥K := by
      have hidx : M.index ≠ 1 := fun h => hMcoatom.1 (Subgroup.index_eq_one.mp h)
      have hidx0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hmul : Nat.card ↥M * M.index = Nat.card ↥K := Subgroup.card_mul_index M
      have hMpos : 0 < Nat.card ↥M := Nat.card_pos
      have h2 : 2 ≤ M.index := by omega
      calc Nat.card ↥M < Nat.card ↥M * 2 := by omega
        _ ≤ Nat.card ↥M * M.index := Nat.mul_le_mul_left _ h2
        _ = Nat.card ↥K := hmul
    refine .step (H := N) (K := K) ?_ (g := (ĝ : G)) ĝ.2 ?_ (ih N (by omega))
    · rintro x hx - ⟨y, hyM, rfl⟩
      exact ⟨⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹,
        conj_mem_of_commutator_le hMle _ hyM, rfl⟩
    · have := congrArg (Subgroup.map K.subtype) hMsup
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at this
      exact this.symm

/-- **Isaacs Problem 3F.2** (書籍 p. 110): 有限可解群は自明群から出発して
**Thm 3.36 (巡回拡大)** を繰り返し適用することで構成できる。

`|K|` に関する強帰納。`K ≠ ⊥` なら `↥K` は非自明可解ゆえ `commutator ↥K < ⊤`
(`IsSolvable.commutator_lt_top_of_nontrivial`) で, それを含む極大部分群 `M` が取れる。
`M` は交換子群を含むので `↥K` で正規, 極大性から `ĝ ∉ M` について `M ⊔ ⟨ĝ⟩ = ⊤`。
`M` を `G` の部分群 `N` に戻せば `|N| < |K|` で帰納法の仮説が使える。 -/
theorem isCyclicExtensionTower_top (G : Type*) [Group G] [Finite G] [IsSolvable G] :
    IsCyclicExtensionTower (⊤ : Subgroup G) :=
  isCyclicExtensionTower_aux _ ⊤ le_rfl

/-! ### Problem 3F.3 — `Q_8` の位数 4 の巡回部分群はちょうど 3 個 -/

open QuaternionGroup in
/-- `Q_8 = QuaternionGroup 2` では, 単位元 `a 0` と唯一の involution `a 2` 以外の
6 個の元がすべて位数 4。 -/
theorem quaternionTwo_orderOf_eq_four_iff (x : QuaternionGroup 2) :
    orderOf x = 4 ↔ x ≠ a 0 ∧ x ≠ a 2 := by
  match x with
  | a i =>
    rw [orderOf_a i]
    revert i
    decide
  | xa i => exact ⟨fun _ => ⟨nofun, nofun⟩, fun _ => orderOf_xa i⟩

/-- `x` と `y` が互いの冪なら生成する巡回部分群は等しい。 -/
theorem zpowers_eq_zpowers_of_mem {G : Type*} [Group G] {x y : G}
    (hxy : x ∈ Subgroup.zpowers y) (hyx : y ∈ Subgroup.zpowers x) :
    Subgroup.zpowers x = Subgroup.zpowers y :=
  le_antisymm (Subgroup.zpowers_le.mpr hxy) (Subgroup.zpowers_le.mpr hyx)

open QuaternionGroup in
/-- **Isaacs Problem 3F.3 (前半)**: `Q_8` の位数 4 の巡回部分群は
`⟨a 1⟩`, `⟨xa 0⟩`, `⟨xa 1⟩` の 3 個しかない。 -/
theorem quaternionTwo_zpowers_of_orderOf_eq_four {x : QuaternionGroup 2} (hx : orderOf x = 4) :
    Subgroup.zpowers x = Subgroup.zpowers (a 1) ∨
      Subgroup.zpowers x = Subgroup.zpowers (xa 0) ∨
      Subgroup.zpowers x = Subgroup.zpowers (xa 1) := by
  have hpow : ∀ u v : QuaternionGroup 2, u ^ (3 : ℕ) = v → v ^ (3 : ℕ) = u →
      Subgroup.zpowers v = Subgroup.zpowers u := fun u v huv hvu =>
    zpowers_eq_zpowers_of_mem (huv ▸ pow_mem (Subgroup.mem_zpowers u) 3)
      (hvu ▸ pow_mem (Subgroup.mem_zpowers v) 3)
  rw [quaternionTwo_orderOf_eq_four_iff] at hx
  rcases x with i | i
  · have hi : i = 1 ∨ i = 3 := by revert hx; revert i; decide
    rcases hi with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl (hpow (a 1) (a 3) (by decide) (by decide))
  · have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl (hpow (xa 0) (xa 2) (by decide) (by decide)))
    · exact Or.inr (Or.inr (hpow (xa 1) (xa 3) (by decide) (by decide)))

open QuaternionGroup in
/-- `Q_8` の位数 4 の 3 つの巡回部分群は相異なる (`⟨a 1⟩` の元は `a _` の形,
`xa 1 ∉ ⟨xa 0⟩`)。 -/
theorem quaternionTwo_zpowers_pairwise_ne :
    Subgroup.zpowers (a 1 : QuaternionGroup 2) ≠ Subgroup.zpowers (xa 0) ∧
      Subgroup.zpowers (a 1 : QuaternionGroup 2) ≠ Subgroup.zpowers (xa 1) ∧
      Subgroup.zpowers (xa 0 : QuaternionGroup 2) ≠ Subgroup.zpowers (xa 1) := by
  have hmem : ∀ u v : QuaternionGroup 2, orderOf u = 4 →
      (v ∈ (Finset.range 4).image (fun k => u ^ k) → False) →
      Subgroup.zpowers u ≠ Subgroup.zpowers v := by
    intro u v hu hv hcon
    exact hv (by
      rw [← hu]
      exact (mem_zpowers_iff_mem_range_orderOf).mp (hcon ▸ Subgroup.mem_zpowers v))
  have h1 : orderOf (a 1 : QuaternionGroup 2) = 4 :=
    (quaternionTwo_orderOf_eq_four_iff _).mpr ⟨by decide, by decide⟩
  have h2 : orderOf (xa 0 : QuaternionGroup 2) = 4 := orderOf_xa 0
  exact ⟨hmem _ _ h1 (by decide), hmem _ _ h1 (by decide), hmem _ _ h2 (by decide)⟩

open QuaternionGroup in
/-- `Q_8` の自己同型 `a 1 ↦ xa 0` (四元数 `i ↦ j`, `j ↦ i`)。

`a k ↦ (xa 0)^k`, `xa k ↦ (a 1) * (xa 0)^k` (= `xa 0 ↦ a 1` の伸長)。 -/
def quaternionSwapIJ : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => (xa 0 : QuaternionGroup 2) ^ i.val
  | .xa i => (a 1 : QuaternionGroup 2) * (xa 0 : QuaternionGroup 2) ^ i.val

open QuaternionGroup in
/-- `Q_8` の自己同型 `a 1 ↦ xa 1` (四元数 `i ↦ k`)。 -/
def quaternionSwapIK : QuaternionGroup 2 → QuaternionGroup 2
  | .a i => (xa 1 : QuaternionGroup 2) ^ i.val
  | .xa i => (a 1 : QuaternionGroup 2) * (xa 1 : QuaternionGroup 2) ^ i.val

/-- `quaternionSwapIJ` を自己同型に仕立てたもの。`map_mul` も全単射性も `decide`
(`QuaternionGroup 2` は 8 元で `DecidableEq` 付き)。 -/
noncomputable def quaternionSwapIJAut : MulAut (QuaternionGroup 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' quaternionSwapIJ (by decide)) (by decide)

/-- `quaternionSwapIK` を自己同型に仕立てたもの。 -/
noncomputable def quaternionSwapIKAut : MulAut (QuaternionGroup 2) :=
  MulEquiv.ofBijective (MonoidHom.mk' quaternionSwapIK (by decide)) (by decide)

open QuaternionGroup in
/-- 位数 4 の巡回部分群はどれも `⟨a 1⟩` の `Aut(Q_8)`-像。 -/
theorem quaternionTwo_exists_mulAut_map_zpowers_a_one {S : Subgroup (QuaternionGroup 2)}
    (hS : S = Subgroup.zpowers (a 1) ∨ S = Subgroup.zpowers (xa 0) ∨
      S = Subgroup.zpowers (xa 1)) :
    ∃ φ : MulAut (QuaternionGroup 2),
      (Subgroup.zpowers (a 1 : QuaternionGroup 2)).map φ.toMonoidHom = S := by
  rcases hS with rfl | rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨quaternionSwapIJAut, by rw [MonoidHom.map_zpowers]; rfl⟩
  · exact ⟨quaternionSwapIKAut, by rw [MonoidHom.map_zpowers]; rfl⟩

/-- **Isaacs Problem 3F.3 (後半)**: `Q_8` の位数 4 の巡回部分群は `Aut(Q_8)` によって
推移的に置換される。

書籍の Hint は Thm 3.35 (巡回拡大の一意性) 経由だが, `Q_8` は 8 元なので
**明示の自己同型 2 本 (`i ↦ j`, `i ↦ k`) を `decide` で検証**する方が短い。
一般の `x`, `y` に対しては両方を `⟨a 1⟩` に戻して合成する。 -/
theorem quaternionTwo_exists_mulAut_map_zpowers {x y : QuaternionGroup 2}
    (hx : orderOf x = 4) (hy : orderOf y = 4) :
    ∃ φ : MulAut (QuaternionGroup 2),
      (Subgroup.zpowers x).map φ.toMonoidHom = Subgroup.zpowers y := by
  obtain ⟨φ, hφ⟩ :=
    quaternionTwo_exists_mulAut_map_zpowers_a_one (quaternionTwo_zpowers_of_orderOf_eq_four hx)
  obtain ⟨ψ, hψ⟩ :=
    quaternionTwo_exists_mulAut_map_zpowers_a_one (quaternionTwo_zpowers_of_orderOf_eq_four hy)
  refine ⟨φ.symm.trans ψ, ?_⟩
  rw [← hφ, Subgroup.map_map, ← hψ]
  congr 1
  exact MonoidHom.ext fun z => by simp

end -- 3F

end OddOrder.Isaacs.Ch03
