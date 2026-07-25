/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch04_Commutators.ProblemsWreath

/-!
# Isaacs Chapter 4 — Problem 4A.12 (交換子でない導来部分群の元)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.12 (書籍 p. 125)。

`𝒯(H)` = 「可換かつ 2 元生成」という性質について極大な `H` の部分群全体, `G = A ≀ H`
(`A` 可換), `B` = base 群とすると

* **(a)** `x, y ∈ G` で `⁅x,y⁆ ∈ B` なら, ある `T ∈ 𝒯(H)` で `⁅x,y⁆ ∈ ⁅B, T⁆`
  (`exists_maximal_commutator_mem`)
* **(b)** `1/|A| > ∑_{T ∈ 𝒯(H)} (1/|A|)^{|H:T|}` なら `G' ⊓ B` は**交換子でない元**を含む
  (`exists_mem_not_isCommutator`; 両辺に `|A|^{|H|}` を掛けた自然数の形で述べる)
* **(c)** `H` が「可換かつ 2 元生成」でなければ, `|A| > |𝒯(H)|` のとき (b) の不等式が成り立つ
  (`sum_lt_of_card_lt`)

(a) の核は `⁅x,y⁆ ∈ B ⟺ x.right` と `y.right` が可換, そのとき
`⁅x,y⁆ = inl (Δ_{x.right} y.left)⁻¹ · inl (Δ_{y.right} x.left)` となること。
(b) は (a) と Problem 4A.11 の位数 `|⁅B,T⁆| = |A|^{|H|−|H:T|}` の数え上げ。
-/

namespace OddOrder.Isaacs.Ch04

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch03.WreathProduct

open scoped commutatorElement

section /- Problem 4A.12 (p. 125) -/

variable {D Q : Type*} [CommGroup D] [Group Q]

/-! ### 可換 2 元生成部分群 -/

/-- **「可換かつ 2 元生成」**な部分群 (Isaacs Problem 4A.12 の `𝒯(H)` はこの性質の極大元). -/
def IsAbelianTwoGen (T : Subgroup Q) : Prop :=
  (∀ a ∈ T, ∀ b ∈ T, a * b = b * a) ∧ ∃ u v : Q, T = Subgroup.closure {u, v}

/-- 可換な 2 元が生成する部分群は「可換かつ 2 元生成」(中心化群の二段論法). -/
theorem isAbelianTwoGen_closure_pair {u v : Q} (huv : u * v = v * u) :
    IsAbelianTwoGen (Subgroup.closure ({u, v} : Set Q)) := by
  refine ⟨?_, u, v, rfl⟩
  have h1 : Subgroup.closure ({u, v} : Set Q) ≤ Subgroup.centralizer ({u, v} : Set Q) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact huv.symm
    · exact huv
    · rfl
  have h2 : Subgroup.closure ({u, v} : Set Q)
      ≤ Subgroup.centralizer (Subgroup.closure ({u, v} : Set Q) : Set Q) := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro g hg
    exact ((Subgroup.mem_centralizer_iff.mp (h1 hg)) z hz).symm
  intro a ha b hb
  exact ((Subgroup.mem_centralizer_iff.mp (h2 ha)) b hb).symm

/-! ### Problem 4A.12(a) -/

/-- `x.right` と `y.right` が可換なとき, 交換子は base 側の 2 つの `Δ` の積.

`⁅inl f · inr h, y⁆ = inl f · ⁅inr h, y⁆ · (inl f)⁻¹ · ⁅inl f, y⁆` を展開する.
`⁅inr h, inr k⁆ = inr ⁅h,k⁆ = 1` が効いて base 成分だけが残る. -/
theorem commutatorElement_eq_of_right_commute (x y : D ≀[Q] Q)
    (hc : x.right * y.right = y.right * x.right) :
    ⁅x, y⁆ = (inl (shiftSubHom x.right y.left) : D ≀[Q] Q)⁻¹
      * inl (shiftSubHom y.right x.left) := by
  have hinr : ⁅(inr x.right : D ≀[Q] Q), y⁆ = (inl (shiftSubHom x.right y.left))⁻¹ := by
    have hy : ⁅y, (inr x.right : D ≀[Q] Q)⁆ = inl (shiftSubHom x.right y.left) := by
      conv_lhs => rw [← inl_left_mul_inr_right y]
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hzero : ⁅(inr y.right : D ≀[Q] Q), (inr x.right : D ≀[Q] Q)⁆ = 1 := by
        rw [← map_commutatorElement, commutatorElement_eq_one_iff_commute.mpr hc.symm, map_one]
      rw [hzero, commutatorElement_inl_inr_eq_shiftSubHom]
      group
    rw [← commutatorElement_inv y, hy]
  have hfold : ∀ a b d : Q → D,
      (inl a : D ≀[Q] Q) * (inl b)⁻¹ * (inl a)⁻¹ * inl d = (inl b : D ≀[Q] Q)⁻¹ * inl d := by
    intro a b d
    have e1 : (inl a : D ≀[Q] Q) * (inl b)⁻¹ * (inl a)⁻¹ * inl d
        = inl (a * b⁻¹ * a⁻¹ * d) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have e2 : (inl b : D ≀[Q] Q)⁻¹ * inl d = inl (b⁻¹ * d) := by
      rw [map_mul, map_inv]
    rw [e1, e2, mul_comm a b⁻¹, mul_assoc b⁻¹ a a⁻¹, mul_inv_cancel, mul_one]
  conv_lhs => rw [← inl_left_mul_inr_right x]
  rw [commutatorElement_mul_left_eq_conj_mul, hinr, commutatorElement_inl_eq_shiftSubHom, hfold]

/-- **Isaacs Problem 4A.12(a)**: `⁅x,y⁆ ∈ B` なら, 「可換 2 元生成」の極大部分群 `T` で
`⁅x,y⁆ ∈ ⁅B, T⁆` となるものが存在する.

`⁅x,y⁆ ∈ B` は `x.right`, `y.right` が可換であることに他ならないので,
`⟨x.right, y.right⟩` は可換 2 元生成. これを含む極大なものが `T`. -/
theorem exists_maximal_commutator_mem [Finite Q] (x y : D ≀[Q] Q)
    (hxy : ⁅x, y⁆ ∈ (inl : (Q → D) →* D ≀[Q] Q).range) :
    ∃ T : Subgroup Q, Maximal IsAbelianTwoGen T ∧
      ⁅x, y⁆ ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range, T.map (inr : Q →* D ≀[Q] Q)⁆ := by
  have hc : x.right * y.right = y.right * x.right := by
    have h1 : (⁅x, y⁆ : D ≀[Q] Q).right = 1 := by
      rw [range_inl_eq_ker_rightHom] at hxy
      exact hxy
    have h2 : (⁅x, y⁆ : D ≀[Q] Q).right = ⁅x.right, y.right⁆ :=
      map_commutatorElement (rightHom : (D ≀[Q] Q) →* Q) x y
    rw [h2] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1
  obtain ⟨T, hle, hmax⟩ :=
    Finite.exists_le_maximal (α := Subgroup Q) (p := IsAbelianTwoGen)
      (isAbelianTwoGen_closure_pair hc)
  refine ⟨T, hmax, ?_⟩
  have hxT : x.right ∈ T := hle (Subgroup.subset_closure (by simp))
  have hyT : y.right ∈ T := hle (Subgroup.subset_closure (by simp))
  have hmem : ∀ (q : Q), q ∈ T → ∀ f : Q → D,
      (inl (shiftSubHom q f) : D ≀[Q] Q)
        ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range, T.map (inr : Q →* D ≀[Q] Q)⁆ := by
    intro q hq f
    rw [← commutatorElement_inl_inr_eq_shiftSubHom]
    exact Subgroup.commutator_mem_commutator ⟨f, rfl⟩ ⟨q, hq, rfl⟩
  rw [commutatorElement_eq_of_right_commute x y hc]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hmem _ hxT _)) (hmem _ hyT _)

/-! ### Problem 4A.12(b) -/

open scoped Classical in
theorem card_filter_mem {G : Type*} [Group G] [Fintype G] (X : Subgroup G) :
    (Finset.univ.filter (fun z => z ∈ X)).card = Nat.card X := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

open scoped Classical in
/-- **Isaacs Problem 4A.12(b)**: `∑_{T ∈ 𝒯(H)} |A|^{|H|−|H:T|} < |A|^{|H|−1}` なら
`⁅B, U⁆` (`⊆ G' ⊓ B`) は**交換子として書けない元**を含む.

書籍は `1/|A| > ∑_{T} (1/|A|)^{|H:T|}` と述べるが, 両辺に `|A|^{|H|}` を掛けた自然数の形。
(a) より `B` に入る交換子はすべて `⋃_{T ∈ 𝒯(H)} ⁅B,T⁆` に属し, その元の個数は
`∑_T |A|^{|H|−|H:T|}` (Problem 4A.11) で抑えられる。一方 `|⁅B, U⁆| = |A|^{|H|−1}` なので
鳩の巣原理。 -/
theorem exists_mem_not_isCommutator [Finite Q] [Finite D] {𝒯 : Finset (Subgroup Q)}
    (h𝒯 : ∀ T : Subgroup Q, Maximal (IsAbelianTwoGen (Q := Q)) T → T ∈ 𝒯)
    (hlt : ∑ T ∈ 𝒯, Nat.card D ^ (Nat.card Q - T.index)
      < Nat.card D ^ (Nat.card Q - 1)) :
    ∃ z ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range, (inr : Q →* D ≀[Q] Q).range⁆,
      ¬ ∃ x y : D ≀[Q] Q, ⁅x, y⁆ = z := by
  letI : Fintype (D ≀[Q] Q) := Fintype.ofFinite _
  by_contra hcontra
  have hcon : ∀ z ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range, (inr : Q →* D ≀[Q] Q).range⁆,
      ∃ x y : D ≀[Q] Q, ⁅x, y⁆ = z := by
    intro z hz
    by_contra h
    exact hcontra ⟨z, hz, h⟩
  have hSU : (Finset.univ.filter
        (fun z : D ≀[Q] Q => z ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range,
          (inr : Q →* D ≀[Q] Q).range⁆))
      ⊆ 𝒯.biUnion (fun T => Finset.univ.filter
        (fun z : D ≀[Q] Q => z ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range,
          T.map (inr : Q →* D ≀[Q] Q)⁆)) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨x, y, hxy⟩ := hcon z hz.2
    have hzB : ⁅x, y⁆ ∈ (inl : (Q → D) →* D ≀[Q] Q).range := by
      rw [hxy]
      exact Subgroup.commutator_le_left _ _ hz.2
    obtain ⟨T, hTmax, hmem⟩ := exists_maximal_commutator_mem x y hzB
    refine Finset.mem_biUnion.mpr ⟨T, h𝒯 T hTmax, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    rwa [hxy] at hmem
  have hrange : ((inr : Q →* D ≀[Q] Q).range) = (⊤ : Subgroup Q).map inr :=
    MonoidHom.range_eq_map _
  have hcardS : (Finset.univ.filter
      (fun z : D ≀[Q] Q => z ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range,
        (inr : Q →* D ≀[Q] Q).range⁆)).card = Nat.card D ^ (Nat.card Q - 1) := by
    rw [card_filter_mem, hrange, card_commutator_range_inl_map_inr, Subgroup.index_top]
  have hcardU : (𝒯.biUnion (fun T => Finset.univ.filter
      (fun z : D ≀[Q] Q => z ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range,
        T.map (inr : Q →* D ≀[Q] Q)⁆))).card
      ≤ ∑ T ∈ 𝒯, Nat.card D ^ (Nat.card Q - T.index) := by
    refine le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun T _ => ?_)
    exact le_of_eq (by rw [card_filter_mem, card_commutator_range_inl_map_inr])
  have h1 := Finset.card_le_card hSU
  rw [hcardS] at h1
  omega

/-! ### Problem 4A.12(c) — 不等式が成り立つ十分条件 -/

/-- 「可換 2 元生成」について極大な部分群は, `⊤` がその性質を持たなければ真部分群. -/
theorem index_ne_one_of_maximal {T : Subgroup Q} (hT : Maximal IsAbelianTwoGen T)
    (htop : ¬ IsAbelianTwoGen (⊤ : Subgroup Q)) : T ≠ ⊤ := by
  rintro rfl
  exact htop hT.prop

/-- **Isaacs Problem 4A.12(c)** (一般部分): `H` が「可換 2 元生成」でなければ,
`|A| > |𝒯(H)|` のとき (b) の不等式が成り立つ.

各 `T ∈ 𝒯(H)` は真部分群ゆえ `|H:T| ≥ 2`, したがって
`∑_T |A|^{|H|−|H:T|} ≤ |𝒯(H)|·|A|^{|H|−2} < |A|·|A|^{|H|−2} = |A|^{|H|−1}`. -/
theorem sum_lt_of_card_lt [Finite Q] [Finite D] {𝒯 : Finset (Subgroup Q)}
    (h𝒯 : ∀ T ∈ 𝒯, Maximal (IsAbelianTwoGen (Q := Q)) T)
    (htop : ¬ IsAbelianTwoGen (⊤ : Subgroup Q)) (hm : 𝒯.card < Nat.card D) :
    ∑ T ∈ 𝒯, Nat.card D ^ (Nat.card Q - T.index) < Nat.card D ^ (Nat.card Q - 1) := by
  have hQ2 : 2 ≤ Nat.card Q := by
    by_contra hcon
    have hone : Nat.card Q = 1 := by
      have := Nat.card_pos (α := Q)
      omega
    haveI hsub : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hone).1
    refine htop ⟨fun a _ b _ => Subsingleton.elim _ _, 1, 1, le_antisymm ?_ le_top⟩
    intro x _
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _
  have hstep : ∀ T ∈ 𝒯, Nat.card D ^ (Nat.card Q - T.index)
      ≤ Nat.card D ^ (Nat.card Q - 2) := by
    intro T hT
    have hne : T ≠ ⊤ := index_ne_one_of_maximal (h𝒯 T hT) htop
    have h1 : T.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
    have h0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.pow_le_pow_right Nat.card_pos (by omega)
  calc ∑ T ∈ 𝒯, Nat.card D ^ (Nat.card Q - T.index)
      ≤ ∑ _T ∈ 𝒯, Nat.card D ^ (Nat.card Q - 2) := Finset.sum_le_sum hstep
    _ = 𝒯.card * Nat.card D ^ (Nat.card Q - 2) := by rw [Finset.sum_const, smul_eq_mul]
    _ < Nat.card D * Nat.card D ^ (Nat.card Q - 2) :=
        (Nat.mul_lt_mul_right (pow_pos Nat.card_pos _)).mpr hm
    _ = Nat.card D ^ (Nat.card Q - 1) := by
        rw [← pow_succ']
        congr 1
        omega

end

end OddOrder.Isaacs.Ch04
