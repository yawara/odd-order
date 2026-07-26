/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Problems6B7

/-!
# Isaacs Problem 6B.8 — Taussky-Todd (書籍 p. 196)

**主張**: `|P| ≥ 8` の `2`-群 `P` が `|P : P'| = 4` をみたすなら, `P` は二面体群・半二面体群・
一般四元数群のいずれか (O. Taussky-Todd の定理)。

**書籍 hint の筋** (`|P|` に関する帰納法):

1. `Z ≤ P' ⊓ Z(P)` で `|Z| = 2` なるものを取る (`P` は `2`-群で `P' ≠ 1` なので
   `P' ⊓ Z(P)` は非自明 — `IsPGroup.normal_inf_center_nontrivial`)。
2. `(P/Z)' = P'/Z` なので `|P/Z : (P/Z)'| = |P : P'| = 4` が保たれる。`|P/Z| = |P|/2`。
3. 帰納法で `P/Z` が二面体・半二面体・一般四元数, とくに**指数 2 の巡回部分群を持つ**。
   その引き戻し `A ≤ P` は指数 2 で `A/Z` 巡回, `Z ≤ Z(P)` なので **`A` は可換**。
4. `A` は巡回か `Z × (巡回)`。前者なら **6B.7** (`|P : Z(P)| > 4` を確認して) で終わり。
   後者で `|P| > 16` なら `Z < Z(P)` が出て矛盾。

現状はステップ 1 を実証明で提供し, 主定理は statement のみ。
-/

namespace OddOrder.Isaacs.Ch06

open OddOrder.GroupTheory

section /- 6B.8: Taussky-Todd (p. 196) -/

/-- **書籍 hint のステップ 1**: 非可換な有限 `2`-群 `P` には `P' ⊓ Z(P)` の中に位数 `2` の
元が取れる。

`P'` は非自明な正規部分群なので `IsPGroup.normal_inf_center_nontrivial` で `P' ⊓ Z(P)` が
非自明。その非単位元 `x` は位数 `2^k` (`k ≥ 1`) なので `x ^ (2^(k-1))` が位数 `2`。 -/
theorem exists_orderOf_eq_two_mem_commutator_center {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (hcomm : (commutator P) ≠ ⊥) :
    ∃ z : P, z ∈ commutator P ∧ z ∈ Subgroup.center P ∧ orderOf z = 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnt : Nontrivial ↥(commutator P) := (Subgroup.nontrivial_iff_ne_bot _).mpr hcomm
  have hK := Ch01.IsPGroup.normal_inf_center_nontrivial hP (N := commutator P) hnt
  obtain ⟨⟨x, hx⟩, hxne⟩ := exists_ne (1 : ↥(commutator P ⊓ Subgroup.center P))
  have hxP : x ≠ 1 := fun h => hxne (Subtype.ext h)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) x
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero] at hk
      exact absurd (orderOf_eq_one_iff.mp hk) hxP
    · exact h
  refine ⟨x ^ (2 ^ (k - 1)), Subgroup.pow_mem _ hx.1 _, Subgroup.pow_mem _ hx.2 _, ?_⟩
  rw [orderOf_pow, hk]
  have hdvd : (2 : ℕ) ^ (k - 1) ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
  rw [Nat.gcd_eq_right hdvd]
  have hsplit : (2 : ℕ) ^ k = 2 ^ (k - 1) * 2 := by
    rw [← pow_succ]; congr 1; omega
  rw [hsplit, Nat.mul_div_cancel_left _ (by positivity)]

/-- **書籍 hint のステップ 2**: `Z ⊴ P` が `Z ≤ P'` をみたすなら剰余群で指数が保たれる:
`|P/Z : (P/Z)'| = |P : P'|`。

`(P/Z)' = P'/Z` (全射準同型で交換子群は像に写る) と, 核を含む部分群の指数が像で保たれる
ことから。帰納法が回る鍵。 -/
theorem index_commutator_quotient {P : Type*} [Group P] {Z : Subgroup P} [Z.Normal]
    (hZ : Z ≤ commutator P) :
    (commutator (P ⧸ Z)).index = (commutator P).index := by
  have hsurj : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  have hmap : commutator (P ⧸ Z) = (commutator P).map (QuotientGroup.mk' Z) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hsurj]
  rw [hmap]
  exact Subgroup.index_map_eq _ hsurj (by rwa [QuotientGroup.ker_mk'])

/-- **書籍 hint のステップ 3**: `Z ≤ Z(A)` かつ `A/Z` が巡回なら `A` は可換。

`P/Z` の指数 `2` の巡回部分群の引き戻し `A` に適用する (`Z ≤ Z(P)` なので `Z ≤ Z(A)`)。 -/
theorem mul_comm_of_center_le_of_isCyclic_quotient {A : Type*} [Group A] {Z : Subgroup A}
    [Z.Normal] (hZ : Z ≤ Subgroup.center A) (hcyc : IsCyclic (A ⧸ Z)) (x y : A) :
    x * y = y * x := by
  haveI : IsCyclic ↥(QuotientGroup.mk' Z).range := by
    haveI := hcyc
    rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Z)]
    have e : (A ⧸ Z) ≃* ↥(⊤ : Subgroup (A ⧸ Z)) := Subgroup.topEquiv.symm
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  exact commutative_of_cyclic_center_quotient (QuotientGroup.mk' Z)
    (by rwa [QuotientGroup.ker_mk']) x y

/-- `|P : Z(P)| ≤ 2` なら `P` は可換 (`P/Z(P)` が巡回になるので)。

`|P : Z(P)| ∈ {1, 2}` を排除するのに使う。 -/
theorem mul_comm_of_index_center_le_two {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index ≤ 2) (x y : P) : x * y = y * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsCyclic (P ⧸ Subgroup.center P) := by
    have hcard : Nat.card (P ⧸ Subgroup.center P) ≤ 2 := h
    rcases Nat.lt_or_ge (Nat.card (P ⧸ Subgroup.center P)) 2 with hlt | hge
    · have hpos : 0 < Nat.card (P ⧸ Subgroup.center P) := Nat.card_pos
      haveI : Subsingleton (P ⧸ Subgroup.center P) :=
        (Nat.card_eq_one_iff_unique.mp (by omega)).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := 2) (by omega)
  exact mul_comm_of_center_le_of_isCyclic_quotient le_rfl hcyc x y

/-- `|P : Z(P)| = 4` なら `P/Z(P)` は `Z₂ × Z₂` — すなわち `∀ x, x² ∈ Z(P)`。

位数 `4` の元があると `P/Z(P)` が巡回になり `P` が可換, すると `|P : Z(P)| = 1` で矛盾。 -/
theorem sq_mem_center_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) (x : P) : x ^ 2 ∈ Subgroup.center P := by
  classical
  set Q := P ⧸ Subgroup.center P with hQ
  have hcard : Nat.card Q = 4 := h
  have hsq : ∀ g : Q, g ^ 2 = 1 := by
    intro g
    have hdvd : orderOf g ∣ 4 := hcard ▸ orderOf_dvd_natCard g
    have hne4 : orderOf g ≠ 4 := by
      intro h4
      haveI : IsCyclic Q := isCyclic_of_orderOf_eq_card g (by rw [h4, hcard])
      have hcomm := mul_comm_of_center_le_of_isCyclic_quotient
        (A := P) (Z := Subgroup.center P) le_rfl ‹IsCyclic Q›
      have htop : Subgroup.center P = ⊤ :=
        eq_top_iff.mpr fun g _ => Subgroup.mem_center_iff.mpr fun y => hcomm y g
      rw [htop, Subgroup.index_top] at h
      omega
    have hdvd2 : orderOf g ∣ 2 := by
      obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        ((show (2 : ℕ) ^ 2 = 4 by norm_num) ▸ hdvd)
      have hine : i ≠ 2 := by
        intro h2
        rw [h2] at hgi
        norm_num at hgi
        exact hne4 hgi
      rw [hgi]
      simpa using pow_dvd_pow 2 (show i ≤ 1 by omega)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd2
  have := hsq (QuotientGroup.mk x)
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
  exact this

/-- `|P : Z(P)| = 4` なら `P/Z(P)` は可換, すなわち `P' ≤ Z(P)`。

`P/Z(P)` の全元が `g² = 1` をみたす (`sq_mem_center_of_index_center_eq_four`) ので
`g⁻¹ = g`, したがって `gk = (gk)⁻¹ = k⁻¹g⁻¹ = kg`。 -/
theorem commutator_le_center_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) : commutator P ≤ Subgroup.center P := by
  have hsq : ∀ g : P ⧸ Subgroup.center P, g ^ 2 = 1 := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact sq_mem_center_of_index_center_eq_four h x
  have hinv : ∀ w : P ⧸ Subgroup.center P, w⁻¹ = w := fun w => by
    have hw := hsq w
    rw [pow_two] at hw
    exact inv_eq_of_mul_eq_one_right hw
  have habel : ∀ g k : P ⧸ Subgroup.center P, g * k = k * g := by
    intro g k
    calc g * k = (g * k)⁻¹ := (hinv _).symm
      _ = k⁻¹ * g⁻¹ := mul_inv_rev g k
      _ = k * g := by rw [hinv, hinv]
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [← commutatorElement_def]
  exact commutatorElement_eq_one_iff_mul_comm.mpr (habel _ _)

/-- `P' ≤ Z(P)` なら各交換子は中心的。 -/
theorem commutatorElement_mem_center_of_le_center {P : Type*} [Group P]
    (hc : commutator P ≤ Subgroup.center P) (u v : P) :
    u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center P := by
  have h1 := Subgroup.commutator_mem_commutator (G := P) (H₁ := ⊤) (H₂ := ⊤)
    (Subgroup.mem_top u) (Subgroup.mem_top v)
  rw [← commutator_def] at h1
  rw [← commutatorElement_def]
  exact hc h1

/-- 第 2 引数についての双線形性: `[x, yw] = [x,y][x,w]`。 -/
theorem commutator_mul_right_of_le_center {P : Type*} [Group P]
    (hc : commutator P ≤ Subgroup.center P) (x y w : P) :
    x * (y * w) * x⁻¹ * (y * w)⁻¹
      = (x * y * x⁻¹ * y⁻¹) * (x * w * x⁻¹ * w⁻¹) := by
  have hxw : ∀ g : P, g * (x * w * x⁻¹ * w⁻¹) = (x * w * x⁻¹ * w⁻¹) * g :=
    Subgroup.mem_center_iff.mp (commutatorElement_mem_center_of_le_center hc x w)
  calc x * (y * w) * x⁻¹ * (y * w)⁻¹
      = (x * y * x⁻¹ * y⁻¹) * (y * (x * w * x⁻¹ * w⁻¹) * y⁻¹) := by group
    _ = (x * y * x⁻¹ * y⁻¹) * ((x * w * x⁻¹ * w⁻¹) * y * y⁻¹) := by rw [hxw y]
    _ = (x * y * x⁻¹ * y⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group

/-- 交換子が中心的なときの**双線形性**: `[xy, w] = [x,w][y,w]`。 -/
theorem commutator_mul_left_of_le_center {P : Type*} [Group P]
    (hc : commutator P ≤ Subgroup.center P) (x y w : P) :
    (x * y) * w * (x * y)⁻¹ * w⁻¹
      = (x * w * x⁻¹ * w⁻¹) * (y * w * y⁻¹ * w⁻¹) := by
  have hcy : ∀ g : P, g * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * g :=
    Subgroup.mem_center_iff.mp (commutatorElement_mem_center_of_le_center hc y w)
  calc (x * y) * w * (x * y)⁻¹ * w⁻¹
      = x * (y * w * y⁻¹ * w⁻¹) * (w * x⁻¹ * w⁻¹) := by group
    _ = (y * w * y⁻¹ * w⁻¹) * x * (w * x⁻¹ * w⁻¹) := by rw [hcy x]
    _ = (y * w * y⁻¹ * w⁻¹) * (x * w * x⁻¹ * w⁻¹) := by group
    _ = (x * w * x⁻¹ * w⁻¹) * (y * w * y⁻¹ * w⁻¹) := (hcy _).symm

/-- 中心元は交換子に効かない (左): `[xz, y] = [x,y]`。 -/
theorem commutator_mul_center_left {P : Type*} [Group P]
    (hc : commutator P ≤ Subgroup.center P) {z : P} (hz : z ∈ Subgroup.center P) (x y : P) :
    (x * z) * y * (x * z)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzero : z * y * z⁻¹ * y⁻¹ = 1 := by
    have hcz := Subgroup.mem_center_iff.mp hz y
    rw [← hcz]
    group
  rw [commutator_mul_left_of_le_center hc x z y, hzero, mul_one]

/-- 中心元は交換子に効かない (右): `[x, yz] = [x,y]`。 -/
theorem commutator_mul_center_right {P : Type*} [Group P]
    (hc : commutator P ≤ Subgroup.center P) {z : P} (hz : z ∈ Subgroup.center P) (x y : P) :
    x * (y * z) * x⁻¹ * (y * z)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzero : x * z * x⁻¹ * z⁻¹ = 1 := by
    have hcz := Subgroup.mem_center_iff.mp hz x
    rw [hcz]
    group
  rw [commutator_mul_right_of_le_center hc x y z, hzero, mul_one]

/-- `|P : Z(P)| = 4` なら交換子はすべて involution: `[x,y]² = 1`。

双線形性で `[x², y] = [x,y]²`, 一方 `x² ∈ Z(P)` なので `[x², y] = 1`。 -/
theorem commutator_sq_eq_one_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) (x y : P) :
    (x * y * x⁻¹ * y⁻¹) ^ 2 = 1 := by
  have hc := commutator_le_center_of_index_center_eq_four h
  have hbil := commutator_mul_left_of_le_center hc x x y
  have hx2 : x ^ 2 ∈ Subgroup.center P := sq_mem_center_of_index_center_eq_four h x
  have hcx : y * (x * x) = (x * x) * y := by
    have hcc := Subgroup.mem_center_iff.mp hx2 y
    rwa [pow_two] at hcc
  have h1 : (x * x) * y * (x * x)⁻¹ * y⁻¹ = 1 := by
    calc (x * x) * y * (x * x)⁻¹ * y⁻¹ = ((x * x) * y) * (x * x)⁻¹ * y⁻¹ := by group
      _ = (y * (x * x)) * (x * x)⁻¹ * y⁻¹ := by rw [← hcx]
      _ = 1 := by group
  rw [h1] at hbil
  rw [pow_two]
  exact hbil.symm

/-- `|P : Z(P)| = 4` かつ `|P : P'| = 4` なら **`P' = Z(P)`** (濃度が一致し `P' ≤ Z(P)`)。 -/
theorem commutator_eq_center_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (hz : (Subgroup.center P).index = 4) (hd : (commutator P).index = 4) :
    commutator P = Subgroup.center P := by
  have hle := commutator_le_center_of_index_center_eq_four hz
  have h1 := Subgroup.card_mul_index (commutator P)
  have h2 := Subgroup.card_mul_index (Subgroup.center P)
  rw [hd] at h1
  rw [hz] at h2
  have heq : Nat.card ↥(Subgroup.center P) ≤ Nat.card ↥(commutator P) := by omega
  refine SetLike.ext' (Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _))
  exact heq

/-- `|P : Z(P)| = 4` のとき, 中心に無い元の中心化群は指数 `2`。

`Z(P) ≤ C_P(y) ≤ P` で `relIndex * index = 4`; `index = 1` なら `y ∈ Z(P)`,
`index = 4` なら `relIndex = 1` すなわち `C_P(y) ≤ Z(P)` でやはり `y ∈ Z(P)` に反する。 -/
theorem index_centralizer_eq_two_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) {y : P} (hy : y ∉ Subgroup.center P) :
    (Subgroup.centralizer ({y} : Set P)).index = 2 := by
  have hZC : Subgroup.center P ≤ Subgroup.centralizer ({y} : Set P) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hx y).symm
  have hmul := Subgroup.relIndex_mul_index hZC
  rw [h] at hmul
  have hyC : y ∈ Subgroup.centralizer ({y} : Set P) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hne1 : (Subgroup.centralizer ({y} : Set P)).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    refine hy (Subgroup.mem_center_iff.mpr fun g => ?_)
    have hg : g ∈ Subgroup.centralizer ({y} : Set P) := by rw [h1]; trivial
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have hne4 : (Subgroup.centralizer ({y} : Set P)).index ≠ 4 := by
    intro h4
    rw [h4] at hmul
    have hrel : (Subgroup.center P).relIndex (Subgroup.centralizer ({y} : Set P)) = 1 := by omega
    exact hy (Subgroup.relIndex_eq_one.mp hrel hyC)
  have hdvd : (Subgroup.centralizer ({y} : Set P)).index ∣ 4 := Dvd.intro_left _ hmul
  obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    ((show (2 : ℕ) ^ 2 = 4 by norm_num) ▸ hdvd)
  have hi0 : i ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hgi
    exact hne1 hgi
  have hi2 : i ≠ 2 := by
    intro h2
    rw [h2] at hgi
    norm_num at hgi
    exact hne4 hgi
  rw [hgi, show i = 1 by omega]
  norm_num

/-- **6B.8 の base case**: `|P| = 8` かつ `|P : P'| = 4` なら `P` は `D_8` か `Q_8`。

`|P'| = 2 ≠ 1` から非可換なので repo の Cor 6.14
(`dihedralOrQuaternion_of_card_eight`) がそのまま使える。 -/
theorem tausskyTodd_card_eight {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 8) (hidx : (commutator P).index = 4) :
    Nonempty (P ≃* DihedralGroup 4) ∨ Nonempty (P ≃* QuaternionGroup 2) := by
  refine dihedralOrQuaternion_of_card_eight hcard ?_
  by_contra hcon
  have hall : ∀ x y : P, x * y = y * x := by
    intro x y
    by_contra h
    exact hcon ⟨x, y, h⟩
  have hbot : commutator P = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    exact Subgroup.mem_centralizer_iff.mpr fun y _ => hall y x
  rw [hbot, Subgroup.index_bot, hcard] at hidx
  omega

/-- **Isaacs Problem 6B.8** (p. 196, O. Taussky-Todd) ⭐: `|P| ≥ 8` の `2`-群 `P` が
`|P : P'| = 4` をみたすなら, `P` は二面体・半二面体・一般四元数のいずれか。 -/
theorem tausskyTodd {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : 8 ≤ Nat.card P) (hidx : (commutator P).index = 4) :
    (∃ n : ℕ, Nonempty (P ≃* DihedralGroup n)) ∨
      (∃ n : ℕ, Nonempty (P ≃* QuaternionGroup n)) ∨
      (∃ k : ℕ, Nonempty (P ≃* SemiDihedralGroup k)) := by
  sorry

end

end OddOrder.Isaacs.Ch06
