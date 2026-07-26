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
  haveI : IsMulCommutative A :=
    MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
      (by rwa [QuotientGroup.ker_mk'])
  exact (IsMulCommutative.is_comm (M := A)).comm x y

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

/-- `b ∈ Z(P)⟨a⟩` なら `a` と `b` は可換。

`b = z a^i` (`z` 中心的) と書けるので直接計算。`⟨Z(P), a⟩` に `b` が入らないことを
示すのに (対偶で) 使う。 -/
theorem mul_comm_of_mem_sup_center_zpowers {P : Type*} [Group P] {a b : P}
    (hb : b ∈ Subgroup.center P ⊔ Subgroup.zpowers a) : a * b = b * a := by
  haveI : (Subgroup.center P).Normal := inferInstance
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hb
  obtain ⟨z, hz, t, ht, rfl⟩ := hb
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hcz := Subgroup.mem_center_iff.mp hz
  have hcomm : a * a ^ i = a ^ i * a := ((Commute.refl a).zpow_right i).eq
  calc a * (z * a ^ i) = (a * z) * a ^ i := by group
    _ = (z * a) * a ^ i := by rw [hcz a]
    _ = z * (a * a ^ i) := by group
    _ = z * (a ^ i * a) := by rw [hcomm]
    _ = (z * a ^ i) * a := by group

/-- `|P : Z(P)| = 4` かつ `a, b` が非可換なら `⟨Z(P), a, b⟩ = P`。

`L := Z(P)⟨a⟩` の指数は `4` でも `1` でもない (どちらでも `a, b` が可換になる) ので `2`,
すると `K := ⟨Z(P), a, b⟩` の指数が `2` だと `L = K ∋ b` でやはり可換になり矛盾。
ゆえに `K` の指数は `1`。 -/
theorem sup_center_zpowers_eq_top {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) {a b : P} (hab : a * b ≠ b * a) :
    Subgroup.center P ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b = ⊤ := by
  have hZL : Subgroup.center P ≤ Subgroup.center P ⊔ Subgroup.zpowers a := le_sup_left
  have haL : a ∈ Subgroup.center P ⊔ Subgroup.zpowers a :=
    (le_sup_right : Subgroup.zpowers a ≤ _) (Subgroup.mem_zpowers a)
  have hLK : (Subgroup.center P ⊔ Subgroup.zpowers a)
      ≤ Subgroup.center P ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b := le_sup_left
  have hbK : b ∈ Subgroup.center P ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b :=
    (le_sup_right : Subgroup.zpowers b ≤ _) (Subgroup.mem_zpowers b)
  have hmulL := Subgroup.relIndex_mul_index hZL
  rw [h] at hmulL
  have hLne4 : (Subgroup.center P ⊔ Subgroup.zpowers a).index ≠ 4 := by
    intro h4
    rw [h4] at hmulL
    have hrel : (Subgroup.center P).relIndex (Subgroup.center P ⊔ Subgroup.zpowers a) = 1 := by
      omega
    have haZ : a ∈ Subgroup.center P := Subgroup.relIndex_eq_one.mp hrel haL
    exact hab (Subgroup.mem_center_iff.mp haZ b).symm
  have hLne1 : (Subgroup.center P ⊔ Subgroup.zpowers a).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    exact hab (mul_comm_of_mem_sup_center_zpowers (h1 ▸ Subgroup.mem_top b))
  have hLdvd : (Subgroup.center P ⊔ Subgroup.zpowers a).index ∣ 4 := Dvd.intro_left _ hmulL
  have hL2 : (Subgroup.center P ⊔ Subgroup.zpowers a).index = 2 := by
    obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      ((show (2 : ℕ) ^ 2 = 4 by norm_num) ▸ hLdvd)
    have hi0 : i ≠ 0 := fun h0 => hLne1 (by rw [hgi, h0, pow_zero])
    have hi2 : i ≠ 2 := fun h2 => hLne4 (by rw [hgi, h2]; norm_num)
    rw [hgi, show i = 1 by omega]
    norm_num
  have hmulK := Subgroup.relIndex_mul_index hLK
  rw [hL2] at hmulK
  have hKne2 : (Subgroup.center P ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b).index ≠ 2 := by
    intro h2
    rw [h2] at hmulK
    have hrel : (Subgroup.center P ⊔ Subgroup.zpowers a).relIndex
        (Subgroup.center P ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b) = 1 := by omega
    exact hab (mul_comm_of_mem_sup_center_zpowers (Subgroup.relIndex_eq_one.mp hrel hbK))
  have hKdvd : (Subgroup.center P ⊔ Subgroup.zpowers a ⊔ Subgroup.zpowers b).index ∣ 2 :=
    Dvd.intro_left _ hmulK
  refine Subgroup.index_eq_one.mp ?_
  rcases (Nat.dvd_prime Nat.prime_two).mp hKdvd with h1 | h2
  · exact h1
  · exact absurd h2 hKne2

/-- `|P : Z(P)| = 4` なら `P' ≤ ⟨[a,b]⟩` (`a, b` は任意の非可換な組)。

`x ↦ [x,y]` と `y ↦ [x,y]` がどちらも準同型 (双線形性) なので, `⟨Z(P), a, b⟩ = P` に
沿った**閉包帰納法**で剰余類代表の場合分けを回避できる。 -/
theorem commutator_le_zpowers_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) {a b : P} (hab : a * b ≠ b * a) :
    commutator P ≤ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) := by
  have hc := commutator_le_center_of_index_center_eq_four h
  have hzero : ∀ z ∈ Subgroup.center P, ∀ y : P, z * y * z⁻¹ * y⁻¹ = 1 := by
    intro z hz y
    have hcz := Subgroup.mem_center_iff.mp hz y
    rw [← hcz]; group
  have hzero' : ∀ x : P, ∀ z ∈ Subgroup.center P, x * z * x⁻¹ * z⁻¹ = 1 := by
    intro x z hz
    have hcz := Subgroup.mem_center_iff.mp hz x
    rw [hcz]; group
  -- 第 1 引数についての閉包帰納法
  have step1 : ∀ y : P, a * y * a⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) →
      b * y * b⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) →
      ∀ x : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) := by
    intro y hay hby x
    let φ : P →* P :=
      { toFun := fun w => w * y * w⁻¹ * y⁻¹
        map_one' := by group
        map_mul' := fun w₁ w₂ => commutator_mul_left_of_le_center hc w₁ w₂ y }
    have hsub : (⊤ : Subgroup P) ≤ (Subgroup.zpowers (a * b * a⁻¹ * b⁻¹)).comap φ := by
      rw [← sup_center_zpowers_eq_top h hab]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro z hz
        have hz1 : φ z = 1 := hzero z hz y
        change φ z ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹)
        rw [hz1]
        exact Subgroup.one_mem _
      · rw [Subgroup.zpowers_le]; exact hay
      · rw [Subgroup.zpowers_le]; exact hby
    exact hsub (Subgroup.mem_top x)
  -- 第 2 引数についての閉包帰納法
  have step2 : ∀ x : P, x * a * x⁻¹ * a⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) →
      x * b * x⁻¹ * b⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) →
      ∀ y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) := by
    intro x hxa hxb y
    let ψ : P →* P :=
      { toFun := fun w => x * w * x⁻¹ * w⁻¹
        map_one' := by group
        map_mul' := fun w₁ w₂ => commutator_mul_right_of_le_center hc x w₁ w₂ }
    have hsub : (⊤ : Subgroup P) ≤ (Subgroup.zpowers (a * b * a⁻¹ * b⁻¹)).comap ψ := by
      rw [← sup_center_zpowers_eq_top h hab]
      refine sup_le (sup_le ?_ ?_) ?_
      · intro z hz
        have hz1 : ψ z = 1 := hzero' x z hz
        change ψ z ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹)
        rw [hz1]
        exact Subgroup.one_mem _
      · rw [Subgroup.zpowers_le]; exact hxa
      · rw [Subgroup.zpowers_le]; exact hxb
    exact hsub (Subgroup.mem_top y)
  have hAll : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) := by
    have hA : ∀ y : P, a * y * a⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) :=
      step2 a (by rw [show a * a * a⁻¹ * a⁻¹ = 1 by group]; exact Subgroup.one_mem _)
        (Subgroup.mem_zpowers _)
    have hB : ∀ y : P, b * y * b⁻¹ * y⁻¹ ∈ Subgroup.zpowers (a * b * a⁻¹ * b⁻¹) :=
      step2 b (by
          rw [show b * a * b⁻¹ * a⁻¹ = (a * b * a⁻¹ * b⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _))
        (by rw [show b * b * b⁻¹ * b⁻¹ = 1 by group]; exact Subgroup.one_mem _)
    intro x y
    exact step1 y (hA y) (hB y) x
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr fun x _ y _ => ?_
  rw [commutatorElement_def]
  exact hAll x y

/-- `|P : Z(P)| = 4` なら `|P'| ≤ 2`。 -/
theorem card_commutator_le_two_of_index_center_eq_four {P : Type*} [Group P] [Finite P]
    (h : (Subgroup.center P).index = 4) : Nat.card ↥(commutator P) ≤ 2 := by
  obtain ⟨a, b, hab⟩ : ∃ a b : P, a * b ≠ b * a := by
    by_contra hcon
    have hall : ∀ x y : P, x * y = y * x := by
      intro x y
      by_contra hxy
      exact hcon ⟨x, y, hxy⟩
    have htop : Subgroup.center P = ⊤ :=
      eq_top_iff.mpr fun g _ => Subgroup.mem_center_iff.mpr fun y => hall y g
    rw [htop, Subgroup.index_top] at h
    omega
  have hle := commutator_le_zpowers_of_index_center_eq_four h hab
  have hc2 : (a * b * a⁻¹ * b⁻¹) ^ 2 = 1 := commutator_sq_eq_one_of_index_center_eq_four h a b
  have hord : orderOf (a * b * a⁻¹ * b⁻¹) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hc2
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers] at hdvd
  exact le_trans (Nat.le_of_dvd (orderOf_pos _) hdvd) hord

/-- **6B.8 の要**: `|P : P'| = 4` かつ `|P| ≥ 16` なら `|P : Z(P)| > 4`
(6B.7 を適用するのに必要)。

`|P : Z(P)| ≤ 2` なら `P` 可換で `P' = 1`, `|P : P'| = |P| ≥ 16 ≠ 4`。
`|P : Z(P)| = 4` なら `|P'| ≤ 2` なので `|P| = |P:P'|·|P'| ≤ 8`。 -/
theorem four_lt_index_center {P : Type*} [Group P] [Finite P]
    (hcard : 16 ≤ Nat.card P) (hidx : (commutator P).index = 4) :
    4 < (Subgroup.center P).index := by
  by_contra hcon
  have hle : (Subgroup.center P).index ≤ 4 := by omega
  have hmul := Subgroup.card_mul_index (commutator P)
  rw [hidx] at hmul
  rcases Nat.lt_or_ge (Subgroup.center P).index 4 with hlt | hge
  · -- `≤ 3`: `P/Z(P)` は巡回ゆえ `P` 可換で `P' = ⊥`
    have hcyc : IsCyclic (P ⧸ Subgroup.center P) := by
      have hcard : Nat.card (P ⧸ Subgroup.center P) < 4 := hlt
      have hpos : 0 < Nat.card (P ⧸ Subgroup.center P) := Nat.card_pos
      interval_cases hn : (Nat.card (P ⧸ Subgroup.center P))
      · haveI : Subsingleton (P ⧸ Subgroup.center P) :=
          (Nat.card_eq_one_iff_unique.mp hn).1
        exact isCyclic_of_subsingleton
      · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card (p := 2) hn
      · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact isCyclic_of_prime_card (p := 3) hn
    have hall := mul_comm_of_center_le_of_isCyclic_quotient (A := P) le_rfl hcyc
    have hbot : commutator P = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _
      exact Subgroup.mem_centralizer_iff.mpr fun y _ => hall y x
    rw [hbot, Subgroup.index_bot] at hidx
    omega
  · -- `= 4`
    have h4 : (Subgroup.center P).index = 4 := by omega
    have hcle := card_commutator_le_two_of_index_center_eq_four h4
    have hpos : 0 < Nat.card ↥(commutator P) := Nat.card_pos
    omega

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

/-- 全元が `g² = 1` をみたす群は可換。 -/
theorem mul_comm_of_forall_sq_eq_one {G : Type*} [Group G] (h : ∀ g : G, g ^ 2 = 1) (x y : G) :
    x * y = y * x := by
  have hinv : ∀ w : G, w⁻¹ = w := fun w => by
    have hw := h w
    rw [pow_two] at hw
    exact inv_eq_of_mul_eq_one_right hw
  calc x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinv, hinv]

/-- **帰納法の base case (指数 2 の巡回部分群版)**: 非可換な位数 `8` の群は位数 `4` の元を
持ち, その生成する巡回部分群は指数 `2`。

全元が `g² = 1` なら可換, 位数 `8` の元があれば巡回でやはり可換。 -/
theorem exists_index_two_zpowers_of_card_eight {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 8) (hnonab : ∃ x y : P, x * y ≠ y * x) :
    ∃ c : P, (Subgroup.zpowers c).index = 2 := by
  classical
  obtain ⟨u, v, huv⟩ := hnonab
  obtain ⟨x, hx⟩ : ∃ x : P, orderOf x = 4 := by
    by_contra hcon
    have hsq : ∀ w : P, w ^ 2 = 1 := by
      intro w
      have hdvd : orderOf w ∣ 8 := hcard ▸ orderOf_dvd_natCard w
      have hne4 : orderOf w ≠ 4 := fun hh => hcon ⟨w, hh⟩
      have hne8 : orderOf w ≠ 8 := by
        intro h8
        haveI : IsCyclic P := isCyclic_of_orderOf_eq_card w (by rw [h8, hcard])
        obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg v)
        exact huv (by rw [← zpow_add, ← zpow_add, add_comm])
      obtain ⟨i, hi, hgi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
        ((show (2 : ℕ) ^ 3 = 8 by norm_num) ▸ hdvd)
      have hi2 : i ≠ 2 := by
        intro h2
        rw [h2] at hgi
        norm_num at hgi
        exact hne4 hgi
      have hi3 : i ≠ 3 := by
        intro h3
        rw [h3] at hgi
        norm_num at hgi
        exact hne8 hgi
      refine orderOf_dvd_iff_pow_eq_one.mp ?_
      rw [hgi]
      simpa using pow_dvd_pow 2 (show i ≤ 1 by omega)
    exact absurd (mul_comm_of_forall_sq_eq_one hsq u v) huv
  refine ⟨x, ?_⟩
  have hmul := Subgroup.card_mul_index (Subgroup.zpowers x)
  rw [Nat.card_zpowers, hx, hcard] at hmul
  omega

/-- 巡回部分群に含まれる部分群は巡回。 -/
theorem isCyclic_of_le_zpowers {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h : H ≤ Subgroup.zpowers g) : IsCyclic ↥H := by
  haveI : IsCyclic ↥(Subgroup.zpowers g) := Subgroup.isCyclic_zpowers g
  haveI : IsCyclic ↥(H.subgroupOf (Subgroup.zpowers g)) := inferInstance
  have e : ↥(H.subgroupOf (Subgroup.zpowers g)) ≃* ↥H := Subgroup.subgroupOfEquivOfLe h
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

/-- 全射準同型による引き戻しは指数を保つ。 -/
theorem index_comap_of_surjective {G G' : Type*} [Group G] [Group G'] {f : G →* G'}
    (hf : Function.Surjective f) (K : Subgroup G') : (K.comap f).index = K.index := by
  rw [Subgroup.index_comap, MonoidHom.range_eq_top.mpr hf, Subgroup.relIndex_top_right]

/-- **帰納 step の引き戻し**: `Z ≤ Z(P)` (正規) のとき, `P/Z` の巡回部分群 `⟨c⟩` の
引き戻しは**可換**。

`φ : A → P/Z` の像は `⟨c⟩` に含まれるので巡回, 核は `Z ∩ A ≤ Z(A)`。 -/
theorem isMulCommutative_comap_zpowers {P : Type*} [Group P] {Z : Subgroup P} [Z.Normal]
    (hZ : Z ≤ Subgroup.center P) (c : P ⧸ Z) :
    IsMulCommutative ↥((Subgroup.zpowers c).comap (QuotientGroup.mk' Z)) := by
  let A : Subgroup P := (Subgroup.zpowers c).comap (QuotientGroup.mk' Z)
  let φ : ↥A →* ↥(Subgroup.zpowers c) :=
    ((QuotientGroup.mk' Z).comp A.subtype).codRestrict (Subgroup.zpowers c) (fun w => w.2)
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center φ ?_
  intro w hw
  have hwZ : (w : P) ∈ Z := by
    have hw1 : (QuotientGroup.mk' Z) ((w : P)) = 1 := congrArg Subtype.val hw
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hw1
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ hwZ) ((g : P)))

/-! ### 帰納 step の非巡回ケース: `θ(x) = x⁻¹ · a x a⁻¹` の性質 -/

/-- `A` 可換で `a` が `A` を正規化するとき `θ(x) = x⁻¹ · a x a⁻¹` は**準同型**。 -/
theorem theta_mul {P : Type*} [Group P] {A : Subgroup P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (a : P)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) {x y : P} (hx : x ∈ A) (hy : y ∈ A) :
    (x * y)⁻¹ * (a * (x * y) * a⁻¹)
      = (x⁻¹ * (a * x * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) := by
  have h1 : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
  have hc : y⁻¹ * (x⁻¹ * (a * x * a⁻¹)) = (x⁻¹ * (a * x * a⁻¹)) * y⁻¹ :=
    hab _ _ (A.inv_mem hy) (A.mul_mem (A.inv_mem hx) (hnorm x hx))
  rw [h1, mul_inv_rev]
  calc y⁻¹ * x⁻¹ * ((a * x * a⁻¹) * (a * y * a⁻¹))
      = (y⁻¹ * (x⁻¹ * (a * x * a⁻¹))) * (a * y * a⁻¹) := by group
    _ = ((x⁻¹ * (a * x * a⁻¹)) * y⁻¹) * (a * y * a⁻¹) := by rw [hc]
    _ = (x⁻¹ * (a * x * a⁻¹)) * (y⁻¹ * (a * y * a⁻¹)) := by group

/-- **`a` は `θ` の像を反転する**: `a² ∈ A` (可換) なので `θ(x)^a = θ(x)⁻¹`。

これが非巡回ケースの矛盾の鍵 — `P' = im θ` が `a` に反転されるので
`C_{P'}(a) = Ω₁(P')` となり `P'` は巡回になる。 -/
theorem theta_conj_eq_inv {P : Type*} [Group P] {A : Subgroup P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) {a : P} (ha2 : a ^ 2 ∈ A)
    {x : P} (hx : x ∈ A) :
    a * (x⁻¹ * (a * x * a⁻¹)) * a⁻¹ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by
  have hcomm := hab _ _ ha2 hx
  have hx2 : a ^ 2 * x * (a ^ 2)⁻¹ = x := by
    calc a ^ 2 * x * (a ^ 2)⁻¹ = (x * a ^ 2) * (a ^ 2)⁻¹ := by rw [hcomm]
      _ = x := by group
  calc a * (x⁻¹ * (a * x * a⁻¹)) * a⁻¹
      = (a * x⁻¹ * a⁻¹) * (a ^ 2 * x * (a ^ 2)⁻¹) := by rw [pow_two]; group
    _ = (a * x⁻¹ * a⁻¹) * x := by rw [hx2]
    _ = (x⁻¹ * (a * x * a⁻¹))⁻¹ := by group

/-- `θ(x) = x⁻¹ · a x a⁻¹` を準同型として束ねたもの (`A` 可換, `a` が `A` を正規化)。 -/
def thetaHom {P : Type*} [Group P] (A : Subgroup P) (a : P)
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) : ↥A →* P where
  toFun x := (x : P)⁻¹ * (a * (x : P) * a⁻¹)
  map_one' := by simp
  map_mul' x y := theta_mul hab a hnorm x.2 y.2

/-- `θ` の像は `A` に含まれる。 -/
theorem thetaHom_range_le {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    (thetaHom A a hab hnorm).range ≤ A := by
  rintro _ ⟨x, rfl⟩
  exact A.mul_mem (A.inv_mem x.2) (hnorm _ x.2)

/-- `θ` の核は `C_A(a)`。 -/
theorem mem_thetaHom_ker_iff {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (x : ↥A) :
    x ∈ (thetaHom A a hab hnorm).ker ↔ a * (x : P) = (x : P) * a := by
  constructor
  · intro hx
    have hx1 : (x : P)⁻¹ * (a * (x : P) * a⁻¹) = 1 := hx
    have h2 := congrArg (fun w => (x : P) * w * a) hx1
    simpa [mul_assoc] using h2
  · intro hx
    show (x : P)⁻¹ * (a * (x : P) * a⁻¹) = 1
    rw [hx]
    group

/-- `θ` の像は `P'` に含まれる (`θ(x) = ⁅x⁻¹, a⁆`)。 -/
theorem thetaHom_range_le_commutator {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) :
    (thetaHom A a hab hnorm).range ≤ commutator P := by
  rintro _ ⟨x, rfl⟩
  have h1 := Subgroup.commutator_mem_commutator (G := P) (H₁ := ⊤) (H₂ := ⊤)
    (Subgroup.mem_top ((x : P)⁻¹)) (Subgroup.mem_top a)
  rw [← commutator_def, commutatorElement_def] at h1
  show (x : P)⁻¹ * (a * (x : P) * a⁻¹) ∈ commutator P
  convert h1 using 1
  group

/-- `thetaHom` 版の反転則: `a · θ(x) · a⁻¹ = θ(x)⁻¹`。 -/
theorem thetaHom_conj_eq_inv {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (ha2 : a ^ 2 ∈ A)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (x : ↥A) :
    a * (thetaHom A a hab hnorm x) * a⁻¹ = (thetaHom A a hab hnorm x)⁻¹ :=
  theta_conj_eq_inv hab ha2 x.2

/-- `A` の元は `θ` の像を中心化する (像は可換な `A` に含まれるから)。 -/
theorem thetaHom_range_centralized {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) {u : P} (hu : u ∈ A)
    {w : P} (hw : w ∈ (thetaHom A a hab hnorm).range) : u * w = w * u :=
  hab _ _ hu (thetaHom_range_le hab hnorm hw)

/-- `a² ∈ A` (可換) なら `a⁻¹` も `A` を正規化する (`a⁻¹ x a = a x a⁻¹`)。 -/
theorem inv_conj_mem_of_sq_mem {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (ha2 : a ^ 2 ∈ A)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) {x : P} (hx : x ∈ A) : a⁻¹ * x * a ∈ A := by
  have hfix : a ^ 2 * x * (a ^ 2)⁻¹ = x := by
    have hc := hab _ _ ha2 hx
    calc a ^ 2 * x * (a ^ 2)⁻¹ = (x * a ^ 2) * (a ^ 2)⁻¹ := by rw [hc]
      _ = x := by group
  have heq : a⁻¹ * x * a = a * x * a⁻¹ := by
    conv_lhs => rw [← hfix]
    group
  rw [heq]
  exact hnorm x hx

/-- `θ` の像は `P` で正規。

`A` の元は像を中心化し, `a` は像を反転する。`P = ⟨A, a⟩` なのでこれで正規化群が `⊤`。 -/
theorem thetaHom_range_normal {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (ha2 : a ^ 2 ∈ A)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A)
    (hgen : A ⊔ Subgroup.zpowers a = ⊤) :
    ((thetaHom A a hab hnorm).range).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
  refine sup_le (fun u hu => ?_) (Subgroup.zpowers_le.mpr ?_)
  · refine Subgroup.mem_normalizer_iff.mpr fun w => ?_
    constructor
    · intro hw
      rwa [thetaHom_range_centralized hab hnorm hu hw, mul_assoc, mul_inv_cancel, mul_one]
    · intro hw
      have hwA : w ∈ A := by
        have hc : u * w * u⁻¹ ∈ A := thetaHom_range_le hab hnorm hw
        have h2 : w = u⁻¹ * (u * w * u⁻¹) * u := by group
        rw [h2]
        exact A.mul_mem (A.mul_mem (A.inv_mem hu) hc) hu
      rwa [hab _ _ hu hwA, mul_assoc, mul_inv_cancel, mul_one] at hw
  · refine Subgroup.mem_normalizer_iff.mpr fun w => ?_
    constructor
    · rintro ⟨x, rfl⟩
      rw [thetaHom_conj_eq_inv hab ha2 hnorm x]
      exact Subgroup.inv_mem _ ⟨x, rfl⟩
    · intro hw
      have hyA : a * w * a⁻¹ ∈ A := thetaHom_range_le hab hnorm hw
      have hwA : w ∈ A := by
        have h2 : w = a⁻¹ * (a * w * a⁻¹) * a := by group
        rw [h2]
        exact inv_conj_mem_of_sq_mem hab ha2 hnorm hyA
      obtain ⟨x, hx⟩ := hw
      have hinv := thetaHom_conj_eq_inv hab ha2 hnorm x
      rw [hx] at hinv
      have hfix : a ^ 2 * w * (a ^ 2)⁻¹ = w := by
        have hc := hab _ _ ha2 hwA
        calc a ^ 2 * w * (a ^ 2)⁻¹ = (w * a ^ 2) * (a ^ 2)⁻¹ := by rw [hc]
          _ = w := by group
      have hkey : w = (thetaHom A a hab hnorm x)⁻¹ := by
        rw [hx, ← hinv]
        conv_lhs => rw [← hfix]
        rw [pow_two]
        group
      rw [hkey]
      exact Subgroup.inv_mem _ ⟨x, rfl⟩

/-- 逆包含 `P' ≤ im θ`。

`R := im θ` は正規で `P/R` は可換 — `A` の像どうしは可換, `a` の像は
`a⁻¹ x⁻¹ a x = a⁻¹ · θ(x) · a ∈ R` (正規性) により `A` の像と可換。 -/
theorem commutator_le_thetaHom_range {P : Type*} [Group P] {A : Subgroup P} {a : P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (ha2 : a ^ 2 ∈ A)
    (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A) (hgen : A ⊔ Subgroup.zpowers a = ⊤) :
    commutator P ≤ (thetaHom A a hab hnorm).range := by
  haveI hRn := thetaHom_range_normal hab ha2 hnorm hgen
  -- `a` の像は `A` の像と可換
  have hax : ∀ x ∈ A, (QuotientGroup.mk a : P ⧸ (thetaHom A a hab hnorm).range) *
      QuotientGroup.mk x = QuotientGroup.mk x * QuotientGroup.mk a := by
    intro x hx
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hmem : a⁻¹ * ((thetaHom A a hab hnorm) ⟨x, hx⟩)⁻¹ * a
        ∈ (thetaHom A a hab hnorm).range := by
      simpa using hRn.conj_mem _ (Subgroup.inv_mem _ ⟨(⟨x, hx⟩ : ↥A), rfl⟩) a⁻¹
    have heq : (a * x)⁻¹ * (x * a)
        = a⁻¹ * ((thetaHom A a hab hnorm) ⟨x, hx⟩)⁻¹ * a := by
      change (a * x)⁻¹ * (x * a) = a⁻¹ * (x⁻¹ * (a * x * a⁻¹))⁻¹ * a
      group
    rw [heq]
    exact hmem
  -- `A` の像どうしは可換
  have haa : ∀ x ∈ A, ∀ y ∈ A, (QuotientGroup.mk x : P ⧸ (thetaHom A a hab hnorm).range) *
      QuotientGroup.mk y = QuotientGroup.mk y * QuotientGroup.mk x := by
    intro x hx y hy
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab _ _ hx hy]
  -- どの元の像も中心的
  have hcentral : ∀ w : P, (QuotientGroup.mk w : P ⧸ (thetaHom A a hab hnorm).range)
      ∈ Subgroup.center _ := by
    have hset : A ⊔ Subgroup.zpowers a ≤
        (Subgroup.center (P ⧸ (thetaHom A a hab hnorm).range)).comap
          (QuotientGroup.mk' (thetaHom A a hab hnorm).range) := by
      refine sup_le (fun x hx => ?_) (Subgroup.zpowers_le.mpr ?_)
      · refine Subgroup.mem_center_iff.mpr fun q => ?_
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        have hv : v ∈ A ⊔ Subgroup.zpowers a := hgen ▸ Subgroup.mem_top v
        have hcx : A ⊔ Subgroup.zpowers a ≤
            (Subgroup.centralizer {(QuotientGroup.mk x :
              P ⧸ (thetaHom A a hab hnorm).range)}).comap
              (QuotientGroup.mk' (thetaHom A a hab hnorm).range) := by
          refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr (haa y hy x hx)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr (hax x hx)
        exact Subgroup.mem_centralizer_singleton_iff.mp (hcx hv)
      · refine Subgroup.mem_center_iff.mpr fun q => ?_
        obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
        have hv : v ∈ A ⊔ Subgroup.zpowers a := hgen ▸ Subgroup.mem_top v
        have hca : A ⊔ Subgroup.zpowers a ≤
            (Subgroup.centralizer {(QuotientGroup.mk a :
              P ⧸ (thetaHom A a hab hnorm).range)}).comap
              (QuotientGroup.mk' (thetaHom A a hab hnorm).range) := by
          refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.mpr ?_)
          · exact Subgroup.mem_centralizer_singleton_iff.mpr (hax y hy).symm
          · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
        exact Subgroup.mem_centralizer_singleton_iff.mp (hca hv)
    intro w
    exact hset (hgen ▸ Subgroup.mem_top w)
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr fun u _ v _ => ?_
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [← commutatorElement_def]
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    (Subgroup.mem_center_iff.mp (hcentral u) _).symm

/-- `A` が指数 `2` で `a ∉ A` なら `⟨A, a⟩ = P`。 -/
theorem sup_zpowers_eq_top_of_index_two {P : Type*} [Group P] {A : Subgroup P}
    (hidxA : A.index = 2) {a : P} (ha : a ∉ A) : A ⊔ Subgroup.zpowers a = ⊤ := by
  have hle : A ≤ A ⊔ Subgroup.zpowers a := le_sup_left
  have hmul := Subgroup.relIndex_mul_index hle
  rw [hidxA] at hmul
  have hne2 : (A ⊔ Subgroup.zpowers a).index ≠ 2 := by
    intro h2
    rw [h2] at hmul
    have hrel : A.relIndex (A ⊔ Subgroup.zpowers a) = 1 := by omega
    exact ha (Subgroup.relIndex_eq_one.mp hrel
      ((le_sup_right : Subgroup.zpowers a ≤ _) (Subgroup.mem_zpowers a)))
  have hdvd : (A ⊔ Subgroup.zpowers a).index ∣ 2 := Dvd.intro_left _ hmul
  refine Subgroup.index_eq_one.mp ?_
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact h1
  · exact absurd h2 hne2

/-- **`|C_A(a)| = 2`**: `A` 可換で指数 `2`, `|P : P'| = 4` なら `θ` の核は位数 `2`。

`|im θ| = |P'| = |P|/4 = |A|/2` と `|ker| · |im| = |A|` から。 -/
theorem card_thetaHom_ker_eq_two {P : Type*} [Group P] [Finite P] {A : Subgroup P}
    (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (hidxA : A.index = 2)
    {a : P} (ha : a ∉ A) (ha2 : a ^ 2 ∈ A) (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A)
    (hidx : (commutator P).index = 4) :
    Nat.card ↥(thetaHom A a hab hnorm).ker = 2 := by
  have hgen := sup_zpowers_eq_top_of_index_two hidxA ha
  have hrange : commutator P = (thetaHom A a hab hnorm).range :=
    le_antisymm (commutator_le_thetaHom_range hab ha2 hnorm hgen)
      (thetaHom_range_le_commutator hab hnorm)
  have hA := Subgroup.card_mul_index A
  rw [hidxA] at hA
  have hC := Subgroup.card_mul_index (commutator P)
  rw [hidx] at hC
  have hsplit : Nat.card ↥(thetaHom A a hab hnorm).ker
      * Nat.card ↥(thetaHom A a hab hnorm).range = Nat.card ↥A := by
    have hq := Subgroup.card_mul_index (thetaHom A a hab hnorm).ker
    have hiso : Nat.card (↥A ⧸ (thetaHom A a hab hnorm).ker)
        = Nat.card ↥(thetaHom A a hab hnorm).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (thetaHom A a hab hnorm)).toEquiv
    rw [show (thetaHom A a hab hnorm).ker.index
      = Nat.card (↥A ⧸ (thetaHom A a hab hnorm).ker) from rfl, hiso] at hq
    exact hq
  rw [← hrange] at hsplit
  have hpos : 0 < Nat.card ↥(commutator P) := Nat.card_pos
  have heq : Nat.card ↥(thetaHom A a hab hnorm).ker * Nat.card ↥(commutator P)
      = 2 * Nat.card ↥(commutator P) := by
    rw [hsplit]
    omega
  exact Nat.eq_of_mul_eq_mul_right hpos heq

/-- 位数 `2` の群では非単位元は一意。 -/
theorem eq_of_ne_one_of_card_eq_two {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 2) {u v : G} (hu : u ≠ 1) (hv : v ≠ 1) : u = v := by
  classical
  by_contra hne
  haveI : Fintype G := Fintype.ofFinite _
  have hc : Fintype.card G = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hsub : ({1, u, v} : Finset G).card ≤ 2 := by
    rw [← hc]; exact Finset.card_le_univ _
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hu, Ne.symm hv]),
    Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton] at hsub
  omega

/-- **`P'` は巡回**: `a` が `P'` を反転し `C_A(a)` が位数 `2` なので, `P'` の involution は
`C_A(a)` の非単位元ただ一つ。 -/
theorem isCyclic_commutator {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    {A : Subgroup P} (hab : ∀ x y : P, x ∈ A → y ∈ A → x * y = y * x) (hidxA : A.index = 2)
    {a : P} (ha : a ∉ A) (ha2 : a ^ 2 ∈ A) (hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A)
    (hidx : (commutator P).index = 4) :
    IsCyclic ↥(commutator P) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen := sup_zpowers_eq_top_of_index_two hidxA ha
  have hrange : commutator P = (thetaHom A a hab hnorm).range :=
    le_antisymm (commutator_le_thetaHom_range hab ha2 hnorm hgen)
      (thetaHom_range_le_commutator hab hnorm)
  have hPA : commutator P ≤ A := by
    rw [hrange]; exact thetaHom_range_le hab hnorm
  have hker2 := card_thetaHom_ker_eq_two hab hidxA ha ha2 hnorm hidx
  refine isCyclic_of_comm_two_group_unique_involution (hP.to_subgroup _) ?_ ?_
  · intro u v
    exact Subtype.ext (hab _ _ (hPA u.2) (hPA v.2))
  · intro y y' hy hy2 hy' hy'2
    -- involution は `ker θ` に入る
    have hmem : ∀ w : ↥(commutator P), w ≠ 1 → w ^ 2 = 1 →
        (⟨(w : P), hPA w.2⟩ : ↥A) ∈ (thetaHom A a hab hnorm).ker := by
      intro w _ hw2
      refine (mem_thetaHom_ker_iff hab hnorm _).mpr ?_
      obtain ⟨x, hx⟩ : ∃ x : ↥A, thetaHom A a hab hnorm x = (w : P) := by
        have : (w : P) ∈ (thetaHom A a hab hnorm).range := hrange ▸ w.2
        exact this
      have hinvw : a * (w : P) * a⁻¹ = (w : P)⁻¹ := by
        rw [← hx]; exact thetaHom_conj_eq_inv hab ha2 hnorm x
      have hwinv : (w : P)⁻¹ = (w : P) := by
        have h2 : (w : P) * (w : P) = 1 := by
          have := congrArg Subtype.val hw2
          rwa [pow_two] at this
        exact (inv_eq_of_mul_eq_one_right h2)
      rw [hwinv] at hinvw
      have := congrArg (fun u => u * a) hinvw
      simpa [mul_assoc] using this
    have hne1 : ∀ w : ↥(commutator P), w ≠ 1 →
        (⟨(w : P), hPA w.2⟩ : ↥A) ≠ 1 := by
      intro w hw hcon
      refine hw ?_
      have hval : (w : P) = 1 := congrArg Subtype.val hcon
      exact Subtype.ext hval
    have hkeq := eq_of_ne_one_of_card_eq_two (G := ↥(thetaHom A a hab hnorm).ker) hker2
      (u := ⟨_, hmem y hy hy2⟩) (v := ⟨_, hmem y' hy' hy'2⟩)
      (by
        intro hcon
        exact hne1 y hy (congrArg Subtype.val hcon))
      (by
        intro hcon
        exact hne1 y' hy' (congrArg Subtype.val hcon))
    exact Subtype.ext (congrArg (fun w => ((w : ↥A) : P)) (congrArg Subtype.val hkeq))

/-- 位数 `2^k` (`k ≥ 2`) の巡回群では involution は平方元: `Ω₁ ≤ ℧¹`。 -/
theorem involution_mem_zpowers_sq {G : Type*} [Group G] {c : G} {k : ℕ} (hk : 2 ≤ k)
    (hord : orderOf c = 2 ^ k) {y : G} (hy : y ∈ Subgroup.zpowers c) (hy2 : y ^ 2 = 1) :
    y ∈ Subgroup.zpowers (c ^ 2) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h1 : c ^ (2 * m) = 1 := by
    rw [mul_comm, zpow_mul]
    exact_mod_cast hy2
  have h2 : ((orderOf c : ℤ)) ∣ 2 * m := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [hord] at h2
  have h3 : ((2 : ℤ) ^ (k - 1)) ∣ m := by
    have hsplit : ((2 ^ k : ℕ) : ℤ) = 2 * 2 ^ (k - 1) := by
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1]
      push_cast
      ring
    rw [hsplit] at h2
    exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
  obtain ⟨s, hs⟩ := h3
  refine Subgroup.mem_zpowers_iff.mpr ⟨(2 : ℤ) ^ (k - 2) * s, ?_⟩
  rw [← zpow_natCast c 2, ← zpow_mul, hs]
  congr 1
  have hk2 : (2 : ℤ) ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    rw [hk1]
    ring
  rw [hk2]
  push_cast
  ring

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
