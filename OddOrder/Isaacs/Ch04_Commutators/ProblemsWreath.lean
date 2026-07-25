/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.WreathProduct
import OddOrder.Isaacs.Ch04_Commutators.Problems

/-!
# Isaacs Chapter 4 — Problem 4A.7 (正則 wreath product の元の位数)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 4A.7 (書籍 p. 124)。

`C` を位数 `p^n` (`n > 0`) の巡回群, `A = C × ⋯ × C` (`p` 個), `U = ⟨u⟩` を位数 `p` の巡回群で
成分を巡回させる作用を入れ, `P = A ⋊ U` (= 正則 wreath product `C ≀ U`) とすると,
**`P` の元の位数の最大値はちょうど `p^{n+1}`**。

* 上界: `P / A ≅ U` は指数 `p` なので `x^p ∈ A`, `A` は指数 `p^n` ⟹ `x^{p^{n+1}} = 1`
  (`pow_prime_pow_succ_eq_one`)
* 下界: `x = ⟨δ_1 c, u⟩` (`c` は `C` の生成元, `δ_1 c` は 1 成分だけ `c` の tuple) は
  `x^p = ⟨const c, 1⟩` を満たす (`pow_card_eq` の巡回和) ので位数はちょうど `p^{n+1}`

`P` は §3A の一般 wreath product `C ≀[Q] Q` (`Q` = 位数 `p` の群の左正則作用) として実現する。
-/

namespace OddOrder.Isaacs.Ch04

open OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch03.WreathProduct

section /- Problem 4A.7: regular wreath product (p. 124) -/

variable {D Q : Type*} [CommGroup D] [Group Q]

/-! ### wreath product の冪の公式 -/

/-- **wreath product の冪** (base 群が可換な場合): `⟨f, q⟩ ^ k` の base 成分は
`f` を `q` の冪で捻ったものの積. -/
theorem pow_mk (f : Q → D) (q : Q) (k : ℕ) :
    (⟨f, q⟩ : D ≀[Q] Q) ^ k
      = ⟨fun ω => ∏ j ∈ Finset.range k, f ((q ^ j)⁻¹ * ω), q ^ k⟩ := by
  induction k with
  | zero => ext ω <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext ω
    · change (fun ω => ∏ j ∈ Finset.range k, f ((q ^ j)⁻¹ * ω)) ω * f ((q ^ k)⁻¹ • ω)
        = ∏ j ∈ Finset.range (k + 1), f ((q ^ j)⁻¹ * ω)
      rw [Finset.prod_range_succ]
      rfl
    · change q ^ k * q = q ^ (k + 1)
      rw [pow_succ]

/-- 生成元の冪で捻った積は群全体にわたる積に等しい (`orderOf q = |Q|` のとき). -/
theorem prod_range_card_eq_prod_univ [Fintype Q] {q : Q}
    (hq : orderOf q = Fintype.card Q) (f : Q → D) (ω : Q) :
    ∏ j ∈ Finset.range (Fintype.card Q), f ((q ^ j)⁻¹ * ω) = ∏ y : Q, f y := by
  classical
  have hinj : ∀ x ∈ Finset.range (Fintype.card Q), ∀ y ∈ Finset.range (Fintype.card Q),
      (q ^ x)⁻¹ * ω = (q ^ y)⁻¹ * ω → x = y := by
    intro x hx y hy hxy
    rw [Finset.mem_range] at hx hy
    have hpow : q ^ x = q ^ y := by
      have := mul_right_cancel hxy
      simpa using congrArg (·⁻¹) this
    rw [← hq] at hx hy
    exact pow_injOn_Iio_orderOf (Set.mem_Iio.mpr hx) (Set.mem_Iio.mpr hy) hpow
  rw [← Finset.prod_image hinj]
  congr 1
  refine Finset.eq_univ_of_card _ ?_
  rw [Finset.card_image_of_injOn hinj, Finset.card_range]

/-! ### Problem 4A.7 -/

variable {p n : ℕ}

/-- **Isaacs Problem 4A.7** (上界, 書籍 p. 124): `|C| = p^n`, `|Q| = p` なら
`C ≀ Q` の元 `x` は `x ^ (p^{n+1}) = 1` を満たす.

`x^p` の `Q`-成分は `(rightHom x)^p = 1` なので `x^p` は base 群 `Q → C` に入り,
そこは指数 `p^n`. -/
theorem pow_prime_pow_succ_eq_one [Finite D] [Finite Q]
    (hD : Nat.card D = p ^ n) (hQ : Nat.card Q = p) (x : D ≀[Q] Q) :
    x ^ p ^ (n + 1) = 1 := by
  -- `x ^ p` の右成分は自明
  have hright : (x ^ p).right = 1 := by
    have : (x ^ p).right = x.right ^ p := by
      simpa using map_pow (rightHom : (D ≀[Q] Q) →* Q) x p
    rw [this, ← hQ]
    exact pow_card_eq_one'
  -- したがって `x ^ p = inl ((x ^ p).left)`
  have hinl : x ^ p = inl (x ^ p).left := eq_inl_of_right_eq_one hright
  -- base 群は指数 `p ^ n`
  have hbase : ((x ^ p).left) ^ p ^ n = 1 := by
    funext ω
    change ((x ^ p).left ω) ^ p ^ n = 1
    rw [← hD]
    exact pow_card_eq_one'
  calc x ^ p ^ (n + 1) = (x ^ p) ^ p ^ n := by rw [← pow_mul, ← pow_succ']
    _ = (inl (x ^ p).left) ^ p ^ n := by rw [← hinl]
    _ = inl (((x ^ p).left) ^ p ^ n) :=
        (map_pow (inl : (Q → D) →* (D ≀[Q] Q)) _ _).symm
    _ = 1 := by rw [hbase, map_one]

/-- **Isaacs Problem 4A.7** (書籍 p. 124): `C` を位数 `p^n` (`n > 0`) の巡回群, `Q` を位数 `p`
の群とすると, 正則 wreath product `C ≀ Q` の元の位数の最大値はちょうど `p^{n+1}`.

下界の証人は `x = ⟨δ c, q⟩` (`c` は `C` の生成元, `δ c` は `1` 成分だけ `c`, `q` は `Q` の生成元):
冪の公式から `x^p = ⟨const c, 1⟩` で, これは位数 `p^n`. -/
theorem exists_orderOf_eq_and_forall_orderOf_dvd [Finite D] [Finite Q]
    [Fact p.Prime] (hD : Nat.card D = p ^ n) (hQ : Nat.card Q = p) (hn : 0 < n)
    (hDcyc : IsCyclic D) :
    (∀ x : D ≀[Q] Q, orderOf x ∣ p ^ (n + 1)) ∧
      ∃ x : D ≀[Q] Q, orderOf x = p ^ (n + 1) := by
  classical
  have := Fintype.ofFinite D
  have := Fintype.ofFinite Q
  have hp1 : 1 < p := Nat.Prime.one_lt (Fact.out : p.Prime)
  refine ⟨fun x => orderOf_dvd_of_pow_eq_one (pow_prime_pow_succ_eq_one hD hQ x), ?_⟩
  -- `Q` の生成元 (位数 `p` は素数)
  obtain ⟨q, hq⟩ : ∃ q : Q, orderOf q = Fintype.card Q := by
    haveI : Fact (Nat.card Q).Prime := ⟨hQ ▸ Fact.out (p := p.Prime)⟩
    obtain ⟨q, hq⟩ := (isCyclic_of_prime_card (α := Q) rfl).exists_generator
    exact ⟨q, by rw [orderOf_eq_card_of_forall_mem_zpowers hq, Nat.card_eq_fintype_card]⟩
  -- `D` の生成元
  obtain ⟨c, hc⟩ := hDcyc.exists_generator
  have hcorder : orderOf c = p ^ n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc, hD]
  -- 証人
  refine ⟨⟨Pi.mulSingle 1 c, q⟩, ?_⟩
  set x : D ≀[Q] Q := ⟨Pi.mulSingle 1 c, q⟩ with hx
  -- `x ^ p = ⟨const c, 1⟩`
  have hcardQ : Fintype.card Q = p := by rw [← Nat.card_eq_fintype_card, hQ]
  have hxp : x ^ p = ⟨fun _ => c, 1⟩ := by
    rw [hx, pow_mk]
    ext ω
    · change (∏ j ∈ Finset.range p, (Pi.mulSingle (1 : Q) c : Q → D) ((q ^ j)⁻¹ * ω)) = c
      rw [← hcardQ, prod_range_card_eq_prod_univ hq]
      rw [Finset.prod_eq_single (1 : Q)]
      · exact Pi.mulSingle_eq_same _ _
      · exact fun b _ hb => Pi.mulSingle_eq_of_ne hb _
      · exact fun h => absurd (Finset.mem_univ _) h
    · change q ^ p = 1
      rw [← hcardQ, ← Nat.card_eq_fintype_card]
      exact pow_card_eq_one'
  -- `x ^ p` の位数は `p ^ n`
  have hconst : orderOf (fun _ : Q => c) = orderOf c := by
    refine orderOf_eq_orderOf_iff.mpr fun m => ?_
    constructor
    · intro h
      simpa using congrFun h (1 : Q)
    · intro h
      funext ω
      simpa using h
  have hxporder : orderOf (x ^ p) = p ^ n := by
    have hmk : (⟨fun _ => c, 1⟩ : D ≀[Q] Q) = inl (fun _ => c) := rfl
    rw [hxp, hmk, orderOf_injective (inl : (Q → D) →* (D ≀[Q] Q)) inl_injective, hconst,
      hcorder]
  -- 位数の確定
  have hdvd : orderOf x ∣ p ^ (n + 1) :=
    orderOf_dvd_of_pow_eq_one (pow_prime_pow_succ_eq_one hD hQ x)
  have hnotdvd : ¬ orderOf x ∣ p ^ n := by
    intro hcon
    have : x ^ p ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp hcon
    have hle : orderOf (x ^ p) ∣ p ^ (n - 1) := by
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← pow_mul]
      have : p * p ^ (n - 1) = p ^ n := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]
      exact ‹x ^ p ^ n = 1›
    rw [hxporder] at hle
    have := (Nat.pow_dvd_pow_iff_le_right hp1).mp hle
    omega
  obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd
  have : k = n + 1 := by
    by_contra hne
    exact hnotdvd (by rw [hkeq]; exact pow_dvd_pow p (by omega))
  rw [hkeq, this]

/-! ### Problem 4A.8(a) — `Z(P) = C_A(U)` = 定数 tuple -/

/-- 任意の元は `inl` 成分と `inr` 成分の積. -/
theorem eq_inl_mul_inr (x : D ≀[Q] Q) : x = inl x.left * inr x.right := by
  ext ω
  · change x.left ω = (x.left * fun ω => (1 : Q → D) ((1 : Q)⁻¹ • ω)) ω
    simp
  · change x.right = 1 * x.right
    rw [one_mul]

/-- **Isaacs Problem 4A.8(a)** (書籍 p. 124): 正則 wreath product `P = A ⋊ U` の中心は
「全成分が等しい tuple」全体, すなわち `Z(P) = C_A(U)`.

`⊇`: 定数 tuple は base とも (base が可換ゆえ) `inr q` とも (共役が成分の置換だけゆえ) 可換.
`⊆`: 中心の元は base を中心化するので `C_W(base) = base` (§3A `centralizer_range_inl_eq`) より
base に入り, さらに `inr` と可換なので §3A `forall_conj_inr_eq_iff_const` で定数. -/
theorem mem_center_iff_exists_const [Nontrivial D] (x : D ≀[Q] Q) :
    x ∈ Subgroup.center (D ≀[Q] Q) ↔ ∃ d : D, x = inl (Function.const Q d) := by
  constructor
  · intro hx
    -- base を中心化 ⟹ base の元
    have hbase : x ∈ (inl : (Q → D) →* D ≀[Q] Q).range := by
      rw [← centralizer_range_inl_eq (Q := Q) (fun a b => mul_comm a b)]
      exact Subgroup.center_le_centralizer _ hx
    obtain ⟨f, rfl⟩ := hbase
    -- `inr` と可換 ⟹ 定数
    have hconst : ∀ ω ω' : Q, f ω = f ω' := by
      refine (forall_conj_inr_eq_iff_const (D := D) (Q := Q) (Ω := Q) f).mp fun q => ?_
      have hq := Subgroup.mem_center_iff.mp hx (inr q)
      calc (inr q : D ≀[Q] Q) * inl f * (inr q)⁻¹ = inl f * inr q * (inr q)⁻¹ := by rw [hq]
        _ = inl f := by group
    exact ⟨f 1, congrArg inl (funext fun ω => hconst ω 1)⟩
  · rintro ⟨d, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    ext ω
    · change (y.left * fun ω => Function.const Q d (y.right⁻¹ • ω)) ω
        = (Function.const Q d * fun ω => y.left ((1 : Q)⁻¹ • ω)) ω
      simp [mul_comm]
    · change y.right * 1 = 1 * y.right
      rw [one_mul, mul_one]

/-- **Isaacs Problem 4A.8(a)** (等式形): `Z(P) = A ⊓ C_P(U) = C_A(U)`. -/
theorem center_eq_inf_centralizer_range_inr [Nontrivial D] :
    Subgroup.center (D ≀[Q] Q)
      = (inl : (Q → D) →* D ≀[Q] Q).range
        ⊓ Subgroup.centralizer ((inr : Q →* D ≀[Q] Q).range : Set (D ≀[Q] Q)) := by
  ext x
  rw [Subgroup.mem_inf, mem_center_iff_exists_const]
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨⟨_, rfl⟩, (mem_centralizer_range_inr_iff (D := D) (Q := Q) (Ω := Q) _).mpr ⟨d, rfl⟩⟩
  · rintro ⟨⟨f, rfl⟩, hcent⟩
    obtain ⟨d, hd⟩ := (mem_centralizer_range_inr_iff (D := D) (Q := Q) (Ω := Q) f).mp hcent
    exact ⟨d, congrArg inl hd⟩

end

end OddOrder.Isaacs.Ch04
