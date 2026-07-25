/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.GeomSum
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

open scoped commutatorElement

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

/-! ### Problem 4A.8(b) — `⁅A, U⁆ = P'` = 成分の積が `1` の tuple -/

/-- base 群の座標積 `f ↦ ∏ ω, f ω` (`D` 可換なので準同型). -/
def coordProdHom [Fintype Q] : (Q → D) →* D where
  toFun f := ∏ ω, f ω
  map_one' := by simp
  map_mul' f g := by simp [Finset.prod_mul_distrib]

/-- 座標の平行移動は座標積を変えない. -/
theorem prod_smul_eq [Fintype Q] (f : Q → D) (q : Q) : ∏ ω, f (q⁻¹ * ω) = ∏ ω, f ω :=
  Fintype.prod_equiv (Equiv.mulLeft q⁻¹) _ _ fun _ => rfl

/-- base と `inr` の交換子: `⁅inl f, inr q⁆ = inl (fun ω => f ω · (f (q⁻¹ ω))⁻¹)`. -/
theorem commutatorElement_inl_inr (f : Q → D) (q : Q) :
    ⁅(inl f : D ≀[Q] Q), inr q⁆ = inl (fun ω => f ω * (f (q⁻¹ * ω))⁻¹) := by
  rw [commutatorElement_def]
  ext ω
  · simp [smul_eq_mul]
  · simp

/-- **Isaacs Problem 4A.8(b)** (書籍 p. 124): `⁅A, U⁆` は「成分の積が `1`」の tuple 全体.

`⊆`: `⁅inl f, inr q⁆` の座標積は `(∏ f)(∏ f)⁻¹ = 1` (平行移動が積を変えないから).
`⊇`: `⁅inl (δ_x d), inr (y x⁻¹)⁆ = inl (δ_x d · (δ_y d)⁻¹)` なので, 積が `1` の `f` を
`f = ∏_x (δ_x (f x) · (δ_1 (f x))⁻¹)` と分解すればよい. -/
theorem commutator_range_inl_range_inr_eq [Fintype Q] :
    ⁅(inl : (Q → D) →* D ≀[Q] Q).range, (inr : Q →* D ≀[Q] Q).range⁆
      = (coordProdHom (D := D) (Q := Q)).ker.map inl := by
  classical
  refine le_antisymm (Subgroup.commutator_le.2 ?_) ?_
  · rintro _ ⟨f, rfl⟩ _ ⟨q, rfl⟩
    refine ⟨fun ω => f ω * (f (q⁻¹ * ω))⁻¹, ?_, (commutatorElement_inl_inr f q).symm⟩
    change (∏ ω, f ω * (f (q⁻¹ * ω))⁻¹) = 1
    calc (∏ ω, f ω * (f (q⁻¹ * ω))⁻¹)
        = (∏ ω, f ω) * ∏ ω, (f (q⁻¹ * ω))⁻¹ := Finset.prod_mul_distrib
      _ = (∏ ω, f ω) * (∏ ω, f (q⁻¹ * ω))⁻¹ := by rw [Finset.prod_inv_distrib]
      _ = (∏ ω, f ω) * (∏ ω, f ω)⁻¹ := by rw [prod_smul_eq]
      _ = 1 := mul_inv_cancel _
  · -- `δ_x d · (δ_y d)⁻¹` が交換子に入る
    have hgen : ∀ (x y : Q) (d : D),
        (inl (fun ω => (Pi.mulSingle x d : Q → D) ω * ((Pi.mulSingle y d : Q → D) ω)⁻¹)
          : D ≀[Q] Q)
          ∈ ⁅(inl : (Q → D) →* D ≀[Q] Q).range, (inr : Q →* D ≀[Q] Q).range⁆ := by
      intro x y d
      have hshift : ∀ ω : Q,
          (Pi.mulSingle x d : Q → D) ((y * x⁻¹)⁻¹ * ω) = (Pi.mulSingle y d : Q → D) ω := by
        intro ω
        by_cases hω : ω = y
        · rw [hω, show ((y * x⁻¹)⁻¹ * y) = x by group, Pi.mulSingle_eq_same,
            Pi.mulSingle_eq_same]
        · rw [Pi.mulSingle_eq_of_ne hω, Pi.mulSingle_eq_of_ne]
          intro hcon
          refine hω ?_
          have h2 : (y * x⁻¹) * ((y * x⁻¹)⁻¹ * ω) = (y * x⁻¹) * x := by rw [hcon]
          calc ω = (y * x⁻¹) * ((y * x⁻¹)⁻¹ * ω) := by group
            _ = (y * x⁻¹) * x := h2
            _ = y := by group
      have hcomm : ⁅(inl (Pi.mulSingle x d) : D ≀[Q] Q), inr (y * x⁻¹)⁆
          = inl (fun ω => (Pi.mulSingle x d : Q → D) ω *
              ((Pi.mulSingle y d : Q → D) ω)⁻¹) := by
        rw [commutatorElement_inl_inr]
        exact congrArg inl (funext fun ω => by rw [hshift ω])
      rw [← hcomm]
      exact Subgroup.commutator_mem_commutator ⟨_, rfl⟩ ⟨_, rfl⟩
    rintro _ ⟨f, hf, rfl⟩
    have hf' : (∏ ω, f ω) = 1 := hf
    -- `f = ∏ x, (δ_x (f x) · (δ_1 (f x))⁻¹)`
    have hdecomp :
        (∏ x : Q, (fun ω => (Pi.mulSingle x (f x) : Q → D) ω *
          ((Pi.mulSingle (1 : Q) (f x) : Q → D) ω)⁻¹)) = f := by
      funext ω
      rw [Finset.prod_apply]
      have h1 : (∏ x : Q, (Pi.mulSingle x (f x) : Q → D) ω) = f ω := by
        have hu := congrFun (Finset.univ_prod_mulSingle f) ω
        rwa [Finset.prod_apply] at hu
      have h2 : (∏ x : Q, (Pi.mulSingle (1 : Q) (f x) : Q → D) ω) = 1 := by
        by_cases hω : ω = (1 : Q)
        · rw [hω]
          simpa only [Pi.mulSingle_eq_same] using hf'
        · simp [Pi.mulSingle_eq_of_ne hω]
      calc (∏ x : Q, ((Pi.mulSingle x (f x) : Q → D) ω *
              ((Pi.mulSingle (1 : Q) (f x) : Q → D) ω)⁻¹))
          = (∏ x : Q, (Pi.mulSingle x (f x) : Q → D) ω)
              * ∏ x : Q, ((Pi.mulSingle (1 : Q) (f x) : Q → D) ω)⁻¹ := Finset.prod_mul_distrib
        _ = f ω * (∏ x : Q, (Pi.mulSingle (1 : Q) (f x) : Q → D) ω)⁻¹ := by
              rw [h1, Finset.prod_inv_distrib]
        _ = f ω := by rw [h2, inv_one, mul_one]
    -- 積は base 群 (可換) の中で取り, `inl` の引き戻し部分群に入ることを使う
    have hmem : (∏ x : Q, (fun ω => (Pi.mulSingle x (f x) : Q → D) ω *
        ((Pi.mulSingle (1 : Q) (f x) : Q → D) ω)⁻¹))
          ∈ Subgroup.comap (inl : (Q → D) →* D ≀[Q] Q)
            ⁅(inl : (Q → D) →* D ≀[Q] Q).range, (inr : Q →* D ≀[Q] Q).range⁆ :=
      Subgroup.prod_mem _ fun x _ => Subgroup.mem_comap.mpr (hgen x 1 (f x))
    rw [← hdecomp]
    exact hmem

/-- `P = A · U` (`A` = base, `U` = `inr` の像) と両者の可換性から, **4A.1** で
`P' = ⁅A, U⁆` (`Q` が可換, たとえば位数 `p` の巡回群のとき). -/
theorem commutator_eq_commutator_range_inl_range_inr (hQcomm : ∀ a b : Q, a * b = b * a) :
    commutator (D ≀[Q] Q)
      = ⁅(inl : (Q → D) →* D ≀[Q] Q).range, (inr : Q →* D ≀[Q] Q).range⁆ := by
  haveI : IsMulCommutative ((inl : (Q → D) →* D ≀[Q] Q).range) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨f, hf⟩ := a.2
    obtain ⟨g, hg⟩ := b.2
    change (a : D ≀[Q] Q) * b = (b : D ≀[Q] Q) * a
    rw [← hf, ← hg, ← map_mul, ← map_mul, mul_comm]
  haveI : IsMulCommutative ((inr : Q →* D ≀[Q] Q).range) := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨q, hq⟩ := a.2
    obtain ⟨q', hq'⟩ := b.2
    change (a : D ≀[Q] Q) * b = (b : D ≀[Q] Q) * a
    rw [← hq, ← hq', ← map_mul, ← map_mul, hQcomm]
  refine commutator_eq_commutator_of_mul_eq_top ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [← inl_left_mul_inr_right x]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  · exact fun g => ⟨inl g.left, ⟨_, rfl⟩, inr g.right, ⟨_, rfl⟩, inl_left_mul_inr_right g⟩

/-- **Isaacs Problem 4A.8(b)** (まとめ): `Q` 可換のとき `P' = ⁅A, U⁆` は
「成分の積が `1`」の tuple 全体. -/
theorem commutator_eq_coordProdHom_ker_map [Fintype Q] (hQcomm : ∀ a b : Q, a * b = b * a) :
    commutator (D ≀[Q] Q) = (coordProdHom (D := D) (Q := Q)).ker.map inl := by
  rw [commutator_eq_commutator_range_inl_range_inr hQcomm,
    commutator_range_inl_range_inr_eq]

/-! ### `P' U` = 増大射 (座標積) の核 -/

/-- **増大射** `x ↦ ∏ ω, x.left ω`: wreath product 全体で定義された準同型.

`(x y).left = x.left · (y.left ∘ shift)` で shift は座標積を変えないので乗法的. -/
def augHom [Fintype Q] : (D ≀[Q] Q) →* D where
  toFun x := ∏ ω, x.left ω
  map_one' := by simp
  map_mul' x y := by
    change (∏ ω, (x * y).left ω) = (∏ ω, x.left ω) * ∏ ω, y.left ω
    calc (∏ ω, (x * y).left ω)
        = ∏ ω, (x.left ω * y.left (x.right⁻¹ * ω)) := by
          refine Finset.prod_congr rfl fun ω _ => ?_
          change (x.left * fun ω => y.left (x.right⁻¹ • ω)) ω = _
          rw [Pi.mul_apply]
          rfl
      _ = (∏ ω, x.left ω) * ∏ ω, y.left (x.right⁻¹ * ω) := Finset.prod_mul_distrib
      _ = (∏ ω, x.left ω) * ∏ ω, y.left ω := by rw [prod_smul_eq]

/-- **`P' U = ker(増大射)`** (`Q` 可換のとき): 「成分の積が `1`」の元全体.

`⊇` は `P' = ⁅A,U⁆` (4A.8(b)) と `inr` の像がどちらも核に入ること,
`⊆` は `x = inl x.left · inr x.right` (§3A) の分解で `inl x.left ∈ P'`. -/
theorem commutator_sup_range_inr_eq_ker_augHom [Fintype Q] (hQcomm : ∀ a b : Q, a * b = b * a) :
    commutator (D ≀[Q] Q) ⊔ (inr : Q →* D ≀[Q] Q).range = (augHom (D := D) (Q := Q)).ker := by
  rw [commutator_eq_coordProdHom_ker_map hQcomm]
  refine le_antisymm (sup_le ?_ ?_) fun x hx => ?_
  · rintro _ ⟨f, hf, rfl⟩
    change (∏ ω, (inl f : D ≀[Q] Q).left ω) = 1
    exact hf
  · rintro _ ⟨q, rfl⟩
    change (∏ ω, (inr q : D ≀[Q] Q).left ω) = 1
    simp
  · have hker : (∏ ω, x.left ω) = 1 := hx
    rw [← inl_left_mul_inr_right x]
    exact Subgroup.mul_mem_sup ⟨x.left, hker, rfl⟩ ⟨x.right, rfl⟩

/-! ### Problem 4A.8(c) — `Z(P'U)` の決定 (⚠ 書籍の主張は `p = 2, n = 1` で偽) -/

/-- **Isaacs Problem 4A.8(c)** (訂正版, 書籍 p. 124): `P'U = ker(augHom)` の元が
`P'U` 全体と可換 ⟺ それは `d^p = 1` なる定数 tuple.

⚠ **仮説 `hd` が要る**: 書籍は無条件に `|Z(P'U)| = p` と述べるが, `p = 2`, `n = 1`
(`C₂ ≀ C₂ = D₈`) では `P' = Z(P)` ゆえ `P'U ≅ C₂ × C₂` が可換で `|Z(P'U)| = 4 ≠ p`.
`hd` (「`d ≠ 1` かつ (`p ≥ 3` または `d² ≠ 1`)」なる `d` の存在) はちょうどこの例外を外す
条件で, `C` が位数 `p^n` の巡回群なら「`p` が奇 または `n ≥ 2`」と同値.

証明: `z` が `P'` の元 `g = δ₁(d) · δ_q(d)⁻¹` (座標積 = 1) と可換なら, 共役が座標の
平行移動なので `g(q⁻¹ ω) = g(ω)`. `ω = 1` で評価すると, `q⁻¹ ≠ q` のとき `d = 1`,
`q⁻¹ = q` (このとき `p = 2`) のとき `d = d⁻¹` となり, どちらも `hd` に反する ⟹ `q = 1`.
あとは `inr` との可換性から `f` が定数, 座標積が `d^p = 1`. -/
theorem forall_commute_ker_augHom_iff [Fintype Q] [Fact p.Prime] (hQcard : Nat.card Q = p)
    (hd : ∃ d : D, d ≠ 1 ∧ (3 ≤ p ∨ d ^ 2 ≠ 1)) (z : D ≀[Q] Q)
    (hz : z ∈ (augHom (D := D) (Q := Q)).ker) :
    (∀ y ∈ (augHom (D := D) (Q := Q)).ker, z * y = y * z)
      ↔ ∃ d : D, d ^ p = 1 ∧ z = inl (Function.const Q d) := by
  classical
  have hcardQ : Fintype.card Q = p := by rw [← Nat.card_eq_fintype_card, hQcard]
  obtain ⟨d, hd1, hd2⟩ := hd
  haveI : Nontrivial D := ⟨⟨d, 1, hd1⟩⟩
  constructor
  · intro hcomm
    -- Step A: `z.right = 1`
    have hright : z.right = 1 := by
      by_contra hq
      have hprod_if : ∀ (x : Q) (c : D), (∏ ω, (if ω = x then c else 1)) = c := by
        intro x c
        rw [Finset.prod_eq_single x] <;> simp +contextual
      set q := z.right with hqdef
      set g : Q → D :=
        fun ω => (if ω = (1 : Q) then d else 1) * (if ω = q then d else 1)⁻¹ with hg
      have hgker : (inl g : D ≀[Q] Q) ∈ (augHom (D := D) (Q := Q)).ker := by
        change (∏ ω, g ω) = 1
        rw [hg, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hprod_if, hprod_if,
          mul_inv_cancel]
      have hconj : ∀ ω : Q, g (q⁻¹ • ω) = g ω := by
        have hzg := hcomm _ hgker
        have hcj : z * inl g * z⁻¹ = inl g := by rw [hzg]; group
        rw [conj_inl_of_comm (fun a b => mul_comm a b) z g] at hcj
        intro ω
        exact congrFun (inl_injective hcj) ω
      have hq1 : (1 : Q) ≠ q := Ne.symm hq
      have hqinv_ne : q⁻¹ ≠ (1 : Q) := fun h => hq (by rw [← inv_inv q, h, inv_one])
      have h1 : g 1 = d := by simp [hg, hq1]
      have hkey : g q⁻¹ = d := by
        have hc1 := hconj 1
        rw [smul_eq_mul, mul_one, h1] at hc1
        exact hc1
      by_cases hqq : q⁻¹ = q
      · -- `q² = 1` かつ `q ≠ 1` ⟹ `p = 2`, よって `hd2` は `d² ≠ 1` の側
        have hgval : g q⁻¹ = d⁻¹ := by simp [hg, hqq, hq]
        have hdd : d * d = 1 := by
          have hinv : d = d⁻¹ := hkey.symm.trans hgval
          nth_rewrite 2 [hinv]
          exact mul_inv_cancel d
        have hd2' : d ^ 2 ≠ 1 := by
          rcases hd2 with h3 | h2
          · exfalso
            have hq2 : q ^ 2 = 1 := by
              rw [pow_two]
              nth_rewrite 1 [← hqq]
              exact inv_mul_cancel q
            have horder : orderOf q = 2 := orderOf_eq_prime hq2 hq
            have hdvd : orderOf q ∣ Nat.card Q := orderOf_dvd_natCard q
            rw [horder, hQcard] at hdvd
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp hdvd
            omega
          · exact h2
        exact hd2' (by rw [pow_two]; exact hdd)
      · have hgval : g q⁻¹ = 1 := by simp [hg, hqinv_ne, hqq]
        exact hd1 (hkey.symm.trans hgval)
    -- Step B: `z = inl f` で `f` は定数
    have hzinl : z = inl z.left := eq_inl_of_right_eq_one hright
    have hconst : ∀ ω ω' : Q, z.left ω = z.left ω' := by
      refine (forall_conj_inr_eq_iff_const (D := D) (Q := Q) (Ω := Q) z.left).mp fun q' => ?_
      have hinr : (inr q' : D ≀[Q] Q) ∈ (augHom (D := D) (Q := Q)).ker := by
        change (∏ ω, (inr q' : D ≀[Q] Q).left ω) = 1
        simp
      have hzq := hcomm _ hinr
      calc (inr q' : D ≀[Q] Q) * inl z.left * (inr q')⁻¹
          = inr q' * z * (inr q')⁻¹ := by rw [← hzinl]
        _ = z * inr q' * (inr q')⁻¹ := by rw [hzq]
        _ = z := by group
        _ = inl z.left := hzinl
    refine ⟨z.left 1, ?_, hzinl.trans (congrArg inl (funext fun ω => hconst ω 1))⟩
    have hker : (∏ ω, z.left ω) = 1 := hz
    calc (z.left 1) ^ p = ∏ _ω : Q, z.left 1 := by
          rw [Finset.prod_const, Finset.card_univ, hcardQ]
      _ = ∏ ω, z.left ω := Finset.prod_congr rfl fun ω _ => (hconst ω 1).symm
      _ = 1 := hker
  · rintro ⟨c, hcp, rfl⟩
    intro y _
    exact (Subgroup.mem_center_iff.mp ((mem_center_iff_exists_const _).mpr ⟨c, rfl⟩) y).symm

/-- 位数 `p^n` (`n ≥ 1`) の巡回群では `x ^ p = 1` の解はちょうど `p` 個
(= `Ω₁` の位数; 4A.8(c) の位数勘定に使う). -/
theorem card_ker_powMonoidHom_prime [Finite D] [Fact p.Prime] (hcyc : IsCyclic D)
    (hD : Nat.card D = p ^ n) (hn : 0 < n) :
    Nat.card ((powMonoidHom p : D →* D).ker) = p := by
  have hp : p.Prime := Fact.out
  obtain ⟨c, hc⟩ := hcyc.exists_generator
  have hcorder : orderOf c = p ^ n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hc, hD]
  -- 像は `⟨c^p⟩`
  have hrange : (powMonoidHom p : D →* D).range = Subgroup.zpowers (c ^ p) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc x)
      refine ⟨k, ?_⟩
      change (c ^ p) ^ k = x ^ p
      rw [← hk, ← zpow_natCast c p, ← zpow_mul, ← zpow_natCast (c ^ k) p, ← zpow_mul, mul_comm]
    · rw [Subgroup.zpowers_le]
      exact ⟨c, rfl⟩
  -- `|range| = p^(n-1)`
  have hcardrange : Nat.card ((powMonoidHom p : D →* D).range) = p ^ (n - 1) := by
    rw [hrange, Nat.card_zpowers, orderOf_pow, hcorder]
    have hgcd : Nat.gcd (p ^ n) p = p := by
      have hdvd : p ∣ p ^ n := dvd_pow_self p (by omega)
      exact Nat.gcd_eq_right hdvd
    rw [hgcd]
    calc p ^ n / p = p ^ n / p ^ 1 := by rw [pow_one]
      _ = p ^ (n - 1) := Nat.pow_div (by omega) hp.pos
  -- Lagrange
  have hmul : Nat.card ((powMonoidHom p : D →* D).ker)
      * ((powMonoidHom p : D →* D).ker).index = Nat.card D := Subgroup.card_mul_index _
  rw [Subgroup.index_ker, hcardrange, hD] at hmul
  have hpow : p ^ n = p * p ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow] at hmul
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos (n - 1)) hmul

/-- **Isaacs Problem 4A.8(c)** (位数, 訂正版, 書籍 p. 124): 仮説 `hd` の下で `|Z(P'U)| = p`.

`Z(P'U) = {inl (const d) : d^p = 1}` (`forall_commute_ker_augHom_iff`) と
「位数 `p^n` の巡回群で `x^p = 1` の解は `p` 個」(`card_ker_powMonoidHom_prime`) を
`d ↦ inl (const d)` の全単射で繋ぐ. -/
theorem card_center_ker_augHom [Fintype Q] [Finite D] [Fact p.Prime] (hQcard : Nat.card Q = p)
    (hD : Nat.card D = p ^ n) (hn : 0 < n) (hcyc : IsCyclic D)
    (hd : ∃ d : D, d ≠ 1 ∧ (3 ≤ p ∨ d ^ 2 ≠ 1)) :
    Nat.card (Subgroup.center ↥((augHom (D := D) (Q := Q)).ker)) = p := by
  have hcardQ : Fintype.card Q = p := by rw [← Nat.card_eq_fintype_card, hQcard]
  have hchar := forall_commute_ker_augHom_iff (D := D) (Q := Q) hQcard hd
  have hmem : ∀ d : D, d ^ p = 1 →
      (inl (Function.const Q d) : D ≀[Q] Q) ∈ (augHom (D := D) (Q := Q)).ker := by
    intro d hdp
    change (∏ _ω : Q, d) = 1
    rw [Finset.prod_const, Finset.card_univ, hcardQ]
    exact hdp
  have hcen : ∀ (d : D) (hdp : d ^ p = 1),
      (⟨inl (Function.const Q d), hmem d hdp⟩ : ↥(augHom (D := D) (Q := Q)).ker)
        ∈ Subgroup.center ↥(augHom (D := D) (Q := Q)).ker := by
    intro d hdp
    refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
    exact ((hchar _ (hmem d hdp)).mpr ⟨d, hdp, rfl⟩ (y : D ≀[Q] Q) y.2).symm
  have hFbij : Function.Bijective
      (fun d : ↥((powMonoidHom p : D →* D).ker) =>
        (⟨⟨inl (Function.const Q (d : D)), hmem (d : D) d.2⟩, hcen (d : D) d.2⟩ :
          ↥(Subgroup.center ↥(augHom (D := D) (Q := Q)).ker))) := by
    constructor
    · intro d₁ d₂ hEq
      have hval : (inl (Function.const Q (d₁ : D)) : D ≀[Q] Q)
          = inl (Function.const Q (d₂ : D)) :=
        congrArg Subtype.val (congrArg Subtype.val hEq)
      exact Subtype.ext (congrFun (inl_injective hval) 1)
    · rintro ⟨⟨z, hzH⟩, hzc⟩
      have hcommz : ∀ y ∈ (augHom (D := D) (Q := Q)).ker, z * y = y * z := by
        intro y hy
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hy⟩).symm
      obtain ⟨d, hdp, rfl⟩ := (hchar z hzH).mp hcommz
      exact ⟨⟨d, hdp⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ hFbij]
  exact card_ker_powMonoidHom_prime hcyc hD hn

/-! ### `P` と `P'U` の位数 (4A.8(d) の maximal class 判定に要る) -/

omit [Group Q] in
/-- 指示関数の座標積は値そのもの. -/
theorem prod_ite_eq_self [Fintype Q] [DecidableEq Q] (x : Q) (c : D) :
    (∏ ω, (if ω = x then c else 1)) = c := by
  rw [Finset.prod_eq_single x] <;> simp +contextual

/-- 増大射は全射 (指示関数で任意の値が実現できる). -/
theorem augHom_surjective [Fintype Q] : Function.Surjective (augHom (D := D) (Q := Q)) := by
  classical
  intro d
  refine ⟨inl (fun ω => if ω = (1 : Q) then d else 1), ?_⟩
  change (∏ ω, (if ω = (1 : Q) then d else 1)) = d
  exact prod_ite_eq_self 1 d

/-- `|P' U| · |C| = |P|`: `P'U = ker(augHom)` で `augHom` は `C` の上へ全射. -/
theorem card_ker_augHom_mul [Fintype Q] [Finite D] :
    Nat.card ((augHom (D := D) (Q := Q)).ker) * Nat.card D = Nat.card (D ≀[Q] Q) := by
  have hidx : ((augHom (D := D) (Q := Q)).ker).index = Nat.card D := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr augHom_surjective]
    exact Subgroup.card_top
  rw [← hidx]
  exact Subgroup.card_mul_index _

/-- `|P| = |C|^{|Q|} · |Q|` (§3A `WreathProduct.card`) から `|P'U| = |C|^{|Q| - 1} · |Q|`. -/
theorem card_ker_augHom_eq [Fintype Q] [Finite D] :
    Nat.card ((augHom (D := D) (Q := Q)).ker) * Nat.card D
      = Nat.card D ^ Nat.card Q * Nat.card Q := by
  rw [card_ker_augHom_mul]
  exact OddOrder.Isaacs.Ch03.WreathProduct.card (D := D) (Q := Q) (Ω := Q)

/-! ### 4A.8(d) の準備: 「`1 - x`」作用素 -/

/-- base 群上の **`1 - x` 作用素** `Δ_q f = f · (f ∘ shift_q)⁻¹`.

群環 `ZMod(p^n)[Q]` の言葉では `f ↦ (1 - q) · f`. 交換子 `⁅inl f, inr q⁆` の base 成分が
ちょうどこれ (`commutatorElement_inl_inr`) なので, 下降中心列
`γ_{i+1}(P) = (1-q)^i A` の解析はこの作用素の反復に帰着する. -/
def shiftSubHom (q : Q) : (Q → D) →* (Q → D) where
  toFun f := fun ω => f ω * (f (q⁻¹ * ω))⁻¹
  map_one' := by funext ω; simp
  map_mul' f g := by
    funext ω
    change f ω * g ω * (f (q⁻¹ * ω) * g (q⁻¹ * ω))⁻¹
      = (f ω * (f (q⁻¹ * ω))⁻¹) * (g ω * (g (q⁻¹ * ω))⁻¹)
    rw [mul_inv_rev]
    simp [mul_comm, mul_left_comm, mul_assoc]

@[simp]
theorem shiftSubHom_apply (q : Q) (f : Q → D) (ω : Q) :
    shiftSubHom q f ω = f ω * (f (q⁻¹ * ω))⁻¹ := rfl

/-- 交換子公式の作用素形: `⁅inl f, inr q⁆ = inl (Δ_q f)`. -/
theorem commutatorElement_inl_inr_eq_shiftSubHom (f : Q → D) (q : Q) :
    ⁅(inl f : D ≀[Q] Q), inr q⁆ = inl (shiftSubHom q f) :=
  commutatorElement_inl_inr f q

/-- `Δ_q` の像は増大射の核に入る (座標積が消える): 群環の `(1-q)·R ⊆ I` に対応. -/
theorem range_shiftSubHom_le_ker_coordProdHom [Fintype Q] (q : Q) :
    (shiftSubHom (D := D) q).range ≤ (coordProdHom (D := D) (Q := Q)).ker := by
  rintro _ ⟨f, rfl⟩
  change (∏ ω, (f ω * (f (q⁻¹ * ω))⁻¹)) = 1
  calc (∏ ω, f ω * (f (q⁻¹ * ω))⁻¹)
      = (∏ ω, f ω) * ∏ ω, (f (q⁻¹ * ω))⁻¹ := Finset.prod_mul_distrib
    _ = (∏ ω, f ω) * (∏ ω, f (q⁻¹ * ω))⁻¹ := by rw [Finset.prod_inv_distrib]
    _ = (∏ ω, f ω) * (∏ ω, f ω)⁻¹ := by rw [prod_smul_eq]
    _ = 1 := mul_inv_cancel _

/-- **base の元と任意の元の交換子**: `⁅inl f, y⁆ = inl (Δ_{y.right} f)`.

`y = inl y.left · inr y.right` と分解すると, `⁅inl f, inl g⁆ = 1` (base は可換) で
残る `⁅inl f, inr q⁆ = inl (Δ_q f)` の共役も base 内なので消える.
下降中心列 `γ_{i+1}(P) = Δ^i(A)` の帰納段はこの式そのもの. -/
theorem commutatorElement_inl_eq_shiftSubHom (f : Q → D) (y : D ≀[Q] Q) :
    ⁅(inl f : D ≀[Q] Q), y⁆ = inl (shiftSubHom y.right f) := by
  have hbase : ⁅(inl f : D ≀[Q] Q), (inl y.left : D ≀[Q] Q)⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    change (inl f : D ≀[Q] Q) * inl y.left = (inl y.left : D ≀[Q] Q) * inl f
    rw [← map_mul, ← map_mul, mul_comm]
  have hcen : (inl y.left : D ≀[Q] Q) * inl (shiftSubHom y.right f) * (inl y.left)⁻¹
      = inl (shiftSubHom y.right f) := by
    rw [← map_inv, ← map_mul, ← map_mul, mul_comm y.left, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅(inl f : D ≀[Q] Q), y⁆
      = ⁅(inl f : D ≀[Q] Q), (inl y.left : D ≀[Q] Q) * inr y.right⁆ := by
          rw [inl_left_mul_inr_right]
    _ = ⁅(inl f : D ≀[Q] Q), (inl y.left : D ≀[Q] Q)⁆ * (inl y.left : D ≀[Q] Q)
          * ⁅(inl f : D ≀[Q] Q), (inr y.right : D ≀[Q] Q)⁆ * (inl y.left : D ≀[Q] Q)⁻¹ :=
        commutatorElement_mul_right_eq_mul_conj _ _ _
    _ = (inl y.left : D ≀[Q] Q) * inl (shiftSubHom y.right f) * (inl y.left : D ≀[Q] Q)⁻¹ := by
          rw [hbase, one_mul, commutatorElement_inl_inr_eq_shiftSubHom]
    _ = inl (shiftSubHom y.right f) := hcen

/-- **部分和作用素** `T_k f = ∏_{j<k} (f ∘ shift^j)` (群環の `1 + x + ⋯ + x^{k-1}`). -/
def shiftSumHom (q : Q) (k : ℕ) : (Q → D) →* (Q → D) where
  toFun f := fun ω => ∏ j ∈ Finset.range k, f ((q ^ j)⁻¹ * ω)
  map_one' := by funext ω; simp
  map_mul' f g := by
    funext ω
    change (∏ j ∈ Finset.range k, (f * g) ((q ^ j)⁻¹ * ω))
      = (∏ j ∈ Finset.range k, f ((q ^ j)⁻¹ * ω)) * ∏ j ∈ Finset.range k, g ((q ^ j)⁻¹ * ω)
    simp only [Pi.mul_apply]
    exact Finset.prod_mul_distrib

@[simp]
theorem shiftSumHom_apply (q : Q) (k : ℕ) (f : Q → D) (ω : Q) :
    shiftSumHom q k f ω = ∏ j ∈ Finset.range k, f ((q ^ j)⁻¹ * ω) := rfl

/-- **`Δ_{q^k} = Δ_q ∘ T_k`** (群環の `1 - x^k = (1-x)(1 + x + ⋯ + x^{k-1})`).

これで「生成元 `q` の `Δ` だけで `⁅A, U⁆` の全生成元が捉えられる」ことが従い,
下降中心列の帰納段が `Δ_q` の反復に帰着する. -/
theorem shiftSubHom_pow_eq_comp (q : Q) (k : ℕ) (f : Q → D) :
    shiftSubHom (q ^ k) f = shiftSubHom q (shiftSumHom q k f) := by
  funext ω
  set G : ℕ → D := fun j => f ((q ^ j)⁻¹ * ω) with hG
  have hstep : ∀ j : ℕ, f ((q ^ j)⁻¹ * (q⁻¹ * ω)) = G (j + 1) := by
    intro j
    have hcomm : (q ^ j)⁻¹ * q⁻¹ = (q ^ (j + 1))⁻¹ := by rw [pow_succ]; group
    rw [hG]
    congr 1
    rw [← mul_assoc, hcomm]
  have htel : (∏ j ∈ Finset.range k, G (j + 1)) * (∏ j ∈ Finset.range k, G j)⁻¹
      = G k * (G 0)⁻¹ := by
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, ← Finset.prod_div_distrib]
    exact Finset.prod_range_div G k
  change f ω * (f ((q ^ k)⁻¹ * ω))⁻¹
    = (∏ j ∈ Finset.range k, G j) * (∏ j ∈ Finset.range k, f ((q ^ j)⁻¹ * (q⁻¹ * ω)))⁻¹
  rw [Finset.prod_congr rfl (fun j _ => hstep j)]
  have hG0 : G 0 = f ω := by rw [hG]; simp
  have hGk : G k = f ((q ^ k)⁻¹ * ω) := rfl
  calc f ω * (f ((q ^ k)⁻¹ * ω))⁻¹ = G 0 * (G k)⁻¹ := by rw [hG0, hGk]
    _ = ((∏ j ∈ Finset.range k, G (j + 1)) * (∏ j ∈ Finset.range k, G j)⁻¹)⁻¹ := by
          rw [htel, mul_inv_rev, inv_inv]
    _ = (∏ j ∈ Finset.range k, G j) * (∏ j ∈ Finset.range k, G (j + 1))⁻¹ := by
          rw [mul_inv_rev, inv_inv]

/-- 座標の平行移動 `shift_q f = f ∘ (q⁻¹ · ·)` (群環の `x ·`). -/
def shiftHom (q : Q) : (Q → D) →* (Q → D) where
  toFun f := fun ω => f (q⁻¹ * ω)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem shiftHom_apply (q : Q) (f : Q → D) (ω : Q) : shiftHom q f ω = f (q⁻¹ * ω) := rfl

/-- shift 安定な部分群は `q` の冪の shift でも閉じている. -/
theorem shift_pow_mem_of_shift_stable {S : Subgroup (Q → D)} {q : Q}
    (hS : S.map (shiftHom q) ≤ S) :
    ∀ (j : ℕ) (f : Q → D), f ∈ S → (fun ω => f ((q ^ j)⁻¹ * ω)) ∈ S := by
  intro j
  induction j with
  | zero => intro f hf; simpa using hf
  | succ j ih =>
    intro f hf
    have hstep : (fun ω => f ((q ^ (j + 1))⁻¹ * ω))
        = shiftHom q (fun ω => f ((q ^ j)⁻¹ * ω)) := by
      funext ω
      change f ((q ^ (j + 1))⁻¹ * ω) = f ((q ^ j)⁻¹ * (q⁻¹ * ω))
      congr 1
      rw [← mul_assoc, pow_succ]
      group
    rw [hstep]
    exact hS ⟨_, ih f hf, rfl⟩

/-- 部分和 `T_k f` は shift 安定な部分群に留まる. -/
theorem shiftSumHom_mem_of_shift_stable {S : Subgroup (Q → D)} {q : Q}
    (hS : S.map (shiftHom q) ≤ S) (k : ℕ) {f : Q → D} (hf : f ∈ S) :
    shiftSumHom q k f ∈ S := by
  have hprod : shiftSumHom q k f
      = ∏ j ∈ Finset.range k, (fun ω => f ((q ^ j)⁻¹ * ω)) := by
    funext ω
    rw [Finset.prod_apply]
    rfl
  rw [hprod]
  exact Subgroup.prod_mem _ fun j _ => shift_pow_mem_of_shift_stable hS j f hf

/-- **下降中心列の帰納段**: `S` が shift 安定なら `⁅S の像, ⊤⁆ = (Δ_q(S)) の像`.

`⊆` は `⁅inl f, y⁆ = inl (Δ_{y.right} f)` と `Δ_{q^k} = Δ_q ∘ T_k`, `T_k f ∈ S`,
`⊇` は `inl (Δ_q f) = ⁅inl f, inr q⁆`. -/
theorem commutator_map_inl_top_eq {q : Q} (hq : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k)
    {S : Subgroup (Q → D)} (hS : S.map (shiftHom q) ≤ S) :
    ⁅S.map (inl : (Q → D) →* D ≀[Q] Q), (⊤ : Subgroup (D ≀[Q] Q))⁆
      = (S.map (shiftSubHom q)).map inl := by
  refine le_antisymm (Subgroup.commutator_le.2 ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩ y -
    obtain ⟨k, hk⟩ := hq y.right
    rw [commutatorElement_inl_eq_shiftSubHom, hk, shiftSubHom_pow_eq_comp]
    exact ⟨shiftSubHom q (shiftSumHom q k f),
      ⟨shiftSumHom q k f, shiftSumHom_mem_of_shift_stable hS k hf, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [← commutatorElement_inl_inr_eq_shiftSubHom]
    exact Subgroup.commutator_mem_commutator ⟨f, hf, rfl⟩ (Subgroup.mem_top _)

/-- `Δ_q` と平行移動は可換 (群環では `(1-x)` と `x` の可換性). -/
theorem shiftSubHom_comp_shiftHom (q : Q) :
    (shiftSubHom (D := D) q).comp (shiftHom q) = (shiftHom q).comp (shiftSubHom q) := by
  ext f ω
  rfl

/-- `Δ_q` の反復で得られる部分群列 `Δ^i(⊤)`. -/
def shiftSubSeq (q : Q) : ℕ → Subgroup (Q → D)
  | 0 => ⊤
  | (i + 1) => (shiftSubSeq q i).map (shiftSubHom q)

@[simp]
theorem shiftSubSeq_zero (q : Q) : shiftSubSeq (D := D) q 0 = ⊤ := rfl

@[simp]
theorem shiftSubSeq_succ (q : Q) (i : ℕ) :
    shiftSubSeq (D := D) q (i + 1) = (shiftSubSeq q i).map (shiftSubHom q) := rfl

/-- 各 `Δ^i(⊤)` は shift 安定. -/
theorem shiftSubSeq_shift_stable (q : Q) (i : ℕ) :
    (shiftSubSeq (D := D) q i).map (shiftHom q) ≤ shiftSubSeq q i := by
  induction i with
  | zero => exact le_top
  | succ i ih =>
    rw [shiftSubSeq_succ, Subgroup.map_map, ← shiftSubHom_comp_shiftHom, ← Subgroup.map_map]
    exact Subgroup.map_mono ih

/-- **4A.8(d) の下降中心列**: `γ_{i+2}(P) = (Δ^{i+1}(A)) の像`
(mathlib の添字では `lowerCentralSeries ⊤ (i+1)`).

基底は 4A.8(b) (`P' = ⁅A, U⁆`), 帰納段は `commutator_map_inl_top_eq`. -/
theorem lowerCentralSeries_eq_map_shiftSubSeq {q : Q} (hq : ∀ q' : Q, ∃ k : ℕ, q' = q ^ k)
    (i : ℕ) :
    Subgroup.lowerCentralSeries (⊤ : Subgroup (D ≀[Q] Q)) (i + 1)
      = (shiftSubSeq (D := D) q (i + 1)).map inl := by
  have hQcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    obtain ⟨j, rfl⟩ := hq a
    obtain ⟨k, rfl⟩ := hq b
    exact (Commute.pow_pow (Commute.refl q) j k).eq
  induction i with
  | zero =>
    rw [Subgroup.top_lowerCentralSeries_one]
    have hcomm : commutator (D ≀[Q] Q)
        = ⁅(⊤ : Subgroup (Q → D)).map (inl : (Q → D) →* D ≀[Q] Q),
            (⊤ : Subgroup (D ≀[Q] Q))⁆ := by
      refine le_antisymm ?_ ?_
      · rw [commutator_eq_commutator_range_inl_range_inr hQcomm, ← MonoidHom.range_eq_map]
        exact Subgroup.commutator_mono le_rfl le_top
      · rw [_root_.commutator_def]
        exact Subgroup.commutator_mono le_top le_rfl
    rw [hcomm]
    exact commutator_map_inl_top_eq hq (le_top : (⊤ : Subgroup (Q → D)).map (shiftHom q) ≤ ⊤)
  | succ i ih =>
    rw [Subgroup.lowerCentralSeries_succ, ih]
    exact commutator_map_inl_top_eq hq (shiftSubSeq_shift_stable q (i + 1))

/-! ### 4A.8(d)(β) への準備: ノルム関係式 `N · (1 - x) = 0` -/

/-- `q` が `Q` 全体を生成するとき, 部分和 `T_{|Q|} f` は**定数関数** (座標積 = ノルム). -/
theorem shiftSumHom_card_eq_const [Fintype Q] {q : Q} (hq : orderOf q = Fintype.card Q)
    (f : Q → D) : shiftSumHom q (Fintype.card Q) f = Function.const Q (∏ y, f y) := by
  funext ω
  exact prod_range_card_eq_prod_univ hq f ω

/-- **ノルム関係式** `Δ_q ∘ T_{|Q|} = 1`: 群環の `(1-x)·N = 0`.

`T_{|Q|} f` は定数なので平行移動で不変, ゆえに `Δ_q` で消える. -/
theorem shiftSubHom_shiftSumHom_card [Fintype Q] {q : Q} (hq : orderOf q = Fintype.card Q)
    (f : Q → D) : shiftSubHom q (shiftSumHom q (Fintype.card Q) f) = 1 := by
  rw [shiftSumHom_card_eq_const hq]
  funext ω
  change (∏ y, f y) * ((∏ y, f y))⁻¹ = (1 : Q → D) ω
  rw [mul_inv_cancel]
  rfl

/-! ### 4A.8(d)(β) の linchpin (多項式版) -/

/-- **標数 `p` の多項式恒等式** `(1 - X)^{p-1} = 1 + X + ⋯ + X^{p-1}`.

`(1-X)^p = 1 - X^p` (`sub_pow_char`) と幾何級数 `(1-X)·∑_{j<p} X^j = 1 - X^p`
(`mul_neg_geom_sum`) を比べ, 整域 `(ZMod p)[X]` で `1 - X ≠ 0` を約す.

これが 4A.8(d) の linchpin `Δ_q^{p-1} = T_p` の多項式側の実体
(`Δ = 1 - x`, `T_p = 1 + x + ⋯ + x^{p-1}` を `x ↦ 平行移動` で作用させる). -/
theorem one_sub_X_pow_prime_sub_one (p : ℕ) [Fact p.Prime] :
    (1 - Polynomial.X : Polynomial (ZMod p)) ^ (p - 1)
      = ∑ j ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p)) ^ j := by
  have hp : 0 < p := Nat.Prime.pos Fact.out
  have h1 : (1 - Polynomial.X : Polynomial (ZMod p)) ^ p = 1 - Polynomial.X ^ p := by
    rw [sub_pow_char]
    simp
  have h2 : (1 - Polynomial.X : Polynomial (ZMod p))
      * (∑ j ∈ Finset.range p, (Polynomial.X : Polynomial (ZMod p)) ^ j)
      = 1 - Polynomial.X ^ p := mul_neg_geom_sum Polynomial.X p
  have hne : (1 - Polynomial.X : Polynomial (ZMod p)) ≠ 0 := by
    intro h
    have hcoef := congrArg (fun r => Polynomial.coeff r 1) h
    simp [Polynomial.coeff_one] at hcoef
  have hsplit : (1 - Polynomial.X : Polynomial (ZMod p)) ^ p
      = (1 - Polynomial.X) * (1 - Polynomial.X) ^ (p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hsplit, ← h2] at h1
  exact mul_left_cancel₀ hne h1

/-- **`(r-1).choose j ≡ (-1)^j (mod r)`** (`j < r`, `r` 素数).

mathlib に無いので自前で証明 (2026-07-25 に grep 済). Pascal
`r.choose (j+1) = (r-1).choose j + (r-1).choose (j+1)` と
`r ∣ r.choose (j+1)` (`Nat.Prime.dvd_choose_self`) から `j` の帰納で従う.

4A.8(d) の linchpin を pointwise 二項展開で示すときの係数計算に使う
(`Δ^{r-1}` の指数がすべて `1` になる理由). -/
theorem cast_choose_prime_sub_one (r : ℕ) (hr : Nat.Prime r) :
    ∀ j : ℕ, j < r → (((r - 1).choose j : ℕ) : ZMod r) = (-1) ^ j := by
  have hr1 : 1 ≤ r := hr.one_lt.le
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hjr : j < r := by omega
    have hpascal : r.choose (j + 1) = (r - 1).choose j + (r - 1).choose (j + 1) := by
      have hrs : r = (r - 1) + 1 := by omega
      rw [hrs, Nat.choose_succ_succ]
      congr 1
    have hdvd : r ∣ r.choose (j + 1) := Nat.Prime.dvd_choose_self hr (by omega) (by omega)
    have hzero : ((r.choose (j + 1) : ℕ) : ZMod r) = 0 := by
      obtain ⟨c, hc⟩ := hdvd
      rw [hc]
      push_cast
      simp
    rw [hpascal] at hzero
    push_cast at hzero
    rw [ih hjr] at hzero
    have hval : (((r - 1).choose (j + 1) : ℕ) : ZMod r) = -(-1) ^ j :=
      eq_neg_of_add_eq_zero_right hzero
    rw [hval, pow_succ]
    ring

omit [CommGroup D] [Group Q] in
/-- `n = 1` の場合の位数: `|C| = |Q| = p` なら `|C ≀ Q| = p^{p+1}`
(maximal class の判定 `class = p` と対になる). -/
theorem card_wreath_of_card_eq_prime [Finite Q] [Finite D] {r : ℕ}
    (hD : Nat.card D = r) (hQ : Nat.card Q = r) : Nat.card (D ≀[Q] Q) = r ^ (r + 1) := by
  rw [OddOrder.Isaacs.Ch03.WreathProduct.card (D := D) (Q := Q) (Ω := Q), hD, hQ, pow_succ]

end

end OddOrder.Isaacs.Ch04
