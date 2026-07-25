/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.ProblemsSemidihedral

/-!
# Isaacs Chapter 3 — Problems §3A (Split Extensions)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 3 "Split Extensions" の章末演習 §3A
(pp. 74-75)。半直積 (`SemidirectProduct`) を扱う。

3A.1 (semidihedral) と 3A.2 (一般化四元数群) は行数の都合で
[`ProblemsSemidihedral.lean`](ProblemsSemidihedral.lean) に分離した (本ファイルが import)。

方針は Ch.1/Ch.2 の `Problems.lean` と同じ (ラッパーは書かず実証明; 教科書番号は docstring)。
-/

namespace OddOrder.Isaacs.Ch03

section /- Problems 3A: Split extensions (pp. 74-75) -/

/-! ### Problem 3A.3 — 位数 pm の群 (正規 P 位数 p, G/P 巡回, Z(G)=1)

`p` 素数, `m ∣ p-1`, `m > 1`。`(ZMod p)ˣ` (巡回, 位数 p-1) の位数 m 元 `u` から自己同型
`σ = ×u` を作り、`G = Multiplicative (ZMod p) ⋊ ⟨σ⟩`。`|G| = p·m`、`P = inl 像` 正規 位数 p、
`G/P ≅ ⟨σ⟩` 巡回、`Z(G) = 1` (作用が忠実 + 非自明: 体で `u-1` 可逆)。 -/

/-- 単元 `u` による `Multiplicative (ZMod p)` の乗法的自己同型 `σ = ×u`。 -/
noncomputable def sigmaOf {p : ℕ} (u : (ZMod p)ˣ) : MulAut (Multiplicative (ZMod p)) :=
  (MulAutMultiplicative (ZMod p)).symm (AddAut.mulLeft u)

theorem sigmaOf_orderOf {p : ℕ} (u : (ZMod p)ˣ) : orderOf (sigmaOf u) = orderOf u := by
  have hinj : Function.Injective
      (AddAut.mulLeft : (ZMod p)ˣ →* Multiplicative (AddAut (ZMod p))) := by
    intro a b h
    have h2 : (↑a : ZMod p) * 1 = (↑b : ZMod p) * 1 :=
      DFunLike.congr_fun (congrArg Multiplicative.toAdd h) (1 : ZMod p)
    rw [mul_one, mul_one] at h2
    exact Units.ext h2
  calc orderOf (sigmaOf u)
      = orderOf (AddAut.mulLeft u) :=
        orderOf_injective (MulAutMultiplicative (ZMod p)).symm.toMonoidHom
          (MulAutMultiplicative (ZMod p)).symm.injective _
    _ = orderOf u := orderOf_injective AddAut.mulLeft hinj u

/-- `σ` の作用: `σ(x) = ↑u · toAdd x` (乗法的). -/
@[simp] theorem sigmaOf_apply {p : ℕ} (u : (ZMod p)ˣ) (x : Multiplicative (ZMod p)) :
    sigmaOf u x = Multiplicative.ofAdd ((↑u : ZMod p) * Multiplicative.toAdd x) := rfl

/-- 位数 pm の群 `G = Multiplicative (ZMod p) ⋊ ⟨σ⟩`。 -/
abbrev affineGroup {p : ℕ} (u : (ZMod p)ˣ) :=
  SemidirectProduct (Multiplicative (ZMod p)) (Subgroup.zpowers (sigmaOf u))
    (Subgroup.zpowers (sigmaOf u)).subtype

/-- **Isaacs Problem 3A.3** (位数). `|G| = p · orderOf u`。 -/
theorem affineGroup_card {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    Nat.card (affineGroup u) = p * orderOf u := by
  rw [affineGroup, SemidirectProduct.card, Nat.card_zpowers, sigmaOf_orderOf,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]

/-- **Isaacs Problem 3A.3** (存在). 位数 `pm` の群で、位数 `p` の正規部分群 `P` をもち、
`G/P` が巡回, `Z(G) = 1`。 -/
theorem exists_group_card_eq_center_trivial (p m : ℕ) [Fact p.Prime] (hm : m ∣ p - 1)
    (hm1 : 1 < m) : ∃ u : (ZMod p)ˣ, orderOf u = m := by
  haveI := ZMod.isCyclic_units_prime (Fact.out (p := p.Prime))
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hp2 := (Fact.out (p := p.Prime)).two_le
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
  have hng : orderOf g = p - 1 := by rw [hg, hcard]
  have hmle : m ≤ p - 1 := Nat.le_of_dvd (by omega) hm
  have hne : (p - 1) / m ≠ 0 := by have := Nat.div_pos hmle (by omega); omega
  have hdvd : (p - 1) / m ∣ orderOf g := by rw [hng]; exact Nat.div_dvd_of_dvd hm
  exact ⟨g ^ ((p - 1) / m), by
    rw [orderOf_pow_of_dvd hne hdvd, hng, Nat.div_div_self hm (by omega)]⟩

/-- **Isaacs Problem 3A.3** (P = ker rightHom の位数). `|P| = p`。P は正規 (`MonoidHom.normal_ker`)。 -/
theorem affineGroup_card_ker {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    Nat.card (SemidirectProduct.rightHom :
      affineGroup u →* Subgroup.zpowers (sigmaOf u)).ker = p := by
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom,
    ← Nat.card_congr (MonoidHom.ofInjective
      (SemidirectProduct.inl_injective
        (φ := (Subgroup.zpowers (sigmaOf u)).subtype))).toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]

/-- **Isaacs Problem 3A.3** (G/P 巡回). `G/ker rightHom ≅ ⟨σ⟩` (巡回)。 -/
theorem affineGroup_quotient_isCyclic {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    IsCyclic (affineGroup u ⧸
      (SemidirectProduct.rightHom : affineGroup u →* Subgroup.zpowers (sigmaOf u)).ker) := by
  have e := QuotientGroup.quotientKerEquivOfSurjective
    (SemidirectProduct.rightHom : affineGroup u →* Subgroup.zpowers (sigmaOf u))
    SemidirectProduct.rightHom_surjective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Isaacs Problem 3A.3** (中心自明). `u ≠ 1` (作用が非自明) なら `Z(G) = 1`。
中心元 `(a,h)`: `inl b` と可換 ⟹ `φ(h)=id` ⟹ `h=1`; `inr σ` と可換 ⟹ `a=σ(a)=×u(a)` ⟹
`(u-1)·toAdd a=0` ⟹ `toAdd a=0` (体 `ZMod p` で `u-1≠0` 可逆) ⟹ `a=1`。 -/
theorem affineGroup_center_eq_bot {p : ℕ} [Fact p.Prime] {u : (ZMod p)ˣ} (hu : u ≠ 1) :
    Subgroup.center (affineGroup u) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  have hright : g.right = 1 := by
    have key : (Subgroup.zpowers (sigmaOf u)).subtype g.right = 1 := by
      ext b
      simp only [MulAut.one_apply]
      have hb := congrArg SemidirectProduct.left (hg (SemidirectProduct.inl b))
      simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, map_one, MulAut.one_apply] at hb
      apply Multiplicative.toAdd.injective
      have hb2 := congrArg Multiplicative.toAdd hb
      rw [toAdd_mul, toAdd_mul] at hb2
      have hc : Multiplicative.toAdd g.left + Multiplicative.toAdd b
          = Multiplicative.toAdd g.left
            + Multiplicative.toAdd ((Subgroup.zpowers (sigmaOf u)).subtype g.right b) := by
        rw [add_comm (Multiplicative.toAdd g.left) (Multiplicative.toAdd b)]; exact hb2
      exact (add_left_cancel hc).symm
    exact (Subgroup.zpowers (sigmaOf u)).subtype_injective
      (key.trans (map_one (Subgroup.zpowers (sigmaOf u)).subtype).symm)
  have hleft : g.left = 1 := by
    have hb := congrArg SemidirectProduct.left (hg (SemidirectProduct.inr
      ⟨sigmaOf u, Subgroup.mem_zpowers _⟩))
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, map_one, mul_one, one_mul] at hb
    rw [show ((Subgroup.zpowers (sigmaOf u)).subtype ⟨sigmaOf u, Subgroup.mem_zpowers _⟩)
        = sigmaOf u from rfl, sigmaOf_apply] at hb
    have ht : Multiplicative.toAdd g.left = (↑u : ZMod p) * Multiplicative.toAdd g.left := by
      have h2 := congrArg Multiplicative.toAdd hb
      rw [toAdd_ofAdd] at h2
      exact h2.symm
    have hu0 : (↑u : ZMod p) - 1 ≠ 0 := by
      intro hcon
      apply hu
      rw [sub_eq_zero] at hcon
      exact Units.ext (hcon.trans Units.val_one.symm)
    have hzero : Multiplicative.toAdd g.left = 0 := by
      have hmul : ((↑u : ZMod p) - 1) * Multiplicative.toAdd g.left = 0 := by
        rw [sub_mul, one_mul, ← ht, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left hu0
    exact Multiplicative.toAdd.injective (by rw [hzero]; rfl)
  exact SemidirectProduct.ext (by rw [hleft, SemidirectProduct.one_left])
    (by rw [hright, SemidirectProduct.one_right])

/-- **Isaacs Problem 3A.3** (まとめ). `p` 素数, `m ∣ p-1`, `m > 1` のとき、位数 `pm` の群 `G` で、
位数 `p` の正規部分群 `P` をもち、`G/P` が巡回, `Z(G) = 1` となるものが存在する。 -/
theorem exists_group_card_eq_normal_cyclic_center_trivial (p m : ℕ) [Fact p.Prime]
    (hm : m ∣ p - 1) (hm1 : 1 < m) :
    ∃ u : (ZMod p)ˣ, Nat.card (affineGroup u) = p * m ∧
      Nat.card (SemidirectProduct.rightHom :
        affineGroup u →* Subgroup.zpowers (sigmaOf u)).ker = p ∧
      IsCyclic (affineGroup u ⧸
        (SemidirectProduct.rightHom : affineGroup u →* Subgroup.zpowers (sigmaOf u)).ker) ∧
      Subgroup.center (affineGroup u) = ⊥ := by
  obtain ⟨u, hu⟩ := exists_group_card_eq_center_trivial p m hm hm1
  have hune : u ≠ 1 := by
    intro h; rw [h, orderOf_one] at hu; omega
  exact ⟨u, by rw [affineGroup_card, hu], affineGroup_card_ker u,
    affineGroup_quotient_isCyclic u, affineGroup_center_eq_bot hune⟩

/-! ### Problem 3A.4 — 位数 `q(q-1)` の群 (正規基本アーベル位数 `q`, 位数 `p` の元は単一共役類)

Isaacs の hint どおり、位数 `q` の有限体 `F` の乗法群 `Fˣ` が加法群 `(F,+)` に自己同型として
作用する半直積 `G = Multiplicative F ⋊ Fˣ` を取る。`|G| = q(q-1)`、`ker rightHom` (= `inl` 像)
は位数 `q` の正規基本アーベル部分群、位数 `p` (= `char F`) の元は `inl x` (`x ≠ 0`) 全体で、
`Fˣ` が `F ∖ {0}` に推移的だからちょうど 1 つの共役類をなす。 -/

/-- 有限体 `F` の乗法群による `Multiplicative F` への作用 (加法群の自己同型として)。 -/
noncomputable def fieldMulAction (F : Type*) [Field F] : Fˣ →* MulAut (Multiplicative F) :=
  (MulAutMultiplicative F).symm.toMonoidHom.comp AddAut.mulLeft

@[simp] theorem fieldMulAction_apply {F : Type*} [Field F] (u : Fˣ) (x : Multiplicative F) :
    fieldMulAction F u x = Multiplicative.ofAdd ((↑u : F) * Multiplicative.toAdd x) := rfl

/-- 位数 `q(q-1)` の群 `G = Multiplicative F ⋊ Fˣ` (`F` は有限体)。 -/
abbrev affineGroupOfField (F : Type*) [Field F] :=
  SemidirectProduct (Multiplicative F) Fˣ (fieldMulAction F)

/-- 有限体の乗法群の位数は `q - 1`。 -/
theorem natCard_units_field (F : Type*) [Field F] [Finite F] :
    Nat.card Fˣ = Nat.card F - 1 := by
  classical
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]

/-- **Isaacs Problem 3A.4** (位数). `|G| = q(q-1)`。 -/
theorem affineGroupOfField_card (F : Type*) [Field F] [Finite F] :
    Nat.card (affineGroupOfField F) = Nat.card F * (Nat.card F - 1) := by
  rw [affineGroupOfField, SemidirectProduct.card,
    Nat.card_congr (Multiplicative.toAdd (α := F)), natCard_units_field]

/-- **Isaacs Problem 3A.4** (正規部分群の位数). `|ker rightHom| = q` (`ker` は正規)。 -/
theorem affineGroupOfField_card_ker (F : Type*) [Field F] :
    Nat.card (SemidirectProduct.rightHom : affineGroupOfField F →* Fˣ).ker
      = Nat.card F := by
  rw [← SemidirectProduct.range_inl_eq_ker_rightHom,
    ← Nat.card_congr (MonoidHom.ofInjective
      (SemidirectProduct.inl_injective (φ := fieldMulAction F))).toEquiv,
    Nat.card_congr (Multiplicative.toAdd (α := F))]

/-- `char F = p` なら `Multiplicative F` の元は `p` 乗して `1`。 -/
theorem multiplicative_pow_char_eq_one {F : Type*} [Field F] (p : ℕ) [CharP F p]
    (x : Multiplicative F) : x ^ p = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero F p, zero_mul]

/-- `ker rightHom` の元は `inl` の像。 -/
theorem eq_inl_of_mem_ker {F : Type*} [Field F] {g : affineGroupOfField F}
    (hg : g.right = 1) : g = SemidirectProduct.inl g.left := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  rw [hg, map_one, mul_one]

/-- **Isaacs Problem 3A.4** (基本アーベル). `ker rightHom` は基本アーベル `p`-群。 -/
theorem affineGroupOfField_ker_isElementaryAbelian (F : Type*) [Field F] (p : ℕ) [CharP F p] :
    ((SemidirectProduct.rightHom : affineGroupOfField F →* Fˣ).ker).IsElementaryAbelian p := by
  refine ⟨fun x y => Subtype.ext ?_, fun x => Subtype.ext ?_⟩
  · have hx : (x : affineGroupOfField F).right = 1 := x.2
    have hy : (y : affineGroupOfField F).right = 1 := y.2
    push_cast
    refine SemidirectProduct.ext ?_ ?_
    · simp only [SemidirectProduct.mul_left, hx, hy, map_one, MulAut.one_apply]
      exact mul_comm _ _
    · simp only [SemidirectProduct.mul_right, hx, hy, mul_one]
  · have hx : (x : affineGroupOfField F).right = 1 := x.2
    push_cast
    rw [eq_inl_of_mem_ker hx, ← map_pow, multiplicative_pow_char_eq_one p, map_one]

/-- 位数 `p^n` (`n ≥ 1`) の有限体では `p ∤ |Fˣ| = q - 1`。 -/
theorem not_dvd_natCard_units (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime]
    [CharP F p] : ¬ (p ∣ Nat.card Fˣ) := by
  classical
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hcard⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have hpn : p ∣ Nat.card F := hcard' ▸ dvd_pow_self p n.2.ne'
  have hge : 1 ≤ Nat.card F := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
  rw [natCard_units_field]
  intro hdvd
  have h1 : p ∣ Nat.card F - (Nat.card F - 1) := Nat.dvd_sub hpn hdvd
  rw [show Nat.card F - (Nat.card F - 1) = 1 from by omega] at h1
  exact (Fact.out (p := p.Prime)).one_lt.ne' (Nat.dvd_one.mp h1)

/-- **Isaacs Problem 3A.4** (位数 `p` の元の形). 位数 `p` の元の `right` 成分は `1`
(`orderOf right` は `p` と `q-1` を割るが両者は互いに素)。 -/
theorem affineGroupOfField_right_eq_one_of_orderOf (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] {g : affineGroupOfField F} (hg : orderOf g = p) :
    g.right = 1 := by
  have hdvd : orderOf g.right ∣ p := hg ▸ orderOf_map_dvd SemidirectProduct.rightHom g
  have hcard : orderOf g.right ∣ Nat.card Fˣ := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime (Fact.out (p := p.Prime))).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hcard) (not_dvd_natCard_units F p)

/-- `Fˣ` の推移性: `a, b ≠ 0` なら `inl (ofAdd a)` と `inl (ofAdd b)` は `inr (b/a)` で共役。 -/
theorem isConj_inl_of_ne_zero {F : Type*} [Field F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsConj (SemidirectProduct.inl (Multiplicative.ofAdd a) : affineGroupOfField F)
      (SemidirectProduct.inl (Multiplicative.ofAdd b)) := by
  refine isConj_iff.mpr ⟨SemidirectProduct.inr (Units.mk0 (b / a) (div_ne_zero hb ha)), ?_⟩
  rw [← map_inv SemidirectProduct.inr, ← SemidirectProduct.inl_aut]
  refine SemidirectProduct.inl_inj.mpr ?_
  apply Multiplicative.toAdd.injective
  simp only [fieldMulAction_apply, toAdd_ofAdd, Units.val_mk0]
  field_simp

/-- **Isaacs Problem 3A.4** (位数 `p` の元は単一共役類). `Fˣ` が `F ∖ {0}` に推移的なので、
位数 `p` の元 (= `inl x`, `x ≠ 0`) はすべて共役。 -/
theorem affineGroupOfField_isConj_of_orderOf_eq (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] {g h : affineGroupOfField F}
    (hg : orderOf g = p) (hh : orderOf h = p) : IsConj g h := by
  have hgl := eq_inl_of_mem_ker (affineGroupOfField_right_eq_one_of_orderOf F p hg)
  have hhl := eq_inl_of_mem_ker (affineGroupOfField_right_eq_one_of_orderOf F p hh)
  have hgne : Multiplicative.toAdd g.left ≠ 0 := by
    intro hz
    rw [hgl, show g.left = 1 from Multiplicative.toAdd.injective hz, map_one,
      orderOf_one] at hg
    exact (Fact.out (p := p.Prime)).one_lt.ne hg
  have hhne : Multiplicative.toAdd h.left ≠ 0 := by
    intro hz
    rw [hhl, show h.left = 1 from Multiplicative.toAdd.injective hz, map_one,
      orderOf_one] at hh
    exact (Fact.out (p := p.Prime)).one_lt.ne hh
  have key := isConj_inl_of_ne_zero (F := F) hgne hhne
  rwa [ofAdd_toAdd, ofAdd_toAdd, ← hgl, ← hhl] at key

/-- **Isaacs Problem 3A.4** (まとめ・存在). `q = p^k` (`k ≥ 1`) のとき、位数 `q(q-1)` の群 `G` で
位数 `q` の正規基本アーベル部分群をもち、`G` の位数 `p` の元がすべて共役なものが存在する。 -/
theorem exists_group_card_eq_elementaryAbelian_isConj (p k : ℕ) [Fact p.Prime] (hk : k ≠ 0) :
    Nat.card (affineGroupOfField (GaloisField p k)) = p ^ k * (p ^ k - 1) ∧
      Nat.card (SemidirectProduct.rightHom :
        affineGroupOfField (GaloisField p k) →* (GaloisField p k)ˣ).ker = p ^ k ∧
      ((SemidirectProduct.rightHom :
        affineGroupOfField (GaloisField p k) →* (GaloisField p k)ˣ).ker).IsElementaryAbelian p ∧
      ∀ g h : affineGroupOfField (GaloisField p k),
        orderOf g = p → orderOf h = p → IsConj g h := by
  have hcard : Nat.card (GaloisField p k) = p ^ k := GaloisField.card p k hk
  exact ⟨by rw [affineGroupOfField_card, hcard],
    by rw [affineGroupOfField_card_ker, hcard],
    affineGroupOfField_ker_isElementaryAbelian _ p,
    fun g h => affineGroupOfField_isConj_of_orderOf_eq _ p⟩

/-! ### Problem 3A.8 — 位数 `pqr` の巡回群の `Aut` にある Klein 四元群

巡回群 `C = ZMod n` の自己同型は単元倍。`n = s·m` (`gcd(s,m) = 1`) のとき「`s`-捩れを固定し
`m`-捩れを反転する」自己同型は、生成元での条件 `u·m = m`, `u·s = -s` と同値で、Bezout
`sA + mB = 1` から `u := -1 + 2·(mB)` として**明示的に構成**できる (CRT の一般論は不要)。 -/

/-- `n = d·m` のとき、`ZMod n` の `d`-捩れ (`d·x = 0`) はちょうど `m` の倍数全体。

`⟸` は `d·m = n ≡ 0`。`⟹` は `x.val` に降りて `n ∣ d·x.val`、`d` で割って `m ∣ x.val`。 -/
theorem mul_eq_zero_iff_exists_mul {n d m : ℕ} [NeZero n] (hn : d * m = n) (x : ZMod n) :
    (d : ZMod n) * x = 0 ↔ ∃ k : ZMod n, x = (m : ZMod n) * k := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exact absurd hn.symm (by rw [h0, zero_mul]; exact (NeZero.ne n))
    · exact h0
  constructor
  · intro h
    have hval : ((d * x.val : ℕ) : ZMod n) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
      exact h
    obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hval
    have hxval : x.val = m * c := by
      refine Nat.eq_of_mul_eq_mul_left hd0 ?_
      rw [hc, ← hn]; ring
    refine ⟨(c : ZMod n), ?_⟩
    have hcast : ((x.val : ℕ) : ZMod n) = ((m * c : ℕ) : ZMod n) := by rw [hxval]
    rwa [ZMod.natCast_val, ZMod.cast_id, Nat.cast_mul] at hcast
  · rintro ⟨k, rfl⟩
    rw [← mul_assoc, ← Nat.cast_mul, hn, ZMod.natCast_self, zero_mul]

/-- `gcd(a,b) = 1` なら `ZMod n` で `a·A + b·B = 1` をみたす `A, B` がある (Bezout の像)。 -/
theorem exists_bezout_zmod (n : ℕ) {a b : ℕ} (hab : Nat.Coprime a b) :
    ∃ A B : ZMod n, (a : ZMod n) * A + (b : ZMod n) * B = 1 := by
  refine ⟨((Nat.gcdA a b : ℤ) : ZMod n), ((Nat.gcdB a b : ℤ) : ZMod n), ?_⟩
  have hg := Nat.gcd_eq_gcd_ab a b
  rw [Nat.Coprime.gcd_eq_one hab] at hg
  have hcast : (((a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b : ℤ) : ZMod n)
      = ((1 : ℤ) : ZMod n) := by rw [← hg]; norm_cast
  push_cast at hcast
  linear_combination hcast

/-- **一意性 (Bezout のみ)**: `gcd(s,m) = 1` のとき、`m` を固定し `s` を反転する `ZMod n` の元は
高々 1 つ (`u - u'` が `m` と `s` の両方を消すので `1 = sA + mB` を掛けて `0`)。 -/
theorem eq_of_fixes_inverts {n s m : ℕ} (hcop : Nat.Coprime s m) {u u' : ZMod n}
    (hu : u * (m : ZMod n) = (m : ZMod n) ∧ u * (s : ZMod n) = -(s : ZMod n))
    (hu' : u' * (m : ZMod n) = (m : ZMod n) ∧ u' * (s : ZMod n) = -(s : ZMod n)) : u = u' := by
  obtain ⟨A, B, hAB⟩ := exists_bezout_zmod n hcop
  have hd : (u - u') * (m : ZMod n) = 0 := by rw [sub_mul, hu.1, hu'.1, sub_self]
  have hd2 : (u - u') * (s : ZMod n) = 0 := by rw [sub_mul, hu.2, hu'.2, sub_self]
  refine sub_eq_zero.mp ?_
  calc u - u' = (u - u') * ((s : ZMod n) * A + (m : ZMod n) * B) := by rw [hAB, mul_one]
    _ = 0 := by rw [mul_add, ← mul_assoc, ← mul_assoc, hd, hd2]; ring

/-- `s` を反転する元は `s` の倍数も反転する。 -/
theorem inverts_mul {n : ℕ} {u : ZMod n} {s : ℕ} (h : u * (s : ZMod n) = -(s : ZMod n))
    (k : ℕ) : u * ((s * k : ℕ) : ZMod n) = -((s * k : ℕ) : ZMod n) := by
  push_cast
  rw [← mul_assoc, h]; ring

/-- `s` を固定する元は `s` の倍数も固定する。 -/
theorem fixes_mul {n : ℕ} {u : ZMod n} {s : ℕ} (h : u * (s : ZMod n) = (s : ZMod n))
    (k : ℕ) : u * ((s * k : ℕ) : ZMod n) = ((s * k : ℕ) : ZMod n) := by
  push_cast
  rw [← mul_assoc, h]

/-- `gcd(a,b) = 1` で `u` が `a·c` と `b·c` をともに反転すれば `c` も反転する。 -/
theorem inverts_of_inverts_coprime {n : ℕ} {u : ZMod n} {a b c : ℕ} (hab : Nat.Coprime a b)
    (ha : u * ((a * c : ℕ) : ZMod n) = -((a * c : ℕ) : ZMod n))
    (hb : u * ((b * c : ℕ) : ZMod n) = -((b * c : ℕ) : ZMod n)) :
    u * (c : ZMod n) = -(c : ZMod n) := by
  obtain ⟨A, B, hAB⟩ := exists_bezout_zmod n hab
  have hc : (c : ZMod n) = ((a * c : ℕ) : ZMod n) * A + ((b * c : ℕ) : ZMod n) * B := by
    push_cast
    linear_combination (c : ZMod n) * hAB.symm
  rw [hc, mul_add, ← mul_assoc, ← mul_assoc, ha, hb]
  ring

/-- `gcd(a,b) = 1` で `u` が `a·c` を固定し `b·c` を反転すれば… は使わないが、対称形として
`a·c` と `b·c` をともに固定すれば `c` も固定する。 -/
theorem fixes_of_fixes_coprime {n : ℕ} {u : ZMod n} {a b c : ℕ} (hab : Nat.Coprime a b)
    (ha : u * ((a * c : ℕ) : ZMod n) = ((a * c : ℕ) : ZMod n))
    (hb : u * ((b * c : ℕ) : ZMod n) = ((b * c : ℕ) : ZMod n)) :
    u * (c : ZMod n) = (c : ZMod n) := by
  obtain ⟨A, B, hAB⟩ := exists_bezout_zmod n hab
  have hc : (c : ZMod n) = ((a * c : ℕ) : ZMod n) * A + ((b * c : ℕ) : ZMod n) * B := by
    push_cast
    linear_combination (c : ZMod n) * hAB.symm
  rw [hc, mul_add, ← mul_assoc, ← mul_assoc, ha, hb]

/-- **Isaacs Problem 3A.8(a)** の核. `n = s·m` (`gcd(s,m) = 1`, `n` 奇数, `1 < m`) のとき、
`ZMod n` に「`s`-捩れの生成元 `m` を固定し `m`-捩れの生成元 `s` を反転する」元 `u` が
**ちょうど 1 つ**存在する。さらに `u·u = 1` かつ `u ≠ 1` (すなわち `Aut(C)` の involution)。

構成: Bezout `sA + mB = 1` に対し `e := mB` は `m ∣ e`, `s ∣ e - 1` をみたし (`e² = e`)、
`u := -1 + 2e` が条件をみたす。一意性は `(u - u')·m = 0 = (u - u')·s` と
`u - u' = (u-u')(sA + mB) = 0` から。 -/
theorem exists_unique_fixes_inverts {n s m : ℕ} [NeZero n] (hn : s * m = n) (hm : 1 < m)
    (hcop : Nat.Coprime s m) (hodd : ¬ (2 ∣ n)) :
    ∃! u : ZMod n, (u * (m : ZMod n) = (m : ZMod n) ∧ u * (s : ZMod n) = -(s : ZMod n)) ∧
      u * u = 1 ∧ u ≠ 1 := by
  obtain ⟨A, B, hAB⟩ : ∃ A B : ℤ, (s : ℤ) * A + (m : ℤ) * B = 1 := by
    refine ⟨Nat.gcdA s m, Nat.gcdB s m, ?_⟩
    have hg := Nat.gcd_eq_gcd_ab s m
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    exact_mod_cast hg.symm
  -- `e := mB` (整数) の像
  set E : ℤ := (m : ℤ) * B with hE
  set e : ZMod n := (E : ZMod n) with he
  have hnZ : ((n : ℤ)) = (s : ℤ) * (m : ℤ) := by exact_mod_cast hn.symm
  -- `e·m = m`, `e·s = 0`, `e² = e`
  have hem : e * (m : ZMod n) = (m : ZMod n) := by
    have : ((E * m - m : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨-A, ?_⟩
      have : E * (m : ℤ) - (m : ℤ) = (m : ℤ) * (E - 1) := by ring
      rw [this, show E - 1 = -((s : ℤ) * A) from by rw [hE]; linarith [hAB], hnZ]
      ring
    have h2 : (E : ZMod n) * ((m : ℤ) : ZMod n) - ((m : ℤ) : ZMod n) = 0 := by
      push_cast at this ⊢; linear_combination this
    push_cast at h2
    rw [he]; linear_combination h2
  have hes : e * (s : ZMod n) = 0 := by
    have : ((E * s : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ⟨B, by rw [hE, hnZ]; ring⟩
    push_cast at this
    rw [he]; linear_combination this
  have hee : e * e = e := by
    have : ((E * E - E : ℤ) : ZMod n) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      refine ⟨-(A * B), ?_⟩
      have : E * E - E = E * (E - 1) := by ring
      rw [this, show E - 1 = -((s : ℤ) * A) from by rw [hE]; linarith [hAB], hE, hnZ]
      ring
    push_cast at this
    rw [he]; linear_combination this
  refine ⟨-1 + 2 * e, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [add_mul, neg_one_mul, mul_assoc, hem]; ring
  · rw [add_mul, neg_one_mul, mul_assoc, hes]; ring
  · have : (-1 + 2 * e) * (-1 + 2 * e) = 1 - 4 * e + 4 * (e * e) := by ring
    rw [this, hee]; ring
  · intro hcon
    -- `u = 1` ⟹ `n ∣ 2sA` ⟹ `m ∣ 2A`、Bezout と合わせて `m ∣ 2`、`m` 奇で `1 < m` に矛盾
    have h1 : ((2 * (s : ℤ) * A : ℤ) : ZMod n) = 0 := by
      have he1 : e - 1 = ((-((s : ℤ) * A) : ℤ) : ZMod n) := by
        rw [he, ← Int.cast_one, ← Int.cast_sub]
        congr 1
        rw [hE]; linarith [hAB]
      have h2 : (2 : ZMod n) * (e - 1) = 0 := by linear_combination hcon
      rw [he1] at h2
      push_cast at h2 ⊢
      linear_combination -h2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hnZ] at h1
    have hs0 : (0 : ℤ) < (s : ℤ) := by
      rcases Nat.eq_zero_or_pos s with h0 | h0
      · exact absurd hn.symm (by rw [h0, zero_mul]; exact (NeZero.ne n))
      · exact_mod_cast h0
    have hm2A : (m : ℤ) ∣ 2 * A := by
      obtain ⟨c, hc⟩ := h1
      refine ⟨c, ?_⟩
      refine mul_left_cancel₀ (ne_of_gt hs0) ?_
      linarith [hc]
    obtain ⟨c, hc⟩ := hm2A
    have hm2 : (m : ℤ) ∣ 2 := ⟨(s : ℤ) * c + 2 * B, by linear_combination (s : ℤ) * hc - 2 * hAB⟩
    have hmodd : ¬ (2 ∣ m) := fun ⟨c', hc'⟩ => hodd ⟨s * c', by rw [← hn, hc']; ring⟩
    have hmle : m ≤ 2 := by exact_mod_cast Int.le_of_dvd two_pos hm2
    exact hmodd (by omega)
  · rintro y ⟨⟨hy1, hy2⟩, -, -⟩
    have hd : (y - (-1 + 2 * e)) * (m : ZMod n) = 0 := by
      rw [sub_mul, hy1]
      rw [add_mul, neg_one_mul, mul_assoc, hem]
      ring
    have hd2 : (y - (-1 + 2 * e)) * (s : ZMod n) = 0 := by
      rw [sub_mul, hy2]
      rw [add_mul, neg_one_mul, mul_assoc, hes]
      ring
    have hone : ((s : ZMod n)) * ((A : ℤ) : ZMod n) + ((m : ZMod n)) * ((B : ℤ) : ZMod n)
        = 1 := by
      have : (((s : ℤ) * A + (m : ℤ) * B : ℤ) : ZMod n) = ((1 : ℤ) : ZMod n) := by rw [hAB]
      push_cast at this
      linear_combination this
    have := sub_eq_zero.mp (by
      calc y - (-1 + 2 * e)
          = (y - (-1 + 2 * e)) * (((s : ZMod n)) * ((A : ℤ) : ZMod n)
              + ((m : ZMod n)) * ((B : ℤ) : ZMod n)) := by rw [hone, mul_one]
        _ = 0 := by
            rw [mul_add, ← mul_assoc, ← mul_assoc, hd, hd2]; ring)
    exact this

/-- **Isaacs Problem 3A.8(b)** の核. `n = p·q·r` (互いに素) で、`u_p` (「`p`-捩れの生成元 `qr`
を固定し `p` を反転する」)、`u_q`、`u_r` を (a) の一意な元とすると `u_p · u_q = u_r`。

`u_p u_q` が `u_r` の 2 条件をみたすことを確かめ、一意性 (`eq_of_fixes_inverts`) で結論:
- `(u_p u_q)·(pq) = u_p·(-(pq)) = pq` (`u_q` は `q` を、`u_p` は `p` を反転するから両者とも
  `pq` を反転する)。
- `(u_p u_q)·(qr) = -(qr)` (`u_q` が反転、`u_p` が固定) かつ `(u_p u_q)·(pr) = -(pr)`
  (`u_q` が固定、`u_p` が反転) なので、`gcd(q,p) = 1` より `(u_p u_q)·r = -r`
  (`inverts_of_inverts_coprime`)。

これと `u_p² = u_q² = u_r² = 1` から `{1, u_p, u_q, u_r}` は位数 4 の部分群 (Klein 四元群)。 -/
theorem mul_eq_of_fixes_inverts_pqr {p q r : ℕ} (hpq : Nat.Coprime p q) (hpr : Nat.Coprime p r)
    (hqr : Nat.Coprime q r) {up uq ur : ZMod (p * q * r)}
    (hup : up * ((q * r : ℕ) : ZMod (p * q * r)) = ((q * r : ℕ) : ZMod (p * q * r)) ∧
      up * (p : ZMod (p * q * r)) = -(p : ZMod (p * q * r)))
    (huq : uq * ((p * r : ℕ) : ZMod (p * q * r)) = ((p * r : ℕ) : ZMod (p * q * r)) ∧
      uq * (q : ZMod (p * q * r)) = -(q : ZMod (p * q * r)))
    (hur : ur * ((p * q : ℕ) : ZMod (p * q * r)) = ((p * q : ℕ) : ZMod (p * q * r)) ∧
      ur * (r : ZMod (p * q * r)) = -(r : ZMod (p * q * r))) :
    up * uq = ur := by
  refine eq_of_fixes_inverts (s := r) (m := p * q)
    (Nat.Coprime.mul_right hpr.symm hqr.symm) ⟨?_, ?_⟩ hur
  · have h1 : uq * ((p * q : ℕ) : ZMod (p * q * r)) = -((p * q : ℕ) : ZMod (p * q * r)) := by
      have h := inverts_mul huq.2 p
      rwa [Nat.mul_comm q p] at h
    have h2 : up * ((p * q : ℕ) : ZMod (p * q * r)) = -((p * q : ℕ) : ZMod (p * q * r)) :=
      inverts_mul hup.2 q
    rw [mul_assoc up uq, h1, mul_neg, h2, neg_neg]
  · refine inverts_of_inverts_coprime (a := q) (b := p) (c := r) hpq.symm ?_ ?_
    · have h1 : uq * ((q * r : ℕ) : ZMod (p * q * r)) = -((q * r : ℕ) : ZMod (p * q * r)) :=
        inverts_mul huq.2 r
      rw [mul_assoc up uq, h1, mul_neg, hup.1]
    · have h2 : up * ((p * r : ℕ) : ZMod (p * q * r)) = -((p * r : ℕ) : ZMod (p * q * r)) :=
        inverts_mul hup.2 r
      rw [mul_assoc up uq, huq.1, h2]

/-- **Isaacs Problem 3A.8(a)** (捩れ表現). `n = s·m` (`gcd(s,m) = 1`) で `u` が生成元条件
`u·m = m`, `u·s = -s` をみたすことは、「`s`-捩れの元をすべて固定し `m`-捩れの元をすべて
反転する」ことと同値 (`mul_eq_zero_iff_exists_mul` で捩れ = 生成元の倍数)。 -/
theorem fixes_inverts_iff_torsion {n s m : ℕ} [NeZero n] (hn : s * m = n) {u : ZMod n} :
    (u * (m : ZMod n) = (m : ZMod n) ∧ u * (s : ZMod n) = -(s : ZMod n)) ↔
      ((∀ x : ZMod n, (s : ZMod n) * x = 0 → u * x = x) ∧
        ∀ x : ZMod n, (m : ZMod n) * x = 0 → u * x = -x) := by
  have hn' : m * s = n := by rw [← hn]; ring
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨k, rfl⟩ := (mul_eq_zero_iff_exists_mul hn x).mp hx
      rw [← mul_assoc, h1]
    · obtain ⟨k, rfl⟩ := (mul_eq_zero_iff_exists_mul hn' x).mp hx
      rw [← mul_assoc, h2]; ring
  · rintro ⟨h1, h2⟩
    refine ⟨h1 _ ?_, h2 _ ?_⟩
    · rw [← Nat.cast_mul, hn, ZMod.natCast_self]
    · rw [← Nat.cast_mul, hn', ZMod.natCast_self]

/-- **Isaacs Problem 3A.8(a)(b)** (まとめ). `p, q, r` を相異なる奇素数とし
`C = ZMod (p·q·r)` (位数 `pqr` の巡回群) とすると、`Aut(C)` (= 単元倍) の中に
「1 つの素数捩れを固定し他 2 つを反転する」involution `u_p, u_q, u_r` がそれぞれ**一意に**
存在し、`u_p·u_q = u_r`, `u_q·u_r = u_p`, `u_r·u_p = u_q` をみたす。
したがって `{1, u_p, u_q, u_r}` は `Aut(C)` の位数 4 の部分群 (Klein 四元群)。

捩れ表現との対応は `fixes_inverts_iff_torsion` (生成元条件 ⟺ 捩れ全体での固定/反転)。 -/
theorem exists_klein_four_pqr {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hr2 : r ≠ 2) :
    ∃ up uq ur : ZMod (p * q * r),
      (up * ((q * r : ℕ) : ZMod (p * q * r)) = ((q * r : ℕ) : ZMod (p * q * r)) ∧
        up * (p : ZMod (p * q * r)) = -(p : ZMod (p * q * r))) ∧
      (uq * ((p * r : ℕ) : ZMod (p * q * r)) = ((p * r : ℕ) : ZMod (p * q * r)) ∧
        uq * (q : ZMod (p * q * r)) = -(q : ZMod (p * q * r))) ∧
      (ur * ((p * q : ℕ) : ZMod (p * q * r)) = ((p * q : ℕ) : ZMod (p * q * r)) ∧
        ur * (r : ZMod (p * q * r)) = -(r : ZMod (p * q * r))) ∧
      (up * up = 1 ∧ uq * uq = 1 ∧ ur * ur = 1) ∧
      (up ≠ 1 ∧ uq ≠ 1 ∧ ur ≠ 1) ∧
      (up * uq = ur ∧ uq * ur = up ∧ ur * up = uq) := by
  haveI : NeZero (p * q * r) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero hp.pos.ne' hq.pos.ne') hr.pos.ne'⟩
  -- 互いに素性
  have cpq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have cpr : Nat.Coprime p r := (Nat.coprime_primes hp hr).mpr hpr
  have cqr : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr hqr
  -- `n` は奇数
  have hodd : ¬ (2 ∣ p * q * r) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h' | h'
    · rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h' with h'' | h''
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h'').symm
      · exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h'').symm
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hr).mp h').symm
  have hlt : ∀ a b : ℕ, a.Prime → b.Prime → 1 < a * b := fun a b ha hb =>
    lt_of_lt_of_le (by norm_num) (Nat.mul_le_mul ha.two_le hb.two_le)
  -- 3 回の instantiation
  obtain ⟨up, hup, -⟩ := exists_unique_fixes_inverts (n := p * q * r) (s := p) (m := q * r)
    (by ring) (hlt q r hq hr) (cpq.mul_right cpr) hodd
  obtain ⟨uq, huq, -⟩ := exists_unique_fixes_inverts (n := p * q * r) (s := q) (m := p * r)
    (by ring) (hlt p r hp hr) (cpq.symm.mul_right cqr) hodd
  obtain ⟨ur, hur, -⟩ := exists_unique_fixes_inverts (n := p * q * r) (s := r) (m := p * q)
    (by ring) (hlt p q hp hq) (cpr.symm.mul_right cqr.symm) hodd
  -- Klein 四元群の関係式
  have hkey : up * uq = ur :=
    mul_eq_of_fixes_inverts_pqr cpq cpr cqr hup.1 huq.1 hur.1
  refine ⟨up, uq, ur, hup.1, huq.1, hur.1, ⟨hup.2.1, huq.2.1, hur.2.1⟩,
    ⟨hup.2.2, huq.2.2, hur.2.2⟩, hkey, ?_, ?_⟩
  · calc uq * ur = uq * (up * uq) := by rw [hkey]
      _ = up * (uq * uq) := by ring
      _ = up := by rw [huq.2.1, mul_one]
  · calc ur * up = (up * uq) * up := by rw [hkey]
      _ = (up * up) * uq := by ring
      _ = uq := by rw [hup.2.1, one_mul]

/-! ### Problem 3A.8(c) — `C ⋊ K` で `⟨α⟩` は regular orbit をもたない

`K ≤ (ZMod n)ˣ` が乗法で `C = Multiplicative (ZMod n)` に作用する半直積 `G = C ⋊ K` で、
`C` の生成元 `c = inl (ofAdd 1)` が誘導する内部自己同型 `α = conj c` は

    α^j ⟨x, k⟩ = ⟨x + j·(1 - k), k⟩

と作用する。したがって `α^j` が `⟨x,k⟩` を固定 ⟺ `j·(1-k) = 0`。 -/

/-- `(ZMod n)ˣ` の `Multiplicative (ZMod n)` への乗法作用 (加法群の自己同型として)。 -/
noncomputable def zmodUnitsAction (n : ℕ) : (ZMod n)ˣ →* MulAut (Multiplicative (ZMod n)) :=
  (MulAutMultiplicative (ZMod n)).symm.toMonoidHom.comp AddAut.mulLeft

@[simp] theorem zmodUnitsAction_apply {n : ℕ} (u : (ZMod n)ˣ) (x : Multiplicative (ZMod n)) :
    zmodUnitsAction n u x = Multiplicative.ofAdd ((↑u : ZMod n) * Multiplicative.toAdd x) := rfl

/-- `G = Multiplicative (ZMod n) ⋊ K` (`K ≤ (ZMod n)ˣ` が乗法で作用)。 -/
abbrev zmodSemidirect (n : ℕ) (K : Subgroup (ZMod n)ˣ) :=
  SemidirectProduct (Multiplicative (ZMod n)) K ((zmodUnitsAction n).comp K.subtype)

/-- `inl (ofAdd t)` による共役の作用: `⟨x, k⟩ ↦ ⟨x + t·(1 - k), k⟩`。 -/
theorem conj_inl_apply {n : ℕ} {K : Subgroup (ZMod n)ˣ} (t : ZMod n)
    (g : zmodSemidirect n K) :
    (MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd t) : zmodSemidirect n K)) g
      = ⟨Multiplicative.ofAdd (Multiplicative.toAdd g.left
          + t * (1 - (↑(g.right : (ZMod n)ˣ) : ZMod n))), g.right⟩ := by
  refine SemidirectProduct.ext ?_ ?_
  · apply Multiplicative.toAdd.injective
    simp only [MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.mul_right,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, SemidirectProduct.inv_left,
      map_one, MulAut.one_apply, one_mul, inv_one,
      zmodUnitsAction_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      toAdd_mul, toAdd_ofAdd, toAdd_inv]
    ring
  · simp [MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]

/-- `c := inl (ofAdd 1)` の `j` 乗は `inl (ofAdd j)`。 -/
theorem inl_ofAdd_one_pow {n : ℕ} {K : Subgroup (ZMod n)ˣ} (j : ℕ) :
    (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod n)) : zmodSemidirect n K) ^ j
      = SemidirectProduct.inl (Multiplicative.ofAdd (j : ZMod n)) := by
  rw [← map_pow]
  congr 1
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, nsmul_eq_mul, mul_one]

/-- **3A.8(c) の鍵**: `α = conj (inl (ofAdd 1))` の `j` 乗が `⟨x, k⟩` を固定するのは
`j·(1-k) = 0` のとき、かつそのときに限る。 -/
theorem conj_pow_fixes_iff {n : ℕ} {K : Subgroup (ZMod n)ˣ} (j : ℕ)
    (g : zmodSemidirect n K) :
    ((MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod n))
      : zmodSemidirect n K)) ^ j) g = g ↔
      (j : ZMod n) * (1 - (↑(g.right : (ZMod n)ˣ) : ZMod n)) = 0 := by
  rw [← map_pow, inl_ofAdd_one_pow, conj_inl_apply]
  constructor
  · intro h
    have hl := congrArg (Multiplicative.toAdd ∘ SemidirectProduct.left) h
    simp only [Function.comp_apply, toAdd_ofAdd] at hl
    linear_combination hl
  · intro h
    refine SemidirectProduct.ext ?_ rfl
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    linear_combination h

/-- 3 つの involution `up, uq, ur` (Klein 関係式つき) が張る `(ZMod n)ˣ` の位数 4 の部分群。 -/
def kleinSubgroup {n : ℕ} (up uq ur : (ZMod n)ˣ)
    (hpp : up * up = 1) (hqq : uq * uq = 1) (hrr : ur * ur = 1)
    (hpq : up * uq = ur) : Subgroup (ZMod n)ˣ where
  carrier := {1, up, uq, ur}
  one_mem' := by simp
  mul_mem' := by
    have hpr : up * ur = uq := by rw [← hpq, ← mul_assoc, hpp, one_mul]
    have hqr : uq * ur = up := by rw [← hpq, mul_comm up uq, ← mul_assoc, hqq, one_mul]
    have hqp : uq * up = ur := by rw [mul_comm]; exact hpq
    have hrp : ur * up = uq := by rw [mul_comm]; exact hpr
    have hrq : ur * uq = up := by rw [mul_comm]; exact hqr
    intro a b ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
    rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;>
      rw [ha, hb] <;>
      simp only [one_mul, mul_one, hpp, hqq, hrr, hpq, hpr, hqr, hqp, hrp, hrq] <;> tauto
  inv_mem' := by
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ⊢
    rcases ha with ha | ha | ha | ha <;> rw [ha] <;>
      simp only [inv_one, inv_eq_of_mul_eq_one_left hpp, inv_eq_of_mul_eq_one_left hqq,
        inv_eq_of_mul_eq_one_left hrr] <;> tauto

@[simp] theorem mem_kleinSubgroup {n : ℕ} {up uq ur : (ZMod n)ˣ} {hpp hqq hrr hpq}
    {k : (ZMod n)ˣ} :
    k ∈ kleinSubgroup up uq ur hpp hqq hrr hpq ↔ k = 1 ∨ k = up ∨ k = uq ∨ k = ur := Iff.rfl

/-- `n = a·b` で `a` が奇素数なら `2·b ≠ 0` in `ZMod n` (`a ∣ 2` が偽だから)。 -/
theorem two_mul_ne_zero_of_odd_prime_factor {n a b : ℕ} (hab : a * b = n) (ha : a.Prime)
    (ha2 : a ≠ 2) (hb : b ≠ 0) : (2 : ZMod n) * ((b : ℕ) : ZMod n) ≠ 0 := by
  intro h
  have hcast : ((2 * b : ℕ) : ZMod n) = 0 := by rw [Nat.cast_mul, Nat.cast_ofNat]; exact h
  obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have h2 : 2 = a * c := by
    refine Nat.eq_of_mul_eq_mul_right hbpos ?_
    calc 2 * b = n * c := hc
      _ = a * c * b := by rw [← hab]; ring
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two a ⟨c, h2⟩ with h' | h'
  · exact ha.one_lt.ne' h'
  · exact ha2 h'

/-- `α^j ≠ 1` の判定: ある `k ∈ K` で `j·(1-k) ≠ 0` なら `α^j ≠ 1`。 -/
theorem conj_pow_ne_one {n : ℕ} {K : Subgroup (ZMod n)ˣ} (j : ℕ) (k : K)
    (h : (j : ZMod n) * (1 - (↑(k : (ZMod n)ˣ) : ZMod n)) ≠ 0) :
    ((MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod n))
      : zmodSemidirect n K)) ^ j) ≠ 1 := fun hcon =>
  h ((conj_pow_fixes_iff j ⟨1, k⟩).mp (by rw [hcon]; rfl))

/-- **Isaacs Problem 3A.8(c)**. `p, q, r` を相異なる奇素数、`C = ZMod (pqr)`、`K` を (b) の
Klein 四元群、`G = C ⋊ K` とし、`α` を `C` の生成元 `c = inl (ofAdd 1)` が誘導する内部自己同型
とすると、**`⟨α⟩` は `G` 上に regular orbit をもたない**: どの `g ∈ G` にも `g` を固定する
非自明な `α^j` が存在する。

`conj_pow_fixes_iff` で `α^j` が `⟨x,k⟩` を固定 ⟺ `j·(1-k) = 0` なので、`k` の 4 通りで
`j` を選べばよい: `k = 1` なら `j = 1` (非自明性は `u_p ≠ 1`)、`k = u_p` なら `j = qr`
(`u_p·(qr) = qr` から固定、非自明性は `qr·(1-u_q) = 2qr ≠ 0`)、`k = u_q` なら `j = pr`、
`k = u_r` なら `j = pq`。 -/
theorem no_regular_orbit_klein {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hr2 : r ≠ 2)
    {up uq ur : (ZMod (p * q * r))ˣ}
    (hpp : up * up = 1) (hqq : uq * uq = 1) (hrr : ur * ur = 1) (hpq : up * uq = ur)
    (hupfix : (↑up : ZMod (p * q * r)) * ((q * r : ℕ) : ZMod (p * q * r))
      = ((q * r : ℕ) : ZMod (p * q * r)))
    (huqfix : (↑uq : ZMod (p * q * r)) * ((p * r : ℕ) : ZMod (p * q * r))
      = ((p * r : ℕ) : ZMod (p * q * r)))
    (hurfix : (↑ur : ZMod (p * q * r)) * ((p * q : ℕ) : ZMod (p * q * r))
      = ((p * q : ℕ) : ZMod (p * q * r)))
    (hupinv : (↑up : ZMod (p * q * r)) * (p : ZMod (p * q * r)) = -(p : ZMod (p * q * r)))
    (huqinv : (↑uq : ZMod (p * q * r)) * (q : ZMod (p * q * r)) = -(q : ZMod (p * q * r)))
    (hup1 : (↑up : ZMod (p * q * r)) ≠ 1)
    (g : zmodSemidirect (p * q * r) (kleinSubgroup up uq ur hpp hqq hrr hpq)) :
    ∃ j : ℕ,
      ((MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod (p * q * r)))
        : zmodSemidirect (p * q * r) (kleinSubgroup up uq ur hpp hqq hrr hpq))) ^ j) g = g ∧
      ((MulAut.conj (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod (p * q * r)))
        : zmodSemidirect (p * q * r) (kleinSubgroup up uq ur hpp hqq hrr hpq))) ^ j) ≠ 1 := by
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hr0 : r ≠ 0 := hr.pos.ne'
  have hp0 : p ≠ 0 := hp.pos.ne'
  -- `u` が `s` を反転すれば `s` の倍数も反転する (値レベル)
  have hup_pq : (↑up : ZMod (p * q * r)) * ((p * q : ℕ) : ZMod (p * q * r))
      = -((p * q : ℕ) : ZMod (p * q * r)) := inverts_mul hupinv q
  have hup_pr : (↑up : ZMod (p * q * r)) * ((p * r : ℕ) : ZMod (p * q * r))
      = -((p * r : ℕ) : ZMod (p * q * r)) := inverts_mul hupinv r
  have huq_qr : (↑uq : ZMod (p * q * r)) * ((q * r : ℕ) : ZMod (p * q * r))
      = -((q * r : ℕ) : ZMod (p * q * r)) := inverts_mul huqinv r
  -- 各 `k` で `j` を選ぶ
  rcases (mem_kleinSubgroup (up := up) (uq := uq) (ur := ur)).mp g.right.2 with hk | hk | hk | hk
  · refine ⟨1, (conj_pow_fixes_iff 1 g).mpr ?_, conj_pow_ne_one 1 ⟨up, by simp⟩ ?_⟩
    · rw [hk]; simp
    · simpa using sub_ne_zero.mpr (Ne.symm hup1)
  · refine ⟨q * r, (conj_pow_fixes_iff (q * r) g).mpr ?_,
      conj_pow_ne_one (q * r) ⟨uq, by simp⟩ ?_⟩
    · rw [hk, Nat.cast_mul, ← Nat.cast_mul]
      linear_combination -hupfix
    · have hval : ((q * r : ℕ) : ZMod (p * q * r)) * (1 - (↑uq : ZMod (p * q * r)))
          = 2 * ((q * r : ℕ) : ZMod (p * q * r)) := by linear_combination -huq_qr
      rw [Nat.cast_mul, ← Nat.cast_mul, hval]
      exact two_mul_ne_zero_of_odd_prime_factor (by ring) hp hp2 (Nat.mul_ne_zero hq0 hr0)
  · refine ⟨p * r, (conj_pow_fixes_iff (p * r) g).mpr ?_,
      conj_pow_ne_one (p * r) ⟨up, by simp⟩ ?_⟩
    · rw [hk, Nat.cast_mul, ← Nat.cast_mul]
      linear_combination -huqfix
    · have hval : ((p * r : ℕ) : ZMod (p * q * r)) * (1 - (↑up : ZMod (p * q * r)))
          = 2 * ((p * r : ℕ) : ZMod (p * q * r)) := by linear_combination -hup_pr
      rw [Nat.cast_mul, ← Nat.cast_mul, hval]
      exact two_mul_ne_zero_of_odd_prime_factor (by ring) hq hq2 (Nat.mul_ne_zero hp0 hr0)
  · refine ⟨p * q, (conj_pow_fixes_iff (p * q) g).mpr ?_,
      conj_pow_ne_one (p * q) ⟨up, by simp⟩ ?_⟩
    · rw [hk, Nat.cast_mul, ← Nat.cast_mul]
      linear_combination -hurfix
    · have hval : ((p * q : ℕ) : ZMod (p * q * r)) * (1 - (↑up : ZMod (p * q * r)))
          = 2 * ((p * q : ℕ) : ZMod (p * q * r)) := by linear_combination -hup_pq
      rw [Nat.cast_mul, ← Nat.cast_mul, hval]
      exact two_mul_ne_zero_of_odd_prime_factor (by ring) hr hr2 (Nat.mul_ne_zero hp0 hq0)

/-! ### Problem 3A.7 — `o(α)` の素因子が 2 個以下なら `⟨α⟩` は regular orbit をもつ

`⟨α⟩` の点 `g` での安定化群が非自明 ⟺ ある素数 `r ∣ n := o(α)` について `α^{n/r}` が `g` を
固定する。したがって regular orbit が無いとすると `G` は固定部分群 `Fix(α^{n/r})`
(`r ∣ n` は高々 2 個) の合併になるが、**群は 2 つの真部分群の合併にならない**ので矛盾。
(3A.8(c) が示すとおり、素因子 3 個では実際に反例がある。) -/

/-- **群は 2 つの真部分群の合併にはならない**。

`H ⊄ K` なる `a ∈ H ∖ K` と `K ⊄ H` なる `b ∈ K ∖ H` を取ると `a*b` はどちらにも入れない。 -/
theorem not_forall_mem_or_mem_of_ne_top {G : Type*} [Group G] {H K : Subgroup G}
    (hH : H ≠ ⊤) (hK : K ≠ ⊤) : ¬ ∀ g : G, g ∈ H ∨ g ∈ K := by
  intro h
  obtain ⟨a, haH, haK⟩ : ∃ a, a ∈ H ∧ a ∉ K := by
    by_contra hc
    push Not at hc
    exact hK (eq_top_iff.mpr fun g _ => (h g).elim (hc g) id)
  obtain ⟨b, hbK, hbH⟩ : ∃ b, b ∈ K ∧ b ∉ H := by
    by_contra hc
    push Not at hc
    exact hH (eq_top_iff.mpr fun g _ => (h g).elim id (hc g))
  rcases h (a * b) with hab | hab
  · exact hbH (by simpa using H.mul_mem (H.inv_mem haH) hab)
  · exact haK (by simpa using K.mul_mem hab (K.inv_mem hbK))

/-- 自己同型 `β ≠ 1` の固定部分群は真部分群。 -/
theorem eqLocus_id_ne_top {G : Type*} [Group G] {β : MulAut G} (hβ : β ≠ 1) :
    (β.toMonoidHom).eqLocus (MonoidHom.id G) ≠ ⊤ := by
  intro h
  refine hβ (MulEquiv.ext fun x => ?_)
  have hx : x ∈ (β.toMonoidHom).eqLocus (MonoidHom.id G) := h ▸ Subgroup.mem_top x
  exact hx

/-- **Isaacs Problem 3A.7**. 有限群 `G` の自己同型 `α` について `o(α)` を割る素数が高々 2 個
ならば、`⟨α⟩` は `G` 上に **regular orbit** をもつ: 安定化群が自明な `g ∈ G` が存在する。 -/
theorem exists_regular_orbit_of_primeFactors_card_le_two {G : Type*} [Group G] [Finite G]
    (α : MulAut G) (h2 : (orderOf α).primeFactors.card ≤ 2) :
    ∃ g : G, ∀ j : ℕ, (α ^ j) g = g → α ^ j = 1 := by
  classical
  by_contra hcon
  push Not at hcon
  set n := orderOf α with hndef
  have hn0 : n ≠ 0 := (orderOf_pos α).ne'
  have hαn : α ^ n = 1 := pow_orderOf_eq_one α
  -- 各 `g` について、`n` の素因子 `r` で `α^{n/r}` が `g` を固定するものがある
  have hkey : ∀ g : G, ∃ r ∈ n.primeFactors, (α ^ (n / r)) g = g := by
    intro g
    obtain ⟨j, hj, hjne⟩ := hcon g
    set m := Nat.gcd n j with hmdef
    have hmn : m ∣ n := Nat.gcd_dvd_left n j
    have hd : orderOf (α ^ j) = n / m := orderOf_pow α
    have hd1 : n / m ≠ 1 := fun h => hjne (orderOf_eq_one_iff.mp (by rw [hd, h]))
    obtain ⟨r, hrp, hrd⟩ := Nat.exists_prime_and_dvd hd1
    have hmr : m * r ∣ n := by
      obtain ⟨c, hc⟩ := hrd
      exact ⟨c, by rw [mul_assoc, ← hc, Nat.mul_div_cancel' hmn]⟩
    have hrn : r ∣ n := dvd_trans ⟨m, by ring⟩ hmr
    refine ⟨r, Nat.mem_primeFactors.mpr ⟨hrp, hrn, hn0⟩, ?_⟩
    -- Bezout で `α^m ∈ ⟨α^j⟩`、よって `α^m` は `g` を固定
    have hstab : α ^ j ∈ MulAction.stabilizer (MulAut G) g := hj
    obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, (m : ℤ) = (n : ℤ) * a + (j : ℤ) * b :=
      ⟨Nat.gcdA n j, Nat.gcdB n j, by exact_mod_cast Nat.gcd_eq_gcd_ab n j⟩
    have hαm : α ^ m = ((α ^ j) ^ b : MulAut G) := by
      calc (α : MulAut G) ^ m = α ^ ((m : ℕ) : ℤ) := (zpow_natCast _ _).symm
        _ = α ^ ((n : ℤ) * a + (j : ℤ) * b) := by rw [hab]
        _ = (α ^ (n : ℤ)) ^ a * (α ^ (j : ℤ)) ^ b := by rw [zpow_add, zpow_mul, zpow_mul]
        _ = ((α ^ j) ^ b : MulAut G) := by
            rw [zpow_natCast, hαn, one_zpow, one_mul, zpow_natCast]
    have hmstab : α ^ m ∈ MulAction.stabilizer (MulAut G) g := hαm ▸ zpow_mem hstab b
    obtain ⟨c, hc⟩ : m ∣ n / r := by
      obtain ⟨t, ht⟩ := hmr
      exact ⟨t, by rw [ht, show m * r * t = r * (m * t) from by ring,
        Nat.mul_div_cancel_left _ hrp.pos]⟩
    have hfix : α ^ (n / r) ∈ MulAction.stabilizer (MulAut G) g := by
      rw [hc, pow_mul]; exact pow_mem hmstab c
    exact hfix
  -- 固定部分群 `F r` は真部分群
  set F : ℕ → Subgroup G := fun r => ((α ^ (n / r)).toMonoidHom).eqLocus (MonoidHom.id G)
    with hF
  have hFmem : ∀ (r : ℕ) (g : G), (α ^ (n / r)) g = g → g ∈ F r := fun _ _ h => h
  have hFne : ∀ r ∈ n.primeFactors, F r ≠ ⊤ := by
    intro r hr
    obtain ⟨hrp, hrn, -⟩ := Nat.mem_primeFactors.mp hr
    have hdiv : n / r ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨hrp.pos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hrn⟩
    have hord : orderOf (α ^ (n / r)) = r := by
      rw [orderOf_pow_of_dvd hdiv (by rw [← hndef]; exact Nat.div_dvd_of_dvd hrn), ← hndef,
        Nat.div_div_self hrn hn0]
    refine eqLocus_id_ne_top fun hcon1 => ?_
    rw [hcon1, orderOf_one] at hord
    exact hrp.one_lt.ne hord
  -- 素因子が高々 2 個 ⟹ `G` は 2 つの真部分群の合併になり矛盾
  by_cases hemp : n.primeFactors = ∅
  · obtain ⟨r, hr, -⟩ := hkey 1
    rw [hemp] at hr
    exact absurd hr (Finset.notMem_empty r)
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
  have hcard : (n.primeFactors.erase p).card ≤ 1 := by
    have := Finset.card_erase_of_mem hp
    omega
  by_cases hT : n.primeFactors.erase p = ∅
  · refine hFne p hp (eq_top_iff.mpr fun g _ => ?_)
    obtain ⟨r, hr, hgr⟩ := hkey g
    have hrp : r = p := by
      by_contra hne
      exact absurd (Finset.mem_erase.mpr ⟨hne, hr⟩) (hT ▸ Finset.notMem_empty r)
    exact hFmem p g (hrp ▸ hgr)
  obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hT
  refine not_forall_mem_or_mem_of_ne_top (hFne p hp) (hFne q (Finset.mem_erase.mp hq).2)
    fun g => ?_
  obtain ⟨r, hr, hgr⟩ := hkey g
  by_cases hrp : r = p
  · exact Or.inl (hFmem p g (hrp ▸ hgr))
  · have hrq : r = q :=
      Finset.card_le_one.mp hcard r (Finset.mem_erase.mpr ⟨hrp, hr⟩) q hq
    exact Or.inr (hFmem q g (hrq ▸ hgr))

/-- **Isaacs Problem 3A.5**. 有限群 `G` について、`G` の自身への共役作用で作った半直積 `G ⋊ G` は
直積 `G × G` に同型。同型 `(n, g) ↦ (n·g, g)` は準同型: 半直積の積 `(a.left · a.right·b.left·a.right⁻¹,
a.right·b.right)` を写すと `(a.left·a.right·b.left·b.right, a.right·b.right)` = 直積の積の像。 -/
def semidirectConjEquivProd (G : Type*) [Group G] :
    SemidirectProduct G G MulAut.conj ≃* G × G where
  toFun x := (x.left * x.right, x.right)
  invFun p := ⟨p.1 * p.2⁻¹, p.2⟩
  left_inv x := SemidirectProduct.ext (by simp) rfl
  right_inv p := by simp
  map_mul' a b := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, MulAut.conj_apply,
      Prod.mk_mul_mk, Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> group

end

end OddOrder.Isaacs.Ch03
