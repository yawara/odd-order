/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.ElementaryAbelianLinear
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.NormNum.Prime

/-!
# The automorphism group of a commutative group

Two general constraints on `Aut(A)` for a commutative group `A`, both needed for the
classification of the abelian groups with simple automorphism group (Isaacs Problem 8C.6):

* inversion `a ↦ a⁻¹` is a *central* automorphism, so if `Aut(A)` is simple and `A` has
  exponent bigger than `2` then `Aut(A)` is forced to be the group of order `2`;
* the power maps `a ↦ a ^ k` for `k` prime to the exponent `n` embed `(ZMod n)ˣ` into
  `Aut(A)`, so `φ(n) ≤ |Aut(A)|`.

Together: a finite abelian `A` with simple `Aut(A)` and an element of order `> 2` has
`φ(exp A) ≤ 2`, i.e. `exp A ∈ {3, 4, 6}`.

## Main results

* `OddOrder.GroupTheory.invMulAut` — inversion as an automorphism, with
  `invMulAut_mem_center`.
* `OddOrder.GroupTheory.card_mulAut_eq_two_of_isSimpleGroup`
* `OddOrder.GroupTheory.totient_exponent_le_card_mulAut`
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

variable {A : Type*} [CommGroup A]

/-! ## Inversion is a central automorphism -/

/-- 可換群 `A` の反転写像 `a ↦ a⁻¹` は自己同型. -/
def invMulAut (A : Type*) [CommGroup A] : MulAut A where
  toFun a := a⁻¹
  invFun a := a⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := mul_inv a b

@[simp]
theorem invMulAut_apply (a : A) : invMulAut A a = a⁻¹ := rfl

/-- 反転はすべての自己同型と可換 — 自己同型は逆元を保つから. -/
theorem invMulAut_mem_center : invMulAut A ∈ Subgroup.center (MulAut A) := by
  rw [Subgroup.mem_center_iff]
  intro g
  ext a
  simp [MulAut.mul_apply]

@[simp]
theorem invMulAut_sq : invMulAut A * invMulAut A = 1 := by
  ext a
  simp [MulAut.mul_apply]

/-- 反転が自明 ⟺ `A` の指数が `2` を割る. -/
theorem invMulAut_eq_one_iff : invMulAut A = 1 ↔ ∀ a : A, a ^ 2 = 1 := by
  constructor
  · intro h a
    have hinv : a⁻¹ = a := by
      have := congrArg (fun f : MulAut A => f a) h
      simpa using this
    calc a ^ 2 = a * a := pow_two a
      _ = a⁻¹ * a := by rw [hinv]
      _ = 1 := inv_mul_cancel a
  · intro h
    ext a
    have : a * a = 1 := by simpa [pow_two] using h a
    simpa using inv_eq_of_mul_eq_one_left this

/-- **可換群 `A` の自己同型群が単純で `A` の指数が `2` より大きいなら `|Aut(A)| = 2`.**

反転 `a ↦ a⁻¹` は `Aut(A)` の中心元 (`invMulAut_mem_center`) なので, 単純性から中心は
`⊤`, すなわち `Aut(A)` は可換. 可換な単純群は素数位数 (`Group.is_simple_iff_prime_card`)
で, 位数 `2` の元 (反転) をもつからその素数は `2`. -/
theorem card_mulAut_eq_two_of_isSimpleGroup (hs : IsSimpleGroup (MulAut A))
    (h : ∃ a : A, a ^ 2 ≠ 1) : Nat.card (MulAut A) = 2 := by
  have hne : invMulAut A ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := h
    exact ha (invMulAut_eq_one_iff.mp hc a)
  have hcenter : Subgroup.center (MulAut A) = ⊤ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (MulAut A)) inferInstance with hb | ht
    · exact absurd (Subgroup.mem_bot.mp (hb ▸ invMulAut_mem_center (A := A))) hne
    · exact ht
  haveI : IsMulCommutative (MulAut A) := Subgroup.center_eq_top_iff.mp hcenter
  have hp : (Nat.card (MulAut A)).Prime := Group.is_simple_iff_prime_card.mp hs
  haveI : Finite (MulAut A) := Nat.finite_of_card_ne_zero hp.ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf (invMulAut A) = 2 :=
    orderOf_eq_prime (by rw [pow_two, invMulAut_sq]) hne
  have hdvd : (2 : ℕ) ∣ Nat.card (MulAut A) := hord ▸ orderOf_dvd_natCard _
  exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hdvd).symm

/-! ## The unit power maps embed `(ZMod n)ˣ` -/

/-- 指数が `n` を割る可換群では, `ZMod n` のスカラー倍は代表元による冪写像. -/
theorem zmod_smul_ofMul {n : ℕ} [NeZero n] [Module (ZMod n) (Additive A)] (c : ZMod n) (a : A) :
    c • (Additive.ofMul a) = Additive.ofMul (a ^ c.val) := by
  conv_lhs => rw [show c = ((c.val : ℕ) : ZMod n) from (ZMod.natCast_rightInverse c).symm]
  rw [Nat.cast_smul_eq_nsmul, ← ofMul_pow]

section Exponent

variable [Finite A]

/-- `Additive A` の `ZMod n`-加群構造と位数ちょうど `n` の元があれば `φ(n) ≤ |Aut(A)|`.

単元 `u : (ZMod n)ˣ` によるスカラー倍 (= 冪写像 `a ↦ a ^ u`) は自己同型
(`LinearEquiv.smulOfUnit` を `mulAutEquivLinearEquiv` で戻す) で, 位数 `n` の元の上で
値が一致すれば `u` が一致するから, `(ZMod n)ˣ → Aut(A)` は単射. -/
theorem totient_le_card_mulAut_of_orderOf_eq {n : ℕ} [NeZero n]
    [Module (ZMod n) (Additive A)] {g : A} (hg : orderOf g = n) :
    Nat.totient n ≤ Nat.card (MulAut A) := by
  classical
  have e : MulAut A ≃* (Additive A ≃ₗ[ZMod n] Additive A) := mulAutEquivLinearEquiv (n := n)
  set F : (ZMod n)ˣ → MulAut A := fun u =>
    e.symm (LinearEquiv.smulOfUnit (R := ZMod n) (M := Additive A) u) with hF
  have hinj : Function.Injective F := by
    intro u v huv
    have h1 : LinearEquiv.smulOfUnit (R := ZMod n) (M := Additive A) u
        = LinearEquiv.smulOfUnit (R := ZMod n) (M := Additive A) v :=
      e.symm.injective huv
    have h2 : (u : ZMod n) • (Additive.ofMul g) = (v : ZMod n) • (Additive.ofMul g) :=
      congrArg (fun e : Additive A ≃ₗ[ZMod n] Additive A => e (Additive.ofMul g)) h1
    rw [zmod_smul_ofMul, zmod_smul_ofMul] at h2
    have h3 : g ^ ((u : ZMod n).val) = g ^ ((v : ZMod n).val) := congrArg Additive.toMul h2
    have h4 : (u : ZMod n).val ≡ (v : ZMod n).val [MOD n] := by
      have := pow_eq_pow_iff_modEq.mp h3
      rwa [hg] at this
    have h5 : (u : ZMod n).val = (v : ZMod n).val := by
      have hu := ZMod.val_lt (u : ZMod n)
      have hv := ZMod.val_lt (v : ZMod n)
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using h4
    exact Units.ext (ZMod.val_injective n h5)
  have hcard : Nat.card ((ZMod n)ˣ) = n.totient := by
    haveI : Fintype (ZMod n) := ZMod.fintype n
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  calc n.totient = Nat.card ((ZMod n)ˣ) := hcard.symm
    _ ≤ Nat.card (MulAut A) := Nat.card_le_card_of_injective F hinj

/-- **`φ(exp A) ≤ |Aut(A)|`** (有限可換 `A`).

指数 `n` に対し `Additive A` は `ZMod n`-加群 (`zmodModule_of_pow_eq_one`) で,
位数ちょうど `n` の元が存在する (`Monoid.exists_orderOf_eq_exponent`) から
`totient_le_card_mulAut_of_orderOf_eq` が使える. -/
theorem totient_exponent_le_card_mulAut :
    Nat.totient (Monoid.exponent A) ≤ Nat.card (MulAut A) := by
  letI : Module (ZMod (Monoid.exponent A)) (Additive A) :=
    zmodModule_of_pow_eq_one (n := Monoid.exponent A) (E := A) fun x =>
      Monoid.pow_exponent_eq_one x
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := A) Monoid.ExponentExists.of_finite
  exact totient_le_card_mulAut_of_orderOf_eq hg

/-! ## `φ(n) ≤ 2` の解 -/

/-- **`φ(n) ≤ 2` をみたす `n ≠ 0` は `1, 2, 3, 4, 6` のみ** (古典的).

`d ∣ n` なら `φ d ∣ φ n` (`Nat.totient_dvd_of_dvd`) なので, どの約数も `φ ≤ 2`.
`φ 8 = 4`, `φ 9 = 6`, `φ p = p - 1` から `8 ∤ n`, `9 ∤ n`, 素因数は `≤ 3`; したがって
`n ∣ 12` で, 残りは有限チェック (`12` 自身は `φ 12 = 4` で落ちる). -/
theorem eq_of_totient_le_two {n : ℕ} (hn : n ≠ 0) (h : n.totient ≤ 2) :
    n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6 := by
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have key : ∀ d : ℕ, d ∣ n → d.totient ≤ 2 := fun d hd =>
    le_trans (Nat.le_of_dvd hpos (Nat.totient_dvd_of_dvd hd)) h
  have h8 : ¬ (8 ∣ n) := fun hd => by have := key 8 hd; revert this; decide
  have h9 : ¬ (9 ∣ n) := fun hd => by have := key 9 hd; revert this; decide
  have hdvd : n ∣ 12 := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    have hpn : p ∣ n := dvd_trans (dvd_pow_self p hk.ne') hpk
    have hp3 : p ≤ 3 := by
      have := key p hpn
      rw [Nat.totient_prime hp] at this
      have := hp.two_le
      omega
    have hp2 := hp.two_le
    interval_cases p
    · -- `p = 2`: `8 ∤ n` から `k ≤ 2`
      have hk2 : k ≤ 2 := by
        by_contra hc
        exact h8 (dvd_trans (pow_dvd_pow 2 (by omega : 3 ≤ k)) hpk)
      exact dvd_trans (pow_dvd_pow 2 hk2) (by norm_num)
    · -- `p = 3`: `9 ∤ n` から `k ≤ 1`
      have hk1 : k ≤ 1 := by
        by_contra hc
        exact h9 (dvd_trans (pow_dvd_pow 3 (by omega : 2 ≤ k)) hpk)
      exact dvd_trans (pow_dvd_pow 3 hk1) (by norm_num)
  have hle : n ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  have hge : 1 ≤ n := Nat.pos_of_ne_zero hn
  interval_cases n <;> revert h <;> decide

/-- **有限可換群 `A` の自己同型群が単純で指数が `2` より大きいなら, 指数は `3`, `4`, `6`.**

単純性から `|Aut(A)| = 2` (`card_mulAut_eq_two_of_isSimpleGroup`), 単元冪写像の埋め込みから
`φ(exp A) ≤ 2` (`totient_exponent_le_card_mulAut`), あとは `eq_of_totient_le_two`. -/
theorem exponent_mem_of_isSimpleGroup_mulAut (hs : IsSimpleGroup (MulAut A))
    (h : ∃ a : A, a ^ 2 ≠ 1) :
    Monoid.exponent A = 3 ∨ Monoid.exponent A = 4 ∨ Monoid.exponent A = 6 := by
  have hcard := card_mulAut_eq_two_of_isSimpleGroup hs h
  have hle : Nat.totient (Monoid.exponent A) ≤ 2 := by
    rw [← hcard]; exact totient_exponent_le_card_mulAut
  have hpow : ∀ a : A, a ^ Monoid.exponent A = 1 := Monoid.pow_exponent_eq_one
  obtain ⟨a, ha⟩ := h
  rcases eq_of_totient_le_two Monoid.exponent_ne_zero_of_finite hle with he | he | he | he | he
  · exact absurd (by have := hpow a; rw [he, pow_one] at this; rw [this]; simp) ha
  · exact absurd (by have := hpow a; rwa [he] at this) ha
  · exact Or.inl he
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr he)

end Exponent

/-! ## Square-zero endomorphisms produce automorphisms -/

/-- 可換群の自己準同型 `f` が `f ∘ f = 1` (自明写像) をみたすなら `a ↦ a * f a` は自己同型
(逆写像は `a ↦ a * (f a)⁻¹`). 加法的に書けば `f² = 0` のとき `1 + f` が可逆で
`(1 + f)⁻¹ = 1 - f`, ということ. -/
def mulAutOfSquareZero (f : A →* A) (hf : ∀ a, f (f a) = 1) : MulAut A where
  toFun a := a * f a
  invFun a := a * (f a)⁻¹
  left_inv a := by simp [map_mul, hf]
  right_inv a := by simp [map_mul, hf]
  map_mul' a b := by simp [map_mul, mul_comm, mul_assoc, mul_left_comm]

@[simp]
theorem mulAutOfSquareZero_apply (f : A →* A) (hf : ∀ a, f (f a) = 1) (a : A) :
    mulAutOfSquareZero f hf a = a * f a := rfl

theorem mulAutOfSquareZero_ne_one {f : A →* A} (hf : ∀ a, f (f a) = 1) (hne : f ≠ 1) :
    mulAutOfSquareZero f hf ≠ 1 := by
  intro hc
  refine hne (MonoidHom.ext fun a => ?_)
  have := congrArg (fun φ : MulAut A => φ a) hc
  simp only [mulAutOfSquareZero_apply, MulAut.one_apply] at this
  simpa using (mul_eq_left.mp this)

/-- 位数 `2` の群では非自明な元は一意. -/
theorem eq_of_ne_one_of_card_eq_two {G : Type*} [Group G] (hG : Nat.card G = 2) {x y : G}
    (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite G
  by_contra hxy
  have hcard3 : ({1, x, y} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx, Ne.symm hy]),
      Finset.card_insert_of_notMem (by simp [hxy]), Finset.card_singleton]
  have hle := Finset.card_le_card (Finset.subset_univ ({1, x, y} : Finset G))
  rw [hcard3, Finset.card_univ, ← Nat.card_eq_fintype_card, hG] at hle
  omega

/-- **`|Aut(A)| = 2` かつ `A` の指数が `2` より大きいとき, 非自明な冪零自己準同型は
`a ↦ a⁻²` に限る.**

`f² = 1` なら `a ↦ a * f a` は自己同型 (`mulAutOfSquareZero`) で, `f ≠ 1` から自明でない.
`Aut(A)` の非自明な元は反転しかない (`eq_of_ne_one_of_card_eq_two`) ので
`a * f a = a⁻¹`. -/
theorem eq_inv_sq_of_card_mulAut_eq_two (hcard : Nat.card (MulAut A) = 2)
    (hexp : ∃ a : A, a ^ 2 ≠ 1) {f : A →* A} (hf : ∀ a, f (f a) = 1) (hne : f ≠ 1) :
    ∀ a : A, f a = (a ^ 2)⁻¹ := by
  have hinv : invMulAut A ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := hexp
    exact ha (invMulAut_eq_one_iff.mp hc a)
  have := eq_of_ne_one_of_card_eq_two hcard (mulAutOfSquareZero_ne_one hf hne) hinv
  intro a
  have ha := congrArg (fun φ : MulAut A => φ a) this
  simp only [mulAutOfSquareZero_apply, invMulAut_apply] at ha
  rw [pow_two, mul_inv]
  calc f a = a⁻¹ * (a * f a) := by group
    _ = a⁻¹ * a⁻¹ := by rw [ha]

/-! ## A proper subgroup is killed by some character of prime order -/

/-- **`Additive V` が `𝔽ₚ` 上の非自明なベクトル空間なら, `V` には非自明な指標
`V →* Multiplicative (ZMod p)` がある** — 基底の座標関数を乗法的に読み替えるだけ.

⚠ 加群構造は **instance 引数**で取る: 呼び出し側が `letI` で供給した `ZMod p`-加群構造の
下では `V →ₗ[ZMod p] ZMod p` の関数強制が解決しないので, 線形写像を扱う部分をこの補題に
閉じ込め, 外へは `MonoidHom` だけを渡す. -/
theorem exists_nontrivial_hom_of_zmodModule {p : ℕ} (hp : p.Prime) {V : Type*} [CommGroup V]
    [Nontrivial V] [Module (ZMod p) (Additive V)] :
    ∃ π : V →* Multiplicative (ZMod p), π ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (Additive V) := inferInstanceAs (Nontrivial V)
  set b := Module.Basis.ofVectorSpace (ZMod p) (Additive V) with hb
  obtain ⟨i⟩ := b.index_nonempty
  have hbi : b.coord i (b i) = 1 := by
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  refine ⟨{ toFun := fun v => Multiplicative.ofAdd (b.coord i (Additive.ofMul v))
            map_one' := by simp
            map_mul' := fun x y => by simp [ofMul_mul, map_add] }, fun hc => ?_⟩
  have hval :=
    congrArg (fun ψ : V →* Multiplicative (ZMod p) => ψ (Additive.toMul (b i))) hc
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, ofMul_toMul] at hval
  have h0 : b.coord i (b i) = 0 := by simpa using congrArg Multiplicative.toAdd hval
  rw [hbi] at h0
  exact one_ne_zero h0

/-- **非自明な有限可換群には, ある素数 `p` について非自明な指標
`Q →* Multiplicative (ZMod p)` がある.**

`p` を `|Q|` の素因数とすると, Cauchy から `Q` の `p` 乗写像は単射でなく, 有限性から
したがって全射でもない. よって `V = Q/Q^p` は非自明で指数が `p` を割る — つまり `𝔽ₚ` 上の
非自明なベクトル空間で, 基底の座標関数が求める指標を与える. -/
theorem exists_prime_nontrivial_hom (Q : Type*) [CommGroup Q] [Finite Q] [Nontrivial Q] :
    ∃ p : ℕ, ∃ _ : p.Prime, ∃ π : Q →* Multiplicative (ZMod p), π ≠ 1 := by
  classical
  set p := (Nat.card Q).minFac with hpdef
  have hcardQ : 1 < Nat.card Q := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hp : p.Prime := Nat.minFac_prime (by omega)
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p` 乗写像は単射でない (Cauchy) から全射でもない
  haveI := Fintype.ofFinite Q
  obtain ⟨q, hq⟩ : ∃ q : Q, orderOf q = p :=
    exists_prime_orderOf_dvd_card p (by rw [← Nat.card_eq_fintype_card]; exact Nat.minFac_dvd _)
  have hq1 : q ≠ 1 := by
    intro hcq
    rw [hcq, orderOf_one] at hq
    exact hp.one_lt.ne hq
  have hnotsurj : ¬ Function.Surjective (powMonoidHom p : Q →* Q) := by
    rw [← Finite.injective_iff_surjective]
    intro hinj
    refine hq1 (hinj ?_)
    change q ^ p = (1 : Q) ^ p
    rw [one_pow, ← hq, pow_orderOf_eq_one]
  set R := (powMonoidHom p : Q →* Q).range with hRdef
  have hR : R ≠ ⊤ := fun hc => hnotsurj (MonoidHom.range_eq_top.mp hc)
  -- `V := Q ⧸ R` は非自明で指数が `p` を割る
  obtain ⟨v₀, hv₀⟩ : ∃ v : Q, v ∉ R := by
    by_contra hc
    exact hR (Subgroup.eq_top_iff' R |>.mpr fun x => not_not.mp fun hx => hc ⟨x, hx⟩)
  haveI : Nontrivial (Q ⧸ R) :=
    ⟨⟨QuotientGroup.mk v₀, 1, by simpa [QuotientGroup.eq_one_iff] using hv₀⟩⟩
  have hVexp : ∀ v : Q ⧸ R, v ^ p = 1 := by
    intro v
    induction v using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact ⟨x, rfl⟩
  letI : Module (ZMod p) (Additive (Q ⧸ R)) := zmodModule_of_pow_eq_one (n := p) hVexp
  obtain ⟨π, hπ⟩ := exists_nontrivial_hom_of_zmodModule (V := Q ⧸ R) hp
  refine ⟨p, hp, π.comp (QuotientGroup.mk' R), fun hc => hπ (MonoidHom.ext fun y => ?_)⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R y
  simpa using congrArg (fun ψ : Q →* Multiplicative (ZMod p) => ψ x) hc

/-- **有限可換群の真部分群 `H` は, ある素数位数の指標で殺される.**

`A ⧸ H` は非自明なので `exists_prime_nontrivial_hom` を適用し, 商写像と合成する. -/
theorem exists_prime_hom_of_ne_top [Finite A] {H : Subgroup A} (hH : H ≠ ⊤) :
    ∃ p : ℕ, ∃ _ : p.Prime, ∃ φ : A →* Multiplicative (ZMod p),
      (∀ x ∈ H, φ x = 1) ∧ φ ≠ 1 := by
  obtain ⟨a₀, ha₀⟩ : ∃ a : A, a ∉ H := by
    by_contra hc
    exact hH (Subgroup.eq_top_iff' H |>.mpr fun x => not_not.mp fun hx => hc ⟨x, hx⟩)
  haveI : Nontrivial (A ⧸ H) :=
    ⟨⟨QuotientGroup.mk a₀, 1, by simpa [QuotientGroup.eq_one_iff] using ha₀⟩⟩
  obtain ⟨p, hp, π, hπ⟩ := exists_prime_nontrivial_hom (A ⧸ H)
  refine ⟨p, hp, π.comp (QuotientGroup.mk' H), fun x hx => ?_, ?_⟩
  · have hx1 : (x : A ⧸ H) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    change π ((QuotientGroup.mk' H) x) = 1
    rw [QuotientGroup.mk'_apply, hx1, map_one]
  · intro hc
    refine hπ (MonoidHom.ext fun y => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective H y
    simpa using congrArg (fun ψ : A →* Multiplicative (ZMod p) => ψ x) hc

/-! ## `|Aut(A)| = 2` forces cyclicity -/

/-- **`|Aut(A)| = 2` かつ指数が `2` より大きい有限可換群は巡回群.**

指数と同じ位数の元 `g` をとり, `⟨g⟩ ≠ ⊤` と仮定して矛盾を導く. `exists_prime_hom_of_ne_top`
から, ある素数 `p` と `⟨g⟩` を殺す非自明な指標 `φ : A →* Multiplicative (ZMod p)` が取れる.
`p ∣ orderOf g` なので `h := g ^ (orderOf g / p)` は位数 `p` で, `f a := h ^ (φ a).val` は
自己準同型. その像は `⟨h⟩ ≤ ⟨g⟩ ≤ ker φ` に入るから `f ∘ f = 1` であり, `φ ≠ 1` から
`f ≠ 1`. よって `eq_inv_sq_of_card_mulAut_eq_two` が `f a = a⁻²` を強制するが,
`a = g` では `f g = 1` (`φ g = 1`) なので `g ^ 2 = 1` となり指数 `> 2` に矛盾. -/
theorem isCyclic_of_card_mulAut_eq_two [Finite A] (hcard : Nat.card (MulAut A) = 2)
    (hexp : ∃ a : A, a ^ 2 ≠ 1) : IsCyclic A := by
  classical
  obtain ⟨g, hg⟩ := Monoid.exists_orderOf_eq_exponent (G := A) Monoid.ExponentExists.of_finite
  have hg2 : g ^ 2 ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := hexp
    have hdvd : Monoid.exponent A ∣ 2 := hg ▸ orderOf_dvd_of_pow_eq_one hc
    exact ha (orderOf_dvd_iff_pow_eq_one.mp ((Monoid.order_dvd_exponent a).trans hdvd))
  rw [isCyclic_iff_exists_zpowers_eq_top]
  refine ⟨g, ?_⟩
  by_contra hne
  obtain ⟨p, hp, φ, hφker, hφ⟩ := exists_prime_hom_of_ne_top (A := A) hne
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  obtain ⟨a₁, ha₁⟩ : ∃ a : A, φ a ≠ 1 := by
    by_contra hc
    exact hφ (MonoidHom.ext fun a => not_not.mp fun hx => hc ⟨a, hx⟩)
  -- `p ∣ orderOf g`
  have hcardMul : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  have hordφ : orderOf (φ a₁) = p := by
    have hdvd : orderOf (φ a₁) ∣ p := by
      have hd := orderOf_dvd_natCard (φ a₁)
      rwa [hcardMul] at hd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha₁
    · exact h1
  have hpg : p ∣ orderOf g := by
    rw [hg]
    exact hordφ ▸ (orderOf_map_dvd φ a₁).trans (Monoid.order_dvd_exponent a₁)
  -- 位数 `p` の元 `h ∈ ⟨g⟩`
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hdivpos : orderOf g / p ≠ 0 :=
    Nat.div_ne_zero_iff.mpr ⟨hp.pos.ne', Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpg⟩
  have hhord : orderOf (g ^ (orderOf g / p)) = p := by
    rw [orderOf_pow' _ hdivpos, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpg),
      Nat.div_div_self hpg hn0]
  -- 自己準同型 `f a = h ^ (φ a).val`
  have hmul : ∀ x y : Multiplicative (ZMod p),
      (g ^ (orderOf g / p)) ^ (Multiplicative.toAdd (x * y)).val
        = (g ^ (orderOf g / p)) ^ (Multiplicative.toAdd x).val *
          (g ^ (orderOf g / p)) ^ (Multiplicative.toAdd y).val := by
    intro x y
    rw [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← pow_mod_orderOf (g ^ (orderOf g / p)), hhord]
  let f : A →* A :=
    { toFun := fun a => (g ^ (orderOf g / p)) ^ (Multiplicative.toAdd (φ a)).val
      map_one' := by simp
      map_mul' := fun a b => by rw [map_mul]; exact hmul _ _ }
  have hfapp : ∀ a : A, f a = (g ^ (orderOf g / p)) ^ (Multiplicative.toAdd (φ a)).val :=
    fun _ => rfl
  have hfg : f g = 1 := by
    rw [hfapp, hφker g (Subgroup.mem_zpowers g)]
    simp
  have hff : ∀ a, f (f a) = 1 := by
    intro a
    have hmem : f a ∈ Subgroup.zpowers g := by
      rw [hfapp, ← pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) _
    rw [hfapp, hφker _ hmem]
    simp
  have hfne : f ≠ 1 := by
    intro hc
    have hval : (g ^ (orderOf g / p)) ^ (Multiplicative.toAdd (φ a₁)).val = 1 := by
      rw [← hfapp, hc]; rfl
    refine pow_ne_one_of_lt_orderOf ?_ (by rw [hhord]; exact ZMod.val_lt _) hval
    intro h0
    exact ha₁ (by simpa using congrArg Multiplicative.ofAdd ((ZMod.val_eq_zero _).mp h0))
  have hkey := eq_inv_sq_of_card_mulAut_eq_two hcard hexp hff hfne g
  rw [hfg] at hkey
  exact hg2 (by simpa using hkey.symm)

/-- **`Aut(A)` が単純で `A` の指数が `2` より大きいなら, `A` は位数 `3`, `4`, `6` の巡回群.**

`card_mulAut_eq_two_of_isSimpleGroup` で `|Aut(A)| = 2`,
`isCyclic_of_card_mulAut_eq_two` で巡回性, `exponent_mem_of_isSimpleGroup_mulAut` で
指数 (= 巡回群なので位数) が `3, 4, 6` のいずれか. -/
theorem isCyclic_and_card_of_isSimpleGroup_mulAut [Finite A] (hs : IsSimpleGroup (MulAut A))
    (hexp : ∃ a : A, a ^ 2 ≠ 1) :
    IsCyclic A ∧ (Nat.card A = 3 ∨ Nat.card A = 4 ∨ Nat.card A = 6) := by
  haveI : IsCyclic A :=
    isCyclic_of_card_mulAut_eq_two (card_mulAut_eq_two_of_isSimpleGroup hs hexp) hexp
  refine ⟨inferInstance, ?_⟩
  have hexpA := exponent_mem_of_isSimpleGroup_mulAut hs hexp
  rwa [IsCyclic.exponent_eq_card] at hexpA

/-! ## Two elementary obstructions to simplicity -/

/-- 位数 `2` 以下の群の自己同型群は自明 — 非自明な元は一意なのでどの自己同型もそれを動かせない. -/
theorem subsingleton_mulAut_of_card_le_two {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G ≤ 2) : Subsingleton (MulAut G) := by
  refine ⟨fun φ ψ => MulEquiv.ext fun a => ?_⟩
  rcases eq_or_ne a 1 with rfl | ha
  · simp
  rcases Nat.lt_or_ge (Nat.card G) 2 with hlt | hge
  · haveI : Subsingleton G := Finite.card_le_one_iff_subsingleton.mp (by omega)
    exact absurd (Subsingleton.elim a 1) ha
  have hcard : Nat.card G = 2 := le_antisymm hG hge
  have hφ : φ a = a :=
    eq_of_ne_one_of_card_eq_two hcard (fun hc => ha (φ.injective (by simp [hc]))) ha
  have hψ : ψ a = a :=
    eq_of_ne_one_of_card_eq_two hcard (fun hc => ha (ψ.injective (by simp [hc]))) ha
  rw [hφ, hψ]

/-- 位数 `6` の群は単純でない — Cauchy で得た位数 `3` の元の生成する部分群は指数 `2`,
したがって正規で真かつ非自明. -/
theorem not_isSimpleGroup_of_card_eq_six {G : Type*} [Group G] (hG : Nat.card G = 6) :
    ¬ IsSimpleGroup G := by
  intro hs
  haveI : Finite G := Nat.finite_of_card_ne_zero (by omega)
  haveI := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ : ∃ x : G, orderOf x = 3 :=
    exists_prime_orderOf_dvd_card 3 (by rw [← Nat.card_eq_fintype_card, hG]; norm_num)
  have hcardH : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have hmul := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hcardH, hG] at hmul
    omega
  haveI : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hindex
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) inferInstance with hb | ht
  · rw [hb, Subgroup.index_bot, hG] at hindex; omega
  · rw [ht, Subgroup.index_top] at hindex; omega

end OddOrder.GroupTheory
