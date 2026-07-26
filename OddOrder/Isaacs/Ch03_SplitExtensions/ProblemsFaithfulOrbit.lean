/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch01_Sylow.Main
import OddOrder.Mathlib.SemidirectProduct

/-!
# Isaacs Chapter 3 — Problem 3A.6 (忠実な軌道の存在)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 3A.6 (書籍 p. 78)。

`p`-群 `P` が `p ∤ |G|` なる群 `G` に**忠実に**自己同型で作用するなら, ある `P`-軌道
`Δ ⊆ G` の上でも `P` は忠実に作用する。hint は **Theorem 1.38** (generalized Brodkey)。

## 証明の構造 (issue 1055 参照)

`Γ := G ⋊ P` の中で:

* `Y := inr(P)` は `Γ` の Sylow `p`-部分群 (`sylowInrRange`) — `|Γ : Y| = |G|` は `p` と互いに素。
* `Y ∩ Y^{inl g} = inr(P_g)` (**Sylow 交叉 = 点安定化群**): `(inl g)⁻¹ · inr u · inl g
  = inl (g⁻¹ · (φ u) g) · inr u` なので `P` に入るのは `(φ u) g = g` のときだけ。
* `O_p(Γ) = 1` (`opCore_eq_bot_of_injective`): `O_p(Γ)` は全 Sylow に含まれるので `Y` に入り,
  `X := inl(G)` とは位数が互いに素で交わらず `⁅O_p(Γ), X⁆ = 1`, すなわち
  `O_p(Γ) ≤ Y ⊓ C_Γ(X) = 1` (忠実性)。
* 軌道 `Δ_g` の各点固定部分群 `N = core_P(P_g)` は `P` **と `P^g` の両方**で正規なので,
  `|Y ⊓ Y^{inl g}|` を最小にする `g` に **Thm 1.38** を適用して `N ≤ O_p(Γ) = 1`。
-/

namespace OddOrder.Isaacs.Ch03

open scoped Pointwise

section /- Problem 3A.6 (p. 78) -/

variable {G P : Type*} [Group G] [Group P] {φ : P →* MulAut G}

/-! ### 半直積の基本計算 -/

/-- **共役の展開**: `(inl g)⁻¹ · inr u · inl g = inl (g⁻¹ * (φ u) g) · inr u`. -/
theorem inl_inv_mul_inr_mul_inl (g : G) (u : P) :
    (SemidirectProduct.inl g)⁻¹ * SemidirectProduct.inr u * SemidirectProduct.inl g
      = (SemidirectProduct.inl (g⁻¹ * (φ u) g) : G ⋊[φ] P) * SemidirectProduct.inr u := by
  ext <;> simp

/-- **Sylow 交叉 = 点安定化群** (元の形): `(inl g)⁻¹ · inr u · inl g ∈ inr(P)` は
`(φ u) g = g` と同値。 -/
theorem conj_inr_mem_inr_range_iff (g : G) (u : P) :
    (SemidirectProduct.inl g)⁻¹ * SemidirectProduct.inr u * SemidirectProduct.inl g
        ∈ (SemidirectProduct.inr : P →* G ⋊[φ] P).range ↔ (φ u) g = g := by
  rw [inl_inv_mul_inr_mul_inl]
  constructor
  · rintro ⟨v, hv⟩
    have hleft := congrArg SemidirectProduct.left hv
    simp only [SemidirectProduct.left_inr, SemidirectProduct.mul_left,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, map_one,
      mul_one] at hleft
    exact (inv_mul_eq_one.mp hleft.symm).symm
  · intro h
    rw [h, inv_mul_cancel, map_one, one_mul]
    exact ⟨u, rfl⟩

/-! ### `Y = inr(P)` は Sylow `p`-部分群 -/

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
/-- `inr(P)` は `p`-群. -/
theorem isPGroup_inr_range (hP : IsPGroup p P) :
    IsPGroup p ↥((SemidirectProduct.inr : P →* G ⋊[φ] P).range) := by
  rintro ⟨_, u, rfl⟩
  obtain ⟨k, hk⟩ := hP u
  refine ⟨k, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow]
  simp only [← map_pow, hk, map_one]
  rfl

variable [Finite G] [Finite P]

/-- `Γ = G ⋊ P` の位数の `p`-部分は `|P|` (`p ∤ |G|` のとき). -/
theorem card_inr_range_eq_pow_factorization (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G) :
    Nat.card ↥((SemidirectProduct.inr : P →* G ⋊[φ] P).range)
      = p ^ (Nat.card (G ⋊[φ] P)).factorization p := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := P)).mp hP
  have hrange : Nat.card ↥((SemidirectProduct.inr : P →* G ⋊[φ] P).range) = Nat.card P :=
    Nat.card_congr
      (MonoidHom.ofInjective (SemidirectProduct.inr_injective (φ := φ))).symm.toEquiv
  have hcard : Nat.card (G ⋊[φ] P) = Nat.card G * p ^ k := by
    rw [SemidirectProduct.card, hk]
  rw [hrange, hk, hcard, Nat.factorization_mul (Nat.card_pos (α := G)).ne'
    (pow_ne_zero k (Fact.out : p.Prime).ne_zero)]
  simp [Nat.factorization_eq_zero_of_not_dvd hG, Nat.Prime.factorization_pow (Fact.out : p.Prime)]

/-- **`inr(P)` は `Γ = G ⋊ P` の Sylow `p`-部分群** (`p ∤ |G|` のとき). -/
noncomputable def sylowInrRange (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G) :
    Sylow p (G ⋊[φ] P) :=
  Sylow.ofCard (SemidirectProduct.inr : P →* G ⋊[φ] P).range
    (card_inr_range_eq_pow_factorization hP hG)

@[simp] theorem sylowInrRange_coe (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G) :
    (sylowInrRange (φ := φ) hP hG : Subgroup (G ⋊[φ] P)) =
      (SemidirectProduct.inr : P →* G ⋊[φ] P).range := rfl

/-! ### 点安定化群と軌道核 -/

variable (φ)

/-- `g` を固定する `P` の元全体 (点安定化群). -/
def fixSubgroup (g : G) : Subgroup P where
  carrier := {u | (φ u) g = g}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, MulAut.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv]
    conv_lhs => rw [← ha]
    simp

omit [Finite G] [Finite P] in
@[simp] theorem mem_fixSubgroup {g : G} {u : P} : u ∈ fixSubgroup φ g ↔ (φ u) g = g := Iff.rfl

/-- `P`-軌道 `Δ_g = {(φ v) g}` を各点固定する `P` の元全体 (= 軌道への作用の核). -/
def orbitKernel (g : G) : Subgroup P where
  carrier := {u | ∀ v : P, (φ u) ((φ v) g) = (φ v) g}
  one_mem' := by intro v; simp
  mul_mem' := fun {a b} ha hb v => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, MulAut.mul_apply, hb v, ha v]
  inv_mem' := fun {a} ha v => by
    simp only [Set.mem_setOf_eq] at *
    rw [map_inv]
    conv_lhs => rw [← ha v]
    simp

omit [Finite G] [Finite P] in
@[simp] theorem mem_orbitKernel {g : G} {u : P} :
    u ∈ orbitKernel φ g ↔ ∀ v : P, (φ u) ((φ v) g) = (φ v) g := Iff.rfl

omit [Finite G] [Finite P] in
theorem orbitKernel_le_fixSubgroup (g : G) : orbitKernel φ g ≤ fixSubgroup φ g := by
  intro u hu
  simpa using hu 1

/-- 軌道核は `P` で正規. -/
instance orbitKernel_normal (g : G) : (orbitKernel φ g).Normal := by
  refine ⟨fun u hu w => ?_⟩
  intro v
  have hinner : ((φ w)⁻¹ : MulAut G) ((φ v) g) = (φ (w⁻¹ * v)) g := by
    rw [map_mul, map_inv, MulAut.mul_apply]
  rw [map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, hinner, hu (w⁻¹ * v),
    ← hinner]
  simp

variable {φ}

/-! ### Sylow 交叉 = 点安定化群 -/

/-- 共役部分群 `inr(P)^{inl g}` (`= {inl g · y · (inl g)⁻¹}`). -/
abbrev conjInrRange (g : G) : Subgroup (G ⋊[φ] P) :=
  ((SemidirectProduct.inr : P →* G ⋊[φ] P).range).map
    (MulAut.conj (SemidirectProduct.inl g : G ⋊[φ] P)).toMonoidHom

omit [Finite G] [Finite P] in
/-- `inr u` が共役 Sylow `conjInrRange g` に入るのは `(φ u) g = g` のとき. -/
theorem inr_mem_conjInrRange_iff (g : G) (u : P) :
    (SemidirectProduct.inr u : G ⋊[φ] P) ∈ conjInrRange (φ := φ) g ↔ (φ u) g = g := by
  rw [← conj_inr_mem_inr_range_iff (φ := φ) g u]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy' : y = (SemidirectProduct.inl g)⁻¹ * SemidirectProduct.inr u *
        SemidirectProduct.inl g := by
      have hcy : (SemidirectProduct.inl g : G ⋊[φ] P) * y * (SemidirectProduct.inl g)⁻¹
          = SemidirectProduct.inr u := hyx
      rw [← hcy]; group
    rwa [hy'] at hy
  · intro h
    refine ⟨(SemidirectProduct.inl g)⁻¹ * SemidirectProduct.inr u * SemidirectProduct.inl g,
      h, ?_⟩
    change (SemidirectProduct.inl g : G ⋊[φ] P) *
      ((SemidirectProduct.inl g)⁻¹ * SemidirectProduct.inr u * SemidirectProduct.inl g) *
        (SemidirectProduct.inl g)⁻¹ = SemidirectProduct.inr u
    group

omit [Finite G] [Finite P] in
/-- **Sylow 交叉 = 点安定化群**: `inr(P) ⊓ inr(P)^{inl g} = inr(P_g)`. -/
theorem inr_range_inf_conjInrRange_eq (g : G) :
    ((SemidirectProduct.inr : P →* G ⋊[φ] P).range) ⊓ conjInrRange (φ := φ) g
      = (fixSubgroup φ g).map (SemidirectProduct.inr : P →* G ⋊[φ] P) := by
  ext x
  constructor
  · rintro ⟨⟨u, rfl⟩, hconj⟩
    exact ⟨u, (inr_mem_conjInrRange_iff (φ := φ) g u).mp hconj, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, rfl⟩, (inr_mem_conjInrRange_iff (φ := φ) g u).mpr hu⟩


/-! ### ⭐ 軌道核は共役 Sylow でも正規 (欠けていた一手) -/

/-- 正規化群の片側判定 (Ch04 の `le_normalizer_of_forall_conj_mem` と同内容; Ch03 は
Ch04 を import できないので局所版)。 -/
private theorem le_normalizer_of_forall_conj_mem' {Γ : Type*} [Group Γ] {S T : Subgroup Γ}
    (h : ∀ x ∈ S, ∀ z ∈ T, x * z * x⁻¹ ∈ T) : S ≤ Subgroup.normalizer (T : Set Γ) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  refine fun z => ⟨fun hz => h x hx z hz, fun hz => ?_⟩
  have hz' := h x⁻¹ (S.inv_mem hx) _ hz
  have hcancel : x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z := by group
  rwa [hcancel] at hz'

omit [Finite G] [Finite P] in
/-- **⭐ 軌道核 `inr(N)` は共役 Sylow `inr(P)^{inl g}` でも正規** — Isaacs 3A.6 で長く
欠けていた一手 (issue 1055)。

`t = inl g · inr v · (inl g)⁻¹ = inl w · inr v` (`w := g · ((φ v) g)⁻¹`) と書くと
`t · inr m₀ · t⁻¹ = inl (w · ((φ m) w)⁻¹) · inr m` (`m := v m₀ v⁻¹`)。ここで `m` は軌道
`Δ_g` を各点固定するので `g` と `(φ v) g` を固定し, **自己同型ゆえその差 `w` も固定**する。
したがって `t · inr m₀ · t⁻¹ = inr m ∈ inr(N)`。 -/
theorem conjInrRange_le_normalizer_orbitKernel_map (g : G) :
    conjInrRange (φ := φ) g ≤ Subgroup.normalizer
      ((((orbitKernel φ g).map (SemidirectProduct.inr : P →* G ⋊[φ] P)) :
        Subgroup (G ⋊[φ] P)) : Set (G ⋊[φ] P)) := by
  refine le_normalizer_of_forall_conj_mem' ?_
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩ _ ⟨m₀, hm₀, rfl⟩
  have hmK : v * m₀ * v⁻¹ ∈ orbitKernel φ g := (orbitKernel_normal φ g).conj_mem m₀ hm₀ v
  have hm₀' : ∀ u : P, (φ m₀) ((φ u) g) = (φ u) g := hm₀
  have h0 : (φ m₀) g = g := by simpa using hm₀' 1
  have h3 : (φ m₀) ((MulEquiv.symm (φ v)) g) = (MulEquiv.symm (φ v)) g := by
    have h := hm₀' v⁻¹
    rwa [map_inv] at h
  refine ⟨v * m₀ * v⁻¹, hmK, ?_⟩
  ext
  · simp [MulAut.conj_apply, h0, h3, mul_assoc]
  · simp


/-! ### `Γ` の Sylow はすべて `conjInrRange a` の形 -/

omit [Finite G] [Finite P] in
theorem conjInrRange_eq_smul (g : G) :
    conjInrRange (φ := φ) g = MulAut.conj (SemidirectProduct.inl g : G ⋊[φ] P) •
      ((SemidirectProduct.inr : P →* G ⋊[φ] P).range) := rfl

/-- `Γ` の任意の Sylow `p`-部分群は `inr(P)^{inl a}` の形 (`γ = inl γ.left · inr γ.right` と
分解し, `inr γ.right` は `inr(P)` を動かさない)。 -/
theorem exists_eq_conjInrRange (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G)
    (S : Sylow p (G ⋊[φ] P)) :
    ∃ a : G, (S : Subgroup (G ⋊[φ] P)) = conjInrRange (φ := φ) a := by
  obtain ⟨γ, hγ⟩ := MulAction.exists_smul_eq (G ⋊[φ] P) (sylowInrRange (φ := φ) hP hG) S
  obtain ⟨a, b⟩ := γ
  refine ⟨a, ?_⟩
  have hstep : (SemidirectProduct.inr b : G ⋊[φ] P) •
      (sylowInrRange (φ := φ) hP hG) = sylowInrRange (φ := φ) hP hG := by
    refine Sylow.ext ?_
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.conj_smul_eq_self_of_mem ⟨b, rfl⟩
  rw [← hγ, SemidirectProduct.mk_eq_inl_mul_inr b a, mul_smul, hstep,
    Sylow.coe_subgroup_smul, conjInrRange_eq_smul]
  rfl


/-! ### `O_p(Γ) = 1` -/

omit [Finite G] [Finite P] in
/-- `inr(P)` と `C_Γ(inl(G))` の交わりは自明 (`φ` が単射のとき). -/
theorem inr_range_inf_centralizer_eq_bot (hφ : Function.Injective φ) :
    (SemidirectProduct.inr : P →* G ⋊[φ] P).range ⊓
        Subgroup.centralizer (((SemidirectProduct.inl : G →* G ⋊[φ] P).range :
          Subgroup (G ⋊[φ] P)) : Set (G ⋊[φ] P)) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨u, rfl⟩, hcent⟩
  rw [Subgroup.mem_bot]
  have hfix : ∀ g : G, (φ u) g = g := by
    intro g
    have hc := Subgroup.mem_centralizer_iff.mp hcent (SemidirectProduct.inl g) ⟨g, rfl⟩
    have hconj : (SemidirectProduct.inr u : G ⋊[φ] P) * SemidirectProduct.inl g *
        (SemidirectProduct.inr u)⁻¹ = SemidirectProduct.inl ((φ u) g) := by
      rw [← map_inv]
      exact (SemidirectProduct.inl_aut (φ := φ) u g).symm
    have : (SemidirectProduct.inl ((φ u) g) : G ⋊[φ] P) = SemidirectProduct.inl g := by
      rw [← hconj, ← hc]
      group
    exact SemidirectProduct.inl_injective this
  have : φ u = 1 := by
    ext g
    exact hfix g
  have hu1 : u = 1 := hφ (by rw [this, map_one])
  rw [hu1, map_one]

/-- **`O_p(Γ) = 1`** (`Γ = G ⋊ P`, `φ` 忠実, `p ∤ |G|`)。

`O_p(Γ)` は全 Sylow に含まれるので `inr(P)` に入り, `inl(G)` とは位数が互いに素ゆえ
`O_p(Γ) ⊓ inl(G) = 1`。両者正規なので `⁅O_p(Γ), inl(G)⁆ = 1`, すなわち
`O_p(Γ) ≤ C_Γ(inl(G))`。あとは `inr_range_inf_centralizer_eq_bot`。 -/
theorem opCore_semidirectProduct_eq_bot (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G)
    (hφ : Function.Injective φ) :
    OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) = ⊥ := by
  have hYle : OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) ≤
      (SemidirectProduct.inr : P →* G ⋊[φ] P).range :=
    OddOrder.Isaacs.Ch01.opCore_le (sylowInrRange (φ := φ) hP hG)
  -- `O_p(Γ) ⊓ inl(G) = ⊥` (位数が互いに素)
  have hXinf : OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) ⊓
      (SemidirectProduct.inl : G →* G ⋊[φ] P).range = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hOp : IsPGroup p ↥(OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P)) :=
      (isPGroup_inr_range (φ := φ) hP).to_le hYle
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)).mp hOp
    have d1 : Nat.card ↥(OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) ⊓
        (SemidirectProduct.inl : G →* G ⋊[φ] P).range) ∣ p ^ n :=
      hn ▸ Subgroup.card_dvd_of_le inf_le_left
    have d2 : Nat.card ↥(OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) ⊓
        (SemidirectProduct.inl : G →* G ⋊[φ] P).range) ∣ Nat.card G := by
      have hle := Subgroup.card_dvd_of_le
        (inf_le_right : OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) ⊓
          (SemidirectProduct.inl : G →* G ⋊[φ] P).range ≤ _)
      rwa [Nat.card_congr
        (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).symm.toEquiv] at hle
    rcases (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp d1 with ⟨m, hm, hcard⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · simpa using hcard
    · exact absurd ((dvd_pow_self p hpos.ne').trans (hcard ▸ d2)) hG
  -- `O_p(Γ) ≤ C_Γ(inl(G))`
  haveI hXnormal : ((SemidirectProduct.inl : G →* G ⋊[φ] P).range).Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hcent : OddOrder.Isaacs.Ch01.opCore p (G ⋊[φ] P) ≤
      Subgroup.centralizer (((SemidirectProduct.inl : G →* G ⋊[φ] P).range :
        Subgroup (G ⋊[φ] P)) : Set (G ⋊[φ] P)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hXinf]
    exact le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
  rw [eq_bot_iff, ← inr_range_inf_centralizer_eq_bot (φ := φ) hφ]
  exact le_inf hYle hcent


/-! ### Problem 3A.6 本体 -/

/-- 任意の Sylow 対の交叉の位数は, ある `a` について `inr(P) ⊓ conjInrRange a` の位数に等しい. -/
theorem exists_card_inf_eq (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G)
    (S T : Sylow p (G ⋊[φ] P)) :
    ∃ a : G, Nat.card ↥((S : Subgroup (G ⋊[φ] P)) ⊓ (T : Subgroup (G ⋊[φ] P)))
      = Nat.card ↥(((SemidirectProduct.inr : P →* G ⋊[φ] P).range) ⊓
          conjInrRange (φ := φ) a) := by
  obtain ⟨b, hb⟩ := exists_eq_conjInrRange (φ := φ) hP hG S
  obtain ⟨c, hc⟩ := exists_eq_conjInrRange (φ := φ) hP hG T
  refine ⟨b⁻¹ * c, ?_⟩
  have hsplit : (SemidirectProduct.inl c : G ⋊[φ] P)
      = SemidirectProduct.inl b * SemidirectProduct.inl (b⁻¹ * c) := by
    rw [← map_mul]; congr 1; group
  rw [hb, hc, conjInrRange_eq_smul, conjInrRange_eq_smul, conjInrRange_eq_smul, hsplit,
    map_mul, mul_smul, ← Subgroup.smul_inf]
  exact Nat.card_congr (Subgroup.equivSMul _ _).symm.toEquiv

/-- **Isaacs Problem 3A.6**: `p`-群 `P` が `p ∤ |G|` の群 `G` に**忠実に**自己同型で作用する
なら, ある `P`-軌道 `Δ_g` の上でも `P` は忠実に作用する。

`Γ = G ⋊ P` の中で `|inr(P) ⊓ inr(P)^{inl g}|` を最小にする `g` を取ると, これは `Γ` の
**包含極小 Sylow 交叉** (`exists_card_inf_eq` で任意の対の交叉位数がこの形の値になるから)。
軌道核 `inr(N)` はその交叉に含まれ, `inr(P)` と `inr(P)^{inl g}` の**両方で正規**
(`conjInrRange_le_normalizer_orbitKernel_map` ⭐) なので **Thm 1.38** より
`inr(N) ≤ O_p(Γ) = 1`。 -/
theorem exists_faithful_orbit (hP : IsPGroup p P) (hG : ¬ p ∣ Nat.card G)
    (hφ : Function.Injective φ) :
    ∃ g : G, ∀ u : P, (∀ v : P, (φ u) ((φ v) g) = (φ v) g) → u = 1 := by
  classical
  haveI : Nonempty G := ⟨1⟩
  set F : G → ℕ := fun a => Nat.card ↥(((SemidirectProduct.inr : P →* G ⋊[φ] P).range) ⊓
    conjInrRange (φ := φ) a) with hF
  obtain ⟨g, hgmin⟩ : ∃ g : G, ∀ a : G, F g ≤ F a :=
    ⟨Function.argmin F, fun a => Function.argmin_le F a⟩
  refine ⟨g, fun u hu => ?_⟩
  set Y : Sylow p (G ⋊[φ] P) := sylowInrRange (φ := φ) hP hG with hY
  set T : Sylow p (G ⋊[φ] P) := (SemidirectProduct.inl g : G ⋊[φ] P) • Y with hTdef
  have hTcoe : (T : Subgroup (G ⋊[φ] P)) = conjInrRange (φ := φ) g := by
    rw [hTdef, Sylow.coe_subgroup_smul, conjInrRange_eq_smul]; rfl
  have hYcoe : (Y : Subgroup (G ⋊[φ] P)) = (SemidirectProduct.inr : P →* G ⋊[φ] P).range := rfl
  -- 包含極小性
  have hmin : ∀ S' T' : Sylow p (G ⋊[φ] P),
      (S' : Subgroup (G ⋊[φ] P)) ⊓ (T' : Subgroup (G ⋊[φ] P)) ≤
        (Y : Subgroup (G ⋊[φ] P)) ⊓ (T : Subgroup (G ⋊[φ] P)) →
      (S' : Subgroup (G ⋊[φ] P)) ⊓ (T' : Subgroup (G ⋊[φ] P)) =
        (Y : Subgroup (G ⋊[φ] P)) ⊓ (T : Subgroup (G ⋊[φ] P)) := by
    intro S' T' hle
    obtain ⟨a, ha⟩ := exists_card_inf_eq (φ := φ) hP hG S' T'
    refine (Subgroup.eq_of_le_of_card_ge hle ?_)
    rw [ha, hYcoe, hTcoe]
    exact hgmin a
  -- 軌道核の像
  set K : Subgroup (G ⋊[φ] P) :=
    (orbitKernel φ g).map (SemidirectProduct.inr : P →* G ⋊[φ] P) with hK
  have hKle : K ≤ (Y : Subgroup (G ⋊[φ] P)) ⊓ (T : Subgroup (G ⋊[φ] P)) := by
    rw [hYcoe, hTcoe, inr_range_inf_conjInrRange_eq]
    exact Subgroup.map_mono (orbitKernel_le_fixSubgroup φ g)
  have hYN : (Y : Subgroup (G ⋊[φ] P)) ≤ Subgroup.normalizer (K : Set (G ⋊[φ] P)) := by
    rw [hYcoe]
    refine le_normalizer_of_forall_conj_mem' ?_
    rintro _ ⟨v, rfl⟩ _ ⟨m, hm, rfl⟩
    exact ⟨v * m * v⁻¹, (orbitKernel_normal φ g).conj_mem m hm v, by
      rw [map_mul, map_mul, map_inv]⟩
  have hTN : (T : Subgroup (G ⋊[φ] P)) ≤ Subgroup.normalizer (K : Set (G ⋊[φ] P)) := by
    rw [hTcoe]
    exact conjInrRange_le_normalizer_orbitKernel_map g
  have hKop := OddOrder.Isaacs.Ch01.opCore_eq_inf_of_minimal_sylow_inter Y T hmin hKle hYN hTN
  rw [opCore_semidirectProduct_eq_bot (φ := φ) hP hG hφ, le_bot_iff] at hKop
  have hbot : orbitKernel φ g = ⊥ := by
    have hle := (Subgroup.map_eq_bot_iff _).mp hKop
    have hker : (SemidirectProduct.inr : P →* G ⋊[φ] P).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr SemidirectProduct.inr_injective
    rwa [hker, le_bot_iff] at hle
  have : u ∈ orbitKernel φ g := hu
  rwa [hbot, Subgroup.mem_bot] at this


end

end OddOrder.Isaacs.Ch03
