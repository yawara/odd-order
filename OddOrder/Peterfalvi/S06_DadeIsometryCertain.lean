/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S05_TICyclic

/-!
# Peterfalvi §6: The Dade Isometry for a Certain Type of Subgroup

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
§6, pp. 21-24.

This module contains:

* **Hypothesis (4.2)** over an abstract group `L` (`S06.Hypothesis`): the
  "certain type" of group `L = K ⋊ W₁` with `W₁ ≠ 1` a cyclic Hall complement,
  `W₂ = C_K(x)` cyclic for all `x ∈ W₁^#`, and `W = W₁ × W₂` of odd order —
  together with its elementary structure theory (the join `W = W₁ ⊔ W₂` is
  abelian, the `W₁`/`W₂`-components of its elements, the Bézout component
  projection).
* the carrier structures for the §6 Dade applications
  (`CertainTypeHypothesis`, which extends the abstract hypothesis for `↥L`
  with a §4 Dade datum on `(G, A, L)`, plus `DadeApplication` /
  `FullDadeApplication`).  These deliberately reuse the §4 bundled Dade data
  instead of creating a second isometry interface.

Reference note: `notes/peterfalvi/s06_dade_certain_subgroup.md`.
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

/- 4: Dade isometry for a certain type of subgroup (pp. 21-24) -/

/- 4.2: the certain-type structural hypothesis (mmd 04.6 L9-L13) -/

/-- Two elements of a cyclic subgroup commute.  (Generic; upstream candidate
`Subgroup.commute_of_mem_of_isCyclic`.) -/
theorem commute_of_mem_of_isCyclic {L : Type*} [Group L] {H : Subgroup L}
    (hH : IsCyclic H) {x y : L} (hx : x ∈ H) (hy : y ∈ H) : Commute x y := by
  haveI := hH
  have hcomm : (⟨x, hx⟩ : H) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ :=
    commutative_of_cyclic_center_quotient (MonoidHom.id H)
      (fun z hz => by
        rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hz
        rw [hz]
        exact Subgroup.one_mem _)
      ⟨x, hx⟩ ⟨y, hy⟩
  exact Subtype.ext_iff.mp hcomm

/-- **Peterfalvi Hypothesis (4.2)** (mmd 04.6 L9-L13), over an abstract group `L`.

* (a) `L = K ⋊ W₁`: `K ⊴ L` with complement `W₁ ≠ 1`, cyclic and **Hall** — by the
  complement decomposition the index of `W₁` is `|K|`, so the Hall property is recorded
  as the coprimality `gcd(|K|, |W₁|) = 1` (`card_coprime`).
* (b) `W₂ ≠ 1` is a cyclic subgroup of `K` with `C_K(x) = W₂` for all `x ∈ W₁^#`.
* (c) `W = W₁ × W₂` is of odd order.  `W` is encoded as the join `W₁ ⊔ W₂`;
  `W₁ ⊓ W₂ = ⊥` is automatic (`W_disjoint`), the join is abelian
  (`isMulCommutative_sup`), and its elements decompose as products
  (`exists_mul_of_mem_sup`), so the join is the internal direct product `W₁ × W₂`.

The ambient group of the §6 results (4.3)-(4.5) is `L` itself; the `G`-embedded variant
used from §8 on is `CertainTypeHypothesis`, which extends this structure with a §4 Dade
datum. -/
structure Hypothesis (L : Type*) [Group L] where
  /-- The normal "kernel" subgroup `K` of `L = K ⋊ W₁`. -/
  K : Subgroup L
  W1 : Subgroup L
  W2 : Subgroup L
  K_normal : K.Normal
  /-- (4.2)(a): `L = K ⋊ W₁` — `W₁` is a complement to the normal subgroup `K`. -/
  isComplement : Subgroup.IsComplement' K W1
  /-- (4.2)(a): `W₁ ≠ 1` is cyclic. -/
  W1_nontrivial : W1 ≠ ⊥
  W1_cyclic : IsCyclic W1
  /-- (4.2)(a): `W₁` is a **Hall** subgroup of `L`: by the complement `L = K·W₁` the
  index of `W₁` is `|K|`, so Hall-ness is the coprimality of `|K|` and `|W₁|`. -/
  card_coprime : Nat.Coprime (Nat.card K) (Nat.card W1)
  /-- (4.2)(b): `W₂ ≠ 1` is a cyclic subgroup of `K`. -/
  W2_nontrivial : W2 ≠ ⊥
  W2_cyclic : IsCyclic W2
  W2_le_K : W2 ≤ K
  /-- (4.2)(b): `C_K(x) = W₂` for every `x ∈ W₁^#`. -/
  centralizer_W2 : ∀ x : L, x ∈ W1 → x ≠ 1 →
    Subgroup.centralizer ({x} : Set L) ⊓ K = W2
  /-- (4.2)(c): `W = W₁ × W₂` has odd order. -/
  W_odd : Odd (Nat.card ↥(W1 ⊔ W2))

namespace Hypothesis

variable {L : Type*} [Group L] (h : Hypothesis L)

/-- `W₁ ⊓ W₂ = ⊥`: automatic from the complement (`W₁ ⊓ K = ⊥`) and `W₂ ≤ K`. -/
theorem W_disjoint : Disjoint h.W1 h.W2 :=
  h.isComplement.disjoint.symm.mono_right h.W2_le_K

/-- (4.2)(b) elementwise: `W₂` centralizes `W₁`.  For `x ≠ 1` this is `W₂ ≤ C_K(x)` from
`centralizer_W2`; for `x = 1` it is trivial. -/
theorem commute_of_mem_W1_of_mem_W2 {x y : L} (hx : x ∈ h.W1) (hy : y ∈ h.W2) :
    Commute x y := by
  rcases eq_or_ne x 1 with rfl | hx1
  · exact Commute.one_left y
  · have hyc : y ∈ Subgroup.centralizer ({x} : Set L) ⊓ h.K := by
      rw [h.centralizer_W2 x hx hx1]; exact hy
    exact Subgroup.mem_centralizer_iff.mp hyc.1 x rfl

/-- The Hall coprimality (4.2.a) descends along `W₂ ≤ K`: `gcd(|W₁|, |W₂|) = 1`. -/
theorem coprime_card_W1_card_W2 : Nat.Coprime (Nat.card h.W1) (Nat.card h.W2) :=
  Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le h.W2_le_K)
    h.card_coprime.symm

/-- `W = W₁ ⊔ W₂` is abelian: `W₁` and `W₂` are abelian (cyclic) and centralize each
other (`commute_of_mem_W1_of_mem_W2`), so the closure of `↑W₁ ∪ ↑W₂` is abelian. -/
theorem isMulCommutative_sup : IsMulCommutative ↥(h.W1 ⊔ h.W2) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (commute_of_mem_of_isCyclic h.W1_cyclic hx hy).eq
  · exact (h.commute_of_mem_W1_of_mem_W2 hx hy).eq
  · exact ((h.commute_of_mem_W1_of_mem_W2 hy hx).symm).eq
  · exact (commute_of_mem_of_isCyclic h.W2_cyclic hx hy).eq

/-- `W₁` and `W₂`, viewed inside `W = W₁ ⊔ W₂`, intersect trivially. -/
theorem W1_subgroupOf_inf_W2_subgroupOf_eq_bot :
    h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊓ h.W2.subgroupOf (h.W1 ⊔ h.W2) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
  have hxbot : (x : L) ∈ h.W1 ⊓ h.W2 := hx
  rw [disjoint_iff.mp h.W_disjoint, Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxbot

/-- `W₁` and `W₂`, viewed inside `W = W₁ ⊔ W₂`, generate it. -/
theorem W1_subgroupOf_sup_W2_subgroupOf_eq_top :
    h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊔ h.W2.subgroupOf (h.W1 ⊔ h.W2) = ⊤ := by
  rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]

open scoped IsMulCommutative in
/-- Every element of `W = W₁ ⊔ W₂` is a product `x·y` with `x ∈ W₁`, `y ∈ W₂` (the join
is abelian, so it is the internal product of `W₁` and `W₂`). -/
theorem exists_mul_of_mem_sup {w : L} (hw : w ∈ h.W1 ⊔ h.W2) :
    ∃ x ∈ h.W1, ∃ y ∈ h.W2, x * y = w := by
  haveI := h.isMulCommutative_sup
  have hmem : (⟨w, hw⟩ : ↥(h.W1 ⊔ h.W2)) ∈
      h.W1.subgroupOf (h.W1 ⊔ h.W2) ⊔ h.W2.subgroupOf (h.W1 ⊔ h.W2) := by
    rw [h.W1_subgroupOf_sup_W2_subgroupOf_eq_top]
    exact Subgroup.mem_top _
  rw [Subgroup.mem_sup] at hmem
  obtain ⟨x, hx, y, hy, hxy⟩ := hmem
  rw [Subgroup.mem_subgroupOf] at hx hy
  exact ⟨x, hx, y, hy, Subtype.ext_iff.mp hxy⟩

/-- A uniform integer exponent projecting products onto their `W₁`-component: there is
`n` with `(x·y)^n = x` for all `x ∈ W₁`, `y ∈ W₂`.  Bézout for `gcd(|W₁|, |W₂|) = 1`
gives `n ≡ 1 mod |W₁|` and `n ≡ 0 mod |W₂|`, and commutation
(`commute_of_mem_W1_of_mem_W2`) splits the power.  This recovers the `W₁`-component of
an element of `W` intrinsically — in particular compatibly with conjugation — which is
the engine of the TI argument in (4.3.a). -/
theorem exists_zpow_proj :
    ∃ n : ℤ, ∀ x ∈ h.W1, ∀ y ∈ h.W2, (x * y) ^ n = x := by
  set c₁ := Nat.card h.W1 with hc₁
  set c₂ := Nat.card h.W2 with hc₂
  have hbez : (c₁ : ℤ) * Nat.gcdA c₁ c₂ + c₂ * Nat.gcdB c₁ c₂ = 1 := by
    have hg := Nat.gcd_eq_gcd_ab c₁ c₂
    have h1 : Nat.gcd c₁ c₂ = 1 := h.coprime_card_W1_card_W2
    rw [h1] at hg
    exact_mod_cast hg.symm
  refine ⟨(c₂ : ℤ) * Nat.gcdB c₁ c₂, fun x hx y hy => ?_⟩
  have hcomm := h.commute_of_mem_W1_of_mem_W2 hx hy
  have hx1 : x ^ (c₁ : ℤ) = 1 := by
    rw [zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hx)
  have hy1 : y ^ (c₂ : ℤ) = 1 := by
    rw [zpow_natCast]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hy)
  rw [hcomm.mul_zpow]
  have hyn : y ^ ((c₂ : ℤ) * Nat.gcdB c₁ c₂) = 1 := by
    rw [zpow_mul, hy1, one_zpow]
  have hxn : x ^ ((c₂ : ℤ) * Nat.gcdB c₁ c₂) = x := by
    have hn : (c₂ : ℤ) * Nat.gcdB c₁ c₂ = 1 - c₁ * Nat.gcdA c₁ c₂ := by
      linarith [hbez]
    rw [hn, zpow_sub, zpow_one, zpow_mul, hx1, one_zpow, inv_one, mul_one]
  rw [hxn, hyn, mul_one]

end Hypothesis

section CertainType

variable {G : Type*} [Group G] [Fintype G]
variable {A : Set G} {L : Subgroup G}

/-- The structural hypotheses used by Peterfalvi §6 before the concrete
character calculations begin, embedded in an ambient group `G`: the abstract
Hypothesis (4.2) for the subgroup `↥L` (fields `K`, `W1`, `W2`, … of the parent
`Hypothesis ↥L`), together with the §4 Dade datum on `(G, A, L)` that maps
class functions of `L` into `G`. -/
structure CertainTypeHypothesis (A : Set G) (L : Subgroup G) extends
    Hypothesis ↥L where
  dade : OddOrder.Peterfalvi.S04.Hypothesis G A L

namespace CertainTypeHypothesis

variable {k : Type*} [CommRing k] [StarRing k]
variable [Fintype L] [Invertible (Nat.card G : k)] [Invertible (Nat.card L : k)]

/-- A §6 application package: the structural §6 hypothesis plus a Dade map
known to satisfy the §4 pointwise and isometry interfaces. -/
structure DadeApplication (hyp : CertainTypeHypothesis (G := G) A L) where
  tau : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.dade

instance (hyp : CertainTypeHypothesis (G := G) A L) :
    CoeFun (DadeApplication (G := G) (k := k) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem coe_mk (hyp : CertainTypeHypothesis (G := G) A L)
    (tau : OddOrder.Peterfalvi.S04.DadeIsometryData (G := G) (k := k) hyp.dade) :
    ((DadeApplication.mk tau : DadeApplication (G := G) (k := k) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) k A L) = tau.toDadeMap :=
  rfl

theorem map_eq_of_mem_hCoset {hyp : CertainTypeHypothesis (G := G) A L}
    (app : DadeApplication (G := G) (k := k) hyp)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) k A L)
    (a : {a : G // a ∈ A}) {g : G} (hg : g ∈ hyp.dade.hCoset a) :
    app.tau.toDadeMap α g =
      (α : ClassFunction L k) ⟨a.1, hyp.dade.mem_L a.2⟩ :=
  OddOrder.Peterfalvi.S04.IsDadeMap.map_eq_of_mem_hCoset
    app.tau.isDadeMap α a hg

theorem map_eq_zero_of_not_mem_dadeSupport {hyp : CertainTypeHypothesis (G := G) A L}
    (app : DadeApplication (G := G) (k := k) hyp)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) k A L)
    {g : G} (hg : g ∉ hyp.dade.dadeSupport) :
    app.tau.toDadeMap α g = 0 :=
  app.tau.isDadeMap.map_eq_zero_of_not_mem_dadeSupport α g hg

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card L : ℂ)]

/-- A complex §6 application package including the virtual-character part of
the §4 Dade isometry theorem. -/
structure FullDadeApplication (hyp : CertainTypeHypothesis (G := G) A L) where
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp.dade

instance (hyp : CertainTypeHypothesis (G := G) A L) :
    CoeFun (FullDadeApplication (G := G) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem full_coe_mk (hyp : CertainTypeHypothesis (G := G) A L)
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) hyp.dade) :
    ((FullDadeApplication.mk tau : FullDadeApplication (G := G) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ A L) = tau.toDadeMap :=
  rfl

theorem full_map_eq_of_mem_hCoset {hyp : CertainTypeHypothesis (G := G) A L}
    (app : FullDadeApplication (G := G) hyp)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
    (a : {a : G // a ∈ A}) {g : G} (hg : g ∈ hyp.dade.hCoset a) :
    app.tau.toDadeMap α g =
      (α : ClassFunction L ℂ) ⟨a.1, hyp.dade.mem_L a.2⟩ :=
  OddOrder.Peterfalvi.S04.IsDadeMap.map_eq_of_mem_hCoset
    app.tau.toDadeIsometryData.isDadeMap α a hg

theorem full_map_eq_zero_of_not_mem_dadeSupport
    {hyp : CertainTypeHypothesis (G := G) A L}
    (app : FullDadeApplication (G := G) hyp)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
    {g : G} (hg : g ∉ hyp.dade.dadeSupport) :
    app.tau.toDadeMap α g = 0 :=
  app.tau.toDadeIsometryData.isDadeMap.map_eq_zero_of_not_mem_dadeSupport α g hg

theorem full_inner_eq {hyp : CertainTypeHypothesis (G := G) A L}
    (app : FullDadeApplication (G := G) hyp)
    (α β : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L) :
    ClassFunction.inner (app.tau.toDadeMap α) (app.tau.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction L ℂ) (β : ClassFunction L ℂ) :=
  app.tau.inner_eq α β

theorem full_maps_virtualCharacter {hyp : CertainTypeHypothesis (G := G) A L}
    (app : FullDadeApplication (G := G) hyp)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A L)
    (hα : (α : ClassFunction L ℂ) ∈ ZIrr L) :
    app.tau.toDadeMap α ∈ ZIrr G :=
  app.tau.maps_virtualCharacter α hα

end CertainTypeHypothesis

end CertainType

end OddOrder.Peterfalvi.S06
