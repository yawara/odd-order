/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.BrauerSuzukiTISubset
import OddOrder.GroupTheory.RepresentationTheory.LinearCharacter
import OddOrder.GroupTheory.RepresentationTheory.CliffordCorrespondence

/-!
# Brauer–Suzuki: the character `θ` on `N` (Gorenstein Ch. 12, Lemma 1.4)

**Gorenstein, *Finite Groups*, Ch. 12, Lemma 1.4** (p. 375): in the
`QuaternionSylowSetup` (issue 9318), with `C = C_G(T)`, `N = N_G(T)`, `A = C − RH`
the TI-subset of Lemma 1.3, let `ψ` be a linear character of `C` with `RH ⊆ ker ψ`
and `ψ(x) = i` (a faithful character of the cyclic quotient `C/RH ≅ ℤ/4`).  Let

`θ = Ind_C^N 1_C − Ind_C^N ψ`.

Then (i) `(θ, θ)_N = 3`, (ii) `θ(1) = 0`, and (iii) `θ` vanishes on `N − A`.

This file develops the pieces in the book's order:

* **Structural prerequisites** — `x² ∉ RH`, `y ∈ N ∖ C`, the coset decomposition
  `N = C ∪ yC`, and hence `[N : C] = 2`.
* **The linear character `ψ`** — built from the faithful character `x̄ ↦ i` of the
  order-`4` cyclic quotient `C/RH`, pulled back to `C` (`psiHom`, `psi`).
* **The virtual character `θ`** and its degree, support, and norm.
-/

namespace OddOrder.GroupTheory

/-- **Integer triples of squared norm `3`**: if `∑_{a∈s} cₐ² = 3` with all `cₐ ≠ 0`, then `s`
has exactly three elements and each coefficient is `±1`.  (The norm-`3` analogue of
`exists_pair_of_sum_sq_eq_two`; could move to `ZIrrFourier` upstream.) -/
theorem exists_triple_of_sum_sq_eq_three {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℤ}
    (hne : ∀ a ∈ s, c a ≠ 0) (hsum : ∑ a ∈ s, c a ^ 2 = 3) :
    ∃ α β γ : ι, α ≠ β ∧ α ≠ γ ∧ β ≠ γ ∧ s = {α, β, γ} ∧
      (c α = 1 ∨ c α = -1) ∧ (c β = 1 ∨ c β = -1) ∧ (c γ = 1 ∨ c γ = -1) := by
  classical
  have hsq2 : ∀ n : ℤ, n ^ 2 ≠ 2 := by
    intro n hn
    have h1 : (n - 1) * (n + 1) = 1 := by linear_combination hn
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h1 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> omega
  have hsq3 : ∀ n : ℤ, n ^ 2 ≠ 3 := by
    intro n hn
    have hb1 : n < 2 := by nlinarith [sq_nonneg (n - 2)]
    have hb2 : -2 < n := by nlinarith [sq_nonneg (n + 2)]
    interval_cases n <;> norm_num at hn
  have hge : ∀ a ∈ s, 1 ≤ c a ^ 2 := fun a ha => by
    have h := Int.one_le_abs (hne a ha)
    calc (1 : ℤ) = 1 ^ 2 := by ring
      _ ≤ |c a| ^ 2 := by gcongr
      _ = c a ^ 2 := sq_abs (c a)
  have hcard3 : s.card ≤ 3 := by
    have hle : (s.card : ℤ) ≤ ∑ a ∈ s, c a ^ 2 := by
      calc (s.card : ℤ) = ∑ _a ∈ s, (1 : ℤ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ∑ a ∈ s, c a ^ 2 := Finset.sum_le_sum hge
    rw [hsum] at hle; omega
  have hcard : s.card = 3 := by
    by_contra hne3
    have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    rcases hcases with hc | hc | hc
    · rw [Finset.card_eq_zero] at hc; subst hc; simp at hsum
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      rw [Finset.sum_singleton] at hsum; exact hsq3 (c a) hsum
    · obtain ⟨α, β, hαβ, rfl⟩ := Finset.card_eq_two.mp hc
      rw [Finset.sum_pair hαβ] at hsum
      have h1 := hge α (by simp); have h2 := hge β (by simp)
      rcases (by omega : c α ^ 2 = 1 ∨ c α ^ 2 = 2) with h | h
      · exact hsq2 (c β) (by omega)
      · exact hsq2 (c α) h
  obtain ⟨α, β, γ, hαβ, hαγ, hβγ, rfl⟩ := Finset.card_eq_three.mp hcard
  have hαmem : α ∉ ({β, γ} : Finset ι) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hαβ, hαγ⟩
  have hβmem : β ∉ ({γ} : Finset ι) := by
    simp only [Finset.mem_singleton]; exact hβγ
  rw [Finset.sum_insert hαmem, Finset.sum_insert hβmem, Finset.sum_singleton] at hsum
  have h1 := hge α (by simp); have h2 := hge β (by simp); have h3 := hge γ (by simp)
  have hcα : c α ^ 2 = 1 := by omega
  have hcβ : c β ^ 2 = 1 := by omega
  have hcγ : c γ ^ 2 = 1 := by omega
  refine ⟨α, β, γ, hαβ, hαγ, hβγ, rfl, ?_, ?_, ?_⟩
  · rw [pow_two] at hcα; exact mul_self_eq_one_iff.mp hcα
  · rw [pow_two] at hcβ; exact mul_self_eq_one_iff.mp hcβ
  · rw [pow_two] at hcγ; exact mul_self_eq_one_iff.mp hcγ

namespace QuaternionSylowSetup

open Subgroup
open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G] (Q : QuaternionSylowSetup G)

/-! ### Structural prerequisites: `[N : C] = 2` -/

/-- **`x² ∉ RH`** (mirror of `x_notMem_RH`): `orderOf x² = 2ⁿ⁻¹` but `R = ⟨x⁴⟩` has
order `2ⁿ⁻²`, so `x² ∉ R`, and `X ∩ RH = R`. -/
theorem x_sq_notMem_RH : Q.x ^ (2 : ℕ) ∉ Q.RH := by
  intro hx
  have hxZ : Q.x ^ ((2 : ℕ) : ℤ) ∈ Q.RH := by rwa [zpow_natCast]
  have hxR : Q.x ^ ((2 : ℕ) : ℤ) ∈ Q.R := Q.mem_R_of_mem_X_of_mem_RH hxZ
  have hxR' : Q.x ^ (2 : ℕ) ∈ Q.R := by rwa [zpow_natCast] at hxR
  have hdvd : orderOf (Q.x ^ (2 : ℕ)) ∣ Nat.card Q.R := by
    have h1 := orderOf_dvd_natCard (⟨Q.x ^ (2 : ℕ), hxR'⟩ : Q.R)
    rwa [← orderOf_injective Q.R.subtype Q.R.subtype_injective ⟨_, hxR'⟩] at h1
  rw [Q.orderOf_x_sq, Q.card_R] at hdvd
  have hle := Nat.le_of_dvd (by positivity) hdvd
  have h2 : (2 : ℕ) ^ (Q.n - 2) < 2 ^ (Q.n - 1) :=
    Nat.pow_lt_pow_right one_lt_two (by have := Q.hn; omega)
  omega

/-- `y ∈ N` (`y ∈ S ≤ N`). -/
theorem y_mem_N : Q.y ∈ Q.N := Q.S_le_N Q.hyS

/-- `y ∉ C` (else `y ∈ S ∩ C = X`, contradicting `y ∉ ⟨x⟩`). -/
theorem y_notMem_C : Q.y ∉ Q.C := by
  intro hy
  have hyX : Q.y ∈ Q.X := by
    have hmem : Q.y ∈ (Q.S : Subgroup G) ⊓ Q.C := ⟨Q.hyS, hy⟩
    rwa [Q.S_inf_C_eq_X] at hmem
  exact Q.y_notMem_zpowers_x hyX

/-- `y² ∈ C` (`y² = x^{2ⁿ⁻¹} ∈ X ≤ C`). -/
theorem y_sq_mem_C : Q.y ^ 2 ∈ Q.C := by
  rw [Q.hy_sq]
  exact Q.X_le_C (Q.mem_X_iff.mpr ⟨((2 ^ (Q.n - 1) : ℕ) : ℤ), (zpow_natCast Q.x _).symm⟩)

/-- `y⁻¹·c·y ∈ C` for `c ∈ C` (`y ∈ N` normalizes `C`). -/
theorem yinv_conj_mem_C {c : G} (hc : c ∈ Q.C) : Q.y⁻¹ * c * Q.y ∈ Q.C := by
  have h := Q.conj_mem_C_of_mem_N (inv_mem Q.y_mem_N) hc
  rwa [inv_inv] at h

/-- **The coset decomposition `N = C ∪ yC`** (Gorenstein p. 375): every element of `N`
lies in `C` or in `y·C`.  Proved by exhibiting `C ∪ yC` as a subgroup (using `y ∈ N`
normalizes `C` and `y² ∈ C`) that contains `x`, `y`, and `H`, hence `S ⊔ H = N`. -/
theorem mem_C_or_yinv_mul_mem_C {n : G} (hn : n ∈ Q.N) :
    n ∈ Q.C ∨ Q.y⁻¹ * n ∈ Q.C := by
  -- closure of the disjunctive predicate under multiplication (stated as a genuine `Or`)
  have key : ∀ {a b : G}, (a ∈ Q.C ∨ Q.y⁻¹ * a ∈ Q.C) →
      (b ∈ Q.C ∨ Q.y⁻¹ * b ∈ Q.C) → (a * b ∈ Q.C ∨ Q.y⁻¹ * (a * b) ∈ Q.C) := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (mul_mem ha hb)
    · refine Or.inr ?_
      rw [show Q.y⁻¹ * (a * b) = (Q.y⁻¹ * a * Q.y) * (Q.y⁻¹ * b) from by group]
      exact mul_mem (Q.yinv_conj_mem_C ha) hb
    · refine Or.inr ?_
      rw [show Q.y⁻¹ * (a * b) = (Q.y⁻¹ * a) * b from by group]
      exact mul_mem ha hb
    · refine Or.inl ?_
      rw [show a * b = Q.y ^ 2 * (Q.y⁻¹ * (Q.y⁻¹ * a) * Q.y) * (Q.y⁻¹ * b) from by
        rw [sq]; group]
      exact mul_mem (mul_mem Q.y_sq_mem_C (Q.yinv_conj_mem_C ha)) hb
  -- the subgroup `K = C ∪ yC`
  let K : Subgroup G :=
    { carrier := {g | g ∈ Q.C ∨ Q.y⁻¹ * g ∈ Q.C}
      one_mem' := Or.inl (one_mem _)
      mul_mem' := fun ha hb => key ha hb
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (inv_mem ha)
        · refine Or.inr ?_
          rw [show Q.y⁻¹ * a⁻¹ = (Q.y⁻¹ * (Q.y⁻¹ * a) * Q.y)⁻¹ * (Q.y ^ 2)⁻¹ from by
            rw [sq]; group]
          exact mul_mem (inv_mem (Q.yinv_conj_mem_C ha)) (inv_mem Q.y_sq_mem_C) }
  -- `K` contains `x`, `y`, `H`, hence `S = closure{x,y}` and `H`, hence `N = S ⊔ H`.
  have hxK : Q.x ∈ K := Or.inl Q.x_mem_C
  have hyK : Q.y ∈ K := Or.inr (by rw [inv_mul_cancel]; exact one_mem _)
  have hSK : (Q.S : Subgroup G) ≤ K := by
    rw [← Q.hclosure, closure_le]
    rintro g (rfl | rfl)
    · exact hxK
    · exact hyK
  have hHK : Q.H ≤ K := fun h hh => Or.inl (Q.H_le_C hh)
  have hNK : Q.N ≤ K := by rw [← Q.S_sup_H_eq_N]; exact sup_le hSK hHK
  exact hNK hn

/-- **`[N : C] = 2`** (Gorenstein p. 375): `C ⊴ N` with quotient of order `2`, via the
coset decomposition `N = C ∪ yC` and `Subgroup.index_eq_two_iff'`. -/
theorem index_C_subgroupOf_N : (Q.C.subgroupOf Q.N).index = 2 := by
  rw [Subgroup.index_eq_two_iff']
  refine ⟨⟨Q.y, Q.y_mem_N⟩, fun b => ?_⟩
  have hcoe : (((⟨Q.y, Q.y_mem_N⟩ : ↥Q.N) * b : ↥Q.N) : G) = Q.y * (b : G) := rfl
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcoe]
  -- goal : `Xor' (y·↑b ∈ C) (↑b ∈ C)`
  rcases Q.mem_C_or_yinv_mul_mem_C b.2 with hb | hb
  · -- `↑b ∈ C` ⟹ `y·↑b ∉ C`
    exact Or.inr ⟨hb, fun hyb => Q.y_notMem_C (by
      rw [show Q.y = (Q.y * (b : G)) * (b : G)⁻¹ from by group]
      exact mul_mem hyb (inv_mem hb))⟩
  · -- `y⁻¹·↑b ∈ C` ⟹ `y·↑b ∈ C` and `↑b ∉ C`
    have hyb : Q.y * (b : G) ∈ Q.C := by
      rw [show Q.y * (b : G) = Q.y ^ 2 * (Q.y⁻¹ * (b : G)) from by rw [sq]; group]
      exact mul_mem Q.y_sq_mem_C hb
    exact Or.inl ⟨hyb, fun hbC => Q.y_notMem_C (by
      rw [show Q.y = (Q.y * (b : G)) * (b : G)⁻¹ from by group]
      exact mul_mem hyb (inv_mem hbC))⟩

/-! ### The linear character `ψ` of `C` (faithful on `C/RH ≅ ℤ/4`) -/

/-- `x` viewed as an element of `C`. -/
def xC : ↥Q.C := ⟨Q.x, Q.x_mem_C⟩

@[simp] theorem coe_xC : (Q.xC : G) = Q.x := rfl

/-- `RH ⊴ C` (as `C ≤ N` and `RH ⊴ N`). -/
instance : (Q.RH.subgroupOf Q.C).Normal := by
  refine ⟨fun a ha c => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have hcN : (c : G) ∈ Q.N := Q.C_le_N c.2
  have h := Q.conj_mem_RH_of_mem_N hcN ha
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h

theorem coe_xC_pow (k : ℕ) : ((Q.xC ^ k : ↥Q.C) : G) = Q.x ^ k := by
  rw [SubgroupClass.coe_pow, coe_xC]

/-- `(x̄)ᵏ = x^k` in `C/RH` (the quotient map is a homomorphism). -/
theorem mk_xC_pow (k : ℕ) :
    (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) ^ k = QuotientGroup.mk (Q.xC ^ k) := by
  rw [← QuotientGroup.mk'_apply, ← map_pow, QuotientGroup.mk'_apply]

/-- `x⁴ ∈ RH` (`x⁴ ∈ R ≤ RH`), so `(x̄)⁴ = 1` in `C/RH`. -/
theorem mk_xC_pow_four :
    (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) ^ 4 = 1 := by
  rw [Q.mk_xC_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_xC_pow]
  exact Q.R_le_RH (show Q.x ^ (4 : ℕ) ∈ Q.R from mem_zpowers _)

/-- `x² ∉ RH`, so `(x̄)² ≠ 1` in `C/RH`. -/
theorem mk_xC_sq_ne_one :
    (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) ^ 2 ≠ 1 := by
  rw [Q.mk_xC_pow, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, coe_xC_pow]
  exact Q.x_sq_notMem_RH

/-- **`orderOf x̄ = 4` in `C/RH`**: `(x̄)⁴ = 1` but `(x̄)² ≠ 1`. -/
theorem orderOf_mk_xC :
    orderOf (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) = 4 := by
  have hdvd : orderOf (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
    exact orderOf_dvd_of_pow_eq_one Q.mk_xC_pow_four
  obtain ⟨j, hj, hje⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hj2 : 2 ≤ j := by
    by_contra hlt
    simp only [not_le] at hlt
    have hdvd2 : (2 : ℕ) ^ j ∣ 2 := by interval_cases j <;> norm_num
    rw [← hje] at hdvd2
    exact Q.mk_xC_sq_ne_one (orderOf_dvd_iff_pow_eq_one.mp hdvd2)
  have hjeq : j = 2 := by omega
  rw [hjeq] at hje
  norm_num at hje
  exact hje

/-- **`C/RH` is generated by `x̄`** (`= ⟨x̄⟩`): the cyclic quotient of order `4`. -/
theorem zpowers_mk_xC_eq_top :
    Subgroup.zpowers (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) = ⊤ := by
  -- `X ⊔ RH = C` (as `R ≤ X`, `X ⊔ H = C`)
  have hXRH : Q.X ⊔ Q.RH = Q.C := by
    rw [RH, ← sup_assoc, sup_eq_left.mpr Q.R_le_X, Q.X_sup_H_eq_C]
  have hXtop : Q.X.subgroupOf Q.C ⊔ Q.RH.subgroupOf Q.C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup Q.X_le_C Q.RH_le_C, hXRH, Subgroup.subgroupOf_self]
  -- `X.subgroupOf C = zpowers xC`
  have hXsub : Q.X.subgroupOf Q.C = Subgroup.zpowers Q.xC := by
    ext c
    rw [Subgroup.mem_subgroupOf, X, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow, coe_xC]; exact hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hk, SubgroupClass.coe_zpow, coe_xC]⟩
  -- map along `mk'`: `⊤ = zpowers (mk xC) ⊔ ⊥`
  set π := QuotientGroup.mk' (Q.RH.subgroupOf Q.C) with hπ
  have hmap := congrArg (Subgroup.map π) hXtop
  rw [Subgroup.map_sup, hXsub, MonoidHom.map_zpowers,
    Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at hmap
  have hkerbot : Subgroup.map π (Q.RH.subgroupOf Q.C) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  rw [hkerbot, sup_bot_eq] at hmap
  have hπx : π Q.xC = QuotientGroup.mk Q.xC := rfl
  rw [hπx] at hmap
  exact hmap

theorem forall_mem_zpowers_mk_xC
    (q : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) :
    q ∈ Subgroup.zpowers (QuotientGroup.mk Q.xC) := by
  rw [Q.zpowers_mk_xC_eq_top]; trivial

/-- `i` as a unit of `ℂ`. -/
noncomputable def iUnit : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

@[simp] theorem coe_iUnit : (iUnit : ℂ) = Complex.I := Units.val_mk0 _

theorem iUnit_pow_four : iUnit ^ 4 = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, coe_iUnit, Complex.I_pow_four, Units.val_one]

theorem orderOf_iUnit_dvd :
    orderOf iUnit ∣ orderOf (QuotientGroup.mk Q.xC : ↥Q.C ⧸ Q.RH.subgroupOf Q.C) := by
  rw [Q.orderOf_mk_xC]
  exact orderOf_dvd_of_pow_eq_one iUnit_pow_four

/-- **The linear character `ψ : C →* ℂˣ`** (Gorenstein p. 375): the faithful character
`x̄ ↦ i` of the order-`4` cyclic quotient `C/RH`, pulled back to `C`.  So `ψ(x) = i` and
`RH ⊆ ker ψ`. -/
noncomputable def psiHom : ↥Q.C →* ℂˣ :=
  (monoidHomOfForallMemZpowers Q.forall_mem_zpowers_mk_xC Q.orderOf_iUnit_dvd).comp
    (QuotientGroup.mk' (Q.RH.subgroupOf Q.C))

/-- **`ψ(x) = i`**. -/
theorem psiHom_xC : Q.psiHom Q.xC = iUnit := by
  rw [psiHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    monoidHomOfForallMemZpowers_apply_gen]

/-- **`RH ⊆ ker ψ`**. -/
theorem psiHom_eq_one_of_mem_RH {c : ↥Q.C} (hc : (c : G) ∈ Q.RH) : Q.psiHom c = 1 := by
  rw [psiHom, MonoidHom.comp_apply,
    show QuotientGroup.mk' (Q.RH.subgroupOf Q.C) c = 1 from by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]; exact hc,
    map_one]

/-- `ψ ≠ 1` (`ψ(x) = i ≠ 1`). -/
theorem psiHom_ne_one : Q.psiHom ≠ 1 := by
  intro h
  have hval : Q.psiHom Q.xC = 1 := by rw [h]; rfl
  rw [Q.psiHom_xC] at hval
  have hI : Complex.I = 1 := by
    have := congrArg Units.val hval
    rwa [coe_iUnit, Units.val_one] at this
  have him := congrArg Complex.im hI
  rw [Complex.I_im, Complex.one_im] at him
  exact one_ne_zero him

/-! ### The character `ψ` viewed inside `N`, and `θ = Ind 1_C − Ind ψ` -/

/-- `RH ⊴ N` (in the `N`-view): `RH.subgroupOf N ⊴ ↥N`. -/
instance : (Q.RH.subgroupOf Q.N).Normal := by
  refine ⟨fun a ha n => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  have h := Q.conj_mem_RH_of_mem_N n.2 ha
  simpa [Subgroup.coe_mul, Subgroup.coe_inv] using h

/-- `ψ` as a class function of `C.subgroupOf N` (for inducing to `N`). -/
noncomputable def psiN : ClassFunction ↥(Q.C.subgroupOf Q.N) ℂ :=
  linearClassFunction (Q.psiHom.comp (Subgroup.subgroupOfEquivOfLe Q.C_le_N).toMonoidHom)

/-- `ψ` as an irreducible (linear) character of `C.subgroupOf N`. -/
noncomputable def psiNIrr : IrreducibleCharacter ↥(Q.C.subgroupOf Q.N) :=
  linearIrreducibleCharacter (Q.psiHom.comp (Subgroup.subgroupOfEquivOfLe Q.C_le_N).toMonoidHom)

@[simp] theorem coe_psiNIrr : (Q.psiNIrr : ClassFunction ↥(Q.C.subgroupOf Q.N) ℂ) = Q.psiN := rfl

/-- `RH ⊆ ker ψ` in the `N`-view: `ψ = 1` on `RH ∩ C`. -/
theorem psiN_eq_one_of_mem_RH {c : ↥(Q.C.subgroupOf Q.N)}
    (hc : ((c : ↥Q.N) : G) ∈ Q.RH) : Q.psiN c = 1 := by
  rw [psiN, linearClassFunction_apply, MonoidHom.comp_apply,
    Q.psiHom_eq_one_of_mem_RH (c := (Subgroup.subgroupOfEquivOfLe Q.C_le_N).toMonoidHom c) hc,
    Units.val_one]

/-- `ψ ≠ 1_C` as an irreducible character (so `⟨1_C, ψ⟩ = 0`). -/
theorem psiNIrr_ne_trivial : Q.psiNIrr ≠ trivialIrreducibleCharacter _ := by
  rw [psiNIrr, Ne, linearIrreducibleCharacter_eq_trivial_iff]
  intro h
  apply Q.psiHom_ne_one
  refine MonoidHom.ext fun d => ?_
  rw [MonoidHom.one_apply]
  have hd := DFunLike.congr_fun h ((Subgroup.subgroupOfEquivOfLe Q.C_le_N).symm d)
  rw [MonoidHom.comp_apply, MonoidHom.one_apply] at hd
  rwa [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hd

/-- **The virtual character `θ = Ind_C^N 1_C − Ind_C^N ψ`** (Gorenstein Lemma 1.4). -/
noncomputable def theta [Fintype ↥Q.N] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ClassFunction ↥Q.N ℂ :=
  ClassFunction.induce (Q.C.subgroupOf Q.N) (trivialClassFunction _)
    - ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN

/-- **`θ(1) = 0`** (Gorenstein Lemma 1.4(ii)): both `Ind 1_C` and `Ind ψ` have degree
`[N : C]·1 = [N : C]`. -/
theorem theta_apply_one [Fintype ↥Q.N] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    Q.theta (1 : ↥Q.N) = 0 := by
  rw [theta, ClassFunction.sub_apply, ClassFunction.induce_apply_one,
    ClassFunction.induce_apply_one, trivialClassFunction_apply]
  have hψ1 : Q.psiN (1 : ↥(Q.C.subgroupOf Q.N)) = 1 := by
    rw [psiN, linearClassFunction_apply, map_one, Units.val_one]
  rw [hψ1, sub_self]

/-- **`θ` vanishes on `N − A`** (Gorenstein Lemma 1.4): `θ(g) = 0` for `g ∉ A = C − RH`.
Off `C` both induced characters vanish (normal support); on `RH` both equal the constant
`⅟|C|·|N|·1` (`RH ⊆ ker ψ`). -/
theorem theta_apply_eq_zero_of_notMem_A [Fintype ↥Q.N]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)]
    {g : ↥Q.N} (hg : (g : G) ∉ Q.A) : Q.theta g = 0 := by
  rw [theta, ClassFunction.sub_apply]
  by_cases hgC : (g : G) ∈ Q.C
  · -- `g ∈ C ∖ A ⟹ g ∈ RH`; both inductions equal the same constant
    have hgRH : (g : G) ∈ Q.RH := by
      by_contra h
      exact hg ⟨hgC, h⟩
    have hgA : g ∈ Q.RH.subgroupOf Q.N := by rw [Subgroup.mem_subgroupOf]; exact hgRH
    have hle : Q.RH.subgroupOf Q.N ≤ Q.C.subgroupOf Q.N :=
      Subgroup.subgroupOf_mono Q.N Q.RH_le_C
    rw [ClassFunction.induce_apply_of_mem_normal_of_const hle (trivialClassFunction _)
        (fun a' _ => trivialClassFunction_apply _) hgA,
      ClassFunction.induce_apply_of_mem_normal_of_const hle Q.psiN
        (fun a' ha' => Q.psiN_eq_one_of_mem_RH (Subgroup.mem_subgroupOf.mp ha')) hgA,
      sub_self]
  · -- `g ∉ C ⟹ both inductions vanish`
    have hgH : g ∉ Q.C.subgroupOf Q.N := by rw [Subgroup.mem_subgroupOf]; exact hgC
    rw [ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ _ hgH,
      ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ _ hgH, sub_zero]

/-! ### `Ind_C^N ψ` is irreducible (inertia of `ψ` is `C`), and `(θ,θ)_N = 3` -/

/-- `x` viewed as an element of `C.subgroupOf N`. -/
def xN : ↥(Q.C.subgroupOf Q.N) :=
  ⟨⟨Q.x, Q.S_le_N Q.hxS⟩, by rw [Subgroup.mem_subgroupOf]; exact Q.x_mem_C⟩

@[simp] theorem coe_xN : ((Q.xN : ↥Q.N) : G) = Q.x := rfl

/-- `ψ(w) = ψ(d)` whenever the underlying `G`-element of `w` (in `C.subgroupOf N`) equals
that of `d` (in `C`). -/
theorem psiN_apply_eq_psiHom {w : ↥(Q.C.subgroupOf Q.N)} {d : ↥Q.C}
    (hwd : ((w : ↥Q.N) : G) = (d : G)) : Q.psiN w = (Q.psiHom d : ℂ) := by
  rw [psiN, linearClassFunction_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  congr 2
  exact Subtype.ext hwd

/-- `ψ(x) = i` in the `N`-view. -/
theorem psiN_xN : Q.psiN Q.xN = Complex.I := by
  rw [Q.psiN_apply_eq_psiHom (d := Q.xC) rfl, Q.psiHom_xC, coe_iUnit]

/-- **`ψ ≠ ψʸ`** (Gorenstein p. 375): `ψʸ(x) = ψ(y·x·y⁻¹) = ψ(x⁻¹) = i⁻¹ ≠ i = ψ(x)`.
This is exactly what forces the inertia of `ψ` in `N` to be `C` (not `N`). -/
theorem conjBy_y_psiN_ne_psiN :
    ClassFunction.conjBy (⟨Q.y, Q.y_mem_N⟩ : ↥Q.N) Q.psiN ≠ Q.psiN := by
  intro h
  have hval := congrArg (fun f : ClassFunction ↥(Q.C.subgroupOf Q.N) ℂ => f Q.xN) h
  have hconj_coe :
      (((⟨Q.y, Q.y_mem_N⟩ : ↥Q.N) * (Q.xN : ↥Q.N) * (⟨Q.y, Q.y_mem_N⟩ : ↥Q.N)⁻¹ :
        ↥Q.N) : G) = ((Q.xC⁻¹ : ↥Q.C) : G) := by
    change Q.y * Q.x * Q.y⁻¹ = Q.x⁻¹
    exact Q.hconj
  rw [ClassFunction.conjBy_apply, Q.psiN_apply_eq_psiHom hconj_coe,
    Q.psiN_apply_eq_psiHom (d := Q.xC) rfl, map_inv, Q.psiHom_xC] at hval
  -- hval : (↑iUnit⁻¹ : ℂ) = (↑iUnit : ℂ)
  have hu : iUnit⁻¹ = iUnit := Units.val_injective hval
  have hsq : iUnit * iUnit = 1 := mul_eq_one_iff_eq_inv.mpr hu.symm
  have hII : Complex.I * Complex.I = 1 := by
    have := congrArg Units.val hsq
    rwa [Units.val_mul, coe_iUnit, Units.val_one] at this
  rw [← sq, Complex.I_sq] at hII
  norm_num at hII

/-- **The inertia group of `ψ` in `N` is `C`** (Gorenstein p. 375): `C ⊆ I_N(ψ)` always,
and `I_N(ψ) ⊆ C` because any `g ∉ C` is `yc` with `c ∈ C`, so `ψ^g = ψ^y ≠ ψ`. -/
theorem inertia_psiN : ClassFunction.inertia Q.psiN = Q.C.subgroupOf Q.N := by
  apply le_antisymm
  · intro g hg
    rw [ClassFunction.mem_inertia] at hg
    rcases Q.mem_C_or_yinv_mul_mem_C g.2 with hgC | hyg
    · rw [Subgroup.mem_subgroupOf]; exact hgC
    · exfalso
      set c : ↥Q.N := (⟨Q.y, Q.y_mem_N⟩ : ↥Q.N)⁻¹ * g with hc
      have hcC : c ∈ Q.C.subgroupOf Q.N := by
        rw [Subgroup.mem_subgroupOf]
        change Q.y⁻¹ * (g : G) ∈ Q.C
        exact hyg
      have hgeq : (⟨Q.y, Q.y_mem_N⟩ : ↥Q.N) * c = g := by rw [hc]; group
      have h1 : ClassFunction.conjBy g Q.psiN
          = ClassFunction.conjBy (⟨Q.y, Q.y_mem_N⟩ : ↥Q.N) Q.psiN := by
        conv_lhs => rw [← hgeq, ClassFunction.conjBy_mul,
          ClassFunction.conjBy_eq_self_of_mem hcC]
      rw [hg] at h1
      exact Q.conjBy_y_psiN_ne_psiN h1.symm
  · exact ClassFunction.subgroup_le_inertia Q.psiN

/-- `ψ` (in the `N`-view) is irreducible. -/
theorem psiN_isIrr : IsIrreducibleCharacter Q.psiN := by
  have h := Q.psiNIrr.isIrreducible
  rwa [coe_psiNIrr] at h

/-- `ψ ≠ 1_C` as a class function. -/
theorem psiN_ne_trivial : Q.psiN ≠ trivialClassFunction ↥(Q.C.subgroupOf Q.N) := by
  intro h
  apply Q.psiNIrr_ne_trivial
  apply IrreducibleCharacter.ext
  rw [coe_psiNIrr, h, IrreducibleCharacter.coe_trivialIrreducibleCharacter]

/-- **`Ind_C^N ψ` is irreducible** (Gorenstein Lemma 1.4): `I_N(ψ) = C`, so induction
from `C` to `N` gives an irreducible character (`isIrreducibleCharacter_induce_of_inertia_eq`). -/
theorem psiN_induce_irreducible [Fintype ↥Q.N] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    IsIrreducibleCharacter (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN) := by
  have h := isIrreducibleCharacter_induce_of_inertia_eq Q.psiNIrr (by
    rw [coe_psiNIrr]; exact Q.inertia_psiN)
  rwa [coe_psiNIrr] at h

/-- **`(θ, θ)_N = 3`** (Gorenstein Lemma 1.4(i)).  Writing `Tc = Ind 1_C`, `Ps = Ind ψ`,
`(θ,θ) = (Tc,Tc) − (Tc,Ps) − (Ps,Tc) + (Ps,Ps) = 2 − 0 − 0 + 1 = 3`:
`(Tc,Tc) = [N:C] = 2`, `(Ps,Tc) = 0` (`ψ` irreducible `≠ 1`), `(Tc,Ps) = 0` (conjugate),
`(Ps,Ps) = 1` (`Ind ψ` irreducible). -/
theorem theta_inner_self [Fintype ↥Q.N] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ClassFunction.inner Q.theta Q.theta = 3 := by
  have hirr : IsIrreducibleCharacter (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN) :=
    Q.psiN_induce_irreducible
  rw [theta, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_sub_right]
  have hTT : ClassFunction.inner
      (ClassFunction.induce (Q.C.subgroupOf Q.N) (trivialClassFunction _))
      (ClassFunction.induce (Q.C.subgroupOf Q.N) (trivialClassFunction _)) = 2 := by
    rw [ClassFunction.induce_trivial_inner_self, Q.index_C_subgroupOf_N]; norm_num
  have hPT : ClassFunction.inner (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN)
      (ClassFunction.induce (Q.C.subgroupOf Q.N) (trivialClassFunction _)) = 0 :=
    ClassFunction.induce_inner_induce_trivial_eq_zero_of_irreducible _ Q.psiN_isIrr
      Q.psiN_ne_trivial
  have hTP : ClassFunction.inner
      (ClassFunction.induce (Q.C.subgroupOf Q.N) (trivialClassFunction _))
      (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN) = 0 := by
    rw [ClassFunction.inner_star_comm, hPT, star_zero]
  have hPP : ClassFunction.inner (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN)
      (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN) = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner
      (mem_irreducibleCharacters.mpr hirr) (mem_irreducibleCharacters.mpr hirr), if_pos rfl]
  rw [hTT, hTP, hPT, hPP]; norm_num

/-! ### The induced character `θ* = Ind_N^G θ` (Gorenstein Lemma 1.5, analytic part) -/

/-- **`θ* = Ind_N^G θ`** (Gorenstein Lemma 1.5): the `TI`-induction of `θ` to the whole
group `G`.  Since `A = C − RH` is a TI-subset with normalizer-bound `N` and `θ` vanishes off
`A`, this induction is an isometry on `θ`. -/
noncomputable def thetaStar [Fintype G] [Fintype ↥Q.N]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ClassFunction G ℂ :=
  ClassFunction.induce Q.N Q.theta

/-- `θ` vanishes off `A` (packaged for the TI isometry). -/
theorem theta_vanishes_off_A [Fintype ↥Q.N]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∀ x : ↥Q.N, (x : G) ∉ Q.A → Q.theta x = 0 :=
  fun _ hx => Q.theta_apply_eq_zero_of_notMem_A hx

/-- **`(θ*, θ*)_G = 3`** (Gorenstein Lemma 1.5): the TI-induction isometry
(`inner_induce_eq_of_isTISubset`) carries `(θ,θ)_N = 3` to `G`. -/
theorem thetaStar_inner_self [Fintype G] [Fintype ↥Q.N] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ClassFunction.inner Q.thetaStar Q.thetaStar = 3 := by
  rw [thetaStar, ClassFunction.inner_induce_eq_of_isTISubset Q.N Q.A_isTISubset
    Q.theta_vanishes_off_A Q.theta_vanishes_off_A, Q.theta_inner_self]

/-- **`θ*(1) = 0`** (Gorenstein Lemma 1.5): `θ*(1) = [G:N]·θ(1) = 0`. -/
theorem thetaStar_apply_one [Fintype G] [Fintype ↥Q.N]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    Q.thetaStar (1 : G) = 0 := by
  rw [thetaStar, ClassFunction.induce_apply_one, Q.theta_apply_one, mul_zero]

/-- **`(θ*, 1_G)_G = 1`** (Gorenstein Lemma 1.5): Frobenius reciprocity reduces this to
`(θ, 1_N)_N = (Ind 1_C, 1_N) − (Ind ψ, 1_N) = 1 − 0 = 1`. -/
theorem thetaStar_inner_trivial [Fintype G] [Fintype ↥Q.N] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ClassFunction.inner Q.thetaStar (trivialClassFunction G) = 1 := by
  haveI : Fintype ↥(Q.C.subgroupOf Q.N) := Fintype.ofFinite _
  rw [thetaStar, ClassFunction.induce_inner_trivial, theta, ClassFunction.inner_sub_left]
  -- (Ind 1_C, 1_N) = 1, (Ind ψ, 1_N) = 0
  have hT : ClassFunction.inner
      (ClassFunction.induce (Q.C.subgroupOf Q.N) (trivialClassFunction _))
      (trivialClassFunction ↥Q.N) = 1 := by
    rw [ClassFunction.induce_inner_trivial, OddOrder.RepresentationTheory.irr_cf_inner
      trivialClassFunction_isIrreducible trivialClassFunction_isIrreducible, if_pos rfl]
  have hP : ClassFunction.inner (ClassFunction.induce (Q.C.subgroupOf Q.N) Q.psiN)
      (trivialClassFunction ↥Q.N) = 0 := by
    rw [ClassFunction.induce_inner_trivial, OddOrder.RepresentationTheory.irr_cf_inner
      (mem_irreducibleCharacters.mpr Q.psiN_isIrr) trivialClassFunction_isIrreducible,
      if_neg Q.psiN_ne_trivial]
  rw [hT, hP, sub_zero]

/-- `θ ∈ ℤ[Irr N]` (virtual character): `θ = Ind 1_C − Ind ψ`, both induced characters. -/
theorem theta_mem_ZIrr [Fintype ↥Q.N] [Invertible (Nat.card ↥Q.N : ℂ)]
    [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    Q.theta ∈ ZIrr ↥Q.N := by
  haveI : Fintype ↥(Q.C.subgroupOf Q.N) := Fintype.ofFinite _
  rw [theta]
  exact sub_mem (ClassFunction.induce_mem_ZIrr _ trivialClassFunction_isIrreducible.mem_ZIrr)
    (ClassFunction.induce_mem_ZIrr _ Q.psiN_isIrr.mem_ZIrr)

/-- `θ* ∈ ℤ[Irr G]` (virtual character): TI-induction of the virtual character `θ`. -/
theorem thetaStar_mem_ZIrr [Fintype G] [Fintype ↥Q.N] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    Q.thetaStar ∈ ZIrr G := by
  rw [thetaStar]
  exact ClassFunction.induce_mem_ZIrr _ Q.theta_mem_ZIrr

/-- **Gorenstein Lemma 1.5 (decomposition)**: `θ* = 1_G + χ₁ − χ` for two distinct
non-principal irreducible characters `χ₁, χ` with `χ(1) = χ₁(1) + 1`.

`ρ = θ* − 1_G` is a virtual character of squared norm `2` orthogonal to `1_G` with
`ρ(1) = −1`; by the Fourier structure `ρ = ±χ₁ ± χ` for distinct irreducibles, both
non-principal (`⟨ρ, 1_G⟩ = 0`), and the degree constraint `ρ(1) = −1` forces the signs to
be `(+, −)` with `χ(1) = χ₁(1) + 1`. -/
theorem thetaStar_decomposition [Fintype G] [Fintype ↥Q.N] [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥Q.N : ℂ)] [Invertible (Nat.card ↥(Q.C.subgroupOf Q.N) : ℂ)] :
    ∃ χ₁ χ : IrreducibleCharacter G, χ₁ ≠ χ ∧ χ₁ ≠ trivialIrreducibleCharacter G ∧
      χ ≠ trivialIrreducibleCharacter G ∧
      Q.thetaStar = trivialClassFunction G + (χ₁ : ClassFunction G ℂ)
        - (χ : ClassFunction G ℂ) ∧
      (χ : ClassFunction G ℂ) (1 : G) = (χ₁ : ClassFunction G ℂ) (1 : G) + 1 := by
  classical
  set ρ : ClassFunction G ℂ := Q.thetaStar - trivialClassFunction G with hρdef
  have hρZ : ρ ∈ ZIrr G :=
    sub_mem Q.thetaStar_mem_ZIrr trivialClassFunction_isIrreducible.mem_ZIrr
  -- (ρ, ρ) = 2
  have hρnorm : ClassFunction.inner ρ ρ = 2 := by
    have h1G : ClassFunction.inner (trivialClassFunction G) (trivialClassFunction G) = 1 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner trivialClassFunction_isIrreducible
        trivialClassFunction_isIrreducible, if_pos rfl]
    have hcross : ClassFunction.inner (trivialClassFunction G) Q.thetaStar = 1 := by
      rw [ClassFunction.inner_star_comm, Q.thetaStar_inner_trivial, star_one]
    rw [hρdef, ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, Q.thetaStar_inner_self, Q.thetaStar_inner_trivial,
      hcross, h1G]
    ring
  -- ρ(1) = -1
  have hρ1 : ρ (1 : G) = -1 := by
    rw [hρdef, ClassFunction.sub_apply, Q.thetaStar_apply_one, trivialClassFunction_apply]
    ring
  -- (ρ, 1_G) = 0
  have hρtriv : ClassFunction.inner ρ (trivialClassFunction G) = 0 := by
    rw [hρdef, ClassFunction.inner_sub_left, Q.thetaStar_inner_trivial,
      OddOrder.RepresentationTheory.irr_cf_inner trivialClassFunction_isIrreducible
        trivialClassFunction_isIrreducible, if_pos rfl, sub_self]
  -- Fourier structure: ρ = c(α₀)·α₀ + c(β₀)·β₀
  obtain ⟨c, hsupp, hrepr, hsq⟩ := mem_ZIrr_inner_self_eq_sum_sq hρZ
  have hsumZ : ∑ a ∈ c.support, c a ^ 2 = 2 := by exact_mod_cast hsq.symm.trans hρnorm
  have hne : ∀ a ∈ c.support, c a ≠ 0 := fun a ha => Finsupp.mem_support_iff.mp ha
  obtain ⟨α₀, β₀, hαβ, hs, hcα, hcβ⟩ := exists_pair_of_sum_sq_eq_two hne hsumZ
  have hα₀ : α₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  have hβ₀ : β₀ ∈ irreducibleCharacters G := hsupp (by rw [hs]; simp)
  rw [hs, Finset.sum_pair hαβ] at hrepr
  obtain ⟨dα, hdα, hα1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ⟨α₀, hα₀⟩
  obtain ⟨dβ, hdβ, hβ1⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ⟨β₀, hβ₀⟩
  simp only [IrreducibleCharacter.coe_mk] at hα1 hβ1
  -- degree equation (in ℤ)
  have hone'Z : c α₀ * (dα : ℤ) + c β₀ * (dβ : ℤ) = -1 := by
    have h := hρ1
    rw [hrepr] at h
    simp only [ClassFunction.add_apply, ClassFunction.smul_apply, hα1, hβ1] at h
    exact_mod_cast h
  have hdα1 : 1 ≤ (dα : ℤ) := by exact_mod_cast hdα
  have hdβ1 : 1 ≤ (dβ : ℤ) := by exact_mod_cast hdβ
  -- non-principality of α₀, β₀ via `⟨ρ, ·⟩ = coeff`
  have hinnα : ClassFunction.inner ρ α₀ = (c α₀ : ℂ) := by
    rw [hrepr, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.irr_cf_inner hα₀ hα₀,
      if_pos rfl, OddOrder.RepresentationTheory.irr_cf_inner hβ₀ hα₀,
      if_neg (Ne.symm hαβ), mul_one, mul_zero, add_zero]
  have hinnβ : ClassFunction.inner ρ β₀ = (c β₀ : ℂ) := by
    rw [hrepr, ClassFunction.inner_add_left, ClassFunction.inner_smul_left,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.irr_cf_inner hα₀ hβ₀,
      if_neg hαβ, OddOrder.RepresentationTheory.irr_cf_inner hβ₀ hβ₀, if_pos rfl,
      mul_zero, mul_one, zero_add]
  have hαnt : α₀ ≠ trivialClassFunction G := by
    intro h
    have hc0 : (c α₀ : ℂ) = 0 := by rw [← hinnα, h]; exact hρtriv
    rcases hcα with hh | hh <;> rw [hh] at hc0 <;> norm_num at hc0
  have hβnt : β₀ ≠ trivialClassFunction G := by
    intro h
    have hc0 : (c β₀ : ℂ) = 0 := by rw [← hinnβ, h]; exact hρtriv
    rcases hcβ with hh | hh <;> rw [hh] at hc0 <;> norm_num at hc0
  -- `θ* = 1_G + ρ`
  have hθρ : Q.thetaStar = trivialClassFunction G + ρ := by rw [hρdef]; abel
  rcases hcα with hcα1 | hcα1 <;> rcases hcβ with hcβ1 | hcβ1
  · -- (+1, +1): `dα + dβ = -1` impossible
    exfalso; rw [hcα1, hcβ1] at hone'Z; omega
  · -- (+1, −1): `θ* = 1 + α₀ − β₀`, `dβ = dα + 1`
    refine ⟨⟨α₀, hα₀⟩, ⟨β₀, hβ₀⟩, fun h => hαβ (congrArg Subtype.val h),
      fun h => hαnt (congrArg Subtype.val h), fun h => hβnt (congrArg Subtype.val h), ?_, ?_⟩
    · rw [hθρ, hrepr, hcα1, hcβ1]
      simp only [IrreducibleCharacter.coe_mk, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
      abel
    · rw [IrreducibleCharacter.coe_mk, IrreducibleCharacter.coe_mk, hα1, hβ1]
      rw [hcα1, hcβ1] at hone'Z
      have : (dβ : ℤ) = dα + 1 := by omega
      exact_mod_cast this
  · -- (−1, +1): `θ* = 1 + β₀ − α₀`, `dα = dβ + 1`
    refine ⟨⟨β₀, hβ₀⟩, ⟨α₀, hα₀⟩, fun h => hαβ (congrArg Subtype.val h).symm,
      fun h => hβnt (congrArg Subtype.val h), fun h => hαnt (congrArg Subtype.val h), ?_, ?_⟩
    · rw [hθρ, hrepr, hcα1, hcβ1]
      simp only [IrreducibleCharacter.coe_mk, Int.cast_one, Int.cast_neg, one_smul, neg_one_smul]
      abel
    · rw [IrreducibleCharacter.coe_mk, IrreducibleCharacter.coe_mk, hα1, hβ1]
      rw [hcα1, hcβ1] at hone'Z
      have : (dα : ℤ) = dβ + 1 := by omega
      exact_mod_cast this
  · -- (−1, −1): `dα + dβ = 1` impossible (both ≥ 1)
    exfalso; rw [hcα1, hcβ1] at hone'Z; omega

end QuaternionSylowSetup

end OddOrder.GroupTheory
