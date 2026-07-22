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

end QuaternionSylowSetup

end OddOrder.GroupTheory
