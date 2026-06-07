/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialKeystone
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialThm25
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# BG Theorem 2.5 at the group level (divisibility part)

`OddOrder.GroupTheory.RepresentationTheory` shared module: wires the BG (2.11) keystone
(`finrank_cyclicEndConjEigenspaceFin_succ`) and the Prop 2.4 counting
(`sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace`) into the **group-level** divisibility
conclusion of Bender–Glauberman Theorem 2.5: for a class-`≤ 2` `p`-group `P ⊴ G` with a faithful
irreducible representation and an element `x` of order `h` acting fixed-point-freely on `P/Z(P)`,
`h ∣ (dim V) ± 1`.

This file supplies the group-theoretic *setup wiring* (the conjugation automorphism `φ` of `P`
induced by `x`, the intertwiner `T = ρ x`, the intertwining relation, `φ^h = 1`, and the eigenspace
decomposition `hV`).  Two inputs are taken as hypotheses, to be discharged separately:

* `hVP : Representation.IsIrreducible (ρ.comp P.subtype)` — **BG Prop 2.2(a)** (`V_P` irreducible,
  the alg-closed Clifford step), still to be formalised;
* `hcent` — **BG Prop 1.5** (`C_{P/Z}(xᵏ) = 1`, i.e. `x` is fixed-point-free on `P/Z`), from the
  hypothesis `C_P(xᵏ) = Z(P)` via coprime action.
-/

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction
open OddOrder.Isaacs.Ch03 (IsAInvariant)

variable {G : Type*} [Group G]

/-- The automorphism of a normal subgroup `P` induced by conjugation by `x ∈ G`. -/
noncomputable def conjAutOfNormal (P : Subgroup G) [P.Normal] (x : G) : P ≃* P :=
  (MulEquiv.subgroupMap (MulAut.conj x) P).trans
    (MulEquiv.subgroupCongr (Subgroup.Normal.conj_smul_eq_self x P))

@[simp]
theorem conjAutOfNormal_apply_coe (P : Subgroup G) [P.Normal] (x : G) (p : P) :
    (conjAutOfNormal P x p : G) = x * (p : G) * x⁻¹ := rfl

/-- Iterating: `(φ^k p : G) = x^k · p · x^{-k}`. -/
theorem conjAutOfNormal_pow_apply_coe (P : Subgroup G) [P.Normal] (x : G) (k : ℕ) (p : P) :
    (((conjAutOfNormal P x) ^ k) p : G) = x ^ k * (p : G) * (x ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, conjAutOfNormal_apply_coe, ih]
    group

/-- If `x^h = 1` then `φ^h = 1`. -/
theorem conjAutOfNormal_pow_eq_one (P : Subgroup G) [P.Normal] {x : G} {h : ℕ} (hx : x ^ h = 1) :
    (conjAutOfNormal P x) ^ h = 1 := by
  ext p
  rw [conjAutOfNormal_pow_apply_coe, hx]
  simp

/-- **BG Proposition 1.5** (the `hcent` input to `finrank_modEq_of_faithful_irreducible`).  In the
Theorem 2.5 setup, `x ∈ G` has order `h` coprime to `|P|` and for every nontrivial power `xᵏ` the
centralizer `C_P(xᵏ)` is contained in `Z(P)` (BG's hypothesis `C_P(x) = Z(P)` for `x ∈ H^#`, stated
here as the fixed points of the conjugation automorphism `(conjAutOfNormal P x)^k` lying in `Z(P)`).
Then `x` acts **fixed-point-freely on `P/Z(P)`**: the only coset fixed by a nontrivial power of the
induced automorphism `σ = quotientCenterCongr (conjAutOfNormal P x)` is the identity.

The proof lifts a fixed coset to a genuine fixed point via the coprime fixed-point theorem (Isaacs
Cor 3.28, `coprime_fixedPoints_quotient_of_coprime_normal`): the cyclic group `⟨φᵏ⟩`
(`φ = conjAutOfNormal P x`) acts on `P` with `Z(P)` an invariant subgroup, and
`(|⟨φᵏ⟩|, |Z(P)|) = 1` since `|⟨φᵏ⟩| ∣ h`,
`|Z(P)| ∣ |P|`, and `(h, |P|) = 1`.  The lifted fixed point lies in `C_P(xᵏ) ⊆ Z(P)`, so the coset
is trivial. -/
theorem quotientCenter_fixedFree_of_centralizer_le_center
    [Finite G] (P : Subgroup G) [P.Normal]
    (x : G) {h : ℕ} (hxh : x ^ h = 1) (hcop : Nat.Coprime h (Nat.card P))
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ p : P,
        (conjAutOfNormal P x ^ k.val) p = p → p ∈ Subgroup.center P) :
    ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c) = c → c = 1 := by
  classical
  intro k hk c hfix
  set φ₀ : P ≃* P := conjAutOfNormal P x with hφ₀
  -- a fixed point of `t` is fixed by every power of `t`
  have hiter : ∀ (t : (P ⧸ Subgroup.center P) ≃* (P ⧸ Subgroup.center P)) (d) (m : ℕ),
      t d = d → (t ^ m) d = d := by
    intro t d m ht
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, MulAut.mul_apply, ht]; exact ih
  -- a coset representative of `c`
  set g : P := Quotient.out c with hg
  have hgc : (g : P ⧸ Subgroup.center P) = c := by rw [hg]; exact Quotient.out_eq' c
  -- `φ₀^k` has order dividing `h`, hence `(|⟨φ₀^k⟩|, |Z(P)|) = 1`
  have hωh : (φ₀ ^ k.val) ^ h = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hφ₀, conjAutOfNormal_pow_eq_one P hxh, one_pow]
  have hAcard : Nat.card (Subgroup.zpowers (φ₀ ^ k.val)) ∣ h := by
    rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hωh
  have hCopN : Nat.Coprime (Nat.card (Subgroup.zpowers (φ₀ ^ k.val)))
      (Nat.card (Subgroup.center P)) :=
    (hcop.coprime_dvd_left hAcard).coprime_dvd_right (Subgroup.card_subgroup_dvd_card _)
  have hSolv : IsSolvable ↥(Subgroup.zpowers (φ₀ ^ k.val)) ∨
      IsSolvable ↥(Subgroup.center P) :=
    Or.inr (isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp a.2 b.1).symm)
  have hN_inv : IsAInvariant (Subgroup.zpowers (φ₀ ^ k.val)).subtype (Subgroup.center P) :=
    IsAInvariant.center _
  -- the coset `gZ` is invariant under all powers of `φ₀^k` (since `σ^k` fixes `c`)
  have hg_fix : ∀ a : Subgroup.zpowers (φ₀ ^ k.val),
      ∃ n ∈ Subgroup.center P, (Subgroup.zpowers (φ₀ ^ k.val)).subtype a g = g * n := by
    intro a
    obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.mpr a.2
    have key : (Subgroup.zpowers (φ₀ ^ k.val)).subtype a g = (φ₀ ^ (k.val * m)) g := by
      rw [show (Subgroup.zpowers (φ₀ ^ k.val)).subtype a = (φ₀ ^ k.val) ^ m from hm.symm,
        ← pow_mul]
    have hquot : ((Subgroup.zpowers (φ₀ ^ k.val)).subtype a g : P ⧸ Subgroup.center P) = c := by
      rw [key, ← quotientCenterCongr_pow_mk, hgc, pow_mul]
      exact hiter ((quotientCenterCongr φ₀) ^ k.val) c m hfix
    refine ⟨g⁻¹ * (Subgroup.zpowers (φ₀ ^ k.val)).subtype a g, ?_, by group⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hgc, hquot,
      inv_mul_cancel]
  -- lift the fixed coset to a genuine fixed point of `φ₀^k`
  obtain ⟨w, hw_fix, n, hn, hwn⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      hCopN hSolv hN_inv hg_fix
  have hωw : (φ₀ ^ k.val) w = w := hw_fix ⟨φ₀ ^ k.val, Subgroup.mem_zpowers _⟩
  have hw_center : w ∈ Subgroup.center P := hCP k hk w hωw
  -- `g = w * n⁻¹ ∈ Z(P)`, so `c = ⟦g⟧ = 1`
  have hg_center : g ∈ Subgroup.center P := by
    have hgwn : g = w * n⁻¹ := by rw [hwn]; group
    rw [hgwn]; exact Subgroup.mul_mem _ hw_center (Subgroup.inv_mem _ hn)
  rw [← hgc, QuotientGroup.eq_one_iff]
  exact hg_center

/-- **BG Theorem 2.5, divisibility part (group level).** Let `P ⊴ G` be a finite group of
nilpotency class `≤ 2` (`commutator P ≤ Z(P)`) with a faithful representation `ρ` over an
algebraically closed field (`char ∤ |P|`), `x ∈ G` of order `h ≥ 2` with `char ∤ h`, `ε` a
primitive `h`-th root of unity.  If the restriction `V_P` is irreducible (BG Prop 2.2(a)) and `x`
acts fixed-point-freely on `P/Z(P)` (`hcent`, BG Prop 1.5), then `dim V ≡ ±1 (mod h)`. -/
theorem finrank_modEq_of_faithful_irreducible
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite G]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hVP : Representation.IsIrreducible (ρ.comp P.subtype))
    (hcent : ∀ k : ZMod h, k ≠ 0 → ∀ c : P ⧸ Subgroup.center P,
        ((quotientCenterCongr (conjAutOfNormal P x) ^ k.val) c) = c → c = 1) :
    ∃ (v₀ δ : ℤ), (δ = 1 ∨ δ = -1) ∧ (Module.finrank F V : ℤ) = (h : ℤ) * v₀ + δ := by
  classical
  set ρP : Representation F P V := ρ.comp P.subtype with hρP
  haveI : Representation.IsIrreducible ρP := hVP
  set φ : P ≃* P := conjAutOfNormal P x with hφ
  set T : LinearMap.GeneralLinearGroup F V := ρ.asGroupHom x with hT
  -- `↑T = ρ x`
  have hTcoe : (T : Module.End F V) = ρ x := by rw [hT]; exact MonoidHom.coe_toHomUnits ρ x
  -- restriction is faithful
  have hfP : Function.Injective ρP := fun a b hab => Subtype.ext (hf hab)
  -- intertwining relation
  have hint : ∀ p : P, (T : Module.End F V) * ρP p = ρP (φ p) * (T : Module.End F V) := by
    intro p
    rw [hTcoe]
    change ρ x * ρ (p : G) = ρ ((φ p : P) : G) * ρ x
    rw [conjAutOfNormal_apply_coe, ← map_mul, ← map_mul]
    congr 1
    group
  -- `φ^h = 1`, `T^h = 1`
  have hφh : φ ^ h = 1 := conjAutOfNormal_pow_eq_one P hxh
  have hTEnd_h : (T : Module.End F V) ^ h = 1 := by
    rw [hTcoe, ← map_pow, hxh, map_one]
  -- eigenspace decomposition of `V` under `T`
  have hV : DirectSum.IsInternal (cyclicEigenspaceFinFamily ε (T : Module.End F V) h) :=
    cyclicEigenspaceFin_isInternal_of_pow_eq_one hprim hTEnd_h
  -- the keystone supplies `hEdim`
  have hEdim := finrank_cyclicEndConjEigenspaceFin_succ ρP hfP hcl φ T hint hφh hprim hh hcent
  -- the Prop 2.4 counting gives `∑ dim Vᵢ ≡ ±1`
  obtain ⟨v₀, δ, hδ, hsum⟩ :=
    sum_eigenspaceFinDim_eq_of_finrank_cyclicEndConjEigenspace hprim hV hh2 hEdim
  -- `∑ dim Vᵢ = dim V`
  have hsumV : ∑ i : Fin h, cyclicEigenspaceFinDim ε (T : Module.End F V) i
      = Module.finrank F V := by
    rw [← (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap (cyclicEigenspaceFinFamily ε (T : Module.End F V) h)) hV).finrank_eq,
      Module.finrank_directSum]
  refine ⟨v₀, δ, hδ, ?_⟩
  rw [← hsum, ← Nat.cast_sum, hsumV]

/-- **BG Theorem 2.5, divisibility part**, with the abstract fixed-point-free hypothesis `hcent`
replaced by the BG-faithful centralizer condition.  Let `P ⊴ G` (finite, class `≤ 2`) carry a
faithful representation `ρ` over an algebraically closed field with `char ∤ |P|`, and let `x ∈ G`
have order `h ≥ 2` with `(h, |P|) = 1` and `char ∤ h`.  If `V_P` is irreducible (BG Prop 2.2(a)) and
`C_P(xᵏ) ⊆ Z(P)` for every nontrivial power `xᵏ` (BG's hypothesis `C_P(x) = Z(P)`, `x ∈ H^#`), then
`dim V ≡ ±1 (mod h)`.  The centralizer hypothesis is converted to fixed-point-freeness on `P/Z(P)`
by `quotientCenter_fixedFree_of_centralizer_le_center` (BG Prop 1.5). -/
theorem finrank_modEq_of_faithful_irreducible_of_centralizer
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Finite G]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) (hf : Function.Injective ρ)
    (hcl : commutator P ≤ Subgroup.center P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hcop : Nat.Coprime h (Nat.card P))
    (hVP : Representation.IsIrreducible (ρ.comp P.subtype))
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ p : P,
        (conjAutOfNormal P x ^ k.val) p = p → p ∈ Subgroup.center P) :
    ∃ (v₀ δ : ℤ), (δ = 1 ∨ δ = -1) ∧ (Module.finrank F V : ℤ) = (h : ℤ) * v₀ + δ :=
  finrank_modEq_of_faithful_irreducible P ρ hf hcl x hxh hh2 hprim hh hVP
    (quotientCenter_fixedFree_of_centralizer_le_center P x hxh hcop hCP)

end OddOrder.RepresentationTheory
