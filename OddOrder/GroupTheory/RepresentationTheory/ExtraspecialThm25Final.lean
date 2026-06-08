/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.ExtraspecialThm25Group
import OddOrder.GroupTheory.RepresentationTheory.CliffordConjugateChar

/-!
# BG Theorem 2.5 at the group level, with `hVP` discharged for an extraspecial `P`

`ExtraspecialThm25Group.lean` proves the group-level *divisibility* and `C_V(H)` conclusions of
Bender–Glauberman Theorem 2.5 **conditional** on
`hVP : Representation.IsIrreducible (ρ.comp P.subtype)` (BG Prop 2.2(a), `V_P` irreducible).
`CliffordConjugateChar.lean` discharges exactly that hypothesis for an extraspecial `P`
(`restriction_isIrreducible_of_extraspecial`: alg-closed Clifford = BG Prop 2.2(a), plus the
constituent faithfulness BG 2.10).

This file **combines** the two into the fully-grounded group-level BG Theorem 2.5 for an
**extraspecial** `P ⊴ G`: it takes only the §3 setup data (faithful irreducible `ρ` over an
algebraically closed field, `G = ⟨P, x⟩`, `x` centralising `Z(P)`, `C_P(xᵏ) ⊆ Z(P)`) and produces
`dim V ≡ ±1 (mod h)` (divisibility) and the `C_V(H)` dichotomy with **no representation-theoretic
hypothesis on the restriction remaining**.

The two helper conjugation automorphisms `conjNormalMulAut P x` (Clifford side) and
`conjAutOfNormal P x` (eigenspace/keystone side) coincide — both send `p ↦ x p x⁻¹` — so the public
hypotheses below use the single map `conjAutOfNormal`; the bridge
`conjNormalMulAut_eq_conjAutOfNormal` reconciles them when feeding the Clifford producer.

## Main results

* `conjNormalMulAut_eq_conjAutOfNormal` — the two conjugation automorphisms agree.
* `finrank_modEq_of_extraspecial` — **BG Theorem 2.5, divisibility**: `dim V ≡ ±1 (mod h)`.
* `finrank_eq_sub_one_of_extraspecial` — **BG Theorem 2.5, `C_V(H)`**: if `C_V(H) = 0` then
  `h = dim V + 1` (contrapositive: `h ≠ dim V + 1 ⟹ C_V(H) ≠ 0`).
-/

namespace OddOrder.RepresentationTheory

open Representation Module EigenspaceUnderCyclicAction

variable {G : Type*} [Group G]

/-- The Clifford-side conjugation automorphism `conjNormalMulAut P x` (`CliffordAlgClosed.lean`) and
the eigenspace/keystone-side `conjAutOfNormal P x` (`ExtraspecialThm25Group.lean`) of a normal
subgroup `P` coincide: both are the automorphism `p ↦ x p x⁻¹`. -/
theorem conjNormalMulAut_eq_conjAutOfNormal (P : Subgroup G) [P.Normal] (x : G) :
    conjNormalMulAut P x = conjAutOfNormal P x :=
  MulEquiv.ext fun p =>
    Subtype.ext (by rw [conjNormalMulAut_apply_coe, conjAutOfNormal_apply_coe])

/-- **BG Theorem 2.5, divisibility part, for an extraspecial `P` (fully grounded).**
Let `P ⊴ G` be extraspecial (`IsExtraspecial p ↥P`, `p` prime) inside a finite group `G`, carrying a
faithful irreducible representation `ρ` over an algebraically closed field `F` of characteristic
prime to `|P|`.  Let `x ∈ G` have order `h ≥ 2` with `(h, |P|) = 1` and `char ∤ h`, let `ε` be a
primitive `h`-th root of unity, and `G = ⟨P, x⟩`.  Assume the BG hypothesis `C_P(xᵏ) = Z(P)` for
`xᵏ ≠ 1`, split into `x` centralising `Z(P)` (`hxZ`, the `Z(P) ⊆ C_P(x)` direction) and
`C_P(xᵏ) ⊆ Z(P)` (`hCP`).  Then `dim V ≡ ±1 (mod h)`.

The restriction `V_P` is irreducible by `restriction_isIrreducible_of_extraspecial` (BG Prop 2.2(a)
alg-closed Clifford + BG 2.10), which discharges the `hVP` hypothesis of
`finrank_modEq_of_faithful_irreducible_of_centralizer`. -/
theorem finrank_modEq_of_extraspecial
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) [ρ.IsIrreducible] (hρf : Function.Injective ρ)
    (hPe : OddOrder.GroupTheory.IsExtraspecial p ↥P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hcop : Nat.Coprime h (Nat.card P))
    (hgen : Subgroup.closure ((P : Set G) ∪ {x}) = ⊤)
    (hxZ : ∀ z : ↥P, z ∈ Subgroup.center ↥P → conjAutOfNormal P x z = z)
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ q : ↥P,
        (conjAutOfNormal P x ^ k.val) q = q → q ∈ Subgroup.center ↥P) :
    ∃ (v₀ δ : ℤ), (δ = 1 ∨ δ = -1) ∧ (Module.finrank F V : ℤ) = (h : ℤ) * v₀ + δ := by
  have hVP : Representation.IsIrreducible (ρ.comp P.subtype) :=
    restriction_isIrreducible_of_extraspecial ρ hρf hPe x hgen
      (fun z hz => by rw [conjNormalMulAut_eq_conjAutOfNormal]; exact hxZ z hz)
  exact finrank_modEq_of_faithful_irreducible_of_centralizer P ρ hρf
    hPe.commutator_eq_center.le x hxh hh2 hprim hh hcop hVP hCP

/-- **BG Theorem 2.5, `C_V(H)` part, for an extraspecial `P` (fully grounded).**
Same setup as `finrank_modEq_of_extraspecial`; in addition assume `dim V ≥ 2` and that `x` has no
nonzero fixed vector (`C_V(H) = C_V(x) = V₀ = 0`).  Then `dim V = h - 1`, i.e. `h = dim V + 1`.
Equivalently (contrapositive), `h ≠ dim V + 1 ⟹ C_V(H) ≠ 0` — the half of Theorem 2.5 feeding the
even/odd contradiction of Theorem 3.4. -/
theorem finrank_eq_sub_one_of_extraspecial
    {F : Type*} [Field F] [IsAlgClosed F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) [P.Normal] [Invertible (Nat.card P : F)]
    (ρ : Representation F G V) [ρ.IsIrreducible] (hρf : Function.Injective ρ)
    (hPe : OddOrder.GroupTheory.IsExtraspecial p ↥P)
    (x : G) {h : ℕ} [NeZero h] (hxh : x ^ h = 1) (hh2 : 2 ≤ h)
    {ε : F} (hprim : IsPrimitiveRoot ε h) (hh : (h : F) ≠ 0)
    (hcop : Nat.Coprime h (Nat.card P))
    (hgen : Subgroup.closure ((P : Set G) ∪ {x}) = ⊤)
    (hxZ : ∀ z : ↥P, z ∈ Subgroup.center ↥P → conjAutOfNormal P x z = z)
    (hCP : ∀ k : ZMod h, k ≠ 0 → ∀ q : ↥P,
        (conjAutOfNormal P x ^ k.val) q = q → q ∈ Subgroup.center ↥P)
    (hV2 : 2 ≤ Module.finrank F V)
    (hCV : cyclicEigenspaceFinDim ε (ρ.asGroupHom x : Module.End F V) (0 : Fin h) = 0) :
    (Module.finrank F V : ℤ) = (h : ℤ) - 1 := by
  have hVP : Representation.IsIrreducible (ρ.comp P.subtype) :=
    restriction_isIrreducible_of_extraspecial ρ hρf hPe x hgen
      (fun z hz => by rw [conjNormalMulAut_eq_conjAutOfNormal]; exact hxZ z hz)
  exact finrank_eq_sub_one_of_faithful_irreducible_of_centralizer P ρ hρf
    hPe.commutator_eq_center.le x hxh hh2 hprim hh hcop hVP hCP hV2 hCV

end OddOrder.RepresentationTheory
