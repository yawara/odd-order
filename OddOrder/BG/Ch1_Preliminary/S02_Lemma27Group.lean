/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke
import OddOrder.GroupTheory.CommGroupAut
import OddOrder.GroupTheory.PRank
import OddOrder.GroupTheory.RepresentationTheory.ElemAbelianAutAction

/-!
# BG §2 Lemma 2.7 in the book's own shape (`Q ⊆ Aut(P)`)

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), Chapter I
§2, Lemma 2.7 (pp. 16–17).

> Let `p ≠ q` be primes, let `P`, `Q` be elementary abelian of orders `p²`, `q²`, and suppose
> `Q ⊆ Aut(P)`.  Then **(a)** `q ∣ p − 1`, and **(b)** there are `a ∈ Q^#` and an integer `r`
> with `xᵃ = xʳ` for all `x ∈ P`, `r^q ≡ 1 (mod p)` and `r ≢ 1 (mod p)`.

## What this file adds

The mathematics is already done, twice:
`OddOrder.RepresentationTheory.elemAbelian_aut_action` (issue 3009, via **G** Thm 3.2.3) and
`prime_dvd_sub_one_of_faithful_rank_two` / `exists_powerMap_of_faithful_rank_two`
(issue 0150, via the Singer order bound).  Both are stated for a **module**: `P` is a
two-dimensional `𝔽_p`-space and the action is a faithful `Representation (ZMod p) Q P`.

`ElemAbelianAutAction.lean`'s docstring argues *in prose* that this faithfully renders BG's
`Q ⊆ Aut(P)`.  This file turns that argument into a theorem, so BG Lemma 2.7 is available with
`P` and `Q` *groups*, the action by *group automorphisms* (`φ : Q →* MulAut P` injective), and
the scalar an *integer* `r` — i.e. exactly as the book states it.  Detected by the BG per-result
audit (issue 0177) as the one packaging gap in §2.

No mathematics is reproved here: the rendering uses the existing bridges
`IsElementaryAbelian.zmodModule`, `OddOrder.BG.Ch1_Preliminary.mulAutToEnd` and
`OddOrder.GroupTheory.zmod_smul_ofMul`.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), §2.
-/

namespace OddOrder.BG.Ch1.S02

open OddOrder.GroupTheory OddOrder.RepresentationTheory

-- the `IsMulCommutative → CommGroup` instances are `scoped`.
open scoped IsMulCommutative

/-- **BG Lemma 2.7, group form** over an abstract `ZMod p`-module carrier.

The module structure on `Additive P` is an instance *parameter* rather than a `letI`-bound local
instance: with the local instance, `Module.Finite` / `FunLike` synthesis for `Additive P` gets
stuck (the trap recorded at `IsElementaryAbelian.addAutEquivGL`).  `bgLemma27` below only has to
supply the instance. -/
theorem elemAbelian_aut_action_ofModule {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {P : Type*} [Group P] [IsMulCommutative P] [Finite P] [Module (ZMod p) (Additive P)]
    (hPrank : Module.finrank (ZMod p) (Additive P) = 2)
    {Q : Type*} [Group Q] [Finite Q]
    (hQea : IsElementaryAbelian q Q) (hQcard : Nat.card Q = q ^ 2)
    (φ : Q →* MulAut P) (hφ : Function.Injective φ) :
    q ∣ p - 1 ∧
      ∃ a : Q, a ≠ 1 ∧ ∃ r : (ZMod p)ˣ, orderOf r = q ∧
        ∀ x : P, φ a x = x ^ (r : ZMod p).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Module.Finite (ZMod p) (Additive P) := Module.Finite.of_finite
  -- `Q ⊆ Aut(P)` becomes a faithful `𝔽_p`-linear representation on `Additive P`.
  have hinj : Function.Injective
      ((OddOrder.BG.Ch1_Preliminary.mulAutToEnd P p).comp φ) := by
    intro b b' h
    exact hφ (MulEquiv.ext fun x => congrArg (fun f => f (Additive.ofMul x)) h)
  obtain ⟨hdvd, a, ha, r, hr, hact⟩ :=
    elemAbelian_aut_action hpq hPrank hQea hQcard
      ((OddOrder.BG.Ch1_Preliminary.mulAutToEnd P p).comp φ) hinj
  refine ⟨hdvd, a, ha, r, hr, fun x => ?_⟩
  have h := hact (Additive.ofMul x)
  rw [MonoidHom.comp_apply, zmod_smul_ofMul] at h
  exact congrArg Additive.toMul h

/-- **BG Lemma 2.7** (Bender–Glauberman, LMS LNS 188, Lemma 2.7, pp. 16–17), stated as in the
book: `P` and `Q` are elementary abelian *groups* of orders `p²` and `q²`, and `Q ⊆ Aut(P)` is
an injective `φ : Q →* MulAut P`.  Then

* **(a)** `q ∣ p − 1`, and
* **(b)** there are `a ∈ Q^#` and `r` with `xᵃ = xʳ` for all `x ∈ P`, `r^q ≡ 1 (mod p)` and
  `r ≢ 1 (mod p)`.

All the mathematics is `OddOrder.RepresentationTheory.elemAbelian_aut_action`; this statement
supplies the rendering of `P` as a two-dimensional `𝔽_p`-space and converts the scalar
`r ∈ 𝔽_pˣ` into BG's integer congruences. -/
theorem bgLemma27 {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {P Q : Type*} [Group P] [Group Q] [Finite P] [Finite Q]
    (hPea : IsElementaryAbelian p P) (hPcard : Nat.card P = p ^ 2)
    (hQea : IsElementaryAbelian q Q) (hQcard : Nat.card Q = q ^ 2)
    (φ : Q →* MulAut P) (hφ : Function.Injective φ) :
    q ∣ p - 1 ∧
      ∃ a : Q, a ≠ 1 ∧ ∃ r : ℕ, (∀ x : P, φ a x = x ^ r) ∧
        r ^ q ≡ 1 [MOD p] ∧ ¬ (r ≡ 1 [MOD p]) := by
  haveI hp : Fact p.Prime := ‹_›
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  letI : IsMulCommutative P := IsMulCommutative.of_comm hPea.comm
  letI : Module (ZMod p) (Additive P) := hPea.zmodModule
  -- `|P| = p²` says exactly that `Additive P` is two-dimensional over `𝔽_p`.
  have hPrank : Module.finrank (ZMod p) (Additive P) = 2 := by
    have h := hPea.card_eq_pow_finrank
    rw [hPcard] at h
    exact (Nat.pow_right_injective hp.out.two_le) h.symm
  obtain ⟨hdvd, a, ha, r, hr, hact⟩ :=
    elemAbelian_aut_action_ofModule hpq hPrank hQea hQcard φ hφ
  have hrne : r ≠ 1 := fun h => by
    rw [h, orderOf_one] at hr
    exact (Fact.out : q.Prime).one_lt.ne hr
  have hcast : (((r : ZMod p).val : ℕ) : ZMod p) = (r : ZMod p) :=
    (ZMod.natCast_rightInverse (r : ZMod p))
  refine ⟨hdvd, a, ha, (r : ZMod p).val, hact, ?_, ?_⟩
  · -- `r^q ≡ 1 (mod p)`, from `orderOf r = q`
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [hcast, ← Units.val_pow_eq_pow_val, ← hr, pow_orderOf_eq_one, Units.val_one]
  · -- `r ≢ 1 (mod p)`, since `r ≠ 1` in `𝔽_pˣ`
    intro hone
    have h : (((r : ZMod p).val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mpr hone
    push_cast at h
    rw [hcast] at h
    exact hrne (Units.ext h)

end OddOrder.BG.Ch1.S02
