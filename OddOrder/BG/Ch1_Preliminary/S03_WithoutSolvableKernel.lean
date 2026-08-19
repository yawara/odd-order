/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch1_Preliminary.S03_FrobeniusActions
import OddOrder.BG.Ch1_Preliminary.S03e_Thm35
import OddOrder.Isaacs.Ch06_FrobeniusActions.KernelNilpotent

/-!
# BG §3: Lemma 3.2 and Theorem 3.5 without the solvability hypothesis

Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), Chapter I
§3, Lemma 3.2 and its **Note** (p. 17).

> **Lemma 3.2.** Let `G = KR` be a Frobenius group with solvable Frobenius kernel `K` and
> Frobenius complement `R` and suppose that `N ⊴ G`.  Assume that `K ⊄ N`.  For each subgroup
> `H` of `G` let `H̄ = HN/N`.  Then: **(a)** `N ⊂ K`; and **(b)** `Ḡ` is a Frobenius group with
> Frobenius kernel `K̄` and Frobenius complement `R̄`.
>
> **Note.** Since Thompson's Thesis (**G**, Theorem 10.2.1, p. 337) implies that the kernel of a
> Frobenius group is nilpotent (**G**, Theorem 10.3.1(iii), p. 339), the assumption that `K` is
> solvable is unnecessary.

**Theorem 3.5** carries the very same Note ("Just as for Lemma 3.2, Thompson's Thesis implies
that `K` is actually nilpotent, so the assumption that `K` is solvable is not necessary").

`isFrobeniusGroup_quotient_of_normal_not_le_kernel` (Lemma 3.2) and `S03e.thm35` /
`S03e.thm35_algClosed` (Theorem 3.5) all carry `Group.IsSolvable ↥K` as a hypothesis, i.e. they
formalize the results *before* their Notes.  This file discharges that hypothesis, so the book's
actual reach — the statements **plus** their Notes — is what the repository states.  Detected by
the BG per-result audit (issue 0177) as a specialization debt in §3.

## Why a separate file

Thompson's theorem lives in `Isaacs.Ch06_FrobeniusActions.KernelNilpotent`
(`IsFrobeniusGroup.isNilpotent_kernel`, Isaacs Thm 6.24 = BG Thm 3.7), and that file imports
`BG.Ch1_Preliminary.S03c_Thm37`, which in turn imports `S03_FrobeniusActions`.  Discharging the
hypothesis *in place* would therefore close an import cycle; the general forms have to live
downstream of both.  The `Group.IsSolvable`-carrying versions stay where they are and remain the
engines — they are used inside the §3 development, where solvability is already available.

## Main results

* `isSolvable_kernel_of_isFrobeniusGroup` — the Note itself: a Frobenius kernel is solvable.
* `bgLemma32` — Lemma 3.2 (a)+(b) with no solvability hypothesis.
* `bgThm35` / `bgThm35_algClosed` — Theorem 3.5 with no solvability hypothesis.

## References

* Bender, Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994), §3.
* Isaacs, _Finite Group Theory_ (AMS GSM 92, 2008), Theorem 6.24 (Thompson).
-/

namespace OddOrder.BG.Ch1.S03

open OddOrder.Isaacs.Ch06

/-- **The Note to BG Lemma 3.2 / Theorem 3.5** (pp. 17, 19): the kernel of a finite Frobenius
group is solvable.

This is Thompson's theorem (`IsFrobeniusGroup.isNilpotent_kernel` = Isaacs Thm 6.24 = BG
Thm 3.7) followed by "nilpotent ⟹ solvable"; it is exactly the observation BG makes to say
that the solvability hypothesis of Lemma 3.2 is unnecessary. -/
theorem isSolvable_kernel_of_isFrobeniusGroup {G : Type*} [Group G] [Finite G]
    {K R : Subgroup G} (h : IsFrobeniusGroup G K R) : Group.IsSolvable ↥K :=
  have : Group.IsNilpotent ↥K := h.isNilpotent_kernel
  inferInstance

/-- **BG Lemma 3.2 (a)+(b)** (p. 17), *including its Note* — no solvability hypothesis.

Let `G = KR` be a finite Frobenius group with kernel `K` and complement `R`, and let `N ⊴ G`
with `K ⊄ N`.  Then `N < K`, and `G/N` is again a Frobenius group with kernel `K̄ = KN/N` and
complement `R̄ = RN/N`.

`isFrobeniusGroup_quotient_of_normal_not_le_kernel` is the same statement with `Group.IsSolvable ↥K`
assumed; the hypothesis is discharged here by `isSolvable_kernel_of_isFrobeniusGroup`. -/
theorem bgLemma32 {G : Type*} [Group G] [Finite G] {K R N : Subgroup G} [N.Normal]
    (h : IsFrobeniusGroup G K R) (hKN : ¬ K ≤ N) :
    N < K ∧
      IsFrobeniusGroup (G ⧸ N) (K.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) :=
  isFrobeniusGroup_quotient_of_normal_not_le_kernel h hKN
    (isSolvable_kernel_of_isFrobeniusGroup h)

/-- **BG Lemma 3.2(a)** with no solvability hypothesis: `N ⊆ K`. -/
theorem normal_le_kernel_of_not_le' {G : Type*} [Group G] [Finite G] {K R N : Subgroup G}
    [N.Normal] (h : IsFrobeniusGroup G K R) (hKN : ¬ K ≤ N) : N ≤ K :=
  normal_le_kernel_of_not_le h hKN (isSolvable_kernel_of_isFrobeniusGroup h)

/-- The auxiliary clause `N ⊓ R = ⊥` of BG Lemma 3.2, with no solvability hypothesis. -/
theorem inf_complement_eq_bot_of_normal_not_le_kernel' {G : Type*} [Group G] [Finite G]
    {K R N : Subgroup G} [N.Normal] (h : IsFrobeniusGroup G K R) (hKN : ¬ K ≤ N) :
    N ⊓ R = ⊥ :=
  inf_complement_eq_bot_of_normal_not_le_kernel h hKN (isSolvable_kernel_of_isFrobeniusGroup h)

/-- **BG Theorem 3.5** (algebraically closed field), *including its Note* — no solvability
hypothesis.

`G = KR` a finite Frobenius group with kernel `K` and prime-order complement `R`, acting on
`V/F` with `char F ∤ |G|` and `F` algebraically closed.  If `dim C_V(R) = 1` then `K' ⊆ C_K(V)`. -/
theorem bgThm35_algClosed
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G)
    (hFrob : IsFrobeniusGroup G K R)
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 :=
  S03e.thm35_algClosed ρ K R hFrob (isSolvable_kernel_of_isFrobeniusGroup hFrob) hRp hchar hCV1

/-- **BG Theorem 3.5** (general field), *including its Note* — no solvability hypothesis.

`G = KR` a finite Frobenius group with kernel `K` and prime-order complement `R`, acting on
`V/F` with `char F ∤ |G|`.  If `C_V(R)` is one-dimensional then `K' ⊆ C_K(V)`.

`S03e.thm35` is the same statement with `Group.IsSolvable ↥K` assumed; the hypothesis is discharged
here by `isSolvable_kernel_of_isFrobeniusGroup`, which is exactly the book's Note. -/
theorem bgThm35
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (K R : Subgroup G)
    (hFrob : IsFrobeniusGroup G K R)
    (hRp : ∃ p : ℕ, p.Prime ∧ Nat.card ↥R = p)
    (hchar : (Nat.card G : F) ≠ 0)
    (hCV1 : Module.finrank F (Representation.invariants (ρ.comp R.subtype)) = 1) :
    ∀ g ∈ ⁅K, K⁆, ρ g = 1 :=
  S03e.thm35 ρ K R hFrob (isSolvable_kernel_of_isFrobeniusGroup hFrob) hRp hchar hCV1

end OddOrder.BG.Ch1.S03
