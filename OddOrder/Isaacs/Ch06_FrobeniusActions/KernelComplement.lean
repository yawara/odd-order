/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusGroup

/-!
# Isaacs Thm 6.7: self-centralizing normal subgroups are Frobenius kernels (p. 181)

**Isaacs, _Finite Group Theory_ (AMS GSM 92), §6A, Theorem 6.7 (p. 181).**

Let `N ⊴ G` (finite) with `C_G(n) ≤ N` for every nonidentity `n ∈ N`.  Then `N` is
complemented in `G`, and if `1 < N < G` then `G` is a Frobenius group with kernel `N`.

## Proof outline (the book's proof)

For each prime `p ∣ |N|`, pick `x ∈ N` of order `p` (Cauchy) and a Sylow `p`-subgroup
`S ≤ G` containing `x`.  Then `Z(S) ≤ C_G(x) ≤ N` and `Z(S)` is nontrivial (center of a
nontrivial `p`-group), so for `1 ≠ z ∈ Z(S)` we get `S ≤ C_G(z) ≤ N`.  Hence `N` contains
a full Sylow `p`-subgroup of `G` for every `p ∣ |N|`, so `(|N|, |G : N|) = 1` and
Schur-Zassenhaus provides a complement `A`.  When `⊥ < N < ⊤` both `N` and `A` are
nontrivial and `IsFrobeniusGroup.of_centralizer_kernel_le` (Thm 6.4 (4) ⇒ (1)) applies.

## Main result

- `OddOrder.Isaacs.Ch06.exists_isComplement'_of_centralizer_le`: **Isaacs Thm 6.7**.
-/

namespace OddOrder.Isaacs.Ch06

variable {G : Type*} [Group G]

section /- 6A: Thm 6.7 (p. 181) -/

/-- **Isaacs Thm 6.7** (p. 181): if `N ⊴ G` (finite) satisfies `C_G(n) ≤ N` for every
nonidentity `n ∈ N`, then `N` has a complement `A` in `G`; and whenever `⊥ ≠ N ≠ ⊤`, the
pair `(N, A)` makes `G` a Frobenius group with kernel `N`. -/
theorem exists_isComplement'_of_centralizer_le [Finite G] {N : Subgroup G} [N.Normal]
    (h4 : ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N) :
    ∃ A : Subgroup G, Subgroup.IsComplement' N A ∧
      (N ≠ ⊥ → N ≠ ⊤ → IsFrobeniusGroup G N A) := by
  classical
  -- Step 1: `N` is a normal Hall subgroup, i.e. `(|N|, [G:N]) = 1`.
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    by_contra hncop
    obtain ⟨p, hp, hpN, hpI⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
    haveI : Fact p.Prime := ⟨hp⟩
    -- Cauchy: an element `x ∈ N` of order `p`.
    obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpN
    set x : G := (x₀ : G) with hx_def
    have hx_ord : orderOf x = p := by rw [hx_def, Subgroup.orderOf_coe]; exact hx₀
    have hx_ne : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx_ord
      exact hp.one_lt.ne' hx_ord.symm
    have hxN : x ∈ N := x₀.2
    -- extend `⟨x⟩` to a Sylow `p`-subgroup `S` of `G`
    have hzp : IsPGroup p (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx_ord, pow_one]
    obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
    have hxS : x ∈ (S : Subgroup G) := hzS (Subgroup.mem_zpowers x)
    haveI hS_nontrivial : Nontrivial ↥(S : Subgroup G) :=
      ⟨⟨⟨x, hxS⟩, 1, fun h => hx_ne (congrArg Subtype.val h)⟩⟩
    -- the center of `S` is a nontrivial subgroup of `C_G(x) ≤ N`
    haveI : Nontrivial (Subgroup.center ↥(S : Subgroup G)) :=
      S.isPGroup'.center_nontrivial
    obtain ⟨z₀, hz₀_ne⟩ := exists_ne (1 : Subgroup.center ↥(S : Subgroup G))
    set z : G := ((z₀ : ↥(S : Subgroup G)) : G) with hz_def
    have hz_ne : z ≠ 1 := by
      intro h1
      exact hz₀_ne (Subtype.ext (Subtype.ext h1))
    have hz_comm : ∀ s : ↥(S : Subgroup G), (s : G) * z = z * (s : G) := by
      intro s
      have := (Subgroup.mem_center_iff.mp z₀.2 s)
      exact congrArg Subtype.val this
    have hzN : z ∈ N := by
      refine h4 x hxN hx_ne ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hz_comm ⟨x, hxS⟩).symm
    -- so `S ≤ C_G(z) ≤ N`
    have hS_le_N : (S : Subgroup G) ≤ N := by
      refine le_trans ?_ (h4 z hzN hz_ne)
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hz_comm ⟨s, hs⟩
    -- contradiction: the full `p`-part of `|G|` divides `|N|`, yet `p ∣ [G:N]`
    have hcardS : Nat.card ↥(S : Subgroup G) = p ^ (Nat.card G).factorization p :=
      S.card_eq_multiplicity
    have hdvd_pow : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := by
      rw [pow_succ, ← hcardS, ← Subgroup.card_mul_index (H := N)]
      exact mul_dvd_mul (hcardS ▸ Subgroup.card_dvd_of_le hS_le_N) hpI
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hdvd_pow
    omega
  -- Step 2: Schur-Zassenhaus complement.
  obtain ⟨A, hA⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  refine ⟨A, hA, fun hN_ne_bot hN_ne_top => ?_⟩
  -- Step 3: Frobenius via Thm 6.4 (4) ⇒ (1).
  have hA_ne_bot : A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.isComplement'_bot_right] at hA
    exact hN_ne_top hA
  exact IsFrobeniusGroup.of_centralizer_kernel_le inferInstance hA hN_ne_bot hA_ne_bot h4

end

end OddOrder.Isaacs.Ch06
