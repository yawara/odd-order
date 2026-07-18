/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Complement
import OddOrder.GroupTheory.SCN

/-!
# Bender–Glauberman Proposition 4.4(b) — `C_G(A) = A × H` for `A ∈ SCN(R)`

**BG Proposition 4.4(b)** (Bender–Glauberman, LMS LNS 188, p. 37; = Gorenstein,
_Finite Groups_, Theorem 7.6.5; = math-comp/odd-order `SCN_Sylow_cent_dprod`):

> If `R` is a Sylow `p`-subgroup of a finite group `G` and `A ∈ SCN(R)`, then
> `C_G(A) = A × H` for some `p'`-subgroup `H` of `G`.

Here `A ∈ SCN(R)` means (see `OddOrder.GroupTheory.IsSCN`) that `A` is a
self-centralizing normal abelian subgroup **of `R`**: as a subgroup `A' : Subgroup ↥R`
with `IsSCN A'`, i.e. `A' ⊴ R`, `A'` abelian, and `C_R(A') = A'` (centralizer inside `R`).
The corresponding subgroup of `G` is `A := A'.map R.subtype`.

## Main result

* `OddOrder.GroupTheory.centralizer_eq_dprod_of_isSCN_of_sylow`: with
  `A := A'.map (R : Subgroup G).subtype` and `C := C_G(A)`, there is a subgroup
  `H ≤ C` which is a `p'`-group (`¬ p ∣ |H|`), disjoint from `A` (`A ⊓ H = ⊥`),
  generating `C` together with `A` (`A ⊔ H = C`), and commuting elementwise with `A`.
  These four facts say exactly that `C = A × H` is an internal direct product with `H`
  a `p'`-group.

## Proof outline (Gorenstein 7.6.5)

Set `C = C_G(A)` and `M = N_G(A)`.

1. `A ≤ C` (as `A` is abelian) and `A ⊴ C` (indeed `A` is central in `C`, since every
   element of `C = C_G(A)` centralizes `A`).
2. `R ⊓ C = A` (the *SCN centralizer bridge*): an element of `R` centralizes `A` iff,
   viewed inside `R`, it centralizes `A'`, and `C_R(A') = A'` by `hA'.selfCentralizing`.
3. `A` is a Sylow `p`-subgroup of `C`. Both `R` and `C` sit inside `M = N_G(A)`
   (`R ≤ M` because `A ⊴ R`; `C ≤ M` because `C_G(A) ≤ N_G(A)`), `R` is a Sylow
   `p`-subgroup of `M`, and `C ⊴ M`. The general fact "a Sylow `p`-subgroup meets a
   normal subgroup in a Sylow `p`-subgroup of it" (`sylow_relIndex_normal_not_dvd`)
   gives `¬ p ∣ [C : R ⊓ C] = [C : A]`, so `A` is Sylow in `C`.
4. `[C : A]` is therefore coprime to `|A| = p^k`, and `A ⊴ C`, so **Schur–Zassenhaus**
   (`Subgroup.exists_right_complement'_of_coprime`) produces a complement `H` inside `C`.
   `H` is a `p'`-group (`|H| = [C : A]`), and since `A` is central in `C` (indeed
   `H ≤ C = C_G(A)`) `A` and `H` commute, so `C = A × H`.

## References

* Bender–Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994),
  §4, Proposition 4.4(b) (p. 37).
* Gorenstein, _Finite Groups_ (1968), Theorem 7.6.5.
* Tracking issue `issues/3012-prop44b-scn-centralizer-dprod.md`.
-/

namespace OddOrder.GroupTheory

/-- **Sylow-in-normal-subgroup** (index form): if `P` is a Sylow `p`-subgroup of a finite
group `M` and `N ⊴ M`, then `P ∩ N` is a Sylow `p`-subgroup of `N`; concretely the index
`[N : P ∩ N] = P.relIndex N` is prime to `p`.

Proof: by the second isomorphism theorem `[N : P ∩ N] = [P N : P] = [P ⊔ N : P]`, which
divides `[M : P]`, and `[M : P]` is prime to `p` since `P` is Sylow. The equality
`P.relIndex (P ⊔ N) = P.relIndex N` is obtained by cancelling `(P ⊓ N).relIndex P` in the
two tower factorisations of `(P ⊓ N).relIndex (P ⊔ N)`. -/
theorem sylow_relIndex_normal_not_dvd {M : Type*} [Group M] [Finite M] {p : ℕ}
    [Fact p.Prime] (P : Sylow p M) (N : Subgroup M) [N.Normal] :
    ¬ p ∣ (P : Subgroup M).relIndex N := by
  set Q : Subgroup M := (P : Subgroup M) with hQ
  -- Two tower factorisations of `(Q ⊓ N).relIndex (Q ⊔ N)`.
  have e2 : (Q ⊓ N).relIndex Q * Q.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (Q ⊓ N) Q (Q ⊔ N) inf_le_left le_sup_left
  have e3 : (Q ⊓ N).relIndex N * N.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (Q ⊓ N) N (Q ⊔ N) inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_sup_right] at e3
  -- `e3 : Q.relIndex N * N.relIndex Q = (Q ⊓ N).relIndex (Q ⊔ N)`
  have hqn : (Q ⊓ N).relIndex Q = N.relIndex Q := by
    rw [inf_comm]; exact Subgroup.inf_relIndex_right N Q
  rw [hqn] at e2
  -- `e2 : N.relIndex Q * Q.relIndex (Q ⊔ N) = (Q ⊓ N).relIndex (Q ⊔ N)`
  have hpos : 0 < N.relIndex Q := by
    haveI : Finite ↥Q := inferInstance
    have h : (N.subgroupOf Q).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.pos_of_ne_zero h
  have hmul : N.relIndex Q * Q.relIndex (Q ⊔ N) = N.relIndex Q * Q.relIndex N := by
    rw [e2, ← e3]; ring
  have hkey : Q.relIndex (Q ⊔ N) = Q.relIndex N := Nat.eq_of_mul_eq_mul_left hpos hmul
  have hdvd : Q.relIndex N ∣ Q.index := by
    rw [← hkey]; exact Subgroup.relIndex_dvd_index_of_le le_sup_left
  intro hp
  exact Sylow.not_dvd_index P (hp.trans hdvd)

/-- **Bender–Glauberman Proposition 4.4(b)** (= Gorenstein 7.6.5).

Let `R` be a Sylow `p`-subgroup of a finite group `G` and let `A' ∈ SCN(R)` (a
self-centralizing normal abelian subgroup of `R`, `hA' : IsSCN A'`). Writing
`A := A'.map (R : Subgroup G).subtype` for the corresponding subgroup of `G`, the
centralizer `C_G(A)` decomposes as an internal direct product `C_G(A) = A × H` with `H`
a `p'`-group: there is `H ≤ C_G(A)` with `¬ p ∣ |H|`, `A ⊓ H = ⊥`, `A ⊔ H = C_G(A)`, and
`A` commuting elementwise with `H`. -/
theorem centralizer_eq_dprod_of_isSCN_of_sylow {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]
    [Finite G] (R : Sylow p G) {A' : Subgroup ↥(R : Subgroup G)} (hA' : IsSCN A') :
    ∃ H : Subgroup G,
      ¬ p ∣ Nat.card ↥H ∧
      H ≤ Subgroup.centralizer (A'.map (R : Subgroup G).subtype : Set G) ∧
      A'.map (R : Subgroup G).subtype ⊓ H = ⊥ ∧
      A'.map (R : Subgroup G).subtype ⊔ H
        = Subgroup.centralizer (A'.map (R : Subgroup G).subtype : Set G) ∧
      ∀ a ∈ A'.map (R : Subgroup G).subtype, ∀ h ∈ H, a * h = h * a := by
  classical
  haveI hA'comm : IsMulCommutative A' := hA'.isMulCommutative
  set A : Subgroup G := A'.map (R : Subgroup G).subtype with hAdef
  set C : Subgroup G := Subgroup.centralizer (A : Set G) with hCdef
  set M : Subgroup G := Subgroup.normalizer (A : Set G) with hMdef
  -- Step 1: `A ≤ C` (as `A` is abelian).
  have hAleC : A ≤ C := by
    intro x hx
    rw [hAdef, Subgroup.mem_map] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hAdef, SetLike.mem_coe, Subgroup.mem_map] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    have hcomm : (a : ↥(R : Subgroup G)) * b = b * a :=
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A') ⟨b, hb⟩)
    have hval := congrArg (R : Subgroup G).subtype hcomm
    simp only [map_mul] at hval
    exact hval.symm
  -- `A ≤ R`.
  have hAleR : A ≤ (R : Subgroup G) := by
    rw [hAdef]; exact Subgroup.map_subtype_le A'
  -- Step 2: the SCN centralizer bridge `R ⊓ C = A`.
  have hbridge : (R : Subgroup G) ⊓ C = A := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxR, hxC⟩ := hx
      have hr : (⟨x, hxR⟩ : ↥(R : Subgroup G))
          ∈ Subgroup.centralizer (A' : Set ↥(R : Subgroup G)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        apply Subtype.ext
        change (w : G) * x = x * (w : G)
        have hwA : (w : G) ∈ A := by
          rw [hAdef]; exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
        have hxc := hxC
        rw [hCdef, Subgroup.mem_centralizer_iff] at hxc
        exact hxc (w : G) hwA
      rw [hA'.selfCentralizing] at hr
      rw [hAdef]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hr, rfl⟩
    · exact le_inf hAleR hAleC
  -- Step 3: `A` is a Sylow `p`-subgroup of `C`, i.e. `¬ p ∣ [C : A]`.
  -- `R ≤ M = N_G(A)` (because `A ⊴ R`).
  have hRM : (R : Subgroup G) ≤ M := by
    rw [hMdef, Subgroup.le_normalizer_iff]
    intro h hh k hk
    rw [hAdef, Subgroup.mem_map] at hk
    obtain ⟨a, ha, rfl⟩ := hk
    rw [hAdef, Subgroup.mem_map]
    exact ⟨⟨h, hh⟩ * a * ⟨h, hh⟩⁻¹, hA'.isNormal.conj_mem a ha ⟨h, hh⟩, by
      simp only [map_mul, map_inv]; rfl⟩
  -- `C ≤ M`.
  have hCM : C ≤ M := Subgroup.centralizer_le_normalizer _
  -- `C ⊴ M` (as `C_G(A) ⊴ N_G(A)`).
  haveI hN₀M : (C.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_centralizer_normalizer _
  -- Apply the Sylow-in-normal fact to `R` (Sylow of `M`) and `C ⊴ M`.
  have hnotdvd : ¬ p ∣ ((R : Subgroup G).subgroupOf M).relIndex (C.subgroupOf M) := by
    have h := sylow_relIndex_normal_not_dvd (R.subtype hRM) (C.subgroupOf M)
    rwa [Sylow.coe_subtype] at h
  have hnotdvd3 : ¬ p ∣ A.relIndex C := by
    rw [← hbridge, Subgroup.inf_relIndex_right, ← Subgroup.relIndex_subgroupOf hCM]
    exact hnotdvd
  -- `|A| = p ^ k`.
  have hAcard : ∃ k, Nat.card A = p ^ k := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp R.isPGroup'
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp
      (hn ▸ Subgroup.card_dvd_of_le hAleR)
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hAcard
  -- Coprimality for Schur–Zassenhaus: `Nat.Coprime |A| [C : A]`.
  have hcop : Nat.Coprime (Nat.card A) (A.relIndex C) := by
    rw [hk]
    exact Nat.Coprime.pow_left k (by rwa [(Fact.out : p.Prime).coprime_iff_not_dvd])
  -- Repackage for `A.subgroupOf C` inside `↥C`.
  have hcardN₀ : Nat.card ↥(A.subgroupOf C) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAleC).toEquiv
  have hcop' : Nat.Coprime (Nat.card ↥(A.subgroupOf C)) (A.subgroupOf C).index := by
    rw [hcardN₀]; exact hcop
  -- `A.subgroupOf C ⊴ C` (indeed `A` central in `C`).
  haveI hN₀C : (A.subgroupOf C).Normal := by
    constructor
    intro n hn c
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h2 : (c : G) ∈ Subgroup.centralizer (A : Set G) := c.2
    have hcomm : (n : G) * (c : G) = (c : G) * (n : G) :=
      Subgroup.mem_centralizer_iff.mp h2 (n : G) hn
    have hval : ((c * n * c⁻¹ : ↥C) : G) = (n : G) := by
      have hstep : (c : G) * (n : G) * (c : G)⁻¹ = (n : G) := by rw [← hcomm]; group
      push_cast
      simpa using hstep
    rw [hval]; exact hn
  -- Step 4: Schur–Zassenhaus in `↥C` gives a complement `H₀`.
  obtain ⟨H₀, hH₀⟩ := Subgroup.exists_right_complement'_of_coprime
    (N := A.subgroupOf C) hcop'
  -- `A = (A.subgroupOf C).map C.subtype` (since `A ≤ C`).
  have hAeq : (A.subgroupOf C).map C.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hAleC
  refine ⟨H₀.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · -- `H` is a `p'`-group.
    rw [Subgroup.card_subtype]
    have hcardH₀ : Nat.card ↥H₀ = (A.subgroupOf C).index := (hH₀.symm.index_eq_card).symm
    rw [hcardH₀]
    exact hnotdvd3
  · -- `H ≤ C`.
    exact Subgroup.map_subtype_le H₀
  · -- `A ⊓ H = ⊥`.
    rw [← hAeq, ← Subgroup.map_inf _ _ C.subtype C.subtype_injective,
      disjoint_iff.mp hH₀.disjoint, Subgroup.map_bot]
  · -- `A ⊔ H = C`.
    rw [← hAeq, ← Subgroup.map_sup, hH₀.sup_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · -- `A` and `H` commute (since `H ≤ C = C_G(A)`).
    intro a ha h hh
    have hhC : h ∈ C := Subgroup.map_subtype_le H₀ hh
    rw [hCdef, Subgroup.mem_centralizer_iff] at hhC
    exact hhC a ha

end OddOrder.GroupTheory
