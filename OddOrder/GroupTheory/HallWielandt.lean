/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.MackeyTransfer
import OddOrder.GroupTheory.WeaklyClosed
import OddOrder.GroupTheory.FrattiniPGroup
import OddOrder.Isaacs.Ch10_MoreTransfer.TransferIndexPrime

/-!
# The Hall–Wielandt transfer theorem (odd `p`, abelian weakly closed `A`)

M. Hall, *The Theory of Groups* (1959), Theorem 14.4.2; the branch used by
T. Peterfalvi, *Character Theory for the Odd Order Theorem*, Part II, Ch. II, (17).

> Let `P` be a Sylow `p`-subgroup of a finite group `G` and let `A ≤ P` be abelian and
> weakly closed in `P` with respect to `G`.  If `p` is odd then `N = N_G(A)` controls
> `p`-transfer: `P ⊓ ⁅G, G⁆ = P ⊓ ⁅N, N⁆`.

The proof is the classical *detailed transfer* argument (it uses neither Alperin's
fusion theorem nor Grün's second theorem); see
[`notes/meta/hall_wielandt_proof.md`](../../notes/meta/hall_wielandt_proof.md) for the
full write-up and its verification, and issue 9503 for the context.

This file develops the transfer ingredients:

* `transfer_mul` / `transfer_div` — the transfer is multiplicative in the coefficient
  homomorphism;
* `transfer_comp_subtype_apply` — the transfer of a homomorphism that extends to the
  ambient group is the `index`-th power (formula (14) of the write-up);
* the resulting double-coset difference formula (formula (17)), on top of the Mackey
  formula `transfer_eq_prod_doubleCoset` (Isaacs Thm 10.10) already available.
-/

set_option autoImplicit false

namespace OddOrder.GroupTheory

open Subgroup MulAction
open scoped Pointwise

variable {G : Type*} [Group G] {H K : Subgroup G} {A : Type*} [CommGroup A]

section CoefficientLinearity

/-- **The transfer is multiplicative in the coefficient homomorphism.** -/
theorem transfer_mul [H.FiniteIndex] (ϕ ψ : ↥H →* A) :
    MonoidHom.transfer (ϕ * ψ) = MonoidHom.transfer ϕ * MonoidHom.transfer ψ := by
  classical
  ext g
  rw [MonoidHom.mul_apply, MonoidHom.transfer_def (ϕ * ψ) default g,
    MonoidHom.transfer_def ϕ default g, MonoidHom.transfer_def ψ default g]
  unfold Subgroup.leftTransversals.diff
  simp only [MonoidHom.mul_apply]
  rw [← Finset.prod_mul_distrib]

/-- **The transfer respects division of coefficient homomorphisms.** -/
theorem transfer_div [H.FiniteIndex] (ϕ ψ : ↥H →* A) :
    MonoidHom.transfer (ϕ / ψ) = MonoidHom.transfer ϕ / MonoidHom.transfer ψ := by
  classical
  ext g
  rw [MonoidHom.div_apply, MonoidHom.transfer_def (ϕ / ψ) default g,
    MonoidHom.transfer_def ϕ default g, MonoidHom.transfer_def ψ default g]
  unfold Subgroup.leftTransversals.diff
  simp only [MonoidHom.div_apply]
  rw [← Finset.prod_div_distrib]

/-- **Transfer of a globally defined character** (formula (14)): if the coefficient map
is the restriction of a homomorphism `ψ` on the ambient group, then the transfer is the
`index`-th power of `ψ`.

Each factor of the transfer product is `ψ(rep q)⁻¹ · ψ g · ψ(rep (g⁻¹ • q))`, and the
`rep`-terms cancel because `q ↦ g⁻¹ • q` permutes the cosets. -/
theorem transfer_comp_subtype_apply [H.FiniteIndex] (ψ : G →* A) (g : G) :
    MonoidHom.transfer (ψ.comp H.subtype) g = ψ g ^ H.index := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  set T : H.LeftTransversal := default with hT_def
  rw [MonoidHom.transfer_def (ψ.comp H.subtype) T g]
  unfold Subgroup.leftTransversals.diff
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
  have hstep : ∀ q : G ⧸ H,
      ψ ((T.2.leftQuotientEquiv q : G)⁻¹ * ((g • T).2.leftQuotientEquiv q : G))
        = (ψ (T.2.leftQuotientEquiv q : G))⁻¹
          * (ψ g * ψ (T.2.leftQuotientEquiv (g⁻¹ • q) : G)) := by
    intro q
    rw [smul_apply_eq_smul_apply_inv_smul g T q, smul_eq_mul, map_mul, map_mul, map_inv]
  rw [Finset.prod_congr rfl fun q _ => hstep q, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_const,
    Finset.card_univ]
  have hperm : ∏ q : G ⧸ H, ψ (T.2.leftQuotientEquiv (g⁻¹ • q) : G)
      = ∏ q : G ⧸ H, ψ (T.2.leftQuotientEquiv q : G) :=
    Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ fun q => rfl
  rw [hperm, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, mul_comm (ψ g ^ H.index),
    ← mul_assoc, inv_mul_cancel, one_mul]

end CoefficientLinearity

section DoubleCosetDifference

variable [H.FiniteIndex] [Fintype (DoubleCoset.Quotient (K : Set G) H)]
  [∀ q : DoubleCoset.Quotient (K : Set G) H,
    ((conjSubgroup q.out H ⊓ K).subgroupOf K).FiniteIndex]

/-- The Mackey stabiliser datum with the coefficient map *restricted* from `ϕ` (rather
than conjugated by the double-coset representative): the second term of the difference
`δ` in formula (17). -/
def mackeyResIncl (ϕ : ↥H →* A) (hKH : K ≤ H) (x : G) :
    ↥((conjSubgroup x H ⊓ K).subgroupOf K) →* A :=
  (ϕ.comp (Subgroup.inclusion hKH)).comp
    ((conjSubgroup x H ⊓ K).subgroupOf K).subtype

/-- **The index sum of the Mackey fibration** (formula (15)): the double cosets
decompose `G ⧸ H` with fibers `↥K ⧸ S_q`, so `∑_q [K : S_q] = [G : H]`. -/
theorem sum_index_mackey :
    ∑ q : DoubleCoset.Quotient (K : Set G) H,
        ((conjSubgroup q.out H ⊓ K).subgroupOf K).index = H.index := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  letI : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      Fintype (↥K ⧸ (conjSubgroup q.out H ⊓ K).subgroupOf K) := fun q =>
    ((conjSubgroup q.out H ⊓ K).subgroupOf K).fintypeQuotientOfFiniteIndex
  have h := Fintype.card_congr (dosetFiberEquiv (K := K) (H := H))
  rw [Fintype.card_sigma] at h
  simp only [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  exact h

/-- **The double-coset difference formula** (formula (17) of the write-up): for `k ∈ K`,

`transfer ϕ k = (∏_q transfer (δ_q) k) · ϕ(k)^{[G:H]}`,

where `δ_q = (mackeyRes ϕ q.out) / (mackeyResIncl ϕ hKH q.out)` compares the conjugated
coefficient map with the plain restriction of `ϕ`.

This is the Mackey formula (`transfer_eq_prod_doubleCoset`) combined with
`transfer_comp_subtype_apply` and the index sum. -/
theorem transfer_eq_prod_doubleCoset_mul_pow (ϕ : ↥H →* A) (hKH : K ≤ H) {k : G}
    (hk : k ∈ K) :
    MonoidHom.transfer ϕ k
      = (∏ q : DoubleCoset.Quotient (K : Set G) H,
          MonoidHom.transfer (mackeyRes ϕ q.out / mackeyResIncl ϕ hKH q.out) ⟨k, hk⟩)
        * ϕ ⟨k, hKH hk⟩ ^ H.index := by
  classical
  rw [transfer_eq_prod_doubleCoset ϕ hk]
  have hterm : ∀ q : DoubleCoset.Quotient (K : Set G) H,
      MonoidHom.transfer (mackeyRes ϕ q.out) (⟨k, hk⟩ : ↥K)
        = MonoidHom.transfer (mackeyRes ϕ q.out / mackeyResIncl ϕ hKH q.out) ⟨k, hk⟩
          * ϕ ⟨k, hKH hk⟩ ^ ((conjSubgroup q.out H ⊓ K).subgroupOf K).index := by
    intro q
    have h2 : MonoidHom.transfer (mackeyResIncl ϕ hKH q.out) (⟨k, hk⟩ : ↥K)
        = ϕ ⟨k, hKH hk⟩ ^ ((conjSubgroup q.out H ⊓ K).subgroupOf K).index := by
      rw [mackeyResIncl, transfer_comp_subtype_apply]
      rfl
    rw [transfer_div, MonoidHom.div_apply, h2, div_mul_cancel]
  rw [Finset.prod_congr rfl fun q _ => hterm q, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, sum_index_mackey]

end DoubleCosetDifference

section LocalLemma

variable {R : Type*} [Group R] {C : Type*} [CommGroup C]

/-- `X_R(x)`: the union of the `R`-conjugates of `⟨x^p⟩` (write-up (18)).  Every
nonidentity element has order strictly smaller than that of `x`. -/
def powConjSet (x : R) (p : ℕ) : Set R :=
  {y | ∃ (k : ℤ) (r : R), y = r⁻¹ * (x ^ p) ^ k * r}

theorem mem_powConjSet_self (x : R) (p : ℕ) : x ^ p ∈ powConjSet x p :=
  ⟨1, 1, by group⟩

theorem powConjSet_conj {x z : R} {p : ℕ} (hz : z ∈ powConjSet x p) (t : R) :
    t⁻¹ * z * t ∈ powConjSet x p := by
  obtain ⟨k, r, rfl⟩ := hz
  exact ⟨k, r * t, by group⟩

theorem powConjSet_zpow {x z : R} {p : ℕ} (hz : z ∈ powConjSet x p) (m : ℤ) :
    z ^ m ∈ powConjSet x p := by
  obtain ⟨k, r, rfl⟩ := hz
  refine ⟨k * m, r, ?_⟩
  rw [zpow_mul]
  induction m using Int.induction_on with
  | zero => group
  | succ i ih => rw [zpow_add_one, ih]; group
  | pred i ih => rw [zpow_sub_one, ih]; group

theorem powConjSet_pow {x z : R} {p : ℕ} (hz : z ∈ powConjSet x p) (m : ℕ) :
    z ^ m ∈ powConjSet x p := by
  have := powConjSet_zpow hz (m : ℤ)
  rwa [zpow_natCast] at this

/-- **The odd-prime local transfer lemma** (§3 of the write-up).

Let `R` be a finite `p`-group with `p` odd, let `A₀ ⊴ R` be abelian with `R = ⟨A₀, x⟩`,
and let `δ : S →* C` be a character of a subgroup `S ≤ R` into an abelian group.  If the
transfer of `δ` is nontrivial at `x` while `δ` kills `X_R(x) ∩ S`, then `S = R`.

The odd hypothesis enters exactly once: the `p` conjugates `y^j x y^{-j}` form the
arithmetic progression `c^j x` with `c = ⁅y, x⁆` central in `A₀`, so their product is
`c^{p(p-1)/2} x^p`, and `p ∣ p(p-1)/2` requires `p - 1` to be even. -/
theorem eq_top_of_transfer_ne_one [Finite R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hRp : IsPGroup p R) {A₀ : Subgroup R} [A₀.Normal]
    (hab : ∀ a ∈ A₀, ∀ b ∈ A₀, a * b = b * a) {x : R}
    (hgen : A₀ ⊔ Subgroup.zpowers x = ⊤)
    {S : Subgroup R} (δ : ↥S →* C)
    (hne : MonoidHom.transfer δ x ≠ 1)
    (hker : ∀ z ∈ powConjSet x p, ∀ hz : z ∈ S, δ ⟨z, hz⟩ = 1) :
    S = ⊤ := by
  classical
  have hp_prime : p.Prime := Fact.out
  by_contra hST
  obtain ⟨M, hM_coatom, hSM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom S).resolve_left hST
  haveI hM_normal : M.Normal := IsCoatom.normal_of_isPGroup hRp hM_coatom
  have hM_idx : M.index = p := by
    rw [Subgroup.index_eq_card]
    exact IsCoatom.card_quotient_of_isPGroup hRp hM_coatom
  set μ : ↥M →* C := MonoidHom.transfer (transferRes hSM δ) with hμ_def
  have hμx : MonoidHom.transfer μ x ≠ 1 := by
    rw [hμ_def, transfer_transfer]
    exact hne
  -- (24): `μ` kills `X_R(x) ∩ M`
  have h24 : ∀ z ∈ powConjSet x p, ∀ hz : z ∈ M, μ ⟨z, hz⟩ = 1 := by
    intro z hz hzM
    letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (⟨z, hzM⟩ : ↥M))
      (↥M ⧸ S.subgroupOf M))) := Fintype.ofFinite _
    rw [hμ_def, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    refine Finset.prod_eq_one fun q _ => ?_
    rw [transferRes_apply]
    refine hker _ ?_ _
    have hcoe : (((⟨q.out.out⁻¹ * (⟨z, hzM⟩ : ↥M) ^
          Function.minimalPeriod ((⟨z, hzM⟩ : ↥M) • ·) q.out * q.out.out,
        QuotientGroup.out_conj_pow_minimalPeriod_mem (S.subgroupOf M) _ q.out⟩ :
          ↥(S.subgroupOf M)) : ↥M) : R)
        = ((q.out.out : ↥M) : R)⁻¹ * z ^
            Function.minimalPeriod ((⟨z, hzM⟩ : ↥M) • ·) q.out
            * ((q.out.out : ↥M) : R) := by
      push_cast
      rfl
    rw [hcoe]
    exact powConjSet_conj (powConjSet_pow hz _) _
  by_cases hxM : x ∈ M
  · -- Case 2: `x ∈ M`, so some `y ∈ A₀ ∖ M` generates `R/M`
    have hA₀M : ¬ A₀ ≤ M := by
      intro hle
      have htop : (⊤ : Subgroup R) ≤ M := by
        rw [← hgen]
        exact sup_le hle (Subgroup.zpowers_le.mpr hxM)
      exact hM_coatom.1 (top_le_iff.mp htop)
    obtain ⟨y, hyA₀, hyM⟩ : ∃ y ∈ A₀, y ∉ M := by
      by_contra hcon
      push Not at hcon
      exact hA₀M hcon
    rw [OddOrder.Isaacs.Ch10.transfer_eq_prod_pow_conj_of_mem hM_idx μ hxM hyM] at hμx
    -- the conjugates form the progression `c ^ j * x`
    set c : R := y * x * y⁻¹ * x⁻¹ with hc_def
    have hcA₀ : c ∈ A₀ := by
      have h1 : x * y⁻¹ * x⁻¹ ∈ A₀ := ‹A₀.Normal›.conj_mem _ (A₀.inv_mem hyA₀) x
      have h2 : c = y * (x * y⁻¹ * x⁻¹) := by rw [hc_def]; group
      rw [h2]
      exact A₀.mul_mem hyA₀ h1
    have hmM : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ ∈ M := fun j => hM_normal.conj_mem x hxM (y ^ j)
    have hcM : c ∈ M := by
      have h1 := hmM 1
      rw [pow_one] at h1
      have h2 : c = (y * x * y⁻¹) * x⁻¹ := by rw [hc_def]
      rw [h2]
      exact M.mul_mem h1 (M.inv_mem hxM)
    -- the `p` conjugates form the progression `c ^ j * x`
    have hprog : ∀ j : ℕ, y ^ j * x * (y ^ j)⁻¹ = c ^ j * x := by
      intro j
      induction j with
      | zero => simp
      | succ i ih =>
        have hyc : y * c ^ i * y⁻¹ = c ^ i := by
          have := hab y hyA₀ (c ^ i) (A₀.pow_mem hcA₀ i)
          calc y * c ^ i * y⁻¹ = (c ^ i * y) * y⁻¹ := by rw [this]
            _ = c ^ i := by group
        have hstep : y ^ (i + 1) * x * (y ^ (i + 1))⁻¹
            = y * (y ^ i * x * (y ^ i)⁻¹) * y⁻¹ := by
          rw [pow_succ']
          group
        rw [hstep, ih]
        calc y * (c ^ i * x) * y⁻¹ = (y * c ^ i * y⁻¹) * (y * x * y⁻¹) := by group
          _ = c ^ i * (y * x * y⁻¹) := by rw [hyc]
          _ = c ^ i * (c * x) := by rw [hc_def]; group
          _ = c ^ (i + 1) * x := by rw [pow_succ]; group
    -- each conjugate has `p`-th power in `X_R(x) ∩ M`, so its `μ`-value has order `∣ p`
    have hpowp : ∀ j : ℕ, (μ ⟨y ^ j * x * (y ^ j)⁻¹, hmM j⟩) ^ p = 1 := by
      intro j
      rw [← map_pow]
      have hmem : ((⟨y ^ j * x * (y ^ j)⁻¹, hmM j⟩ : ↥M) ^ p : ↥M)
          = ⟨y ^ j * x ^ p * (y ^ j)⁻¹, hM_normal.conj_mem _ (M.pow_mem hxM p) (y ^ j)⟩ := by
        refine Subtype.ext ?_
        push_cast
        exact conj_pow
      rw [hmem]
      refine h24 _ ?_ _
      have hconj : y ^ j * x ^ p * (y ^ j)⁻¹ = ((y ^ j)⁻¹)⁻¹ * x ^ p * (y ^ j)⁻¹ := by group
      rw [hconj]
      exact powConjSet_conj (mem_powConjSet_self x p) _
    -- `μ(x)` and `μ(c)` have order dividing `p`
    have hx0 : (μ ⟨x, hxM⟩) ^ p = 1 := by
      have := hpowp 0
      simpa using this
    have hc0 : (μ ⟨c, hcM⟩) ^ p = 1 := by
      have h1 := hpowp 1
      have h2 : (⟨y ^ 1 * x * (y ^ 1)⁻¹, hmM 1⟩ : ↥M) = ⟨c, hcM⟩ * ⟨x, hxM⟩ := by
        refine Subtype.ext ?_
        push_cast
        rw [hprog 1, pow_one]
      rw [h2, map_mul, mul_pow, hx0, mul_one] at h1
      exact h1
    -- the product over the `p` conjugates is `μ(c) ^ (p(p-1)/2) · μ(x) ^ p = 1`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, p - 1 = 2 * m := by
      have hodd : Odd p := hp_prime.odd_of_ne_two hp2
      obtain ⟨k, hk⟩ := hodd
      exact ⟨k, by omega⟩
    have hsum : ∑ j ∈ Finset.range p, j = p * m := by
      refine Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) ?_
      rw [Finset.sum_range_id_mul_two p, hm]
      ring
    refine hμx ?_
    have hterm : ∀ j ∈ Finset.range p,
        μ ⟨y ^ j * x * (y ^ j)⁻¹, hmM j⟩ = μ ⟨c, hcM⟩ ^ j * μ ⟨x, hxM⟩ := by
      intro j _
      have h2 : (⟨y ^ j * x * (y ^ j)⁻¹, hmM j⟩ : ↥M) = ⟨c, hcM⟩ ^ j * ⟨x, hxM⟩ := by
        refine Subtype.ext ?_
        push_cast
        exact hprog j
      rw [h2, map_mul, map_pow]
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_const, Finset.card_range, hsum, pow_mul, hc0, one_pow, one_mul, hx0]
  · -- Case 1: `x ∉ M`, and the single orbit gives `μ (x ^ p)`
    rw [OddOrder.Isaacs.Ch10.transfer_eq_pow_of_notMem hM_idx μ hxM] at hμx
    exact hμx (h24 (x ^ p) (mem_powConjSet_self x p) _)

end LocalLemma

section MainTheorem

/-- **Weak closure forces `A ⊴ P`**: for `u ∈ P` the conjugate `A^u` again lies in `P`,
hence equals `A`.  In particular `P ≤ N_G(A)`. -/
theorem le_normalizer_of_isWeaklyClosed {A P : Subgroup G} (hAP : A ≤ P)
    (hwc : IsWeaklyClosed A P) : P ≤ Subgroup.normalizer (A : Set G) := by
  intro u hu
  have hconj : A.map (MulAut.conj u).toMonoidHom = A := by
    refine hwc u ?_
    rintro - ⟨a, ha, rfl⟩
    have : (MulAut.conj u).toMonoidHom a = u * a * u⁻¹ := rfl
    rw [this]
    exact P.mul_mem (P.mul_mem hu (hAP ha)) (P.inv_mem hu)
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hconj]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hconj] at hy
    obtain ⟨a, ha, hay⟩ := hy
    have hay' : u * a * u⁻¹ = u * y * u⁻¹ := hay
    have : a = y := by
      have h1 := mul_right_cancel hay'
      exact mul_left_cancel h1
    rwa [← this]

/-- A nonempty set of group elements contains one of minimal order. -/
theorem exists_min_orderOf {S : Set G} (hne : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, orderOf x ≤ orderOf y := by
  classical
  have h : ∃ n, ∃ x ∈ S, orderOf x = n := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨orderOf x, x, hx, rfl⟩
  obtain ⟨x, hxS, hx⟩ := Nat.find_spec h
  refine ⟨x, hxS, fun y hyS => ?_⟩
  rw [hx]
  exact Nat.find_le ⟨y, hyS, rfl⟩

end MainTheorem

end OddOrder.GroupTheory
