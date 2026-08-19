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
open scoped Pointwise commutatorElement

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

/-- The transfer of the trivial coefficient homomorphism is trivial. -/
theorem transfer_one [H.FiniteIndex] :
    MonoidHom.transfer (1 : ↥H →* A) = 1 := by
  classical
  ext g
  rw [MonoidHom.transfer_def (1 : ↥H →* A) default g]
  unfold Subgroup.leftTransversals.diff
  simp

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
  let := H.fintypeQuotientOfFiniteIndex
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
  let := H.fintypeQuotientOfFiniteIndex
  let : ∀ q : DoubleCoset.Quotient (K : Set G) H,
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
  have hM_normal : M.Normal := IsCoatom.normal_of_isPGroup hRp hM_coatom
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
    let : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers (⟨z, hzM⟩ : ↥M))
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

/-- Conjugation preserves the order of an element. -/
theorem orderOf_conj_eq (a t : G) : orderOf (t⁻¹ * a * t) = orderOf a := by
  have h := (MulAut.conj t⁻¹).orderOf_eq a
  simpa [MulAut.conj_apply] using h

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

variable {p : ℕ} [Fact p.Prime]

/-- **Hall–Wielandt** (the `p` odd, `A` abelian branch), in the form needed downstream:
if the Sylow `p`-subgroup `P` lies in `⁅G, G⁆` and `A ≤ P` is abelian and weakly closed
in `P`, then `P` already lies in `⁅N, N⁆` for `N = N_G(A)`. -/
theorem sylow_le_commutator_normalizer [Finite G] (hp2 : p ≠ 2) (P : Sylow p G)
    {A : Subgroup G} (hAP : A ≤ (P : Subgroup G))
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hwc : IsWeaklyClosed A (P : Subgroup G))
    (hPG' : (P : Subgroup G) ≤ commutator G) :
    (P : Subgroup G) ≤ (commutator ↥(Subgroup.normalizer (A : Set G))).map
      (Subgroup.normalizer (A : Set G)).subtype := by
  classical
  set N : Subgroup G := Subgroup.normalizer (A : Set G) with hN_def
  have hPN : (P : Subgroup G) ≤ N := le_normalizer_of_isWeaklyClosed hAP hwc
  set Nc : Subgroup G := (commutator ↥N).map N.subtype with hNc_def
  by_contra hcon
  -- an element of `P` outside `N'` of minimal order
  obtain ⟨x, ⟨hxP, hxNc⟩, hmin⟩ :=
    exists_min_orderOf (S := {y : G | y ∈ (P : Subgroup G) ∧ y ∉ Nc})
      (by
        obtain ⟨y, hyP, hyNc⟩ := SetLike.not_le_iff_exists.mp hcon
        exact ⟨y, hyP, hyNc⟩)
  have hmin' : ∀ y ∈ (P : Subgroup G), orderOf y < orderOf x → y ∈ Nc := by
    intro y hyP hlt
    by_contra hyNc
    exact absurd (hmin y ⟨hyP, hyNc⟩) (by omega)
  -- the abelian quotient `P/D` and its quotient character
  set D : Subgroup ↥(P : Subgroup G) := (Nc.subgroupOf (P : Subgroup G)) with hD_def
  have hNc_conj : ∀ u ∈ N, ∀ z ∈ Nc, u * z * u⁻¹ ∈ Nc := by
    rintro u hu - ⟨c, hc, rfl⟩
    refine ⟨⟨u, hu⟩ * c * ⟨u, hu⟩⁻¹, ?_, ?_⟩
    · exact (inferInstance : (_root_.commutator ↥N).Normal).conj_mem c hc _
    · rfl
  have hDnormal : D.Normal := by
    refine ⟨fun n hn r => ?_⟩
    rw [hD_def, Subgroup.mem_subgroupOf] at hn ⊢
    have := hNc_conj (r : G) (hPN r.2) (n : G) hn
    push_cast
    exact this
  have hcommD : commutator ↥(P : Subgroup G) ≤ D := by
    rw [hD_def, _root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_subgroupOf]
    refine ⟨⁅(⟨(a : G), hPN a.2⟩ : ↥N), (⟨(b : G), hPN b.2⟩ : ↥N)⁆, ?_, ?_⟩
    · rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · rfl
  let : CommGroup (↥(P : Subgroup G) ⧸ D) :=
    { (inferInstance : Group (↥(P : Subgroup G) ⧸ D)) with
      mul_comm := by
        intro a b
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
            refine hcommD ?_
            rw [_root_.commutator_def]
            have h1 : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
              rw [commutatorElement_def]
              group
            rw [h1]
            exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
              (Subgroup.mem_top _) }
  set lam : ↥(P : Subgroup G) →* (↥(P : Subgroup G) ⧸ D) :=
    QuotientGroup.mk' D with hlam_def
  have hlam : ∀ y : ↥(P : Subgroup G), lam y = 1 ↔ y ∈ D := by
    intro y
    rw [hlam_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hxD : (⟨x, hxP⟩ : ↥(P : Subgroup G)) ∉ D := by
    rw [hD_def, Subgroup.mem_subgroupOf]
    exact hxNc
  have hlamx : lam ⟨x, hxP⟩ ≠ 1 := fun h => hxD ((hlam _).mp h)
  -- the target is a `p`-group, so the `[G:P]`-th power of `lam x` is still nontrivial
  have hCp : IsPGroup p (↥(P : Subgroup G) ⧸ D) := IsPGroup.to_quotient P.2 D
  have hpow : lam ⟨x, hxP⟩ ^ (P : Subgroup G).index ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hCp) (lam ⟨x, hxP⟩)
    have hdvd : orderOf (lam ⟨x, hxP⟩) ∣ (P : Subgroup G).index :=
      orderOf_dvd_of_pow_eq_one h
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hlamx hk
    · rw [hk] at hdvd
      exact P.not_dvd_index (dvd_trans (dvd_pow_self p hkpos.ne') hdvd)
  -- the double-coset difference formula for `R = ⟨A, x⟩`
  set R : Subgroup G := A ⊔ Subgroup.zpowers x with hR_def
  have hRP : R ≤ (P : Subgroup G) := sup_le hAP (Subgroup.zpowers_le.mpr hxP)
  have hxR : x ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have : Finite (DoubleCoset.Quotient (R : Set G) (P : Subgroup G)) := Quotient.finite _
  have : Fintype (DoubleCoset.Quotient (R : Set G) (P : Subgroup G)) := Fintype.ofFinite _
  have hkey := transfer_eq_prod_doubleCoset_mul_pow lam hRP hxR
  have hzero : MonoidHom.transfer lam x = 1 := by
    have hker : commutator G ≤ (MonoidHom.transfer lam).ker :=
      Abelianization.commutator_subset_ker _
    exact MonoidHom.mem_ker.mp (hker (hPG' hxP))
  rw [hzero] at hkey
  obtain ⟨q, hq⟩ : ∃ q : DoubleCoset.Quotient (R : Set G) (P : Subgroup G),
      MonoidHom.transfer (mackeyRes lam q.out / mackeyResIncl lam hRP q.out)
        (⟨x, hxR⟩ : ↥R) ≠ 1 := by
    by_contra hall
    push Not at hall
    rw [Finset.prod_congr rfl fun q _ => hall q, Finset.prod_const_one, one_mul] at hkey
    exact hpow hkey.symm
  -- the local lemma applies inside `↥R`
  set g : G := q.out with hg_def
  set δ : ↥((conjSubgroup g (P : Subgroup G) ⊓ R).subgroupOf R) →* (↥(P : Subgroup G) ⧸ D) :=
    mackeyRes lam g / mackeyResIncl lam hRP g with hδ_def
  have hAR : A ≤ R := le_sup_left
  have hA₀normal : (A.subgroupOf R).Normal := by
    refine ⟨fun n hn r => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hrP := le_normalizer_of_isWeaklyClosed hAP hwc (hRP r.2)
    rw [Subgroup.mem_set_normalizer_iff] at hrP
    push_cast
    exact (hrP ((n : G))).mp hn
  have hA₀ab : ∀ a ∈ A.subgroupOf R, ∀ b ∈ A.subgroupOf R, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    refine Subtype.ext ?_
    push_cast
    exact hAab _ ha _ hb
  have hgen : (A.subgroupOf R) ⊔ Subgroup.zpowers (⟨x, hxR⟩ : ↥R) = ⊤ := by
    refine Subgroup.map_injective (Subgroup.subtype_injective R) ?_
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAR,
      MonoidHom.map_zpowers, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rfl
  -- the minimality hypothesis of the local lemma
  have hx1 : x ≠ 1 := fun h => hxNc (h ▸ Nc.one_mem)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp P.2) (⟨x, hxP⟩ : ↥(P : Subgroup G))
  rw [Subgroup.orderOf_mk] at hn
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rw [pow_zero, orderOf_eq_one_iff] at hn
      exact absurd hn hx1
    · exact h
  have hordlt : orderOf (x ^ p) < orderOf x := by
    have hdvd : p ∣ orderOf x := by
      rw [hn]
      exact dvd_pow_self p hnpos.ne'
    rw [orderOf_pow, Nat.gcd_eq_right hdvd, hn]
    refine Nat.div_lt_self (pow_pos (Fact.out : p.Prime).pos n) ?_
    exact (Fact.out : p.Prime).one_lt
  have hker : ∀ z ∈ powConjSet (⟨x, hxR⟩ : ↥R) p,
      ∀ hz : z ∈ (conjSubgroup g (P : Subgroup G) ⊓ R).subgroupOf R, δ ⟨z, hz⟩ = 1 := by
    intro z hz hzS
    obtain ⟨k, r, hzeq⟩ := hz
    have hzP : ((z : ↥R) : G) ∈ (P : Subgroup G) := hRP z.2
    have hzconj : ((z : ↥R) : G) ∈ conjSubgroup g (P : Subgroup G) :=
      (Subgroup.mem_subgroupOf.mp hzS).1
    have hgz : g⁻¹ * ((z : ↥R) : G) * g ∈ (P : Subgroup G) := mem_conjSubgroup.mp hzconj
    have hzval : ((z : ↥R) : G) = ((r : ↥R) : G)⁻¹ * (x ^ p) ^ k * ((r : ↥R) : G) := by
      rw [hzeq]
      push_cast
      rfl
    have hzord : orderOf ((z : ↥R) : G) ∣ orderOf (x ^ p) := by
      rw [hzval, orderOf_conj_eq]
      exact orderOf_dvd_of_mem_zpowers ⟨k, rfl⟩
    have hmemNc : ∀ y : G, y ∈ (P : Subgroup G) → orderOf y = orderOf ((z : ↥R) : G) →
        y ∈ Nc := by
      intro y hyP hyord
      by_cases hy1 : y = 1
      · rw [hy1]
        exact Nc.one_mem
      · refine hmin' y hyP ?_
        calc orderOf y = orderOf ((z : ↥R) : G) := hyord
          _ ≤ orderOf (x ^ p) := Nat.le_of_dvd (orderOf_pos _) hzord
          _ < orderOf x := hordlt
    have hzNc : ((z : ↥R) : G) ∈ Nc := hmemNc _ hzP rfl
    have hgzNc : g⁻¹ * ((z : ↥R) : G) * g ∈ Nc :=
      hmemNc _ hgz (orderOf_conj_eq _ _)
    rw [hδ_def, MonoidHom.div_apply, div_eq_one]
    have h1 : lam ⟨g⁻¹ * ((z : ↥R) : G) * g, hgz⟩ = 1 := by
      rw [hlam, hD_def, Subgroup.mem_subgroupOf]
      exact hgzNc
    have h2 : lam ⟨((z : ↥R) : G), hzP⟩ = 1 := by
      rw [hlam, hD_def, Subgroup.mem_subgroupOf]
      exact hzNc
    rw [show (mackeyRes lam g) ⟨z, hzS⟩ = lam ⟨g⁻¹ * ((z : ↥R) : G) * g, hgz⟩ from rfl,
      show (mackeyResIncl lam hRP g) ⟨z, hzS⟩ = lam ⟨((z : ↥R) : G), hzP⟩ from rfl, h1, h2]
  have hStop := eq_top_of_transfer_ne_one hp2 (isPGroup_of_le P.2 hRP) hA₀ab hgen _ hq hker
  -- `S = ⊤` puts `R` inside `g P g⁻¹`, so weak closure forces `g ∈ N`
  have hRconj : R ≤ conjSubgroup g (P : Subgroup G) := by
    intro w hw
    have : (⟨w, hw⟩ : ↥R) ∈ (conjSubgroup g (P : Subgroup G) ⊓ R).subgroupOf R := by
      rw [hStop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1
  have hAconj : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rintro - ⟨a, ha, rfl⟩
    have h1 : (MulAut.conj g⁻¹).toMonoidHom a = g⁻¹ * a * g := by
      change g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * a * g
      group
    rw [h1]
    exact mem_conjSubgroup.mp (hRconj (hAR ha))
  have hgN : g ∈ N := by
    have hfix := hwc g⁻¹ hAconj
    have : g⁻¹ ∈ N := by
      rw [hN_def, Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← hfix]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [← hfix] at hy
        obtain ⟨a, ha, hay⟩ := hy
        have : a = y := by
          have h1 : g⁻¹ * a * g⁻¹⁻¹ = g⁻¹ * y * g⁻¹⁻¹ := hay
          exact mul_left_cancel (mul_right_cancel h1)
        rwa [← this]
    simpa using N.inv_mem this
  -- but then every `δ`-value is trivial, contradicting the choice of `q`
  refine hq ?_
  have hzero : ∀ w : ↥((conjSubgroup g (P : Subgroup G) ⊓ R).subgroupOf R), δ w = 1 := by
    intro w
    have hwR : ((w : ↥R) : G) ∈ R := (w : ↥R).2
    have hwP : ((w : ↥R) : G) ∈ (P : Subgroup G) := hRP hwR
    have hgw : g⁻¹ * ((w : ↥R) : G) * g ∈ (P : Subgroup G) :=
      mem_conjSubgroup.mp (Subgroup.mem_subgroupOf.mp w.2).1
    -- `(g⁻¹ w g) w⁻¹ ∈ N' ⊓ P = D`
    have hdiff : (g⁻¹ * ((w : ↥R) : G) * g) * (((w : ↥R) : G))⁻¹ ∈ Nc := by
      have hwN : ((w : ↥R) : G) ∈ N := hPN hwP
      have hgN' : g⁻¹ ∈ N := N.inv_mem hgN
      refine ⟨⁅(⟨g⁻¹, hgN'⟩ : ↥N), (⟨((w : ↥R) : G), hwN⟩ : ↥N)⁆, ?_, ?_⟩
      · rw [_root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      · rw [commutatorElement_def]
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
        group
    rw [hδ_def, MonoidHom.div_apply, div_eq_one,
      show (mackeyRes lam g) w = lam ⟨g⁻¹ * ((w : ↥R) : G) * g, hgw⟩ from rfl,
      show (mackeyResIncl lam hRP g) w = lam ⟨((w : ↥R) : G), hwP⟩ from rfl]
    have hq1 : lam ⟨g⁻¹ * ((w : ↥R) : G) * g, hgw⟩ * (lam ⟨((w : ↥R) : G), hwP⟩)⁻¹ = 1 := by
      rw [← map_inv, ← map_mul]
      rw [hlam, hD_def, Subgroup.mem_subgroupOf]
      push_cast
      exact hdiff
    rw [← div_eq_one, div_eq_mul_inv]
    exact hq1
  have hδ1 : δ = 1 := by
    ext w
    exact hzero w
  rw [hδ1, transfer_one]
  rfl

/-- **The Hall–Wielandt theorem, transfer-control form** (M. Hall, Thm 14.4.2, the odd
`p`, abelian `A` branch): if `A ≤ P` is abelian and weakly closed in the Sylow
`p`-subgroup `P` and `p` is odd, then `N = N_G(A)` controls the `p`-transfer; in
particular `p ∤ |G^{ab}|` forces `p ∤ |N^{ab}|`.

This is the form consumed by Peterfalvi Part II, Ch. II, (17) (issue 9503). -/
theorem not_dvd_card_abelianization_normalizer_of_abelian [Finite G] (hp2 : p ≠ 2)
    (P : Sylow p G) {A : Subgroup G} (hAP : A ≤ (P : Subgroup G))
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hwc : IsWeaklyClosed A (P : Subgroup G))
    (hG : ¬ p ∣ Nat.card (Abelianization G)) :
    ¬ p ∣ Nat.card (Abelianization ↥(Subgroup.normalizer (A : Set G))) := by
  have hPG' := sylow_le_commutator_of_not_dvd P hG
  have hle := sylow_le_commutator_normalizer hp2 P hAP hAab hwc hPG'
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (A : Set G) :=
    le_normalizer_of_isWeaklyClosed hAP hwc
  refine not_dvd_card_abelianization_of_sylow_le_commutator (P.subtype hPN) ?_
  intro z hz
  have hzP : ((z : ↥(Subgroup.normalizer (A : Set G))) : G) ∈ (P : Subgroup G) :=
    Subgroup.mem_subgroupOf.mp hz
  obtain ⟨c, hc, hcz⟩ := hle hzP
  have : c = z := Subtype.ext hcz
  rwa [← this]

end MainTheorem

end OddOrder.GroupTheory
