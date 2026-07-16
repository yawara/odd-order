/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch10_MoreTransfer.TransferIndexPrime
import OddOrder.GroupTheory.MackeyTransfer

/-!
# Isaacs §10A — Yoshida's theorem (pp. 295-296, 303-304)

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Chapter 10, §10A の中核:

* **Theorem 10.1 (Yoshida)**: `P ∈ Syl_p(G)`, `N = N_G(P)` が `p`-transfer を
  制御しないなら、`C_p ≀ C_p` は `P` の準同型像。

## 組み立て (本 leaf)

1. Lemma 10.11 (`exists_normal_index_prime_transfer_mem`) で `M ⊴ N` 指数 `p`
   と「全 transfer 値が `M` の像に入る」を取る。
2. `N ∖ M` から位数最小の元 `n` を選ぶ (`exists_minimal_orderOf_notMem`)。
   その位数は `p`-冪 (`orderOf_eq_prime_pow_of_minimal_notMem`)、
   よって `n ∈ P` (正規 Sylow の一意性)。
3. Mackey transfer (`transfer_eq_prod_doubleCoset`) を `n` で展開。積は `M` の
   像に入るが、自明 double coset (`N` 自身) の因子は `n` の `N`-共役の像で
   `M` の像に入らない (`M ⊴ N`)。因子論法 (`exists_ne_notMem_of_prod_mem`)
   で別の因子 `x ∉ N` も像の外。
4. その因子 = `S := xNx⁻¹ ⊓ P` への transfer 値。`n` の最小性から
   `R ≤ Q := xMx⁻¹ ⊓ P`、`|S : Q| ≤ p` から `Φ(S) ≤ Q`、よって
   `W(n) ∉ R·Φ(S)` — Theorem 10.9 が `C_p ≀ C_p ↞ P` を与える。
-/

namespace OddOrder.Isaacs.Ch10

open OddOrder.GroupTheory Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

section YoshidaSetup

/-- In a commutative group, if a finite product lies in a subgroup but one
factor does not, then some *other* factor also lies outside the subgroup. -/
lemma exists_ne_notMem_of_prod_mem {ι : Type*} [Fintype ι] {A : Type*}
    [CommGroup A] {f : ι → A} {B : Subgroup A}
    (hprod : ∏ i, f i ∈ B) {y : ι} (hy : f y ∉ B) :
    ∃ x, x ≠ y ∧ f x ∉ B := by
  classical
  by_contra hall
  push_neg at hall
  have h1 : ∏ i ∈ Finset.univ.erase y, f i ∈ B :=
    Subgroup.prod_mem _ fun i hi => hall i (Finset.ne_of_mem_erase hi)
  apply hy
  have h2 : f y = (∏ i, f i) * (∏ i ∈ Finset.univ.erase y, f i)⁻¹ := by
    rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ y)]
    group
  rw [h2]
  exact B.mul_mem hprod (B.inv_mem h1)

/-- A proper subgroup admits an element outside it of minimal order. -/
lemma exists_minimal_orderOf_notMem {N₀ : Type*} [Group N₀] [Finite N₀]
    {M : Subgroup N₀} (hM : M ≠ ⊤) :
    ∃ n : N₀, n ∉ M ∧ ∀ m : N₀, m ∉ M → orderOf n ≤ orderOf m := by
  classical
  letI : Fintype N₀ := Fintype.ofFinite N₀
  have hne : (Finset.univ.filter (fun n : N₀ => n ∉ M)).Nonempty := by
    obtain ⟨n, -, hn⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hM)
    exact ⟨n, by simp [hn]⟩
  obtain ⟨n, hn_mem, hn_min⟩ :=
    Finset.exists_min_image _ orderOf hne
  refine ⟨n, by simpa using hn_mem, fun m hm => hn_min m (by simp [hm])⟩

/-- If `M ⊴ N₀` has prime index `p` and `n ∉ M` has minimal order among the
elements outside `M`, then the order of `n` is a power of `p`: for every prime
`q ∣ o(n)` one has `n^q ∈ M` by minimality, so the image of `n` in `N₀ ⧸ M`
(a group of order `p`) has order `q`, forcing `q = p`. -/
lemma orderOf_eq_prime_pow_of_minimal_notMem {N₀ : Type*} [Group N₀] [Finite N₀]
    {M : Subgroup N₀} [M.Normal] (hidx : M.index = p)
    {n : N₀} (hn : n ∉ M) (hmin : ∀ m : N₀, m ∉ M → orderOf n ≤ orderOf m) :
    ∃ a : ℕ, orderOf n = p ^ a := by
  have hp_prime : p.Prime := hp.out
  have hord_pos : 0 < orderOf n := orderOf_pos n
  refine ⟨(Nat.primeFactorsList (orderOf n)).length,
    Nat.eq_prime_pow_of_unique_prime_dvd hord_pos.ne' ?_⟩
  intro q hq hq_dvd
  -- n^q has strictly smaller order, hence lies in M
  have hlt : orderOf (n ^ q) < orderOf n := by
    rw [orderOf_pow, Nat.gcd_eq_right hq_dvd]
    exact Nat.div_lt_self hord_pos hq.one_lt
  have hnq : n ^ q ∈ M := by
    by_contra hout
    exact absurd (hmin _ hout) (by omega)
  -- the image of n in N₀ ⧸ M has order q, and divides p
  have hbar_ne : ((n : N₀) : N₀ ⧸ M) ≠ 1 := by
    simpa [QuotientGroup.eq_one_iff] using hn
  have hbar_q : ((n : N₀) : N₀ ⧸ M) ^ q = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hnq
  have hbar_ord : orderOf ((n : N₀) : N₀ ⧸ M) = q := by
    rcases hq.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hbar_q) with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hbar_ne
    · exact h
  have hcard : Nat.card (N₀ ⧸ M) = p := by
    rw [← Subgroup.index_eq_card, hidx]
  have hdvd_p : q ∣ p := by
    rw [← hbar_ord, ← hcard]
    exact orderOf_dvd_natCard _
  exact (Nat.prime_dvd_prime_iff_eq hq hp_prime).mp hdvd_p

/-- A `p`-element of a group with a normal Sylow `p`-subgroup lies in it. -/
lemma mem_sylow_of_orderOf_prime_pow {N₀ : Type*} [Group N₀] [Finite N₀]
    (P₀ : Sylow p N₀) [(P₀ : Subgroup N₀).Normal]
    {n : N₀} {a : ℕ} (hord : orderOf n = p ^ a) :
    n ∈ (P₀ : Subgroup N₀) := by
  -- ⟨n⟩ is a p-group; ⟨n⟩ ⊔ P₀ is then a p-group containing the Sylow P₀
  have hzn : IsPGroup p (Subgroup.zpowers n) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers, hord]
  have hsup : IsPGroup p ↥(Subgroup.zpowers n ⊔ (P₀ : Subgroup N₀)) :=
    IsPGroup.to_sup_of_normal_right hzn P₀.2
  have heq : Subgroup.zpowers n ⊔ (P₀ : Subgroup N₀) = P₀ :=
    P₀.3 hsup le_sup_right
  have h1 : n ∈ Subgroup.zpowers n ⊔ (P₀ : Subgroup N₀) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers n)
  rwa [heq] at h1

/-- Conjugation by an element of the normalizer fixes the subgroup:
`conjSubgroup y H = H` for `y ∈ N_G(H)`. In particular this applies to any
subgroup and `y ∈ H` itself. -/
lemma conjSubgroup_eq_self_of_mem_normalizer {H : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (H : Set G)) : conjSubgroup y H = H := by
  ext g
  rw [mem_conjSubgroup]
  exact (Subgroup.mem_normalizer_iff''.mp hy g).symm

/-- If a Sylow subgroup satisfies `↑P ≤ x N x⁻¹` for `N := N_G(P)`, then
`x ∈ N`: the conjugate `x⁻¹ P x` is a Sylow subgroup contained in `N`, where
`P` is a *normal* Sylow subgroup, so `x⁻¹ P x = P` by maximality. -/
lemma mem_normalizer_of_sylow_le_conj (P : Sylow p G) {x : G}
    (hle : (P : Subgroup G)
      ≤ conjSubgroup x (Subgroup.normalizer ((P : Subgroup G) : Set G))) :
    x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
  set N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G) with hN_def
  -- the conjugate x⁻¹ P x lies in N
  have hconj_le : conjSubgroup x⁻¹ (P : Subgroup G) ≤ N := by
    rintro g hg
    rw [mem_conjSubgroup, inv_inv] at hg
    -- x * g * x⁻¹ ∈ P; and ↑P ≤ x N x⁻¹ gives g ∈ N
    have h1 : x * g * x⁻¹ ∈ conjSubgroup x N := hle hg
    rw [mem_conjSubgroup] at h1
    have h2 : x⁻¹ * (x * g * x⁻¹) * x = g := by group
    rwa [h2] at h1
  -- inside ↥N, the image of x⁻¹ P x is a p-subgroup; join with the normal
  -- Sylow P and use maximality
  have hP_le_N : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
  set P₀ : Sylow p ↥N := P.subtype hP_le_N with hP₀_def
  haveI : (P₀ : Subgroup ↥N).Normal := by
    rw [hP₀_def]
    show ((P : Subgroup G).subgroupOf N).Normal
    infer_instance
  have hinj : Function.Injective (MulAut.conj x⁻¹).toMonoidHom :=
    (MulAut.conj x⁻¹).injective
  have hpg0 : IsPGroup p ↥(conjSubgroup x⁻¹ (P : Subgroup G)) :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ hinj)
  have hpg : IsPGroup p ↥((conjSubgroup x⁻¹ (P : Subgroup G)).subgroupOf N) :=
    hpg0.of_equiv (Subgroup.subgroupOfEquivOfLe hconj_le).symm
  -- join with the normal Sylow P₀ and use maximality
  have hsup : IsPGroup p
      ↥((conjSubgroup x⁻¹ (P : Subgroup G)).subgroupOf N ⊔ (P₀ : Subgroup ↥N)) :=
    IsPGroup.to_sup_of_normal_right hpg P₀.2
  have heq := P₀.3 hsup le_sup_right
  have hconj_le_P :
      (conjSubgroup x⁻¹ (P : Subgroup G)).subgroupOf N ≤ (P₀ : Subgroup ↥N) := by
    rw [← heq]
    exact le_sup_left
  -- back in G: x⁻¹ P x ≤ P, hence equality by cardinality
  have hle_P : conjSubgroup x⁻¹ (P : Subgroup G) ≤ (P : Subgroup G) := by
    intro g hg
    have h3 : (⟨g, hconj_le hg⟩ : ↥N)
        ∈ (conjSubgroup x⁻¹ (P : Subgroup G)).subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      exact hg
    have h4 := hconj_le_P h3
    rw [hP₀_def] at h4
    have h5 : (⟨g, hconj_le hg⟩ : ↥N) ∈ (P : Subgroup G).subgroupOf N := h4
    rwa [Subgroup.mem_subgroupOf] at h5
  have hcard : Nat.card ↥(P : Subgroup G)
      ≤ Nat.card ↥(conjSubgroup x⁻¹ (P : Subgroup G)) :=
    le_of_eq (Nat.card_congr
      (Subgroup.equivMapOfInjective (P : Subgroup G) _ hinj).toEquiv)
  have heq2 : conjSubgroup x⁻¹ (P : Subgroup G) = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hle_P hcard
  -- conjugation by x⁻¹ fixing P means x normalizes P
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h6 := SetLike.ext_iff.mp heq2 h
  rw [mem_conjSubgroup, inv_inv] at h6
  exact h6.symm

end YoshidaSetup

end OddOrder.Isaacs.Ch10
