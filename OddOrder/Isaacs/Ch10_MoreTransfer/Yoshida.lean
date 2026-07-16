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

/-- A subgroup of prime index is a coatom of the subgroup lattice. -/
private lemma isCoatom_of_index_prime'' {H₀ : Type*} [Group H₀] {Q : Subgroup H₀}
    (hidx : Q.index = p) : IsCoatom Q := by
  have hp_prime : p.Prime := hp.out
  constructor
  · intro htop
    rw [htop, Subgroup.index_top] at hidx
    exact hp_prime.one_lt.ne' hidx.symm
  · intro X hQX
    have hmul := Subgroup.relIndex_mul_index hQX.le
    rw [hidx] at hmul
    rcases hp_prime.eq_one_or_self_of_dvd X.index (Dvd.intro_left _ hmul) with h1 | hXp
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hrel : Q.relIndex X = 1 := by
        rw [hXp] at hmul
        exact Nat.eq_of_mul_eq_mul_right hp_prime.pos
          (by rw [one_mul]; exact hmul)
      exact hQX.not_ge (Subgroup.relIndex_eq_one.mp hrel)

/-- **Yoshida, main reduction step**: if the Mackey factor at a representative
`x ∉ N = N_G(P)` lies outside the image of `M` (where `M ⊴ N` has index `p` and
`n ∈ P ∖ M` has minimal order), then the `S₀ = (xNx⁻¹ ⊓ P)`-transfer of `n`
avoids `R·Φ(S₀)` and Theorem 10.9 yields `C_p ≀ C_p` as an image of `P`.

The Frattini bound is obtained via a kernel argument: the composite
`↥S₀ → ↥(xNx⁻¹) ≃ ↥N → ↥N ⧸ M` has kernel of index dividing `p`, so the kernel
contains `Φ(S₀)`; membership in the kernel means the conjugate `x⁻¹ s x` lies in
`M`. The `R` bound is the minimality of `n`. -/
private lemma yoshida_of_mackey_factor_notMem (P : Sylow p G)
    {N : Subgroup G} (hN_def : N = Subgroup.normalizer ((P : Subgroup G) : Set G))
    (hPN : (P : Subgroup G) ≤ N)
    {M : Subgroup ↥N} [M.Normal] (hM_idx : M.index = p)
    {n : ↥N} (hn_min : ∀ m : ↥N, m ∉ M → orderOf n ≤ orderOf m)
    (hnPg : ((n : ↥N) : G) ∈ (P : Subgroup G))
    {x : G} (hxN : x ∉ N)
    (hfac : MonoidHom.transfer
        (mackeyRes (K := (P : Subgroup G)) (Abelianization.of (G := ↥N)) x)
        ⟨((n : ↥N) : G), hnPg⟩
      ∉ M.map (Abelianization.of (G := ↥N))) :
    ∃ φ : ↥(P : Subgroup G) →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)),
      Function.Surjective φ := by
  classical
  set Pg : Subgroup G := (P : Subgroup G) with hPg_def
  set S₀ : Subgroup ↥Pg := (conjSubgroup x N ⊓ Pg).subgroupOf Pg with hS₀_def
  set nhat : ↥Pg := ⟨((n : ↥N) : G), hnPg⟩ with hnhat_def
  -- S₀ is proper: otherwise x would normalize P
  have hS₀_ne_top : S₀ ≠ ⊤ := by
    intro htop
    rw [hS₀_def, Subgroup.subgroupOf_eq_top] at htop
    apply hxN
    rw [hN_def]
    exact mem_normalizer_of_sylow_le_conj P (by
      rw [← hN_def]
      exact le_trans htop inf_le_left)
  -- the S₀-values conjugate into N
  have hmem_conj : ∀ s : ↥S₀, x⁻¹ * ((s : ↥Pg) : G) * x ∈ N := by
    intro s
    have h1 : ((s : ↥Pg) : G) ∈ conjSubgroup x N ⊓ Pg := s.2
    exact mem_conjSubgroup.mp h1.1
  -- Theorem 10.9 will conclude, provided the S₀-transfer avoids R·Φ(S₀)
  refine exists_surjective_wreath_of_transfer_notMem_orderClosure_sup_frattini
    (P := ↥Pg) P.2 hS₀_ne_top (x := nhat) ?_
  intro h109
  apply hfac
  -- factor the Mackey coefficient through the abelianization of S₀
  set ρ : Abelianization ↥S₀ →* Abelianization ↥N :=
    Abelianization.lift (mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) x)
    with hρ_def
  have hfac_eq : MonoidHom.transfer
      (mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) x) nhat
      = ρ (MonoidHom.transfer (Abelianization.of (G := ↥S₀)) nhat) := by
    have h1 : mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) x
        = ρ.comp (Abelianization.of (G := ↥S₀)) := by
      ext s
      simp [hρ_def]
    conv_lhs => rw [h1]
    rw [OddOrder.GroupTheory.transfer_comp_left]
    rfl
  rw [hfac_eq]
  -- it suffices that ρ maps the R·Φ image into the image of M
  have himage : ((Subgroup.closure {s : ↥S₀ | orderOf ((s : ↥Pg)) < orderOf nhat}
        ⊔ frattini ↥S₀).map (Abelianization.of (G := ↥S₀))).map ρ
      ≤ M.map (Abelianization.of (G := ↥N)) := by
    rw [Subgroup.map_map]
    have hcomp : ρ.comp (Abelianization.of (G := ↥S₀))
        = mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) x := by
      ext s
      simp [hρ_def]
    rw [hcomp, Subgroup.map_sup]
    apply sup_le
    · -- R-part: generators have small order, so their conjugates lie in M
      rw [MonoidHom.map_closure]
      rw [Subgroup.closure_le]
      rintro - ⟨s, hs_lt, rfl⟩
      show mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) x s
        ∈ M.map (Abelianization.of (G := ↥N))
      have hzmem : x⁻¹ * ((s : ↥Pg) : G) * x ∈ N := hmem_conj s
      have hzM : (⟨x⁻¹ * ((s : ↥Pg) : G) * x, hzmem⟩ : ↥N) ∈ M := by
        by_contra hout
        have h2 := hn_min _ hout
        -- order bridges through the subtype/conjugation embeddings
        have hordN : ∀ z : ↥N, orderOf z = orderOf ((z : G)) := fun z =>
          (orderOf_injective N.subtype N.subtype_injective z).symm
        have hordP : ∀ z : ↥Pg, orderOf z = orderOf ((z : G)) := fun z =>
          (orderOf_injective Pg.subtype Pg.subtype_injective z).symm
        have hconj_ord : orderOf (x⁻¹ * ((s : ↥Pg) : G) * x)
            = orderOf (((s : ↥Pg) : G)) := by
          have h5 := orderOf_injective (MulAut.conj x⁻¹).toMonoidHom
            (MulAut.conj x⁻¹).injective (((s : ↥Pg) : G))
          have h6 : (MulAut.conj x⁻¹).toMonoidHom (((s : ↥Pg) : G))
              = x⁻¹ * ((s : ↥Pg) : G) * x := by
            show x⁻¹ * _ * x⁻¹⁻¹ = _
            rw [inv_inv]
          rw [h6] at h5
          exact h5
        have h3 : orderOf (⟨x⁻¹ * ((s : ↥Pg) : G) * x, hzmem⟩ : ↥N)
            = orderOf ((s : ↥Pg)) := by
          rw [hordN, hordP]
          exact hconj_ord
        have h7 : orderOf n = orderOf nhat := by
          rw [hordN n, hordP nhat]
        have hs_lt' : orderOf ((s : ↥Pg)) < orderOf nhat := hs_lt
        rw [← h3] at hs_lt'
        rw [h7] at h2
        omega
      exact Subgroup.mem_map_of_mem _ hzM
    · -- Φ-part: the kernel of S₀ → N ⧸ M has index dividing p
      -- the inclusion of S₀ into the conjugate subgroup
      set φ₀ : ↥S₀ →* ↥(conjSubgroup x N) :=
        { toFun := fun s => ⟨((s : ↥Pg) : G), s.2.1⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl } with hφ₀_def
      -- the conjugation isomorphism ↥N ≃* ↥(xNx⁻¹)
      set e : ↥N ≃* ↥(conjSubgroup x N) :=
        Subgroup.equivMapOfInjective N (MulAut.conj x).toMonoidHom
          (MulAut.conj x).injective with he_def
      set ψ : ↥S₀ →* ↥N ⧸ M :=
        (QuotientGroup.mk' M).comp (e.symm.toMonoidHom.comp φ₀) with hψ_def
      -- Φ(S₀) ≤ ker ψ
      have hker_idx : ψ.ker.index ∣ p := by
        rw [Subgroup.index_ker]
        have h10 := Subgroup.card_subgroup_dvd_card ψ.range
        rwa [show Nat.card (↥N ⧸ M) = p by
          rw [← Subgroup.index_eq_card, hM_idx]] at h10
      have hΦ_ker : frattini ↥S₀ ≤ ψ.ker := by
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _ hker_idx) with h11 | h11
        · rw [Subgroup.index_eq_one.mp h11]
          exact le_top
        · exact frattini_le_coatom (isCoatom_of_index_prime'' h11)
      -- membership in the kernel means the conjugate lies in M
      rw [Subgroup.map_le_iff_le_comap]
      intro s hsΦ
      rw [Subgroup.mem_comap]
      have hker := hΦ_ker hsΦ
      rw [MonoidHom.mem_ker, hψ_def] at hker
      have hM_mem : e.symm (φ₀ s) ∈ M := by
        have h12 : (QuotientGroup.mk' M) (e.symm (φ₀ s)) = 1 := hker
        exact (QuotientGroup.eq_one_iff _).mp h12
      -- the kernel membership identifies the conjugate value inside M
      have hval : (⟨x⁻¹ * ((s : ↥Pg) : G) * x, hmem_conj s⟩ : ↥N) = e.symm (φ₀ s) := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply]
        refine Subtype.ext ?_
        show x * (x⁻¹ * ((s : ↥Pg) : G) * x) * x⁻¹ = ((s : ↥Pg) : G)
        group
      have hvalue : mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) x s
          = Abelianization.of ⟨x⁻¹ * ((s : ↥Pg) : G) * x, hmem_conj s⟩ := rfl
      rw [hvalue, hval]
      exact Subgroup.mem_map_of_mem _ hM_mem
  exact himage (Subgroup.mem_map_of_mem ρ h109)

end YoshidaSetup

/-- **Isaacs Theorem 10.1 (Yoshida's theorem)**: let `P` be a Sylow
`p`-subgroup of the finite group `G` and `N = N_G(P)`. If `N` does not control
`p`-transfer — expressed as the image of the `G`-transfer to `P^{ab}` being
properly contained in the image of the `N`-level transfer — then `C_p ≀ C_p`
is a homomorphic image of `P`.

**組み立て**: Lemma 10.11 で `M ⊴ N` (指数 `p`, 全 transfer 値が像に入る) を
取り、`N ∖ M` の位数最小元 `n` (p-冪位数 → `n ∈ P`) で Mackey transfer を展開。
自明 double coset の因子は `n` の `N`-共役の像で `M` の像に入らない
(指数 1 の transfer 評価 + `M ⊴ N`)。よって別の代表 `x ∉ N` の因子も像の外で、
`yoshida_of_mackey_factor_notMem` (Thm 10.9 への還元) が結論を与える。 -/
theorem exists_surjective_wreath_of_transfer_range_lt (P : Sylow p G)
    (hlt : (MonoidHom.transfer
        (Abelianization.of (G := ↥(P : Subgroup G)))).range
      < (MonoidHom.transfer (transferRes Subgroup.le_normalizer
          (Abelianization.of (G := ↥(P : Subgroup G))))).range) :
    ∃ φ : ↥(P : Subgroup G) →* (Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p)),
      Function.Surjective φ := by
  classical
  have hp_prime : p.Prime := hp.out
  set Pg : Subgroup G := (P : Subgroup G) with hPg_def
  set N : Subgroup G := Subgroup.normalizer (Pg : Set G) with hN_def
  have hPN : Pg ≤ N := Subgroup.le_normalizer
  -- Step 1: Lemma 10.11
  obtain ⟨M, hM_normal, hM_idx, hVM⟩ :=
    exists_normal_index_prime_transfer_mem (P := Pg) (N := N) P.2 hPN hlt
  -- N' ≤ M and the pullback of the image of M
  have hcomm_le : _root_.commutator ↥N ≤ M := by
    have hQcard : Nat.card (↥N ⧸ M) = p := by
      rw [← Subgroup.index_eq_card, hM_idx]
    haveI : IsCyclic (↥N ⧸ M) := isCyclic_of_prime_card hQcard
    letI : CommGroup (↥N ⧸ M) := IsCyclic.commGroup
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp ⟨⟨mul_comm⟩⟩
  have hker_le : (Abelianization.of (G := ↥N)).ker ≤ M := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have h1 : z ∈ _root_.commutator ↥N := by
      rw [← QuotientGroup.eq_one_iff z]
      exact hz
    exact hcomm_le h1
  have hM_pull : ∀ z : ↥N,
      Abelianization.of (G := ↥N) z ∈ M.map (Abelianization.of (G := ↥N)) ↔ z ∈ M := by
    intro z
    constructor
    · intro hmem
      have h1 : z ∈ (M.map (Abelianization.of (G := ↥N))).comap
          (Abelianization.of (G := ↥N)) := hmem
      rw [Subgroup.comap_map_eq, sup_of_le_left hker_le] at h1
      exact h1
    · exact fun h => Subgroup.mem_map_of_mem _ h
  -- Step 2: minimal-order n outside M; it is a p-element, hence in P
  have hM_ne_top : M ≠ ⊤ := by
    intro htop
    rw [htop, Subgroup.index_top] at hM_idx
    exact hp_prime.one_lt.ne' hM_idx.symm
  obtain ⟨n, hnM, hn_min⟩ := exists_minimal_orderOf_notMem hM_ne_top
  obtain ⟨a, ha⟩ := orderOf_eq_prime_pow_of_minimal_notMem hM_idx hnM hn_min
  set P₀ : Sylow p ↥N := P.subtype hPN with hP₀_def
  haveI : (P₀ : Subgroup ↥N).Normal := by
    rw [hP₀_def]
    show (Pg.subgroupOf N).Normal
    rw [hN_def, hPg_def]
    infer_instance
  have hnP₀ : n ∈ (P₀ : Subgroup ↥N) := mem_sylow_of_orderOf_prime_pow P₀ ha
  have hnPg : ((n : ↥N) : G) ∈ Pg := hnP₀
  -- Step 3: expand the transfer at n by the Mackey formula
  haveI : Finite (DoubleCoset.Quotient (Pg : Set G) N) := Quotient.finite _
  letI : Fintype (DoubleCoset.Quotient (Pg : Set G) N) := Fintype.ofFinite _
  have htotal := hVM ((n : ↥N) : G)
  rw [transfer_eq_prod_doubleCoset (H := N) (K := Pg)
    (Abelianization.of (G := ↥N)) hnPg] at htotal
  -- Step 4: the trivial double-coset factor lies outside the image of M
  set q₁ : DoubleCoset.Quotient (Pg : Set G) N := DoubleCoset.mk Pg N 1 with hq₁_def
  have hyN : q₁.out ∈ N := by
    obtain ⟨h₀, k₀, hh₀, hk₀, hout⟩ := DoubleCoset.mk_out_eq_mul Pg N 1
    rw [hq₁_def, hout]
    exact N.mul_mem (N.mul_mem (hPN hh₀) N.one_mem) hk₀
  have hJy_idx : ((conjSubgroup q₁.out N ⊓ Pg).subgroupOf Pg).index = 1 := by
    rw [conjSubgroup_eq_self_of_mem_normalizer (Subgroup.le_normalizer hyN),
      inf_eq_right.mpr hPN, Subgroup.subgroupOf_self, Subgroup.index_top]
  have hfactor_y : MonoidHom.transfer
      (mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) q₁.out)
      ⟨((n : ↥N) : G), hnPg⟩
      ∉ M.map (Abelianization.of (G := ↥N)) := by
    obtain ⟨r, hr⟩ := OddOrder.GroupTheory.exists_transfer_eq_conj_of_index_eq_one
      hJy_idx (mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) q₁.out)
      ⟨((n : ↥N) : G), hnPg⟩
    rw [hr]
    -- the value is the image of an N-conjugate of n
    have hzN : (((r : ↥Pg) : G)) * q₁.out ∈ N := N.mul_mem (hPN r.2) hyN
    set zhat : ↥N := ⟨((r : ↥Pg) : G) * q₁.out, hzN⟩ with hzhat_def
    have hwN : q₁.out⁻¹ * ((r⁻¹ * ⟨((n : ↥N) : G), hnPg⟩ * r : ↥Pg) : G) * q₁.out
        ∈ N := by
      have h2 : q₁.out⁻¹ * ((r⁻¹ * ⟨((n : ↥N) : G), hnPg⟩ * r : ↥Pg) : G) * q₁.out
          = zhat⁻¹ * n * zhat := by
        rw [hzhat_def]
        push_cast
        group
      rw [h2]
      exact (zhat⁻¹ * n * zhat).2
    have hvalue : mackeyRes (K := Pg) (Abelianization.of (G := ↥N)) q₁.out
        (⟨r⁻¹ * ⟨((n : ↥N) : G), hnPg⟩ * r, by
          rw [Subgroup.index_eq_one.mp hJy_idx]; trivial⟩)
        = Abelianization.of (G := ↥N)
            ⟨q₁.out⁻¹ * ((r⁻¹ * ⟨((n : ↥N) : G), hnPg⟩ * r : ↥Pg) : G) * q₁.out,
              hwN⟩ := rfl
    rw [hvalue, hM_pull]
    -- the conjugate ẑ⁻¹ n ẑ lies outside M since M ⊴ N and n ∉ M
    have hw_eq : (⟨q₁.out⁻¹ * ((r⁻¹ * ⟨((n : ↥N) : G), hnPg⟩ * r : ↥Pg) : G) * q₁.out,
          hwN⟩ : ↥N)
        = zhat⁻¹ * n * zhat := by
      refine Subtype.ext ?_
      rw [hzhat_def]
      push_cast
      group
    rw [hw_eq]
    intro hmem
    apply hnM
    have h3 := hM_normal.conj_mem _ hmem zhat
    have h4 : zhat * (zhat⁻¹ * n * zhat) * zhat⁻¹ = n := by group
    rwa [h4] at h3
  -- Step 5: some factor at a representative outside N avoids the image of M
  obtain ⟨q₂, hq₂_ne, hq₂_notin⟩ := exists_ne_notMem_of_prod_mem htotal hfactor_y
  have hxN : q₂.out ∉ N := by
    intro hxN'
    apply hq₂_ne
    have h5 : DoubleCoset.mk Pg N q₂.out = DoubleCoset.mk Pg N 1 := by
      rw [DoubleCoset.eq]
      exact ⟨1, Pg.one_mem, q₂.out⁻¹, N.inv_mem hxN', by group⟩
    rw [hq₁_def, ← h5, DoubleCoset.out_eq']
  -- Step 6: conclude by the main reduction
  exact yoshida_of_mackey_factor_notMem P hN_def hPN hM_idx hn_min hnPg hxN hq₂_notin

end OddOrder.Isaacs.Ch10
