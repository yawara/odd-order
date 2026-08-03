/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.BrauerHomomorphism
import OddOrder.Algebra.ClassSum
import OddOrder.GroupTheory.PGroupRelIndex

/-!
# The kernel of the Brauer homomorphism

For a `p`-subgroup `P ≤ G` and a coefficient ring of characteristic `p`, the Brauer homomorphism
`Br_P` truncates to the part supported on `C_G(P)`.  On the fixed ring `(k[G])^P` its kernel is

`ker Br_P = ∑_{Q < P} Tr^P_Q ((k[G])^Q)`.

Both inclusions are elementary once the relative trace of a monomial is known to be an orbit sum
(`relTrace_single_apply`):

* `⊇` — the coefficient of `Tr^P_Q(a)` at a point `c` of `C_G(P)` is `[P : Q] · a c`, because
  every representative conjugates `c` to itself; and `p ∣ [P : Q]` for `Q < P` inside a
  `p`-group.
* `⊆` — a `P`-fixed `b` killed by `Br_P` is supported off `C_G(P)`, so each `g` in its support
  has stabiliser `Q = P ∩ C_G(g)` strictly smaller than `P`, and subtracting
  `Tr^P_Q(b_g · g)` — which is `b_g` times the orbit sum of `g` — removes a whole orbit from the
  support.  Induction on the size of the support finishes.

This is the computation behind Brauer's first main theorem, where `Br_P` is used to match blocks
of `G` with blocks of `N_G(P)`.

## Main results

* `OddOrder.GroupAlgebra.brauerProj_relTrace_eq_zero`
* `OddOrder.GroupAlgebra.brauerProj_eq_zero_iff` — the kernel description.
* `OddOrder.GroupAlgebra.brauerProj_eq_iff_sub_mem` — the Brauer quotient.
-/

namespace OddOrder.GroupAlgebra

open MonoidAlgebra

open scoped OddOrder.Conjugation

variable {k : Type*} [CommRing k] {G : Type*} [Group G]

section Kernel

variable {p : ℕ}

/-- **Relative traces from proper subgroups die under `Br_P`.**  The coefficient of `Tr^P_Q(a)`
at a point of `C_G(P)` is `[P : Q] · a c`, and `p ∣ [P : Q]`. -/
theorem brauerProj_relTrace_eq_zero [Finite G] (hchar : (p : k) = 0) {P Q : Subgroup G}
    (hdvd : p ∣ Q.relIndex P) (a : MonoidAlgebra k G) :
    brauerProj P (GAlgebra.relTrace Q P a) = 0 := by
  classical
  letI : Fintype (↥P ⧸ Q.subgroupOf P) := Fintype.ofFinite _
  have hindex : (Q.relIndex P : k) = 0 := by
    obtain ⟨t, ht⟩ := hdvd
    rw [ht, Nat.cast_mul, hchar, zero_mul]
  refine Finsupp.ext fun n => ?_
  rw [brauerProj_apply]
  by_cases hn : n ∈ Subgroup.centralizer (P : Set G)
  · rw [if_pos hn]
    set rep : ↥P ⧸ Q.subgroupOf P → G := fun x => ((x.out : ↥P) : G) with hrep
    have hR : GAlgebra.relTrace Q P a = ∑ x : ↥P ⧸ Q.subgroupOf P, rep x • a := rfl
    have hsplit : (∑ x : ↥P ⧸ Q.subgroupOf P, rep x • a) n
        = ∑ x : ↥P ⧸ Q.subgroupOf P, (rep x • a) n := Finsupp.finsetSum_apply _ _ _
    -- Every representative fixes `n`, so all the terms are `a n`.
    have hterm : ∀ x : ↥P ⧸ Q.subgroupOf P, (rep x • a) n = a n := by
      intro x
      rw [conj_smul_apply]
      congr 1
      have hcomm := (Subgroup.mem_centralizer_iff.mp hn) (rep x) (x.out : ↥P).2
      rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hR, hsplit, Finset.sum_congr rfl fun x _ => hterm x, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    have : (Nat.card (↥P ⧸ Q.subgroupOf P) : k) = 0 := hindex
    rw [this, zero_mul]
    rfl
  · rw [if_neg hn]
    rfl

open scoped Classical in
/-- **The kernel of the Brauer homomorphism on `(k[G])^P`.**  A `P`-fixed element is killed by
`Br_P` exactly when it is a sum of relative traces from proper subgroups of `P`. -/
theorem brauerProj_eq_zero_iff [Finite G] [Fact p.Prime] (hchar : (p : k) = 0)
    {P : Subgroup G} (hP : IsPGroup p ↥P) {b : MonoidAlgebra k G} (hb : ∀ u ∈ P, u • b = b) :
    brauerProj P b = 0 ↔
      b ∈ ⨆ Q : {Q : Subgroup G // Q < P}, GAlgebra.relTraceIdeal (Q : Subgroup G) P := by
  classical
  constructor
  · -- Peel off one `P`-orbit at a time.
    intro hbr
    suffices H : ∀ m : ℕ, ∀ c : MonoidAlgebra k G, c.support.card ≤ m →
        (∀ u ∈ P, u • c = c) → brauerProj P c = 0 →
        c ∈ ⨆ Q : {Q : Subgroup G // Q < P}, GAlgebra.relTraceIdeal (Q : Subgroup G) P from
      H b.support.card b le_rfl hb hbr
    intro m
    induction m with
    | zero =>
      intro c hcard _ _
      have hc0 : c = 0 :=
        Finsupp.support_eq_empty.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
      exact hc0 ▸ zero_mem _
    | succ m ih =>
      intro c hcard hcfix hcbr
      rcases eq_or_ne c 0 with rfl | hc0
      · exact zero_mem _
      obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hc0
      rw [Finsupp.mem_support_iff] at hg
      -- `g` is off the centraliser, so its stabiliser in `P` is proper.
      have hgc : g ∉ Subgroup.centralizer (P : Set G) := by
        intro hmem
        exact hg (by rw [← brauerProj_apply_of_mem hmem c, hcbr]; rfl)
      set Q : Subgroup G := P ⊓ Subgroup.centralizer ({g} : Set G) with hQ
      have hQlt : Q < P := by
        refine lt_of_le_of_ne inf_le_left fun hQP => hgc ?_
        refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
        have huQ : u ∈ Q := hQP ▸ hu
        exact ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp huQ).2)
          g (Set.mem_singleton g)).symm
      -- The orbit sum of `g` with coefficient `c g`.
      set t : MonoidAlgebra k G := GAlgebra.relTrace Q P (single g (c g)) with ht
      have htfix : ∀ u ∈ Q, u • (single g (c g) : MonoidAlgebra k G) = single g (c g) :=
        fun u hu => smul_single_of_mem_centralizer (Subgroup.mem_inf.mp hu).2 _
      have htmem : t ∈ GAlgebra.relTraceIdeal Q P := ⟨single g (c g), htfix, rfl⟩
      have htapp_pos : ∀ n : G, (∃ u ∈ P, u * g * u⁻¹ = n) → t n = c g := by
        letI := Fintype.ofFinite G
        intro n horb
        have h := relTrace_single_apply P g (c g) n
        rwa [if_pos horb] at h
      have htapp_neg : ∀ n : G, ¬ (∃ u ∈ P, u * g * u⁻¹ = n) → t n = 0 := by
        letI := Fintype.ofFinite G
        intro n horb
        have h := relTrace_single_apply P g (c g) n
        rwa [if_neg horb] at h
      -- `c - t` is still fixed, still killed by `Br_P`, and has a smaller support.
      have hdfix : ∀ u ∈ P, u • (c - t) = c - t := by
        intro u hu
        rw [smul_sub, hcfix u hu, ht, GAlgebra.smul_relTrace htfix hu]
      have hdvdQ : p ∣ Q.relIndex P := dvd_relIndex_of_lt_of_isPGroup hP hQlt
      have hdbr : brauerProj P (c - t) = 0 := by
        rw [sub_eq_add_neg, brauerProj_add, hcbr, ht, ← neg_one_smul k (GAlgebra.relTrace _ _ _),
          brauerProj_smul, brauerProj_relTrace_eq_zero hchar hdvdQ, smul_zero, add_zero]
      have hcconj : ∀ u ∈ P, ∀ x : G, c (u * x * u⁻¹) = c x :=
        (forall_mem_smul_eq_iff_apply P c).mp hcfix
      have hsub : ∀ n : G, (c - t) n = c n - t n := fun _ => rfl
      have hsupp : (c - t).support ⊆ c.support.erase g := by
        intro n hn
        rw [Finsupp.mem_support_iff, hsub n] at hn
        by_cases horb : ∃ u ∈ P, u * g * u⁻¹ = n
        · obtain ⟨u, hu, hun⟩ := horb
          rw [htapp_pos n ⟨u, hu, hun⟩, ← hun, hcconj u hu g, sub_self] at hn
          exact absurd rfl hn
        · rw [htapp_neg n horb, sub_zero] at hn
          refine Finset.mem_erase.mpr ⟨fun hng => horb ⟨1, P.one_mem, by rw [hng]; group⟩, ?_⟩
          exact Finsupp.mem_support_iff.mpr hn
      have hdcard : (c - t).support.card ≤ m := by
        have h1 := Finset.card_le_card hsupp
        rw [Finset.card_erase_of_mem (Finsupp.mem_support_iff.mpr hg)] at h1
        omega
      have hdmem := ih (c - t) hdcard hdfix hdbr
      have hct : c = (c - t) + t := by abel
      rw [hct]
      exact add_mem hdmem (SetLike.le_def.mp
        (le_iSup _ (⟨Q, hQlt⟩ : {Q : Subgroup G // Q < P})) htmem)
  · -- Conversely every such trace is killed.
    intro hmem
    have hle : (⨆ Q : {Q : Subgroup G // Q < P}, GAlgebra.relTraceIdeal (Q : Subgroup G) P)
        ≤ (brauerProjHom (k := k) P).ker := by
      refine iSup_le fun Q => ?_
      rintro x ⟨a, -, rfl⟩
      exact AddMonoidHom.mem_ker.mpr
        (brauerProj_relTrace_eq_zero hchar (dvd_relIndex_of_lt_of_isPGroup hP Q.2) a)
    exact AddMonoidHom.mem_ker.mp (SetLike.le_def.mp hle hmem)

/-- **The Brauer quotient.**  Two `P`-fixed elements have the same image under `Br_P` exactly
when they differ by a sum of relative traces from proper subgroups of `P`.  Together with the
section `exists_forall_smul_eq_brauerProj_eq` this identifies

`(k[G])^P / ∑_{Q<P} Tr^P_Q ((k[G])^Q) ≅ k[C_G(P)]`,

the Brauer construction. -/
theorem brauerProj_eq_iff_sub_mem [Finite G] [Fact p.Prime] (hchar : (p : k) = 0)
    {P : Subgroup G} (hP : IsPGroup p ↥P) {x y : MonoidAlgebra k G}
    (hx : ∀ u ∈ P, u • x = x) (hy : ∀ u ∈ P, u • y = y) :
    brauerProj P x = brauerProj P y ↔
      x - y ∈ ⨆ Q : {Q : Subgroup G // Q < P}, GAlgebra.relTraceIdeal (Q : Subgroup G) P := by
  have hsub : ∀ u ∈ P, u • (x - y) = x - y := fun u hu => by
    rw [smul_sub, hx u hu, hy u hu]
  rw [← brauerProj_eq_zero_iff hchar hP hsub, sub_eq_add_neg, brauerProj_add,
    ← neg_one_smul k y, brauerProj_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero]

end Kernel

end OddOrder.GroupAlgebra
