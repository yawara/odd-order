/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7A2_NormalPThm75

/-!
# Isaacs FGT Ch.7 (Thompson subgroup) — S7B part 1: normal-J (Thm 7.6) Steps 1-6 (pp. 209-214)
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7B: normal-J theorem (pp. 209-214) -/


/-! ### Thm 7.6 — normal-J theorem ⭐⭐ (conditional on 8-step argument)

**Isaacs Thm 7.6** (mmd L3832):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) `O_{p'}(G) = 1`,
> (v) `P = C_G(Z(P))` ⇒ `J(P) ⊴ G`.

**= BG Theorem 6.2 の odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8,
§9, App.A で 7 ヶ所超で直接引用.

**proof 戦略** (8 Step, mmd L3832-3896): Thm 7.5 + Ch.6 **6.20** (abelian coprime
⟨C_N(a)⟩=N) + Ch.4 **4.35** (Ω₁ fixed) + Hall-Higman 3.21.

The full Goldschmidt-style 8-step proof requires Thm 7.5 (✅ landed) + Ch.6 6.20 +
Ch.4 4.35 (still pending).  Below we land the **conditional version** that takes
the minimum-counterexample contradiction as a forward-dependency hypothesis. -/

/-! ### Step 1 corollaries of Hall-Higman 3.21 (mmd L3837)

The first step of Isaacs Thm 7.6 proof observes that under hyp (iv)
`O_{p'}(G) = 1`, Hall-Higman 3.21 (with `π = {p}`) yields
`C_G(O_p(G)) ≤ O_p(G)`, and consequently `Z(P) ≤ O_p(G)` for any
Sylow `p`-subgroup `P`. -/

/-- The image of `Z(P)` in `G` centralizes `O_p(G)`.

Pure structural fact: since `O_p(G) ≤ P`, any element of `Z(P)` commutes with
every element of `O_p(G)`.  Hypothesis (iv) `O_{p'}(G) = 1` is **not** needed
here; it enters only at the next step (Hall-Higman 3.21). -/
private theorem center_sylow_le_centralizer_opCore
    {G : Type*} [Group G] {p : ℕ} (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  rintro _ ⟨⟨z, hzP⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh_P : h ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P hh
  have hc : (⟨h, hh_P⟩ : (P : Subgroup G)) * ⟨z, hzP⟩
      = ⟨z, hzP⟩ * ⟨h, hh_P⟩ :=
    Subgroup.mem_center_iff.mp hz_center ⟨h, hh_P⟩
  exact congr_arg Subtype.val hc

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): Hall-Higman 3.21 with `π = {p}`.

If `G` is `{p}`-separable (equivalently `p`-solvable) and `O_{p'}(G) = ⊥`,
then `C_G(O_p(G)) ≤ O_p(G)`. -/
theorem centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) :
    Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G := by
  have hπ' : OddOrder.Isaacs.Ch03.oPiCore {q | q ∉ ({p} : Set ℕ)} G = ⊥ := by
    rw [show ({q | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} by
      ext q; simp]
    exact hOp'
  have hHH :=
    OddOrder.Isaacs.Ch03.hall_higman_1_2_3 (G := G) ({p} : Set ℕ) hπ'
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p] at hHH
  exact hHH

/-- **Isaacs Thm 7.6 Step 1** (mmd L3837): `Z(P) ≤ O_p(G)` under `O_{p'}(G) = ⊥`.

Composition of `center_sylow_le_centralizer_opCore` (structural) and
`centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot` (Hall-Higman 3.21).
This is the core conclusion of Step 1 in the 8-step proof of Thm 7.6. -/
theorem center_sylow_le_opCore_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  (center_sylow_le_centralizer_opCore P).trans
    (centralizer_opCore_le_opCore_of_oPiCorePrime_eq_bot hOp')

/-- **Isaacs Thm 7.6 Step 1(c)** (mmd L3839): in the quotient
`G̅ := G / O_p(G)`, the centralizer of `L̅ := O_{p'}(G̅)` is contained in `L̅`.

Stated with the quotient taken at `oPiCore ({p} : Set ℕ) G` (the canonical
form recognized by `oPiCore_quotient_self_eq_bot`).  Use sites that work with
`opCore p G` should transport across `oPiCore_singleton_eq_opCore` via
`QuotientGroup.quotientMulEquivOfEq` before calling. -/
theorem step1_c_centralizer_oPiPrime_quotient_le_self
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G] :
    Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
            (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
          Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ≤
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
  -- (1) `{p}`-separability passes to the quotient (mathlib instance).
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := inferInstance
  -- (2) Take complement: `IsPiSeparable π G → IsPiSeparable {p | p ∉ π} G`.
  haveI : OddOrder.Isaacs.Ch03.IsPiSeparable ({q | q ≠ p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
    have hcompl := OddOrder.Isaacs.Ch03.isPiSeparable_compl
      ({p} : Set ℕ) (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) inferInstance
    have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
      ext q; simp
    rw [hπeq] at hcompl
    exact hcompl
  -- (3) Hall-Higman complement: `O_{{p}}(G̅) = ⊥` (self-quotient kills radical).
  have hπ'bot :
      OddOrder.Isaacs.Ch03.oPiCore
          ({q : ℕ | q ∉ ({q | q ≠ p} : Set ℕ)} : Set ℕ)
          (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by
    have hπ'eq : ({q : ℕ | q ∉ ({q | q ≠ p} : Set ℕ)} : Set ℕ) = ({p} : Set ℕ) := by
      ext q; simp
    rw [hπ'eq]
    exact OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot ({p} : Set ℕ)
  -- (4) Apply Hall-Higman 3.21 to `G̅` with `π = {q | q ≠ p}`.
  exact OddOrder.Isaacs.Ch03.hall_higman_1_2_3 ({q | q ≠ p} : Set ℕ) hπ'bot

/-! ### §7B Step 4 setup: the subgroup `L = O_{p',p}(G)`.

Following Isaacs L3835 the book sets `L̅ = O_{p'}(G̅)` (where `G̅ = G/U`,
`U = O_p(G)`) and defines `L` to be the unique preimage of `L̅` in `G`
containing `U`.  We work with the comap-along-`mk'` form. -/

/-- `L = O_{p',p}(G)` defined as the preimage of `L̅ = O_{p'}(G̅)` along
the quotient map `G →* G/(O_p(G))`.  This is the second term of the lower
`p`-radical series of `G` (with `O_p` first, `O_{p'}` second). -/
noncomputable def opPpPrimeCore (G : Type*) [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] : Subgroup G :=
  (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).comap
    (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))

/-- `L = O_{p',p}(G)` is `G`-normal (comap of normal subgroup is normal). -/
instance opPpPrimeCore_normal {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] : (opPpPrimeCore G p).Normal := by
  unfold opPpPrimeCore
  infer_instance

/-- `U = O_p(G) ≤ L = O_{p',p}(G)`: the kernel of the quotient map lies in the
preimage of any subgroup of the quotient. -/
theorem oPiCore_p_le_opPpPrimeCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G ≤ opPpPrimeCore G p := by
  unfold opPpPrimeCore
  intro x hx
  rw [Subgroup.mem_comap]
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
  exact (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
    (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)).one_mem

/-- `L.map (mk' U) = L̅`: the image of `L = O_{p',p}(G)` in `G̅ = G/U`
is exactly `L̅ = O_{p'}(G̅)`.  Follows from `map_comap_eq_self_of_surjective`. -/
theorem opPpPrimeCore_map_eq_LBar
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (opPpPrimeCore G p).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) =
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := by
  unfold opPpPrimeCore
  exact Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective _) _

/-- **Isaacs Thm 7.6 Step 5 prep** (mmd L3873): for any `p`-subgroup `A ≤ G`,
the image `Ā = A.map (mk' U)` is disjoint from `L̅ = O_{p'}(G̅)` in `G̅ = G/U`.

`Ā` is a `p`-group (image of `p`-group `A`), and `L̅` is a `{q | q ≠ p}`-group
by `oPiCore.isPiGroup`.  Their cardinalities are coprime, hence the
intersection is trivial. -/
theorem AbarInf_LBar_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) = ⊥ := by
  -- A̅ is a p-group, hence {p}-IsPiGroup.
  have hAbar_pg : IsPGroup p
      (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
    hA_pg.map _
  have hAbar_pi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup ({p} : Set ℕ)
      (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) := by
    intro q hq
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hq_dvd : q ∣ Nat.card
        (A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))) :=
      Nat.dvd_of_mem_primeFactors hq
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAbar_pg
    rw [hk] at hq_dvd
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq hq_prime Fact.out).mp
        (hq_prime.dvd_of_dvd_pow hq_dvd)
    simp [hq_eq_p]
  -- L̅ is a {q | q ≠ p}-group; rewrite as `{q | q ∉ {p}}` for the coprime lemma.
  have hLbar_pi' : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup
      ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ)
      (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
        (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) := by
    have hLbar_pi := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup
      (G := G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) ({q | q ≠ p} : Set ℕ)
    have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
      ext q; simp
    rw [hπeq]; exact hLbar_pi
  -- Apply `inf_eq_bot_of_coprime` + `coprime_of_isPiGroup_of_isPiGroup_compl`.
  apply Subgroup.inf_eq_bot_of_coprime
  exact OddOrder.Isaacs.Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
    Nat.card_pos.ne' Nat.card_pos.ne' hAbar_pi hLbar_pi'

/-- **Step 5 conclusion synthesizer** (mmd L3874): a nontrivial, finite,
elementary abelian, cyclic `p`-group has order exactly `p`.  Generic. -/
theorem card_eq_prime_of_isElementaryAbelian_isCyclic_nontrivial
    {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hH_el : OddOrder.GroupTheory.IsElementaryAbelian p H) (hH_cyc : IsCyclic H) :
    Nat.card H = p := by
  -- Get generator; |H| = orderOf g for cyclic.
  obtain ⟨g, hg⟩ := hH_cyc.exists_generator
  have hzgen : Subgroup.zpowers g = ⊤ := by
    ext x
    exact ⟨fun _ => Subgroup.mem_top _, fun _ => hg x⟩
  have hcard : Nat.card H = orderOf g := by
    have hcard_zpow : Nat.card (Subgroup.zpowers g) = Nat.card H := by
      rw [hzgen]
      exact Nat.card_congr Subgroup.topEquiv.toEquiv
    rw [← hcard_zpow, Nat.card_zpowers]
  -- g^p = 1 ⇒ orderOf g ∣ p.
  have hpow : g ^ p = 1 := hH_el.pow_eq_one g
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hpow
  -- p prime + orderOf g ∣ p ⇒ orderOf g = 1 or p.
  rcases (Nat.dvd_prime Fact.out).mp hdvd with h1 | hp'
  · -- orderOf g = 1 ⇒ g = 1 ⇒ zpowers g = ⊥; but zpowers g = ⊤ (hzgen), contradict.
    exfalso
    have hg_eq : g = 1 := orderOf_eq_one_iff.mp h1
    have hbot : Subgroup.zpowers g = ⊥ := by
      rw [hg_eq, Subgroup.zpowers_one_eq_bot]
    have hcontra : (⊤ : Subgroup H) = ⊥ := hzgen.symm.trans hbot
    exact absurd hcontra top_ne_bot
  · rw [hcard, hp']

/-- `A ≤ P` propagates to images: `Ā ≤ P̄`.  Pure monotonicity of `Subgroup.map`. -/
theorem map_le_map_of_le
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {P A : Subgroup G} (hA_le_P : A ≤ P) :
    A.map (QuotientGroup.mk' N) ≤ P.map (QuotientGroup.mk' N) :=
  Subgroup.map_mono hA_le_P

/-- **Step 2 entry / Step 7 closure**: `J(P) ≤ X` iff every elementary abelian
maximal `E ∈ E(P)` is contained in `X`.  Pure unfold of the iSup definition. -/
theorem thompsonJ_le_iff
    {G : Type*} [Group G] (P X : Subgroup G) (p : ℕ) :
    Subgroup.thompsonJ P p ≤ X ↔
      ∀ E ∈ Subgroup.maxElemAbelianIn P p, E ≤ X := by
  unfold Subgroup.thompsonJ
  exact iSup₂_le_iff

/-- Contrapositive of `thompsonJ_le_iff`: if `J(P) ⊄ X` then some maximal
elementary abelian member is not contained in `X`.  This is the Step 2
entry of the Thm 7.6 counterexample-minimum argument: assuming `G` is a
counterexample, `J(P) ⊄ U`, hence we can pick `A ∈ E(P)` with `A ⊄ U`. -/
theorem exists_maxElemAbelianIn_not_le_of_thompsonJ_not_le
    {G : Type*} [Group G] (P X : Subgroup G) (p : ℕ)
    (h : ¬ Subgroup.thompsonJ P p ≤ X) :
    ∃ E ∈ Subgroup.maxElemAbelianIn P p, ¬ E ≤ X := by
  by_contra h_all
  push Not at h_all
  exact h ((thompsonJ_le_iff P X p).mpr h_all)

/-- The image of an elementary abelian subgroup under a group hom is
elementary abelian.  Generic for `Subgroup.IsElementaryAbelian`. -/
theorem isElementaryAbelian_map_of_isElementaryAbelian
    {G H : Type*} [Group G] [Group H] {p : ℕ} (f : G →* H)
    {A : Subgroup G} (hA : A.IsElementaryAbelian p) :
    (A.map f).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨_, a₁, ha₁, rfl⟩ ⟨_, a₂, ha₂, rfl⟩
    apply Subtype.ext
    show f a₁ * f a₂ = f a₂ * f a₁
    rw [← f.map_mul, ← f.map_mul]
    have hcomm : (⟨a₁, ha₁⟩ : A) * ⟨a₂, ha₂⟩ = ⟨a₂, ha₂⟩ * ⟨a₁, ha₁⟩ :=
      hA.1 ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
    exact congr_arg f (congr_arg Subtype.val hcomm)
  · rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    show (f a) ^ p = 1
    rw [← f.map_pow, ← f.map_one]
    have hpow : (⟨a, ha⟩ : A) ^ p = 1 := hA.2 ⟨a, ha⟩
    exact congr_arg f (congr_arg Subtype.val hpow)

/-- **Isaacs Thm 7.6 Step 5 nontriviality** (mmd L3874): if `A ⊄ U`
(= `oPiCore {p} G`), then the image `Ā = A.map (mk' U)` is nontrivial.

Contrapositive: `Ā = ⊥ ⇒ A ≤ ker mk' = U`. -/
theorem Abar_ne_bot_of_not_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G}
    (hA_not_le : ¬ A ≤ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ≠ ⊥ := by
  intro h_eq
  apply hA_not_le
  intro x hx
  have hmem :
      (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) x ∈
        A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) :=
    ⟨x, hx, rfl⟩
  rw [h_eq, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff x).mp hmem

/-- **Isaacs Thm 7.6 Step 5 faithfulness** (mmd L3874): for any `p`-subgroup
`A ≤ G`, the image `Ā = A.map (mk' U)` acts faithfully on `L̅ = O_{p'}(G̅)`,
i.e., `Ā ⊓ C_{G̅}(L̅) = ⊥`.

Combines Step 1(c) (`C_{G̅}(L̅) ⊆ L̅`) with `Ā ⊓ L̅ = ⊥`. -/
theorem AbarInf_centralizer_LBar_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    {A : Subgroup G} (hA_pg : IsPGroup p A) :
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
      Subgroup.centralizer
        (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
            (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
          Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [eq_bot_iff]
  calc
    A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
        Subgroup.centralizer
          (OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
              (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :
            Set (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G))
        ≤ A.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) ⊓
            OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p}
              (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) :=
      inf_le_inf_left _ step1_c_centralizer_oPiPrime_quotient_le_self
    _ = ⊥ := AbarInf_LBar_eq_bot hA_pg

/-! ### Step 2-3: structural bridges for `A ∈ E(P)`, `A ⊄ L` (mmd L3845-3858)

We pick `A ∈ maxElemAbelianIn P p` with `A ⊄ L = O_p(G)`.  These bridges express
the basic structural relations between `A`, `D := A ⊓ L`, and the global subgroups
of `G` needed in subsequent steps.

The book takes `A ∈ E(P)` failing to lie in `L` for the contradiction in Step 7.
We package the elementary observations: `A` is an elementary abelian `p`-subgroup
of `P`, hence contained in `P`; and `D = A ⊓ L` is a proper subgroup of `A` (with
nontrivial quotient `A/D`). -/

/-- **Isaacs Thm 7.6 Step 2** preparation (mmd L3845-3846):
`A ∈ maxElemAbelianIn P p` is an elementary abelian `p`-subgroup of `P`.

Pure unpacking of the `maxElemAbelianIn` definition (see
`OddOrder.GroupTheory.ThompsonSubgroup.maxElemAbelianIn`).  Placed here as a
shorthand for §7B Steps 3-7 which reuse the elementary-abelian / `≤ P` facts. -/
private theorem maxElemAbelianIn_isElementaryAbelian {G : Type*} [Group G]
    {P A : Subgroup G} {p : ℕ}
    (hA : A ∈ Subgroup.maxElemAbelianIn P p) :
    A.IsElementaryAbelian p :=
  hA.2.1

private theorem maxElemAbelianIn_le_parent {G : Type*} [Group G]
    {P A : Subgroup G} {p : ℕ}
    (hA : A ∈ Subgroup.maxElemAbelianIn P p) :
    A ≤ P :=
  hA.1

/-- **Isaacs Thm 7.6 Step 3** (mmd L3850-3856): the quotient `A / (A ⊓ L)` has order `p`.

Book argument: `A` is elementary abelian (`x^p = 1` for all `x ∈ A`), so `A/D`
embeds into `G/L`.  Under hypothesis (iv) `O_{p'}(G) = 1` we have `L = O_p(G)`,
hence `G/L` has trivial `p`-Sylow (Hall-Higman 3.21 / Isaacs Cor 3.21).

For the bridge layer we record the **abstract version**: if `D ≤ A`, `D ≠ A`, and
`A.IsElementaryAbelian p`, then `D` has index dividing `p` in `A`.  In an
elementary abelian `p`-group every proper subgroup has prime power index.  The
stronger conclusion "index exactly `p`" needs the **maximality of `A`** —
otherwise we could enlarge `D` to a strict sub of `A` of index `p`, contradicting
that `A ∈ E(P)`.

We package the elementary-abelian quotient observation: in `A/D` the exponent
divides `p` so `|A/D|` is a power of `p`. -/
private theorem relIndex_isPGroup_of_isElementaryAbelian
    {G : Type*} [Group G] {A D : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hA_el : A.IsElementaryAbelian p) :
    IsPGroup p (D.subgroupOf A) := by
  -- A is elementary abelian ⇒ A is a p-group ⇒ subgroup of A is a p-group.
  have hA_pG : IsPGroup p A := hA_el.isPGroup
  exact hA_pG.to_subgroup _

/-- **Isaacs Thm 7.6 Step 3** companion: the order of `A` is a power of `p`.

Since `A.IsElementaryAbelian p`, `A` is itself a `p`-group, so `Nat.card A = p^k`
for some `k`. -/
private theorem isPGroup_of_isElementaryAbelian
    {G : Type*} [Group G] {A : Subgroup G} {p : ℕ}
    (hA_el : A.IsElementaryAbelian p) :
    IsPGroup p A :=
  hA_el.isPGroup

/-! ### Step 4: action of `A` on `V := Z(L) = Z(O_p(G))` (mmd L3858-3864)

Set `V := Z(L)`.  Since `L = O_p(G)` is `G`-normal, the conjugation action of `G`
on `L` restricts to an action on `Z(L)`, and in particular `A ≤ P ≤ G` acts on `V`.
Furthermore `D = A ⊓ L ≤ L` commutes with all of `V = Z(L)` by definition of
center, so `D` is contained in the kernel of the action of `A` on `V`. -/

/-- **Isaacs Thm 7.6 Step 4** (mmd L3858): `Z(O_p(G))` is `G`-normal (and `G`-characteristic).

The `Subgroup.center` of a characteristic subgroup is itself characteristic in the
ambient group.  In particular `Subgroup.center` of `O_p(G)`, viewed as the image
of `Subgroup.center (opCore p G)` in `G`, is `G`-normal. -/
private theorem center_opCore_map_normal {G : Type*} [Group G] {p : ℕ} :
    ((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨⟨z, hz_L⟩, hz_center, rfl⟩ g
  -- g * z * g⁻¹ ∈ opCore p G  (since opCore is normal)
  have hLnorm : (OddOrder.Isaacs.Ch01.opCore p G).Normal := inferInstance
  have hgz : g * z * g⁻¹ ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    hLnorm.conj_mem z hz_L g
  refine ⟨⟨g * z * g⁻¹, hgz⟩, ?_, rfl⟩
  -- Show ⟨g*z*g⁻¹, _⟩ ∈ Subgroup.center (opCore p G).
  change (⟨g * z * g⁻¹, hgz⟩ : OddOrder.Isaacs.Ch01.opCore p G) ∈
    Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  rintro ⟨h, hh_L⟩
  -- ⟨h, hh_L⟩ * ⟨g*z*g⁻¹, hgz⟩ = ⟨g*z*g⁻¹, hgz⟩ * ⟨h, hh_L⟩,
  -- i.e., h * (g*z*g⁻¹) = (g*z*g⁻¹) * h.
  have hgh : g⁻¹ * h * g ∈ OddOrder.Isaacs.Ch01.opCore p G := by
    have := hLnorm.conj_mem h hh_L g⁻¹
    simpa [mul_assoc] using this
  have hcomm : (⟨g⁻¹ * h * g, hgh⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨z, hz_L⟩
      = ⟨z, hz_L⟩ * ⟨g⁻¹ * h * g, hgh⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  have hcomm_G : (g⁻¹ * h * g) * z = z * (g⁻¹ * h * g) := congr_arg Subtype.val hcomm
  apply Subtype.ext
  calc h * (g * z * g⁻¹)
      = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hcomm_G]
    _ = (g * z * g⁻¹) * h := by group

/-- **Isaacs Thm 7.6 Step 4** (mmd L3859-3860):
`D := A ⊓ L` centralizes `V := Z(L)`.

For any `d ∈ D`, `d ∈ L`.  For any `v` representing an element of `Z(L) ↪ G`,
the conjugation `d * v * d⁻¹` equals `v` because `v ∈ Z(L)`.  This packages the
"the `A`-action restricted to `D` is trivial" observation: `D ≤ centralizer V`. -/
private theorem A_inter_opCore_le_centralizer_center_opCore
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} :
    A ⊓ OddOrder.Isaacs.Ch01.opCore p G ≤
      Subgroup.centralizer
        (((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
          (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype) : Set G) := by
  intro d hd
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨⟨v, hv_L⟩, hv_center, rfl⟩
  -- d ∈ L, ⟨v, _⟩ ∈ Z(L) ⇒ they commute in L ⇒ commute in G.
  have hd_L : d ∈ OddOrder.Isaacs.Ch01.opCore p G := hd.2
  -- mem_centralizer_iff: ∀ h ∈ s, h * g = g * h, so v * d = d * v.
  -- mem_center_iff gives ∀ g, g * z = z * g, so ⟨d, _⟩ * ⟨v, _⟩ = ⟨v, _⟩ * ⟨d, _⟩.
  have hcomm : (⟨d, hd_L⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨v, hv_L⟩
      = ⟨v, hv_L⟩ * ⟨d, hd_L⟩ :=
    Subgroup.mem_center_iff.mp hv_center _
  exact (congr_arg Subtype.val hcomm).symm

/-! ### Step 5-6: action triviality on `V := Z(O_p(G))` (mmd L3864-3884)

The book applies Ch.6 Thm 6.20 + Ch.4 Cor 4.35 to deduce that the action of
`A/D ≅ ℤ/p` on `V = Z(L)` is trivial.  At the bridge layer we record:

* `V` is a finite abelian `p`-group (Ch.4 Cor 4.35 hypothesis).
* `Z(L)` is the centralizer of `L` inside `L`, which contains the image of
  `Z(P)` (by Step 1's `center_sylow_le_opCore_of_oPiCorePrime_eq_bot` and the
  fact that `Z(P)` ≤ centralizer (Z(P)) ≤ centralizer L ⊓ L = Z(L)`...).

The combined deduction "A trivial on `Ω₁ Z(L)` ⇒ A trivial on `Z(L)`" requires
both Thm 6.20 (factoring through cyclic quotients) and Cor 4.35 (Ω₁ argument).
We supply pieces; the full Step 5-6 deduction is deferred to a later session. -/

/-- **Isaacs Thm 7.6 Step 5** (mmd L3864): `Z(O_p(G))` is a `p`-group.

Direct: `O_p(G)` is itself a `p`-group (`opCore_isPGroup`), and the center of a
`p`-group is a `p`-group (`IsPGroup.to_subgroup`). -/
private theorem center_opCore_isPGroup {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).to_subgroup _

/-- **Isaacs Thm 7.6 Step 5** (mmd L3864): the image of `Z(O_p(G))` in `G` is also a
`p`-group.

Push-forward of `center_opCore_isPGroup` under the inclusion `opCore p G ↪ G`. -/
private theorem center_opCore_map_isPGroup
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p
      ((Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
        (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype) :=
  (center_opCore_isPGroup p).map _

/-- **Isaacs Thm 7.6 Step 5** (mmd L3864): `Z(O_p(G))` is commutative as a group.

Since `Z(O_p(G)) ≤ Z(O_p(G))` (tautologically) and the center is commutative,
`Z(O_p(G))` carries a `CommGroup` structure.  We expose only the underlying
`∀ x y, x * y = y * x` (lemma form), which avoids declaring a `CommGroup`
instance that could collide. -/
private theorem center_opCore_comm
    {G : Type*} [Group G] (p : ℕ) :
    ∀ x y : Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G),
      x * y = y * x := by
  intro x y
  -- Both x, y belong to Subgroup.center; use mem_center_iff to commute.
  have hx : (x : OddOrder.Isaacs.Ch01.opCore p G) ∈
      Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) := x.2
  have hcomm := Subgroup.mem_center_iff.mp hx (y : OddOrder.Isaacs.Ch01.opCore p G)
  -- hcomm : (y : _) * (x : _) = (x : _) * (y : _).  Want x * y = y * x in Z(L).
  apply Subtype.ext
  exact hcomm.symm

/-! ### Step 7 preparation: `V := Ω₁(Z(O_p(G)))` as a subgroup of `G` (sub-session A)

For the Step 5-6 application of Cor 4.35 we need
`V := Ω₁(Z(O_p(G)))`, i.e., `{z ∈ Z(O_p(G)) | z^p = 1}`.  Since `Z(O_p(G))`
is abelian (it is a center), this set forms a subgroup of `G` directly,
without taking a closure.  We package it as `omega1ZCenterOpCore` together
with its key properties: normal in `G`, contained in `O_p(G)`, abelian as
a group, and a `p`-group.

These are the structural ingredients for **Isaacs Thm 7.6 Step 7 sub-session
(A)**.  The downstream application combines `V` with Cor 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`) to derive
`[A, V] = ⊥` from the fixed-point hypothesis. -/

/-- Local notation shorthand inside §7B: the underlying subgroup of `Z(O_p(G))`
viewed inside `G` (i.e., the image of `Subgroup.center (opCore p G)` under
the inclusion `opCore p G ↪ G`). -/
def zCenterOpCoreSubgroup (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  (Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G)).map
    (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G).subtype

private theorem zCenterOpCoreSubgroup_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    zCenterOpCoreSubgroup G p ≤ OddOrder.Isaacs.Ch01.opCore p G := by
  rintro _ ⟨⟨z, hz_L⟩, _, rfl⟩
  exact hz_L

private theorem zCenterOpCoreSubgroup_comm
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x ∈ zCenterOpCoreSubgroup G p,
      ∀ y ∈ zCenterOpCoreSubgroup G p, x * y = y * x := by
  rintro _ ⟨⟨x, hx_L⟩, hx_center, rfl⟩ _ ⟨⟨y, hy_L⟩, hy_center, rfl⟩
  -- ⟨x, _⟩ ∈ Z(L) so commutes with ⟨y, _⟩ in L; project to G.
  -- mem_center_iff: x ∈ center ↔ ∀ g, g * x = x * g.
  have hcomm :
      (⟨y, hy_L⟩ : OddOrder.Isaacs.Ch01.opCore p G) * ⟨x, hx_L⟩ =
        ⟨x, hx_L⟩ * ⟨y, hy_L⟩ :=
    Subgroup.mem_center_iff.mp hx_center _
  exact (congr_arg Subtype.val hcomm).symm

/-- **V := Ω₁(Z(O_p(G)))** as a subgroup of `G`.

The set `{g ∈ Z(O_p(G)) | g^p = 1}`, viewed inside `G`.  Since `Z(O_p(G))`
is abelian, this is a subgroup of `G` directly (no closure required).

This is the `V` of **Isaacs Thm 7.6 Step 7 sub-session (A)**: the bottom
layer `Ω₁` of the center of the `p`-core, on which the action of
`A ∈ E(P)` will be analyzed via Cor 4.35. -/
def omega1ZCenterOpCore (G : Type*) [Group G] (p : ℕ) : Subgroup G :=
  OddOrder.GroupTheory.omega1OfAbelian G (zCenterOpCoreSubgroup G p) p
    zCenterOpCoreSubgroup_comm

/-- Membership characterization for `V := Ω₁(Z(O_p(G)))`. -/
theorem mem_omega1ZCenterOpCore {G : Type*} [Group G] {p : ℕ} {g : G} :
    g ∈ omega1ZCenterOpCore G p ↔
      g ∈ zCenterOpCoreSubgroup G p ∧ g ^ p = 1 := by
  unfold omega1ZCenterOpCore
  exact OddOrder.GroupTheory.mem_omega1OfAbelian

/-- `V ≤ Z(O_p(G))` (the bottom layer is contained in the center it sits in). -/
theorem omega1ZCenterOpCore_le_zCenterOpCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ zCenterOpCoreSubgroup G p :=
  OddOrder.GroupTheory.omega1OfAbelian_le

/-- `V ≤ O_p(G)`: immediate via the chain `V ≤ Z(O_p(G)) ≤ O_p(G)`. -/
theorem omega1ZCenterOpCore_le_opCore
    {G : Type*} [Group G] {p : ℕ} :
    omega1ZCenterOpCore G p ≤ OddOrder.Isaacs.Ch01.opCore p G :=
  omega1ZCenterOpCore_le_zCenterOpCore.trans zCenterOpCoreSubgroup_le_opCore

/-- **Isaacs Thm 7.6 Step 7 sub-session (A)**: `V := Ω₁(Z(O_p(G)))` is normal in `G`.

Proof: `Z(O_p(G))` (as `zCenterOpCoreSubgroup`) is normal in `G` (already in
`center_opCore_map_normal`).  Conjugation by `g ∈ G` preserves the power map
`x ↦ x^p`, so it sends `{z ∈ Z(O_p(G)) | z^p = 1}` to itself. -/
instance omega1ZCenterOpCore_normal {G : Type*} [Group G] {p : ℕ} :
    (omega1ZCenterOpCore G p).Normal := by
  refine ⟨?_⟩
  intro n hn g
  rw [mem_omega1ZCenterOpCore] at hn ⊢
  refine ⟨?_, ?_⟩
  · -- Z(O_p(G)) is normal (center_opCore_map_normal).
    have h_norm : (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal
    exact h_norm.conj_mem _ hn.1 g
  · -- (g * n * g⁻¹) ^ p = g * n^p * g⁻¹ = g * 1 * g⁻¹ = 1.
    calc (g * n * g⁻¹) ^ p
        = g * n ^ p * g⁻¹ := by rw [conj_pow]
      _ = g * 1 * g⁻¹ := by rw [hn.2]
      _ = 1 := by group

/-- `V := Ω₁(Z(O_p(G)))` is a `p`-group.

Direct consequence of `V ≤ O_p(G)` and `O_p(G)` being a `p`-group. -/
theorem omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (omega1ZCenterOpCore G p) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).of_injective
    (Subgroup.inclusion omega1ZCenterOpCore_le_opCore)
    (Subgroup.inclusion_injective _)

/-- The elements of `V := Ω₁(Z(O_p(G)))` commute pairwise (V is abelian).

Inherited from the fact that they sit in `Z(O_p(G))`. -/
theorem omega1ZCenterOpCore_comm {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(omega1ZCenterOpCore G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  have hx : (x : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore x.2
  have hy : (y : G) ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore y.2
  exact zCenterOpCoreSubgroup_comm _ hx _ hy

/-- `V := Ω₁(Z(O_p(G)))` as a `CommGroup`.

The pairwise-commutativity from `omega1ZCenterOpCore_comm` upgrades the
ambient `Group ↥V` structure to `CommGroup`. -/
@[reducible] def omega1ZCenterOpCore_commGroup (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(omega1ZCenterOpCore G p) :=
  { (inferInstance : Group ↥(omega1ZCenterOpCore G p)) with
    mul_comm := omega1ZCenterOpCore_comm }

/-- Every element of `V := Ω₁(Z(O_p(G)))` has order dividing `p`.

Pure unpacking of `mem_omega1ZCenterOpCore.2`. -/
theorem pow_p_eq_one_of_mem_omega1ZCenterOpCore
    {G : Type*} [Group G] {p : ℕ} {g : G}
    (hg : g ∈ omega1ZCenterOpCore G p) : g ^ p = 1 :=
  ((mem_omega1ZCenterOpCore).mp hg).2

/-! ### Step 7 sub-session (A): Cor 4.35 wrapper for `V := Ω₁(Z(O_p(G)))`

We specialize **Isaacs Cor 4.35**
(`OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
to `V := Ω₁(Z(O_p(G)))`: any `p'`-group `A` acting on `V` that fixes every
element of order `p` (= every element of `V`!) has `actionCommutator φ = ⊥`.

The wrapper packages the `CommGroup`, `IsPGroup p`, `Finite` instances on `V`
so callers only need to supply the action `φ : A →* MulAut ↥V` and the
hypotheses `¬ p ∣ |A|` and the fixed-point property. -/

/-- **Isaacs Thm 7.6 Step 7 sub-session (A)**: Cor 4.35 specialized to
`V := Ω₁(Z(O_p(G)))`.

Given a finite group `A` with `p ∤ |A|` acting on `V` via `φ : A →* MulAut ↥V`,
if every element of order `p` (equivalently every element of `V`, since
`V = Ω₁(...)`) is fixed by every `a ∈ A`, then `actionCommutator φ = ⊥`.

Reduces to Cor 4.35
(`OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`)
once the abelian + `p`-group instances on `V` are produced. -/
theorem cor_4_35_for_omega1ZCenterOpCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] [Finite A]
    (φ : A →* MulAut ↥(omega1ZCenterOpCore G p))
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ v : ↥(omega1ZCenterOpCore G p), v ^ p = 1 →
      ∀ a : A, (φ a) v = v) :
    OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
  let _ : CommGroup ↥(omega1ZCenterOpCore G p) :=
    omega1ZCenterOpCore_commGroup G p
  OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    (p := p) φ (omega1ZCenterOpCore_isPGroup p) hA_p' h_fix

/-- `Z(U) = Z(O_p(G))` is `G`-normal: it is the image of the center
of the (`G`-normal) `O_p(G)`, transported up via `center_opCore_map_normal`. -/
instance zCenterOpCoreSubgroup_normal
    {G : Type*} [Group G] {p : ℕ} :
    (zCenterOpCoreSubgroup G p).Normal := center_opCore_map_normal

/-- The conjugation action of an arbitrary subgroup `Q ≤ G` on `Z(U) = Z(O_p(G))`:
`Q →* MulAut Z(U)` via `MulAut.conjNormal ∘ Q.subtype`.

Used in Step 6: `Q` (a Sylow `q`-subgroup of `K = C_G(V)`, `q ≠ p`) acts on
`Z(U)` by conjugation; combined with `Q` fixing `V = Ω₁ Z(U)` (from `Q ⊆ K`),
Cor 4.35 yields `Q` acts trivially on `Z(U)`. -/
noncomputable def conjActionOnZCenterOpCoreSubgroup
    {G : Type*} [Group G] {p : ℕ} (Q : Subgroup G) :
    Q →* MulAut ↥(zCenterOpCoreSubgroup G p) :=
  MulAut.conjNormal.comp Q.subtype


/-- `Z(U) = Z(O_p(G))` is a `p`-group: it is a subgroup of `U = O_p(G)`,
which is a `p`-group. -/
theorem zCenterOpCoreSubgroup_isPGroup
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    IsPGroup p (zCenterOpCoreSubgroup G p) :=
  (OddOrder.Isaacs.Ch01.opCore_isPGroup p G).to_le zCenterOpCoreSubgroup_le_opCore

/-- Pairwise commutativity on the subtype ↥(Z(U)). -/
theorem zCenterOpCoreSubgroup_comm_subtype
    {G : Type*} [Group G] {p : ℕ} :
    ∀ x y : ↥(zCenterOpCoreSubgroup G p), x * y = y * x := by
  intro x y
  apply Subtype.ext
  exact zCenterOpCoreSubgroup_comm _ x.2 _ y.2

/-- `Z(U)` as a `CommGroup`. -/
@[reducible] def zCenterOpCoreSubgroup_commGroup
    (G : Type*) [Group G] (p : ℕ) :
    CommGroup ↥(zCenterOpCoreSubgroup G p) :=
  { (inferInstance : Group ↥(zCenterOpCoreSubgroup G p)) with
    mul_comm := zCenterOpCoreSubgroup_comm_subtype }

/-- Centralizer-conjugation lemma: `q ∈ centralizer s` ⇒ `q * z * q⁻¹ = z`
for every `z ∈ s`.  Generic. -/
theorem conj_eq_self_of_mem_centralizer
    {G : Type*} [Group G] {s : Set G}
    {q : G} (hq : q ∈ Subgroup.centralizer s) {z : G} (hz : z ∈ s) :
    q * z * q⁻¹ = z := by
  have hcomm : z * q = q * z := Subgroup.mem_centralizer_iff.mp hq z hz
  calc q * z * q⁻¹ = z * q * q⁻¹ := by rw [hcomm]
    _ = z := by group

/-- **Isaacs Cor 4.35 specialized for Z(U) = Z(O_p(G))**.

Given a `p'`-group `A` acting on `Z(U)` and fixing every element of order
`p` (= elements of `V = Ω₁ Z(U)`), `actionCommutator φ = ⊥`. -/
theorem cor_4_35_for_zCenterOpCoreSubgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Type*} [Group A] [Finite A]
    (φ : A →* MulAut ↥(zCenterOpCoreSubgroup G p))
    (hA_p' : ¬ p ∣ Nat.card A)
    (h_fix : ∀ v : ↥(zCenterOpCoreSubgroup G p), v ^ p = 1 →
      ∀ a : A, (φ a) v = v) :
    OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
  let _ : CommGroup ↥(zCenterOpCoreSubgroup G p) :=
    zCenterOpCoreSubgroup_commGroup G p
  OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p
    (p := p) φ (zCenterOpCoreSubgroup_isPGroup p) hA_p' h_fix

/-- Generic: a subgroup-level `IsElementaryAbelian p H` upgrades the ambient
`Group ↥H` to a `CommGroup ↥H` using the commutativity component.  Local
construction used when applying CommGroup-requiring lemmas (e.g., index
calculations) on elementary abelian subgroups. -/
@[reducible] def isElementaryAbelian_commGroup
    {G : Type*} [Group G] {p : ℕ} {H : Subgroup G} (hH : H.IsElementaryAbelian p) :
    CommGroup ↥H :=
  { (inferInstance : Group ↥H) with mul_comm := hH.1 }

/-- `O_p(G) ⊓ O_{p'}(G) = ⊥`: the `p`-core and the `p'`-core of `G` are
disjoint, by coprime cardinalities.  Specialization of `oPiCore.coprime_inf`. -/
theorem opCore_inf_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    OddOrder.Isaacs.Ch01.opCore p G ⊓
      OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥ := by
  have h1 : OddOrder.Isaacs.Ch01.opCore p G =
      OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G :=
    (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm
  have hπeq : ({q : ℕ | q ∉ ({p} : Set ℕ)} : Set ℕ) = {q | q ≠ p} := by
    ext q; simp
  rw [h1, ← hπeq]
  exact OddOrder.Isaacs.Ch03.oPiCore.coprime_inf ({p} : Set ℕ)

/-- If `Q ⊆ K = C_G(V)`, conjugation by elements of `Q` fixes every element
of `V = Ω₁ Z(U)` pointwise in `G`. -/
theorem conj_fixes_omega1ZCenterOpCore_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (q : ↥Q) {v : G} (hv : v ∈ omega1ZCenterOpCore G p) :
    (q : G) * v * (q : G)⁻¹ = v :=
  conj_eq_self_of_mem_centralizer (hQ_le_K q.2) hv

/-- `V ⊆ centralizer U` in `G`: since `V ⊆ Z(U)`, every element of `V`
commutes with every element of `U`.  Used in Step 7 to argue `V * D`
is abelian (`V ⊆ centralizer U ⊇ D`). -/
theorem omega1ZCenterOpCore_centralizes_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (OddOrder.Isaacs.Ch01.opCore p G : Set G) := by
  intro x hx
  have hx_ZU : x ∈ zCenterOpCoreSubgroup G p :=
    omega1ZCenterOpCore_le_zCenterOpCore hx
  rcases hx_ZU with ⟨⟨z, hz_U⟩, hz_center, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hcomm : (⟨u, hu⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) * ⟨z, hz_U⟩ =
      ⟨z, hz_U⟩ * ⟨u, hu⟩ :=
    Subgroup.mem_center_iff.mp hz_center _
  exact congr_arg Subtype.val hcomm

/-- `U.map (mk' U) = ⊥`: the image of `U = O_p(G)` in `G̅ = G/U` is trivial. -/
theorem opCore_map_mk_oPiCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (OddOrder.Isaacs.Ch01.opCore p G).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [show OddOrder.Isaacs.Ch01.opCore p G =
        OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G from
      (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm]

/-- Intersection with any subgroup preserves `IsElementaryAbelian`: if `A` is
elementary abelian then `A ⊓ B` is elementary abelian.  Used in Step 7 to
get `D = A ⊓ U`, `E = A ⊓ V` elementary abelian. -/
theorem inf_isElementaryAbelian_of_isElementaryAbelian
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} (hA : A.IsElementaryAbelian p)
    (B : Subgroup G) :
    (A ⊓ B).IsElementaryAbelian p := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hxA, _hxB⟩ ⟨y, hyA, _hyB⟩
    apply Subtype.ext
    -- Goal in G: x * y = y * x
    have hcomm_A : (⟨x, hxA⟩ : ↥A) * ⟨y, hyA⟩ = ⟨y, hyA⟩ * ⟨x, hxA⟩ := hA.1 _ _
    exact (congr_arg (Subtype.val (p := fun x => x ∈ A)) hcomm_A : (x * y : G) = y * x)
  · rintro ⟨x, hxA, _hxB⟩
    apply Subtype.ext
    -- Goal in G: x^p = 1
    have hpow_A : (⟨x, hxA⟩ : ↥A) ^ p = 1 := hA.2 _
    exact (congr_arg (Subtype.val (p := fun x => x ∈ A)) hpow_A : (x ^ p : G) = 1)

/-- **V is elementary abelian**: every element has order dividing `p`,
and the group is commutative (it lies inside the center `Z(O_p(G))`).
Used in Step 7 (`VD` elementary abelian counting argument). -/
theorem omega1ZCenterOpCore_isElementaryAbelian
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (omega1ZCenterOpCore G p).IsElementaryAbelian p := by
  refine ⟨omega1ZCenterOpCore_comm, ?_⟩
  intro x
  apply Subtype.ext
  show ((x : G) ^ p) = 1
  exact pow_p_eq_one_of_mem_omega1ZCenterOpCore x.2

/-- **Isaacs Thm 7.6 Step 6 prep** (mmd L3881): `Z(P) ⊆ Z(U)` (in the image
form): under hypothesis (iv), `Z(P)` lies inside `Z(O_p(G)) = Z(U)`.

`Z(P) ⊆ U` by Step 1(a) (`center_sylow_le_opCore_of_oPiCorePrime_eq_bot`),
and any `z ∈ Z(P)` commutes with every `u ∈ U ⊆ P`. -/
theorem center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G) :
    (Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      zCenterOpCoreSubgroup G p := by
  rintro _ ⟨⟨z', hz'_P⟩, hz'_center, rfl⟩
  -- z' ∈ U by Step 1(a).
  have hz_in_U : (z' : G) ∈ OddOrder.Isaacs.Ch01.opCore p G :=
    center_sylow_le_opCore_of_oPiCorePrime_eq_bot hOp' P
      ⟨⟨z', hz'_P⟩, hz'_center, rfl⟩
  -- ⟨z', hz_in_U⟩ ∈ Z(U) because z' commutes with each u ∈ U ⊆ P.
  refine ⟨⟨(z' : G), hz_in_U⟩, ?_, rfl⟩
  show (⟨(z' : G), hz_in_U⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) ∈
      Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  show ((u : G) * (z' : G)) = ((z' : G) * (u : G))
  have hu_P : (u : G) ∈ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P u.2
  have hcomm : (⟨(u : G), hu_P⟩ : (P : Subgroup G)) * ⟨z', hz'_P⟩
      = ⟨z', hz'_P⟩ * ⟨(u : G), hu_P⟩ :=
    Subgroup.mem_center_iff.mp hz'_center _
  exact congr_arg Subtype.val hcomm

/-- `V ⊆ K = C_G(V)`: abelian subgroup is contained in its own centralizer. -/
theorem omega1ZCenterOpCore_le_centralizer_self
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    omega1ZCenterOpCore G p ≤
      Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hcomm : (⟨y, hy⟩ : ↥(omega1ZCenterOpCore G p)) * ⟨x, hx⟩ =
      ⟨x, hx⟩ * ⟨y, hy⟩ := omega1ZCenterOpCore_comm _ _
  exact congr_arg Subtype.val hcomm

/-- **Isaacs Thm 7.6 Step 6 setup** (mmd L3879): `K := C_G(V)` (where
`V = Ω₁(Z(O_p(G)))`) is `G`-normal.  Trivial: centralizers of normal subgroups
are normal. -/
instance centralizer_omega1ZCenterOpCore_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).Normal :=
  Subgroup.normal_centralizer

/-- **Isaacs Thm 7.6 Step 6 conclusion** (mmd L3882): if `K = C_G(V)` is a
`p`-group, then `K ≤ O_p(G)` via `normal_pgroup_le_opCore`. -/
theorem centralizer_omega1ZCenterOpCore_le_opCore_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_pg : IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))) :
    Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
      OddOrder.Isaacs.Ch01.opCore p G :=
  OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK_pg

/-! ### Step 6 main: `K := C_G(V)` is a `p`-group (mmd L3879-3884)

This is the heart of Step 6: for every prime `q ≠ p`, the action of any
Sylow `q`-subgroup `Q` of `K` on `Z(U) = Z(O_p(G))` (by conjugation) is
forced to be trivial via Cor 4.35 (`Q` fixes every element of order `p`
in `Z(U)`, namely all of `V`), so `Q ⊆ C_G(Z(U)) ⊆ C_G(Z(P)) = P`.  Then
`Q ⊆ P ∩ K`, but `Q` is a `q`-group and `P` is a `p`-group with `q ≠ p`,
forcing `Q = ⊥`.  Since all primes `q ≠ p` give trivial Sylow `q`-subgroups
of `K`, `K` is a `p`-group. -/

/-- The conjugation action of `Q ≤ K = C_G(V)` on `V = Ω₁ Z(U)` is trivial:
every element of `V` is fixed by every element of `Q`.  Pure unpacking of
`conj_fixes_omega1ZCenterOpCore_of_le_centralizer` into the action form needed
to apply Cor 4.35. -/
private theorem conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G}
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G))
    (z : ↥(zCenterOpCoreSubgroup G p)) (hz_p : z ^ p = 1) (q : ↥Q) :
    (conjActionOnZCenterOpCoreSubgroup Q q) z = z := by
  -- (z : G) ∈ V := Ω₁ Z(U) since z ∈ Z(U) and z^p = 1.
  have hz_V : (z : G) ∈ omega1ZCenterOpCore G p := by
    rw [mem_omega1ZCenterOpCore]
    refine ⟨z.2, ?_⟩
    -- z^p = 1 in subtype ↥(Z(U)) ⇒ (z : G)^p = 1.
    have hzp_coe := congr_arg (fun x : ↥(zCenterOpCoreSubgroup G p) => (x : G)) hz_p
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hzp_coe
    exact hzp_coe
  -- Q ⊆ C_G(V), so (q : G) * (z : G) * (q : G)⁻¹ = (z : G).
  have hconj : (q : G) * (z : G) * (q : G)⁻¹ = (z : G) :=
    conj_fixes_omega1ZCenterOpCore_of_le_centralizer hQ_le_K q hz_V
  apply Subtype.ext
  -- (conjActionOnZCenterOpCoreSubgroup Q q) z = MulAut.conjNormal (q : G) z
  unfold conjActionOnZCenterOpCoreSubgroup
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  exact hconj

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
the centralizer of `Z(U)` in `G`.

Apply Cor 4.35 (`cor_4_35_for_zCenterOpCoreSubgroup`) with the conjugation action
of `Q` on `Z(U)`: `Q` is a `p'`-group, and `Q` fixes every order-`p` element of
`Z(U)` (these are the elements of `V = Ω₁ Z(U)`, and `Q ⊆ K = C_G(V)`).  This
yields `actionCommutator = ⊥`, i.e., `Q` acts trivially on `Z(U)`. -/
private theorem q_subgroup_in_K_le_centralizer_zCenter
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  -- (1) Q is a p'-group: q ≠ p prime + |Q| = q^k ⇒ p ∤ |Q|.
  have hQp' : ¬ p ∣ Nat.card Q := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ_q
    rw [hk]
    intro hpdvd
    have hp_prime : p.Prime := Fact.out
    have hq_dvd_p : p ∣ q := hp_prime.dvd_of_dvd_pow hpdvd
    -- p ∣ q with p, q prime ⇒ p = q
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp_prime hq_prime).mp hq_dvd_p
    exact hqp this.symm
  -- (2) Apply Cor 4.35: the conjugation action of Q on Z(U) has actionCommutator = ⊥.
  have h_ac_bot :
      OddOrder.Isaacs.Ch04.actionCommutator (conjActionOnZCenterOpCoreSubgroup Q)
        = ⊥ :=
    cor_4_35_for_zCenterOpCoreSubgroup (conjActionOnZCenterOpCoreSubgroup Q) hQp'
      (fun z hz_p s => conj_fixes_zCenterOpCoreSubgroup_v_of_le_centralizer hQ_le_K z hz_p s)
  -- (3) Translate "actionCommutator = ⊥" into "Q acts trivially":
  --     for all (qq : Q), (z : Z(U)), MulAut.conjNormal qq z = z.
  have h_trivial :
      ∀ qq : Q, ∀ z : ↥(zCenterOpCoreSubgroup G p),
        (conjActionOnZCenterOpCoreSubgroup Q qq) z = z :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially _).mp h_ac_bot
  -- (4) Convert to: Q ⊆ C_G(Z(U)) inside G.
  intro qq hqq_Q
  rw [Subgroup.mem_centralizer_iff]
  rintro z hz
  -- z ∈ Z(U) as Subgroup G ⇒ z is in zCenterOpCoreSubgroup, lifted from a z' in subtype.
  -- Apply h_trivial at (⟨qq, hqq_Q⟩ : ↥Q) and (⟨z, hz⟩ : ↥(Z(U))).
  have hcommute := h_trivial ⟨qq, hqq_Q⟩ ⟨z, hz⟩
  -- hcommute: (conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ = ⟨z, hz⟩
  -- Unfold: MulAut.conjNormal (qq) ⟨z, hz⟩ = ⟨z, hz⟩, i.e., qq * z * qq⁻¹ = z.
  have hcommute_coe : ((conjActionOnZCenterOpCoreSubgroup Q ⟨qq, hqq_Q⟩) ⟨z, hz⟩ : G)
      = (⟨z, hz⟩ : ↥(zCenterOpCoreSubgroup G p)) := by
    rw [hcommute]
  unfold conjActionOnZCenterOpCoreSubgroup at hcommute_coe
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply] at hcommute_coe
  -- hcommute_coe : qq * z * qq⁻¹ = z. Rearrange to z * qq = qq * z.
  calc z * qq = (qq * z * qq⁻¹) * qq := by rw [hcommute_coe]
    _ = qq * z := by group

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is contained in
`P`, under hypothesis (v) `P = C_G(Z(P))` and `O_{p'}(G) = ⊥`.

Combines `q_subgroup_in_K_le_centralizer_zCenter` (yielding `Q ⊆ C_G(Z(U))`) with
the chain `Z(P) ⊆ Z(U)` (`center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot`)
+ contravariant `centralizer_le` + hypothesis (v) `C_G(Z(P)) = P`. -/
private theorem q_subgroup_in_K_le_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q ≤ (P : Subgroup G) := by
  -- Q ⊆ C_G(Z(U)).
  have hQ_cZU : Q ≤ Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) :=
    q_subgroup_in_K_le_centralizer_zCenter hq_prime hqp hQ_q hQ_le_K
  -- Z(P) ⊆ Z(U), so C_G(Z(U)) ⊆ C_G(Z(P)) = P.
  have hZP_le_ZU :
      ((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) ≤
        zCenterOpCoreSubgroup G p :=
    center_sylow_le_zCenterOpCoreSubgroup_of_oPiCorePrime_eq_bot hOp' P
  have hC_ZU_le_C_ZP :
      Subgroup.centralizer (zCenterOpCoreSubgroup G p : Set G) ≤
        Subgroup.centralizer
          (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G) :=
    Subgroup.centralizer_le hZP_le_ZU
  rw [h_centralizer_center] at hC_ZU_le_C_ZP
  exact hQ_cZU.trans hC_ZU_le_C_ZP

/-- A `q`-subgroup `Q` of `K = C_G(V)` (`q ≠ p` prime) is trivial,
under the Thm 7.6 hypotheses (iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`.

From `q_subgroup_in_K_le_sylow` we get `Q ⊆ P`.  Then `Q` is a `q`-group inside a
`p`-group `P` with `q ≠ p`, forcing `Q = ⊥` by coprimality of cardinalities. -/
private theorem q_subgroup_in_K_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G))
    {q : ℕ} (hq_prime : q.Prime) (hqp : q ≠ p)
    {Q : Subgroup G} (hQ_q : IsPGroup q Q)
    (hQ_le_K : Q ≤ Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) :
    Q = ⊥ := by
  haveI : Fact q.Prime := ⟨hq_prime⟩
  have hQ_le_P : Q ≤ (P : Subgroup G) :=
    q_subgroup_in_K_le_sylow hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- Q is a q-group and Q ≤ P which is a p-group; coprime ⇒ |Q| = 1.
  have hP_p : IsPGroup p (P : Subgroup G) := P.isPGroup'
  have hQ_p : IsPGroup p Q := hP_p.to_le hQ_le_P
  obtain ⟨a, hQa⟩ := IsPGroup.iff_card.mp hQ_q
  obtain ⟨b, hQb⟩ := IsPGroup.iff_card.mp hQ_p
  have hp_prime : p.Prime := Fact.out
  have hQ_card : Nat.card Q = 1 := by
    have h_eq : q ^ a = p ^ b := hQa.symm.trans hQb
    by_contra h_ne
    have ha_pos : 1 ≤ a := by
      rcases a with _ | a'
      · -- a = 0 ⇒ |Q| = q^0 = 1, contradicting h_ne.
        exfalso
        apply h_ne
        rw [hQa, pow_zero]
      · exact Nat.le_add_left 1 a'
    have hq_dvd_qa : q ∣ q ^ a := dvd_pow_self q (Nat.one_le_iff_ne_zero.mp ha_pos)
    rw [h_eq] at hq_dvd_qa
    have hq_dvd_p : q ∣ p := hq_prime.dvd_of_dvd_pow hq_dvd_qa
    have : q = p := (Nat.prime_dvd_prime_iff_eq hq_prime hp_prime).mp hq_dvd_p
    exact hqp this
  exact Subgroup.eq_bot_of_card_eq Q hQ_card

/-- **Isaacs Thm 7.6 Step 6 main** (mmd L3879-3884): under hypotheses
(iv) `O_{p'}(G) = ⊥` and (v) `P = C_G(Z(P))`, `K := C_G(V)` is a `p`-group.

Proof: for every `g ∈ K`, the order `orderOf g` has only `p` as a prime divisor.
Indeed, if some prime `q ≠ p` divided `orderOf g = n`, then `g^(n/q) ∈ K` would
generate a `q`-subgroup of order `q`, which is forced to be trivial by
`q_subgroup_in_K_eq_bot`, contradicting `orderOf (g^(n/q)) = q > 1`.

Hence `orderOf g` is a power of `p` for every `g ∈ K`, so `K` is a `p`-group. -/
theorem centralizer_omega1ZCenterOpCore_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    [OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ) G]
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ p} G = ⊥) (P : Sylow p G)
    (h_centralizer_center :
       Subgroup.centralizer
         (((Subgroup.center (P : Subgroup G)).map (P : Subgroup G).subtype) : Set G)
         = (P : Subgroup G)) :
    IsPGroup p (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)) := by
  -- Use IsPGroup.iff_orderOf: K is a p-group iff every g ∈ K has order a power of p.
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg_K⟩
  set K : Subgroup G := Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) with hK_def
  -- Step (1): orderOf ⟨g, hg_K⟩ in K = orderOf g in G.
  set n : ℕ := orderOf g with hn_def
  have h_ord_eq : orderOf (⟨g, hg_K⟩ : ↥K) = n := Subgroup.orderOf_mk g hg_K
  rw [h_ord_eq]
  -- Reduce to: n is a power of p. Argue by contradiction.
  by_contra hno_pk
  push Not at hno_pk
  have hn_pos : 0 < n := orderOf_pos g
  have hp_prime : p.Prime := Fact.out
  -- ∃ q prime, q ≠ p, q ∣ n.
  have h_exists_q : ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ n := by
    by_contra h_all
    push Not at h_all
    suffices ∀ q ∈ n.primeFactorsList, q = p by
      have : ∃ k, n = p ^ k := by
        refine ⟨n.primeFactorsList.length, ?_⟩
        rw [← List.prod_replicate, ← List.eq_replicate_of_mem this,
          Nat.prod_primeFactorsList hn_pos.ne']
      obtain ⟨k, hk⟩ := this
      exact hno_pk _ hk
    intro q hq
    obtain ⟨hq_prime, hq_dvd⟩ := (Nat.mem_primeFactorsList hn_pos.ne').mp hq
    by_contra hqp
    exact h_all q hq_prime hqp hq_dvd
  obtain ⟨q, hq_prime, hqp, hq_dvd_n⟩ := h_exists_q
  -- Set h := g^(n/q). It has order q.
  set h_elem : G := g ^ (n / q) with h_elem_def
  have hh_K : h_elem ∈ K := K.pow_mem hg_K _
  have hgq_pow_q : h_elem ^ q = 1 := by
    rw [h_elem_def, ← pow_mul, Nat.div_mul_cancel hq_dvd_n, pow_orderOf_eq_one]
  -- h ≠ 1 because n/q < n and orderOf g = n.
  have hh_ne_one : h_elem ≠ 1 := by
    intro h_eq
    have h_div : n ∣ (n / q) := by
      rw [hn_def]; exact orderOf_dvd_of_pow_eq_one h_eq
    have hq_two : 2 ≤ q := hq_prime.two_le
    have hnq_lt : n / q < n := Nat.div_lt_self hn_pos hq_two
    have hnq_pos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn_pos hq_dvd_n) hq_prime.pos
    have : n ≤ n / q := Nat.le_of_dvd hnq_pos h_div
    omega
  -- orderOf h = q.
  have hh_ord : orderOf h_elem = q := by
    have h_ord_dvd : orderOf h_elem ∣ q := orderOf_dvd_of_pow_eq_one hgq_pow_q
    rcases (Nat.dvd_prime hq_prime).mp h_ord_dvd with h1 | hqeq
    · exact absurd (orderOf_eq_one_iff.mp h1) hh_ne_one
    · exact hqeq
  -- Q := Subgroup.zpowers h is a q-group of K.
  have hQ_q : IsPGroup q (Subgroup.zpowers h_elem) := by
    haveI : Fact q.Prime := ⟨hq_prime⟩
    rw [IsPGroup.iff_card]
    refine ⟨1, ?_⟩
    rw [Nat.card_zpowers, hh_ord, pow_one]
  have hQ_le_K : (Subgroup.zpowers h_elem) ≤ K := by
    rw [Subgroup.zpowers_le]; exact hh_K
  -- Apply q_subgroup_in_K_eq_bot: ⟨h⟩ = ⊥.
  have hQ_bot : Subgroup.zpowers h_elem = ⊥ :=
    q_subgroup_in_K_eq_bot hOp' P h_centralizer_center hq_prime hqp hQ_q hQ_le_K
  -- But h ∈ ⟨h⟩ = ⊥ ⇒ h = 1, contradicting hh_ne_one.
  have : h_elem ∈ Subgroup.zpowers h_elem := Subgroup.mem_zpowers _
  rw [hQ_bot, Subgroup.mem_bot] at this
  exact hh_ne_one this

/-- **Isaacs Thm 7.6 Step 6 faithfulness** (mmd L3884): `K̄ = ⊥` in `Ḡ` given
`K ≤ U`.  This is the final Step 6 conclusion: the Ḡ-action on V is faithful
because its kernel `K̄ = (K.map mk')` is trivial. -/
theorem centralizer_omega1ZCenterOpCore_map_eq_bot_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hK_le_U : Subgroup.centralizer (omega1ZCenterOpCore G p : Set G) ≤
        OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.centralizer (omega1ZCenterOpCore G p : Set G)).map
        (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G)) = ⊥ := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  -- Goal: K ≤ oPiCore {p} G
  intro x hx
  have hx_U : x ∈ OddOrder.Isaacs.Ch01.opCore p G := hK_le_U hx
  rwa [show OddOrder.Isaacs.Ch01.opCore p G =
        OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G from
      (OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := G) p).symm] at hx_U

/-! ### Step 7 counting argument: `|V : V ∩ A| ≤ p` (mmd L3886-3892)

The book's Step 7 derives a counting bound on `V := Ω₁ Z(O_p(G))`:

> Write `D = U ∩ A` and `E = V ∩ A`.  Then `|V:E| = |V:V∩D| = |VD:D|`.  Now
> `D` is elementary abelian in `U`, and `V` is a central elementary abelian
> subgroup of `U`, so `VD` is elementary abelian.  By `A ∈ E(P)`, `|VD| ≤ |A|`,
> hence `|VD:D| ≤ |A:D| = |Ā| = p`.

We package this combinatorial step as `omega1ZCenterOpCore_relIndex_inter_A_le`,
isolating from the broader Goldschmidt argument the part that only needs
elementary-abelian structure, `V ≤ centralizer U`, and the maximality of
`A ∈ maxElemAbelianIn P p`.

The hypothesis `|A : A ⊓ U| ≤ p` is supplied externally (it is the Step 5
conclusion `|Ā| = p`). -/

/-- **Subgroup `V ⊔ D` is contained in its own centralizer** when `V`
centralizes `D`, `V` is commutative, and `D` is commutative.

This packages `V ⊔ D ≤ centralizer (V ⊔ D)`, i.e., `V ⊔ D` is abelian. -/
private theorem sup_le_centralizer_self_of_centralizing
    {G : Type*} [Group G] {V D : Subgroup G}
    (hV_comm : ∀ x y : ↥V, x * y = y * x)
    (hD_comm : ∀ x y : ↥D, x * y = y * x)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G) ≤ Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
  -- Strategy: show V ∪ D ⊆ centralizer (V ⊔ D), then by closure of centralizer.
  -- centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- V ⊔ D = closure (V ∪ D), giving the conclusion.
  have h_VuD_in_cent : (V : Set G) ∪ (D : Set G) ⊆
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) := by
    -- Show each element of V ∪ D commutes with every element of V ⊔ D.
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    -- x ∈ V ⊔ D ⟺ x ∈ closure (V ∪ D). Use closure_induction.
    have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
      rwa [← Subgroup.sup_eq_closure]
    clear hx
    -- w ∈ V ∪ D, x ∈ closure (V ∪ D). Goal: x * w = w * x.
    induction hx_clos using Subgroup.closure_induction with
    | mem y hy =>
      -- Both w and y are in V ∪ D, show they commute.
      rcases hw with hw_V | hw_D
      · rcases hy with hy_V | hy_D
        · have := hV_comm ⟨y, hy_V⟩ ⟨w, hw_V⟩
          exact congr_arg Subtype.val this
        · -- w ∈ V, y ∈ D: hVD says V centralizes D.
          have h_w_cent := hVD hw_V
          rw [Subgroup.mem_centralizer_iff] at h_w_cent
          exact h_w_cent y hy_D
      · rcases hy with hy_V | hy_D
        · -- w ∈ D, y ∈ V: hVD says V centralizes D.
          have h_y_cent := hVD hy_V
          rw [Subgroup.mem_centralizer_iff] at h_y_cent
          exact (h_y_cent w hw_D).symm
        · have := hD_comm ⟨y, hy_D⟩ ⟨w, hw_D⟩
          exact congr_arg Subtype.val this
    | one => rw [one_mul, mul_one]
    | mul a b _ _ ha hb =>
      calc (a * b) * w = a * (b * w) := by group
        _ = a * (w * b) := by rw [hb]
        _ = (a * w) * b := by group
        _ = (w * a) * b := by rw [ha]
        _ = w * (a * b) := by group
    | inv a _ ha =>
      have hcomm : a * w = w * a := ha
      calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [hcomm]
        _ = w * a⁻¹ := by group
  -- Now centralizer is a subgroup, so closure (V ∪ D) ⊆ centralizer (V ⊔ D).
  -- The result follows because V ⊔ D = closure (V ∪ D).
  intro x hx
  -- Convert hx to closure form, apply h_VuD_in_cent + closure_le.
  have hx_clos : x ∈ Subgroup.closure ((V : Set G) ∪ (D : Set G)) := by
    rwa [← Subgroup.sup_eq_closure]
  exact (Subgroup.closure_le _).mpr h_VuD_in_cent hx_clos

/-- **VD is elementary abelian**: if `V` centralizes `D`, both `V` and `D` are
elementary abelian `p`-groups, and `V` is normal in `G`, then `V ⊔ D` is also
elementary abelian.

Proof: by `mul_normal`, every element of `V ⊔ D` is `v * d` for some `v ∈ V`,
`d ∈ D`.  Commutativity in `V ⊔ D` and exponent `p` both follow from `V` and
`D` commuting pointwise. -/
private theorem sup_isElementaryAbelian_of_centralizing
    {G : Type*} [Group G] {p : ℕ} {V D : Subgroup G} [V.Normal]
    (hV : V.IsElementaryAbelian p) (hD : D.IsElementaryAbelian p)
    (hVD : V ≤ Subgroup.centralizer (D : Set G)) :
    (V ⊔ D : Subgroup G).IsElementaryAbelian p := by
  have h_VD_comm : (V ⊔ D : Subgroup G) ≤
      Subgroup.centralizer ((V ⊔ D : Subgroup G) : Set G) :=
    sup_le_centralizer_self_of_centralizing hV.1 hD.1 hVD
  -- Element decomposition: every element of V ⊔ D is v*d for v ∈ V, d ∈ D.
  have h_decomp : ∀ x ∈ (V ⊔ D : Subgroup G), ∃ v ∈ V, ∃ d ∈ D, (v * d : G) = x := by
    intro x hx
    have h_mul : (↑(V ⊔ D) : Set G) = V * D := Subgroup.normal_mul V D
    have hx_set : x ∈ (↑(V ⊔ D) : Set G) := hx
    rw [h_mul] at hx_set
    obtain ⟨v, hv, d, hd, hvd⟩ := hx_set
    exact ⟨v, hv, d, hd, hvd⟩
  refine ⟨?_, ?_⟩
  · -- Commutativity in V ⊔ D.
    intro x y
    apply Subtype.ext
    have hxy_cent := h_VD_comm x.2
    rw [Subgroup.mem_centralizer_iff] at hxy_cent
    have : (y : G) * x = x * y := hxy_cent y y.2
    exact this.symm
  · -- Exponent p.  In V ⊔ D, every element w has w^p = 1.
    intro w
    apply Subtype.ext
    change (w.val : G) ^ p = 1
    -- w = v * d for some v ∈ V, d ∈ D.
    obtain ⟨v, hv_V, d, hd_D, hvd_eq⟩ := h_decomp w.val w.2
    rw [← hvd_eq]
    -- (v * d)^p = v^p * d^p (since v and d commute), and v^p = 1, d^p = 1.
    have hv_d_comm : v * d = d * v := by
      have hv_cent := hVD hv_V
      rw [Subgroup.mem_centralizer_iff] at hv_cent
      exact (hv_cent d hd_D).symm
    have hCom : Commute v d := hv_d_comm
    have : (v * d) ^ p = v ^ p * d ^ p := Commute.mul_pow hCom p
    rw [this]
    have hv_p : v ^ p = 1 := by
      have := hV.2 ⟨v, hv_V⟩
      exact congr_arg Subtype.val this
    have hd_p : d ^ p = 1 := by
      have := hD.2 ⟨d, hd_D⟩
      exact congr_arg Subtype.val this
    rw [hv_p, hd_p, mul_one]

/-- **Isaacs Thm 7.6 Step 7** (mmd L3886-3892): `|V : V ∩ A| ≤ p` for any
`A ∈ maxElemAbelianIn P p`, assuming `|A : A ∩ U| ≤ p` (Step 5).

`A.relIndex V` is `|V : V ⊓ A|` in book notation
(`(A.subgroupOf V).index = |V/(A ⊓ V)|`).  Similarly,
`(A ⊓ U).relIndex A = |A : A ⊓ U|` is the Step-5 bound.

The book's argument:
1. Set `D = U ∩ A` and `E = V ∩ A`.  Observe `V ⊆ U` (so `V ∩ A = V ∩ D`).
2. `D` is elementary abelian (sub of `A`).
3. `V` is elementary abelian and central in `U`, so `V ⊆ centralizer D`.
4. `VD := V ⊔ D` is elementary abelian (`sup_isElementaryAbelian_of_centralizing`).
5. `VD ≤ P` (since `V ≤ U ≤ P` and `D ≤ A ≤ P`).
6. By maximality `A ∈ E(P)`, `|VD| ≤ |A|`, so `|VD : D| ≤ |A : D|`.
7. By second isomorphism (V normal, V centralizes D), `|V : V ∩ D| = |VD : D|`.
8. Combine: `|V : V ∩ A| = |V : V ∩ D| = |VD : D| ≤ |A : D| ≤ p`. -/
theorem omega1ZCenterOpCore_relIndex_inter_A_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {A : Subgroup G}
    (hA : A ∈ Subgroup.maxElemAbelianIn (P : Subgroup G) p)
    (hA_D_relIndex : (OddOrder.Isaacs.Ch01.opCore p G).relIndex A ≤ p) :
    A.relIndex (omega1ZCenterOpCore G p) ≤ p := by
  classical
  set V : Subgroup G := omega1ZCenterOpCore G p with hV_def
  set U : Subgroup G := OddOrder.Isaacs.Ch01.opCore p G with hU_def
  set D : Subgroup G := A ⊓ U with hD_def
  -- Basic facts.
  have hV_le_U : V ≤ U := omega1ZCenterOpCore_le_opCore
  have hA_P : A ≤ (P : Subgroup G) := hA.1
  have hU_P : U ≤ (P : Subgroup G) := OddOrder.Isaacs.Ch01.opCore_le P
  have hA_el : A.IsElementaryAbelian p := hA.2.1
  have hD_el : D.IsElementaryAbelian p :=
    inf_isElementaryAbelian_of_isElementaryAbelian hA_el U
  have hV_el : V.IsElementaryAbelian p := omega1ZCenterOpCore_isElementaryAbelian
  have hV_cent_U : V ≤ Subgroup.centralizer (U : Set G) :=
    omega1ZCenterOpCore_centralizes_opCore
  have hD_le_U : D ≤ U := inf_le_right
  have hD_le_A : D ≤ A := inf_le_left
  have hV_cent_D : V ≤ Subgroup.centralizer (D : Set G) :=
    hV_cent_U.trans (Subgroup.centralizer_le hD_le_U)
  -- V ⊔ D is elementary abelian.
  haveI : V.Normal := omega1ZCenterOpCore_normal
  have hVD_el : (V ⊔ D : Subgroup G).IsElementaryAbelian p :=
    sup_isElementaryAbelian_of_centralizing hV_el hD_el hV_cent_D
  -- V ⊔ D ≤ P.
  have hVD_le_P : (V ⊔ D : Subgroup G) ≤ (P : Subgroup G) := by
    rw [sup_le_iff]
    exact ⟨hV_le_U.trans hU_P, hD_le_A.trans hA_P⟩
  -- Maximality of A: |V ⊔ D| ≤ |A|.
  have hVD_card_le_A : Nat.card (V ⊔ D : Subgroup G) ≤ Nat.card A :=
    hA.2.2 (V ⊔ D) hVD_le_P hVD_el
  -- A.relIndex V = |V : V ∩ A| (book notation).  Rewrite via V ⊓ A = V ⊓ D.
  -- V ⊓ A = V ⊓ U ⊓ A = V ⊓ (U ⊓ A) = V ⊓ (A ⊓ U) = V ⊓ D since V ≤ U.
  have hVA_eq_VD : V ⊓ A = V ⊓ D := by
    have h_VU : V ⊓ U = V := inf_eq_left.mpr hV_le_U
    rw [hD_def, inf_comm A U, ← inf_assoc, h_VU]
  have hAV_eq : A.relIndex V = D.relIndex V := by
    -- A.relIndex V = (A ⊓ V).relIndex V via inf_relIndex_right.
    -- Same for D. Use V ⊓ A = V ⊓ D, i.e., A ⊓ V = D ⊓ V (by inf_comm).
    have h1 : A.relIndex V = (A ⊓ V).relIndex V := (Subgroup.inf_relIndex_right A V).symm
    have h2 : D.relIndex V = (D ⊓ V).relIndex V := (Subgroup.inf_relIndex_right D V).symm
    have h_inf_comm : A ⊓ V = D ⊓ V := by
      rw [inf_comm A V, inf_comm D V]; exact hVA_eq_VD
    rw [h1, h2, h_inf_comm]
  rw [hAV_eq]
  -- Second isomorphism: V / (D ⊓ V) ≅ (V ⊔ D) / D, requiring V ≤ normalizer D.
  -- V centralizes D, so V ≤ centralizer D ≤ normalizer D.
  have hV_norm_D : V ≤ Subgroup.normalizer D := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hv_cent : v ∈ Subgroup.centralizer (D : Set G) := hV_cent_D hv
    have hv_inv_cent : v⁻¹ ∈ Subgroup.centralizer (D : Set G) := Subgroup.inv_mem _ hv_cent
    constructor
    · intro hy
      have hyv : y * v = v * y := Subgroup.mem_centralizer_iff.mp hv_cent y hy
      have heq : v * y * v⁻¹ = y := by
        calc v * y * v⁻¹ = (y * v) * v⁻¹ := by rw [hyv]
          _ = y := by group
      rw [heq]
      exact hy
    · intro hyc
      have hcomm := Subgroup.mem_centralizer_iff.mp hv_inv_cent (v * y * v⁻¹) hyc
      have heq : y = v⁻¹ * (v * y * v⁻¹) * v := by group
      have hpush : v⁻¹ * (v * y * v⁻¹) * v = v * y * v⁻¹ := by
        calc v⁻¹ * (v * y * v⁻¹) * v
            = (v * y * v⁻¹) * v⁻¹ * v := by rw [← hcomm]
          _ = v * y * v⁻¹ := by group
      rw [heq, hpush]
      exact hyc
  set VD : Subgroup G := V ⊔ D with hVD_def
  have hD_le_VD : D ≤ VD := hVD_def ▸ le_sup_right
  -- Apply second iso: |V/(D ⊓ V).subgroupOf V| = |VD/D.subgroupOf VD|.
  letI hD_normal_in_V : (D.subgroupOf V).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hV_norm_D
  letI hD_normal_in_VD : (D.subgroupOf VD).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hV_norm_D
  have h_card_quot_V : Nat.card (V ⧸ D.subgroupOf V) =
      Nat.card (VD ⧸ D.subgroupOf VD) :=
    Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient V D hV_norm_D).toEquiv
  have h_card_eq : D.relIndex V = D.relIndex VD := by
    unfold Subgroup.relIndex Subgroup.index
    exact h_card_quot_V
  rw [h_card_eq]
  -- Lagrange: |VD| = D.relIndex VD * |D|, |A| = U.relIndex A * |D|.
  have hD_card_pos : 0 < Nat.card D := Nat.card_pos
  have h_lag_VD : Nat.card VD = D.relIndex VD * Nat.card D := by
    have h_index_mul_card : (D.subgroupOf VD).index *
        Nat.card (D.subgroupOf VD) = Nat.card VD :=
      Subgroup.index_mul_card _
    have hD_card_eq : Nat.card (D.subgroupOf VD) = Nat.card D := by
      have h_map_eq : ((D.subgroupOf VD : Subgroup VD).map VD.subtype : Subgroup G) = D :=
        Subgroup.map_subgroupOf_eq_of_le hD_le_VD
      have h_card : Nat.card (D.subgroupOf VD) =
          Nat.card ((D.subgroupOf VD : Subgroup VD).map VD.subtype) :=
        (Subgroup.card_map_of_injective VD.subtype_injective).symm
      rw [h_card, h_map_eq]
    rw [show D.relIndex VD = (D.subgroupOf VD).index from rfl,
        ← h_index_mul_card, hD_card_eq]
  have h_lag_A : Nat.card A = U.relIndex A * Nat.card D := by
    have h_index_mul_card : (U.subgroupOf A).index *
        Nat.card (U.subgroupOf A) = Nat.card A :=
      Subgroup.index_mul_card _
    have hU_subgrpOf_card : Nat.card (U.subgroupOf A) = Nat.card D := by
      -- (U.subgroupOf A).map A.subtype = U ⊓ A = A ⊓ U = D.
      have h_map_eq : ((U.subgroupOf A : Subgroup A).map A.subtype : Subgroup G) = U ⊓ A :=
        Subgroup.subgroupOf_map_subtype U A
      have h_card : Nat.card (U.subgroupOf A) =
          Nat.card ((U.subgroupOf A : Subgroup A).map A.subtype) :=
        (Subgroup.card_map_of_injective A.subtype_injective).symm
      rw [h_card, h_map_eq, inf_comm, ← hD_def]
    rw [show U.relIndex A = (U.subgroupOf A).index from rfl,
        ← h_index_mul_card, hU_subgrpOf_card]
  -- D.relIndex VD * |D| = |VD| ≤ |A| = U.relIndex A * |D|.
  have hVD_card_le_A' : Nat.card VD ≤ Nat.card A := hVD_card_le_A
  have hmul_le : D.relIndex VD * Nat.card D ≤ U.relIndex A * Nat.card D := by
    rw [← h_lag_VD, ← h_lag_A]
    exact hVD_card_le_A'
  exact (Nat.le_of_mul_le_mul_right hmul_le hD_card_pos).trans hA_D_relIndex

/-! ### Step 7-8: closing reductions (mmd L3884-3896)

Once Step 5-6 produce the triviality of the `A`-action on `V = Z(L)`, the book:

* (Step 7) Combines `[A, V] = 1` with hypothesis (v) `P = C_G(Z(P))` and the
  maximality of `A ∈ E(P)` to force `A ⊆ L`, contradicting `A ⊄ L`.
* (Step 8) From Step 2's conclusion `J(P) ≤ L`, applies Thm 7.2
  (`thompsonJ_eq_of_le_of_le`) to get `J(L) = J(P)`, then uses that `J(L)` is
  characteristic in `L` and `L` is characteristic in `G` to conclude
  `J(P) ⊴ G`.

The Step 7 contradiction itself is a delicate counting argument over `E(P)`
combined with the action analysis; we defer it.  Step 8 only needs the Thm 7.2
bridge, which we record here. -/

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893): if `J(P) ≤ L` and `L ≤ P` then
`J(L) = J(P)`, the consequence of Thm 7.2 needed in the closing step. -/
private theorem thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
  Subgroup.thompsonJ_eq_of_le_of_le h_le (OddOrder.Isaacs.Ch01.opCore_le P)

/-- **Conjugating `maxElemAbelianIn L p` by `g ∈ G`** when `L` is `G`-normal.

If `L ⊴ G` and `E ∈ maxElemAbelianIn L p`, then for any `g : G`, the conjugate
`g E g⁻¹` is again in `maxElemAbelianIn L p`.  Pure normality + the fact that
conjugation is an isomorphism (preserves cardinality and elementary-abelian
property). -/
private theorem maxElemAbelianIn_conj_mem
    {G : Type*} [Group G] {L E : Subgroup G} [hL : L.Normal] {p : ℕ}
    (hE : E ∈ Subgroup.maxElemAbelianIn L p) (g : G) :
    E.map (MulAut.conj g).toMonoidHom ∈ Subgroup.maxElemAbelianIn L p := by
  refine ⟨?_, ?_, ?_⟩
  · -- E.map (conj g) ≤ L
    rintro _ ⟨e, he_E, rfl⟩
    have he_L : e ∈ L := hE.1 he_E
    change g * e * g⁻¹ ∈ L
    exact hL.conj_mem _ he_L g
  · -- E.map (conj g) is elementary abelian
    refine ⟨?_, ?_⟩
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩ ⟨_, ⟨b, hb_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹)
      have habcomm : a * b = b * a := by
        have h := hE.2.1.comm ⟨a, ha_E⟩ ⟨b, hb_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) * (g * b * g⁻¹)
          = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [habcomm]
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group
    · rintro ⟨_, ⟨a, ha_E, rfl⟩⟩
      apply Subtype.ext
      change (g * a * g⁻¹) ^ p = 1
      have ha_p : a ^ p = 1 := by
        have h := hE.2.1.pow_eq_one ⟨a, ha_E⟩
        exact congr_arg Subtype.val h
      calc (g * a * g⁻¹) ^ p
          = g * a ^ p * g⁻¹ := by
            rw [conj_pow]
        _ = g * 1 * g⁻¹ := by rw [ha_p]
        _ = 1 := by group
  · -- E.map (conj g) is of maximum cardinality
    intro F hF_L hF_el
    have hF_conj_card : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) =
        Nat.card F :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    have hE_conj_card : Nat.card (E.map (MulAut.conj g).toMonoidHom : Subgroup G) =
        Nat.card E :=
      Subgroup.card_map_of_injective (MulEquiv.injective _)
    rw [hE_conj_card]
    have hF_inv : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ L := by
      rintro _ ⟨e, he_F, rfl⟩
      have he_L : e ∈ L := hF_L he_F
      change g⁻¹ * e * g⁻¹⁻¹ ∈ L
      exact hL.conj_mem _ he_L g⁻¹
    have hF_inv_el : (F.map (MulAut.conj g⁻¹).toMonoidHom).IsElementaryAbelian p := by
      refine ⟨?_, ?_⟩
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩ ⟨_, ⟨b, hb_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹) =
          (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹)
        have habcomm : a * b = b * a := by
          have h := hF_el.comm ⟨a, ha_F⟩ ⟨b, hb_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) * (g⁻¹ * b * g⁻¹⁻¹)
            = g⁻¹ * (a * b) * g⁻¹⁻¹ := by group
          _ = g⁻¹ * (b * a) * g⁻¹⁻¹ := by rw [habcomm]
          _ = (g⁻¹ * b * g⁻¹⁻¹) * (g⁻¹ * a * g⁻¹⁻¹) := by group
      · rintro ⟨_, ⟨a, ha_F, rfl⟩⟩
        apply Subtype.ext
        change (g⁻¹ * a * g⁻¹⁻¹) ^ p = 1
        have ha_p : a ^ p = 1 := by
          have h := hF_el.pow_eq_one ⟨a, ha_F⟩
          exact congr_arg Subtype.val h
        calc (g⁻¹ * a * g⁻¹⁻¹) ^ p
            = g⁻¹ * a ^ p * g⁻¹⁻¹ := by rw [conj_pow]
          _ = g⁻¹ * 1 * g⁻¹⁻¹ := by rw [ha_p]
          _ = 1 := by group
    have := hE.2.2 (F.map (MulAut.conj g⁻¹).toMonoidHom) hF_inv hF_inv_el
    rw [hF_conj_card] at this
    exact this

/-- **Isaacs Thm 7.6 Step 8** (mmd L3893-3896): under the running hypotheses, the
**conditional conclusion** of Step 2 (`J(P) ≤ L`) yields normality of `J(P)` in `G`.

Strategy: from `J(P) ≤ L = O_p(G)` and the Step 2 / Thm 7.2 bridge, `J(L) = J(P)`.
Then `g ∈ G`, `E ∈ E(L)` ⇒ `g E g⁻¹ ∈ E(L)` (`maxElemAbelianIn_conj_mem`), so the
iSup defining `J(L)` is `G`-stable. -/
theorem normal_thompsonJ_of_le_opCore
    {G : Type*} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    (h_le : Subgroup.thompsonJ (P : Subgroup G) p ≤ OddOrder.Isaacs.Ch01.opCore p G) :
    (Subgroup.thompsonJ (P : Subgroup G) p).Normal := by
  -- Replace J(P) by J(L) using Thm 7.2.
  have hJLP : Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p =
      Subgroup.thompsonJ (P : Subgroup G) p :=
    thompsonJ_opCore_eq_thompsonJ_sylow_of_thompsonJ_le_opCore P h_le
  rw [← hJLP]
  -- It suffices to show: ∀ g ∈ G, (J(L)).map (conj g) ≤ J(L).
  refine ⟨?_⟩
  intro n hn g
  -- Reduce to: g * J(L) * g⁻¹ ≤ J(L).
  -- We show `(J(L)).map (MulAut.conj g).toMonoidHom ≤ J(L)`.
  have h_map_le :
      (Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom ≤
      Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p := by
    rw [show Subgroup.thompsonJ (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p
          = ⨆ E ∈ Subgroup.maxElemAbelianIn
            (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p, E from rfl,
        Subgroup.map_iSup]
    refine iSup_le fun E => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hE_mem => ?_
    -- E.map (conj g) ∈ maxElemAbelianIn L p, so E.map (conj g) ≤ J(L).
    have h_conj_mem :=
      maxElemAbelianIn_conj_mem (L := OddOrder.Isaacs.Ch01.opCore p G) hE_mem g
    exact Subgroup.le_thompsonJ_of_mem_maxElemAbelianIn h_conj_mem
  have : g * n * g⁻¹ ∈ (Subgroup.thompsonJ
      (OddOrder.Isaacs.Ch01.opCore p G : Subgroup G) p).map
        (MulAut.conj g).toMonoidHom := by
    refine ⟨n, hn, ?_⟩
    change g * n * g⁻¹ = g * n * g⁻¹
    rfl
  exact h_map_le this

/-! ### Step 7: contradiction giving `J(P) ≤ L` (mmd L3884-3892)

The book's Step 7 combines:

* The Step 5-6 conclusion: `A` acts trivially on `V := Z(O_p(G))`, i.e.,
  `[A, V] = 1` (`A` and `V` commute pointwise).
* The Step 1 conclusion: `Z(P) ≤ Z(L)` (Z(P) sits inside Z(L) since
  Z(P) commutes with all of L).
* The hypothesis (v): `P = C_G(Z(P))`.
* The maximality of `A ∈ E(P)`.

The combined counting argument forces `A ⊆ L`, contradicting the choice of
`A ⊄ L`.  This is the most delicate part of the Goldschmidt-style proof; we
**axiomatize the Step 7 conclusion** as the existence of a contradiction from
the working hypotheses, and use it together with Step 8's wrap-up.

Tracking issue: [`issues/0036-stuck-7-6-step-7.md`](../../../issues/0036-stuck-7-6-step-7.md). -/


end OddOrder.Isaacs.Ch07
