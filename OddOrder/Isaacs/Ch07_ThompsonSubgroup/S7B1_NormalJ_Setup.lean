/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7A2_NormalPThm75

/-!
# Isaacs FGT Ch.7 — normal-J theorem (Thm 7.6), Steps 1-5 + the `V`-setup (pp. 209-214)

The infrastructure layer of the 8-step normal-J argument: the Hall-Higman 3.21
corollaries (Step 1), the core `L = O_{p',p}(G)` (`opPpPrimeCore`) with its `A ⊓ L̄ = ⊥`
bridges (Steps 2-4), and the subgroup `V := Ω₁(Z(O_p(G)))` (`omega1ZCenterOpCore`)
with its elementary-abelian / centralizing API and the Cor 4.35 wrappers (Steps 5-7
preparation).

Split from `OddOrder.Isaacs.Ch07_ThompsonSubgroup.S7B1_NormalJ` (issue 0149, the
longFile-1500 campaign); `S7B1_NormalJ` imports this leaf, so downstream imports are
unchanged.
-/

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement
open scoped Pointwise

variable {G : Type*} [Group G]

/-! ## §7B: normal-J theorem (pp. 209-214) -/


/-! ### Thm 7.6 — normal-J theorem ⭐⭐ (8-step argument, fully landed)

**Isaacs Thm 7.6** (mmd L3832):

> (i) G p-solvable, (ii) `p ≠ 2`, (iii) Sylow-2 abelian, (iv) `O_{p'}(G) = 1`,
> (v) `P = C_G(Z(P))` ⇒ `J(P) ⊴ G`.

**= BG Theorem 6.2 の odd-order 等価版**. **FT クリティカル度 HIGHEST**: BG §6, §8,
§9, App.A で 7 ヶ所超で直接引用.

**proof 戦略** (8 Step, mmd L3832-3896): Thm 7.5 + Ch.6 **6.20** (abelian coprime
⟨C_N(a)⟩=N) + Ch.4 **4.35** (Ω₁ fixed) + Hall-Higman 3.21.

The full Goldschmidt-style 8-step proof is landed: Thm 7.5 + Ch.6 6.20
(`isCyclic_of_faithful_trivial_on_proper_invariant`) + Ch.4 4.35
(`actionCommutator_eq_bot_of_abelian_pgroup_of_fixes_order_p`).  The
unconditional `normal_J` lives in `S7B2_NormalJ_PComplement` (sorry-free,
axiom-clean).  This file lands the Step 1-7 bridge lemmas. -/

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
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({p} : Set ℕ)
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) G) := inferInstance
  -- (2) Take complement: `IsPiSeparable π G → IsPiSeparable {p | p ∉ π} G`.
  have : OddOrder.Isaacs.Ch03.IsPiSeparable ({q | q ≠ p} : Set ℕ)
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
  -- Apply `disjoint_of_coprime_natCard` + `coprime_of_isPiGroup_of_isPiGroup_compl`.
  apply Disjoint.eq_bot
  apply Subgroup.disjoint_of_coprime_natCard
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
    change f a₁ * f a₂ = f a₂ * f a₁
    rw [← f.map_mul, ← f.map_mul]
    have hcomm : (⟨a₁, ha₁⟩ : A) * ⟨a₂, ha₂⟩ = ⟨a₂, ha₂⟩ * ⟨a₁, ha₁⟩ :=
      hA.1 ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
    exact congr_arg f (congr_arg Subtype.val hcomm)
  · rintro ⟨_, a, ha, rfl⟩
    apply Subtype.ext
    change (f a) ^ p = 1
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
  change ((x : G) ^ p) = 1
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
  change (⟨(z' : G), hz_in_U⟩ : ↥(OddOrder.Isaacs.Ch01.opCore p G)) ∈
      Subgroup.center (OddOrder.Isaacs.Ch01.opCore p G)
  rw [Subgroup.mem_center_iff]
  intro u
  apply Subtype.ext
  change ((u : G) * (z' : G)) = ((z' : G) * (u : G))
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


end OddOrder.Isaacs.Ch07
