/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_FurtherResults

/-!
# BG Appendix E, Theorem E.3: the regular-operator eigenvalue count

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 159--161 — the `(E.9)`--`(E.12)` part of Step 2 and
the conclusion `|S| ≤ p^q` of Theorem E.3(c).

This is a sibling leaf of `OddOrder/BG/AppE_FurtherResults.lean`, which carries `(E.1)`
through `(E.9)`.  The split is deliberate: that file reached the repo's 2000-line hard limit
(issue 0134), so further Appendix E work lands here instead of growing it.

## BG's elision, and the route taken

BG picks `w ∈ H₀ − H₁`, sets `wᵢ = [wᵢ₋₁, v]`, and later writes *"So `⟨w̄ᵢ⟩ = H̄ᵢ`"*.  That
silently requires `wᵢ ∉ Hᵢ₊₁`, for which BG gives no argument.

The route here is to observe that `x ↦ ⁅v, x⁆` is a **homomorphism modulo the next chain
term** (`commutator_mul_mem_chain`), so `{x ∈ Hᵢ | ⁅v,x⁆ ∈ Hᵢ₊₂}` is the kernel of a map
`Hᵢ → Hᵢ₊₁/Hᵢ₊₂`.  It contains `Hᵢ₊₁`, and cannot be all of `Hᵢ` (that would collapse
`Hᵢ₊₁ ≤ Hᵢ₊₂`), so by `|Hᵢ : Hᵢ₊₁| = p` it *is* `Hᵢ₊₁` — giving
`⁅v, x⁆ ∈ Hᵢ₊₂ ↔ x ∈ Hᵢ₊₁` and hence `wᵢ ∉ Hᵢ₊₁` by induction from `w ∉ H₁`.

⚠ This supersedes the bijection/fibre argument recorded earlier in issue 3021, which routed
through the tightness of the counting; the kernel argument needs no counting at all.  (The
sharpened `Ch1.S05.index_centralizer_le_card_of_commutator_mem` remains a genuine
improvement to that lemma, but is not needed here.)
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory
open scoped commutatorElement

/-! ### `x ↦ ⁅v, x⁆` is multiplicative modulo the next chain term -/

/-- **The multiplicativity behind (E.12)**: for `y ∈ Hᵢ`,
`(⁅v,x⁆ * ⁅v,y⁆)⁻¹ * ⁅v, x*y⁆ ∈ Hᵢ₊₂`.

That is, `x ↦ ⁅v, x⁆` becomes a homomorphism `Hᵢ → Hᵢ₊₁/Hᵢ₊₂` after passing to the
quotient.  The computation is the standard expansion
`⁅v, xy⁆ = ⁅v,x⁆ · (x ⁅v,y⁆ x⁻¹)`, together with
`x ⁅v,y⁆ x⁻¹ ⁅v,y⁆⁻¹ = ⁅x, ⁅v,y⁆⁆ ∈ ⁅S, Hᵢ₊₁⁆ = Hᵢ₊₂`.

⚠ Only `y ∈ Hᵢ` is needed — `v` and `x` are unconstrained, because the chain brackets
against all of `S`. -/
theorem commutator_mul_mem_chain {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {i : ℕ} {v x y : G}
    (hy : y ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i) :
    (⁅v, x⁆ * ⁅v, y⁆)⁻¹ * ⁅v, x * y⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  -- `⁅v,y⁆ ∈ Hᵢ₊₁`
  have hvy : ⁅v, y⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hy
  -- `c := ⁅x, ⁅v,y⁆⁆ ∈ Hᵢ₊₂`
  have hc : ⁅x, ⁅v, y⁆⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hvy
  -- the identity: the difference is a conjugate of `c`
  have hrw : (⁅v, x⁆ * ⁅v, y⁆)⁻¹ * ⁅v, x * y⁆ = ⁅v, y⁆⁻¹ * ⁅x, ⁅v, y⁆⁆ * ⁅v, y⁆ := by
    simp only [commutatorElement_def]
    group
  rw [hrw]
  exact Subgroup.Normal.conj_mem' inferInstance _ hc _

/-- **The homomorphism behind (E.12)**: `x ↦ ⁅v, x⁆ mod Hᵢ₊₂`, as a map `Hᵢ →* G/Hᵢ₊₂`.

Multiplicativity is `commutator_mul_mem_chain`.  Taking the *ambient* quotient `G/Hᵢ₊₂` as
codomain (rather than `Hᵢ₊₁/Hᵢ₊₂`) keeps the construction light — the image automatically
lands in the image of `Hᵢ₊₁`, but nothing here needs to say so.

Its kernel is `{x ∈ Hᵢ | ⁅v,x⁆ ∈ Hᵢ₊₂}`, the set BG needs to identify with `Hᵢ₊₁`. -/
def chainStepHom {G : Type*} [Group G] (T : Subgroup G) [T.Characteristic] (v : G) (i : ℕ) :
    ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i) →*
      (G ⧸ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2)) where
  toFun x := QuotientGroup.mk ⁅v, (x : G)⁆
  map_one' := by simp; rfl
  map_mul' x y := by
    rw [← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.coe_mul]
    have h := Subgroup.inv_mem _ (commutator_mul_mem_chain (v := v) (x := (x : G)) y.2)
    simpa [mul_inv_rev] using h

@[simp]
theorem chainStepHom_apply {G : Type*} [Group G] (T : Subgroup G) [T.Characteristic] (v : G)
    (i : ℕ) (x : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i)) :
    chainStepHom T v i x = QuotientGroup.mk ⁅v, (x : G)⁆ := rfl

/-- `Hᵢ₊₁` lies in the kernel: `⁅v, x⁆ ∈ ⁅S, Hᵢ₊₁⁆ = Hᵢ₊₂` already for `x ∈ Hᵢ₊₁`.

This is the easy half of BG's identification; the hard half is that the kernel is no
*bigger* than `Hᵢ₊₁`, which follows because it is a proper subgroup of `Hᵢ` and
`|Hᵢ : Hᵢ₊₁| = p` is prime. -/
theorem chainStepHom_ker_ge {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {v : G} {i : ℕ}
    {x : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i)}
    (hx : (x : G) ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1)) :
    chainStepHom T v i x = 1 := by
  rw [chainStepHom_apply, QuotientGroup.eq_one_iff,
    OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hx

/-- If `⁅v, x⁆ ∈ Hᵢ₊₂` then so is `⁅vᵏ, x⁆`.

In `G/Hᵢ₊₂` the element `⁅v, x⁆` becomes trivial, hence central, so BG Lemma 4.2(a)
(`Ch1.S04.commutatorElement_pow_left_of_central`) gives `⁅vᵏ, x⁆ ≡ ⁅v,x⁆ᵏ = 1`.

This is what upgrades "the kernel contains `x` for the single element `v`" to "… for the
whole of `R₀ = ⟨v⟩`", which is what BG's `Hᵢ₊₁ = ⁅R₀, Hᵢ⁆` needs.  ⚠ No hypothesis on `x` is
required — centrality comes from `⁅v,x⁆` being trivial in the quotient, not from
`chain_map_le_center`. -/
theorem commutator_pow_mem_of_commutator_mem {G : Type*} [Group G] {T : Subgroup G}
    [T.Characteristic] {i : ℕ} {v x : G}
    (h : ⁅v, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2)) (k : ℕ) :
    ⁅v ^ k, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  set N := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) with hN
  have h1 : (QuotientGroup.mk' N) ⁅v, x⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr h
  have h2 : ⁅(QuotientGroup.mk' N) v, (QuotientGroup.mk' N) x⁆ = 1 := by
    rw [← map_commutatorElement]; exact h1
  have hcent : ⁅(QuotientGroup.mk' N) v, (QuotientGroup.mk' N) x⁆ ∈
      Subgroup.center (G ⧸ N) := by rw [h2]; exact Subgroup.one_mem _
  have h3 := OddOrder.BG.Ch1.S04.commutatorElement_pow_left_of_central hcent k
  rw [h2, one_pow] at h3
  have h4 : (QuotientGroup.mk' N) ⁅v ^ k, x⁆ = 1 := by
    rw [map_commutatorElement, map_pow]; exact h3
  exact (QuotientGroup.eq_one_iff _).mp h4

/-- If `⁅v, x⁆ ∈ Hᵢ₊₂` for **every** `x ∈ Hᵢ` — i.e. the kernel of `chainStepHom` is all of
`Hᵢ` — then `⁅⟨v⟩, Hᵢ⁆ ≤ Hᵢ₊₂`.

`⁅⟨v⟩, Hᵢ⁆` is generated by brackets `⁅vᵏ, x⁆`, and
`commutator_pow_mem_of_commutator_mem` lifts the hypothesis from `v` to each `vᵏ`.
Finiteness lets the integer exponents of `zpowers` be taken natural.

Combined with BG's `Hᵢ₊₁ = ⁅R₀, Hᵢ⁆` (`commutator_R₀_eq_commutator_top`), this says a full
kernel would force `Hᵢ₊₁ ≤ Hᵢ₊₂` — impossible while the chain is still descending.  That is
the *hard* half of BG's unargued `⟨w̄ᵢ⟩ = H̄ᵢ`. -/
theorem commutator_zpowers_le_of_forall {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    [T.Characteristic] {i : ℕ} {v : G}
    (h : ∀ x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i,
      ⁅v, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2)) :
    ⁅Subgroup.zpowers v, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i⁆ ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff a v).mp (mem_powers_iff_mem_zpowers.mpr ha)
  exact commutator_pow_mem_of_commutator_mem (h b hb) k

/-- A subgroup containing one of **prime** index is either that subgroup or the whole group.

`H.relIndex K * K.index = H.index = p` leaves only `(1, p)` and `(p, 1)`: the first gives
`K ≤ H` (hence `K = H`), the second `K = ⊤`.

This is the lattice step that pins `chainStepHom`'s kernel: it contains `Hᵢ₊₁`, which has
prime index `p` in `Hᵢ`, and it is not everything — so it *is* `Hᵢ₊₁`. -/
theorem eq_or_top_of_index_prime {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    {p : ℕ} (hp : p.Prime) (hidx : H.index = p) : K = H ∨ K = ⊤ := by
  have hmul : H.relIndex K * K.index = H.index := Subgroup.relIndex_mul_index hHK
  rw [hidx] at hmul
  have hdvd : K.index ∣ p := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact Or.inr (Subgroup.index_eq_one.mp h1)
  · refine Or.inl (le_antisymm ?_ hHK)
    refine Subgroup.relIndex_eq_one.mp ?_
    rw [hp'] at hmul
    have h1 : H.relIndex K * p = 1 * p := by rw [one_mul]; exact hmul
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1

/-! ### The hard half of BG's `⟨w̄ᵢ⟩ = H̄ᵢ`, at setup level -/

/-- **BG Theorem E.3(b), Step 2**: for a generator `v` of `R₀`, some `x ∈ Hᵢ` has
`⁅v, x⁆ ∉ Hᵢ₊₂`.

Equivalently: the kernel of `chainStepHom` is a *proper* subgroup of `Hᵢ`.  If it were all
of `Hᵢ`, then `commutator_zpowers_le_of_forall` would give `⁅R₀, Hᵢ⁆ ≤ Hᵢ₊₂`, and BG's
identification `⁅R₀, Hᵢ⁆ = ⁅S, Hᵢ⁆ = Hᵢ₊₁` (`commutator_R₀_eq_commutator_top`) would then
collapse `Hᵢ₊₁ ≤ Hᵢ₊₂` — impossible while the chain is still descending.

Together with `chainStepHom_ker_ge` and `|Hᵢ : Hᵢ₊₁| = p` prime, this pins the kernel to
exactly `Hᵢ₊₁`, which is what BG asserts in five words. -/
theorem RegularOperatorSetup.exists_commutator_not_mem {R B : Type*} [Group R] [Group B]
    [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hR₀S : hyp.R₀ ≤ S) (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥)
    (hlt : ¬ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 1) ≤
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 2))
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S) :
    ∃ x ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
      ⁅v, x⁆ ∉ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 2) := by
  by_contra hcon
  push Not at hcon
  have hHT := iterCommutator_le_start
    (T := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) i
  have h1 := commutator_zpowers_le_of_forall
    (T := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (v := v) hcon
  rw [hv, hyp.commutator_R₀_eq_commutator_top hR₀S hexp hS hne hHT] at h1
  refine hlt ?_
  rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
  exact h1

/-- **BG's `⟨w̄ᵢ⟩ = H̄ᵢ`, in usable form**: for `x ∈ Hᵢ`,
`⁅v, x⁆ ∈ Hᵢ₊₂ ↔ x ∈ Hᵢ₊₁`.

The three inputs meet here: the kernel of `chainStepHom` contains `Hᵢ₊₁`
(`chainStepHom_ker_ge`), is not all of `Hᵢ` (`exists_commutator_not_mem`), and
`|Hᵢ : Hᵢ₊₁| = p` is prime — so `eq_or_top_of_index_prime` pins it to exactly `Hᵢ₊₁`.

This is the statement BG replaces with five words, and it is what propagates
`w ∉ H₁` to `wᵢ ∉ Hᵢ₊₁` along the sequence `wᵢ = ⁅wᵢ₋₁, v⁆`. -/
theorem RegularOperatorSetup.commutator_mem_iff_mem {R B : Type*} [Group R] [Group B]
    [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hR₀S : hyp.R₀ ≤ S) (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥)
    (hlt : ¬ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 1) ≤
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 2))
    (hidx : ((OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (i + 1)).subgroupOf
        (OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          i)).index = p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S) {x : ↥S}
    (hxi : x ∈ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i) :
    ⁅v, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 2) ↔
      x ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 1) := by
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  constructor
  · intro hmem
    have hxK : (⟨x, hxi⟩ : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)) ∈
        (chainStepHom T v i).ker := by
      rw [MonoidHom.mem_ker, chainStepHom_apply]
      exact (QuotientGroup.eq_one_iff _).mpr hmem
    have hge : (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1)).subgroupOf
        (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) ≤
        (chainStepHom T v i).ker := by
      intro y hy
      rw [MonoidHom.mem_ker]
      exact chainStepHom_ker_ge (Subgroup.mem_subgroupOf.mp hy)
    rcases eq_or_top_of_index_prime hge hyp.p_prime hidx with h | h
    · rw [h] at hxK
      exact Subgroup.mem_subgroupOf.mp hxK
    · exfalso
      obtain ⟨y, hy, hyn⟩ := hyp.exists_commutator_not_mem hR₀S hexp hS hne hlt hv
      refine hyn ?_
      have hyK : (⟨y, hy⟩ : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)) ∈
          (chainStepHom T v i).ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, chainStepHom_apply] at hyK
      exact (QuotientGroup.eq_one_iff _).mp hyK
  · intro hmem
    have h := chainStepHom_ker_ge (T := T) (v := v) (x := ⟨x, hxi⟩) hmem
    rw [chainStepHom_apply] at h
    exact (QuotientGroup.eq_one_iff _).mp h

/-- **The inductive step for `wᵢ ∉ Hᵢ₊₁`**: if `wᵢ ∉ Hᵢ₊₁` then `wᵢ₊₁ ∉ Hᵢ₊₂`.

`wᵢ₊₁ = ⁅wᵢ, v⁆ = ⁅v, wᵢ⁆⁻¹`, and `commutator_mem_iff_mem` says `⁅v, wᵢ⁆ ∈ Hᵢ₊₂` exactly
when `wᵢ ∈ Hᵢ₊₁`.  Chained from `w ∉ H₁`, this is BG's `⟨w̄ᵢ⟩ = H̄ᵢ` for every `i`. -/
theorem RegularOperatorSetup.commutatorIterate_not_mem_succ {R B : Type*} [Group R] [Group B]
    [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hR₀S : hyp.R₀ ≤ S) (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥)
    (hlt : ¬ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 1) ≤
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 2))
    (hidx : ((OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (i + 1)).subgroupOf
        (OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          i)).index = p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S) {w : ↥S}
    (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hwi : commutatorIterate w v i ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1)) :
    commutatorIterate w v (i + 1) ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
      (i + 2) := by
  have hmem := commutatorIterate_mem_chain
    (T := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (v := v) hw i
  intro hcon
  refine hwi ((hyp.commutator_mem_iff_mem hR₀S hexp hS hne hlt hidx hv hmem).mp ?_)
  rw [← commutatorElement_inv]
  exact Subgroup.inv_mem _ hcon

/-- **(E.12) bilinearity in the quotient**: for `x ∈ Hᵢ`,
`⁅vᵏ, x⁆ ≡ ⁅v, x⁆ᵏ (mod Hᵢ₊₂)`.

This is the *equality* form that BG's `[wᵢ₋₁^{rᵢ₋₁} u, vʳ] = wᵢ^{rᵢ₋₁ r}` needs, as opposed
to the membership form `commutator_pow_mem_of_commutator_mem`.  It is the first consumer of
`chain_map_le_center`: `⁅v,x⁆ ∈ Hᵢ₊₁` becomes **central** in `G/Hᵢ₊₂`, so BG Lemma 4.2(a)
applies there. -/
theorem commutator_pow_left_congr {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {i : ℕ} {v x : G}
    (hx : x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i) (k : ℕ) :
    (⁅v, x⁆ ^ k)⁻¹ * ⁅v ^ k, x⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  set N := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) with hN
  have hvx : ⁅v, x⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hx
  have hcent : ⁅(QuotientGroup.mk' N) v, (QuotientGroup.mk' N) x⁆ ∈
      Subgroup.center (G ⧸ N) := by
    rw [← map_commutatorElement]
    exact chain_map_le_center T (i + 1) (Subgroup.mem_map.mpr ⟨⁅v, x⁆, hvx, rfl⟩)
  have h3 := OddOrder.BG.Ch1.S04.commutatorElement_pow_left_of_central hcent k
  refine QuotientGroup.eq.mp ?_
  show (QuotientGroup.mk' N) (⁅v, x⁆ ^ k) = (QuotientGroup.mk' N) ⁅v ^ k, x⁆
  rw [map_pow, map_commutatorElement, map_commutatorElement, map_pow]
  exact h3.symm

/-- **The `u ∈ Hᵢ` remainder is invisible mod `Hᵢ₊₁`**: `⁅v, x·u⁆ ≡ ⁅v, x⁆`.

BG writes `wᵢ₋₁ᵃ = wᵢ₋₁^{rᵢ₋₁} u` for some `u ∈ Hᵢ` and then simply computes with
`wᵢ₋₁^{rᵢ₋₁}`; this is what licenses dropping the remainder.  Both factors of
`⁅v,x⁆⁻¹ ⁅v,x·u⁆ = ⁅v,u⁆ · ((⁅v,x⁆⁅v,u⁆)⁻¹ ⁅v,x·u⁆)` lie in `Hᵢ₊₁` — the first because
`u ∈ Hᵢ`, the second by `commutator_mul_mem_chain` (which even lands in `Hᵢ₊₂`). -/
theorem commutator_mul_congr {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {i : ℕ} {v x u : G}
    (hu : u ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i) :
    (⁅v, x⁆)⁻¹ * ⁅v, x * u⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
  have hvu : ⁅v, u⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top v) hu
  have hrest : (⁅v, x⁆ * ⁅v, u⁆)⁻¹ * ⁅v, x * u⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) :=
    iterCommutator_antitone (i + 1) (commutator_mul_mem_chain hu)
  have hrw : (⁅v, x⁆)⁻¹ * ⁅v, x * u⁆ =
      ⁅v, u⁆ * ((⁅v, x⁆ * ⁅v, u⁆)⁻¹ * ⁅v, x * u⁆) := by group
  rw [hrw]
  exact Subgroup.mul_mem _ hvu hrest

end OddOrder.BG.AppE
