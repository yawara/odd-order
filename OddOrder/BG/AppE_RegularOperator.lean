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

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03
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
  change (QuotientGroup.mk' N) (⁅v, x⁆ ^ k) = (QuotientGroup.mk' N) ⁅v ^ k, x⁆
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

/-! ### (E.12): the eigenvalue recursion `rᵢ ≡ rᵢ₋₁ r (mod p)`

BG's chain `T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1` carries, on each section `Hᵢ/Hᵢ₊₁` (which has order
`p`), an eigenvalue `rᵢ` for the action of `a ∈ A`.  BG relates consecutive eigenvalues by
the single computation

`wᵢ^{rᵢ} ≡ wᵢᵃ = ⁅wᵢ₋₁, v⁆ᵃ = ⁅wᵢ₋₁^{rᵢ₋₁} u, vʳ⁆ ≡ ⁅wᵢ₋₁, v⁆^{rᵢ₋₁ r} = wᵢ^{rᵢ₋₁ r}`,

all `mod Hᵢ₊₁`, and then cancels `wᵢ` — which is legitimate exactly because `w̄ᵢ` generates
the order-`p` section, i.e. because `wᵢ ∉ Hᵢ₊₁` (the fact recovered above). -/

/-- A central factor in the left slot of a commutator drops out: `⁅a * c, b⁆ = ⁅a, b⁆`.

This is what lets BG's remainder `u` disappear once one passes to `G/Hᵢ₊₂`, where `ū` is
central by `chain_map_le_center`. -/
theorem commutatorElement_mul_central_left {K : Type*} [Group K] {a b c : K}
    (hc : c ∈ Subgroup.center K) : ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have hcb : c * b = b * c := (Subgroup.mem_center_iff.mp hc b).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * b * (a * c)⁻¹ * b⁻¹
      = a * (c * b) * (a * c)⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * (a * c)⁻¹ * b⁻¹ := by rw [hcb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

/-- **BG Lemma 4.2(a), both slots, integer exponents**: if `⁅x, y⁆` is central then
`⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n)` for `m n : ℤ`.

The natural-exponent form is `commutatorElement_pow_pow_of_central`; `(E.12)` needs this
one, because the eigenvalues `rᵢ` are integers (they are exponents of an automorphism of a
group of order `p`, so only their class mod `p` matters, but they arrive as `ℤ`). -/
theorem commutatorElement_zpow_zpow_of_central {K : Type*} [Group K] {x y : K}
    (hz : ⁅x, y⁆ ∈ Subgroup.center K) (m n : ℤ) :
    ⁅x ^ m, y ^ n⁆ = ⁅x, y⁆ ^ (m * n) := by
  have h1 : ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m :=
    OddOrder.BG.Ch1.S04.commutatorElement_zpow_left_of_central hz m
  have hc : ⁅x ^ m, y⁆ ∈ Subgroup.center K := by
    rw [h1]; exact Subgroup.zpow_mem _ hz m
  rw [OddOrder.BG.Ch1.S04.commutatorElement_zpow_right_of_central hc n, h1, ← zpow_mul]

/-- **(E.12) in one step**: for `x ∈ Hᵢ` and `u ∈ Hᵢ₊₁`,
`⁅x^m · u, v^k⁆ ≡ ⁅x, v⁆^(m·k) (mod Hᵢ₊₂)`.

This is BG's one-line `[wᵢ₋₁^{rᵢ₋₁} u, vʳ] = wᵢ^{rᵢ₋₁ r}`.  Two facts make it work in
`G/Hᵢ₊₂`, and both come from `chain_map_le_center`: the remainder `u ∈ Hᵢ₊₁` becomes
**central**, so it drops out of the left slot (`commutatorElement_mul_central_left`); and
`⁅x, v⁆ ∈ Hᵢ₊₁` is central, so Lemma 4.2(a) applies in both slots at once.

⚠ `v` is unconstrained — the chain brackets against all of `S`, so no hypothesis relating
`v` to `R₀` is needed here.  That enters only when the eigenvalue `r` of `v` is produced. -/
theorem commutator_zpow_mul_congr {G : Type*} [Group G] {T : Subgroup G} [T.Characteristic]
    {i : ℕ} {x u v : G}
    (hx : x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i)
    (hu : u ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1)) (m k : ℤ) :
    (⁅x, v⁆ ^ (m * k))⁻¹ * ⁅x ^ m * u, v ^ k⁆ ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) := by
  set N := OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 2) with hN
  have hucent : (QuotientGroup.mk' N) u ∈ Subgroup.center (G ⧸ N) :=
    chain_map_le_center T (i + 1) (Subgroup.mem_map.mpr ⟨u, hu, rfl⟩)
  have hxv : ⁅x, v⁆ ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) (i + 1) := by
    rw [OddOrder.Isaacs.Ch04.iterCommutator_succ]
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top v)
  have hcent : ⁅(QuotientGroup.mk' N) x, (QuotientGroup.mk' N) v⁆ ∈ Subgroup.center (G ⧸ N) := by
    rw [← map_commutatorElement]
    exact chain_map_le_center T (i + 1) (Subgroup.mem_map.mpr ⟨⁅x, v⁆, hxv, rfl⟩)
  refine QuotientGroup.eq.mp ?_
  change (QuotientGroup.mk' N) (⁅x, v⁆ ^ (m * k)) = (QuotientGroup.mk' N) ⁅x ^ m * u, v ^ k⁆
  rw [map_zpow, map_commutatorElement, map_commutatorElement, map_mul, map_zpow, map_zpow,
    commutatorElement_mul_central_left hucent]
  exact (commutatorElement_zpow_zpow_of_central hcent m k).symm

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **(E.9) as a congruence between elements**: `yᵃ ≡ y^{rᵢ} (mod Hᵢ₊₁)` for every `y ∈ Hᵢ`.

`exists_zpow_eq_on_chain_section` produces the eigenvalue inside the quotient `Hᵢ/Hᵢ₊₁`; BG
writes it as `wᵢᵃ ≡ wᵢ^{rᵢ} (mod Hᵢ₊₁)`.  That is the form `(E.12)` consumes, because there
the remainder `u = (y^{rᵢ})⁻¹ yᵃ ∈ Hᵢ₊₁` is carried explicitly into a commutator rather than
being discarded. -/
theorem RegularOperatorSetup.exists_zpow_eq_mod_chain {R B : Type*} [Group R] [Group B]
    [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hR₀S : hyp.R₀ ≤ S) (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥)
    {a : B} (ha : a ∈ hyp.A) :
    ∃ r : ℤ, ((r : ZMod p) ^ q = 1) ∧
      ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
        (y ^ r)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈
          OddOrder.Isaacs.Ch04.iterCommutator
            (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
            (i + 1) := by
  obtain ⟨r, hr, hrq⟩ := hyp.exists_zpow_eq_on_chain_section hR₀S hexp hS hSinv hne ha
  refine ⟨r, hrq, fun y hy => ?_⟩
  have h := hr (QuotientGroup.mk' _ (⟨y, hy⟩ : ↥(OddOrder.Isaacs.Ch04.iterCommutator
    (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i)))
  rw [quotientMulAutHom_apply_mk', ← map_zpow] at h
  have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h.symm)
  simpa using h2

/-- **BG Theorem E.3(b), Step 2, (E.12)**: `rᵢ₊₁ ≡ rᵢ · r (mod p)`.

BG's computation, in full:
`wᵢ₊₁^{rᵢ₊₁} ≡ wᵢ₊₁ᵃ = ⁅wᵢ, v⁆ᵃ = ⁅wᵢᵃ, vᵃ⁆ = ⁅wᵢ^{rᵢ} u, vʳ⁆ ≡ ⁅wᵢ, v⁆^{rᵢ r} = wᵢ₊₁^{rᵢ r}`,
all modulo `Hᵢ₊₂`.  Cancelling `wᵢ₊₁` is legitimate because `w̄ᵢ₊₁` generates the order-`p`
section `Hᵢ₊₁/Hᵢ₊₂` — BG's five-word *"So `⟨w̄ᵢ⟩ = H̄ᵢ`"*, supplied here as the hypothesis
`wᵢ₊₁ ∉ Hᵢ₊₂` (which `commutatorIterate_not_mem_succ` propagates from `w ∉ H₁`).

The eigenvalues enter as hypotheses in the shape `exists_zpow_eq_mod_chain` and
`exists_zpow_eq_act_of_mem_A` deliver them, so that the caller chooses `a` once and reuses
the same `r` down the whole chain — which is what makes `rᵢ ≡ r₀ rⁱ` an induction.

⚠ The chain's liveness `Hᵢ₊₁ ≠ 1` is *not* needed here: the index hypothesis `hidx` and the
non-membership `hwi` already carry everything the computation uses. -/
theorem RegularOperatorSetup.eigenvalue_step {R B : Type*} [Group R] [Group B] [Finite R]
    {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) {i : ℕ}
    (hidx : ((OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (i + 2)).subgroupOf
        (OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (i + 1))).index = p)
    {a : B} (ha : a ∈ hyp.A) {v w : ↥S}
    (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hwi : commutatorIterate w v (i + 1) ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 2))
    {r r₀ r₁ : ℤ} (hr : (hSinv.restrict ⟨a, ha⟩) v = v ^ r)
    (hr₀ : ((commutatorIterate w v i) ^ r₀)⁻¹ *
        (hSinv.restrict ⟨a, ha⟩) (commutatorIterate w v i) ∈
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1))
    (hr₁ : ((commutatorIterate w v (i + 1)) ^ r₁)⁻¹ *
        (hSinv.restrict ⟨a, ha⟩) (commutatorIterate w v (i + 1)) ∈
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 2)) :
    (r₁ : ZMod p) = (r₀ : ZMod p) * (r : ZMod p) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  set σ := hSinv.restrict (⟨a, ha⟩ : ↥hyp.A) with hσ
  set x := commutatorIterate w v i with hx
  set y := commutatorIterate w v (i + 1) with hy
  set u := (x ^ r₀)⁻¹ * σ x with hu
  -- `wᵢ ∈ Hᵢ` and `wᵢ₊₁ = ⁅wᵢ, v⁆ ∈ Hᵢ₊₁`
  have hxmem : x ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i :=
    commutatorIterate_mem_chain hw i
  have hymem : y ∈ OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1) :=
    commutatorIterate_mem_chain hw (i + 1)
  -- `wᵢ₊₁ᵃ = ⁅wᵢ^{rᵢ} u, vʳ⁆`
  have hσy : σ y = ⁅x ^ r₀ * u, v ^ r⁆ := by
    have hxu : x ^ r₀ * u = σ x := by rw [hu]; group
    rw [hy, commutatorIterate_succ, ← hx, hxu, ← hr]
    exact map_commutatorElement σ x v
  -- BG's `⁅wᵢ^{rᵢ} u, vʳ⁆ ≡ wᵢ₊₁^{rᵢ r} (mod Hᵢ₊₂)`
  have hbil : (y ^ (r₀ * r))⁻¹ * σ y ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 2) := by
    rw [hσy, hy, commutatorIterate_succ, ← hx]
    exact commutator_zpow_mul_congr hxmem hr₀ r₀ r
  -- so `wᵢ₊₁^{rᵢ₊₁} ≡ wᵢ₊₁^{rᵢ r}`
  have hcomb : (y ^ r₁)⁻¹ * y ^ (r₀ * r) ∈
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 2) := by
    have h := Subgroup.mul_mem _ hr₁ (Subgroup.inv_mem _ hbil)
    have hrw : ((y ^ r₁)⁻¹ * σ y) * ((y ^ (r₀ * r))⁻¹ * σ y)⁻¹ =
        (y ^ r₁)⁻¹ * y ^ (r₀ * r) := by group
    rwa [hrw] at h
  -- pass to the order-`p` section `Hᵢ₊₁/Hᵢ₊₂` and cancel `w̄ᵢ₊₁`
  set N := (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 2)).subgroupOf
    (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1)) with hN
  set z := QuotientGroup.mk' N (⟨y, hymem⟩ :
    ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1))) with hz
  have hzne : z ≠ 1 := by
    rw [hz]
    intro hcon
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hN, Subgroup.mem_subgroupOf] at hcon
    exact hwi hcon
  have hzord : orderOf z = p := by
    have hdvd : orderOf z ∣ p := by
      have h := orderOf_dvd_natCard z
      rwa [← Subgroup.index_eq_card, hidx] at h
    rcases (Nat.dvd_prime hyp.p_prime).mp hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hzne
    · exact hp'
  have hzpow : z ^ r₁ = z ^ (r₀ * r) := by
    rw [hz, ← map_zpow, ← map_zpow]
    refine QuotientGroup.eq.mpr ?_
    rw [hN, Subgroup.mem_subgroupOf]
    push_cast
    exact hcomb
  have := OddOrder.BG.Ch1.S04.zmod_eq_of_zpow_eq_of_order_prime hzord hzpow
  push_cast at this
  exact this

/-! ### How far down the chain BG's bookkeeping runs

BG's sequences are indexed `i = 0, 1, …, n − 1`, where `n` is the first index with
`Hₙ = 1`.  In Lean the cleanest single hypothesis for "index `i` is still in range" is
`Hᵢ ≠ ⊥`: the chain descends **strictly** while it is alive (each step has index `p`), so
`Hᵢ ≠ ⊥` both bounds `i` and supplies the strictness `Hᵢ₊₁ < Hᵢ` that the `(E.12)`
machinery consumes. -/

/-- The chain is antitone across arbitrary index gaps, not just single steps. -/
theorem iterCommutator_le_of_le {G : Type*} [Group G] {T : Subgroup G} [T.Normal] {i j : ℕ}
    (hij : j ≤ i) :
    OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i ≤
      OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) j := by
  induction i with
  | zero => rw [Nat.le_zero.mp hij]
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · rw [h]
      · exact (iterCommutator_antitone n).trans (ih (Nat.lt_succ_iff.mp h))

/-- If the chain is still alive at `i`, it is alive at every earlier index. -/
theorem iterCommutator_ne_bot_of_le {G : Type*} [Group G] {T : Subgroup G} [T.Normal] {i j : ℕ}
    (hij : j ≤ i)
    (hne : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) i ≠ ⊥) :
    OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup G) j ≠ ⊥ := fun h =>
  hne (le_bot_iff.mp ((iterCommutator_le_of_le hij).trans (le_of_eq h)))

/-- **The chain descends strictly while alive**: `Hᵢ₊₁ < Hᵢ` whenever `Hᵢ ≠ 1`.

Immediate from the index-`p` step `|Hᵢ| = p·|Hᵢ₊₁|` of `(E.6)`.  This is the form the
`(E.12)` machinery consumes — both as `¬ Hᵢ₊₁ ≤ Hᵢ₊₂` and as the nontriviality of the
section that `quotient_action_ne_one` needs. -/
theorem RegularOperatorSetup.iterCommutator_lt {R B : Type*} [Group R] [Group B] [Finite R]
    {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥) :
    OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 1) <
      OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i := by
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  refine lt_of_le_of_ne (iterCommutator_antitone i) fun heq => ?_
  have hcard := hyp.card_iterCommutator_eq hR₀S hexp hS (le_refl T) hne
  rw [heq] at hcard
  have hpos : 0 < Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) :=
    Nat.card_pos
  have hone : Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) * 1 =
      Nat.card ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) * p := by
    rw [mul_one, mul_comm]; exact hcard
  have h2 := hyp.p_prime.two_le
  have := Nat.eq_of_mul_eq_mul_left hpos hone
  omega

/-- **BG's `wᵢ ∉ Hᵢ₊₁`, for the whole range `i = 0, …, n − 1`**.

The induction whose step is `commutatorIterate_not_mem_succ`, started from BG's choice
`w ∈ H₀ − H₁`.  This is what makes `⟨w̄ᵢ⟩ = H̄ᵢ` true at every level, and hence what
licenses cancelling `wᵢ` in `(E.12)`. -/
theorem RegularOperatorSetup.commutatorIterate_not_mem {R B : Type*} [Group R] [Group B]
    [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hR₀S : hyp.R₀ ≤ S) (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S)
    {w : ↥S} (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hw1 : w ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1) :
    ∀ i : ℕ, OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥ →
      commutatorIterate w v i ∉ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1)
  | 0, _ => hw1
  | i + 1, hne => by
      have hprev := iterCommutator_ne_bot_of_le (Nat.le_succ i) hne
      exact hyp.commutatorIterate_not_mem_succ hR₀S hexp hS hprev
        (not_le_of_gt (hyp.iterCommutator_lt hR₀S hexp hS hne))
        (hyp.index_subgroupOf_chain hR₀S hexp hS hprev) hv hw
        (hyp.commutatorIterate_not_mem hR₀S hexp hS hv hw hw1 i hprev)

/-- **BG Theorem E.3(b), Step 2, (E.12)**: `rᵢ ≡ r₀ rⁱ (mod p)`.

BG: *"We now see by induction that, for `i = 0, 1, …, n − 1`, `rᵢ ≡ r₀ rⁱ (mod p)`."*  The
step is `eigenvalue_step`, the base is the choice of `r₀`.

The eigenvalue is carried in the shape `exists_zpow_eq_mod_chain` delivers — a statement
about **every** `y ∈ Hᵢ`, not just about `wᵢ`.  That is deliberate: `(E.10)` needs to
conclude that `A` centralizes the *whole* section `Hᵢ/Hᵢ₊₁`, which the single element `wᵢ`
would only give after re-deriving that `w̄ᵢ` generates it. -/
theorem RegularOperatorSetup.exists_eigenvalue_pow {R B : Type*} [Group R] [Group B]
    [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hR₀S : hyp.R₀ ≤ S) (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S)
    {a : B} (ha : a ∈ hyp.A) {v : ↥S} (hv : Subgroup.zpowers v = hyp.R₀.subgroupOf S)
    {w : ↥S} (hw : w ∈ Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S))
    (hw1 : w ∉ OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1)
    {r : ℤ} (hr : (hSinv.restrict ⟨a, ha⟩) v = v ^ r)
    {r₀ : ℤ} (hr₀ : ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 0,
      (y ^ r₀)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) 1) :
    ∀ i : ℕ, OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥ →
      ∃ s : ℤ, (s : ZMod p) = (r₀ : ZMod p) * (r : ZMod p) ^ i ∧
        ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
            (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
          (y ^ s)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈ OddOrder.Isaacs.Ch04.iterCommutator
            (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
            (i + 1) := by
  intro i
  induction i with
  | zero => exact fun _ => ⟨r₀, by simp, hr₀⟩
  | succ i ih =>
      intro hne
      have hprev := iterCommutator_ne_bot_of_le (Nat.le_succ i) hne
      obtain ⟨s, hs, hsmem⟩ := ih hprev
      obtain ⟨s', _, hs'mem⟩ := hyp.exists_zpow_eq_mod_chain hR₀S hexp hS hSinv hne ha
      refine ⟨s', ?_, hs'mem⟩
      have hstep := hyp.eigenvalue_step hSinv
        (hyp.index_subgroupOf_chain hR₀S hexp hS hne) ha hw
        (hyp.commutatorIterate_not_mem hR₀S hexp hS hv hw hw1 (i + 1) hne) hr
        (hsmem _ (commutatorIterate_mem_chain hw i))
        (hs'mem _ (commutatorIterate_mem_chain hw (i + 1)))
      rw [hstep, hs, pow_succ]
      ring

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom quotientMulAutHom_apply) in
/-- If the eigenvalue on the section `Hᵢ/Hᵢ₊₁` is `≡ 1 (mod p)`, the induced automorphism of
that section is the identity.

The section has order `p`, so `z^{s} = z` as soon as `p ∣ s − 1`; and `yᵃ ≡ y^{s}` for every
`y ∈ Hᵢ` is exactly the eigenvalue hypothesis.  This is the direction `(E.10)` needs: BG
argues that `rᵢ ≡ 1` would make `A` centralize `Hᵢ/Hᵢ₊₁`. -/
theorem RegularOperatorSetup.quotient_action_eq_one_of_eigenvalue_one {R B : Type*} [Group R]
    [Group B] [Finite R] {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R}
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) {i : ℕ}
    (hidx : ((OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          (i + 1)).subgroupOf
        (OddOrder.Isaacs.Ch04.iterCommutator
          (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
          i)).index = p)
    {a : B} (ha : a ∈ hyp.A) {s : ℤ}
    (hs : ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
      (y ^ s)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) (i + 1))
    (h1 : (s : ZMod p) = 1) :
    (quotientMulAutHom (hyp.isAInvariant_subgroupOf_chain hSinv i)) ⟨a, ha⟩ = 1 := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  set N := (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (i + 1)).subgroupOf
    (OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) with hN
  -- `p ∣ s − 1`
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ s - 1 := by
    have : ((s - 1 : ℤ) : ZMod p) = 0 := by push_cast [h1]; ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  refine MulEquiv.ext fun x => ?_
  rw [MulAut.one_apply]
  refine QuotientGroup.induction_on x fun y => ?_
  -- the section has order `p`, so `zˢ = z`
  have hcard : Nat.card (↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i) ⧸ N) = p := by
    rw [← Subgroup.index_eq_card]; exact hidx
  have hzp : ((y : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)) : _ ⧸ N) ^ (p : ℤ)
      = 1 := by
    have h := pow_card_eq_one' (G := ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)
      ⧸ N) (x := (y : _ ⧸ N))
    rw [hcard] at h
    rw [zpow_natCast]
    exact h
  have hzs : ((y : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)) : _ ⧸ N) ^ s =
      ((y : ↥(OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i)) : _ ⧸ N) := by
    have hsplit : s = 1 + (p : ℤ) * k := by omega
    rw [hsplit, zpow_add, zpow_one, zpow_mul, hzp, one_zpow, mul_one]
  -- the eigenvalue hypothesis, read in the section
  rw [quotientMulAutHom_apply]
  have hmem : (y ^ s)⁻¹ * ((hyp.isAInvariant_iterCommutator hSinv i).restrict ⟨a, ha⟩) y ∈ N := by
    rw [hN, Subgroup.mem_subgroupOf]
    simpa using hs _ y.2
  rw [((QuotientGroup.eq (s := N)).mpr hmem).symm, ← hzs]
  exact map_zpow (QuotientGroup.mk' N) y s

/-- **BG Theorem E.3(b), Step 2, (E.10)**, in congruence form: `rᵢ ≢ 1 (mod p)`.

BG: *"if `rᵢ ≡ 1 (mod p)` for some `i`, then `A` centralizes `Hᵢ/Hᵢ₊₁` by Proposition
1.5(d), … contrary to the regular action of `A` on `R`."*  The two halves are
`quotient_action_eq_one_of_eigenvalue_one` (the congruence trivialises the action) and
`quotient_action_ne_one` (regularity forbids that). -/
theorem RegularOperatorSetup.eigenvalue_ne_one {R B : Type*} [Group R] [Group B] [Finite R]
    {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) {i : ℕ}
    (hne : OddOrder.Isaacs.Ch04.iterCommutator
      (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥)
    {a : B} (ha : a ∈ hyp.A) (hane : a ≠ 1) {s : ℤ}
    (hs : ∀ y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i,
      (y ^ s)⁻¹ * (hSinv.restrict ⟨a, ha⟩) y ∈ OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S)
        (i + 1)) :
    (s : ZMod p) ≠ 1 := fun h1 =>
  hyp.quotient_action_ne_one hSinv (hyp.iterCommutator_lt hR₀S hexp hS hne) ha hane
    (hyp.quotient_action_eq_one_of_eigenvalue_one hSinv
      (hyp.index_subgroupOf_chain hR₀S hexp hS hne) ha hs h1)

/-! ### The closing count: `n ≤ q − 1` and `|S| ≤ p^q` -/

/-- **BG's `n`**: the chain `T = H₀ ⊃ H₁ ⊃ ⋯` reaches `1`, and `|T| = pⁿ` for the first
index `n` at which it does.

BG's `T = H₀ ⊃ H₁ ⊃ ⋯ ⊃ Hₙ = 1` with `|Hᵢ₋₁ : Hᵢ| = p`.  The chain terminates because `S`
is a `p`-group, hence nilpotent; `|T| = pⁿ` is `card_start_eq_pow_mul` at `n − 1` combined
with the final step `|Hₙ₋₁| = p·|Hₙ| = p`. -/
theorem RegularOperatorSetup.exists_chain_length {R B : Type*} [Group R] [Group B] [Finite R]
    {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p) :
    ∃ n : ℕ,
      (∀ i < n, OddOrder.Isaacs.Ch04.iterCommutator
        (Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) (⊤ : Subgroup ↥S) i ≠ ⊥) ∧
      Nat.card ↥(Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S)) = p ^ n := by
  classical
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  haveI : Group.IsNilpotent ↥S := (hyp.R_pGroup.to_subgroup S).isNilpotent
  have hex : ∃ m, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) m = ⊥ :=
    OddOrder.Isaacs.Ch04.iterCommutator_eq_bot_of_isNilpotent_ambient T (⊤ : Subgroup ↥S)
  set n := Nat.find hex with hn
  have hbot : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) n = ⊥ := Nat.find_spec hex
  have hlive : ∀ i < n, OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) i ≠ ⊥ :=
    fun i hi => Nat.find_min hex hi
  refine ⟨n, hlive, ?_⟩
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · have hTbot : T = ⊥ := by
      have h := hbot
      rw [h0, OddOrder.Isaacs.Ch04.iterCommutator_zero] at h
      exact h
    rw [hTbot, h0, Subgroup.card_bot, pow_zero]
  · have hmlive : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) (n - 1) ≠ ⊥ :=
      hlive (n - 1) (by omega)
    have h1 := hyp.card_start_eq_pow_mul hR₀S hexp hS (le_refl T) (n - 1) hmlive
    have h2 := hyp.card_iterCommutator_eq hR₀S hexp hS (le_refl T) hmlive
    rw [show n - 1 + 1 = n by omega, hbot, Subgroup.card_bot, mul_one] at h2
    rw [h1, h2, ← pow_succ]
    congr 1
    omega

/-- **BG Theorem E.3(b), Step 2, the closing count**, transported to `(ZMod p)ˣ`.

BG: *"the nonzero integers `(mod p)` form a cyclic group of order `p − 1` and `rᵠ ≡ 1`;
therefore by `(E.10)` and `(E.11)` there exists `j` with `1 ≤ j ≤ q − 1` and `rʲ ≡ r₀`;
by `(E.12)` none of `r₀, r₀r, …, r₀rⁿ⁻¹` is `≡ 1`; therefore `q − 1 ≥ j + n − 1 ≥ n`."*

`le_pred_of_forall_mul_pow_ne_one` is that argument for an abstract cyclic group; this
wrapper supplies the group — `(ZMod p)ˣ`, cyclic because `ZMod p` is a finite field — and
promotes the residues `r`, `r₀` to units (they are, since they satisfy `x^q = 1`). -/
theorem le_pred_of_forall_zmod_mul_pow_ne_one {p q n : ℕ} [Fact p.Prime] (hq : q.Prime)
    {r r₀ : ℤ} (hrq : (r : ZMod p) ^ q = 1) (hrne : (r : ZMod p) ≠ 1)
    (hr₀q : (r₀ : ZMod p) ^ q = 1)
    (hne : ∀ i < n, (r₀ : ZMod p) * (r : ZMod p) ^ i ≠ 1) : n ≤ q - 1 := by
  have hqpos : 0 < q := hq.pos
  have hsplit : q - 1 + 1 = q := Nat.succ_pred_eq_of_pos hqpos
  have hunit : ∀ x : ZMod p, x ^ q = 1 → IsUnit x := by
    intro x hx
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, zero_pow hqpos.ne'] at hx
    exact zero_ne_one hx
  set u : (ZMod p)ˣ := (hunit _ hrq).unit with hu
  set u₀ : (ZMod p)ˣ := (hunit _ hr₀q).unit with hu₀
  have huval : (u : ZMod p) = (r : ZMod p) := IsUnit.unit_spec _
  have hu₀val : (u₀ : ZMod p) = (r₀ : ZMod p) := IsUnit.unit_spec _
  refine le_pred_of_forall_mul_pow_ne_one hq (u := u) (u₀ := u₀) ?_ ?_ ?_ ?_
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val, huval, hrq, Units.val_one])
  · exact fun h => hrne (by rw [← huval, h, Units.val_one])
  · exact Units.ext (by rw [Units.val_pow_eq_pow_val, hu₀val, hr₀q, Units.val_one])
  · intro i hi h
    refine hne i hi ?_
    have := congrArg (Units.val) h
    rwa [Units.val_mul, Units.val_pow_eq_pow_val, huval, hu₀val, Units.val_one] at this

/-- **BG Theorem E.3(b), Step 2, third clause**: `|S| ≤ p^q`.

BG: *"Recall that the nonzero integers `(mod p)` form a cyclic group of order `p − 1` and
`rᵠ ≡ 1 (mod p)`.  Therefore, by `(E.10)` and `(E.11)`, there exists an integer `j` such
that `1 ≤ j ≤ q − 1` and `rʲ ≡ r₀ (mod p)`.  By `(E.12)`, none of the integers
`r₀, r₀r, …, r₀rⁿ⁻¹` is congruent to `1 (mod p)`.  Therefore `q − 1 ≥ j + n − 1 ≥ n` and
`|S| = |R₀T| = p·pⁿ ≤ p^q`.  This completes the proof of Step 2."*

The size is read off from `(E.5)` rather than from BG's `|R₀T|`: `|S| = |T|·|S : T| = pⁿ·p`
uses only the index `|S : T| = p`, which Lemma 5.2 already delivers.

⚠ Unlike the first two clauses of Step 2, this one genuinely needs the `A`-action: the
regularity of `A` is what forbids the eigenvalue `1` and so bounds the chain length. -/
theorem RegularOperatorSetup.card_le_pow_card_A {R B : Type*} [Group R] [Group B] [Finite R]
    {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1) (hS : 3 ≤ pRank ↥S p)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) :
    Nat.card ↥S ≤ p ^ q := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hT
  obtain ⟨n, hlive, hTcard⟩ := hyp.exists_chain_length hR₀S hexp hS
  -- `|S| = |T| · |S : T| = pⁿ · p`
  have hScard : Nat.card ↥S = p ^ (n + 1) := by
    have h := Subgroup.card_mul_index T
    rw [hTcard, (hyp.card_omega1Center_and_index_centralizer hR₀S hS).2] at h
    rw [← h, pow_succ]
  suffices hn : n ≤ q - 1 by
    rw [hScard]
    exact Nat.pow_le_pow_right hyp.p_prime.pos (by have := hyp.q_prime.pos; omega)
  rcases Nat.eq_zero_or_pos n with rfl | hnpos
  · omega
  -- the chain is alive at `0`, i.e. `T ≠ 1`
  have h0live : OddOrder.Isaacs.Ch04.iterCommutator T (⊤ : Subgroup ↥S) 0 ≠ ⊥ := hlive 0 hnpos
  -- BG's `a ∈ A^#`
  obtain ⟨a, ha, hane⟩ : ∃ a, ∃ h : a ∈ hyp.A, (⟨a, h⟩ : ↥hyp.A) ≠ 1 := by
    haveI : Nontrivial ↥hyp.A := by
      have hcard := hyp.A_card
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro h
      rw [h, Subgroup.card_bot] at hcard
      exact hyp.q_prime.one_lt.ne hcard
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥hyp.A)
    exact ⟨x.1, x.2, by simpa using hx⟩
  have hane' : a ≠ 1 := fun h => hane (Subtype.ext (by simpa using h))
  -- BG's `v ∈ R₀^#`
  obtain ⟨v, hv⟩ := hyp.exists_zpowers_eq_R₀_subgroupOf hR₀S
  have hvR₀ : (v : R) ∈ hyp.R₀ := by
    have : v ∈ hyp.R₀.subgroupOf S := by rw [← hv]; exact Subgroup.mem_zpowers v
    exact Subgroup.mem_subgroupOf.mp this
  -- `(E.9)`: `vᵃ = vʳ`, and `(E.11)`: `r ≢ 1`
  obtain ⟨r, hrall, hrq⟩ := hyp.exists_zpow_eq_act_of_mem_A ha
  have hrne : (r : ZMod p) ≠ 1 := hyp.zpow_exponent_ne_one ha hane' hrall
  have hr : (hSinv.restrict ⟨a, ha⟩) v = v ^ r := by
    refine Subtype.ext ?_
    rw [IsAInvariant.restrict_apply_val]
    push_cast
    exact hrall _ hvR₀
  -- BG's `w ∈ H₀ − H₁`
  obtain ⟨w, hwmem, hw1⟩ := SetLike.exists_of_lt (hyp.iterCommutator_lt hR₀S hexp hS h0live)
  rw [OddOrder.Isaacs.Ch04.iterCommutator_zero] at hwmem
  -- `r₀`, the eigenvalue on the top section
  obtain ⟨r₀, hr₀q, hr₀⟩ := hyp.exists_zpow_eq_mod_chain hR₀S hexp hS hSinv h0live ha
  -- `(E.12)` + `(E.10)`: none of `r₀ rⁱ` is `≡ 1`, for `i < n`
  refine le_pred_of_forall_zmod_mul_pow_ne_one hyp.q_prime hrq hrne hr₀q ?_
  intro i hi
  obtain ⟨s, hs, hsmem⟩ :=
    hyp.exists_eigenvalue_pow hR₀S hexp hS hSinv ha hv hwmem hw1 hr hr₀ i (hlive i hi)
  rw [← hs]
  exact hyp.eigenvalue_ne_one hR₀S hexp hS hSinv (hlive i hi) ha hane' hsmem

/-- **BG Theorem E.3(b), Step 2, third clause, with no rank hypothesis**: `|S| ≤ p^q`.

The rank-`≥ 3` case is `card_le_pow_card_A`.  In the remaining case `|S| ≤ p³`, and `p³ ≤ p^q`
because `q` is an **odd** prime, hence `≥ 3` — so BG's "check the `p`-groups of order at most
`p³`" is again not needed (cf. `not_le_derivedInG`, where the same branch collapsed).

⚠ Unlike `card_quotient_commutator`, the small case here needs nothing about `S` beyond its
order: the bound is `p³` on the nose. -/
theorem RegularOperatorSetup.card_le_pow {R B : Type*} [Group R] [Group B] [Finite R]
    {p q : ℕ} (hyp : RegularOperatorSetup R B p q) {S : Subgroup R} (hR₀S : hyp.R₀ ≤ S)
    (hexp : ∀ x : ↥S, x ^ p = 1)
    (hSinv : IsAInvariant (hyp.act.comp hyp.A.subtype) S) :
    Nat.card ↥S ≤ p ^ q := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rcases le_or_gt (Nat.card ↥S) (p ^ 3) with hle | hgt
  · refine hle.trans (Nat.pow_le_pow_right hyp.p_prime.pos ?_)
    obtain ⟨k, hk⟩ := hyp.q_odd
    have := hyp.q_prime.two_le
    omega
  · exact hyp.card_le_pow_card_A hR₀S hexp
      (three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup S) hexp hgt) hSinv

/- **BG Theorem E.3(c)** (`|Ω₁(R)| ≤ p^q`) is `card_omega_le` in
`OddOrder/BG/AppE_ExponentP.lean`: its proof is `card_le_pow` above applied to `S = Ω₁(R)`,
which needs Step 3's exponent statement, and that is what the downstream leaf carries. -/

end OddOrder.BG.AppE
