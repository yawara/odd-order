/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import OddOrder.GroupTheory.SubgroupInAmbient

/-!
# Three-step groups (Gorenstein, Ch. 12 §1)

D. Gorenstein, *Finite Groups* (2nd ed.), Chapter 12 "Groups in which centralizers are
nilpotent", Section 1 "Basic properties of CN-groups".

Bender--Glauberman, *Local Analysis for the Odd Order Theorem*, Appendix D cites this material
as "**G**, Section 14.1 / Corollary 14.1.6"; in the edition transcribed under `references/` the
same text is Chapter 12 §1 (the *3-step group* definition, Theorem 1.5, Corollary 1.6).

## Scope

This file formalizes **only** the minimal path Appendix D consumes: the definition of a 3-step
group and the two structural consequences BG uses from it.  Chapter 12 is deliberately *not*
formalized wholesale.

## Main definitions

* `opPPrimeCore p G` — the subgroup `O_{p,p'}(G)`, i.e. the preimage in `G` of `O_{p'}(G/O_p(G))`.
* `opPPrimePCore p G` — the subgroup `O_{p,p',p}(G)`, i.e. the preimage in `G` of
  `O_p(G/O_{p,p'}(G))`.
* `IsThreeStepGroup G p` — Gorenstein's *3-step group with respect to `p`*, stated verbatim as
  the conjunction of his three conditions.

## Main results

* `IsFrobeniusGroup.eq_bot_of_normal_of_inf_kernel_eq_bot` — in a Frobenius group a normal
  subgroup meeting the kernel trivially is trivial.  (General Frobenius theory; the engine
  behind the first consequence below.)
* `IsThreeStepGroup.oPiCore_pPrime_eq_bot` — a 3-step group has `O_{p'}(G) = 1`.
* `IsThreeStepGroup.isPGroup_quotient` / `IsThreeStepGroup.nontrivial_quotient` — for a 3-step
  group `G/O_{p,p'}(G)` is a nontrivial `p`-group.
* `IsThreeStepGroup.inf_sylow_eq_oPiCore` — in a 3-step group two *distinct* Sylow
  `p`-subgroups intersect in exactly `O_p(G)`.  This is BG Appendix D's display (D.2), which
  the text obtains from "the definition of a 3-step group and a short argument".

These three are exactly the facts BG Lemma D.1 extracts from Corollary 1.6.

## Conventions

`O_p` is spelled `Ch03.oPiCore ({p} : Set ℕ)` (the supremum of the normal `p`-subgroups) rather
than `Ch01.opCore` (the intersection of the Sylow `p`-subgroups); the two agree for finite `G`
by `Ch04.oPiCore_singleton_eq_opCore`, but only the former has the maximality property used
throughout, and only the former composes with the `π`-core machinery of `Ch03`.  The `p'`-core is
spelled `Ch03.oPiCore {q | q ≠ p}`; see `oPiCore_ne_eq_oPiCore_not_mem` for the conversion to the
`{q | q ∉ {p}}` spelling that `Ch03` uses internally.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

/-! ## The `p`-prime core, spelled two ways

`Ch03` states its `π`-core lemmas for the complement set `{q | q ∉ π}`, while it is more
convenient here to write `{q | q ≠ p}`.  The two sets are equal; this is the bridge. -/

/-- The two spellings of the set of primes different from `p` agree. -/
theorem setOf_ne_eq_setOf_not_mem_singleton (p : ℕ) :
    {q : ℕ | q ≠ p} = {q : ℕ | q ∉ ({p} : Set ℕ)} := by
  ext q; simp

/-- `O_{p'}(G)` written with `{q | q ≠ p}` agrees with the `Ch03` spelling `{q | q ∉ {p}}`. -/
theorem oPiCore_ne_eq_oPiCore_not_mem (p : ℕ) (G : Type*) [Group G] :
    Ch03.oPiCore {q : ℕ | q ≠ p} G = Ch03.oPiCore {q : ℕ | q ∉ ({p} : Set ℕ)} G := by
  rw [setOf_ne_eq_setOf_not_mem_singleton]

/-- `O_p(G) ⊓ O_{p'}(G) = 1`: the `p`-core and the `p'`-core intersect trivially. -/
theorem oPiCore_singleton_inf_oPiCore_ne_eq_bot [Finite G] (p : ℕ) :
    Ch03.oPiCore ({p} : Set ℕ) G ⊓ Ch03.oPiCore {q : ℕ | q ≠ p} G = ⊥ := by
  rw [oPiCore_ne_eq_oPiCore_not_mem]
  exact Ch03.oPiCore.coprime_inf ({p} : Set ℕ)

/-! ## `O_{p,p'}` and `O_{p,p',p}`

Gorenstein's upper `p`-series terms.  `Ch03` supplies `oPiPrimePiCore = O_{π',π}`, which starts
with the `π'`-core; the 3-step group definition needs the series that starts with the `p`-core,
so we build the two terms here.  Both are built as preimages under the canonical quotient map,
matching the shape of `Ch03.oPiPrimePiCore`. -/

/-- **`O_{p,p'}(G)`**: the preimage in `G` of the `p'`-core of `G/O_p(G)`.

Equivalently, the unique normal subgroup of `G` containing `O_p(G)` whose quotient by `O_p(G)`
is the largest normal `p'`-subgroup of `G/O_p(G)`. -/
def opPPrimeCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G))
    (Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G))

instance opPPrimeCore.normal (p : ℕ) (G : Type*) [Group G] : (opPPrimeCore p G).Normal :=
  Subgroup.Normal.comap (Ch03.oPiCore.normal _ _) _

/-- `O_p(G) ≤ O_{p,p'}(G)`. -/
theorem oPiCore_le_opPPrimeCore (p : ℕ) (G : Type*) [Group G] :
    Ch03.oPiCore ({p} : Set ℕ) G ≤ opPPrimeCore p G := by
  intro x hx
  have : (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G)) x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx
  simp [opPPrimeCore, Subgroup.mem_comap, this]

/-- **`O_{p,p',p}(G)`**: the preimage in `G` of the `p`-core of `G/O_{p,p'}(G)`. -/
def opPPrimePCore (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' (opPPrimeCore p G))
    (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ opPPrimeCore p G))

instance opPPrimePCore.normal (p : ℕ) (G : Type*) [Group G] : (opPPrimePCore p G).Normal :=
  Subgroup.Normal.comap (Ch03.oPiCore.normal _ _) _

/-- `O_{p,p'}(G) ≤ O_{p,p',p}(G)`. -/
theorem opPPrimeCore_le_opPPrimePCore (p : ℕ) (G : Type*) [Group G] :
    opPPrimeCore p G ≤ opPPrimePCore p G := by
  intro x hx
  have : (QuotientGroup.mk' (opPPrimeCore p G)) x = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hx
  simp [opPPrimePCore, Subgroup.mem_comap, this]

/-- `O_{p,p',p}(G) = ⊤` exactly when `O_p(G/O_{p,p'}(G))` is everything. -/
theorem opPPrimePCore_eq_top_iff (p : ℕ) (G : Type*) [Group G] :
    opPPrimePCore p G = ⊤ ↔ Ch03.oPiCore ({p} : Set ℕ) (G ⧸ opPPrimeCore p G) = ⊤ := by
  constructor
  · intro h
    rw [eq_top_iff]
    rintro x -
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (opPPrimeCore p G) x
    have : g ∈ opPPrimePCore p G := h ▸ Subgroup.mem_top g
    exact this
  · intro h
    rw [eq_top_iff]
    rintro x -
    simp only [opPPrimePCore, Subgroup.mem_comap, h, Subgroup.mem_top]

/-! ### The two cores mean what Gorenstein's notation says

These two lemmas certify that the subgroups appearing in `IsThreeStepGroup` below really are
`O_p(G)` and `O_{p,p'}(G)/O_p(G)`, rather than some accidental artefact of the `comap`/
`subgroupOf` encoding.  They are the first half of the non-vacuity audit of the definition. -/

/-- `O_{p,p'}(G)/O_p(G) = O_{p'}(G/O_p(G))`: the subgroup used as the Frobenius kernel in the
third condition of `IsThreeStepGroup` really is the `p'`-core of `G/O_p(G)`. -/
theorem opPPrimeCore_map_mk_eq (p : ℕ) (G : Type*) [Group G] :
    (opPPrimeCore p G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G)) =
      Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) :=
  Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- `O_p(G)`, viewed inside `O_{p,p'}(G)` and pushed back to `G`, is `O_p(G)`: the subgroup used
as the Frobenius kernel in the first condition of `IsThreeStepGroup` really is `O_p(G)`. -/
theorem oPiCore_subgroupOf_map_subtype (p : ℕ) (G : Type*) [Group G] :
    ((Ch03.oPiCore ({p} : Set ℕ) G).subgroupOf (opPPrimeCore p G)).map
        (opPPrimeCore p G).subtype = Ch03.oPiCore ({p} : Set ℕ) G :=
  Subgroup.map_subgroupOf_eq_of_le (oPiCore_le_opPPrimeCore p G)

/-! ### How a Sylow `p`-subgroup sits across `O_{p,p'}(G)`

Two facts about an arbitrary finite group, used below to identify the image of a Sylow
`p`-subgroup in `G/O_p(G)` as a complement to `O_{p,p'}(G)/O_p(G)`. -/

/-- `O_p(G)` lies in every Sylow `p`-subgroup: it is a normal `p`-subgroup. -/
theorem oPiCore_le_sylow [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    Ch03.oPiCore ({p} : Set ℕ) G ≤ (S : Subgroup G) := by
  rw [Ch04.oPiCore_singleton_eq_opCore]
  exact Ch01.opCore_le S

/-- A Sylow `p`-subgroup covers every quotient of `G` that is a `p`-group. -/
theorem sylow_sup_eq_top_of_isPGroup_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hN : IsPGroup p (G ⧸ N)) (S : Sylow p G) :
    (S : Subgroup G) ⊔ N = ⊤ := by
  -- The image of `S` is a Sylow `p`-subgroup of the `p`-group `G/N`, hence everything.
  have hmap : (S : Subgroup G).map (QuotientGroup.mk' N) = ⊤ := by
    have hSyl : ((S.mapSurjective (QuotientGroup.mk'_surjective N) : Sylow p (G ⧸ N)) :
        Subgroup (G ⧸ N)) = (S : Subgroup G).map (QuotientGroup.mk' N) :=
      Sylow.coe_mapSurjective _ _
    rw [← hSyl]
    exact ((S.mapSurjective (QuotientGroup.mk'_surjective N)).3
      (hN.to_subgroup ⊤) le_top).symm
  have := Subgroup.comap_map_eq (QuotientGroup.mk' N) (S : Subgroup G)
  rw [hmap, QuotientGroup.ker_mk'] at this
  simpa using this.symm

/-- A Sylow `p`-subgroup meets `O_{p,p'}(G)` exactly in `O_p(G)`: the quotient
`O_{p,p'}(G)/O_p(G)` is a `p'`-group, so it can absorb nothing more of `S`. -/
theorem sylow_inf_opPPrimeCore_eq_oPiCore [Finite G] {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    (S : Subgroup G) ⊓ opPPrimeCore p G = Ch03.oPiCore ({p} : Set ℕ) G := by
  refine le_antisymm ?_ (le_inf (oPiCore_le_sylow S) (oPiCore_le_opPPrimeCore p G))
  set mk := QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G) with hmk
  -- The image of `S ⊓ O_{p,p'}(G)` downstairs is a `p`-subgroup of the `p'`-group `O_{p'}`.
  set H := ((S : Subgroup G) ⊓ opPPrimeCore p G).map mk with hH
  have hHle : H ≤ Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) := by
    rw [hH, ← opPPrimeCore_map_mk_eq p G]
    exact Subgroup.map_mono inf_le_right
  have hHp : IsPGroup p ↥H := (S.2.to_inf_left (K := opPPrimeCore p G)).map mk
  have hHbot : H = ⊥ := by
    refine eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl (π := {q : ℕ | q ≠ p}) hHle ?_ ?_
    · exact fun r hr => Ch03.oPiCore.isPiGroup {q : ℕ | q ≠ p} r hr
    · intro r hr
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hHp
      rw [hk] at hr
      obtain ⟨hrp, hrdvd, -⟩ := Nat.mem_primeFactors.mp hr
      have hrp' : r = p := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
        (hrp.dvd_of_dvd_pow hrdvd)
      simp [hrp']
  -- A trivial image means `S ⊓ O_{p,p'}(G)` sits inside the kernel `O_p(G)`.
  intro x hx
  have : mk x = 1 := by
    have : mk x ∈ H := Subgroup.mem_map_of_mem _ hx
    rw [hHbot, Subgroup.mem_bot] at this
    exact this
  rwa [hmk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this

/-! ## A general Frobenius lemma

In a Frobenius group `G = K ⋊ A`, a normal subgroup `M` with `M ⊓ K = 1` centralizes `K`
elementwise, hence lies in `C_G(k) ≤ K` for any `1 ≠ k ∈ K`, hence is trivial.  This is the
engine behind `O_{p'}(G) = 1` for 3-step groups. -/

/-- In a Frobenius group, a normal subgroup meeting the kernel trivially is trivial.

If `M ⊴ G` and `M ⊓ N = 1` with `N` the Frobenius kernel, then `M` and `N` commute elementwise
(disjoint normal subgroups), so `M ≤ C_G(n)` for any `1 ≠ n ∈ N`; but `C_G(n) ≤ N` in a
Frobenius group (Isaacs Thm 6.4 (4)), so `M ≤ M ⊓ N = 1`. -/
theorem IsFrobeniusGroup.eq_bot_of_normal_of_inf_kernel_eq_bot
    [Finite G] {N A M : Subgroup G} (h : Ch06.IsFrobeniusGroup G N A) (hMnormal : M.Normal)
    (hM : M ⊓ N = ⊥) : M = ⊥ := by
  -- Choose a nonidentity element of the kernel.
  obtain ⟨n, hn_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot_kernel
  have hn_ne' : (n : G) ≠ 1 := fun hc => hn_ne (Subtype.ext hc)
  -- `M` centralizes `n`: disjoint normal subgroups commute elementwise.
  have hdisj : Disjoint M N := disjoint_iff.mpr hM
  have hMcent : M ≤ Subgroup.centralizer ({(n : G)} : Set G) := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.commute_of_normal_of_disjoint M N hMnormal h.isNormal hdisj
      m (n : G) hm n.2).eq
  -- In a Frobenius group `C_G(n) ≤ N` for `1 ≠ n ∈ N`.
  have hle : M ≤ N := hMcent.trans (h.centralizer_kernel_le (n : G) n.2 hn_ne')
  rw [eq_bot_iff, ← hM]
  exact le_inf le_rfl hle

/-! ## 3-step groups (Gorenstein Ch. 12 §1)

> We shall call `G` a **3-step group** (with respect to the prime `p`) provided:
>
> * `O_{p,p'}(G)` is a Frobenius group with kernel `O_p(G)` and cyclic complement of odd order;
> * `G = O_{p,p',p}(G)` and `G ⊋ O_{p,p'}(G)`;
> * `G/O_p(G)` is a Frobenius group with kernel `O_{p,p'}(G)/O_p(G)`.
-/

/-- **Gorenstein Ch. 12 §1** (3-step group), stated verbatim.

`G` is a *3-step group with respect to the prime `p`* when the three displayed conditions hold.
The Frobenius conditions are witnessed by the complement, which Gorenstein leaves implicit; the
repository's `Ch06.IsFrobeniusGroup` takes kernel and complement as explicit arguments, so the
complements appear here existentially. -/
structure IsThreeStepGroup (G : Type*) [Group G] (p : ℕ) : Prop where
  /-- (1) `O_{p,p'}(G)` is a Frobenius group with kernel `O_p(G)` and cyclic complement of odd
  order. -/
  frobenius_opPPrimeCore :
    ∃ A : Subgroup ↥(opPPrimeCore p G),
      Ch06.IsFrobeniusGroup ↥(opPPrimeCore p G)
        ((Ch03.oPiCore ({p} : Set ℕ) G).subgroupOf (opPPrimeCore p G)) A ∧
      IsCyclic ↥A ∧ Odd (Nat.card ↥A)
  /-- (2a) `G = O_{p,p',p}(G)`. -/
  opPPrimePCore_eq_top : opPPrimePCore p G = ⊤
  /-- (2b) `G ⊋ O_{p,p'}(G)`, i.e. the inclusion is proper. -/
  opPPrimeCore_ne_top : opPPrimeCore p G ≠ ⊤
  /-- (3) `G/O_p(G)` is a Frobenius group with kernel `O_{p,p'}(G)/O_p(G)`. -/
  frobenius_quotient :
    ∃ B : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G),
      Ch06.IsFrobeniusGroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)
        ((opPPrimeCore p G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G))) B

namespace IsThreeStepGroup

variable {p : ℕ}

/-! ### Consequence (a): `O_{p'}(G) = 1` -/

/-- `O_{p'}(G) ≤ O_{p,p'}(G)`: the image of the `p'`-core in `G/O_p(G)` is a normal
`p'`-subgroup, hence lies in `O_{p'}(G/O_p(G))`. -/
theorem oPiCore_pPrime_le_opPPrimeCore [Finite G] (p : ℕ) :
    Ch03.oPiCore {q : ℕ | q ≠ p} G ≤ opPPrimeCore p G := by
  intro x hx
  simp only [opPPrimeCore, Subgroup.mem_comap]
  refine Ch03.oPiCore.map_le_of_surjective {q : ℕ | q ≠ p} _
    (QuotientGroup.mk'_surjective _) ?_
  exact Subgroup.mem_map_of_mem _ hx

/-- **Consequence (a)**: a 3-step group has trivial `p'`-core, `O_{p'}(G) = 1`.

`O_{p'}(G)` is normal in `G`, lies in `O_{p,p'}(G)`, and meets the Frobenius kernel `O_p(G)`
trivially (coprime orders); by
`IsFrobeniusGroup.eq_bot_of_normal_of_inf_kernel_eq_bot` it is therefore trivial. -/
theorem oPiCore_pPrime_eq_bot [Finite G] (h : IsThreeStepGroup G p) :
    Ch03.oPiCore {q : ℕ | q ≠ p} G = ⊥ := by
  obtain ⟨A, hFrob, -, -⟩ := h.frobenius_opPPrimeCore
  set K : Subgroup G := Ch03.oPiCore {q : ℕ | q ≠ p} G with hK
  have hKle : K ≤ opPPrimeCore p G := oPiCore_pPrime_le_opPPrimeCore p
  -- Transport `K` into the subgroup `O_{p,p'}(G)` viewed as a type.
  set M : Subgroup ↥(opPPrimeCore p G) := K.subgroupOf (opPPrimeCore p G) with hM
  have hMnormal : M.Normal := Subgroup.Normal.subgroupOf (Ch03.oPiCore.normal _ _) _
  -- `M` meets the Frobenius kernel `O_p(G) ∩ O_{p,p'}(G)` trivially.
  have hKp : K ⊓ Ch03.oPiCore ({p} : Set ℕ) G = ⊥ := by
    rw [hK, inf_comm]; exact oPiCore_singleton_inf_oPiCore_ne_eq_bot p
  have hinf : M ⊓ (Ch03.oPiCore ({p} : Set ℕ) G).subgroupOf (opPPrimeCore p G) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyM, hyP⟩
    have hy1 : (y : G) = 1 := by
      have : (y : G) ∈ K ⊓ Ch03.oPiCore ({p} : Set ℕ) G := ⟨hyM, hyP⟩
      rw [hKp] at this
      simpa using this
    simpa [Subgroup.mem_bot] using Subtype.ext hy1
  have hMbot : M = ⊥ :=
    IsFrobeniusGroup.eq_bot_of_normal_of_inf_kernel_eq_bot hFrob hMnormal hinf
  -- `M = ⊥` together with `K ≤ O_{p,p'}(G)` forces `K = ⊥`.
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hKle hx⟩ : ↥(opPPrimeCore p G)) ∈ M := hx
  rw [hMbot, Subgroup.mem_bot] at hx'
  have : x = 1 := congrArg Subtype.val hx'
  simp [this]

/-! ### Consequence (b): `G/O_{p,p'}(G)` is a nontrivial `p`-group -/

/-- **Consequence (b), first half**: for a 3-step group `G/O_{p,p'}(G)` is a `p`-group.

Immediate from `G = O_{p,p',p}(G)`: that says the `p`-core of `G/O_{p,p'}(G)` is everything. -/
theorem isPGroup_quotient [Finite G] [Fact p.Prime] (h : IsThreeStepGroup G p) :
    IsPGroup p (G ⧸ opPPrimeCore p G) := by
  have htop : Ch03.oPiCore ({p} : Set ℕ) (G ⧸ opPPrimeCore p G) = ⊤ :=
    (opPPrimePCore_eq_top_iff p G).mp h.opPPrimePCore_eq_top
  have hpi : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (⊤ : Subgroup (G ⧸ opPPrimeCore p G)) := by
    rw [← htop]; exact Ch03.oPiCore.isPiGroup ({p} : Set ℕ)
  exact (Ch04.isPGroup_of_isPiGroup_singleton (p := p) hpi).of_equiv Subgroup.topEquiv

/-- **Consequence (b), second half**: for a 3-step group `G/O_{p,p'}(G)` is nontrivial.

Immediate from the proper inclusion `G ⊋ O_{p,p'}(G)`. -/
theorem nontrivial_quotient (h : IsThreeStepGroup G p) :
    Nontrivial (G ⧸ opPPrimeCore p G) := by
  exact QuotientGroup.nontrivial_iff.mpr h.opPPrimeCore_ne_top

/-! ### Consequence (c): distinct Sylow `p`-subgroups meet exactly in `O_p(G)`

BG Appendix D derives the displayed identity `P ∩ Q = O_p(M)` (D.2) from "the definition of a
3-step group and a short argument".  This is that argument, in the generality it proves.

The image `S̄` of a Sylow `p`-subgroup in `Ḡ = G/O_p(G)` is a *complement* to the Frobenius
kernel `K̄ = O_{p,p'}(G)/O_p(G)`: it meets `K̄` trivially because `S ⊓ O_{p,p'}(G) = O_p(G)`
(`sylow_inf_opPPrimeCore_eq_oPiCore`) and it covers `Ḡ/K̄ ≅ G/O_{p,p'}(G)`, a `p`-group by
consequence (b).  A complement to a Frobenius kernel is automatically a *Frobenius* complement,
because the Frobenius condition can be read off the kernel alone (`C_Ḡ(k) ≤ K̄` for `1 ≠ k ∈ K̄`,
Isaacs Thm 6.4 (4)).  Frobenius complements form a trivial-intersection family
(Isaacs Thm 6.4 (1) ⇒ (2)), so distinct `S̄`, `T̄` meet trivially — which upstairs says that
`S ⊓ T` is exactly the kernel `O_p(G)` of the quotient map. -/

/-- In a 3-step group the image of a Sylow `p`-subgroup in `G/O_p(G)` is a complement to the
Frobenius kernel `O_{p,p'}(G)/O_p(G)`. -/
theorem isComplement'_quotient_sylow [Finite G] [Fact p.Prime] (h : IsThreeStepGroup G p)
    (S : Sylow p G) :
    Subgroup.IsComplement'
      ((opPPrimeCore p G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G)))
      ((S : Subgroup G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G))) := by
  set mk := QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G) with hmk
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hker : mk.ker = Ch03.oPiCore ({p} : Set ℕ) G := QuotientGroup.ker_mk' _
  have hkerS : mk.ker ≤ (S : Subgroup G) := by rw [hker]; exact oPiCore_le_sylow S
  have hkerK : mk.ker ≤ opPPrimeCore p G := by rw [hker]; exact oPiCore_le_opPPrimeCore p G
  haveI hKnormal : ((opPPrimeCore p G).map mk).Normal := by
    rw [hmk, opPPrimeCore_map_mk_eq]; infer_instance
  have hdisj : Disjoint ((opPPrimeCore p G).map mk) ((S : Subgroup G).map mk) := by
    rw [disjoint_iff]
    refine Subgroup.comap_injective hsurj ?_
    rw [Subgroup.comap_inf, Subgroup.comap_map_eq_self hkerK, Subgroup.comap_map_eq_self hkerS,
      MonoidHom.comap_bot, hker, inf_comm]
    exact sylow_inf_opPPrimeCore_eq_oPiCore S
  have hsup : (opPPrimeCore p G).map mk ⊔ (S : Subgroup G).map mk = ⊤ := by
    rw [sup_comm, ← Subgroup.map_sup,
      sylow_sup_eq_top_of_isPGroup_quotient h.isPGroup_quotient S]
    exact Subgroup.map_top_of_surjective mk hsurj
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
  rw [← Subgroup.normal_mul, hsup]
  rfl

/-- In a 3-step group the image of *any* Sylow `p`-subgroup in `G/O_p(G)` is a Frobenius
complement to `O_{p,p'}(G)/O_p(G)`.

Condition (3) of the definition supplies *some* complement `B`; the Frobenius property it
carries is a statement about the kernel alone, so it transfers to the Sylow image. -/
theorem isFrobeniusGroup_quotient_sylow [Finite G] [Fact p.Prime] (h : IsThreeStepGroup G p)
    (S : Sylow p G) :
    Ch06.IsFrobeniusGroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)
      ((opPPrimeCore p G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G)))
      ((S : Subgroup G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G))) := by
  obtain ⟨B, hB⟩ := h.frobenius_quotient
  refine Ch06.IsFrobeniusGroup.of_centralizer_kernel_le hB.isNormal
    (h.isComplement'_quotient_sylow S) hB.ne_bot_kernel ?_ hB.centralizer_kernel_le
  -- The Sylow image is nontrivial: otherwise `S ≤ O_{p,p'}(G)`, forcing `O_{p,p'}(G) = ⊤`.
  intro hbot
  refine h.opPPrimeCore_ne_top ?_
  have hSle : (S : Subgroup G) ≤ opPPrimeCore p G := by
    intro x hx
    have hmem : (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G)) x ∈
        (S : Subgroup G).map (QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G)) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    exact oPiCore_le_opPPrimeCore p G hmem
  have hsup := sylow_sup_eq_top_of_isPGroup_quotient h.isPGroup_quotient S
  rwa [sup_eq_right.mpr hSle] at hsup

/-- **BG Appendix D, display (D.2)** in its general form: in a 3-step group two *distinct* Sylow
`p`-subgroups intersect in exactly `O_p(G)`.

This is the "short argument" BG leaves to the reader after invoking Gorenstein's Corollary
1.6. -/
theorem inf_sylow_eq_oPiCore [Finite G] [Fact p.Prime] (h : IsThreeStepGroup G p)
    {S T : Sylow p G} (hST : (S : Subgroup G) ≠ (T : Subgroup G)) :
    (S : Subgroup G) ⊓ (T : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G := by
  set mk := QuotientGroup.mk' (Ch03.oPiCore ({p} : Set ℕ) G) with hmk
  have hsurj : Function.Surjective mk := QuotientGroup.mk'_surjective _
  have hker : mk.ker = Ch03.oPiCore ({p} : Set ℕ) G := QuotientGroup.ker_mk' _
  have hkerS : mk.ker ≤ (S : Subgroup G) := by rw [hker]; exact oPiCore_le_sylow S
  have hkerT : mk.ker ≤ (T : Subgroup G) := by rw [hker]; exact oPiCore_le_sylow T
  set Sbar : Sylow p (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) := S.mapSurjective hsurj with hSbar
  set Tbar : Sylow p (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) := T.mapSurjective hsurj with hTbar
  have hScoe : (Sbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) =
      (S : Subgroup G).map mk := by rw [hSbar]; simp
  have hTcoe : (Tbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) =
      (T : Subgroup G).map mk := by rw [hTbar]; simp
  -- The two images are distinct (both contain the kernel, so `comap` undoes `map`).
  have hne : (Sbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) ≠
      (Tbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) := by
    rw [hScoe, hTcoe]
    intro hEq
    refine hST ?_
    have hcomap := congrArg (Subgroup.comap mk) hEq
    rwa [Subgroup.comap_map_eq_self hkerS, Subgroup.comap_map_eq_self hkerT] at hcomap
  -- Downstairs they are conjugate Sylow subgroups, and Frobenius complements are TI.
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G) Sbar Tbar
  have hconj : (Tbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) =
      Subgroup.map (MulAut.conj g).toMonoidHom
        (Sbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hgnot : g ∉ (Sbar : Subgroup (G ⧸ Ch03.oPiCore ({p} : Set ℕ) G)) := by
    intro hgmem
    refine hne ?_
    rw [hconj]
    ext x
    simp only [Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
    refine ⟨fun hx => ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hgmem) hx) hgmem, by group⟩, ?_⟩
    rintro ⟨y, hy, rfl⟩
    exact mul_mem (mul_mem hgmem hy) (inv_mem hgmem)
  have hTI := (h.isFrobeniusGroup_quotient_sylow S).trivialIntersection g (hScoe ▸ hgnot)
  rw [← hScoe, ← hconj] at hTI
  -- Pull the trivial intersection back through the quotient map.
  have hpull := congrArg (Subgroup.comap mk) hTI
  rwa [Subgroup.comap_inf, hScoe, hTcoe, Subgroup.comap_map_eq_self hkerS,
    Subgroup.comap_map_eq_self hkerT, MonoidHom.comap_bot, hker] at hpull

/-! ### Gorenstein Lemma 1.4 (solvability half)

> A 3-step group is a solvable CN-group.

We prove the solvability half.  It doubles as the second half of the non-vacuity audit: a
definition that were accidentally contradictory would of course also prove solvability, but a
definition that were accidentally *degenerate* (e.g. if the `subgroupOf`/`map` encodings had
collapsed the Frobenius conditions) would not produce this proof through the intended route —
here the cyclic complement and the `p`-group quotient are both genuinely consumed. -/

/-- `O_p(G)`, as a subgroup of `O_{p,p'}(G)`, is a `p`-group. -/
theorem isPGroup_oPiCore_subgroupOf [Finite G] [Fact p.Prime] :
    IsPGroup p ↥((Ch03.oPiCore ({p} : Set ℕ) G).subgroupOf (opPPrimeCore p G)) :=
  (Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))).of_equiv
    (Subgroup.subgroupOfEquivOfLe (oPiCore_le_opPPrimeCore p G)).symm

/-- **Gorenstein Ch. 12 §1 Lemma 1.4** (solvability half): a 3-step group is solvable.

`O_{p,p'}(G)` is an extension of the `p`-group `O_p(G)` by the cyclic complement `A`, hence
solvable; and `G/O_{p,p'}(G)` is a `p`-group by `isPGroup_quotient`, hence solvable. -/
theorem isSolvable [Finite G] [Fact p.Prime] (h : IsThreeStepGroup G p) : IsSolvable G := by
  set L := opPPrimeCore p G with hL
  set N : Subgroup ↥L := (Ch03.oPiCore ({p} : Set ℕ) G).subgroupOf L with hN
  obtain ⟨Acompl, hFrob, hAcyc, -⟩ := h.frobenius_opPPrimeCore
  -- `N` is a `p`-group, hence nilpotent, hence solvable.
  haveI : N.Normal := hFrob.isNormal
  haveI hNnil : Group.IsNilpotent ↥N := (isPGroup_oPiCore_subgroupOf (G := G) (p := p)).isNilpotent
  haveI hNsolv : IsSolvable ↥N := inferInstance
  -- The quotient `L/N` is isomorphic to the cyclic complement `Acompl`, hence solvable.
  haveI hAcyc' : IsCyclic ↥Acompl := hAcyc
  haveI hAcomm : IsSolvable ↥Acompl :=
    isSolvable_of_comm (fun a b => (IsCyclic.commGroup (α := ↥Acompl)).mul_comm a b)
  haveI hQsolv : IsSolvable (↥L ⧸ N) :=
    solvable_of_surjective (f := (hFrob.isComplement.symm.QuotientMulEquiv).symm.toMonoidHom)
      (MulEquiv.surjective _)
  -- Hence `L = O_{p,p'}(G)` is solvable.
  haveI hLsolv : IsSolvable ↥L :=
    solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])
  -- `G/L` is a `p`-group, hence solvable; conclude by the same extension argument.
  haveI hGQnil : Group.IsNilpotent (G ⧸ L) := (h.isPGroup_quotient).isNilpotent
  haveI hGQ : IsSolvable (G ⧸ L) := inferInstance
  exact solvable_of_ker_le_range L.subtype (QuotientGroup.mk' L)
    (by rw [QuotientGroup.ker_mk', Subgroup.subtype_range])

end IsThreeStepGroup

end OddOrder.GroupTheory
