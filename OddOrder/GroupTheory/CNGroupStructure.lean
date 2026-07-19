/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.FittingSelfCentralizing
import OddOrder.GroupTheory.NilpotentCoprimeCommute

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

These last two are exactly the facts BG Lemma D.1 extracts from Corollary 1.6.

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

/-! ## Gorenstein Ch. 12 §1 Lemma 1.2

> Let `P` and `Q` be `S_p`- and `S_q`-subgroups of the CN-group `G`, where `p` and `q` are
> distinct primes.  If an element of `P^*` centralizes an element of `Q^*`, then `P` centralizes
> `Q`.

This is the CN-specific engine of the section (it is used four times in the proof of
Theorem 1.5).  The CN hypothesis is taken here in unfolded form — "every nonidentity element of
`G` has nilpotent centralizer" — which is definitionally `OddOrder.BG.AppD.IsCNGroup G`; taking
it unfolded keeps this general-purpose leaf free of a dependency on `OddOrder.BG`. -/

/-- The centre of a subgroup `H`, transported back to an ambient subgroup of `G`. -/
def centerIn (H : Subgroup G) : Subgroup G := (Subgroup.center ↥H).map H.subtype

theorem centerIn_le (H : Subgroup G) : centerIn H ≤ H := Subgroup.map_subtype_le _

/-- Every element of `H` commutes with every element of the centre of `H`. -/
theorem commute_of_mem_centerIn {H : Subgroup G} {a z : G} (ha : a ∈ H) (hz : z ∈ centerIn H) :
    Commute a z := by
  obtain ⟨⟨w, hw⟩, hwc, rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc ⟨a, ha⟩)

/-- A nontrivial finite `p`-subgroup has nontrivial centre. -/
theorem centerIn_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hH : IsPGroup p ↥H) (hne : H ≠ ⊥) : centerIn H ≠ ⊥ := by
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  haveI := hH.center_nontrivial
  obtain ⟨⟨⟨z, hzH⟩, hzc⟩, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥H))
  intro hbot
  apply hz1
  have hmem : z ∈ centerIn H := ⟨⟨z, hzH⟩, hzc, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

/-- In a finite nilpotent group, a `p`-subgroup and a `q`-subgroup with `p ≠ q` commute
elementwise: both lie in normal (hence unique) Sylow subgroups, which are disjoint. -/
theorem commute_of_isNilpotent_of_isPGroup {L : Type*} [Group L] [Finite L]
    [Group.IsNilpotent L] {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {H K : Subgroup L} (hH : IsPGroup p ↥H) (hK : IsPGroup q ↥K) :
    ∀ a ∈ H, ∀ b ∈ K, Commute a b := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hK.exists_le_sylow
  intro a ha b hb
  exact Subgroup.commute_of_normal_of_disjoint _ _
    (Ch01.Sylow.normal_of_isNilpotent P) (Ch01.Sylow.normal_of_isNilpotent Q)
    (IsPGroup.disjoint_of_ne p q hpq _ _ P.isPGroup' Q.isPGroup') a b (hP ha) (hQ hb)

/-- Ambient form of `commute_of_isNilpotent_of_isPGroup`: if `H` and `K` are a `p`-subgroup and a
`q`-subgroup (`p ≠ q`) of `G` both contained in a subgroup `N` with `N` nilpotent, then `H` and
`K` commute elementwise in `G`. -/
theorem commute_of_le_nilpotent_of_isPGroup [Finite G] {N : Subgroup G}
    (hN : Group.IsNilpotent ↥N) {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {H K : Subgroup G} (hHN : H ≤ N) (hKN : K ≤ N)
    (hH : IsPGroup p ↥H) (hK : IsPGroup q ↥K) :
    ∀ a ∈ H, ∀ b ∈ K, Commute a b := by
  haveI := hN
  have hH' : IsPGroup p ↥(H.subgroupOf N) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHN).symm
  have hK' : IsPGroup q ↥(K.subgroupOf N) :=
    hK.of_equiv (Subgroup.subgroupOfEquivOfLe hKN).symm
  intro a ha b hb
  exact congrArg Subtype.val
    (commute_of_isNilpotent_of_isPGroup hpq hH' hK'
      ⟨a, hHN ha⟩ ha ⟨b, hKN hb⟩ hb).eq

/-- **Gorenstein Ch. 12 §1 Lemma 1.2**.

Let `G` be a group in which every nonidentity element has nilpotent centralizer (a *CN-group*),
and let `P`, `Q` be a `p`-subgroup and a `q`-subgroup with `p ≠ q`.  If some nonidentity element
of `P` commutes with some nonidentity element of `Q`, then `P` and `Q` commute elementwise.

The proof is Gorenstein's, in four passes through the CN hypothesis: `C_G(x)` shows `y`
centralizes `Z(P)`; `C_G(x₁)` for `1 ≠ x₁ ∈ Z(P)` shows `P` centralizes `y`; `C_G(y)` shows `P`
centralizes `Z(Q)`; `C_G(y₁)` for `1 ≠ y₁ ∈ Z(Q)` shows `P` centralizes `Q`.

Stated for arbitrary `p`- and `q`-subgroups rather than only Sylow subgroups: the proof uses
nothing beyond the `p`-group property, so this is the general form. -/
theorem commute_of_cn_of_commute_ne_one [Finite G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {P Q : Subgroup G} (hP : IsPGroup p ↥P) (hQ : IsPGroup q ↥Q)
    {x y : G} (hxP : x ∈ P) (hx1 : x ≠ 1) (hyQ : y ∈ Q) (hy1 : y ≠ 1)
    (hxy : Commute x y) :
    ∀ a ∈ P, ∀ b ∈ Q, Commute a b := by
  -- Notation for the two centres and the cyclic subgroup generated by `y`.
  have hZPle : centerIn P ≤ P := centerIn_le P
  have hZQle : centerIn Q ≤ Q := centerIn_le Q
  have hZP : IsPGroup p ↥(centerIn P) := hP.to_le hZPle
  have hZQ : IsPGroup q ↥(centerIn Q) := hQ.to_le hZQle
  have hyzp : Subgroup.zpowers y ≤ Q := Subgroup.zpowers_le.mpr hyQ
  have hyP : IsPGroup q ↥(Subgroup.zpowers y) := hQ.to_le hyzp
  -- Step 1: `y` centralizes `Z(P)`, via the nilpotent centralizer `C_G(x)`.
  have step1 : ∀ z ∈ centerIn P, Commute z y := by
    have hZPc : centerIn P ≤ Subgroup.centralizer ({x} : Set G) := fun z hz =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn hxP hz).symm.eq
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm.eq)
    intro z hz
    exact commute_of_le_nilpotent_of_isPGroup (hCN x hx1) hpq hZPc hyc hZP hyP
      z hz y (Subgroup.mem_zpowers y)
  -- Step 2: `P` centralizes `y`, via `C_G(x₁)` for a nonidentity `x₁ ∈ Z(P)`.
  have hPne : P ≠ ⊥ := fun hc => hx1 (by simpa [hc, Subgroup.mem_bot] using hxP)
  obtain ⟨x₁, hx₁mem⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (centerIn_ne_bot hP hPne)
  have hx₁1 : (x₁ : G) ≠ 1 := fun hc => hx₁mem (Subtype.ext hc)
  have step2 : ∀ a ∈ P, Commute a y := by
    have hPc : P ≤ Subgroup.centralizer ({(x₁ : G)} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_mem_centerIn ha x₁.2).eq
    have hyc : Subgroup.zpowers y ≤ Subgroup.centralizer ({(x₁ : G)} : Set G) :=
      Subgroup.zpowers_le.mpr
        (Subgroup.mem_centralizer_singleton_iff.mpr (step1 _ x₁.2).symm.eq)
    intro a ha
    exact commute_of_le_nilpotent_of_isPGroup (hCN _ hx₁1) hpq hPc hyc hP hyP
      a ha y (Subgroup.mem_zpowers y)
  -- Step 3: `P` centralizes `Z(Q)`, via `C_G(y)`.
  have step3 : ∀ a ∈ P, ∀ w ∈ centerIn Q, Commute a w := by
    have hPc : P ≤ Subgroup.centralizer ({y} : Set G) := fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (step2 a ha).eq
    have hZQc : centerIn Q ≤ Subgroup.centralizer ({y} : Set G) := fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn hyQ hw).symm.eq
    exact commute_of_le_nilpotent_of_isPGroup (hCN y hy1) hpq hPc hZQc hP hZQ
  -- Step 4: `P` centralizes `Q`, via `C_G(y₁)` for a nonidentity `y₁ ∈ Z(Q)`.
  have hQne : Q ≠ ⊥ := fun hc => hy1 (by simpa [hc, Subgroup.mem_bot] using hyQ)
  obtain ⟨y₁, hy₁mem⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (centerIn_ne_bot hQ hQne)
  have hy₁1 : (y₁ : G) ≠ 1 := fun hc => hy₁mem (Subtype.ext hc)
  have hPc : P ≤ Subgroup.centralizer ({(y₁ : G)} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (step3 a ha _ y₁.2).eq
  have hQc : Q ≤ Subgroup.centralizer ({(y₁ : G)} : Set G) := fun b hb =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn hb y₁.2).eq
  exact commute_of_le_nilpotent_of_isPGroup (hCN _ hy₁1) hpq hPc hQc hP hQ

/-! ## Step 2 of Theorem 1.5: `F(G) A` is Frobenius

Gorenstein's Theorem 1.5 begins by setting `F = F(G)`, `π = π(F)`, and taking a Hall
`π'`-subgroup `A` of the solvable group `G`.  Its first substantive claim is that no nonidentity
element of `A` centralizes a nonidentity element of `F`, so that `A` acts regularly on `F` and
`FA` is a Frobenius group.  This is where the CN hypothesis enters, through Lemma 1.2.

The proof uses nothing about `A` beyond `(|A|, |F|) = 1`, so it is stated for a single element
whose order is prime to `|F(G)|`.  That is a genuine generalization of the book's statement, not
a weakening: the Hall `π'`-subgroup version follows by applying it to each element of `A`. -/

/-- The Sylow `p`-subgroup of `F(G)`, pushed back into `G`, lies in `O_p(G)`.

`F(G)` is nilpotent, so its Sylow `p`-subgroup is normal in it and therefore characteristic;
`F(G)` is normal in `G`, so the image is normal in `G`; a normal `p`-subgroup lies in `O_p(G)`. -/
theorem sylow_fitting_map_le_oPiCore [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p ↥(Ch01.fitting G)) :
    (S : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype ≤
      Ch03.oPiCore ({p} : Set ℕ) G := by
  haveI hSn : (S : Subgroup ↥(Ch01.fitting G)).Normal := Ch01.Sylow.normal_of_isNilpotent S
  haveI hSc : (S : Subgroup ↥(Ch01.fitting G)).Characteristic :=
    Sylow.characteristic_of_normal S hSn
  haveI : ((S : Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype).Normal :=
    normal_map_subtype_of_characteristic hSc
  exact (Ch04.isPiGroup_singleton_of_isPGroup
    (S.isPGroup'.map (Ch01.fitting G).subtype)).le_oPiCore

/-- The order of an element of a subgroup, computed in the subgroup, is its order in `G`. -/
theorem orderOf_mk_eq {H : Subgroup G} {x : G} (hx : x ∈ H) :
    orderOf (⟨x, hx⟩ : ↥H) = orderOf x :=
  (orderOf_injective H.subtype H.subtype_injective ⟨x, hx⟩).symm

/-- Two elements of `F(G)` whose orders are coprime commute, `F(G)` being nilpotent. -/
theorem commute_of_mem_fitting_of_coprime_orderOf [Finite G] {x f : G}
    (hx : x ∈ Ch01.fitting G) (hf : f ∈ Ch01.fitting G)
    (hcop : Nat.Coprime (orderOf x) (orderOf f)) : Commute x f := by
  exact congrArg Subtype.val
    (commute_of_coprime_orderOf_of_isNilpotent (L := ↥(Ch01.fitting G))
      (x := ⟨x, hx⟩) (y := ⟨f, hf⟩) (by rw [orderOf_mk_eq, orderOf_mk_eq]; exact hcop)).eq

/-- **Gorenstein Ch. 12 §1, Theorem 1.5, step 2.**

In a finite solvable CN-group, an element whose order is prime to `|F(G)|` centralizes no
nonidentity element of `F(G)`.

Gorenstein argues with a `q`-element `y` of a Hall `π(F)'`-subgroup `A` and a `p`-element `x` of
`F`; the four moves are (1) Lemma 1.2 makes `y` centralize a whole Sylow `p`-subgroup of `G`,
hence `O_p(G)`; (2) `C_G(x)` is nilpotent by the CN hypothesis and contains every element of `F`
of order prime to `p`; (3) coprimality of orders inside that nilpotent centralizer makes `y`
centralize all of those; (4) `F` is generated by its Sylow subgroups, so `y` centralizes `F`, and
`C_G(F) ≤ F` puts `y` in `F` — impossible, since `|y|` is prime to `|F|`. -/
theorem not_commute_of_coprime_orderOf_card_fitting [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {x y : G} (hxF : x ∈ Ch01.fitting G) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hcop : Nat.Coprime (orderOf y) (Nat.card ↥(Ch01.fitting G))) :
    ¬ Commute x y := by
  classical
  intro hxy
  -- Replace `x` and `y` by elements of prime order `p` and `q` inside `⟨x⟩` and `⟨y⟩`.
  obtain ⟨p, hp, hpx⟩ := Nat.exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
  obtain ⟨q, hq, hqy⟩ := Nat.exists_prime_and_dvd (fun h => hy1 (orderOf_eq_one_iff.mp h))
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) p
    (by rw [Nat.card_zpowers]; exact hpx)
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers y)) q
    (by rw [Nat.card_zpowers]; exact hqy)
  set x' : G := (x₀ : G) with hx'def
  set y' : G := (y₀ : G) with hy'def
  have hx'ord : orderOf x' = p :=
    (orderOf_injective (Subgroup.zpowers x).subtype
      (Subgroup.zpowers x).subtype_injective x₀).trans hx₀
  have hy'ord : orderOf y' = q :=
    (orderOf_injective (Subgroup.zpowers y).subtype
      (Subgroup.zpowers y).subtype_injective y₀).trans hy₀
  have hx'1 : x' ≠ 1 := fun h => hp.ne_one (by rw [← hx'ord, h, orderOf_one])
  have hy'1 : y' ≠ 1 := fun h => hq.ne_one (by rw [← hy'ord, h, orderOf_one])
  have hx'F : x' ∈ Ch01.fitting G :=
    (Subgroup.zpowers_le.mpr hxF) x₀.2
  -- `x'` and `y'` still commute: each is a power of the original.
  have hcomm' : Commute x' y' := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x₀.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y₀.2
    rw [hx'def, hy'def, ← hj, ← hk]
    exact (hxy.zpow_left j).zpow_right k
  -- `p ∣ |F(G)|` but `q ∤ |F(G)|`; in particular `p ≠ q`.
  have hpF : p ∣ Nat.card ↥(Ch01.fitting G) := by
    rw [← hx'ord, ← orderOf_mk_eq hx'F]
    exact orderOf_dvd_natCard _
  have hqF : ¬ q ∣ Nat.card ↥(Ch01.fitting G) := by
    intro hdvd
    have hqy' : q ∣ orderOf y := hy'ord ▸ orderOf_dvd_of_mem_zpowers y₀.2
    exact hq.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hqy' hdvd))
  have hpq : p ≠ q := fun h => hqF (h ▸ hpF)
  -- Step 1: Lemma 1.2 makes `y'` commute with a whole Sylow `p`-subgroup, hence with `O_p(G)`.
  have hx'pg : IsPGroup p ↥(Subgroup.zpowers x') :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hx'ord, pow_one]⟩
  have hy'qg : IsPGroup q ↥(Subgroup.zpowers y') :=
    IsPGroup.iff_card.mpr ⟨1, by rw [Nat.card_zpowers, hy'ord, pow_one]⟩
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hx'pg
  have hstep1 : ∀ a ∈ (P : Subgroup G), ∀ b ∈ Subgroup.zpowers y', Commute a b :=
    commute_of_cn_of_commute_ne_one hCN hpq P.isPGroup' hy'qg
      (hPle (Subgroup.mem_zpowers x')) hx'1 (Subgroup.mem_zpowers y') hy'1 hcomm'
  have hOple : Ch03.oPiCore ({p} : Set ℕ) G ≤ (P : Subgroup G) := by
    rw [Ch04.oPiCore_singleton_eq_opCore]
    exact Ch01.opCore_le P
  -- Step 2/3: inside the nilpotent centralizer `C_G(x')`, coprime orders commute.
  haveI hCnil : Group.IsNilpotent ↥(Subgroup.centralizer ({x'} : Set G)) := hCN x' hx'1
  have hy'C : y' ∈ Subgroup.centralizer ({x'} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm'.symm.eq
  -- Step 4: `F(G)` is generated by its Sylow subgroups, and `y'` commutes with each of them.
  have hcentF : ∀ f ∈ Ch01.fitting G, Commute y' f := by
    intro f hf
    have hmem : (⟨f, hf⟩ : ↥(Ch01.fitting G)) ∈
        ⨆ r : (Nat.card ↥(Ch01.fitting G)).primeFactors,
          ((default : Sylow (r : ℕ) ↥(Ch01.fitting G)) : Subgroup ↥(Ch01.fitting G)) := by
      rw [Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥(Ch01.fitting G)]; trivial
    refine Subgroup.iSup_induction _ (C := fun z : ↥(Ch01.fitting G) => Commute y' (z : G))
      hmem ?_ (Commute.one_right _) (fun a b ha hb => ha.mul_right hb)
    rintro ⟨r, hr⟩ z hz
    haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    have hzF : (z : G) ∈ Ch01.fitting G := z.2
    have hzr : IsPGroup r
        ↥((default : Sylow r ↥(Ch01.fitting G)) : Subgroup ↥(Ch01.fitting G)) :=
      (default : Sylow r ↥(Ch01.fitting G)).isPGroup'
    rcases eq_or_ne r p with rfl | hrp
    · -- `z` lies in the Sylow `p`-subgroup of `F(G)`, hence in `O_p(G) ≤ P`.
      have : (z : G) ∈ Ch03.oPiCore ({r} : Set ℕ) G :=
        sylow_fitting_map_le_oPiCore (default : Sylow r ↥(Ch01.fitting G))
          ⟨z, hz, rfl⟩
      exact (hstep1 (z : G) (hOple this) y' (Subgroup.mem_zpowers y')).symm
    · -- `z` has order prime to `p`, so it lies in `C_G(x')`; there coprimality finishes.
      obtain ⟨n, hn⟩ := hzr.exists_card_eq
      have hzcoe : orderOf (z : G) = orderOf z :=
        orderOf_injective (Ch01.fitting G).subtype (Ch01.fitting G).subtype_injective z
      have hzdvd : orderOf (z : G) ∣ r ^ n := by
        rw [hzcoe, ← orderOf_mk_eq hz, ← hn]
        exact orderOf_dvd_natCard _
      have hzC : (z : G) ∈ Subgroup.centralizer ({x'} : Set G) := by
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        refine (commute_of_mem_fitting_of_coprime_orderOf hx'F hzF ?_).symm.eq
        rw [hx'ord]
        exact Nat.Coprime.coprime_dvd_right hzdvd
          (Nat.Coprime.pow_right n ((Nat.coprime_primes hp Fact.out).mpr (Ne.symm hrp)))
      have hcopzy : Nat.Coprime (orderOf y') (orderOf (z : G)) := by
        rw [hy'ord]
        refine Nat.Coprime.coprime_dvd_right hzdvd (Nat.Coprime.pow_right n ?_)
        refine (Nat.coprime_primes hq Fact.out).mpr ?_
        rintro rfl
        exact hqF (Nat.dvd_of_mem_primeFactors hr)
      exact congrArg Subtype.val
        (commute_of_coprime_orderOf_of_isNilpotent
          (L := ↥(Subgroup.centralizer ({x'} : Set G)))
          (x := ⟨y', hy'C⟩) (y := ⟨(z : G), hzC⟩)
          (by rw [orderOf_mk_eq, orderOf_mk_eq]; exact hcopzy)).eq
  -- `y' ∈ C_G(F(G)) ≤ F(G)`, so `q = |y'|` divides `|F(G)|` — contradiction.
  have hy'F : y' ∈ Ch01.fitting G :=
    centralizer_fitting_le_fitting
      (Subgroup.mem_centralizer_iff.mpr fun f hf => (hcentF f hf).symm.eq)
  refine hqF ?_
  rw [← hy'ord, ← orderOf_mk_eq hy'F]
  exact orderOf_dvd_natCard _

/-! ## Gorenstein Ch. 12 §1 Theorem 1.5 and Corollary 1.6

> **Theorem 1.5.** If `G` is a solvable CN-group, then one of the following holds:
> (i) `G` is nilpotent; (ii) `G` is a Frobenius group whose complement is either cyclic or the
> direct product of a cyclic group of odd order and a generalized quaternion group;
> (iii) `G` is a 3-step group.
>
> **Corollary 1.6.** If `G` is a solvable CN-group and `O_p(G) ≠ 1`, then either `O_p(G)` is an
> `S_p`-subgroup of `G` or `G` is a 3-step group with respect to `p`.

Theorem 1.5 is stated below (`solvableCN_nilpotent_or_frobenius_or_threeStep`) and is the only
remaining `sorry` of this file; Corollary 1.6 is derived from it `sorry`-free.

The two cases of Theorem 1.5 that do *not* immediately hand back a 3-step group both produce a
normal nilpotent subgroup of index prime to `p` — all of `G` in case (i), the Fitting subgroup
in case (ii), whose index is the order of the Frobenius complement and hence prime to `|F(G)|`.
That shared step is isolated as `exists_sylow_eq_oPiCore_of_isNilpotent_normal_of_not_dvd_index`.
-/

/-- If a finite group `G` has a nilpotent normal subgroup `N` whose index is prime to `p`, then
`O_p(G)` is a Sylow `p`-subgroup of `G`.

Since `p ∤ [G : N]`, a Sylow `p`-subgroup `R` of `N` already has the full `p`-part of `|G|`, so
its image in `G` is Sylow.  `R` is normal in the nilpotent group `N`, hence characteristic in
`N`, hence normal in `G`; being a normal `p`-subgroup it lies in `O_p(G)`.  But `O_p(G)` is
itself a `p`-group containing the Sylow subgroup `R`, so maximality forces equality. -/
theorem exists_sylow_eq_oPiCore_of_isNilpotent_normal_of_not_dvd_index
    [Finite G] {p : ℕ} [Fact p.Prime] {N : Subgroup G} [N.Normal] [Group.IsNilpotent ↥N]
    (hidx : ¬ p ∣ N.index) :
    ∃ P : Sylow p G, (P : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G := by
  classical
  -- The `p`-part of `|G|` is already attained inside `N`.
  have hfact : (Nat.card ↥N).factorization p = (Nat.card G).factorization p := by
    have hmul : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p ↥N))
  haveI hRnormal : (R : Subgroup ↥N).Normal := Ch01.Sylow.normal_of_isNilpotent R
  haveI hRchar : (R : Subgroup ↥N).Characteristic := Sylow.characteristic_of_normal R hRnormal
  set Rmap : Subgroup G := (R : Subgroup ↥N).map N.subtype with hRmapdef
  haveI hRmapNormal : Rmap.Normal := normal_map_subtype_of_characteristic hRchar
  have hRpg : IsPGroup p ↥Rmap := R.isPGroup'.map N.subtype
  have hRcard : Nat.card ↥Rmap = p ^ (Nat.card G).factorization p := by
    rw [hRmapdef, Subgroup.card_map_of_injective N.subtype_injective, R.card_eq_multiplicity,
      hfact]
  -- `Rmap` is a Sylow `p`-subgroup of `G`.
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow hRpg
  have hRP : Rmap = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hPle
      (le_of_eq (P.card_eq_multiplicity.trans hRcard.symm))
  -- A normal `p`-subgroup lies in `O_p(G)`, which is itself a `p`-group.
  have hle : Rmap ≤ Ch03.oPiCore ({p} : Set ℕ) G :=
    (Ch04.isPiGroup_singleton_of_isPGroup hRpg).le_oPiCore
  have hOp : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  exact ⟨P, (P.is_maximal' hOp (hRP ▸ hle)).symm⟩

/-- **Gorenstein Ch. 12 §1 Theorem 1.5**, in the form Corollary 1.6 consumes.

A solvable CN-group is nilpotent, or a Frobenius group with kernel `F(G)`, or a 3-step group
with respect to some prime.

**Book-strength debt.**  Gorenstein's clause (ii) additionally pins the Frobenius complement
down to "cyclic, or the direct product of a cyclic group of odd order and a generalized
quaternion group" (his Theorem 1.3.1(ii)).  That refinement is omitted here because the
repository has no `IsGeneralizedQuaternion` predicate yet and Corollary 1.6 does not consume it;
stating the weaker disjunct keeps this `sorry` conservative.  Restoring the full clause is
tracked in issue 9133.

**Status: not yet proved.**  Gorenstein's argument sets `F = F(G)` and, when `G ≠ F`, takes a
Hall `π(F)'`-subgroup `A` (`Ch03.hall_exists_of_piSeparable`).  Lemma 1.2
(`commute_of_cn_of_commute_ne_one`, proved above) shows no nonidentity element of `A`
centralizes a nonidentity element of `F`, so `FA` is Frobenius; a second application of
Lemma 1.2 shows `A` is nilpotent, and `π(F)` is then shown to be a single prime unless
`G = FA`.  Beyond Lemma 1.2, Hall's theorem and `C_G(F(G)) ≤ F(G)` (Gorenstein Thm 6.1.3, now
available here as `centralizer_fitting_le_fitting`), the proof still needs, neither of which is
in the repository at the required strength:

1. Gorenstein Thm 10.3.1 (iv)/(v)/(vi) on Frobenius complements — of the three, "a subgroup of
   order `q · r` is cyclic" and the metacyclic structure (with Thm 7.6.2) are **absent**;
   `Ch06.isZGroup_of_isFrobeniusAction_of_odd`,
   `Ch06.sylow_isCyclic_or_two_quaternion_of_frobeniusAction` and
   `Ch06.IsFrobeniusAction.unique_involution` cover the rest.
2. Gorenstein Lemma 10.1.3, that a fixed-point-free automorphism of `K` induces a fixed-point-free
   automorphism of `K/F` for an invariant `F`.  **Absent.**

Both are substantive gaps on the path to Corollary 1.6.  Gorenstein Thm 1.3.1(ii) (the structure
of a group all of whose Sylow subgroups are cyclic or generalized quaternion) is also absent, but
is needed only to retire the book-strength debt recorded above.  (An earlier revision of this list
also named
Gorenstein Thm 5.3.5, the coprime-action factorization `K = [R,K] · C_K(R)`, as absent; it is
in fact present as `OddOrder.BG.Ch3.S13.subgroup_coprime_decomposition`, and Gorenstein's proof
of Theorem 1.5 does not use it.) -/
theorem solvableCN_nilpotent_or_frobenius_or_threeStep [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G))) :
    Group.IsNilpotent G ∨
      (∃ A : Subgroup G, Ch06.IsFrobeniusGroup G (Ch01.fitting G) A) ∨
      (∃ q : ℕ, q.Prime ∧ IsThreeStepGroup G q) := by
  sorry

/-- **Gorenstein Ch. 12 §1 Corollary 1.6**: for a solvable CN-group `G` with `O_p(G) ≠ 1`,
either `O_p(G)` is a Sylow `p`-subgroup of `G`, or `G` is a 3-step group with respect to `p`.

Bender--Glauberman Appendix D uses this contrapositively (Lemma D.1): when `O_p(M) ≠ 1` is *not*
Sylow in `M`, `M` is a 3-step group, and then only `IsThreeStepGroup.oPiCore_pPrime_eq_bot` and
`IsThreeStepGroup.isPGroup_quotient` / `nontrivial_quotient` are consumed — all three of which
are proved above, `sorry`-free.

Derived from `solvableCN_nilpotent_or_frobenius_or_threeStep` (Theorem 1.5) by dispatching its
three cases:

* `G` nilpotent — apply the index lemma with `N = ⊤`;
* `G` Frobenius with kernel `F(G)` — the index of `F(G)` is the order of the complement, which
  is prime to `|F(G)|`, and `p` divides `|F(G)|` because `1 ≠ O_p(G) ≤ F(G)`;
* `G` a 3-step group with respect to `q` — then `q = p`, since a 3-step group with respect to
  `q` has `O_{q'}(G) = 1` (`oPiCore_pPrime_eq_bot`) while `O_p(G) ≠ 1`. -/
theorem oPiCore_isSylow_or_isThreeStepGroup [Finite G] {p : ℕ} [Fact p.Prime] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    (hne : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥) :
    (∃ P : Sylow p G, (P : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G) ∨
      IsThreeStepGroup G p := by
  classical
  -- `O_p(G)` is a nontrivial `p`-group, so `p` divides its order.
  have hOp : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  have hpdvdOp : p ∣ Nat.card ↥(Ch03.oPiCore ({p} : Set ℕ) G) := by
    obtain ⟨n, hn⟩ := hOp.exists_card_eq
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hn)) hne
    · exact hn ▸ dvd_pow_self p hpos.ne'
  rcases solvableCN_nilpotent_or_frobenius_or_threeStep hCN with hnil | ⟨A, hFrob⟩ | ⟨q, hq, h3⟩
  · -- (i) `G` nilpotent: take `N = ⊤`, of index `1`.
    haveI := hnil
    exact Or.inl (exists_sylow_eq_oPiCore_of_isNilpotent_normal_of_not_dvd_index
      (N := (⊤ : Subgroup G))
      (by rw [Subgroup.index_top]; exact Nat.Prime.not_dvd_one Fact.out))
  · -- (ii) `G` Frobenius with kernel `F(G)`: `[G : F(G)] = |A|` is prime to `p`.
    refine Or.inl (exists_sylow_eq_oPiCore_of_isNilpotent_normal_of_not_dvd_index
      (N := Ch01.fitting G) ?_)
    have hindex : (Ch01.fitting G).index = Nat.card ↥A :=
      hFrob.isComplement.symm.index_eq_card
    have hleF : Ch03.oPiCore ({p} : Set ℕ) G ≤ Ch01.fitting G := by
      haveI : Group.IsNilpotent ↥(Ch03.oPiCore ({p} : Set ℕ) G) := hOp.isNilpotent
      exact Ch01.nilpotent_normal_le_fitting
    have hpF : p ∣ Nat.card ↥(Ch01.fitting G) :=
      hpdvdOp.trans (Subgroup.card_dvd_of_le hleF)
    have hcop : Nat.Coprime (Nat.card ↥(Ch01.fitting G)) (Nat.card ↥A) :=
      hFrob.coprime_card_kernel_complement
    rw [hindex]
    intro hpA
    exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hpF hpA))
  · -- (iii) `G` a 3-step group with respect to `q`: necessarily `q = p`.
    haveI : Fact q.Prime := ⟨hq⟩
    rcases eq_or_ne q p with rfl | hqp
    · exact Or.inr h3
    · exfalso
      refine hne (le_bot_iff.mp ?_)
      rw [← h3.oPiCore_pPrime_eq_bot]
      refine Ch03.Subgroup.IsPiGroup.le_oPiCore (π := {r : ℕ | r ≠ q}) ?_
      intro r hr
      have hrp := Ch03.oPiCore.isPiGroup ({p} : Set ℕ) (G := G) r hr
      simp only [Set.mem_singleton_iff] at hrp
      subst hrp
      exact Ne.symm hqp

end OddOrder.GroupTheory
