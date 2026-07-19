/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch06_FrobeniusActions.Main
import OddOrder.Isaacs.Ch06_FrobeniusActions.OddComplement
import OddOrder.Isaacs.Ch04_Commutators.Main.ThreeSubgroups
import OddOrder.GroupTheory.SubgroupInAmbient
import OddOrder.GroupTheory.FittingSelfCentralizing
import OddOrder.GroupTheory.NilpotentCoprimeCommute
import OddOrder.GroupTheory.FixedPointFreeConjugation
import OddOrder.GroupTheory.SylowCovering

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

/-! ## Step 3 of Theorem 1.5: `π(F(G))` is a single prime

Once `G ≠ F(G) A`, Gorenstein rules out `|π(F(G))| ≥ 2` by showing that each `p ∈ π(F(G))` with
a nontrivial `p'`-part in `F(G)` already has `O_p(G)` Sylow — so that `F(G)` would be a Hall
`π`-subgroup and `G = F(G) A` after all. -/

/-- A subgroup of a subgroup with nilpotent carrier is nilpotent. -/
theorem isNilpotent_of_le_of_isNilpotent {H K : Subgroup G}
    (hHK : H ≤ K) (hK : Group.IsNilpotent ↥K) : Group.IsNilpotent ↥H := by
  haveI := hK
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hHK)

/-- **In a CN-group, a subgroup with nontrivial centre is nilpotent.**

For `1 ≠ z ∈ Z(A)` we have `A ≤ C_G(z)`, and `C_G(z)` is nilpotent by the CN hypothesis.

This is the last move of Gorenstein's argument that the Hall `π(F(G))'`-subgroup `A` of
Theorem 1.5 is nilpotent, and it reduces that claim to `Z(A) ≠ 1`.  Gorenstein gets `Z(A) ≠ 1`
from the Frobenius-complement structure of `A` (his Theorem 10.3.1(iv)/(v)), which is the part
still missing from this repository. -/
theorem isNilpotent_of_centerIn_ne_bot [Finite G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {A : Subgroup G} (hZ : centerIn A ≠ ⊥) : Group.IsNilpotent ↥A := by
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz1 : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  refine isNilpotent_of_le_of_isNilpotent (fun a ha => ?_) (hCN (z : G) hz1)
  exact Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_centerIn ha z.2).eq

/-- **Gorenstein Ch. 12 §1, Theorem 1.5, step 3.**

In a CN-group, if `O_p(G) ≠ 1` and `F(G)` contains a nontrivial normal subgroup `N` of order
prime to `p`, then `O_p(G)` is already a Sylow `p`-subgroup of `G`.

`O_p(G)` centralizes `N` — both lie in the nilpotent `F(G)` and their orders are coprime — so
Lemma 1.2 promotes this to "a whole Sylow `p`-subgroup `P` of `G` centralizes `N`", `N` being
generated by its Sylow subgroups.  Then `P ≤ C := C_G(N)`, which is normal in `G` and nilpotent
(it sits inside the nilpotent `C_G(z)` for any `1 ≠ z ∈ N`); so `P`, a Sylow `p`-subgroup of the
nilpotent `C`, is normal and hence characteristic in `C`, and therefore normal in `G`.  A normal
`p`-subgroup lies in `O_p(G)`, so `P = O_p(G)`.

Gorenstein applies this with `N = O_{p'}(F(G))`, concluding that if every `p ∈ π(F(G))` had a
nontrivial `p'`-part then `F(G)` would be a Hall subgroup and `G = F(G) A`. -/
theorem exists_sylow_eq_oPiCore_of_normal_pPrime_le_fitting
    [Finite G] {p : ℕ} [Fact p.Prime]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    (hOpne : Ch03.oPiCore ({p} : Set ℕ) G ≠ ⊥)
    {N : Subgroup G} [N.Normal] (hNbot : N ≠ ⊥) (hNF : N ≤ Ch01.fitting G)
    (hpN : ¬ p ∣ Nat.card ↥N) :
    ∃ P : Sylow p G, (P : Subgroup G) = Ch03.oPiCore ({p} : Set ℕ) G := by
  classical
  have hOpPG : IsPGroup p ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
    Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))
  have hOpF : Ch03.oPiCore ({p} : Set ℕ) G ≤ Ch01.fitting G := by
    haveI : Group.IsNilpotent ↥(Ch03.oPiCore ({p} : Set ℕ) G) := hOpPG.isNilpotent
    exact Ch01.nilpotent_normal_le_fitting
  haveI hNnil : Group.IsNilpotent ↥N := isNilpotent_of_le_of_isNilpotent hNF inferInstance
  -- Step 1: `O_p(G)` centralizes `N`, both lying in the nilpotent `F(G)` with coprime orders.
  have hOpcentN : ∀ a ∈ Ch03.oPiCore ({p} : Set ℕ) G, ∀ n ∈ N, Commute a n := by
    intro a ha n hn
    refine commute_of_mem_fitting_of_coprime_orderOf (hOpF ha) (hNF hn) ?_
    obtain ⟨k, hk⟩ := hOpPG ⟨a, ha⟩
    have hadvd : orderOf a ∣ p ^ k := by
      rw [← orderOf_mk_eq ha]; exact orderOf_dvd_of_pow_eq_one hk
    have hnp : ¬ p ∣ orderOf n := fun hdvd =>
      hpN (hdvd.trans (by rw [← orderOf_mk_eq hn]; exact orderOf_dvd_natCard _))
    exact Nat.Coprime.coprime_dvd_left hadvd
      (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp))
  -- Step 2: Lemma 1.2 upgrades this to a whole Sylow `p`-subgroup of `G`.
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hOpne
  have hx1 : (x : G) ≠ 1 := fun h => hxne (Subtype.ext h)
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hOpP : Ch03.oPiCore ({p} : Set ℕ) G ≤ (P : Subgroup G) := by
    rw [Ch04.oPiCore_singleton_eq_opCore]; exact Ch01.opCore_le P
  have hPcentN : ∀ a ∈ (P : Subgroup G), ∀ n ∈ N, Commute a n := by
    intro a ha n hn
    have hmem : (⟨n, hn⟩ : ↥N) ∈ ⨆ r : (Nat.card ↥N).primeFactors,
        ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N) := by
      rw [Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥N]; trivial
    refine Subgroup.iSup_induction _ (C := fun w : ↥N => Commute a (w : G)) hmem ?_
      (Commute.one_right _) (fun u v hu hv => hu.mul_right hv)
    rintro ⟨r, hr⟩ w hw
    haveI : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
    have hrp : (r : ℕ) ≠ p := fun h => hpN (h ▸ Nat.dvd_of_mem_primeFactors hr)
    rcases eq_or_ne (w : G) 1 with hw1 | hw1
    · rw [hw1]; exact Commute.one_right a
    · have hQpg : IsPGroup (r : ℕ)
          ↥(((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N).map N.subtype) :=
        (default : Sylow (r : ℕ) ↥N).isPGroup'.map N.subtype
      have hwQ : (w : G) ∈ ((default : Sylow (r : ℕ) ↥N) : Subgroup ↥N).map N.subtype :=
        ⟨w, hw, rfl⟩
      exact commute_of_cn_of_commute_ne_one hCN (Ne.symm hrp) P.isPGroup' hQpg
        (hOpP x.2) hx1 hwQ hw1 (hOpcentN _ x.2 _ w.2) a ha (w : G) hwQ
  -- Step 3: `C = C_G(N)` is normal and nilpotent, and contains `P`.
  have hPC : (P : Subgroup G) ≤ Subgroup.centralizer (N : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun n hn => (hPcentN a ha n hn).symm.eq
  obtain ⟨z, hzne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbot
  have hz1 : (z : G) ≠ 1 := fun h => hzne (Subtype.ext h)
  haveI hCnil : Group.IsNilpotent ↥(Subgroup.centralizer (N : Set G)) :=
    isNilpotent_of_le_of_isNilpotent
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr z.2)) (hCN (z : G) hz1)
  -- Step 4: `P` is Sylow in the nilpotent `C`, hence characteristic there, hence normal in `G`.
  haveI hPn : ((P.subtype hPC : Sylow p ↥(Subgroup.centralizer (N : Set G))) :
      Subgroup ↥(Subgroup.centralizer (N : Set G))).Normal :=
    Ch01.Sylow.normal_of_isNilpotent _
  haveI hPc : ((P.subtype hPC : Sylow p ↥(Subgroup.centralizer (N : Set G))) :
      Subgroup ↥(Subgroup.centralizer (N : Set G))).Characteristic :=
    Sylow.characteristic_of_normal _ hPn
  haveI hPnormal : (P : Subgroup G).Normal := by
    have hmap := normal_map_subtype_of_characteristic hPc
    rwa [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPC] at hmap
  -- Step 5: a normal `p`-subgroup lies in `O_p(G)`, so `P = O_p(G)`.
  exact ⟨P, le_antisymm (Ch04.isPiGroup_singleton_of_isPGroup P.isPGroup').le_oPiCore hOpP⟩

/-! ## Step 1 of Theorem 1.5: the setup

Gorenstein sets `F = F(G)`; if `G = F` then `G` is nilpotent and case (i) holds, and otherwise he
takes a Hall `π(F)'`-subgroup `A` (available since `G` is solvable) and shows `F A` is Frobenius.
The three lemmas here are the setup, the regular-action conclusion in the form
`Ch06.IsFrobeniusGroup` wants, and the bridge to case (ii). -/

/-- `F(G) = G` forces `G` nilpotent — case (i) of Theorem 1.5. -/
theorem isNilpotent_of_fitting_eq_top [Finite G] (h : Ch01.fitting G = ⊤) :
    Group.IsNilpotent G := by
  haveI : Group.IsNilpotent ↥(⊤ : Subgroup G) := h ▸ Ch01.fitting.isNilpotent (G := G)
  exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv

/-- A Hall `π(F(G))'`-subgroup acts on `F(G)` with no nonidentity fixed points.

This is `not_commute_of_coprime_orderOf_card_fitting` (Theorem 1.5, step 2) packaged in the form
`Ch06.IsFrobeniusGroup.conj_frobenius` expects: the Hall condition makes every element of `A`
have order prime to `|F(G)|`. -/
theorem conj_ne_of_isHallSubgroup_fitting_pPrime [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {A : Subgroup G}
    (hA : Ch03.IsHallSubgroup
      {r : ℕ | r ∉ (Nat.card ↥(Ch01.fitting G)).primeFactors} A) :
    ∀ a ∈ A, a ≠ 1 → ∀ n ∈ Ch01.fitting G, n ≠ 1 → a * n * a⁻¹ ≠ n := by
  intro a ha ha1 n hn hn1 hconj
  refine not_commute_of_coprime_orderOf_card_fitting hCN hn hn1 ha1 ?_ ?_
  · -- `|a|` is prime to `|F(G)|`: a common prime factor would have to lie in and out of `π(F)`.
    rw [Nat.Coprime]
    by_contra hne
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hne
    have hra : r ∣ Nat.card ↥A :=
      (hrdvd.trans (Nat.gcd_dvd_left _ _)).trans
        (by rw [← orderOf_mk_eq ha]; exact orderOf_dvd_natCard _)
    have hrF : r ∣ Nat.card ↥(Ch01.fitting G) := hrdvd.trans (Nat.gcd_dvd_right _ _)
    exact hA.1 r (Nat.mem_primeFactors.mpr ⟨hr, hra, Nat.card_pos.ne'⟩)
      (Nat.mem_primeFactors.mpr ⟨hr, hrF, Nat.card_pos.ne'⟩)
  · -- `Commute n a` is exactly the conjugation identity assumed for contradiction.
    have : a * n = n * a := by
      have := congrArg (· * a) hconj
      simpa [mul_assoc] using this
    exact this.symm

/-- **Case (ii) of Theorem 1.5**: if a Hall `π(F(G))'`-subgroup `A` complements `F(G)` in `G`,
then `G` is a Frobenius group with kernel `F(G)` and complement `A`. -/
theorem isFrobeniusGroup_fitting_of_isComplement [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {A : Subgroup G}
    (hA : Ch03.IsHallSubgroup
      {r : ℕ | r ∉ (Nat.card ↥(Ch01.fitting G)).primeFactors} A)
    (hcompl : Subgroup.IsComplement' (Ch01.fitting G) A)
    (hFne : Ch01.fitting G ≠ ⊥) (hAne : A ≠ ⊥) :
    Ch06.IsFrobeniusGroup G (Ch01.fitting G) A where
  isNormal := Ch01.fitting.normal G
  isComplement := hcompl
  ne_bot_kernel := hFne
  ne_bot_complement := hAne
  conj_frobenius := conj_ne_of_isHallSubgroup_fitting_pPrime hCN hA

/-! ## Steps 4-6 of Theorem 1.5: the case `G ⊋ F(G)A`

When `π(F(G))` has been reduced to a single prime `p` (step 3), Gorenstein passes to
`Ḡ = G/F` and shows `Ḡ` is a Frobenius group with kernel `O_{p'}(Ḡ)`.  The two lemmas here
supply the commuting obstructions that drive that endgame:

* `not_commute_of_not_dvd_orderOf_of_isPGroup_fitting` — **(†)** in `G` itself, no nontrivial
  `p'`-element commutes with a nontrivial `p`-element (a strengthening of step 2 from elements
  of `F` to arbitrary `p`-elements);
* `not_commute_mk_of_not_dvd_orderOf_of_isPGroup_fitting` — **(‡)** the same obstruction one
  floor up: in `Ḡ = G/F(G)`, the image of a `p'`-element commutes with no nontrivial
  `p`-element of `Ḡ`.  This is where Gorenstein's Lemma 10.1.3
  (`mem_of_inv_mul_conj_mem_of_fixedPointFree`) is consumed. -/

/-- **(†).**  In a finite solvable CN-group whose Fitting subgroup is a `p`-group, no
nontrivial element of order prime to `p` commutes with a nontrivial `p`-element.

If `x` (with `p ∤ |x|`) commuted with the `p`-element `k ≠ 1`, a power `x'` of `x` of prime
order `r ≠ p` still would; Lemma 1.2 then makes `x'` centralize a full Sylow `p`-subgroup
`P ⊇ F(G)`, so `x' ∈ C_G(F(G)) ≤ F(G)`, forcing `r = p` — absurd. -/
theorem not_commute_of_not_dvd_orderOf_of_isPGroup_fitting [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {p : ℕ} [Fact p.Prime] (hF : IsPGroup p ↥(Ch01.fitting G))
    {x k : G} (hx1 : x ≠ 1) (hxp : ¬ p ∣ orderOf x)
    (hk1 : k ≠ 1) (hkp : IsPGroup p ↥(Subgroup.zpowers k)) :
    ¬ Commute x k := by
  intro hxy
  -- A power `x'` of `x` of prime order `r ≠ p`.
  obtain ⟨r, hr, hrx⟩ := Nat.exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
  haveI : Fact r.Prime := ⟨hr⟩
  have hrp : r ≠ p := fun hc => hxp (hc ▸ hrx)
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers x)) r
    (by rw [Nat.card_zpowers]; exact hrx)
  set x' : G := (x₀ : G) with hx'def
  have hx'ord : orderOf x' = r := by
    rw [hx'def, ← hx₀]
    exact (orderOf_mk_eq x₀.2).symm
  have hx'1 : x' ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hx'ord
    exact hr.one_lt.ne' hx'ord.symm
  have hx'k : Commute x' k := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x₀.2
    rw [hx'def, ← hn]
    exact hxy.zpow_left n
  -- Lemma 1.2 with the Sylow `p`-subgroup containing `k`.
  obtain ⟨P, hkP⟩ := hkp.exists_le_sylow
  have hall := commute_of_cn_of_commute_ne_one hCN (Ne.symm hrp) P.isPGroup'
    (IsPGroup.of_card (by rw [Nat.card_zpowers, hx'ord, pow_one]))
    (hkP (Subgroup.mem_zpowers k)) hk1 (Subgroup.mem_zpowers x') hx'1 hx'k.symm
  -- `F(G) ≤ P`: the normal `p`-group `F(G)` lies in `O_p(G)`, the meet of the Sylows.
  have hFP : Ch01.fitting G ≤ (P : Subgroup G) := by
    refine ((Ch04.isPiGroup_singleton_of_isPGroup hF).le_oPiCore).trans ?_
    rw [Ch04.oPiCore_singleton_eq_opCore]
    exact Ch01.opCore_le P
  -- `x'` centralizes `F(G)`, hence lies in it; but its order is prime to `p`.
  have hx'F : x' ∈ Ch01.fitting G := by
    refine centralizer_fitting_le_fitting ?_
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hall f (hFP hf) x' (Subgroup.mem_zpowers x')).eq
  have hrF : r ∣ Nat.card ↥(Ch01.fitting G) := by
    rw [← hx'ord, ← orderOf_mk_eq hx'F]
    exact orderOf_dvd_natCard _
  obtain ⟨n, hn⟩ := hF.exists_card_eq
  rw [hn] at hrF
  exact hrp ((Nat.prime_dvd_prime_iff_eq hr Fact.out).mp (hr.dvd_of_dvd_pow hrF))

/-- **(‡).**  In a finite solvable CN-group `G` with `F := F(G)` a `p`-group, the image in
`G/F` of a nontrivial element `a` of order prime to `p` commutes with no nontrivial `p`-element
of `G/F`.

If `mk a` commuted with the `p`-element `u ≠ 1`, the preimage `K` of `⟨u⟩` would be a `p`-group
normalized by `a` on which `a` acts fixed-point-freely (by (†)); by descent
(`mem_of_inv_mul_conj_mem_of_fixedPointFree`, Gorenstein Lemma 10.1.3) the fixed coset of any
representative of `u` collapses, i.e. `u = 1`. -/
theorem not_commute_mk_of_not_dvd_orderOf_of_isPGroup_fitting [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {p : ℕ} [Fact p.Prime] (hF : IsPGroup p ↥(Ch01.fitting G))
    {a : G} (hap : ¬ p ∣ orderOf a)
    (ha1 : QuotientGroup.mk' (Ch01.fitting G) a ≠ 1)
    {u : G ⧸ Ch01.fitting G} (hu1 : u ≠ 1)
    (hup : IsPGroup p ↥(Subgroup.zpowers u)) :
    ¬ Commute (QuotientGroup.mk' (Ch01.fitting G) a) u := by
  intro hcomm
  have ha1' : a ≠ 1 := fun hc => ha1 (by rw [hc, map_one])
  -- The preimage `K` of `⟨u⟩` is a `p`-group containing `F(G)`.
  set K : Subgroup G := (Subgroup.zpowers u).comap (QuotientGroup.mk' (Ch01.fitting G))
    with hKdef
  have hFK : Ch01.fitting G ≤ K := by
    intro f hf
    rw [hKdef, Subgroup.mem_comap, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff f).mpr hf]
    exact Subgroup.one_mem _
  have hKp : IsPGroup p ↥K := by
    refine hup.comap_of_ker_isPGroup _ ?_
    rw [QuotientGroup.ker_mk']
    exact hF
  -- `a` normalizes `K` because `mk a` centralizes `⟨u⟩`.
  have haK : ∀ f ∈ K, a * f * a⁻¹ ∈ K := by
    intro f hfK
    rw [hKdef, Subgroup.mem_comap] at hfK ⊢
    rw [map_mul, map_mul, map_inv]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hfK
    rw [← hn, (hcomm.zpow_right n).eq]
    simpa [mul_assoc] using Subgroup.zpow_mem _ (Subgroup.mem_zpowers u) n
  -- `a` acts fixed-point-freely on `K`, by (†).
  have hfpf : ∀ f ∈ K, a * f * a⁻¹ = f → f = 1 := by
    intro f hfK hfix
    by_contra hf1
    refine not_commute_of_not_dvd_orderOf_of_isPGroup_fitting hCN hF ha1' hap hf1
      (hKp.to_le (Subgroup.zpowers_le.mpr hfK)) ?_
    have h := congrArg (· * a) hfix
    have hc : a * f = f * a := by simpa [mul_assoc] using h
    exact hc
  -- A representative of `u` has its coset fixed by `a`; descend (Lemma 10.1.3).
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk'_surjective (Ch01.fitting G) u
  have hk₀K : k₀ ∈ K := by
    rw [hKdef, Subgroup.mem_comap, hk₀]
    exact Subgroup.mem_zpowers u
  have hmem : k₀⁻¹ * (a * k₀ * a⁻¹) ∈ Ch01.fitting G := by
    have h1 : (QuotientGroup.mk' (Ch01.fitting G)) (k₀⁻¹ * (a * k₀ * a⁻¹)) = 1 := by
      simp only [map_mul, map_inv, hk₀]
      rw [hcomm.eq]
      group
    rwa [← QuotientGroup.ker_mk' (Ch01.fitting G), MonoidHom.mem_ker]
  have hk₀F : k₀ ∈ Ch01.fitting G :=
    mem_of_inv_mul_conj_mem_of_fixedPointFree hFK
      (fun f hf => (Ch01.fitting.normal G).conj_mem f hf a) hfpf hk₀K hmem
  exact hu1 (by rw [← hk₀, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hk₀F)

/-- **Steps 5-6 of Theorem 1.5**: in a finite CN-group, a subgroup `A` of **odd** order acting
fixed-point-freely by conjugation on a nontrivial normal subgroup `F` is **cyclic**.

Gorenstein deduces nilpotency of `A` from its metacyclic structure (Thm 10.3.1(iv), 7.6.2); we
shortcut through the repository's Isaacs 6.19 inventory instead.  `A` is a Z-group
(`isZGroup_of_isFrobeniusAction_of_odd`) with a *unique* subgroup of each prime order
(`eq_of_card_prime_of_isFrobeniusAction_of_odd`), so that subgroup is normal and contained in
every Sylow subgroup for its prime.  For distinct primes `q, r ∣ |A|` the unique subgroups
commute elementwise (normal and disjoint), and Lemma 1.2 upgrades that single commuting pair to
*Sylow-q commutes with Sylow-r elementwise*.  Hence the centralizer of a fixed Sylow `q`-subgroup
`Q₀` contains a Sylow subgroup for every prime, so it is all of `A`; thus `Q₀ ≤ Z(A) ≠ 1`, the CN
hypothesis makes `A` nilpotent (`isNilpotent_of_centerIn_ne_bot`), and a nilpotent Z-group is
cyclic (mathlib). -/
theorem isCyclic_of_cn_of_conj_frobenius_of_odd [Finite G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G)))
    {F A : Subgroup G} [F.Normal] (hFne : F ≠ ⊥)
    (hfpf : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ F, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hodd : Odd (Nat.card ↥A)) : IsCyclic ↥A := by
  classical
  rcases eq_or_ne A ⊥ with rfl | hAne
  · haveI : Subsingleton ↥(⊥ : Subgroup G) :=
      (Nat.card_eq_one_iff_unique.mp Subgroup.card_bot).1
    exact isCyclic_of_subsingleton
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
  -- The conjugation action of `A` on `F` is a Frobenius action.
  letI : MulDistribMulAction ↥A ↥F :=
    MulDistribMulAction.compHom ↥F ((MulAut.conjNormal (H := F)).comp A.subtype)
  haveI : Nontrivial ↥F := (Subgroup.nontrivial_iff_ne_bot F).mpr hFne
  have hact : Ch06.IsFrobeniusAction ↥A ↥F := by
    intro a ha n hn hfix
    have haG : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hnG : (n : G) ≠ 1 := fun h => hn (Subtype.ext h)
    exact hfpf (a : G) a.2 haG (n : G) n.2 hnG (Subtype.ext_iff.mp hfix)
  haveI hZ : IsZGroup ↥A := Ch06.isZGroup_of_isFrobeniusAction_of_odd hact hodd
  -- A prime `q ∣ |A|` and a Sylow `q`-subgroup `Q₀`.
  obtain ⟨q, hq, hqA⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := ↥A)).ne'
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨Q₀⟩ := (inferInstance : Nonempty (Sylow q ↥A))
  -- A subgroup of prime order `r ∣ |A|` lies in every Sylow `r`-subgroup: the Sylow subgroup
  -- contains *an* order-`r` subgroup (Cauchy), and order-`r` subgroups are unique (Isaacs 6.19).
  have hle_sylow : ∀ (r : ℕ) [Fact r.Prime], r ∣ Nat.card ↥A → ∀ (S : Sylow r ↥A)
      (R : Subgroup ↥A), Nat.card ↥R = r → R ≤ (S : Subgroup ↥A) := by
    intro r hrFact hrA S R hR
    have hr : r.Prime := hrFact.out
    have hrS : r ∣ Nat.card ↥(S : Subgroup ↥A) := by
      rw [S.card_eq_multiplicity]
      exact dvd_pow_self r
        (Nat.Prime.factorization_pos_of_dvd hr Nat.card_pos.ne' hrA).ne'
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S : Subgroup ↥A)) r hrS
    set R' : Subgroup ↥A := (Subgroup.zpowers y).map (S : Subgroup ↥A).subtype with hR'def
    have hR'card : Nat.card ↥R' = r := by
      rw [hR'def, Nat.card_congr (Subgroup.equivMapOfInjective _ _
        Subtype.coe_injective).toEquiv.symm, Nat.card_zpowers, hy]
    have hRR' : R = R' :=
      Ch06.eq_of_card_prime_of_isFrobeniusAction_of_odd hact hodd hr hR hR'card
    rw [hRR', hR'def]
    exact Subgroup.map_subtype_le _
  -- Distinct-prime Sylow subgroups of `A` commute with `Q₀` elementwise, via Lemma 1.2 in `G`.
  have hSylowComm : ∀ (r : ℕ), r.Prime → r ≠ q → r ∣ Nat.card ↥A → ∀ (S : Sylow r ↥A),
      (S : Subgroup ↥A) ≤ Subgroup.centralizer ((Q₀ : Subgroup ↥A) : Set ↥A) := by
    intro r hr hrq hrA S
    haveI : Fact r.Prime := ⟨hr⟩
    -- The unique order-`q` and order-`r` subgroups, generated by Cauchy elements.
    obtain ⟨aq, haq⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q hqA
    obtain ⟨ar, har⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) r hrA
    have hRqcard : Nat.card ↥(Subgroup.zpowers aq) = q := by rw [Nat.card_zpowers, haq]
    have hRrcard : Nat.card ↥(Subgroup.zpowers ar) = r := by rw [Nat.card_zpowers, har]
    haveI hRqn : (Subgroup.zpowers aq).Normal :=
      Ch06.normal_of_card_prime_of_isFrobeniusAction_of_odd hact hodd hq hRqcard
    haveI hRrn : (Subgroup.zpowers ar).Normal :=
      Ch06.normal_of_card_prime_of_isFrobeniusAction_of_odd hact hodd hr hRrcard
    -- Normal and disjoint, so `aq` and `ar` commute.
    have hdisj : Disjoint (Subgroup.zpowers aq) (Subgroup.zpowers ar) := by
      rw [disjoint_iff]
      have hcoprs : Nat.Coprime q r := (Nat.coprime_primes hq hr).mpr (Ne.symm hrq)
      have hdvdq : Nat.card ↥(Subgroup.zpowers aq ⊓ Subgroup.zpowers ar) ∣ q :=
        hRqcard ▸ Subgroup.card_dvd_of_le inf_le_left
      have hdvdr : Nat.card ↥(Subgroup.zpowers aq ⊓ Subgroup.zpowers ar) ∣ r :=
        hRrcard ▸ Subgroup.card_dvd_of_le inf_le_right
      exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp (hcoprs ▸ Nat.dvd_gcd hdvdq hdvdr))
    have hcpair : Commute aq ar :=
      Subgroup.commute_of_normal_of_disjoint _ _ hRqn hRrn hdisj aq ar
        (Subgroup.mem_zpowers aq) (Subgroup.mem_zpowers ar)
    -- Nontriviality of the Cauchy elements, in `↥A` and in `G`.
    have haq1 : aq ≠ 1 := by
      intro h; rw [h, orderOf_one] at haq; exact hq.one_lt.ne' haq.symm
    have har1 : ar ≠ 1 := by
      intro h; rw [h, orderOf_one] at har; exact hr.one_lt.ne' har.symm
    have haqG : (aq : G) ≠ 1 := fun h => haq1 (Subtype.ext h)
    have harG : (ar : G) ≠ 1 := fun h => har1 (Subtype.ext h)
    -- The unique prime-order subgroups sit inside the given Sylow subgroups.
    have haqQ₀ : aq ∈ (Q₀ : Subgroup ↥A) :=
      hle_sylow q hqA Q₀ (Subgroup.zpowers aq) hRqcard (Subgroup.mem_zpowers aq)
    have harS : ar ∈ (S : Subgroup ↥A) :=
      hle_sylow r hrA S (Subgroup.zpowers ar) hRrcard (Subgroup.mem_zpowers ar)
    -- Lemma 1.2 in `G`, with the two Sylow subgroups pushed along `A.subtype`.
    have hallG := commute_of_cn_of_commute_ne_one hCN (Ne.symm hrq)
      (Q₀.isPGroup'.map A.subtype) (S.isPGroup'.map A.subtype)
      (Subgroup.mem_map_of_mem A.subtype haqQ₀) haqG
      (Subgroup.mem_map_of_mem A.subtype harS) harG
      (show Commute ((aq : G)) ((ar : G)) from congrArg A.subtype hcpair.eq)
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact Subtype.ext ((hallG (c : G) (Subgroup.mem_map_of_mem A.subtype hc)
      (b : G) (Subgroup.mem_map_of_mem A.subtype hb)).eq)
  -- The centralizer of `Q₀` contains a Sylow subgroup for every prime, hence is all of `A`.
  have hC : Subgroup.centralizer ((Q₀ : Subgroup ↥A) : Set ↥A) = ⊤ := by
    refine eq_top_of_forall_exists_sylow_le (fun r hr => ?_)
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow r ↥A))
    by_cases hrA : r ∣ Nat.card ↥A
    · rcases eq_or_ne r q with rfl | hrq
      · -- `r = q`: `Q₀` is cyclic (Z-group), hence abelian, and centralizes itself.
        refine ⟨Q₀, fun x hx => ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        letI : CommGroup ↥(Q₀ : Subgroup ↥A) := IsCyclic.commGroup
        exact congrArg (Subgroup.subtype _)
          (mul_comm (⟨c, hc⟩ : ↥(Q₀ : Subgroup ↥A)) ⟨x, hx⟩)
      · exact ⟨S, hSylowComm r hr hrq hrA S⟩
    · -- `r ∤ |A|`: the Sylow `r`-subgroup is trivial.
      refine ⟨S, fun x hx => ?_⟩
      have hcard : Nat.card ↥(S : Subgroup ↥A) = 1 := by
        rcases S.isPGroup'.card_eq_or_dvd with h1 | hd
        · exact h1
        · exact absurd (hd.trans (Subgroup.card_subgroup_dvd_card S.toSubgroup)) hrA
      have hx1 : x = 1 := by
        haveI : Subsingleton ↥(S : Subgroup ↥A) := (Nat.card_eq_one_iff_unique.mp hcard).1
        exact congrArg (Subgroup.subtype _)
          (Subsingleton.elim (⟨x, hx⟩ : ↥(S : Subgroup ↥A)) 1)
      rw [hx1]
      exact Subgroup.one_mem _
  -- A Cauchy element of order `q` is nontrivial and central: `Z(A) ≠ 1`.
  obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q hqA
  have ha₀1 : a₀ ≠ 1 := by
    intro h; rw [h, orderOf_one] at ha₀; exact hq.one_lt.ne' ha₀.symm
  have ha₀Q : a₀ ∈ (Q₀ : Subgroup ↥A) :=
    hle_sylow q hqA Q₀ (Subgroup.zpowers a₀)
      (by rw [Nat.card_zpowers, ha₀]) (Subgroup.mem_zpowers a₀)
  have ha₀c : a₀ ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ((Q₀ : Subgroup ↥A) : Set ↥A) :=
      hC ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp hg a₀ ha₀Q).symm
  -- CN nilpotency from the nontrivial centre, then mathlib: nilpotent Z-group ⟹ cyclic.
  have hcin : centerIn A ≠ ⊥ := by
    intro hbot
    have hmem : (a₀ : G) ∈ centerIn A := ⟨a₀, ha₀c, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha₀1 (Subtype.ext hmem)
  haveI := isNilpotent_of_centerIn_ne_bot hCN hcin
  infer_instance

/-! ### Small counting helpers for the endgame -/

/-- `|H ⊔ N| * |H ⊓ N| = |H| * |N|` for `N` normal (second isomorphism theorem). -/
theorem card_sup_mul_card_inf_eq [Finite G] (H N : Subgroup G) [N.Normal] :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card ↥H * Nat.card ↥N := by
  have h1 : Nat.card ↥H =
      Nat.card (↥H ⧸ (N.subgroupOf H)) * Nat.card ↥(N.subgroupOf H) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card ↥(H ⊔ N) =
      Nat.card (↥(H ⊔ N) ⧸ (N.subgroupOf (H ⊔ N))) * Nat.card ↥(N.subgroupOf (H ⊔ N)) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card ↥(N.subgroupOf (H ⊔ N)) = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have h4 : Nat.card ↥(N.subgroupOf H) = Nat.card ↥(H ⊓ N) :=
    Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, x.2⟩, fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
      fun _ => rfl, fun _ => rfl⟩
  have h5 : Nat.card (↥H ⧸ (N.subgroupOf H)) =
      Nat.card (↥(H ⊔ N) ⧸ (N.subgroupOf (H ⊔ N))) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient H N).toEquiv
  rw [h2, h3, ← h4, ← h5, h1]
  ring

/-- A positive natural number all of whose prime factors are `p` is a power of `p`. -/
theorem eq_pow_factorization_of_primeFactors_subset {n p : ℕ} (hn : n ≠ 0)
    (h : n.primeFactors ⊆ {p}) : n = p ^ n.factorization p := by
  rcases Finset.subset_singleton_iff.mp h with h0 | h1
  · rcases Nat.primeFactors_eq_empty.mp h0 with rfl | rfl
    · exact absurd rfl hn
    · simp
  · conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn,
      Nat.prod_factorization_eq_prod_primeFactors, h1, Finset.prod_singleton]

/-- A `p`-group has `O_p = ⊤`. -/
theorem oPiCore_singleton_eq_top_of_isPGroup {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (hX : IsPGroup p X) : Ch03.oPiCore ({p} : Set ℕ) X = ⊤ := by
  rw [eq_top_iff]
  have htop : IsPGroup p ↥(⊤ : Subgroup X) := by
    intro x
    obtain ⟨n, hn⟩ := hX (x : X)
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  exact (Ch04.isPiGroup_singleton_of_isPGroup htop).le_oPiCore

/-! ### Helpers for the endgame of Theorem 1.5

Three general-purpose lemmas: transport of a subgroup onto its image under a homomorphism whose
kernel it misses, the fact that commutators centralize a finite cyclic normal subgroup
(conjugation lands in the abelian automorphism group), and the packaging of a fixed-point-free
action as a Frobenius-group structure on the join `A ⊔ F`. -/

open scoped commutatorElement

/-- A subgroup meeting the kernel of `f` trivially maps isomorphically onto its image. -/
noncomputable def mulEquivMapOfInfKerEqBot {H : Type*} [Group H] (f : G →* H) (A : Subgroup G)
    (h : A ⊓ f.ker = ⊥) : ↥A ≃* ↥(A.map f) :=
  (MonoidHom.ofInjective (f := f.restrict A) (by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.ker_restrict] at hx
    have hxk : (x : G) ∈ A ⊓ f.ker := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at hxk
    simpa [Subgroup.mem_bot] using Subtype.ext hxk)).trans
    (MulEquiv.subgroupCongr (f.restrict_range (K := A)))

/-- Every commutator centralizes a finite cyclic normal subgroup: conjugation is a homomorphism
into its automorphism group, which is abelian (`IsCyclic.mulAutMulEquiv`). -/
theorem commutatorElement_mem_centralizer_of_isCyclic_normal
    {N : Subgroup G} [N.Normal] [Finite ↥N] (hN : IsCyclic ↥N) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.centralizer (N : Set G) := by
  haveI := hN
  have hcomm : MulAut.conjNormal (H := N) x * MulAut.conjNormal (H := N) y =
      MulAut.conjNormal (H := N) y * MulAut.conjNormal (H := N) x :=
    (IsCyclic.mulAutMulEquiv ↥N).injective (by rw [map_mul, map_mul, mul_comm])
  have hone : MulAut.conjNormal (H := N) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have happ := congrArg (fun ψ : MulAut ↥N => ((ψ ⟨n, hn⟩ : ↥N) : G)) hone
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at happ
  calc n * ⁅x, y⁆ = (⁅x, y⁆ * n * ⁅x, y⁆⁻¹) * ⁅x, y⁆ := by rw [happ]
    _ = ⁅x, y⁆ * n := by group

/-- A fixed-point-free conjugation action of `A` on a normal subgroup `F` disjoint from it
packages as a Frobenius-group structure on the join `A ⊔ F`, with kernel `F` and
complement `A`. -/
theorem isFrobeniusGroup_subgroupOf_sup [Finite G] {F A : Subgroup G} [F.Normal]
    (hinf : A ⊓ F = ⊥) (hFne : F ≠ ⊥) (hAne : A ≠ ⊥)
    (hfpf : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ F, n ≠ 1 → a * n * a⁻¹ ≠ n) :
    Ch06.IsFrobeniusGroup ↥(A ⊔ F) (F.subgroupOf (A ⊔ F)) (A.subgroupOf (A ⊔ F)) where
  isNormal := Subgroup.Normal.subgroupOf ‹F.Normal› _
  isComplement := by
    refine Subgroup.isComplement'_of_card_mul_and_disjoint ?_ ?_
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : F ≤ A ⊔ F)).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ F)).toEquiv]
      have h := card_sup_mul_card_inf_eq A F
      rw [hinf, Subgroup.card_bot, mul_one] at h
      rw [h]
      exact Nat.mul_comm _ _
    · rw [disjoint_iff, eq_bot_iff]
      rintro x ⟨hxF, hxA⟩
      have hx : (x : G) ∈ A ⊓ F := ⟨hxA, hxF⟩
      rw [hinf, Subgroup.mem_bot] at hx
      simpa [Subgroup.mem_bot] using Subtype.ext hx
  ne_bot_kernel := by
    obtain ⟨f, hfne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
    intro hbot
    have hmem : (⟨(f : G), Subgroup.mem_sup_right f.2⟩ : ↥(A ⊔ F)) ∈ F.subgroupOf (A ⊔ F) :=
      f.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have hfG : (f : G) = 1 := congrArg Subtype.val hmem
    exact hfne (Subtype.ext hfG)
  ne_bot_complement := by
    obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
    intro hbot
    have hmem : (⟨(a : G), Subgroup.mem_sup_left a.2⟩ : ↥(A ⊔ F)) ∈ A.subgroupOf (A ⊔ F) :=
      a.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have haG : (a : G) = 1 := congrArg Subtype.val hmem
    exact hane (Subtype.ext haG)
  conj_frobenius := by
    intro a ha ha1 n hn hn1 hconj
    exact hfpf (a : G) ha (fun h => ha1 (Subtype.ext h)) (n : G) hn
      (fun h => hn1 (Subtype.ext h)) (Subtype.ext_iff.mp hconj)

/-! Two transport lemmas along an equality of normal subgroups.  A direct `rw` through the
quotient type `G ⧸ M` fails ("motive is not type correct") because the `Normal` instance term
baked into the quotient's group structure mentions the concrete subgroup; stating the
congruence with *variable* subgroups lets `subst` do the transport, with proof irrelevance
closing the instance mismatch. -/

/-- The preimage of `O_π` of the quotient is invariant under changing the description of the
normal subgroup being quotiented by. -/
theorem comap_oPiCore_quotient_congr {M N : Subgroup G} [M.Normal] [N.Normal]
    (h : M = N) (π : Set ℕ) :
    (Ch03.oPiCore π (G ⧸ M)).comap (QuotientGroup.mk' M) =
      (Ch03.oPiCore π (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  subst h
  rfl

/-- Existence of a Frobenius complement over the image of `K` in the quotient is invariant
under changing the description of the normal subgroup being quotiented by. -/
theorem exists_isFrobeniusGroup_map_quotient_congr {M N K : Subgroup G}
    [M.Normal] [N.Normal] (h : M = N) :
    (∃ B : Subgroup (G ⧸ M),
        Ch06.IsFrobeniusGroup (G ⧸ M) (K.map (QuotientGroup.mk' M)) B) ↔
      ∃ B : Subgroup (G ⧸ N),
        Ch06.IsFrobeniusGroup (G ⧸ N) (K.map (QuotientGroup.mk' N)) B := by
  subst h
  rfl

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

**Proof route** (Gorenstein's, with the `Ā ⊴ Ḡ` gap between the lines filled; issue 9133).
Set `F = F(G)`; if `F = ⊤` then (i).  Otherwise take a Hall `π(F)'`-subgroup `A`
(`Ch03.hall_exists_of_piSeparable`); step 2 (`conj_ne_of_isHallSubgroup_fitting_pPrime`) makes
`A` act fixed-point-freely on `F`.  If `A ⊔ F = ⊤` then `FA = G` is Frobenius with kernel `F` —
case (ii).  Otherwise `π(F) = {p}` (step 3 applied at each prime of a hypothetical second prime
divisor makes `F` a Hall `π(F)`-subgroup and `G = FA`), `|A|` is odd (an involution `t ∈ A`
would invert `F`, so `⁅t, g⁆ ∈ C_G(F) ≤ F` for all `g`, making the image of `t` central in
`Ḡ = G/F` and hence commuting with a nontrivial `p`-element of `Ḡ` — contradicting (‡)), and
`A` is cyclic (`isCyclic_of_cn_of_conj_frobenius_of_odd`).  In `Ḡ`: `O_p(Ḡ) = 1`, so
`1 ≠ F(Ḡ) ≤ N̄ := O_{p'}(Ḡ) ≤ Ā` (Hall maximality), `N̄` is cyclic, `C_Ḡ(N̄)` contains no
nontrivial `p`-element by (‡) and is therefore a normal `p'`-subgroup inside `N̄`; commutators
of `Ḡ` centralize the cyclic normal `N̄`
(`commutatorElement_mem_centralizer_of_isCyclic_normal`), so `Ḡ' ≤ N̄ ≤ Ā` and `Ā = N̄ ⊴ Ḡ`.
The three 3-step conditions then assemble with `O_p(G) = F`, `O_{p,p'}(G) = A ⊔ F`, complement
a Sylow `p`-subgroup of `Ḡ`, and (‡) supplying both Frobenius conditions. -/
theorem solvableCN_nilpotent_or_frobenius_or_threeStep [Finite G] [IsSolvable G]
    (hCN : ∀ z : G, z ≠ 1 → Group.IsNilpotent ↥(Subgroup.centralizer ({z} : Set G))) :
    Group.IsNilpotent G ∨
      (∃ A : Subgroup G, Ch06.IsFrobeniusGroup G (Ch01.fitting G) A) ∨
      (∃ q : ℕ, q.Prime ∧ IsThreeStepGroup G q) := by
  classical
  -- Case (i): `F(G) = ⊤` (this also covers the trivial group).
  by_cases hFtop : Ch01.fitting G = ⊤
  · exact Or.inl (isNilpotent_of_fitting_eq_top hFtop)
  haveI : Nontrivial G := by
    rcases subsingleton_or_nontrivial G with hs | hn
    · exact absurd (Subsingleton.elim _ _) hFtop
    · exact hn
  have hFbot : Ch01.fitting G ≠ ⊥ := Ch01.fitting_ne_bot_of_solvable_nontrivial G
  -- A Hall `π(F(G))'`-subgroup `A`.
  obtain ⟨A, hA⟩ := Ch03.hall_exists_of_piSeparable
    {r : ℕ | r ∉ (Nat.card ↥(Ch01.fitting G)).primeFactors} (G := G)
  -- `|F(G)|` and `|A|` are coprime, so `A ⊓ F(G) = ⊥` and `|A ⊔ F(G)| = |A| · |F(G)|`.
  have hcop : Nat.Coprime (Nat.card ↥(Ch01.fitting G)) (Nat.card ↥A) := by
    rw [← Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne']
    exact Finset.disjoint_left.mpr fun r hrF hrA => hA.1 r hrA hrF
  have hinfAF : A ⊓ Ch01.fitting G = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxA, hxF⟩
    have h1 : orderOf x ∣ Nat.card ↥A := by
      rw [← orderOf_mk_eq hxA]; exact orderOf_dvd_natCard _
    have h2 : orderOf x ∣ Nat.card ↥(Ch01.fitting G) := by
      rw [← orderOf_mk_eq hxF]; exact orderOf_dvd_natCard _
    have h3 := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one hcop] at h3
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hcardsup :
      Nat.card ↥(A ⊔ Ch01.fitting G) = Nat.card ↥A * Nat.card ↥(Ch01.fitting G) := by
    have h := card_sup_mul_card_inf_eq A (Ch01.fitting G)
    rwa [hinfAF, Subgroup.card_bot, mul_one] at h
  -- Case (ii): `A` complements `F(G)`, and `G` is Frobenius with kernel `F(G)`.
  by_cases hsup : A ⊔ Ch01.fitting G = ⊤
  · have hAne : A ≠ ⊥ := by
      rintro rfl
      rw [bot_sup_eq] at hsup
      exact hFtop hsup
    have hcompl : Subgroup.IsComplement' (Ch01.fitting G) A := by
      refine Subgroup.isComplement'_of_coprime ?_ hcop
      rw [Nat.mul_comm (Nat.card ↥(Ch01.fitting G)) (Nat.card ↥A), ← hcardsup, hsup,
        Subgroup.card_top]
    exact Or.inr (Or.inl ⟨A, isFrobeniusGroup_fitting_of_isComplement hCN hA hcompl hFbot hAne⟩)
  -- Case (iii): `G ⊋ F(G) A`.  First, `π(F(G))` is a single prime `p`.
  have hcardF_ne : Nat.card ↥(Ch01.fitting G) ≠ 1 :=
    fun h => hFbot (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpF⟩ := Nat.exists_prime_and_dvd hcardF_ne
  haveI : Fact p.Prime := ⟨hp⟩
  have hsingleF : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(Ch01.fitting G) → r = p := by
    by_contra hcon
    push Not at hcon
    obtain ⟨q, hq, hqF, hqp⟩ := hcon
    -- For each prime `r ∣ |F(G)|`, the full `r`-part of `|G|` already lies in `F(G)`:
    -- apply step 3 with `N` the Sylow subgroup of `F(G)` at a second prime `s ≠ r`.
    have hfull : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(Ch01.fitting G) →
        (Nat.card G).factorization r ≤ (Nat.card ↥(Ch01.fitting G)).factorization r := by
      intro r hr hrF
      haveI : Fact r.Prime := ⟨hr⟩
      obtain ⟨s, hs, hsF, hsr⟩ :
          ∃ s : ℕ, s.Prime ∧ s ∣ Nat.card ↥(Ch01.fitting G) ∧ s ≠ r := by
        rcases eq_or_ne r p with rfl | hrp
        · exact ⟨q, hq, hqF, hqp⟩
        · exact ⟨p, hp, hpF, fun h => hrp h.symm⟩
      haveI : Fact s.Prime := ⟨hs⟩
      haveI hSn : ((default : Sylow s ↥(Ch01.fitting G)) :
          Subgroup ↥(Ch01.fitting G)).Normal := Ch01.Sylow.normal_of_isNilpotent _
      haveI hSc : ((default : Sylow s ↥(Ch01.fitting G)) :
          Subgroup ↥(Ch01.fitting G)).Characteristic :=
        Sylow.characteristic_of_normal _ hSn
      haveI hNnormal : (((default : Sylow s ↥(Ch01.fitting G)) :
          Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype).Normal :=
        normal_map_subtype_of_characteristic hSc
      have hNcard : Nat.card ↥(((default : Sylow s ↥(Ch01.fitting G)) :
          Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype) =
          s ^ (Nat.card ↥(Ch01.fitting G)).factorization s := by
        rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
          Sylow.card_eq_multiplicity]
      have hspos : 0 < (Nat.card ↥(Ch01.fitting G)).factorization s :=
        Nat.Prime.factorization_pos_of_dvd hs Nat.card_pos.ne' hsF
      have hNbot : ((default : Sylow s ↥(Ch01.fitting G)) :
          Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hNcard
        exact (Nat.one_lt_pow hspos.ne' hs.one_lt).ne' hNcard.symm
      have hrN : ¬ r ∣ Nat.card ↥(((default : Sylow s ↥(Ch01.fitting G)) :
          Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype) := by
        rw [hNcard]
        intro hdvd
        exact hsr ((Nat.prime_dvd_prime_iff_eq hr hs).mp (hr.dvd_of_dvd_pow hdvd)).symm
      have hOrne : Ch03.oPiCore ({r} : Set ℕ) G ≠ ⊥ := by
        intro hbot
        have hle := sylow_fitting_map_le_oPiCore (default : Sylow r ↥(Ch01.fitting G))
        rw [hbot, le_bot_iff] at hle
        have hcard : Nat.card ↥(((default : Sylow r ↥(Ch01.fitting G)) :
            Subgroup ↥(Ch01.fitting G)).map (Ch01.fitting G).subtype) =
            r ^ (Nat.card ↥(Ch01.fitting G)).factorization r := by
          rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
            Sylow.card_eq_multiplicity]
        rw [hle, Subgroup.card_bot] at hcard
        have hrpos : 0 < (Nat.card ↥(Ch01.fitting G)).factorization r :=
          Nat.Prime.factorization_pos_of_dvd hr Nat.card_pos.ne' hrF
        exact (Nat.one_lt_pow hrpos.ne' hr.one_lt).ne' hcard.symm
      obtain ⟨P, hP⟩ := exists_sylow_eq_oPiCore_of_normal_pPrime_le_fitting (p := r)
        hCN hOrne hNbot (Subgroup.map_subtype_le _) hrN
      have hOrF : Ch03.oPiCore ({r} : Set ℕ) G ≤ Ch01.fitting G := by
        haveI : Group.IsNilpotent ↥(Ch03.oPiCore ({r} : Set ℕ) G) :=
          (Ch04.isPGroup_of_isPiGroup_singleton
            (Ch03.oPiCore.isPiGroup ({r} : Set ℕ))).isNilpotent
        exact Ch01.nilpotent_normal_le_fitting
      have hdvd : r ^ (Nat.card G).factorization r ∣ Nat.card ↥(Ch01.fitting G) := by
        rw [← P.card_eq_multiplicity]
        exact Subgroup.card_dvd_of_le (le_of_eq_of_le hP hOrF)
      exact (Nat.Prime.pow_dvd_iff_le_factorization hr Nat.card_pos.ne').mp hdvd
    -- Hence `|G| ∣ |F(G)| · |A|`, so `A ⊔ F(G) = ⊤` — contradiction.
    have hGdvd : Nat.card G ∣ Nat.card ↥(Ch01.fitting G) * Nat.card ↥A := by
      rw [← Nat.factorization_le_iff_dvd Nat.card_pos.ne'
        (mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'),
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.le_iff]
      intro r hrsupp
      rw [Nat.support_factorization] at hrsupp
      have hr : r.Prime := Nat.prime_of_mem_primeFactors hrsupp
      rw [Finsupp.add_apply]
      by_cases hrF : r ∣ Nat.card ↥(Ch01.fitting G)
      · exact (hfull r hr hrF).trans le_self_add
      · have hAidx : ¬ r ∣ A.index := by
          intro hdvd
          have hmem := hA.2 r
            (Nat.mem_primeFactors.mpr ⟨hr, hdvd, Subgroup.index_ne_zero_of_finite⟩)
          simp only [Set.mem_setOf_eq, not_not] at hmem
          exact hrF (Nat.dvd_of_mem_primeFactors hmem)
        have hsplit : (Nat.card G).factorization r =
            (Nat.card ↥A).factorization r + A.index.factorization r := by
          rw [← Subgroup.card_mul_index A,
            Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
            Finsupp.add_apply]
        rw [hsplit, Nat.factorization_eq_zero_of_not_dvd hAidx, add_zero,
          Nat.factorization_eq_zero_of_not_dvd hrF, zero_add]
    refine hsup (Subgroup.eq_top_of_card_eq _ ?_)
    refine Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card _) ?_
    rw [hcardsup, Nat.mul_comm]
    exact hGdvd
  -- `F(G)` is a `p`-group and `A` is a nontrivial Hall `p'`-subgroup.
  have hF : IsPGroup p ↥(Ch01.fitting G) := by
    refine IsPGroup.iff_card.mpr ⟨(Nat.card ↥(Ch01.fitting G)).factorization p, ?_⟩
    refine eq_pow_factorization_of_primeFactors_subset Nat.card_pos.ne' ?_
    intro r hr
    rw [Finset.mem_singleton]
    exact hsingleF r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
  have hpA : ¬ p ∣ Nat.card ↥A := fun hdvd =>
    hA.1 p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
      (Nat.mem_primeFactors.mpr ⟨hp, hpF, Nat.card_pos.ne'⟩)
  have hAne : A ≠ ⊥ := by
    rintro rfl
    have hGp : IsPGroup p G := by
      refine IsPGroup.iff_card.mpr ⟨(Nat.card G).factorization p, ?_⟩
      refine eq_pow_factorization_of_primeFactors_subset Nat.card_pos.ne' ?_
      intro r hr
      rw [Finset.mem_singleton]
      have hmem := hA.2 r (by rwa [Subgroup.index_bot])
      simp only [Set.mem_setOf_eq, not_not] at hmem
      exact hsingleF r (Nat.prime_of_mem_primeFactors hmem) (Nat.dvd_of_mem_primeFactors hmem)
    haveI : Group.IsNilpotent G := hGp.isNilpotent
    refine hFtop ?_
    rw [eq_top_iff]
    haveI : Group.IsNilpotent ↥(⊤ : Subgroup G) :=
      Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
    exact Ch01.nilpotent_normal_le_fitting
  -- `[G : A ⊔ F(G)]` is a nontrivial `p`-power `p ^ k`.
  have hAidx_pf : A.index.primeFactors ⊆ {p} := by
    intro r hr
    rw [Finset.mem_singleton]
    have hmem := hA.2 r hr
    simp only [Set.mem_setOf_eq, not_not] at hmem
    exact hsingleF r (Nat.prime_of_mem_primeFactors hmem) (Nat.dvd_of_mem_primeFactors hmem)
  obtain ⟨k, -, hHidx⟩ := (Nat.dvd_prime_pow hp).mp
    ((eq_pow_factorization_of_primeFactors_subset Subgroup.index_ne_zero_of_finite hAidx_pf) ▸
      Subgroup.index_dvd_of_le (le_sup_left : A ≤ A ⊔ Ch01.fitting G))
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hHidx
    exact hsup (Subgroup.index_eq_one.mp hHidx)
  -- The fixed-point-free action of `A` on `F(G)` (step 2), and `p ∣ |G/F(G)|`.
  have hfpfA : ∀ a ∈ A, a ≠ 1 → ∀ n ∈ Ch01.fitting G, n ≠ 1 → a * n * a⁻¹ ≠ n :=
    conj_ne_of_isHallSubgroup_fitting_pPrime hCN hA
  have hpQ : p ∣ Nat.card (G ⧸ Ch01.fitting G) := by
    rw [← Subgroup.index_eq_card]
    exact (hHidx.symm ▸ dvd_pow_self p hk0).trans
      (Subgroup.index_dvd_of_le (le_sup_right : Ch01.fitting G ≤ A ⊔ Ch01.fitting G))
  -- Step 5: `|A|` is odd.  A hypothetical involution `t ∈ A` inverts `F(G)`, so its image is
  -- central in `G/F(G)` and commutes with a nontrivial `p`-element there, contradicting (‡).
  have hodd : Odd (Nat.card ↥A) := by
    rcases Nat.even_or_odd (Nat.card ↥A) with heven | h
    swap
    · exact h
    exfalso
    have h2dvd : (2 : ℕ) ∣ Nat.card ↥A := heven.two_dvd
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht2⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) 2 h2dvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hpA h2dvd
    have htG : orderOf (t : G) = 2 := by
      rw [← ht2]
      exact orderOf_injective A.subtype A.subtype_injective t
    have ht1 : (t : G) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at htG
      exact absurd htG (by norm_num)
    have htt : (t : G) * (t : G) = 1 := by
      have h1 := pow_orderOf_eq_one (t : G)
      rwa [htG, pow_two] at h1
    have hfpf_t : ∀ f ∈ Ch01.fitting G, (t : G) * f * (t : G)⁻¹ = f → f = 1 := by
      intro f hf hfix
      by_contra hf1
      exact hfpfA (t : G) t.2 ht1 f hf hf1 hfix
    have hcentral : ∀ x : G ⧸ Ch01.fitting G,
        Commute (QuotientGroup.mk' (Ch01.fitting G) (t : G)) x := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Ch01.fitting G) x
      rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact centralizer_fitting_le_fitting
        (commutatorElement_mem_centralizer_of_orderTwo_of_fixedPointFree htt hfpf_t g)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := G ⧸ Ch01.fitting G) p hpQ
    have hu1 : u ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hu
      exact hp.ne_one hu.symm
    have hup : IsPGroup p ↥(Subgroup.zpowers u) :=
      IsPGroup.of_card (by rw [Nat.card_zpowers, hu, pow_one])
    have hap : ¬ p ∣ orderOf (t : G) := by
      rw [htG]
      intro hdvd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    have ha1 : QuotientGroup.mk' (Ch01.fitting G) (t : G) ≠ 1 := by
      rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      intro htF
      have h2F : (2 : ℕ) ∣ Nat.card ↥(Ch01.fitting G) := by
        rw [← htG, ← orderOf_mk_eq htF]
        exact orderOf_dvd_natCard _
      obtain ⟨n, hn⟩ := hF.exists_card_eq
      rw [hn] at h2F
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2F)).symm
    exact not_commute_mk_of_not_dvd_orderOf_of_isPGroup_fitting hCN hF hap ha1 hu1 hup
      (hcentral u)
  -- Step 6: `A` is cyclic.
  haveI hAcyc : IsCyclic ↥A :=
    isCyclic_of_cn_of_conj_frobenius_of_odd hCN hFbot hfpfA hodd
  -- Step 7 setup: in `Ḡ = G/F(G)`, `O_p(Ḡ) = 1` and `N̄ := O_{p'}(Ḡ) ⊇ F(Ḡ) ≠ 1`.
  have hOpQ : Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch01.fitting G) = ⊥ := by
    have hmapcomap := Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective (Ch01.fitting G))
      (Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch01.fitting G))
    haveI : ((Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch01.fitting G)).comap
        (QuotientGroup.mk' (Ch01.fitting G))).Normal :=
      Subgroup.Normal.comap (Ch03.oPiCore.normal _ _) _
    haveI : Group.IsNilpotent ↥((Ch03.oPiCore ({p} : Set ℕ) (G ⧸ Ch01.fitting G)).comap
        (QuotientGroup.mk' (Ch01.fitting G))) :=
      ((Ch04.isPGroup_of_isPiGroup_singleton
        (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))).comap_of_ker_isPGroup _
        (by rw [QuotientGroup.ker_mk']; exact hF)).isNilpotent
    rw [← hmapcomap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact Ch01.nilpotent_normal_le_fitting
  haveI : Nontrivial (G ⧸ Ch01.fitting G) := QuotientGroup.nontrivial_iff.mpr hFtop
  have hFQne : Ch01.fitting (G ⧸ Ch01.fitting G) ≠ ⊥ :=
    Ch01.fitting_ne_bot_of_solvable_nontrivial (G ⧸ Ch01.fitting G)
  have hNbar_ne : Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) ≠ ⊥ := by
    intro hbot
    refine hFQne (le_bot_iff.mp ?_)
    rw [← hbot]
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro r hr
    simp only [Set.mem_setOf_eq]
    intro hrp
    rw [hrp] at hr
    have hle := sylow_fitting_map_le_oPiCore
      (default : Sylow p ↥(Ch01.fitting (G ⧸ Ch01.fitting G)))
    rw [hOpQ, le_bot_iff] at hle
    have hcard : Nat.card ↥(((default : Sylow p ↥(Ch01.fitting (G ⧸ Ch01.fitting G))) :
        Subgroup ↥(Ch01.fitting (G ⧸ Ch01.fitting G))).map
          (Ch01.fitting (G ⧸ Ch01.fitting G)).subtype) =
        p ^ (Nat.card ↥(Ch01.fitting (G ⧸ Ch01.fitting G))).factorization p := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        Sylow.card_eq_multiplicity]
    rw [hle, Subgroup.card_bot] at hcard
    have hppos : 0 < (Nat.card ↥(Ch01.fitting (G ⧸ Ch01.fitting G))).factorization p :=
      Nat.Prime.factorization_pos_of_dvd hp Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hr)
    exact (Nat.one_lt_pow hppos.ne' hp.one_lt).ne' hcard.symm
  -- `A` maps isomorphically onto `Ā`, a Hall `p'`-subgroup of `Ḡ`.
  have hkerA : A ⊓ (QuotientGroup.mk' (Ch01.fitting G)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk']
    exact hinfAF
  have hAbar_card : Nat.card ↥(A.map (QuotientGroup.mk' (Ch01.fitting G))) = Nat.card ↥A :=
    Nat.card_congr (mulEquivMapOfInfKerEqBot _ _ hkerA).symm.toEquiv
  haveI hAbar_cyc : IsCyclic ↥(A.map (QuotientGroup.mk' (Ch01.fitting G))) :=
    isCyclic_of_surjective (mulEquivMapOfInfKerEqBot _ _ hkerA).toMonoidHom
      (mulEquivMapOfInfKerEqBot _ _ hkerA).surjective
  have hGcard : Nat.card G = Nat.card ↥(Ch01.fitting G) * (Nat.card ↥A * p ^ k) := by
    rw [← Subgroup.card_mul_index (A ⊔ Ch01.fitting G), hcardsup, hHidx]
    ring
  have hQcard : Nat.card (G ⧸ Ch01.fitting G) = Nat.card ↥A * p ^ k := by
    have h1 : Nat.card ↥(Ch01.fitting G) * (Ch01.fitting G).index = Nat.card G :=
      Subgroup.card_mul_index _
    rw [hGcard] at h1
    rw [← Subgroup.index_eq_card]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hAbar_idx : (A.map (QuotientGroup.mk' (Ch01.fitting G))).index = p ^ k := by
    have h1 : Nat.card ↥(A.map (QuotientGroup.mk' (Ch01.fitting G))) *
        (A.map (QuotientGroup.mk' (Ch01.fitting G))).index =
        Nat.card (G ⧸ Ch01.fitting G) := Subgroup.card_mul_index _
    rw [hAbar_card, hQcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hAbar_hall : Ch03.IsHallSubgroup {q : ℕ | q ≠ p}
      (A.map (QuotientGroup.mk' (Ch01.fitting G))) := by
    constructor
    · intro r hr
      rw [hAbar_card] at hr
      simp only [Set.mem_setOf_eq]
      intro hrp
      rw [hrp] at hr
      exact hpA (Nat.dvd_of_mem_primeFactors hr)
    · intro r hr
      rw [hAbar_idx] at hr
      simp only [Set.mem_setOf_eq, not_not]
      exact (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hr) hp).mp
        ((Nat.prime_of_mem_primeFactors hr).dvd_of_dvd_pow (Nat.dvd_of_mem_primeFactors hr))
  -- Step 7: `N̄ ≤ Ā`, `N̄` cyclic, `C_Ḡ(N̄) ≤ N̄`, commutators centralize `N̄`, and `Ā = N̄`.
  have hNbar_le : Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) ≤
      A.map (QuotientGroup.mk' (Ch01.fitting G)) :=
    Ch03.Subgroup.IsPiGroup.normal_le_hall (Ch03.oPiCore.isPiGroup _) hAbar_hall
  haveI hNbar_cyc : IsCyclic ↥(Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G)) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hNbar_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNbar_le).surjective
  have hCle : Subgroup.centralizer
      ((Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) : Subgroup (G ⧸ Ch01.fitting G)) :
        Set (G ⧸ Ch01.fitting G)) ≤
      Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) := by
    have hpC : ¬ p ∣ Nat.card ↥(Subgroup.centralizer
        ((Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) :
          Subgroup (G ⧸ Ch01.fitting G)) : Set (G ⧸ Ch01.fitting G))) := by
      intro hdvd
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
      obtain ⟨nbar, hnbar_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hNbar_ne
      obtain ⟨a, haA, hamk⟩ := hNbar_le nbar.2
      have hap : ¬ p ∣ orderOf a := fun hdvd' =>
        hpA (hdvd'.trans (by rw [← orderOf_mk_eq haA]; exact orderOf_dvd_natCard _))
      have ha1 : QuotientGroup.mk' (Ch01.fitting G) a ≠ 1 := by
        rw [hamk]
        intro h1
        exact hnbar_ne (Subtype.ext h1)
      have hordu : orderOf (u : G ⧸ Ch01.fitting G) = p :=
        (orderOf_injective _ (Subgroup.subtype_injective _) u).trans hu
      have hu1 : (u : G ⧸ Ch01.fitting G) ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hordu
        exact hp.ne_one hordu.symm
      have hup : IsPGroup p ↥(Subgroup.zpowers (u : G ⧸ Ch01.fitting G)) :=
        IsPGroup.of_card (by rw [Nat.card_zpowers, hordu, pow_one])
      refine not_commute_mk_of_not_dvd_orderOf_of_isPGroup_fitting hCN hF hap ha1 hu1 hup ?_
      rw [hamk]
      exact Subgroup.mem_centralizer_iff.mp u.2 (nbar : G ⧸ Ch01.fitting G) nbar.2
    refine Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
    intro r hr
    simp only [Set.mem_setOf_eq]
    intro hrp
    rw [hrp] at hr
    exact hpC (Nat.dvd_of_mem_primeFactors hr)
  have hcomm_mem : ∀ x y : G ⧸ Ch01.fitting G,
      ⁅x, y⁆ ∈ Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) := fun x y =>
    hCle (commutatorElement_mem_centralizer_of_isCyclic_normal hNbar_cyc x y)
  haveI hAbar_normal : (A.map (QuotientGroup.mk' (Ch01.fitting G))).Normal := by
    constructor
    intro a haA g
    have hmem := hNbar_le (hcomm_mem g a)
    rw [commutatorElement_def] at hmem
    have hrw : g * a * g⁻¹ = g * a * g⁻¹ * a⁻¹ * a := by group
    rw [hrw]
    exact Subgroup.mul_mem _ hmem haA
  have hAbarN : A.map (QuotientGroup.mk' (Ch01.fitting G)) =
      Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) := by
    refine le_antisymm ?_ hNbar_le
    exact Ch03.Subgroup.IsPiGroup.le_oPiCore hAbar_hall.1
  -- The two cores of the 3-step conditions: `O_p(G) = F(G)` and `O_{p,p'}(G) = A ⊔ F(G)`.
  have hOpF : Ch03.oPiCore ({p} : Set ℕ) G = Ch01.fitting G := by
    refine le_antisymm ?_ (Ch04.isPiGroup_singleton_of_isPGroup hF).le_oPiCore
    haveI : Group.IsNilpotent ↥(Ch03.oPiCore ({p} : Set ℕ) G) :=
      (Ch04.isPGroup_of_isPiGroup_singleton (Ch03.oPiCore.isPiGroup ({p} : Set ℕ))).isNilpotent
    exact Ch01.nilpotent_normal_le_fitting
  have hkey : opPPrimeCore p G = A ⊔ Ch01.fitting G := by
    rw [show opPPrimeCore p G =
        (Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G)).comap
          (QuotientGroup.mk' (Ch01.fitting G)) from
        comap_oPiCore_quotient_congr hOpF {q : ℕ | q ≠ p},
      ← hAbarN, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  -- Assemble the 3-step structure.
  refine Or.inr (Or.inr ⟨p, hp, ?_, ?_, ?_, ?_⟩)
  · -- (1) `O_{p,p'}(G) = F(G) A` is Frobenius with kernel `O_p(G) = F(G)` and cyclic
    --     complement `A` of odd order.
    rw [hkey, hOpF]
    refine ⟨A.subgroupOf (A ⊔ Ch01.fitting G),
      isFrobeniusGroup_subgroupOf_sup hinfAF hFbot hAne hfpfA, ?_, ?_⟩
    · exact isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ Ch01.fitting G)).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ Ch01.fitting G)).symm.surjective
    · rw [Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : A ≤ A ⊔ Ch01.fitting G)).toEquiv]
      exact hodd
  · -- (2a) `G = O_{p,p',p}(G)`: the quotient by `O_{p,p'}(G)` is a `p`-group.
    rw [opPPrimePCore_eq_top_iff]
    refine oPiCore_singleton_eq_top_of_isPGroup ?_
    refine IsPGroup.iff_card.mpr ⟨k, ?_⟩
    rw [← Subgroup.index_eq_card, hkey, hHidx]
  · -- (2b) `G ⊋ O_{p,p'}(G)`.
    rw [hkey]
    exact hsup
  · -- (3) `G/O_p(G)` is Frobenius with kernel `O_{p,p'}(G)/O_p(G) = Ā = N̄`, complemented by a
    --     Sylow `p`-subgroup; both Frobenius conditions come from (‡).
    rw [exists_isFrobeniusGroup_map_quotient_congr hOpF, hkey]
    have hmap : (A ⊔ Ch01.fitting G).map (QuotientGroup.mk' (Ch01.fitting G)) =
        Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G) := by
      have hFmap : (Ch01.fitting G).map (QuotientGroup.mk' (Ch01.fitting G)) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      rw [Subgroup.map_sup, hFmap, sup_bot_eq, hAbarN]
    rw [hmap]
    obtain ⟨Pbar⟩ := (inferInstance : Nonempty (Sylow p (G ⧸ Ch01.fitting G)))
    have hPcard : Nat.card ↥(Pbar : Subgroup (G ⧸ Ch01.fitting G)) = p ^ k := by
      rw [Pbar.card_eq_multiplicity, hQcard]
      congr 1
      rw [Nat.factorization_mul Nat.card_pos.ne' (pow_ne_zero k hp.pos.ne'),
        Finsupp.add_apply, Nat.factorization_pow_self hp,
        Nat.factorization_eq_zero_of_not_dvd hpA, zero_add]
    have hNbar_card :
        Nat.card ↥(Ch03.oPiCore {q : ℕ | q ≠ p} (G ⧸ Ch01.fitting G)) = Nat.card ↥A := by
      rw [← hAbarN, hAbar_card]
    refine ⟨Pbar, ?_⟩
    exact
      { isNormal := hAbarN ▸ hAbar_normal
        isComplement := by
          refine Subgroup.isComplement'_of_coprime ?_ ?_
          · rw [hNbar_card, hPcard, hQcard]
          · rw [hNbar_card, hPcard]
            exact (((Nat.Prime.coprime_iff_not_dvd hp).mpr hpA).symm).pow_right k
        ne_bot_kernel := hNbar_ne
        ne_bot_complement := by
          intro hbot
          rw [hbot, Subgroup.card_bot] at hPcard
          exact (Nat.one_lt_pow hk0 hp.one_lt).ne' hPcard.symm
        conj_frobenius := by
          intro b hbP hb1 n hnN hn1 hconj
          rw [← hAbarN] at hnN
          obtain ⟨a, haA, hamk⟩ := hnN
          have hap : ¬ p ∣ orderOf a := fun hdvd =>
            hpA (hdvd.trans (by rw [← orderOf_mk_eq haA]; exact orderOf_dvd_natCard _))
          have ha1 : QuotientGroup.mk' (Ch01.fitting G) a ≠ 1 := by
            rw [hamk]
            exact hn1
          have hbp : IsPGroup p ↥(Subgroup.zpowers b) :=
            Pbar.isPGroup'.to_le (Subgroup.zpowers_le.mpr hbP)
          refine not_commute_mk_of_not_dvd_orderOf_of_isPGroup_fitting hCN hF hap ha1 hb1
            hbp ?_
          rw [hamk]
          have hnb : b * n = n * b := by
            have h1 := congrArg (· * b) hconj
            simpa [mul_assoc] using h1
          exact hnb.symm }

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
