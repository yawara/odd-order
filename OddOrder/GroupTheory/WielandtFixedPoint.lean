/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CoprimeAction
import OddOrder.GroupTheory.WielandtPerFactorDischarge

/-!
# Peterfalvi (9.1): Wielandt's fixed-point formula (assembled) and the (13.17.b) engine

`OddOrder.GroupTheory.WielandtFixedPoint`: the group-level statement of **Peterfalvi (9.1)** and its
corollaries, proved from the chief-series assembly, together with the fixed-point-free engine of
(13.17.b).

The shared carrier `CoprimeFrobeniusAction` and the fixed-point subgroups `fixedByUE/E/U` live
upstream in `OddOrder.GroupTheory.CoprimeAction` (reused by the BG and Isaacs layers); the Wielandt
*theorems* live here because their proof goes through the chief-series assembly
(`wielandt_formula_of_perfactor` ∘ `wielandtPerFactor_of_dim`), which `CoprimeAction` cannot import
without a cycle.

`wielandt_fixedPoint_frobenius` is reduced — via the group-theoretic chief-series assembly (pieces
A/B/C, all axiom-clean) — to the single per-chief-factor **dimension identity** (⋆)
`PerFactorDimIdentity` on each elementary-abelian chief factor.  That dimension identity is the sole
remaining representation-theoretic input (the kernel-FPF fact (†), to be discharged by the modular
Brauer / free-orbit machinery of lane-f); it is the lone `sorry` below.

`notes/peterfalvi/s11_wielandt_91_design.md` (assembly piece E), issue 2014.
-/

namespace OddOrder.GroupTheory

open OddOrder.Isaacs
open OddOrder.Isaacs.Ch03 (IsAInvariant)

section WielandtFixedPoint

/-- **Peterfalvi (9.1)**: Wielandt's fixed-point formula for a coprime Frobenius action.
For `L = U ⋊ E` Frobenius with kernel `U` acting on a finite solvable `H` of order prime
to `|L|`,
`|C_H(UE)|^{|E|} · |H| = |C_H(E)|^{|E|} · |C_H(U)|`.

Proved by the **chief-series assembly** (`wielandt_formula_of_perfactor`): the group-level identity
follows by strong induction on `|H|` from the per-chief-factor identity `WielandtPerFactor`, which
in turn (`wielandtPerFactor_of_dim`) follows from the per-factor **dimension identity** (⋆)
`PerFactorDimIdentity` on each elementary-abelian chief factor.  The whole group-theoretic reduction
(pieces A/B/C) is axiom-clean; the sole remaining input is that dimension identity — the kernel-FPF
fact (†) (modular Brauer / free-orbit count, lane-f), which is the `sorry` `hdim` below. -/
theorem wielandt_fixedPoint_frobenius {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H) :
    Nat.card ↥act.fixedByUE ^ Nat.card ↥act.E * Nat.card H =
      Nat.card ↥act.fixedByE ^ Nat.card ↥act.E * Nat.card ↥act.fixedByU := by
  haveI : IsSolvable H := act.H_solvable
  letI : Fintype ↥act.E := Fintype.ofFinite _
  -- The per-chief-factor dimension identity (⋆) on each elementary-abelian chief factor — the sole
  -- remaining representation-theoretic input (the kernel-FPF fact (†), lane-f rep-theory: piece D).
  have hdim : ∀ (H' : Type _) [Group H'] [Finite H'] (φ' : L →* MulAut H') (N' : Subgroup H')
      [N'.Normal] (hN' : IsAInvariant φ' N') (p' : ℕ) (_hp' : p'.Prime)
      (hpe' : IsElementaryAbelian p' ↥N'),
      PerFactorDimIdentity (U := act.U) (E := act.E) φ' hN' p' hpe' := by
    sorry
  -- The chief-series assembly: per-factor identity ⟹ group-level Wielandt formula.
  exact wielandt_formula_of_perfactor (wielandtPerFactor_of_dim hdim) H act.φ act.coprime_order.symm

/-- **Peterfalvi (9.1), first corollary**: if `C_H(E) = 1` then the Frobenius kernel `U`
centralizes `H`, i.e. `C_H(U) = H`. -/
theorem wielandt_fixedPoint_trivial_E_fixed {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hE : act.fixedByE = ⊥) :
    act.fixedByU = ⊤ := by
  have key := wielandt_fixedPoint_frobenius act
  have hUE : act.fixedByUE = ⊥ := le_bot_iff.mp (hE ▸ act.fixedByUE_le_fixedByE)
  simp only [hUE, hE, Subgroup.card_bot, one_pow, one_mul] at key
  exact Subgroup.eq_top_of_card_eq _ key.symm

/-- **Peterfalvi (9.1), second corollary**: if `C_H(U) = 1` then `|H| = |C_H(E)|^{|E|}`. -/
theorem wielandt_fixedPoint_trivial_U_fixed {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hU : act.fixedByU = ⊥) :
    Nat.card H = Nat.card ↥act.fixedByE ^ Nat.card ↥act.E := by
  have key := wielandt_fixedPoint_frobenius act
  have hUE : act.fixedByUE = ⊥ := le_bot_iff.mp (hU ▸ act.fixedByUE_le_fixedByU)
  simp only [hUE, hU, Subgroup.card_bot, one_pow, one_mul, mul_one] at key
  exact key

/-- **Peterfalvi (9.1), the fixed-point-free corollary**: if *both* the Frobenius kernel `U` and
the complement `E` act fixed-point-freely on `H` (`C_H(U) = C_H(E) = 1`), then `H` is trivial.
This is the form used in Peterfalvi (13.17.b): a Frobenius group `U W₁` acting fixed-point-freely
on the Fitting kernel `H = L_F` forces `|L_F| = 1`. -/
theorem coprimeFrobeniusAction_card_eq_one {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hE : act.fixedByE = ⊥) (hU : act.fixedByU = ⊥) :
    Nat.card H = 1 := by
  have key := wielandt_fixedPoint_trivial_U_fixed act hU
  rw [hE, Subgroup.card_bot, one_pow] at key
  exact key

end WielandtFixedPoint

section FrobeniusCentralizer

/-- **Peterfalvi (13.17.b), the fixed-point-free engine**: let `Lsub ≤ G` be a finite Frobenius
group with kernel `N` (`N ≤ Lsub`, `N.subgroupOf Lsub` normal).  If a *Frobenius subgroup*
`U E ≤ Lsub` (kernel `U`, complement `E`, with its own Frobenius structure on `↥(U ⊔ E)`) meets `N`
trivially (`U ⊓ N = E ⊓ N = ⊥`) and acts coprimely (`|N| ⟂ |UE|`), then `N = ⊥`.

Both `U` and `E` act fixed-point-freely on `N`: every nontrivial element, lifted into the Frobenius
group `↥Lsub`, lies outside the kernel, so `centralizer_inf_kernel_eq_bot_of_not_mem` makes its
centralizer meet `N` trivially.  Hence the fixed-point subgroups vanish and Wielandt's formula
(`coprimeFrobeniusAction_card_eq_one`) forces `|N| = 1`.  This is exactly the step that, in
(13.17.b), derives `|L_F| = 1` from `U ∩ L_F = 1`, contradicting `L_F ≠ 1`.  Phrasing the Frobenius
subgroup `U E` in the ambient `G` (rather than inside `↥Lsub`) lets callers supply
`basic_structure`'s `UW1_frobenius` directly, with no `subgroupOf` transfer. -/
theorem isFrobenius_kernel_eq_bot_of_frobenius_subgroup {G : Type*} [Group G] [Finite G]
    {Lsub N U E : Subgroup G} (hNL : N ≤ Lsub) (hUL : U ⊔ E ≤ Lsub)
    (hFrob : ∃ A : Subgroup ↥Lsub, Ch06.IsFrobeniusGroup ↥Lsub (N.subgroupOf Lsub) A)
    (hUE : Ch06.IsFrobeniusGroup ↥(U ⊔ E) (U.subgroupOf (U ⊔ E)) (E.subgroupOf (U ⊔ E)))
    (hUN : U ⊓ N = ⊥) (hEN : E ⊓ N = ⊥) (hsolv : IsSolvable ↥N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(U ⊔ E))) :
    N = ⊥ := by
  classical
  obtain ⟨A, hFrobA⟩ := hFrob
  -- `U ⊔ E ≤ Lsub ≤ N_G(N)` (the latter because `N` is normal in the Frobenius group `↥Lsub`).
  have hUEnorm : (U ⊔ E) ≤ Subgroup.normalizer (N : Set G) :=
    hUL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hNL).mp hFrobA.isNormal)
  letI act : MulDistribMulAction ↥(U ⊔ E) ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hUEnorm)
  set φ : ↥(U ⊔ E) →* MulAut ↥N := MulDistribMulAction.toMulAut ↥(U ⊔ E) ↥N with hφ
  have hφ_coe : ∀ (a : ↥(U ⊔ E)) (x : ↥N), ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  let act' : CoprimeFrobeniusAction ↥(U ⊔ E) ↥N :=
    { U := U.subgroupOf (U ⊔ E), E := E.subgroupOf (U ⊔ E), frobenius := hUE,
      H_solvable := hsolv, φ := φ, coprime_order := hcop }
  -- Each factor's nontrivial elements lie outside `N`, hence (lifted into the Frobenius group
  -- `↥Lsub`) centralize nothing nontrivial in `N`: the fixed-point subgroup is trivial.
  have key : ∀ {K : Subgroup G}, K ⊓ N = ⊥ → K ≠ ⊥ → K ≤ U ⊔ E →
      fixedSubgroup φ (K.subgroupOf (U ⊔ E)) = ⊥ := by
    intro K hKN hKne hKle
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    by_contra hne
    have hnG : (n : G) ≠ 1 := fun h => hne (Subtype.ext h)
    obtain ⟨k, hkK, hkne⟩ := (K.bot_or_exists_ne_one).resolve_left hKne
    have hkUE : k ∈ U ⊔ E := hKle hkK
    have hfix := (mem_fixedSubgroup.mp hn) ⟨k, hkUE⟩ (Subgroup.mem_subgroupOf.mpr hkK)
    have hcomm : k * (n : G) * k⁻¹ = (n : G) := by
      have hc : ((φ ⟨k, hkUE⟩) n : G) = (n : G) := Subtype.ext_iff.mp hfix
      rwa [hφ_coe] at hc
    have hkN : k ∉ N := fun h =>
      hkne (Subgroup.disjoint_def.mp (disjoint_iff.mpr hKN) hkK h)
    -- Lift `k`, `n` into the Frobenius group `↥Lsub` and apply the kernel-centralizer engine.
    have hk_notmem : (⟨k, hUL hkUE⟩ : ↥Lsub) ∉ N.subgroupOf Lsub :=
      fun h => hkN (Subgroup.mem_subgroupOf.mp h)
    have hcb := IsFrobeniusGroup.centralizer_inf_kernel_eq_bot_of_not_mem hFrobA hk_notmem
    have hkn : k * (n : G) = (n : G) * k := by rwa [mul_inv_eq_iff_eq_mul] at hcomm
    have hn_cent : (⟨(n : G), hNL n.2⟩ : ↥Lsub) ∈
        Subgroup.centralizer ({(⟨k, hUL hkUE⟩ : ↥Lsub)} : Set ↥Lsub) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hkn.symm
    have hn_in : (⟨(n : G), hNL n.2⟩ : ↥Lsub) ∈
        Subgroup.centralizer ({(⟨k, hUL hkUE⟩ : ↥Lsub)} : Set ↥Lsub) ⊓ N.subgroupOf Lsub :=
      ⟨hn_cent, Subgroup.mem_subgroupOf.mpr n.2⟩
    exact hnG (congrArg Subtype.val (Subgroup.mem_bot.mp (hcb.le hn_in)))
  have hUne : U ≠ ⊥ := fun hb => hUE.ne_bot_kernel (by rw [hb, Subgroup.bot_subgroupOf])
  have hEne : E ≠ ⊥ := fun hb => hUE.ne_bot_complement (by rw [hb, Subgroup.bot_subgroupOf])
  have hfixU : act'.fixedByU = ⊥ := key hUN hUne le_sup_left
  have hfixE : act'.fixedByE = ⊥ := key hEN hEne le_sup_right
  have hcard := coprimeFrobeniusAction_card_eq_one act' hfixE hfixU
  exact Subgroup.card_eq_one.mp hcard

end FrobeniusCentralizer

end OddOrder.GroupTheory
