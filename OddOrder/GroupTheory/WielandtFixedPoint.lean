/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.CoprimeAction
import OddOrder.GroupTheory.WielandtPerFactorDischarge
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabFrobenius

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

`wielandt_fixedPoint_frobenius` is **fully unconditional** (sorry-free, axiom-clean): the
group-theoretic chief-series assembly (pieces A/B/C) reduces it to the per-chief-factor **dimension
identity** (⋆) `PerFactorDimIdentity` on each elementary-abelian chief factor, and that identity is
discharged by the kernel-FPF fact (†) over `𝔽̄_p`
(`WielandtKernelFPF.wielandtDimIdentity_of_frobenius`,
the modular Brauer / free-orbit count plus base change `𝔽_p → 𝔽̄_p`).

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
`PerFactorDimIdentity` on each elementary-abelian chief factor.  That dimension identity is supplied
by `WielandtKernelFPF.wielandtDimIdentity_of_frobenius` (the kernel-FPF fact (†) over `𝔽̄_p` plus
base
change), so the whole proof is unconditional (axiom-clean). -/
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
      (hpe' : IsElementaryAbelian p' ↥N') (hcop' : Nat.Coprime (Nat.card L) (Nat.card H')),
      PerFactorDimIdentity (U := act.U) (E := act.E) φ' hN' p' hpe' := by
    intro H' _ _ φ' N' _ hN' p' hp' hpe' hcop'
    haveI : Fact p'.Prime := ⟨hp'⟩
    haveI hUnorm : act.U.Normal := act.frobenius.isNormal
    haveI : Fintype ↥act.U := Fintype.ofFinite _
    -- The Frobenius data of `act` feeding (†).
    have hsup : act.U ⊔ act.E = ⊤ := act.frobenius.isComplement.sup_eq_top
    have hcopUE : Nat.Coprime (Nat.card ↥act.E) (Nat.card ↥act.U) :=
      (act.frobenius.coprime_card_kernel_complement).symm
    have hEnt : 1 < Nat.card ↥act.E := by
      haveI : Nontrivial ↥act.E :=
        act.E.nontrivial_iff_ne_bot.mpr act.frobenius.ne_bot_complement
      exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    have hfpf : ∀ e ∈ act.E, e ≠ 1 → ∀ u ∈ act.U, e * u * e⁻¹ = u → u = 1 := by
      intro e he hne u hu heq
      by_contra hune
      exact act.frobenius.conj_frobenius e he hne u hu hune heq
    -- The canonical `𝔽_{p'}`-module structure on the chief factor `↥N'`.
    letI : CommGroup ↥N' := hpe'.subgroupCommGroup
    letI : Module (ZMod p') (Additive ↥N') := hpe'.subgroupZmodModule
    change WielandtDimIdentity (V := ↥N') p' hN'.restrict act.U act.E
    by_cases hN1 : Nat.card ↥N' = 1
    · -- Trivial chief factor: the module is `0`-dimensional, both sides vanish.
      haveI : Subsingleton ↥N' := (Nat.card_eq_one_iff_unique.mp hN1).1
      haveI : Subsingleton (Additive ↥N') := inferInstanceAs (Subsingleton ↥N')
      simp only [WielandtDimIdentity, Module.finrank_zero_of_subsingleton, mul_zero, add_zero]
    · -- Nontrivial chief factor: `p' ∤ |U|, |E|` (coprimality), so (†) over `𝔽_p` applies.
      haveI : Nontrivial ↥N' := by
        rw [← Finite.one_lt_card_iff_nontrivial]
        have := Nat.card_pos (α := ↥N'); omega
      -- `p' ∣ |N'| ∣ |H'|`, so coprimality forces `p' ∤ |L|`, hence `p' ∤ |U|, |E|`.
      have hpN : p' ∣ Nat.card ↥N' := by
        obtain ⟨x, hx⟩ := exists_ne (1 : ↥N')
        have hdvd : orderOf x ∣ p' := orderOf_dvd_of_pow_eq_one (hpe'.2 x)
        have hox : orderOf x = p' :=
          (hp'.eq_one_or_self_of_dvd _ hdvd).resolve_left
            (fun h => hx (orderOf_eq_one_iff.mp h))
        exact hox ▸ orderOf_dvd_natCard x
      have hpH : p' ∣ Nat.card H' := hpN.trans (Subgroup.card_subgroup_dvd_card N')
      have hpL : ¬ p' ∣ Nat.card L := fun h =>
        hp'.ne_one (Nat.dvd_one.mp (hcop' ▸ Nat.dvd_gcd h hpH))
      have hpU : ¬ p' ∣ Nat.card ↥act.U := fun h =>
        hpL (h.trans (Subgroup.card_subgroup_dvd_card act.U))
      have hpE : ¬ p' ∣ Nat.card ↥act.E := fun h =>
        hpL (h.trans (Subgroup.card_subgroup_dvd_card act.E))
      haveI : Invertible (Fintype.card ↥act.U : ZMod p') := invertibleOfNonzero (by
        rw [← Nat.card_eq_fintype_card]
        intro h; exact hpU ((ZMod.natCast_eq_zero_iff _ p').mp h))
      -- (†) over `𝔽_{p'}` ⟹ the elementary-abelian dimension identity (⋆).
      exact WielandtKernelFPF.wielandtDimIdentity_of_frobenius
        hsup hcopUE hEnt hfpf hpU hpE hN'.restrict
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

/-- **Peterfalvi (9.6), the arithmetic step**: if the Frobenius kernel acts fixed-point-freely
(`C_H(U) = 1`) and `C_H(E)` has order dividing a prime `p` — e.g. `H` is an elementary abelian
`p`-group on which `C_H(E)` is cyclic — then a nontrivial `H` has order `p^{|E|}`.

From `wielandt_fixedPoint_trivial_U_fixed`, `|H| = |C_H(E)|^{|E|}`; the divisibility and primality
pin `|C_H(E)| = p` once `H ≠ 1` rules out `|C_H(E)| = 1`.  This is the final order computation of
Peterfalvi (9.6): `|H̄| = |W̄₂|^q` with `W̄₂` cyclic of order dividing `p`, whence `|H̄| = p^q`. -/
theorem coprimeFrobeniusAction_card_eq_prime_pow {L H : Type*} [Group L] [Group H]
    [Finite L] [Finite H] (act : CoprimeFrobeniusAction L H)
    (hU : act.fixedByU = ⊥) {p : ℕ} (hp : p.Prime)
    (hdvd : Nat.card ↥act.fixedByE ∣ p) (hHne : Nat.card H ≠ 1) :
    Nat.card H = p ^ Nat.card ↥act.E := by
  have key := wielandt_fixedPoint_trivial_U_fixed act hU
  have hCEne : Nat.card ↥act.fixedByE ≠ 1 := by
    intro h; rw [h, one_pow] at key; exact hHne key
  have hCEp : Nat.card ↥act.fixedByE = p :=
    (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left hCEne
  rw [key, hCEp]

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

/-- **Peterfalvi (9.1), the kernel-centralizes corollary (ambient form).**  Let a Frobenius group
`U ⋊ E` (kernel `U`, complement `E`), realised as subgroups of `G` with `U ⊔ E ≤ N_G(N)`, act
coprimely on a finite solvable subgroup `N`.  If the complement `E` acts **fixed-point-freely** on
`N` (`C_N(E) = 1`), then the kernel `U` **centralizes** `N`.

This is the form used in Peterfalvi (13.16): the Frobenius group `K W₂` (kernel `K`, complement
`W₂`) with `C_{Q₁}(W₂) = 1` forces `K` to centralize the Maschke complement `Q₁` of `W₁` in `Q`.
It is the ambient-subgroup packaging of `wielandt_fixedPoint_trivial_E_fixed` (`C_N(E) = 1 ⟹
C_N(U) = N`), built through the conjugation action `U ⊔ E → MulAut N`. -/
theorem frobenius_kernel_centralizes_of_complement_fpf {G : Type*} [Group G] [Finite G]
    {N U E : Subgroup G} (hUEnorm : U ⊔ E ≤ Subgroup.normalizer (N : Set G))
    (hUE : Ch06.IsFrobeniusGroup ↥(U ⊔ E) (U.subgroupOf (U ⊔ E)) (E.subgroupOf (U ⊔ E)))
    (hsolv : IsSolvable ↥N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(U ⊔ E)))
    (hEfpf : ∀ n ∈ N, (∀ e ∈ E, e * n * e⁻¹ = n) → n = 1) :
    U ≤ Subgroup.centralizer (N : Set G) := by
  classical
  letI act : MulDistribMulAction ↥(U ⊔ E) ↥N :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (N : Set G))) ↥N
      (Subgroup.inclusion hUEnorm)
  set φ : ↥(U ⊔ E) →* MulAut ↥N := MulDistribMulAction.toMulAut ↥(U ⊔ E) ↥N with hφ
  have hφ_coe : ∀ (a : ↥(U ⊔ E)) (x : ↥N), ((φ a) x : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun _ _ => rfl
  let act' : CoprimeFrobeniusAction ↥(U ⊔ E) ↥N :=
    { U := U.subgroupOf (U ⊔ E), E := E.subgroupOf (U ⊔ E), frobenius := hUE,
      H_solvable := hsolv, φ := φ, coprime_order := hcop }
  -- `C_N(E) = 1` ⟹ `act'.fixedByE = ⊥`.
  have hE : act'.fixedByE = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    refine OneMemClass.coe_eq_one.mp (hEfpf (n : G) n.2 (fun e he => ?_))
    have heUE : e ∈ U ⊔ E := (le_sup_right : E ≤ U ⊔ E) he
    have hfix := (mem_fixedSubgroup.mp hn) ⟨e, heUE⟩ (Subgroup.mem_subgroupOf.mpr he)
    have hco := hφ_coe ⟨e, heUE⟩ n
    rw [hfix] at hco
    exact hco.symm
  -- Wielandt (9.1): the kernel `U` then fixes all of `N`, i.e. `act'.fixedByU = ⊤`.
  have hU : act'.fixedByU = ⊤ := wielandt_fixedPoint_trivial_E_fixed act' hE
  -- Translate `fixedByU = ⊤` to `U ≤ C_G(N)`.
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have huUE : u ∈ U ⊔ E := (le_sup_left : U ≤ U ⊔ E) hu
  have hnfix : (⟨n, hn⟩ : ↥N) ∈ act'.fixedByU := by rw [hU]; exact Subgroup.mem_top _
  have hfix := (mem_fixedSubgroup.mp hnfix) ⟨u, huUE⟩ (Subgroup.mem_subgroupOf.mpr hu)
  have hco := hφ_coe ⟨u, huUE⟩ ⟨n, hn⟩
  rw [hfix] at hco
  exact (mul_inv_eq_iff_eq_mul.mp hco.symm).symm

/-- **Peterfalvi (9.1), the complement-fixed-point corollary via a sub-Frobenius group.**  Let
`Lsub ≤ G` be a finite Frobenius group with kernel `H`, let `P ≤ H` be a nontrivial subgroup
normalized by a nontrivial `A ≤ Lsub` meeting the kernel trivially (`A ⊓ H = ⊥`).  Suppose the
sub-Frobenius group `P ⊔ A` (kernel `P`, complement `A`) acts coprimely on a finite solvable
subgroup `K` (`P ⊔ A ≤ N_G(K)`) and the kernel `P` does **not** centralize `K`.  Then the complement
`A` has a nontrivial fixed point on `K`: some `1 ≠ n ∈ K` is centralized by all of `A`.

This is the `C_K(A) ≠ 1` step of Peterfalvi (12.11): the sub-Frobenius group `P ⊔ A` is built by
`frobeniusGroup_sup_of_invariant_le_kernel_ambient`, and the conclusion is the contrapositive of
`frobenius_kernel_centralizes_of_complement_fpf` (`C_K(A) = 1 ⟹ P` centralizes `K`). -/
theorem exists_ne_one_centralized_by_complement_of_kernel_not_centralizes
    {G : Type*} [Group G] [Finite G] {Lsub H P A K : Subgroup G} (hHL : H ≤ Lsub)
    (hFrobL : ∃ C : Subgroup ↥Lsub, Ch06.IsFrobeniusGroup ↥Lsub (H.subgroupOf Lsub) C)
    (hPH : P ≤ H) (hPne : P ≠ ⊥) (hAL : A ≤ Lsub) (hAH : A ⊓ H = ⊥) (hAne : A ≠ ⊥)
    (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hPAK : P ⊔ A ≤ Subgroup.normalizer (K : Set G))
    (hKsolv : IsSolvable ↥K)
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(P ⊔ A)))
    (hPnc : ¬ P ≤ Subgroup.centralizer (K : Set G)) :
    ∃ n ∈ K, n ≠ 1 ∧ ∀ a ∈ A, a * n * a⁻¹ = n := by
  classical
  have hFrob := IsFrobeniusGroup.frobeniusGroup_sup_of_invariant_le_kernel_ambient
    hHL hFrobL hPH hPne hAL hAH hAne hAP
  by_contra hcon
  refine hPnc (frobenius_kernel_centralizes_of_complement_fpf hPAK hFrob hKsolv hcop ?_)
  intro n hnK hfix
  by_contra hn1
  exact hcon ⟨n, hnK, hn1, hfix⟩

end FrobeniusCentralizer

end OddOrder.GroupTheory
