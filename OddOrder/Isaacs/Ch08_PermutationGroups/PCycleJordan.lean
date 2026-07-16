/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Isaacs, Finite Group Theory — Ch. 8: the `p`-cycle Jordan theorem (Thm 8.23)

Formalizes **Isaacs Thm 8.23** (pp. 236–237; Wielandt 13.9): a primitive
subgroup `G ≤ Sym(Ω)` containing a `p`-cycle with `p` prime and
`p ≤ |Ω| - 3` contains the alternating group.  This is mathlib's
`proof_wanted alternatingGroup_le_of_isPreprimitive_of_isCycle_mem`
(`Mathlib.GroupTheory.GroupAction.Jordan`).

Current contents: the groundwork —

* agreement-transport lemmas: if permutations agree on an invariant set,
  so do their inverses, products, commutators and powers
  (`commutator_apply_eq_of_agree`, `pow_apply_eq_of_agree`);
* the realization lemma (`exists_agree_of_isMultiplyPretransitive`): an
  `|S|`-transitive subgroup of `Perm α` contains an element agreeing with
  any prescribed permutation on `S`.

The main theorem (Frattini/Sylow correction, centralizer of the `p`-cycle
via `IsCycle.commute_iff`, and the `x^p` three-cycle) follows in this file.
-/

namespace OddOrder.Isaacs.Ch08

open Equiv Equiv.Perm MulAction

open scoped commutatorElement

variable {α : Type*}

/-! ### Agreement transport on an invariant set -/

section Agree

variable {x w x₁ x₂ w₁ w₂ : Perm α} {S : Set α}

/-- Invariance of a set under `w` transfers to `w⁻¹`. -/
private lemma inv_invariant (hwS : ∀ b, b ∈ S ↔ w b ∈ S) (b : α) :
    b ∈ S ↔ w⁻¹ b ∈ S := by
  constructor
  · intro hb
    exact (hwS (w⁻¹ b)).mpr (by simpa using hb)
  · intro hb
    have := (hwS (w⁻¹ b)).mp hb
    simpa using this

/-- Two permutations agreeing on a `w`-invariant set have agreeing
inverses there. -/
private lemma inv_apply_eq_of_agree (hwS : ∀ b, b ∈ S ↔ w b ∈ S)
    (h : ∀ b ∈ S, x b = w b) : ∀ b ∈ S, x⁻¹ b = w⁻¹ b := by
  intro b hb
  have hw : w⁻¹ b ∈ S := (inv_invariant hwS b).mp hb
  have hx : x (w⁻¹ b) = b := (h _ hw).trans (by simp)
  apply x.injective
  rw [hx]
  simp

/-- Agreement on an invariant set is preserved by products. -/
private lemma mul_apply_eq_of_agree (h₂S : ∀ b, b ∈ S ↔ w₂ b ∈ S)
    (h₁ : ∀ b ∈ S, x₁ b = w₁ b) (h₂ : ∀ b ∈ S, x₂ b = w₂ b) :
    ∀ b ∈ S, (x₁ * x₂) b = (w₁ * w₂) b := by
  intro b hb
  rw [Perm.mul_apply, Perm.mul_apply, h₂ b hb]
  exact h₁ _ ((h₂S b).mp hb)

/-- Agreement on an invariant set is preserved by commutators. -/
private lemma commutator_apply_eq_of_agree
    (h₁S : ∀ b, b ∈ S ↔ w₁ b ∈ S) (h₂S : ∀ b, b ∈ S ↔ w₂ b ∈ S)
    (h₁ : ∀ b ∈ S, x₁ b = w₁ b) (h₂ : ∀ b ∈ S, x₂ b = w₂ b) :
    ∀ b ∈ S, ⁅x₁, x₂⁆ b = ⁅w₁, w₂⁆ b := by
  intro b hb
  rw [commutatorElement_def, commutatorElement_def]
  exact mul_apply_eq_of_agree (inv_invariant h₂S)
    (mul_apply_eq_of_agree (inv_invariant h₁S)
      (mul_apply_eq_of_agree h₂S h₁ h₂)
      (inv_apply_eq_of_agree h₁S h₁))
    (inv_apply_eq_of_agree h₂S h₂) b hb

/-- Agreement on an invariant set is preserved by powers. -/
private lemma pow_apply_eq_of_agree (hwS : ∀ b, b ∈ S ↔ w b ∈ S)
    (h : ∀ b ∈ S, x b = w b) (n : ℕ) :
    ∀ b ∈ S, (x ^ n) b = (w ^ n) b := by
  induction n with
  | zero => intro b _; simp
  | succ n ih =>
    intro b hb
    rw [pow_succ, pow_succ, Perm.mul_apply, Perm.mul_apply, h b hb]
    exact ih _ ((hwS b).mp hb)

end Agree

/-! ### Realizing prescribed behavior by multiple transitivity -/

/-- A subgroup of `Perm α` that is `|S|`-transitive contains an element
agreeing with any prescribed permutation on the finset `S`. -/
private lemma exists_agree_of_isMultiplyPretransitive
    {G : Subgroup (Perm α)} {S : Finset α}
    (hT : IsMultiplyPretransitive G α S.card) (τ : Perm α) :
    ∃ k : Perm α, k ∈ G ∧ ∀ b ∈ S, k b = τ b := by
  classical
  haveI := hT
  set e : Fin S.card ≃ {b // b ∈ S} := S.equivFin.symm with he
  set ι₁ : Fin S.card ↪ α :=
    ⟨fun i => ↑(e i), fun i j hij => e.injective (Subtype.ext hij)⟩ with hι₁
  set ι₂ : Fin S.card ↪ α :=
    ⟨fun i => τ ↑(e i), fun i j hij =>
      e.injective (Subtype.ext (τ.injective hij))⟩ with hι₂
  obtain ⟨k, hk⟩ := exists_smul_eq (M := G) ι₁ ι₂
  refine ⟨(k : Perm α), k.2, fun b hb => ?_⟩
  have happ : (k • ι₁) (e.symm ⟨b, hb⟩) = ι₂ (e.symm ⟨b, hb⟩) := by rw [hk]
  rw [Function.Embedding.smul_apply] at happ
  have hb1 : ι₁ (e.symm ⟨b, hb⟩) = b := by simp [hι₁]
  have hb2 : ι₂ (e.symm ⟨b, hb⟩) = τ b := by simp [hι₂]
  rw [hb1, hb2] at happ
  exact happ

/-! ### The pointwise stabilizer of the fixed points of `g` -/

section FixingSubgroup

variable [DecidableEq α] [Fintype α]

/-- A permutation fixing the complement of `g.support` pointwise preserves
`g.support`. -/
private lemma mem_support_iff_of_fixes_compl {g σ : Perm α}
    (hσ : ∀ b ∉ g.support, σ b = b) (b : α) :
    b ∈ g.support ↔ σ b ∈ g.support := by
  constructor
  · intro hb
    by_contra hc
    have h2 : σ b = b := σ.injective (hσ _ hc)
    exact hc (h2.symm ▸ hb)
  · intro hb
    by_contra hc
    exact hc (hσ b hc ▸ hb)

/-- Elements of `G ⊓ fixingSubgroup (supportᶜ)` fix the complement of the
support pointwise. -/
private lemma fixes_compl_of_mem_inf_fixing {G : Subgroup (Perm α)} {g : Perm α}
    {σ : Perm α} (hσ : σ ∈ G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)))
    (b : α) (hb : b ∉ g.support) : σ b = b := by
  have h2 := (Subgroup.mem_inf.mp hσ).2
  rw [mem_fixingSubgroup_iff] at h2
  exact h2 b (by simpa using hb)

/-- **Isaacs Thm 8.23, step (Sylow bound)** — the pointwise stabilizer
`F = G ⊓ fix(supportᶜ)` acts faithfully on the support, so its order
divides `|support g|!`. -/
private lemma card_inf_fixing_dvd_factorial (G : Subgroup (Perm α)) (g : Perm α) :
    Nat.card ↥(G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)))
      ∣ Nat.factorial g.support.card := by
  classical
  set F := G ⊓ fixingSubgroup (Perm α) ((↑g.supportᶜ : Set α)) with hFdef
  set Φ : ↥F →* Perm {b // b ∈ g.support} := MonoidHom.mk'
    (fun σ => (σ : Perm α).subtypePerm fun b =>
      (mem_support_iff_of_fixes_compl (fixes_compl_of_mem_inf_fixing σ.2) b).symm)
    (fun σ₁ σ₂ => by ext b; rfl) with hΦdef
  have hinj : Function.Injective Φ := by
    intro σ₁ σ₂ h
    ext b
    by_cases hb : b ∈ g.support
    · have h2 := congrArg (fun π : Perm {b // b ∈ g.support} => (π ⟨b, hb⟩ : α)) h
      exact h2
    · rw [fixes_compl_of_mem_inf_fixing σ₁.2 b hb,
        fixes_compl_of_mem_inf_fixing σ₂.2 b hb]
  calc Nat.card ↥F
      = Nat.card Φ.range := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    _ ∣ Nat.card (Perm {b // b ∈ g.support}) :=
        Subgroup.card_subgroup_dvd_card _
    _ = Nat.factorial g.support.card := by
        rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_coe]

end FixingSubgroup

/-! ### Sylow conjugation and the abelian-automorphism centralizer step -/

section SylowConj

open scoped Pointwise

variable {M : Type*} [Group M] [Finite M]

/-- **Isaacs Thm 8.23, Frattini correction** — if `F` contains an element
`g` of prime order `p` and `|F| ∣ p!`, then `⟨g⟩` is a full Sylow
`p`-subgroup of `F`, so any `k` conjugating `F` into itself can be corrected
by an element `h ∈ F` so that `h * k` normalizes `⟨g⟩`. -/
private lemma exists_mul_mem_normalizer_zpowers {p : ℕ} (hp : p.Prime)
    {F : Subgroup M} {g : M} (hgF : g ∈ F) (hord : orderOf g = p)
    (hcard : Nat.card F ∣ Nat.factorial p)
    {k : M} (hk : ∀ q ∈ F, k * q * k⁻¹ ∈ F) :
    ∃ h ∈ F, h * k ∈ Subgroup.normalizer (Subgroup.zpowers g) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard0 : Nat.card F ≠ 0 := Nat.card_pos.ne'
  -- `p` divides `|F|` exactly once
  have hordF : orderOf (⟨g, hgF⟩ : F) = p :=
    (orderOf_injective F.subtype F.subtype_injective ⟨g, hgF⟩).symm.trans hord
  have hpF : p ∣ Nat.card F := hordF ▸ orderOf_dvd_natCard (⟨g, hgF⟩ : F)
  have hp2F : ¬ p * p ∣ Nat.card F := by
    intro hc
    have h1 : p * p ∣ Nat.factorial p := hc.trans hcard
    have h2 : Nat.factorial p = p * Nat.factorial (p - 1) :=
      (Nat.mul_factorial_pred hp.pos.ne').symm
    rw [h2] at h1
    have h3 : p ∣ Nat.factorial (p - 1) :=
      (Nat.mul_dvd_mul_iff_left hp.pos).mp h1
    have h4 := (Nat.Prime.dvd_factorial hp).mp h3
    have h5 := hp.pos
    omega
  have hfact : (Nat.card F).factorization p = 1 := by
    have h1 : 1 ≤ (Nat.card F).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp hcard0).mp (by simpa using hpF)
    have h2 : ¬ 2 ≤ (Nat.card F).factorization p := by
      rw [← Nat.Prime.pow_dvd_iff_le_factorization hp hcard0]
      simpa [pow_two] using hp2F
    omega
  -- the two conjugate order-`p` subgroups, as Sylow subgroups of `F`
  have hPle : Subgroup.zpowers g ≤ F := Subgroup.zpowers_le.mpr hgF
  have hgF' : k * g * k⁻¹ ∈ F := hk g hgF
  have hordg' : orderOf (k * g * k⁻¹) = p := by
    have h1 := orderOf_injective (MulAut.conj k).toMonoidHom
      (MulAut.conj k).injective g
    simpa [MulAut.conj_apply, hord] using h1
  have hQle : Subgroup.zpowers (k * g * k⁻¹) ≤ F := Subgroup.zpowers_le.mpr hgF'
  have hcardP : Nat.card ((Subgroup.zpowers g).subgroupOf F) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv,
      Nat.card_zpowers, hord]
  have hcardQ : Nat.card ((Subgroup.zpowers (k * g * k⁻¹)).subgroupOf F) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle).toEquiv,
      Nat.card_zpowers, hordg']
  set SP : Sylow p ↥F := Sylow.ofCard _ (by rw [hcardP, hfact, pow_one])
    with hSP
  set SQ : Sylow p ↥F := Sylow.ofCard _ (by rw [hcardQ, hfact, pow_one])
    with hSQ
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (M := ↥F) SQ SP
  have hsub : MulAut.conj h • (SQ : Subgroup ↥F) = (SP : Subgroup ↥F) := by
    rw [← Sylow.coe_subgroup_smul, hh]
  have hSPcoe : (SP : Subgroup ↥F) = (Subgroup.zpowers g).subgroupOf F := by
    rw [hSP, Sylow.coe_ofCard]
  have hSQcoe : (SQ : Subgroup ↥F) =
      (Subgroup.zpowers (k * g * k⁻¹)).subgroupOf F := by
    rw [hSQ, Sylow.coe_ofCard]
  refine ⟨↑h, h.2, Subgroup.mem_normalizer_iff.mpr fun w => ?_⟩
  constructor
  · -- `w ∈ ⟨g⟩ → (h k) w (h k)⁻¹ ∈ ⟨g⟩`
    intro hw
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hkw : k * w * k⁻¹ ∈ Subgroup.zpowers (k * g * k⁻¹) := by
      rw [← hn, ← conj_zpow]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) n
    have hkwF : k * w * k⁻¹ ∈ F := hk w (hPle hw)
    have hu : (⟨k * w * k⁻¹, hkwF⟩ : ↥F) ∈ (SQ : Subgroup ↥F) := by
      rw [hSQcoe]
      exact Subgroup.mem_subgroupOf.mpr hkw
    have hv : MulAut.conj h • (⟨k * w * k⁻¹, hkwF⟩ : ↥F) ∈ (SP : Subgroup ↥F) := by
      rw [← hsub]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hu
    rw [hSPcoe] at hv
    have hv' := Subgroup.mem_subgroupOf.mp hv
    have hval : ((MulAut.conj h • (⟨k * w * k⁻¹, hkwF⟩ : ↥F) : ↥F) : M) =
        ↑h * (k * w * k⁻¹) * (↑h)⁻¹ := rfl
    rw [hval] at hv'
    have hrw : ↑h * k * w * (↑h * k)⁻¹ = ↑h * (k * w * k⁻¹) * (↑h)⁻¹ := by
      group
    rwa [hrw]
  · -- `(h k) w (h k)⁻¹ ∈ ⟨g⟩ → w ∈ ⟨g⟩`
    intro hw
    have hwF : ↑h * k * w * (↑h * k)⁻¹ ∈ F := hPle hw
    have hv : (⟨↑h * k * w * (↑h * k)⁻¹, hwF⟩ : ↥F) ∈ (SP : Subgroup ↥F) := by
      rw [hSPcoe]
      exact Subgroup.mem_subgroupOf.mpr hw
    have hu : (MulAut.conj h)⁻¹ • (⟨↑h * k * w * (↑h * k)⁻¹, hwF⟩ : ↥F) ∈
        (SQ : Subgroup ↥F) := by
      rw [← Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hsub]
      exact hv
    rw [hSQcoe] at hu
    have hu' := Subgroup.mem_subgroupOf.mp hu
    have hval : (((MulAut.conj h)⁻¹ • (⟨↑h * k * w * (↑h * k)⁻¹, hwF⟩ : ↥F) : ↥F) : M) =
        (↑h)⁻¹ * (↑h * k * w * (↑h * k)⁻¹) * ↑h := rfl
    rw [hval] at hu'
    have hrw : (↑h : M)⁻¹ * (↑h * k * w * (↑h * k)⁻¹) * ↑h = k * w * k⁻¹ := by
      group
    rw [hrw] at hu'
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hu'
    rw [conj_zpow] at hn
    have : g ^ n = w := by
      have := mul_left_cancel (a := k) (mul_right_cancel (b := k⁻¹) hn)
      exact this
    exact this ▸ Subgroup.zpow_mem _ (Subgroup.mem_zpowers g) n

omit [Finite M] in
/-- **Isaacs Thm 8.23, centralizer step** — the automorphism group of the
cyclic group `⟨g⟩` is abelian, so the commutator of two elements
normalizing `⟨g⟩` centralizes it. -/
private lemma commute_commutator_of_mem_normalizer {g x₁ x₂ : M}
    (h₁ : x₁ ∈ Subgroup.normalizer (Subgroup.zpowers g : Set M))
    (h₂ : x₂ ∈ Subgroup.normalizer (Subgroup.zpowers g : Set M)) :
    Commute ⁅x₁, x₂⁆ g := by
  classical
  haveI : IsCyclic ↥(Subgroup.zpowers g) := by
    refine ⟨⟨⟨g, Subgroup.mem_zpowers g⟩, fun w => ?_⟩⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp w.2
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  set φ := (Subgroup.zpowers g).normalizerMonoidHom with hφ
  set c : ↥(Subgroup.normalizer (Subgroup.zpowers g : Set M)) :=
    ⁅(⟨x₁, h₁⟩ : ↥(Subgroup.normalizer (Subgroup.zpowers g : Set M))),
      ⟨x₂, h₂⟩⁆ with hc
  have hker : c ∈ φ.ker := by
    rw [MonoidHom.mem_ker, hc, map_commutatorElement]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    apply (IsCyclic.mulAutMulEquiv _).injective
    rw [map_mul, map_mul, mul_comm]
  rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  have hval : (c : M) = ⁅x₁, x₂⁆ := rfl
  rw [hval] at hker
  exact (Subgroup.mem_centralizer_iff.mp hker g (Subgroup.mem_zpowers g)).symm

end SylowConj

end OddOrder.Isaacs.Ch08
