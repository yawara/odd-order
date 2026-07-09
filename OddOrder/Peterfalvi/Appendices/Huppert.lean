/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S16_NonExistenceG
import OddOrder.BG.Ch3_MaximalSubgroups.S12_Theorem1212

/-!
# Peterfalvi Appendix B: A Special Case of a Theorem of Huppert

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Appendix B (= Appendix I), pp. 135--136.

A group `D` of odd order acts faithfully on an elementary abelian `q`-group `E`
and transitively on `E^#`.  Then `F(D)` is cyclic, acts without fixed points on
`E`, and `D / F(D)` is abelian.

The crucial **fixed-point-free ⟹ cyclic** step is Huppert V.8.15, which is
already formalized in this repository as **BG Proposition 3.9**
(`OddOrder.BG.Ch3.S12.isCyclic_of_coprime_fpf_pgroup_action`, a coprime
fixed-point-free `p`-action of odd `p` is cyclic).  This file records the genuine
group-theoretic content of Appendix B on top of that endpoint:

* `smul_eq_of_sq_smul_eq_of_odd_orderOf` — the odd-order "no transposition" step
  of part (1) of the Lemma ("the second case is impossible since `x` has odd
  order");
* `isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian` — the cyclic conclusion
  for an elementary abelian module, with the coprimality `q ≠ p` *derived* from
  fixed-point-freeness via the `p`-group fixed-point congruence (this is what the
  Lemma silently uses; it is more than a rename of Proposition 3.9);
* `pGroup_cyclic_fixedPointFree` — the Lemma, and
* `fitting_cyclic_fixedPointFree` — Proposition 1.

Proposition 1 is now fully assembled from the per-prime step: `F(D)` is cyclic
(`isCyclic_fitting_of_forall_opCore_isCyclic`), fixed-point-free
(`fitting_fpf_of_transitive`), and `D' ≤ F(D)` for solvable `D`
(`commutator_le_fitting_of_isCyclic_fitting`).

The single remaining `sorry` is the heart of the Lemma: the *irreducible,
non-cyclic* case of the constant-stabilizer ⟹ fixed-point-free argument
(Schur over `𝔽_q` + the normal type-`(p,p)` subgroup, p. 136).  Everything
else — the reducible/Maschke reduction, the abelian-irreducible case, and the
whole of Proposition 1 — is unconditional.
-/

namespace OddOrder.Peterfalvi.Appendices.Huppert

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch06
open OddOrder.BG.Ch3.S12
open OddOrder.Isaacs.Ch03
open OddOrder.BG.Ch1_Preliminary

section Lemma

variable {P E : Type*} [Group P] [Group E]

/-- The point stabilizer `P_a = {x ∈ P | x · a = a}` of a point `a : E` under an
action `φ : P →* MulAut E` (`P_a` in Peterfalvi's Lemma). -/
def pointStabilizer (φ : P →* MulAut E) (a : E) : Subgroup P :=
  (MulAction.stabilizer (MulAut E) a).comap φ

@[simp]
theorem mem_pointStabilizer {φ : P →* MulAut E} {a : E} {x : P} :
    x ∈ pointStabilizer φ a ↔ (φ x) a = a := by
  simp only [pointStabilizer, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rfl

/-- **Peterfalvi Appendix B, Lemma, part (1) odd-order step**: an element of odd
order cannot interchange two points that it permutes.  Concretely, if `g ^ 2`
fixes `a` and `g` has odd order, then `g` already fixes `a`.  (Peterfalvi: "the
second case is impossible since `x` has odd order".) -/
theorem smul_eq_of_sq_smul_eq_of_odd_orderOf
    {M α : Type*} [Group M] [MulAction M α] {g : M} (hodd : Odd (orderOf g))
    {a : α} (h : g ^ 2 • a = a) : g • a = a := by
  have hcop : Nat.Coprime 2 (orderOf g) := Nat.coprime_two_left.mpr hodd
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hstab : g ^ 2 ∈ MulAction.stabilizer M a := MulAction.mem_stabilizer_iff.mpr h
  calc g • a = (g ^ 2) ^ m • a := by rw [hm]
    _ = a := MulAction.mem_stabilizer_iff.mp (pow_mem hstab m)

/-- **Peterfalvi Appendix B, Lemma, part (1) key step**: if `φ x` permutes an
independent family `S` of subgroups of the abelian group `E`, `a ∈ S i`, `b ∈ S j`
(`i ≠ j`, both nontrivial), `x` has odd order and fixes `a * b`, then `x` fixes both
`a` and `b`.

This is Peterfalvi's "`ax = a, bx = b`, or `ax = b, bx = a` (impossible since `x`
has odd order)" dichotomy (p. 135): the components `φ x a ∈ S (perm x i)` and
`φ x b ∈ S (perm x j)` of `a * b = (φ x a)(φ x b)` are pinned to `S i`, `S j` by
independence, and the swap is killed by `smul_eq_of_sq_smul_eq_of_odd_orderOf`. -/
theorem fixes_components_of_permutes_indep
    {ι : Type*} {S : ι → Subgroup E} (hind : iSupIndep S)
    (hcomm : ∀ y z : E, y * z = z * y)
    (φ : P →* MulAut E) (perm : P → Equiv.Perm ι)
    (hperm : ∀ (x : P) (k : ι), (S k).map (φ x).toMonoidHom = S (perm x k))
    {x : P} (hodd : Odd (orderOf x))
    {i j : ι} (hij : i ≠ j) {a b : E} (ha : a ∈ S i) (hb : b ∈ S j)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hfix : (φ x) (a * b) = a * b) :
    (φ x) a = a ∧ (φ x) b = b := by
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  set σi := perm x i with hσi
  set σj := perm x j with hσj
  have hσ_ne : σi ≠ σj := fun h => hij ((perm x).injective h)
  have hxa_mem : (φ x) a ∈ S σi := by
    have h := Subgroup.mem_map_of_mem (φ x).toMonoidHom ha
    rwa [hperm x i] at h
  have hxb_mem : (φ x) b ∈ S σj := by
    have h := Subgroup.mem_map_of_mem (φ x).toMonoidHom hb
    rwa [hperm x j] at h
  have hprod : (φ x) a * (φ x) b = a * b := by rw [← map_mul]; exact hfix
  have hxa1 : (φ x) a ≠ 1 := fun h => ha1 ((φ x).injective (h.trans (map_one (φ x)).symm))
  have hxb1 : (φ x) b ≠ 1 := fun h => hb1 ((φ x).injective (h.trans (map_one (φ x)).symm))
  have hkill : ∀ (c : E) (k l₁ l₂ l₃ : ι), c ∈ S k → c ∈ S l₁ ⊔ S l₂ ⊔ S l₃ →
      k ≠ l₁ → k ≠ l₂ → k ≠ l₃ → c = 1 := by
    intro c k l₁ l₂ l₃ hck hcsup hk1 hk2 hk3
    have hle : S l₁ ⊔ S l₂ ⊔ S l₃ ≤ ⨆ (m) (_ : m ≠ k), S m := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup_of_le l₁ (le_iSup_of_le (Ne.symm hk1) le_rfl)
      · exact le_iSup_of_le l₂ (le_iSup_of_le (Ne.symm hk2) le_rfl)
      · exact le_iSup_of_le l₃ (le_iSup_of_le (Ne.symm hk3) le_rfl)
    exact Subgroup.disjoint_def.mp ((hind k).mono_right hle) hck hcsup
  have hpair : ∀ {p q : ι} {s t : E}, p ≠ q → s ∈ S p → t ∈ S q → s * t = 1 →
      s = 1 ∧ t = 1 := by
    intro p q s t hpq hsp htq hst
    have hdpq : Disjoint (S p) (S q) := hind.pairwiseDisjoint hpq
    have hs1 : s = 1 :=
      Subgroup.disjoint_def.mp hdpq hsp ((mul_eq_one_iff_eq_inv.mp hst).symm ▸ inv_mem htq)
    exact ⟨hs1, by rw [hs1, one_mul] at hst; exact hst⟩
  have hxa_eq : (φ x) a = a * b * ((φ x) b)⁻¹ := eq_mul_inv_iff_mul_eq.mpr hprod
  have hxb_eq : (φ x) b = a * b * ((φ x) a)⁻¹ := by
    rw [mul_comm a b]
    exact eq_mul_inv_iff_mul_eq.mpr
      ((mul_comm ((φ x) b) ((φ x) a)).trans (hprod.trans (mul_comm a b)))
  have hσi_cases : σi = i ∨ σi = j := by
    by_contra hc; push Not at hc
    refine hxa1 (hkill _ σi i j σj hxa_mem ?_ hc.1 hc.2 hσ_ne)
    rw [hxa_eq]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))
      (Subgroup.mem_sup_right (inv_mem hxb_mem))
  have hσj_cases : σj = i ∨ σj = j := by
    by_contra hc; push Not at hc
    refine hxb1 (hkill _ σj i j σi hxb_mem ?_ hc.1 hc.2 (Ne.symm hσ_ne))
    rw [hxb_eq]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))
      (Subgroup.mem_sup_right (inv_mem hxa_mem))
  have hac : ∀ s t : E, ((φ x) a * s) * ((φ x) b * t) = ((φ x) a * (φ x) b) * (s * t) := by
    intro s t; simp only [mul_assoc, mul_comm, mul_left_comm]
  rcases hσi_cases with hi | hi <;> rcases hσj_cases with hj | hj
  · exact absurd (hi.trans hj.symm) hσ_ne
  · rw [hi] at hxa_mem; rw [hj] at hxb_mem
    have huv : ((φ x) a * a⁻¹) * ((φ x) b * b⁻¹) = 1 := by
      rw [hac, hprod, mul_comm a⁻¹ b⁻¹, ← mul_inv_rev, mul_inv_cancel]
    obtain ⟨hu, hv⟩ := hpair hij (mul_mem hxa_mem (inv_mem ha)) (mul_mem hxb_mem (inv_mem hb)) huv
    exact ⟨mul_inv_eq_one.mp hu, mul_inv_eq_one.mp hv⟩
  · exfalso
    rw [hi] at hxa_mem; rw [hj] at hxb_mem
    have huv : ((φ x) a * b⁻¹) * ((φ x) b * a⁻¹) = 1 := by
      rw [hac, hprod, ← mul_inv_rev, mul_inv_cancel]
    obtain ⟨hu, hv⟩ :=
      hpair (Ne.symm hij) (mul_mem hxa_mem (inv_mem hb)) (mul_mem hxb_mem (inv_mem ha)) huv
    have hfa : (φ x) a = b := mul_inv_eq_one.mp hu
    have hfb : (φ x) b = a := mul_inv_eq_one.mp hv
    letI : MulAction P E := MulAction.compHom E φ
    have hsmul : ∀ (y : P) (g : E), y • g = (φ y) g := fun _ _ => rfl
    have hsq : x ^ 2 • a = a := by
      rw [hsmul]
      have hpow : (φ (x ^ 2)) a = (φ x) ((φ x) a) := by rw [map_pow, sq]; rfl
      rw [hpow, hfa, hfb]
    have hcontra := smul_eq_of_sq_smul_eq_of_odd_orderOf hodd hsq
    rw [hsmul, hfa] at hcontra
    exact ha1 (Subgroup.disjoint_def.mp (hind.pairwiseDisjoint hij) ha (hcontra ▸ hb))
  · exact absurd (hi.trans hj.symm) hσ_ne

/-- `P_{a*b} = P_a ⊓ P_b` for components `a ∈ S i`, `b ∈ S j` (`i ≠ j`) of a
permuted independent family (part (1): `P_{a+b} = P_a ∩ P_b`, p. 135). -/
theorem pointStabilizer_mul_eq_inf_of_components
    {ι : Type*} {S : ι → Subgroup E} (hindep : iSupIndep S) (hcomm : ∀ y z : E, y * z = z * y)
    (φ : P →* MulAut E) (perm : P → Equiv.Perm ι)
    (hperm : ∀ (x : P) (k : ι), (S k).map (φ x).toMonoidHom = S (perm x k))
    (hPodd : ∀ x : P, Odd (orderOf x))
    {i j : ι} (hij : i ≠ j) {a b : E} (ha : a ∈ S i) (hb : b ∈ S j) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    pointStabilizer φ (a * b) = pointStabilizer φ a ⊓ pointStabilizer φ b := by
  ext x
  simp only [mem_pointStabilizer, Subgroup.mem_inf]
  constructor
  · intro hx
    exact fixes_components_of_permutes_indep hindep hcomm φ perm hperm (hPodd x) hij ha hb ha1 hb1
      hx
  · rintro ⟨hxa, hxb⟩
    rw [map_mul, hxa, hxb]

/-- `a * b ≠ 1` for nontrivial components in distinct members of an independent family. -/
theorem mul_ne_one_of_components
    {ι : Type*} {S : ι → Subgroup E} (hindep : iSupIndep S)
    {i j : ι} (hij : i ≠ j) {a b : E} (ha : a ∈ S i) (hb : b ∈ S j) (ha1 : a ≠ 1) :
    a * b ≠ 1 := by
  intro h
  exact ha1 (Subgroup.disjoint_def.mp (hindep.pairwiseDisjoint hij) ha
    (mul_eq_one_iff_eq_inv.mp h ▸ inv_mem hb))

/-- **Peterfalvi Appendix B, Lemma, part (1)**: a constant point-stabilizer order forces
equal point stabilizers `P_a = P_b` for components in distinct members of the permuted
independent family (p. 135: `P_a = P_b`). -/
theorem pointStabilizer_eq_of_components_of_constant [Finite P]
    {ι : Type*} {S : ι → Subgroup E} (hindep : iSupIndep S) (hcomm : ∀ y z : E, y * z = z * y)
    (φ : P →* MulAut E) (perm : P → Equiv.Perm ι)
    (hperm : ∀ (x : P) (k : ι), (S k).map (φ x).toMonoidHom = S (perm x k))
    (hPodd : ∀ x : P, Odd (orderOf x))
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (pointStabilizer φ a) = Nat.card (pointStabilizer φ b))
    {i j : ι} (hij : i ≠ j) {a b : E} (ha : a ∈ S i) (hb : b ∈ S j) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    pointStabilizer φ a = pointStabilizer φ b := by
  have hab1 : a * b ≠ 1 := mul_ne_one_of_components hindep hij ha hb ha1
  have hba1 : b * a ≠ 1 := mul_ne_one_of_components hindep (Ne.symm hij) hb ha hb1
  have hinfab := pointStabilizer_mul_eq_inf_of_components hindep hcomm φ perm hperm hPodd
    hij ha hb ha1 hb1
  have hinfba := pointStabilizer_mul_eq_inf_of_components hindep hcomm φ perm hperm hPodd
    (Ne.symm hij) hb ha hb1 ha1
  have hPa : pointStabilizer φ a ⊓ pointStabilizer φ b = pointStabilizer φ a := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [← hinfab]; exact (hconst (a * b) a hab1 ha1).ge
  have hPb : pointStabilizer φ b ⊓ pointStabilizer φ a = pointStabilizer φ b := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [← hinfba]; exact (hconst (b * a) b hba1 hb1).ge
  exact le_antisymm (hPa ▸ inf_le_right) (hPb ▸ inf_le_right)

/-- **Peterfalvi Appendix B, Lemma, part (1)** (full): a `P`-permuted independent
family decomposition `E = ⨆ S i` with `≥ 2` nontrivial members, a faithful odd-order
action, and a constant point-stabilizer order, force the action to be
fixed-point-free.

Proof (p. 135): for a fixed `a₀ ∈ S i₀^#`, every `x ∈ P_{a₀}` fixes each summand
pointwise — `P_{a₀} = P_s` for `s ∈ S k^#` (directly if `k ≠ i₀`, else bridged
through a third summand via `pointStabilizer_eq_of_components_of_constant`) — hence
fixes `⨆ S i = E`, so `φ x = 1` and `x = 1`; thus `P_{a₀} = ⊥`, and by constancy
`P_a = ⊥` for every `a ≠ 1`. -/
theorem fpf_of_constant_stabilizer_of_permuted_decomp [Finite P]
    {ι : Type*} {S : ι → Subgroup E} (hindep : iSupIndep S) (hsup : ⨆ i, S i = ⊤)
    (hcomm : ∀ y z : E, y * z = z * y)
    (φ : P →* MulAut E) (hfaithful : Function.Injective φ)
    (perm : P → Equiv.Perm ι)
    (hperm : ∀ (x : P) (k : ι), (S k).map (φ x).toMonoidHom = S (perm x k))
    (hPodd : ∀ x : P, Odd (orderOf x))
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (pointStabilizer φ a) = Nat.card (pointStabilizer φ b))
    (htwo : ∃ i₁ i₂ : ι, i₁ ≠ i₂ ∧ S i₁ ≠ ⊥ ∧ S i₂ ≠ ⊥) :
    ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
  have peq : ∀ {i j : ι} {a b : E}, i ≠ j → a ∈ S i → b ∈ S j → a ≠ 1 → b ≠ 1 →
      pointStabilizer φ a = pointStabilizer φ b :=
    fun hij ha hb ha1 hb1 =>
      pointStabilizer_eq_of_components_of_constant hindep hcomm φ perm hperm hPodd hconst
        hij ha hb ha1 hb1
  have hother : ∀ k : ι, ∃ m, m ≠ k ∧ S m ≠ ⊥ := by
    obtain ⟨i₁, i₂, h12, hn1, hn2⟩ := htwo
    intro k
    rcases eq_or_ne k i₁ with rfl | hk1
    · exact ⟨i₂, Ne.symm h12, hn2⟩
    · exact ⟨i₁, Ne.symm hk1, hn1⟩
  obtain ⟨i₀, _, _, hi₀nt, _⟩ := htwo
  obtain ⟨a₀, ha₀, ha₀1⟩ := (S i₀).bot_or_exists_ne_one.resolve_left hi₀nt
  have hPa0_bot : pointStabilizer φ a₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hfix_summand : ∀ (k : ι) (s : E), s ∈ S k → (φ x) s = s := by
      intro k s hsk
      rcases eq_or_ne s 1 with rfl | hs1
      · exact map_one (φ x)
      · have hPas : pointStabilizer φ a₀ = pointStabilizer φ s := by
          rcases eq_or_ne k i₀ with hki | hki
          · have hsk' : s ∈ S i₀ := hki ▸ hsk
            obtain ⟨m, hmi, hmnt⟩ := hother i₀
            obtain ⟨c, hcm, hc1⟩ := (S m).bot_or_exists_ne_one.resolve_left hmnt
            exact (peq (Ne.symm hmi) ha₀ hcm ha₀1 hc1).trans
              (peq (Ne.symm hmi) hsk' hcm hs1 hc1).symm
          · exact peq (Ne.symm hki) ha₀ hsk ha₀1 hs1
        exact mem_pointStabilizer.mp (hPas ▸ hx)
    have htop : actionFixedBy φ x = ⊤ := by
      rw [eq_top_iff, ← hsup, iSup_le_iff]
      intro k s hsk
      exact mem_actionFixedBy.mpr (hfix_summand k s hsk)
    have hφx1 : φ x = 1 := by
      ext e
      have he : e ∈ actionFixedBy φ x := by rw [htop]; exact Subgroup.mem_top e
      simpa using mem_actionFixedBy.mp he
    exact hfaithful (hφx1.trans (map_one φ).symm)
  intro x hx1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  by_contra ha1
  have hPa_bot : pointStabilizer φ a = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [hconst a a₀ ha1 ha₀1, hPa0_bot, Subgroup.card_bot])
  have hxa : x ∈ pointStabilizer φ a := mem_pointStabilizer.mpr (mem_actionFixedBy.mp ha)
  rw [hPa_bot, Subgroup.mem_bot] at hxa
  exact hx1 hxa

/-- **Peterfalvi Appendix B, Lemma, part (2), cyclic case**: an abelian group acting
faithfully and irreducibly on `E` acts fixed-point-freely (p. 135: "Suppose that `P`
is cyclic.  Then ... `C_E(x) = 0` and so `P` acts without fixed points").  For `x ≠ 1`
the fixed subgroup `C_E(x) = actionFixedBy φ x` is `P`-invariant (commutativity) and
`≠ E` (faithfulness), hence `= ⊥` by irreducibility. -/
theorem fpf_of_abelian_of_irreducible
    (φ : P →* MulAut E) (hfaithful : Function.Injective φ) (hPab : ∀ x y : P, x * y = y * x)
    (hirr : ∀ H : Subgroup E, (∀ (y : P) (e : E), e ∈ H → φ y e ∈ H) → H = ⊥ ∨ H = ⊤) :
    ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
  intro x hx1
  have hinv : ∀ (y : P) (e : E), e ∈ actionFixedBy φ x → φ y e ∈ actionFixedBy φ x := by
    intro y e he
    rw [mem_actionFixedBy] at he ⊢
    have e1 : (φ (x * y)) e = (φ x) ((φ y) e) := by rw [map_mul]; rfl
    have e2 : (φ (y * x)) e = (φ y) ((φ x) e) := by rw [map_mul]; rfl
    have hcomm_act : (φ x) ((φ y) e) = (φ y) ((φ x) e) := by rw [← e1, ← e2, hPab x y]
    rw [hcomm_act, he]
  rcases hirr _ hinv with h | h
  · exact h
  · exfalso
    apply hx1
    apply hfaithful
    rw [map_one]
    ext e
    have he : e ∈ actionFixedBy φ x := by rw [h]; exact Subgroup.mem_top e
    simpa using mem_actionFixedBy.mp he

/-- **Peterfalvi Appendix B, Lemma, part (1) — reducible case**: part (1) applied to a
`P`-invariant complement `E = U ⊕ W` (both nontrivial), via the trivial permutation of
the two summands.  A Maschke complement of a proper nonzero `P`-submodule feeds this. -/
theorem fpf_of_constant_stabilizer_of_invariant_compl [Finite P]
    (hcomm : ∀ y z : E, y * z = z * y)
    (φ : P →* MulAut E) (hfaithful : Function.Injective φ)
    {U W : Subgroup E} (hcompl : IsCompl U W) (hU : U ≠ ⊥) (hW : W ≠ ⊥)
    (hUinv : ∀ x : P, U.map (φ x).toMonoidHom = U)
    (hWinv : ∀ x : P, W.map (φ x).toMonoidHom = W)
    (hPodd : ∀ x : P, Odd (orderOf x))
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (pointStabilizer φ a) = Nat.card (pointStabilizer φ b)) :
    ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
  refine fpf_of_constant_stabilizer_of_permuted_decomp (S := fun b : Bool => cond b U W)
    ?_ ?_ hcomm φ hfaithful (fun _ => Equiv.refl Bool) ?_ hPodd hconst ?_
  · exact (iSupIndep_pair (i := true) (j := false) (by decide) (by decide)).mpr hcompl.disjoint
  · rw [iSup_bool_eq]
    exact hcompl.sup_eq_top
  · intro x k
    cases k
    · exact hWinv x
    · exact hUinv x
  · exact ⟨true, false, by decide, hU, hW⟩

/-- **Peterfalvi Appendix B, Lemma — cyclic conclusion** for an elementary
abelian module.  A `p`-group `P` (`p` odd) acting faithfully and fixed-point-freely
on a nontrivial elementary abelian `q`-group `E` is cyclic.

The coprimality `q ≠ p` is *derived* from fixed-point-freeness: were `q = p`, the
`p`-group `P` acting on the nontrivial `p`-group `E` would have a nonzero common
fixed point (the `p`-group fixed-point congruence), contradicting
fixed-point-freeness; given coprimality, cyclicity is **BG Proposition 3.9**. -/
theorem isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian
    [Finite P] [Finite E] {p q : ℕ} [Fact p.Prime] (hq : q.Prime) [Nontrivial E]
    (hP : IsPGroup p P) (hp_odd : Odd p) (hE : IsElementaryAbelian q E)
    (φ : P →* MulAut E)
    (hfpf : ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥) :
    IsCyclic P := by
  rcases subsingleton_or_nontrivial P with _ | hPnt
  · exact isCyclic_of_subsingleton
  · haveI : Fact q.Prime := ⟨hq⟩
    letI : MulAction P E := MulAction.compHom E φ
    have hsmul : ∀ (x : P) (e : E), x • e = (φ x) e := fun _ _ => rfl
    -- Step 1: `q ≠ p`, derived from fixed-point-freeness.
    have hqp : q ≠ p := by
      intro hqeq
      have h1lt : 1 < Nat.card E := Finite.one_lt_card
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hE.isPGroup
      have hn0 : n ≠ 0 := by rintro rfl; simp only [pow_zero] at hn; omega
      have hqdvd : q ∣ Nat.card E := hn ▸ dvd_pow_self q hn0
      -- `P` is a `q`-group too, since `p = q`.
      have hPq : IsPGroup q P := by rw [hqeq]; exact hP
      have hmod := hPq.card_modEq_card_fixedPoints E
      have hpfix : q ∣ Nat.card (MulAction.fixedPoints P E) :=
        (Nat.modEq_zero_iff_dvd).mp
          (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hqdvd))
      haveI : Nonempty (MulAction.fixedPoints P E) :=
        ⟨⟨1, fun g => by rw [hsmul]; exact map_one (φ g)⟩⟩
      have hfix_pos : 0 < Nat.card (MulAction.fixedPoints P E) := Nat.card_pos
      have hp2 : 2 ≤ q := hq.two_le
      have hfix_gt1 : 1 < Nat.card (MulAction.fixedPoints P E) :=
        lt_of_lt_of_le one_lt_two (hp2.trans (Nat.le_of_dvd hfix_pos hpfix))
      haveI : Nontrivial (MulAction.fixedPoints P E) :=
        Finite.one_lt_card_iff_nontrivial.mp hfix_gt1
      -- a nonidentity common fixed point contradicts fixed-point-freeness
      have key : ∀ e : ↥(MulAction.fixedPoints P E), (e : E) ≠ 1 → False := by
        intro e he_ne
        obtain ⟨x, hx⟩ := exists_ne (1 : P)
        have hxe : (φ x) (e : E) = (e : E) := by
          have hge := e.property x; rwa [hsmul] at hge
        have hmem : (e : E) ∈ actionFixedBy φ x := mem_actionFixedBy.mpr hxe
        rw [hfpf x hx, Subgroup.mem_bot] at hmem
        exact he_ne hmem
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(MulAction.fixedPoints P E))
      rcases eq_or_ne (a : E) 1 with ha1 | ha1
      · exact key b (fun hb1 => hab (Subtype.ext (ha1.trans hb1.symm)))
      · exact key a ha1
    -- Step 2: coprimality of the `p`-power `|P|` and the `q`-power `|E|`, then Prop 3.9.
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p)).mp hP
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hE.isPGroup
    have hcop : Nat.Coprime (Nat.card P) (Nat.card E) := by
      rw [hm, hn]
      exact ((Nat.coprime_primes Fact.out hq).mpr (Ne.symm hqp)).pow m n
    exact isCyclic_of_coprime_fpf_pgroup_action hP hp_odd hcop φ hfpf

end Lemma

section Maschke

variable {E : Type*} [Group E] [Finite E] {P : Type*} [Group P] [Finite P]

/-- **Operator Maschke for an elementary abelian group**: a coprime `MulAut`-action of `P`
on an elementary abelian `q`-group `E` splits any `P`-invariant subgroup off via a
`P`-invariant complement.  This is the module-Maschke input for the Lemma's reducible
case (`fpf_of_constant_stabilizer_of_invariant_compl`): a proper nonzero `P`-invariant
subgroup gives a `P`-invariant complement `E = U ⊕ W`. -/
theorem exists_aInvariant_complement_of_elementaryAbelian
    {q : ℕ} [Fact q.Prime] (hqE : q ∣ Nat.card E) {φ : P →* MulAut E}
    (hcop : Nat.Coprime (Nat.card P) (Nat.card E)) (hE : IsElementaryAbelian q E)
    {U : Subgroup E} (hUinv : IsAInvariant φ U) :
    ∃ W : Subgroup E, IsAInvariant φ W ∧ U ⊓ W = ⊥ ∧ U ⊔ W = ⊤ := by
  classical
  haveI hEcomm : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.comm }
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hqsmul : ∀ x : Additive E, (q : ℕ) • x = 0 := by
    intro x; apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]; exact hE.pow_eq_one x.toMul
  haveI : Module (ZMod q) (Additive E) := AddCommGroup.zmodModule hqsmul
  haveI : NeZero ((Nat.card P : ZMod q)) := neZero_natCast_zmod_of_coprime hcop hqE
  set ρ : Representation (ZMod q) P (Additive E) := (mulAutToEnd E q).comp φ with hρ_def
  have key_rho : ∀ (a : P) (v : Additive E),
      Additive.toMul (ρ a v) = (φ a) (Additive.toMul v) := fun _ _ => rfl
  set pU := AddSubgroup.toZModSubmodule (n := q) (Subgroup.toAddSubgroup U) with hpU_def
  have hmem_pU : ∀ v : Additive E, v ∈ pU ↔ Additive.toMul v ∈ U := by
    intro v
    simp only [hpU_def, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
  have hpU_invt : pU ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    rw [hmem_pU] at hv ⊢
    rw [key_rho]
    exact hUinv.smul_mem a hv
  have hpU_sub : ∀ (a : P) ⦃v : Additive E⦄, v ∈ pU → ρ a v ∈ pU := by
    intro a v hv
    have hmem := ρ.mem_invtSubmodule.mp hpU_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem v hv
  obtain ⟨qcSub, hcompl⟩ :=
    ComplementedLattice.exists_isCompl (⟨pU, hpU_sub⟩ : Subrepresentation ρ)
  set qc : Submodule (ZMod q) (Additive E) := qcSub.toSubmodule with hqc_def
  have hqc_invt : qc ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact fun v hv => qcSub.apply_mem_toSubmodule a hv
  -- `(⊓/⊔).toSubmodule` and `⊥/⊤.toSubmodule` are defeq projections (wave6 OperatorMaschke パターン).
  have hinf : pU ⊓ qc = ⊥ := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
  have hsup : pU ⊔ qc = ⊤ := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
  let Φ : Submodule (ZMod q) (Additive E) ≃o Subgroup E :=
    (AddSubgroup.toZModSubmodule (n := q)).symm.trans AddSubgroup.toSubgroup'
  set W : Subgroup E := Φ qc with hW_def
  have hΦpU : Φ pU = U := by
    have h1 : (AddSubgroup.toZModSubmodule (n := q)).symm pU = Subgroup.toAddSubgroup U := by
      rw [hpU_def, OrderIso.symm_apply_apply]
    simp only [Φ, OrderIso.trans_apply, h1]
    exact Subgroup.toAddSubgroup.symm_apply_apply U
  have hmem_W : ∀ h : E, h ∈ W ↔ (Additive.ofMul h) ∈ qc := by
    intro h
    rw [hW_def]
    simp only [Φ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]
  have hW_inv : IsAInvariant φ W := by
    rw [isAInvariant_iff_smul_mem]
    intro a h hh
    rw [hmem_W] at hh ⊢
    have hmem := ρ.mem_invtSubmodule.mp hqc_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem _ hh
  refine ⟨W, hW_inv, ?_, ?_⟩
  · have h := congrArg Φ hinf; rwa [Φ.map_inf, Φ.map_bot, hΦpU, ← hW_def] at h
  · have h := congrArg Φ hsup; rwa [Φ.map_sup, Φ.map_top, hΦpU, ← hW_def] at h

/-- **Peterfalvi Appendix B, Lemma — reducible case**: if the faithful coprime odd-order
action of `P` on the elementary abelian `q`-group `E` admits a proper nonzero `P`-invariant
subgroup `U`, then a constant point-stabilizer order forces the action to be
fixed-point-free.  Maschke (`exists_aInvariant_complement_of_elementaryAbelian`) splits off a
`P`-invariant complement `E = U ⊕ W`, which feeds the invariant-complement form of part (1). -/
theorem fpf_of_reducible
    {q : ℕ} [Fact q.Prime] (hqE : q ∣ Nat.card E)
    (hcop : Nat.Coprime (Nat.card P) (Nat.card E)) (hE : IsElementaryAbelian q E)
    (φ : P →* MulAut E) (hfaithful : Function.Injective φ)
    (hPodd : ∀ x : P, Odd (orderOf x))
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card (pointStabilizer φ a) = Nat.card (pointStabilizer φ b))
    {U : Subgroup E} (hUinv : IsAInvariant φ U) (hUbot : U ≠ ⊥) (hUtop : U ≠ ⊤) :
    ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
  obtain ⟨W, hWinv, hinf, hsup⟩ :=
    exists_aInvariant_complement_of_elementaryAbelian hqE hcop hE hUinv
  have hWbot : W ≠ ⊥ := by rintro rfl; rw [sup_bot_eq] at hsup; exact hUtop hsup
  have hcompl : IsCompl U W := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  have conv : ∀ {V : Subgroup E}, IsAInvariant φ V → ∀ x : P, V.map (φ x).toMonoidHom = V := by
    intro V hV x
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩; exact hV.smul_mem x hg
    · intro u hu
      exact ⟨(φ x)⁻¹ u, hV.inv_smul_mem x hu, MulAut.apply_inv_self E (φ x) u⟩
  exact fpf_of_constant_stabilizer_of_invariant_compl hE.comm φ hfaithful hcompl hUbot hWbot
    (conv hUinv) (conv hWinv) hPodd hconst

/-- **Peterfalvi Appendix B, Lemma**: let `p ≠ 2` be prime, `q ≠ p`, and let the `p`-group
`P` act faithfully on the elementary abelian `q`-group `E`.  If `|P_a|` is the same for every
`a ∈ E^#`, then `P` is cyclic and acts without fixed points on `E`.

Case split (p. 135--136): if `P` acts reducibly, `fpf_of_reducible` (Maschke + part (1));
if irreducibly and `P` is cyclic, `fpf_of_abelian_of_irreducible` (part (2) cyclic case); the
remaining irreducible non-cyclic case (Schur's Lemma ⟹ `E = ⊕ C_E(Tᵢ)` ⟹ part (1)) is the
sole remaining gap.  Cyclicity then follows from
`isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian`.

(`q ≠ p` is a hypothesis; for nontrivial `P` it is forced by the other hypotheses — `q = p`
would make `P` act on the `p`-group `E` with a nonzero common fixed point, which the constant
stabilizer order propagates to all of `E^#`, contradicting faithfulness.) -/
theorem pGroup_cyclic_fixedPointFree
    {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hqp : q ≠ p) [Nontrivial E]
    (hP : IsPGroup p P) (hp_odd : Odd p) (hE : IsElementaryAbelian q E)
    (φ : P →* MulAut E) (hfaithful : Function.Injective φ)
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card ↥(pointStabilizer φ a) = Nat.card ↥(pointStabilizer φ b)) :
    IsCyclic P ∧ ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqE : q ∣ Nat.card E := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hE.isPGroup
    have hn0 : n ≠ 0 := by
      rintro rfl; simp only [pow_zero] at hn
      exact absurd hn (by have := Finite.one_lt_card (α := E); omega)
    exact hn ▸ dvd_pow_self q hn0
  have hcop : Nat.Coprime (Nat.card P) (Nat.card E) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p)).mp hP
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hE.isPGroup
    rw [hm, hn]; exact ((Nat.coprime_primes Fact.out hq).mpr (Ne.symm hqp)).pow m n
  have hPodd : ∀ x : P, Odd (orderOf x) := by
    intro x
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p)).mp hP
    have h2pm : Nat.Coprime 2 (p ^ m) := Nat.coprime_two_left.mpr hp_odd.pow
    exact Nat.coprime_two_left.mp (h2pm.coprime_dvd_right (hm ▸ orderOf_dvd_natCard x))
  have hfpf : ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
    by_cases hirr : ∀ U : Subgroup E, IsAInvariant φ U → U = ⊥ ∨ U = ⊤
    · by_cases hcyc : IsCyclic P
      · haveI := hcyc
        letI : CommGroup P := IsCyclic.commGroup
        refine fpf_of_abelian_of_irreducible φ hfaithful (fun x y => mul_comm x y) ?_
        intro H hH
        exact hirr H (isAInvariant_iff_smul_mem.mpr hH)
      · -- Irreducible non-cyclic case (p. 136).  Peterfalvi's argument:
        -- [H] III.7.5 gives a *normal* `R ⊴ P` of type `(p,p)`; Schur ([Is] 1.5)
        -- makes `End_{𝔽_q[P]}(E)` a finite field, so `Z(P)` (in its unit group) is
        -- cyclic, whence `|R ∩ Z(P)| = p` and `P` transitively permutes the other `p`
        -- order-`p` subgroups `Tᵢ ≤ R`; `E = ⊕ C_E(Tᵢ)` (coprime `Z_p×Z_p` action) is
        -- a `P`-permuted decomposition with `≥ 2` parts, so part (1)
        -- (`fpf_of_constant_stabilizer_of_permuted_decomp`) forces `P` cyclic — contra.
        -- BLOCKER: the normal type-`(p,p)` step is [H] III.7.5 = Gorenstein 5.4.10.  Schur
        -- forces `Z(P)` cyclic, so `Ω₁(Z(P))` has order `p` and the repo's available
        -- `exists_normal_isElementaryAbelian_card_prime_sq_of_prime_sq_dvd_card_omega1Center`
        -- (abelian-center case) does NOT apply — this is exactly the cyclic-center case
        -- deferred in `BG/Ch1_Preliminary/S04_PGroupsSmallRank.lean` (≈ line 911).  See
        -- issue 2004.  Off-FT-critical-path (Appendix B = Peterfalvi Part II).
        sorry
    · push Not at hirr
      obtain ⟨U, hUinv, hUbot, hUtop⟩ := hirr
      exact fpf_of_reducible hqE hcop hE φ hfaithful hPodd hconst hUinv hUbot hUtop
  exact ⟨isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian hq hP hp_odd hE φ hfpf, hfpf⟩

end Maschke

section Proposition1

variable {D E : Type*} [Group D] [Group E]

/-- **Peterfalvi Appendix B, Proposition 1 — irreducibility from transitivity**: a group
acting transitively on `E^#` acts irreducibly, i.e. every `D`-invariant subgroup of `E` is
`⊥` or `⊤`.  (`E ⋊ D` then acts doubly transitively on `E`, p. 135.) -/
theorem isAInvariant_eq_bot_or_top_of_transitive
    (φ : D →* MulAut E)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ g : D, (φ g) a = b)
    {U : Subgroup E} (hU : IsAInvariant φ U) : U = ⊥ ∨ U = ⊤ := by
  rcases eq_or_ne U ⊥ with h | h
  · exact Or.inl h
  · refine Or.inr (eq_top_iff.mpr fun b _ => ?_)
    rcases eq_or_ne b 1 with rfl | hb1
    · exact one_mem U
    · obtain ⟨a, haU, ha1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left h
      obtain ⟨g, hg⟩ := htrans a b ha1 hb1
      exact hg ▸ hU.smul_mem g haU

/-- **Peterfalvi Appendix B, Proposition 1 — no normal `q`-subgroup**: a faithful irreducible
action of `D` on the elementary abelian `q`-group `E` admits no nontrivial normal `q`-subgroup.
(So for `D` acting transitively on `E^#`, `q ∤ |F(D)|`, i.e. every Fitting prime is `≠ q`.)
The fixed subgroup `C_E(N)` is `D`-invariant (normality) and nonzero (the `q`-group `N` acts on
the `q`-group `E`), so by irreducibility `C_E(N) = E`, forcing `N ≤ ker φ = ⊥` (faithfulness). -/
theorem normal_isPGroup_eq_bot_of_faithful_irreducible
    [Finite E] {q : ℕ} [Fact q.Prime] (hqE : q ∣ Nat.card E)
    (φ : D →* MulAut E) (hfaithful : Function.Injective φ)
    (hirr : ∀ U : Subgroup E, IsAInvariant φ U → U = ⊥ ∨ U = ⊤)
    {N : Subgroup D} (hNnorm : N.Normal) (hNq : IsPGroup q ↥N) :
    N = ⊥ := by
  have hCinv : IsAInvariant φ (actionFixedPoints φ N) := by
    rw [isAInvariant_iff_smul_mem]
    intro d e he n
    rw [mem_actionFixedPoints] at he
    have hmem : d⁻¹ * (n : D) * d ∈ N := by
      have h := hNnorm.conj_mem (n : D) n.2 d⁻¹; simpa using h
    calc (φ (n : D)) ((φ d) e)
        = (φ ((n : D) * d)) e := by rw [map_mul]; rfl
      _ = (φ (d * (d⁻¹ * (n : D) * d))) e := by
          rw [show (n : D) * d = d * (d⁻¹ * (n : D) * d) by group]
      _ = (φ d) ((φ (d⁻¹ * (n : D) * d)) e) := by rw [map_mul]; rfl
      _ = (φ d) e := by rw [he ⟨d⁻¹ * (n : D) * d, hmem⟩]
  have hCne : actionFixedPoints φ N ≠ ⊥ := by
    letI : MulAction ↥N E := MulAction.compHom E (φ.comp N.subtype)
    have hsmul : ∀ (n : ↥N) (e : E), n • e = (φ (n : D)) e := fun _ _ => rfl
    have hmod := hNq.card_modEq_card_fixedPoints E
    have hpfix : q ∣ Nat.card (MulAction.fixedPoints ↥N E) :=
      (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hqE))
    haveI : Nonempty (MulAction.fixedPoints ↥N E) :=
      ⟨⟨1, fun n => by rw [hsmul]; exact map_one _⟩⟩
    have hpos : 0 < Nat.card (MulAction.fixedPoints ↥N E) := Nat.card_pos
    have hgt1 : 1 < Nat.card (MulAction.fixedPoints ↥N E) :=
      lt_of_lt_of_le one_lt_two ((Fact.out : q.Prime).two_le.trans (Nat.le_of_dvd hpos hpfix))
    haveI : Nontrivial (MulAction.fixedPoints ↥N E) := Finite.one_lt_card_iff_nontrivial.mp hgt1
    obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(MulAction.fixedPoints ↥N E))
    have key : ∀ c : ↥(MulAction.fixedPoints ↥N E), (c : E) ≠ 1 → actionFixedPoints φ N ≠ ⊥ := by
      intro c hc hbot
      have hcmem : (c : E) ∈ actionFixedPoints φ N := by
        rw [mem_actionFixedPoints]; intro n
        have := c.property n; rwa [hsmul] at this
      rw [hbot, Subgroup.mem_bot] at hcmem
      exact hc hcmem
    rcases eq_or_ne (a : E) 1 with ha1 | ha1
    · exact key b (fun hb1 => hab (Subtype.ext (ha1.trans hb1.symm)))
    · exact key a ha1
  rcases hirr _ hCinv with h | h
  · exact (hCne h).elim
  · rw [eq_bot_iff]
    intro n hn
    rw [Subgroup.mem_bot]
    have hφn1 : φ n = 1 := by
      ext e
      have he : e ∈ actionFixedPoints φ N := by rw [h]; exact Subgroup.mem_top e
      rw [mem_actionFixedPoints] at he
      simpa using he ⟨n, hn⟩
    exact hfaithful (hφn1.trans (map_one φ).symm)

/-- **Peterfalvi Appendix B, Proposition 1 bridge**: if `D` acts transitively on
`E^#` and `N ⊴ D`, then the `N`-point-stabilizers `N_a`, `N_b` of any two
nonidentity points have the same order — they are conjugate in `D` (`N_b = d N_a
d⁻¹` for any `d` with `d·a = b`, using normality of `N`).

This is exactly Peterfalvi's "`P_a` and `P_b` are conjugate in `D`" step (p. 136),
which supplies the constant point-stabilizer hypothesis of the Lemma for the
characteristic subgroups `N = O_p(F(D))`. -/
theorem card_pointStabilizer_comp_eq_of_normal_of_transitive
    (φ : D →* MulAut E) {N : Subgroup D} (hN : N.Normal)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, (φ d) a = b)
    {a b : E} (ha : a ≠ 1) (hb : b ≠ 1) :
    Nat.card ↥(pointStabilizer (φ.comp N.subtype) a) =
      Nat.card ↥(pointStabilizer (φ.comp N.subtype) b) := by
  obtain ⟨d, hd⟩ := htrans a b ha hb
  have happ : ∀ (g h : D) (e : E), (φ (g * h)) e = (φ g) ((φ h) e) := fun g h e => by
    rw [map_mul]; rfl
  have hinv : ∀ (g : D) (e : E), (φ g⁻¹) e = (φ g).symm e := fun g e => by
    rw [map_inv]; rfl
  have hsymm : (φ d).symm b = a := by rw [← hd]; exact (φ d).symm_apply_apply a
  -- conjugation by `d` (resp. `d⁻¹`) carries the `a`-stabilizer to the `b`-stabilizer.
  have hfix : ∀ x : D, (φ x) a = a → (φ (d * x * d⁻¹)) b = b := by
    intro x hx; rw [happ, happ, hinv, hsymm, hx, hd]
  have hfix' : ∀ y : D, (φ y) b = b → (φ (d⁻¹ * y * d)) a = a := by
    intro y hy; rw [happ, happ, hd, hy, hinv, ← hd]; exact (φ d).symm_apply_apply a
  refine Nat.card_congr ⟨fun s => ⟨⟨d * (s.1 : D) * d⁻¹, hN.conj_mem _ s.1.2 d⟩,
      mem_pointStabilizer.mpr (hfix _ (mem_pointStabilizer.mp s.2))⟩,
    fun t => ⟨⟨d⁻¹ * (t.1 : D) * d, hN.conj_mem' _ t.1.2 d⟩,
      mem_pointStabilizer.mpr (hfix' _ (mem_pointStabilizer.mp t.2))⟩,
    fun s => ?_, fun t => ?_⟩
  · apply Subtype.ext; apply Subtype.ext; show d⁻¹ * (d * (s.1 : D) * d⁻¹) * d = (s.1 : D); group
  · apply Subtype.ext; apply Subtype.ext; show d * (d⁻¹ * (t.1 : D) * d) * d⁻¹ = (t.1 : D); group

/-- **Peterfalvi Appendix B, Proposition 1 — the abelian-quotient step**: for a
finite solvable group `D` whose Fitting subgroup `F(D)` is cyclic, `D/F(D)` is
abelian, i.e. `commutator D ≤ F(D)`.

Proof (Peterfalvi p. 136, last paragraph): `D` acts on `F = F(D)` by conjugation
(`MulAut.conjNormal : D →* MulAut F`) with kernel `C_D(F)`; `MulAut F` is abelian
because `F` is cyclic, so `commutator D ≤ ker = C_D(F) ≤ F`, the last inclusion
being self-centralization of the Fitting subgroup in a solvable group
(`centralizer_fitting_le_fitting`). -/
theorem commutator_le_fitting_of_isCyclic_fitting
    [Finite D] [IsSolvable D] (hcyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting D)) :
    commutator D ≤ OddOrder.Isaacs.Ch01.fitting D := by
  set F : Subgroup D := OddOrder.Isaacs.Ch01.fitting D with hF
  haveI : F.Normal := OddOrder.Isaacs.Ch01.fitting.normal D
  haveI : IsCyclic ↥F := hcyc
  letI : CommGroup (MulAut ↥F) :=
    (IsCyclic.mulAutMulEquiv (G := ↥F)).toMonoidHom.commGroupOfInjective
      (IsCyclic.mulAutMulEquiv (G := ↥F)).injective
  refine (Abelianization.commutator_subset_ker (MulAut.conjNormal (H := F))).trans ?_
  refine le_trans ?_ (hF ▸ OddOrder.BG.Ch1.S01.centralizer_fitting_le_fitting (G := D))
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_centralizer_iff]
  intro x hxF
  have hap := MulAut.conjNormal_apply (H := F) g ⟨x, hxF⟩
  rw [hg] at hap
  simp only [MulAut.one_apply] at hap
  -- `hap : (x : D) = g * x * g⁻¹`
  exact (mul_inv_eq_iff_eq_mul.mp hap.symm).symm

/-- **Peterfalvi Appendix B, Proposition 1 — per-prime `O_p` step**: under the hypotheses
of Proposition 1, each `p`-core `O_p(D) = opCore p D` is cyclic and acts without fixed points
on `E`.  For `O_p = ⊥` this is trivial; otherwise `p` is odd (`p ∣ |D|` odd) and `p ≠ q`
(no nontrivial normal `q`-subgroup), the conjugate-stabilizer bridge gives the constant
point-stabilizer order, and the Lemma applies. -/
theorem opCore_isCyclic_and_fpf_of_transitive
    [Finite D] [Finite E] {q : ℕ} (hq : q.Prime) (hqE : q ∣ Nat.card E) [Nontrivial E]
    (hE : IsElementaryAbelian q E) (hD_odd : Odd (Nat.card D))
    (φ : D →* MulAut E) (hfaithful : Function.Injective φ)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, (φ d) a = b)
    {p : ℕ} (hp : p.Prime) :
    IsCyclic ↥(OddOrder.Isaacs.Ch01.opCore p D) ∧
      ∀ x : ↥(OddOrder.Isaacs.Ch01.opCore p D), x ≠ 1 →
        actionFixedBy (φ.comp (OddOrder.Isaacs.Ch01.opCore p D).subtype) x = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  rcases eq_or_ne (OddOrder.Isaacs.Ch01.opCore p D) ⊥ with hbot | hbot
  · exact ⟨by rw [hbot]; exact isCyclic_of_subsingleton,
      fun x hx => absurd (Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ x.2))) hx⟩
  · have hirr : ∀ U : Subgroup E, IsAInvariant φ U → U = ⊥ ∨ U = ⊤ :=
      fun _ hU => isAInvariant_eq_bot_or_top_of_transitive φ htrans hU
    have hqp : q ≠ p := by
      rintro rfl
      exact hbot (normal_isPGroup_eq_bot_of_faithful_irreducible hqE φ hfaithful hirr
        (OddOrder.Isaacs.Ch01.opCore.normal q D) (OddOrder.Isaacs.Ch01.opCore_isPGroup q D))
    have hpdvd : p ∣ Nat.card D := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).mp (OddOrder.Isaacs.Ch01.opCore_isPGroup p D)
      have hk0 : k ≠ 0 := by
        rintro rfl; rw [pow_zero] at hk
        exact hbot (Subgroup.eq_bot_of_card_eq _ hk)
      exact (hk ▸ dvd_pow_self p hk0).trans (Subgroup.card_subgroup_dvd_card _)
    have hpodd : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | hpodd
      · exfalso; rw [Nat.odd_iff] at hD_odd; omega
      · exact hpodd
    have hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
        Nat.card ↥(pointStabilizer (φ.comp (OddOrder.Isaacs.Ch01.opCore p D).subtype) a) =
          Nat.card ↥(pointStabilizer (φ.comp (OddOrder.Isaacs.Ch01.opCore p D).subtype) b) :=
      fun a b ha hb => card_pointStabilizer_comp_eq_of_normal_of_transitive φ
        (OddOrder.Isaacs.Ch01.opCore.normal p D) htrans ha hb
    exact pGroup_cyclic_fixedPointFree hq hqp (OddOrder.Isaacs.Ch01.opCore_isPGroup p D) hpodd hE
      (φ.comp (OddOrder.Isaacs.Ch01.opCore p D).subtype)
      (hfaithful.comp (Subgroup.subtype_injective _)) hconst

open OddOrder.Isaacs.Ch01 OddOrder.BG.Ch3.S10 in
/-- The `p`-core of `F(D)` maps onto the `p`-core of `D`: `O_p(F(D)) = O_p(D)` (both are the
largest normal `p`-subgroup, and `F(D)` is characteristic in `D`).  Bridges per-prime facts
about `O_p(D)` to Sylow/`p`-element facts inside the (nilpotent) Fitting subgroup. -/
theorem opCore_fitting_map_subtype_eq [Finite D] (p : ℕ) [Fact p.Prime] :
    (opCore p ↥(fitting D)).map (fitting D).subtype = opCore p D := by
  apply le_antisymm
  · haveI : ((opCore p ↥(fitting D)).map (fitting D).subtype).Normal :=
      normal_map_subtype_of_characteristic (opCore.characteristic p ↥(fitting D))
    exact normal_pgroup_le_opCore ((opCore_isPGroup p ↥(fitting D)).map (fitting D).subtype)
  · have hofit : opCore p D ≤ fitting D := opCore_le_fitting ⟨p, Fact.out⟩ D
    haveI : ((opCore p D).subgroupOf (fitting D)).Normal := Subgroup.normal_subgroupOf
    have hle : (opCore p D).subgroupOf (fitting D) ≤ opCore p ↥(fitting D) :=
      normal_pgroup_le_opCore ((opCore_isPGroup p D).comap_subtype)
    calc opCore p D = ((opCore p D).subgroupOf (fitting D)).map (fitting D).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hofit).symm
      _ ≤ (opCore p ↥(fitting D)).map (fitting D).subtype := Subgroup.map_mono hle

open OddOrder.Isaacs.Ch01 OddOrder.BG.Ch3.S10 in
/-- **Peterfalvi Appendix B, Proposition 1 — `F(D)` cyclic from cyclic `p`-cores**: if every
`p`-core `O_p(D)` is cyclic, then the Fitting subgroup `F(D)` is cyclic.  Pure group theory:
`F(D)` is nilpotent (`fitting.isNilpotent`), each Sylow of `F(D)` is its unique normal one and
equals an `O_p(D)` (`= ⨅` of Sylows), so `F(D)` is a nilpotent `Z`-group, hence cyclic. -/
theorem isCyclic_fitting_of_forall_opCore_isCyclic [Finite D]
    (h : ∀ p : ℕ, p.Prime → IsCyclic ↥(opCore p D)) :
    IsCyclic ↥(fitting D) := by
  haveI : _root_.IsZGroup ↥(fitting D) := by
    rw [_root_.isZGroup_iff]
    intro p hp P
    haveI : Fact p.Prime := ⟨hp⟩
    have hPnorm : (↑P : Subgroup ↥(fitting D)).Normal := Sylow.normal_of_isNilpotent P
    have hPchar : (↑P : Subgroup ↥(fitting D)).Characteristic :=
      Sylow.characteristic_of_normal P hPnorm
    haveI hPmap_norm : ((↑P : Subgroup ↥(fitting D)).map (fitting D).subtype).Normal :=
      normal_map_subtype_of_characteristic hPchar
    have hPmap_pg : IsPGroup p ((↑P : Subgroup ↥(fitting D)).map (fitting D).subtype) :=
      P.isPGroup'.map (fitting D).subtype
    have hmap_le : (↑P : Subgroup ↥(fitting D)).map (fitting D).subtype ≤ opCore p D :=
      normal_pgroup_le_opCore hPmap_pg
    have hop_le : opCore p D ≤ (↑P : Subgroup ↥(fitting D)).map (fitting D).subtype := by
      have hofit : opCore p D ≤ fitting D := opCore_le_fitting ⟨p, hp⟩ D
      have hQpg : IsPGroup p ((opCore p D).subgroupOf (fitting D)) :=
        (opCore_isPGroup p D).comap_subtype
      obtain ⟨S, hQS⟩ := IsPGroup.exists_le_sylow hQpg
      haveI := Sylow.unique_of_normal P hPnorm
      have hSP : S = P := Subsingleton.elim S P
      calc opCore p D = ((opCore p D).subgroupOf (fitting D)).map (fitting D).subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hofit).symm
        _ ≤ (↑S : Subgroup ↥(fitting D)).map (fitting D).subtype := Subgroup.map_mono hQS
        _ = (↑P : Subgroup ↥(fitting D)).map (fitting D).subtype := by rw [hSP]
    have heq : (↑P : Subgroup ↥(fitting D)).map (fitting D).subtype = opCore p D :=
      le_antisymm hmap_le hop_le
    haveI : IsCyclic ↥((↑P : Subgroup ↥(fitting D)).map (fitting D).subtype) := heq ▸ h p hp
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective (↑P) (fitting D).subtype
        (fitting D).subtype_injective).symm.surjective
  infer_instance

open OddOrder.Isaacs.Ch01 in
/-- **Peterfalvi Appendix B, Proposition 1 — `F(D)` fixed-point-free**: under the hypotheses
of Proposition 1, every nontrivial element of the Fitting subgroup acts without fixed points on
`E`.  For `f ∈ F(D)^#`, pick a prime `p ∣ |f|` and the order-`p` power `g = f ^ (|f| / p)`; then
`g ∈ O_p(F(D))`, hence `g ∈ O_p(D)` (`opCore_fitting_map_subtype_eq`), the per-prime step gives
`C_E(g) = ⊥`, and `C_E(f) ≤ C_E(g)` (a point fixed by `f` is fixed by every power of `f`). -/
theorem fitting_fpf_of_transitive [Finite D] [Finite E] {q : ℕ}
    (hq : q.Prime) (hqE : q ∣ Nat.card E) [Nontrivial E] (hE : IsElementaryAbelian q E)
    (hD_odd : Odd (Nat.card D)) (φ : D →* MulAut E) (hfaithful : Function.Injective φ)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ d : D, (φ d) a = b) :
    ∀ x : D, x ∈ fitting D → x ≠ 1 → actionFixedBy φ x = ⊥ := by
  have hmono : ∀ (a : D) (n : ℕ), actionFixedBy φ a ≤ actionFixedBy φ (a ^ n) := by
    intro a n e he
    rw [mem_actionFixedBy] at he ⊢
    rw [map_pow]
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ']; show (φ a) ((φ a ^ k) e) = e; rw [ih, he]
  intro f hfF hf1
  haveI : Fact q.Prime := ⟨hq⟩
  set f' : ↥(fitting D) := ⟨f, hfF⟩ with hf'def
  have hf'1 : f' ≠ 1 := by rw [hf'def, ne_eq, Subgroup.mk_eq_one]; exact hf1
  have hord_ne : orderOf f' ≠ 1 := fun h => hf'1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hord_ne
  haveI : Fact p.Prime := ⟨hp⟩
  set g' : ↥(fitting D) := f' ^ (orderOf f' / p) with hg'def
  have hord_pos : 0 < orderOf f' := orderOf_pos f'
  have hdvd2 : (orderOf f' / p) ∣ orderOf f' := Nat.div_dvd_of_dvd hpd
  have hk_ne : orderOf f' / p ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hord_pos hpd) hp.pos).ne'
  have hg'ord : orderOf g' = p := by
    rw [hg'def, orderOf_pow_of_dvd hk_ne hdvd2, Nat.div_div_self hpd hord_pos.ne']
  have hg'1 : g' ≠ 1 := by
    intro h; rw [h, orderOf_one] at hg'ord; exact hp.ne_one hg'ord.symm
  have hg'pg : IsPGroup p (Subgroup.zpowers g') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hg'ord, pow_one])
  obtain ⟨S, hgS⟩ := IsPGroup.exists_le_sylow hg'pg
  haveI := Sylow.unique_of_normal S (Sylow.normal_of_isNilpotent S)
  have hg'op : g' ∈ opCore p ↥(fitting D) :=
    mem_opCore.mpr fun P => (Subsingleton.elim P S) ▸ hgS (Subgroup.mem_zpowers g')
  have hgD : (g' : D) ∈ opCore p D := by
    rw [← opCore_fitting_map_subtype_eq p]; exact ⟨g', hg'op, rfl⟩
  have hper := opCore_isCyclic_and_fpf_of_transitive hq hqE hE hD_odd φ hfaithful htrans hp
  have hgD_ne : (g' : D) ≠ 1 := by rw [Ne, OneMemClass.coe_eq_one]; exact hg'1
  have hgne : (⟨(g' : D), hgD⟩ : ↥(opCore p D)) ≠ 1 := by
    rw [Ne, Subgroup.mk_eq_one]; exact hgD_ne
  have hgfpf : actionFixedBy φ (g' : D) = ⊥ := hper.2 ⟨(g' : D), hgD⟩ hgne
  have hgpow : (g' : D) = f ^ (orderOf f' / p) := by rw [hg'def]; rfl
  rw [eq_bot_iff, ← hgfpf, hgpow]
  exact hmono f (orderOf f' / p)

/-- **Peterfalvi Appendix B, Proposition 1**: let `D` be a solvable group of odd order
acting faithfully on the elementary abelian `q`-group `E`, transitively on `E^#`.  Then
the Fitting subgroup `F(D)` is cyclic, acts without fixed points on `E`, and
`D / F(D)` is abelian (equivalently `D' ≤ F(D)`).

Proof (p. 136): for each odd prime `p`, `P = O_p(F(D)) ⊴ D`, so transitivity gives
constant point-stabilizer order (`card_pointStabilizer_comp_eq_of_normal_of_transitive`)
and the Lemma makes `O_p(F)` cyclic and fixed-point-free; `F = ∏_p O_p(F)` is then
cyclic and fixed-point-free; finally `C_D(F) = F` (Feit–Thompson + Fitting, `D`
solvable of odd order) gives `D/F ↪ Aut(F)`, abelian since `F` is cyclic. -/
theorem fitting_cyclic_fixedPointFree
    [Finite D] [Finite E] [IsSolvable D] {q : ℕ} (hq : q.Prime) [Nontrivial E]
    (hD_odd : Odd (Nat.card D)) (hE : IsElementaryAbelian q E)
    (φ : D →* MulAut E) (hfaithful : Function.Injective φ)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ g : D, (φ g) a = b) :
    IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting D) ∧
      (∀ x ∈ OddOrder.Isaacs.Ch01.fitting D, x ≠ 1 → actionFixedBy φ x = ⊥) ∧
      commutator D ≤ OddOrder.Isaacs.Ch01.fitting D := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hqE : q ∣ Nat.card E := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hE.isPGroup
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      have h1 : 1 < Nat.card E := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    exact hn ▸ dvd_pow_self q hn0
  have hcyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting D) :=
    isCyclic_fitting_of_forall_opCore_isCyclic
      (fun p hp =>
        (opCore_isCyclic_and_fpf_of_transitive hq hqE hE hD_odd φ hfaithful htrans hp).1)
  exact ⟨hcyc, fitting_fpf_of_transitive hq hqE hE hD_odd φ hfaithful htrans,
    commutator_le_fitting_of_isCyclic_fitting hcyc⟩

end Proposition1

end OddOrder.Peterfalvi.Appendices.Huppert
