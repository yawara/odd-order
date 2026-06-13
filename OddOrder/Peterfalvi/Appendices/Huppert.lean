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

The remaining `sorry`s are exactly the two structural reductions: the
constant-stabilizer ⟹ fixed-point-free argument of parts (1)--(2) of the Lemma
(Clifford decomposition + the irreducible case, p. 136), and the Fitting-subgroup
structure of Proposition 1.
-/

namespace OddOrder.Peterfalvi.Appendices.Huppert

open OddOrder.GroupTheory
open OddOrder.Isaacs.Ch06
open OddOrder.BG.Ch3.S12

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
    by_contra hc; push_neg at hc
    refine hxa1 (hkill _ σi i j σj hxa_mem ?_ hc.1 hc.2 hσ_ne)
    rw [hxa_eq]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)))
      (Subgroup.mem_sup_right (inv_mem hxb_mem))
  have hσj_cases : σj = i ∨ σj = j := by
    by_contra hc; push_neg at hc
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

/-- **Peterfalvi Appendix B, Lemma**: let `p ≠ 2` be prime and let the `p`-group
`P` act faithfully on the elementary abelian `q`-group `E`.  If `|P_a|` is the same
for every `a ∈ E^#`, then `P` is cyclic and acts without fixed points on `E`.

The fixed-point-free conclusion is parts (1)--(2) of Peterfalvi's proof (the
Clifford decomposition `E = E₁ ⊕ ⋯ ⊕ Eᵣ` argument together with the irreducible
case via Schur's Lemma, p. 136); cyclicity then follows from
`isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian`. -/
theorem pGroup_cyclic_fixedPointFree
    [Finite P] [Finite E] {p q : ℕ} [Fact p.Prime] (hq : q.Prime) [Nontrivial E]
    (hP : IsPGroup p P) (hp_odd : Odd p) (hE : IsElementaryAbelian q E)
    (φ : P →* MulAut E) (hfaithful : Function.Injective φ)
    (hconst : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      Nat.card ↥(pointStabilizer φ a) = Nat.card ↥(pointStabilizer φ b)) :
    IsCyclic P ∧ ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
  have hfpf : ∀ x : P, x ≠ 1 → actionFixedBy φ x = ⊥ := by
    -- parts (1)–(2) of the proof: constant point-stabilizer order forces a
    -- fixed-point-free action (Clifford decomposition + the irreducible case).
    sorry
  exact ⟨isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian hq hP hp_odd hE φ hfpf, hfpf⟩

end Lemma

section Proposition1

variable {D E : Type*} [Group D] [Group E]

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

/-- **Peterfalvi Appendix B, Proposition 1**: let `D` have odd order and act
faithfully on the elementary abelian `q`-group `E`, transitively on `E^#`.  Then
the Fitting subgroup `F(D)` is cyclic, acts without fixed points on `E`, and
`D / F(D)` is abelian (equivalently `D' ≤ F(D)`).

Proof (p. 136): for each odd prime `p`, `P = O_p(F(D)) ⊴ D`, so transitivity gives
constant point-stabilizer order (`card_pointStabilizer_comp_eq_of_normal_of_transitive`)
and the Lemma makes `O_p(F)` cyclic and fixed-point-free; `F = ∏_p O_p(F)` is then
cyclic and fixed-point-free; finally `C_D(F) = F` (Feit–Thompson + Fitting, `D`
solvable of odd order) gives `D/F ↪ Aut(F)`, abelian since `F` is cyclic. -/
theorem fitting_cyclic_fixedPointFree
    [Finite D] [Finite E] {q : ℕ} (hq : q.Prime) [Nontrivial E]
    (hD_odd : Odd (Nat.card D)) (hE : IsElementaryAbelian q E)
    (φ : D →* MulAut E) (hfaithful : Function.Injective φ)
    (htrans : ∀ a b : E, a ≠ 1 → b ≠ 1 → ∃ g : D, (φ g) a = b) :
    IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting D) ∧
      (∀ x ∈ OddOrder.Isaacs.Ch01.fitting D, x ≠ 1 → actionFixedBy φ x = ⊥) ∧
      commutator D ≤ OddOrder.Isaacs.Ch01.fitting D := by
  sorry

end Proposition1

end OddOrder.Peterfalvi.Appendices.Huppert
