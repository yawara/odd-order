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

/-- **Peterfalvi Appendix B, Proposition 1**: let `D` have odd order and act
faithfully on the elementary abelian `q`-group `E`, transitively on `E^#`.  Then
the Fitting subgroup `F(D)` is cyclic, acts without fixed points on `E`, and
`D / F(D)` is abelian (equivalently `D' ≤ F(D)`).

The point-stabilizer orders are constant under a transitive action, so each Sylow
subgroup of `D` is cyclic and fixed-point-free by the Lemma; the structure of
`F(D)` and the abelian quotient then follow (p. 136). -/
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
