/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.NumberTheory.Multiplicity
import Mathlib.SetTheory.Cardinal.Finite
import OddOrder.GroupTheory.SemiDihedral
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03
import OddOrder.Isaacs.Ch04_Commutators.Main

/-!
# Isaacs FGT Ch.6 — Frobenius action basics (pp. 177-183)

`IsFrobeniusAction` (no nonidentity element of `A` fixes a nonidentity element of `N`)
and its basic API: stabilizers, fixed points, restriction to subgroups and quotients,
the congruence `|N| ≡ 1 (mod |A|)` with `Nat.Coprime`, and the even-order-complement
facts (Thm 6.3: unique involution, `n ↦ n⁻¹` inversion).

Split from `OddOrder.Isaacs.Ch06_FrobeniusActions.FrobeniusActionTI` (issue 0149, the
longFile-1500 campaign); `FrobeniusActionTI` imports this leaf, so downstream imports
are unchanged.
-/

namespace OddOrder.Isaacs.Ch06

section /- 6A: Frobenius action basics (pp. 177-183) -/

/-! ### Definition of Frobenius action

Isaacs Defn (p. 177): an action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity
element of `A` fixes any nonidentity element of `N`. Equivalently `C_N(a) = 1` for all `1 ≠ a ∈ A`,
or `C_A(n) = 1` for all `1 ≠ n ∈ N`, or the action of `A` on `N \ {1}` is semiregular. -/

/-- An action of `A` on `N` by automorphisms is **Frobenius** if no nonidentity element of `A`
fixes any nonidentity element of `N`.

Isaacs p. 177: "the action of `A` on `N` is said to be Frobenius if `n^a ≠ n` whenever `n ∈ N`
and `a ∈ A` are nonidentity elements." -/
def IsFrobeniusAction (A N : Type*) [Group A] [Group N] [MulDistribMulAction A N] : Prop :=
  ∀ a : A, a ≠ 1 → ∀ n : N, n ≠ 1 → a • n ≠ n

variable {A N : Type*} [Group A] [Group N] [MulDistribMulAction A N]

namespace IsFrobeniusAction

/-- The orbit of `1 ∈ N` under any `MulDistribMulAction` is `{1}`. (Structural, not Frobenius.) -/
theorem orbit_one : MulAction.orbit A (1 : N) = {1} := by
  ext n
  simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩; exact smul_one a
  · rintro rfl; exact ⟨1, smul_one 1⟩

/-- **Frobenius action ⇒ stabilizer trivial on nonidentity.** -/
theorem stabilizer_eq_bot (h : IsFrobeniusAction A N) {n : N} (hn : n ≠ 1) :
    MulAction.stabilizer A n = ⊥ := by
  ext a
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
  refine ⟨fun hax => ?_, ?_⟩
  · by_contra ha; exact h a ha n hn hax
  · rintro rfl; exact one_smul A n

/-- **Frobenius action: `fixedBy N a = {1}` for `a ≠ 1`.** -/
theorem fixedBy_eq_singleton_one (h : IsFrobeniusAction A N) {a : A} (ha : a ≠ 1) :
    MulAction.fixedBy N a = {1} := by
  ext n
  simp only [MulAction.mem_fixedBy, Set.mem_singleton_iff]
  refine ⟨fun hn => ?_, ?_⟩
  · by_contra hne; exact h a ha n hne hn
  · rintro rfl; exact smul_one a

@[reducible] def invariantSubgroupMulDistribMulAction (M : Subgroup N)
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : MulDistribMulAction A M := by
  letI : SMul A M := ⟨fun a m => ⟨a • (m : N), hM a m m.2⟩⟩
  exact Subtype.coe_injective.mulDistribMulAction M.subtype (fun _ _ => rfl)

/-- A Frobenius action restricts to every invariant subgroup. -/
theorem subgroup (h : IsFrobeniusAction A N) (M : Subgroup N)
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) :
    @IsFrobeniusAction A M _ _ (invariantSubgroupMulDistribMulAction M hM) := by
  letI : MulDistribMulAction A M := invariantSubgroupMulDistribMulAction M hM
  intro a ha m hm hfix
  have hmN : (m : N) ≠ 1 := fun hmN => hm (Subtype.ext hmN)
  exact h a ha (m : N) hmN (Subtype.ext_iff.mp hfix)

/-- A Frobenius action remains Frobenius after restricting the acting group to a subgroup. -/
theorem actorSubgroup (h : IsFrobeniusAction A N) (B : Subgroup A) :
    IsFrobeniusAction B N := by
  intro b hb n hn hfix
  have hbA : (b : A) ≠ 1 := fun hbA => hb (Subtype.ext hbA)
  exact h (b : A) hbA n hn ((Subgroup.smul_def b n).symm.trans hfix)

@[reducible] def invariantQuotientMulAut (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) (a : A) : MulAut (N ⧸ M) := by
  let f : N ⧸ M →* N ⧸ M :=
    QuotientGroup.map M M (MulDistribMulAction.toMulAut A N a).toMonoidHom
      (by
        intro m hm
        exact hM a m hm)
  let g : N ⧸ M →* N ⧸ M :=
    QuotientGroup.map M M (MulDistribMulAction.toMulAut A N a⁻¹).toMonoidHom
      (by
        intro m hm
        exact hM a⁻¹ m hm)
  exact MonoidHom.toMulEquiv f g
    (by
      ext n
      simp [f, g])
    (by
      ext n
      simp [f, g])

@[reducible] def invariantQuotientMulAutHom (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : A →* MulAut (N ⧸ M) where
  toFun := invariantQuotientMulAut M hM
  map_one' := by
    ext q
    refine QuotientGroup.induction_on q ?_
    intro n
    simp [invariantQuotientMulAut]
  map_mul' := by
    intro a b
    ext q
    refine QuotientGroup.induction_on q ?_
    intro n
    simp [invariantQuotientMulAut, mul_smul]

@[reducible] def invariantQuotientMulDistribMulAction (M : Subgroup N) [M.Normal]
    (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) : MulDistribMulAction A (N ⧸ M) :=
  MulDistribMulAction.compHom (N ⧸ M) (invariantQuotientMulAutHom M hM)

/-- **Isaacs Lemma 6.1**: a Frobenius action gives `|N| ≡ 1 (mod |A|)`.

Proof via Burnside's lemma:
`∑_{a ∈ A} |fixedBy N a| = (#orbits) * |A|`. For `a = 1` the fixed-set is all of `N` (size `|N|`),
and for `a ≠ 1` it is `{1}` (size 1). So `|N| + (|A| - 1) = (#orbits) * |A|`, hence
`|A| ∣ |N| - 1`. -/
theorem card_modEq_one [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Fintype.card N ≡ 1 [MOD Fintype.card A] := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient A N) := Quotient.fintype _
  -- Burnside.
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group A N
  -- Compute LHS: split `a = 1` from `a ≠ 1`.
  have h_one : Fintype.card (MulAction.fixedBy N (1 : A)) = Fintype.card N := by
    have h_eq : MulAction.fixedBy N (1 : A) = Set.univ := by
      ext n; simp
    calc Fintype.card (MulAction.fixedBy N (1 : A))
        = Fintype.card ((Set.univ : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = Fintype.card N := Fintype.card_congr (Equiv.Set.univ N)
  have h_other : ∀ a ∈ Finset.univ.erase (1 : A),
      Fintype.card (MulAction.fixedBy N a) = 1 := by
    intro a ha
    have ha_ne : a ≠ 1 := (Finset.mem_erase.mp ha).1
    have h_eq := fixedBy_eq_singleton_one h ha_ne
    calc Fintype.card (MulAction.fixedBy N a)
        = Fintype.card (({1} : Set N) : Type _) :=
          Fintype.card_congr (Equiv.setCongr h_eq)
      _ = 1 := by simp
  have hLHS : ∑ a : A, Fintype.card (MulAction.fixedBy N a)
            = Fintype.card N + (Fintype.card A - 1) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : A)), h_one,
        Finset.sum_congr rfl h_other, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, add_comm]
  rw [hLHS] at hburn
  -- Now: |N| + (|A| - 1) = (#orbits) * |A|, so |A| ∣ |N| - 1.
  haveI : Nonempty (MulAction.orbitRel.Quotient A N) := ⟨⟦1⟧⟩
  set k := Fintype.card (MulAction.orbitRel.Quotient A N)
  set a := Fintype.card A
  set n := Fintype.card N
  have ha_pos : 0 < a := Fintype.card_pos
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_pos : 0 < k := Fintype.card_pos
  -- |N| - 1 = a * (k - 1).
  have hdvd : a ∣ n - 1 := by
    refine ⟨k - 1, ?_⟩
    rw [mul_comm a (k - 1), tsub_mul, one_mul]
    omega
  exact ((Nat.modEq_iff_dvd' hn_pos).mpr hdvd).symm

/-- Corollary of Lemma 6.1: a Frobenius action implies `|N|` and `|A|` are coprime. -/
theorem coprime_card [Fintype A] [Fintype N] (h : IsFrobeniusAction A N) :
    Nat.Coprime (Fintype.card N) (Fintype.card A) := by
  unfold Nat.Coprime
  rw [(card_modEq_one h).gcd_eq, Nat.gcd_one_left]

/-- **Isaacs Corollary 6.2**: a Frobenius action descends to every invariant normal quotient. -/
theorem quotient [Finite A] [Finite N] (h : IsFrobeniusAction A N) (M : Subgroup N)
    [M.Normal] (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _ (invariantQuotientMulDistribMulAction M hM) := by
  classical
  letI : MulDistribMulAction A (N ⧸ M) := invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix
  revert hq_ne hfix
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := hfix
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype N := Fintype.ofFinite N
  have hCopAN : Nat.Coprime (Nat.card A) (Nat.card N) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact (coprime_card h).symm
  have hCopCN : Nat.Coprime (Nat.card C) (Nat.card N) :=
    hCopAN.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  haveI : IsCyclic C := Subgroup.isCyclic_zpowers a
  letI : CommGroup C := IsCyclic.commGroup
  have hSolvC : IsSolvable C ∨ IsSolvable N := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC, P] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (A := C) (G := N) (φ := φC) hCopCN hSolvC hM_inv_C hg_fix_C
  have hx_ne : x ≠ 1 := by
    intro hx_one
    rcases hx_coset with ⟨m, hm, hx_eq⟩
    have hn_eq : n = m⁻¹ := by
      calc
        n = n * m * m⁻¹ := by group
        _ = x * m⁻¹ := by rw [hx_eq]
        _ = m⁻¹ := by rw [hx_one, one_mul]
    have hnM : n ∈ M := by
      rw [hn_eq]
      exact M.inv_mem hm
    exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)
  have hax : a • x = x := by
    have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
    simpa [φC, φ] using this
  exact h a ha x hx_ne hax

/-- **Fixed-point-free action on a quotient from a "fixed points lie in `M`" condition.**
A variant of `IsFrobeniusAction.quotient` that does *not* require the action on `N` to be Frobenius:
if a finite group `A` acts on a finite group `N` with `(|A|, |N|) = 1`, and for every nonidentity
`a ∈ A` the `a`-fixed points of `N` lie in the `A`-invariant normal subgroup `M`, then the induced
action of `A` on `N ⧸ M` is Frobenius (fixed-point-free).

This is Peterfalvi's (6.5)/(6.8)(c2) mechanism: in the certain-type case `A = W₁` does *not* act
fixed-point-freely on the kernel `N = H` (the fixed points are `C_H(x) = W₂ ≠ 1`), but since
`W₂ ⊆ ⁅H,H⁆ = M`, it acts fixed-point-freely on the abelianization `H / ⁅H,H⁆`.  The proof is the
coprime fixed-point lifting (Isaacs Cor 3.28): an `a`-fixed coset of `N / M` lifts to an `a`-fixed
`c ∈ N` (cyclic `⟨a⟩` acting coprimely), and `c` lies in `M` by hypothesis, so the coset is
trivial. -/
theorem quotient_of_fixedPoints_le [Finite A] [Finite N]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card N))
    (M : Subgroup N) [M.Normal] (hM : ∀ a : A, ∀ m ∈ M, a • m ∈ M)
    (hfixle : ∀ a : A, a ≠ 1 → ∀ x : N, a • x = x → x ∈ M) :
    @IsFrobeniusAction A (N ⧸ M) _ _ (invariantQuotientMulDistribMulAction M hM) := by
  classical
  letI : MulDistribMulAction A (N ⧸ M) := invariantQuotientMulDistribMulAction M hM
  intro a ha q hq_ne hfix_q
  revert hq_ne hfix_q
  refine QuotientGroup.induction_on q ?_
  intro n hq_ne hfix_q
  let φ : A →* MulAut N := MulDistribMulAction.toMulAut A N
  let P : Subgroup A :=
    { carrier := {b | ∃ m ∈ M, φ b n = n * m}
      one_mem' := by
        refine ⟨1, M.one_mem, ?_⟩
        simp [φ]
      mul_mem' := by
        intro b c hb hc
        rcases hb with ⟨mb, hmb, hb⟩
        rcases hc with ⟨mc, hmc, hc⟩
        refine ⟨mb * (φ b) mc, M.mul_mem hmb (hM b mc hmc), ?_⟩
        calc
          φ (b * c) n = φ b (φ c n) := by
            change (b * c) • n = b • c • n
            rw [mul_smul]
          _ = φ b (n * mc) := by rw [hc]
          _ = φ b n * φ b mc := by simp
          _ = n * (mb * φ b mc) := by rw [hb]; group
      inv_mem' := by
        intro b hb
        rcases hb with ⟨m, hm, hb⟩
        refine ⟨((φ b⁻¹) m)⁻¹, M.inv_mem (hM b⁻¹ m hm), ?_⟩
        have hb' : n = φ b⁻¹ n * φ b⁻¹ m := by
          calc
            n = φ b⁻¹ (φ b n) := by simp [φ]
            _ = φ b⁻¹ (n * m) := by rw [hb]
            _ = φ b⁻¹ n * φ b⁻¹ m := by simp
        calc
          φ b⁻¹ n = (φ b⁻¹ n * φ b⁻¹ m) * (φ b⁻¹ m)⁻¹ := by group
          _ = n * (φ b⁻¹ m)⁻¹ := by rw [← hb'] }
  have haP : a ∈ P := by
    have hfix' : ((a • n : N) : N ⧸ M) = (n : N ⧸ M) := hfix_q
    have hdiv : (a • n) / n ∈ M := (QuotientGroup.eq_iff_div_mem (N := M)).mp hfix'
    have hMN : M.Normal := inferInstance
    have hm : n⁻¹ * (a • n) ∈ M := by
      rw [← hMN.mem_comm_iff]
      simpa [div_eq_mul_inv] using hdiv
    refine ⟨n⁻¹ * (a • n), hm, ?_⟩
    simp [φ]
  let C : Subgroup A := Subgroup.zpowers a
  let φC : C →* MulAut N := φ.comp C.subtype
  have hC_le_P : C ≤ P := Subgroup.zpowers_le.mpr haP
  have hM_inv_C : OddOrder.Isaacs.Ch03.IsAInvariant φC M := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro c m hm
    exact hM (c : A) m hm
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype N := Fintype.ofFinite N
  have hCopCN : Nat.Coprime (Nat.card C) (Nat.card N) :=
    hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card C)
  haveI : IsCyclic C := Subgroup.isCyclic_zpowers a
  letI : CommGroup C := IsCyclic.commGroup
  have hSolvC : IsSolvable C ∨ IsSolvable N := Or.inl inferInstance
  have hg_fix_C : ∀ c : C, ∃ m ∈ M, φC c n = n * m := by
    intro c
    simpa [φC, P] using hC_le_P c.2
  obtain ⟨x, hx_fixed, hx_coset⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
      (A := C) (G := N) (φ := φC) hCopCN hSolvC hM_inv_C hg_fix_C
  have hax : a • x = x := by
    have := hx_fixed ⟨a, Subgroup.mem_zpowers a⟩
    simpa [φC, φ] using this
  have hxM : x ∈ M := hfixle a ha x hax
  rcases hx_coset with ⟨m, hm, hx_eq⟩
  have hnM : n ∈ M := by
    have hne : n = x * m⁻¹ := by rw [hx_eq]; group
    rw [hne]; exact M.mul_mem hxM (M.inv_mem hm)
  exact hq_ne ((QuotientGroup.eq_one_iff n).mpr hnM)

/-! ### Theorem 6.3: even-order Frobenius complements

If `|A|` is even and `N` is nontrivial under a Frobenius action, then `A` contains a *unique*
involution and `N` is abelian.

The proof leverages mathlib's `MonoidHom.FixedPointFree` machinery (`Mathlib/GroupTheory/
FixedPointFree.lean`): for each `t ∈ A`, the map `n ↦ t • n` is an automorphism of `N`, and the
Frobenius condition (with `t ≠ 1`) is exactly fixed-point-freeness. When `t² = 1` (involution),
the map is involutive, so by `commute_all_of_involutive` `N` is commutative, and the unique
involution follows from the fact that any involution inverts every element. -/

/-- The action of `t ∈ A` on `N` (as `MulDistribMulAction.toMulAut`) is fixed-point-free whenever
`t ≠ 1` and the action of `A` on `N` is Frobenius. -/
theorem fixedPointFree_toMulAut (h : IsFrobeniusAction A N) {t : A} (ht : t ≠ 1) :
    MonoidHom.FixedPointFree (MulDistribMulAction.toMulAut A N t) := by
  intro n hn
  by_contra hne
  exact h t ht n hne (by simpa using hn)

/-- If `t ∈ A` satisfies `t² = 1`, then its action on `N` is involutive (as a function). -/
theorem involutive_toMulAut_of_sq_eq_one {t : A} (ht_sq : t ^ 2 = 1) :
    Function.Involutive ((MulDistribMulAction.toMulAut A N t : MulAut N) : N → N) := by
  intro n
  change t • (t • n) = n
  rw [← mul_smul, ← sq, ht_sq, one_smul]

/-- **Key lemma for Thm 6.3**: an involution `t ∈ A` (`t ≠ 1`, `t² = 1`) inverts every element
of `N` under a Frobenius action. -/
theorem involution_smul_eq_inv [Finite N] (h : IsFrobeniusAction A N)
    {t : A} (ht_ne : t ≠ 1) (ht_sq : t ^ 2 = 1) (n : N) : t • n = n⁻¹ := by
  have hfree := fixedPointFree_toMulAut h ht_ne
  have hinv := involutive_toMulAut_of_sq_eq_one (A := A) (N := N) ht_sq
  have h_eq := hfree.coe_eq_inv_of_involutive hinv
  -- h_eq : ⇑(MulDistribMulAction.toMulAut A N t) = (·⁻¹)
  have := congrFun h_eq n
  simpa using this

/-- **Isaacs Theorem 6.3** (commutativity part): `|A|` even + Frobenius action on nontrivial `N`
⇒ every pair in `N` commutes. -/
theorem commute_of_card_even [Finite A] [Finite N] (h : IsFrobeniusAction A N)
    (h_even : 2 ∣ Nat.card A) (x y : N) : Commute x y := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h_even)
  have ht_ne : t ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at ht_ord; norm_num at ht_ord
  have ht_sq : t ^ 2 = 1 := by rw [← ht_ord, pow_orderOf_eq_one]
  exact (fixedPointFree_toMulAut h ht_ne).commute_all_of_involutive
    (involutive_toMulAut_of_sq_eq_one ht_sq) x y

/-- **Isaacs Theorem 6.3** (uniqueness of involution): `|A|` even + Frobenius action on nontrivial
`N` ⇒ `A` has exactly one element of order 2. -/
theorem unique_involution [Finite A] [Finite N] (h : IsFrobeniusAction A N)
    (h_even : 2 ∣ Nat.card A) (hN : Nontrivial N) :
    ∃! t : A, t ≠ 1 ∧ t ^ 2 = 1 := by
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht_ord⟩ :=
    exists_prime_orderOf_dvd_card 2 (by rwa [Nat.card_eq_fintype_card] at h_even)
  have ht_ne : t ≠ 1 := by
    intro heq; rw [heq, orderOf_one] at ht_ord; norm_num at ht_ord
  have ht_sq : t ^ 2 = 1 := by rw [← ht_ord, pow_orderOf_eq_one]
  refine ⟨t, ⟨ht_ne, ht_sq⟩, ?_⟩
  rintro s ⟨hs_ne, hs_sq⟩
  -- Both `s` and `t` invert every element of `N`. Hence `s * t⁻¹` fixes a nontrivial `n`.
  obtain ⟨n, hn_ne⟩ := exists_ne (1 : N)
  have hs_inv : s • n = n⁻¹ := involution_smul_eq_inv h hs_ne hs_sq n
  have ht_inv : t • n = n⁻¹ := involution_smul_eq_inv h ht_ne ht_sq n
  -- `t⁻¹ = t` since `t² = 1`.
  have ht_inv_eq : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← sq, ht_sq]
  -- `(s * t⁻¹) • n = s • (t • n) = s • n⁻¹ = (s • n)⁻¹ = n`.
  have h_st_n : (s * t⁻¹) • n = n := by
    rw [mul_smul, ht_inv_eq, ht_inv, smul_inv', hs_inv, inv_inv]
  -- By Frobenius, `s * t⁻¹ = 1`, i.e., `s = t`.
  by_contra h_neq
  have h_st_ne : s * t⁻¹ ≠ 1 := by
    intro h_eq
    exact h_neq (mul_inv_eq_one.mp h_eq)
  exact h _ h_st_ne n hn_ne h_st_n

end IsFrobeniusAction

end

end OddOrder.Isaacs.Ch06
