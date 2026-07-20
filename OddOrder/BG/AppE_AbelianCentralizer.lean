/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_SemidirectFrattini
import OddOrder.BG.Ch1_Preliminary.OperatorMaschke

/-!
# BG Appendix E, Proposition E.4: `C_S(Z₂(S))` is abelian of index `p`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, pp. 162–164.

> **Proposition E.4.**  Assume the situation of Theorem E.3 and let `S = Ω₁(R)`.  Suppose
> `|S| ≥ p⁴`, `B` acts regularly on `R`, and `B` does not fix `R₀`.  Then `C_S(Z₂(S))` is
> abelian and has index `p` in `S`.

BG's proof opens by collecting, from Theorem E.3,

> `S` has exponent `p`, `|S/S'| = p²`, `|S| ≤ p^q`, and `B` does not fix `R₀Φ(S)`  (E.18)

— the last clause being exactly the **contrapositive of E.3(d)**, which is why the
proposition is gated on Step 4.  The index clause is then Step 2's `|S : T| = p`; the hard
half is that `T = C_S(Z₂(S))` is abelian, proved by contradiction inside the two-dimensional
`𝔽_p`-space `S/S'`, comparing the eigenvalues `r, r₀` of `α` on `R₀S'/S'` and `T/S'` with
the eigenvalues `t, t₀` of `β` on a `B`-invariant complement `Q/S'` and on `T/S'`.

## Naming

Step 2 spells BG's `T = C_S(Z₂(S))` as `C_S(Ω₁(Z₂(S)))`, because Lemma 5.2 (which supplies
`|S : T| = p`) is stated for the narrow-`p`-group subgroup `W = Ω₁(Z₂(S))`.  The two agree
here since `S` has exponent `p`; `omega1UpperCentralTwo_eq_upperCentralSeries` is that
bridge, and it is what lets the proposition be *stated* with BG's `Z₂(S)`.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open scoped commutatorElement Pointwise

variable {R B : Type*} [Group R] [Group B] {p q : ℕ}

/-! ## `Ω₁(Z₂(S)) = Z₂(S)` for exponent-`p` `S` -/

/-- In a group of exponent `p`, `Ω₁(Z₂(S))` is all of `Z₂(S)`.

Step 2 works with `C_S(Ω₁(Z₂(S)))` because Lemma 5.2 is phrased for the narrow-group
subgroup `W = Ω₁(Z₂(S))`; BG's Proposition E.4 says `C_S(Z₂(S))`.  Under the exponent-`p`
hypothesis carried by `S = Ω₁(R)` (E.3(b), first clause) the two subgroups coincide, so the
two names describe the same `T`. -/
theorem omega1UpperCentralTwo_eq_upperCentralSeries {G : Type*} [Group G] {p : ℕ}
    (hexp : ∀ x : G, x ^ p = 1) :
    omega1UpperCentralTwo G p = Subgroup.upperCentralSeries G 2 := by
  refine le_antisymm (omega1UpperCentralTwo_le G p) fun x hx => ?_
  refine ⟨⟨x, hx⟩, Omega.mem_of_pow_eq_one ?_, rfl⟩
  exact Subtype.ext (by simpa using hexp x)

/-- `C_S(Z₂(S)) = C_S(Ω₁(Z₂(S)))` for `S` of exponent `p` — the centralizer form of
`omega1UpperCentralTwo_eq_upperCentralSeries`, which is how Step 2's `T` enters. -/
theorem centralizer_upperCentralSeries_eq_centralizer_omega1 {G : Type*} [Group G] {p : ℕ}
    (hexp : ∀ x : G, x ^ p = 1) :
    Subgroup.centralizer ((Subgroup.upperCentralSeries G 2 : Subgroup G) : Set G) =
      Subgroup.centralizer (omega1UpperCentralTwo G p : Set G) := by
  rw [omega1UpperCentralTwo_eq_upperCentralSeries hexp]

/-! ## `(E.18)`: `B` does not fix `R₀Φ(S)` -/

/-- **BG `(E.18)`, last clause**: if `B` does not fix `R₀` then `B` does not fix `R₀Φ(Ω₁(R))`.

This is the contrapositive of Theorem E.3(d) (`B_fixes_R₀_of_fixes_frattini`), and it is the
only place Proposition E.4 uses Step 4. -/
theorem RegularOperatorSetup.not_fixes_sup_frattini_of_not_fixes_R₀ [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q)
    (hB : ¬ ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀) :
    ¬ ∀ b : B, (hyp.act b) • (hyp.R₀ ⊔ frattiniInG (Omega R p 1)) =
      hyp.R₀ ⊔ frattiniInG (Omega R p 1) :=
  fun h => hB (hyp.B_fixes_R₀_of_fixes_frattini h)

/-! ## The index clause of Proposition E.4 -/

/-- `3 ≤ r(Ω₁(R))` under BG's `|S| ≥ p⁴`.

Step 2's results are all conditioned on `p`-rank at least `3`; Proposition E.4 supplies that
through its cardinality hypothesis, since an exponent-`p` group of `p`-rank `≤ 2` has order
at most `p³` (`three_le_pRank_of_prime_cube_lt_card`). -/
theorem RegularOperatorSetup.three_le_pRank_omega [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) :
    3 ≤ pRank ↥(Omega R p 1) p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  refine three_le_pRank_of_prime_cube_lt_card (hyp.R_pGroup.to_subgroup _)
    hyp.omega_pow_eq_one' (lt_of_lt_of_le ?_ hcard)
  exact Nat.pow_lt_pow_right hyp.p_prime.one_lt (by omega)

/-- **BG Proposition E.4, index clause**: `|S : C_S(Z₂(S))| = p`.

Step 2's `|S : T| = p` (`card_omega1Center_and_index_centralizer`, out of Lemma 5.2 applied
inside the narrow group `S`), transported along
`centralizer_upperCentralSeries_eq_centralizer_omega1`.

⚠ Only `|S| ≥ p⁴` is used — neither the regularity of `B` nor `B ⊄ N(R₀)` enters.  BG lists
all three hypotheses for the proposition as a whole; the abelianness clause is what consumes
the other two. -/
theorem RegularOperatorSetup.index_centralizer_upperCentralSeries [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) :
    (Subgroup.centralizer
        ((Subgroup.upperCentralSeries ↥(Omega R p 1) 2 : Subgroup ↥(Omega R p 1)) :
          Set ↥(Omega R p 1))).index = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rw [centralizer_upperCentralSeries_eq_centralizer_omega1 (p := p) hyp.omega_pow_eq_one']
  exact (hyp.card_omega1Center_and_index_centralizer hyp.R₀_le_omega
    (hyp.three_le_pRank_omega hcard)).2

/-! ## `(E.20)`: `B` is abelian

BG: *"Now `Aut(S/T)` is abelian because `|S/T| = p`.  So `B'` centralizes `S/T`.  By
Proposition 1.5(d), `B'` centralizes an element of `S − T`.  Since `B` acts regularly on
`R`, we have `B' = 1`."*

BG's Proposition 1.5(d) — *"`C_{G/H}(A)` is the image of `C_G(A)` in `G/H`"* — is
**Isaacs Corollary 3.28**, formalized as
`OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal`. -/

/-- The automorphism group of a cyclic group is abelian: `MulAut G ≃* (ZMod |G|)ˣ`.

BG's *"`Aut(S/T)` is abelian because `|S/T| = p`"*, with the primality repackaged as
cyclicity. -/
theorem mulAut_mul_comm_of_isCyclic {G : Type*} [Group G] [IsCyclic G] (f g : MulAut G) :
    f * g = g * f :=
  (IsCyclic.mulAutMulEquiv G).injective (by rw [map_mul, map_mul, mul_comm])

/-- A homomorphism into `MulAut` of a cyclic group kills the derived subgroup. -/
theorem commutator_le_ker_of_isCyclic {A G : Type*} [Group A] [Group G] [IsCyclic G]
    (ρ : A →* MulAut G) : _root_.commutator A ≤ ρ.ker := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
    mulAut_mul_comm_of_isCyclic (ρ x) (ρ y)]
  group

/-- **BG `(E.20)`**: under Proposition E.4's hypotheses `B` is abelian.

`T = C_S(Ω₁(Z₂(S)))` is characteristic in `S` of index `p`, so `S/T` is cyclic of order `p`
and the induced map `B → Aut(S/T)` kills `B'`; that is, `B'` acts trivially on `S/T`.
Isaacs Cor 3.28 (BG Prop 1.5(d)) then lifts a `B'`-fixed point out of any coset of `T`, in
particular out of a coset ≠ `T`, giving a **nontrivial** element of `S` centralized by `B'`.
Regularity of `B` on `R` forces `B' = 1`. -/
theorem RegularOperatorSetup.commutator_eq_bot [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1))
    (hB_regular : ∀ b : B, b ≠ 1 → ∀ x : R, hyp.act b x = x → x = 1) :
    _root_.commutator B = ⊥ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set S : Subgroup R := Omega R p 1 with hSdef
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hTdef
  have hSinv : IsAInvariant hyp.act S := by
    haveI : S.Characteristic := Omega.characteristic
    exact IsAInvariant.of_characteristic hyp.act
  set φ : B →* MulAut ↥S := hSinv.restrict with hφdef
  have hTinv : IsAInvariant φ T := IsAInvariant.of_characteristic φ
  -- `|S : T| = p`, so `S/T` is cyclic of order `p`.
  have hidx : T.index = p := (hyp.card_omega1Center_and_index_centralizer hyp.R₀_le_omega
    (hyp.three_le_pRank_omega hcard)).2
  have hcardq : Nat.card (↥S ⧸ T) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  haveI : IsCyclic (↥S ⧸ T) := isCyclic_of_prime_card hcardq
  -- `B'` acts trivially on `S/T`.
  have hker := commutator_le_ker_of_isCyclic (A := B) (G := ↥S ⧸ T) hTinv.quotientMulAutHom
  have htriv : ∀ b ∈ _root_.commutator B, ∀ x : ↥S, ∃ n ∈ T, φ b x = x * n := by
    intro b hb x
    have h1 : hTinv.quotientMulAutHom b = 1 := MonoidHom.mem_ker.mp (hker hb)
    have h2 : (QuotientGroup.mk' T) ((φ b) x) = (QuotientGroup.mk' T) x := by
      rw [← IsAInvariant.quotientMulAutHom_apply_mk' hTinv, h1]; rfl
    refine ⟨x⁻¹ * (φ b) x, ?_, by group⟩
    simpa using (QuotientGroup.eq (s := T)).mp h2.symm
  -- A coset ≠ `T` exists, since `|S : T| = p > 1`.
  have hTne : T ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hidx
    exact hyp.p_prime.one_lt.ne hidx
  obtain ⟨x, hx⟩ : ∃ x : ↥S, x ∉ T := by
    by_contra h
    exact hTne (eq_top_iff.mpr fun x _ => not_not.mp fun hxT => h ⟨x, hxT⟩)
  -- Isaacs Cor 3.28 lifts a `B'`-fixed point out of `x·T`.
  set B' : Subgroup B := _root_.commutator B with hB'def
  have hCop : Nat.Coprime (Nat.card ↥B') (Nat.card ↥T) := by
    obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup S).to_subgroup T |>.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_right k (Nat.Coprime.symm ?_)
    refine ((Nat.Prime.coprime_iff_not_dvd hyp.p_prime).mpr fun hdvd => ?_)
    exact hyp.p_not_dvd_card_B (hdvd.trans (Subgroup.card_subgroup_dvd_card B'))
  haveI hTsolv : IsSolvable ↥T := by
    haveI : Group.IsNilpotent ↥T :=
      IsPGroup.isNilpotent ((hyp.R_pGroup.to_subgroup S).to_subgroup T)
    infer_instance
  obtain ⟨c, hcfix, n, hn, hcn⟩ :=
    OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient_of_coprime_normal
      (φ := φ.comp B'.subtype) (N := T) hCop (Or.inr hTsolv)
      (fun a => hTinv a.val) (g := x) (fun a => htriv a.val a.property x)
  -- `c ∉ T`, hence `c ≠ 1`; regularity of `B` then kills `B'`.
  have hcT : c ∉ T := by
    rw [hcn]
    exact fun hmem => hx (by simpa using T.mul_mem hmem (T.inv_mem hn))
  have hcne : (c : R) ≠ 1 := fun h => hcT (by
    have : c = 1 := Subtype.ext h
    rw [this]; exact T.one_mem)
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_bot]
  by_contra hbne
  exact hcne (hB_regular b hbne (c : R) (congrArg Subtype.val (hcfix ⟨b, hb⟩)))

/-! ## `S/S'` as a two-dimensional `𝔽_p`-space

By E.3(b)'s third clause `|S/S'| = p²`, and `S` has exponent `p`, so `S/S'` is elementary
abelian of order `p²` — BG's *"Let us regard `S/S'` as a 2-dimensional vector space over
`𝔽_p`"*.  The two distinguished lines are `R₀S'/S'` and `T/S'`. -/

/-- A subgroup of prime index — more precisely, one with cyclic quotient — contains the
derived subgroup.  This puts BG's `T` above `S'`, so that `T/S'` is a *subspace* of `S/S'`. -/
theorem commutator_le_of_isCyclic_quotient {G : Type*} [Group G] {T : Subgroup G} [T.Normal]
    [IsCyclic (G ⧸ T)] : _root_.commutator G ≤ T := by
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hcomm : ∀ a b : G ⧸ T, a * b = b * a := fun a b => by
    letI := IsCyclic.commGroup (α := G ⧸ T)
    exact mul_comm a b
  have h1 : (QuotientGroup.mk' T) ⁅x, y⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm _ _
  simpa using (QuotientGroup.eq_one_iff _).mp h1

/-- `S' ≤ T = C_S(Ω₁(Z₂(S)))`: the index of `T` is the prime `p`, so `S/T` is cyclic. -/
theorem RegularOperatorSetup.commutator_le_centralizer [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) :
    _root_.commutator ↥(Omega R p 1) ≤
      Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1)) := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hidx : (Subgroup.centralizer
      (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))).index = p :=
    (hyp.card_omega1Center_and_index_centralizer hyp.R₀_le_omega
      (hyp.three_le_pRank_omega hcard)).2
  have hq : Nat.card (↥(Omega R p 1) ⧸ Subgroup.centralizer
      (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))) = p := by
    rw [← Subgroup.index_eq_card]; exact hidx
  haveI : IsCyclic (↥(Omega R p 1) ⧸ Subgroup.centralizer
      (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))) :=
    isCyclic_of_prime_card (p := p) hq
  exact commutator_le_of_isCyclic_quotient

/-- **BG's two-dimensional space**: `S/S'` is elementary abelian of order `p²`.

Abelian because it is an abelianization, of exponent `p` because `S` is (E.3(b), first
clause), and of order `p²` by E.3(b)'s third clause. -/
theorem RegularOperatorSetup.isElementaryAbelian_quotient_commutator [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    IsElementaryAbelian p (↥(Omega R p 1) ⧸ _root_.commutator ↥(Omega R p 1)) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥(Omega R p 1)) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥(Omega R p 1)) y
    rw [← map_mul, ← map_mul]
    refine QuotientGroup.eq.mpr ?_
    have hrw : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by group
    rw [hrw, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (_root_.commutator ↥(Omega R p 1)) x
    rw [← map_pow, hyp.omega_pow_eq_one' a, map_one]

/-- **BG's `B` fixes some complement `Q/S'` of `T/S'` in `S/S'`**.

Operator Maschke (`OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian`) applied
to the elementary abelian `S/S'` with the coprime `B`-action: `p ∤ |B|` while `|S/S'| = p²`,
so the `B`-invariant subspace `T/S'` splits off. -/
theorem RegularOperatorSetup.exists_aInvariant_complement_of_centralizer [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1))
    (hSinv : IsAInvariant hyp.act (Omega R p 1))
    (hS'inv : IsAInvariant hSinv.restrict (_root_.commutator ↥(Omega R p 1))) :
    ∃ W : Subgroup (↥(Omega R p 1) ⧸ _root_.commutator ↥(Omega R p 1)),
      IsAInvariant hS'inv.quotientMulAutHom W ∧
      (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))).map
          (QuotientGroup.mk' (_root_.commutator ↥(Omega R p 1))) ⊓ W = ⊥ ∧
      (Subgroup.centralizer (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))).map
          (QuotientGroup.mk' (_root_.commutator ↥(Omega R p 1))) ⊔ W = ⊤ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hcard2 : Nat.card (↥(Omega R p 1) ⧸ _root_.commutator ↥(Omega R p 1)) = p ^ 2 :=
    hyp.card_omega_abelianization
  refine OddOrder.BG.Ch1_Preliminary.exists_aInvariant_complement_of_isElementaryAbelian
    (p := p) (hcard2 ▸ dvd_pow_self p two_ne_zero) ?_
    hyp.isElementaryAbelian_quotient_commutator ?_
  · rw [hcard2]
    exact Nat.Coprime.pow_right 2
      (((Nat.Prime.coprime_iff_not_dvd hyp.p_prime).mpr hyp.p_not_dvd_card_B).symm)
  · exact OddOrder.BG.Ch1_Preliminary.isAInvariant_map_mk' hS'inv
      (IsAInvariant.of_characteristic hSinv.restrict)

/-! ## Eigenvalues on the lines of `S/S'`

BG speaks of *"the eigenvalues `r` and `r₀` of `α` on `R₀S'/S'` and `T/S'`"*.  A line of
`S/S'` is a cyclic group of order `p`, and any automorphism preserving it is a power map on
it; `exists_zpow_of_map_eq_of_isCyclic` is that extraction, and the two lemmas after it
identify BG's two lines. -/

/-- **Eigenvalue extraction**: an automorphism preserving a cyclic subgroup acts on it as a
power map.

`f` sends a generator `g` of `V` to some `g ^ r`, and then `f (g ^ k) = (g ^ r) ^ k =
(g ^ k) ^ r` for every element of `V`.  This is what makes BG's talk of "eigenvalues" on the
lines of `S/S'` literal. -/
theorem exists_zpow_of_map_eq_of_isCyclic {G : Type*} [Group G] {V : Subgroup G}
    [IsCyclic ↥V] (f : MulAut G) (hf : V.map ((f : MulAut G) : G →* G) = V) :
    ∃ r : ℤ, ∀ x ∈ V, f x = x ^ r := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
  have hgV : (g : G) ∈ V := g.2
  have hfg : f (g : G) ∈ V := by
    have hmem : f (g : G) ∈ V.map ((f : MulAut G) : G →* G) := ⟨(g : G), hgV, rfl⟩
    rwa [hf] at hmem
  obtain ⟨r, hr⟩ := hg ⟨f (g : G), hfg⟩
  refine ⟨r, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := hg ⟨x, hx⟩
  have hkx : (g : G) ^ k = x := congrArg Subtype.val hk
  have hrg : (g : G) ^ r = f (g : G) := congrArg Subtype.val hr
  rw [← hkx, map_zpow, ← hrg, ← zpow_mul, ← zpow_mul, Int.mul_comm]

/-- BG's first line: `|R₀S'/S'| = p`.

`R₀` has order `p` and meets `S'` trivially (`inf_derived_omega_eq_bot`), so it injects into
`S/S'`. -/
theorem RegularOperatorSetup.card_map_R₀_subgroupOf [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card ↥((hyp.R₀.subgroupOf (Omega R p 1)).map
      (QuotientGroup.mk' (_root_.commutator ↥(Omega R p 1)))) = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set S : Subgroup R := Omega R p 1 with hSdef
  set R₀' : Subgroup ↥S := hyp.R₀.subgroupOf S with hR₀'
  set N : Subgroup ↥S := _root_.commutator ↥S with hNdef
  set ψ : ↥R₀' →* (↥S ⧸ N) := (QuotientGroup.mk' N).comp R₀'.subtype with hψ
  -- The map `R₀' → S/S'` is injective, because `R₀ ⊓ S' = 1`.
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxS' : (x : ↥S) ∈ N := by
      simpa using (QuotientGroup.eq_one_iff (N := N) _).mp hx
    have hxR₀ : ((x : ↥S) : R) ∈ hyp.R₀ := Subgroup.mem_subgroupOf.mp x.2
    have hxd : ((x : ↥S) : R) ∈ derivedInG S := ⟨(x : ↥S), hxS', rfl⟩
    have hbot := hyp.inf_derived_omega_eq_bot ▸ Subgroup.mem_inf.mpr ⟨hxR₀, hxd⟩
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp hbot))
  have hrange : ψ.range = R₀'.map (QuotientGroup.mk' N) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card ↥ψ.range = Nat.card ↥R₀' :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  rw [← hrange, hcard, hR₀']
  exact hyp.card_R₀_subgroupOf hyp.R₀_le_omega

/-- BG's second line: `|T/S'| = p`.

`|S/S'| = p²` (E.3(b), third clause) and `|S : T| = p`, and `S' ≤ T`, so the image of `T` in
`S/S'` has order `p²/p = p`. -/
theorem RegularOperatorSetup.card_map_centralizer [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (hcard : p ^ 4 ≤ Nat.card ↥(Omega R p 1)) :
    Nat.card ↥((Subgroup.centralizer
        (omega1UpperCentralTwo ↥(Omega R p 1) p : Set ↥(Omega R p 1))).map
      (QuotientGroup.mk' (_root_.commutator ↥(Omega R p 1)))) = p := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  set S : Subgroup R := Omega R p 1 with hSdef
  set T : Subgroup ↥S := Subgroup.centralizer (omega1UpperCentralTwo ↥S p : Set ↥S) with hTdef
  set N : Subgroup ↥S := _root_.commutator ↥S with hNdef
  -- `|T/S'| · |S : T| = |S/S'|`, since `S' ≤ T`.
  have hidx : T.index = p := (hyp.card_omega1Center_and_index_centralizer hyp.R₀_le_omega
    (hyp.three_le_pRank_omega hcard)).2
  have hle : N ≤ T := hyp.commutator_le_centralizer hcard
  have hmapidx : (T.map (QuotientGroup.mk' N)).index = T.index := by
    rw [Subgroup.index_map, QuotientGroup.ker_mk', sup_of_le_left hle,
      QuotientGroup.range_mk', Subgroup.index_top, mul_one]
  have hquot : Nat.card (↥S ⧸ N) = p ^ 2 := hyp.card_omega_abelianization
  have hmul := Subgroup.card_mul_index (T.map (QuotientGroup.mk' N))
  rw [hmapidx, hidx, hquot] at hmul
  refine Nat.eq_of_mul_eq_mul_right hyp.p_prime.pos ?_
  rw [hmul]; ring

/-! ## Eigenspaces, and why commuting operators preserve them

BG: *"Since `β` centralizes `α`, `β` fixes both subspaces if `r ≠ r₀`."*  The eigenspaces are
genuine subgroups of the abelian `S/S'`, and a commuting automorphism preserves each of
them; when the two eigenvalues differ the eigenspaces are the two *lines* `R₀S'/S'` and
`T/S'` themselves, which is how BG turns "β preserves eigenspaces" into "β fixes `R₀S'`". -/

/-- The `r`-eigenspace `{x | f x = x ^ r}` of an automorphism of an abelian group. -/
def eigenSubgroup {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x) (f : MulAut E)
    (r : ℤ) : Subgroup E where
  carrier := {x : E | f x = x ^ r}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    have hz : (a * b) ^ r = a ^ r * b ^ r := by
      letI : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
      exact mul_zpow a b r
    change f (a * b) = (a * b) ^ r
    rw [map_mul, ha, hb, hz]
  inv_mem' := fun {a} ha => by
    change f a⁻¹ = a⁻¹ ^ r
    rw [map_inv, ha, inv_zpow]

@[simp] theorem mem_eigenSubgroup {E : Type*} [Group E] (hcomm : ∀ x y : E, x * y = y * x)
    (f : MulAut E) (r : ℤ) {x : E} : x ∈ eigenSubgroup hcomm f r ↔ f x = x ^ r := Iff.rfl

/-- **BG's *"`β` centralizes `α`, so `β` fixes the eigenspaces"***: an automorphism commuting
with `f` maps each `f`-eigenspace onto itself.

`f (g x) = g (f x) = g (x ^ r) = (g x) ^ r`, and the reverse inclusion is the same argument
for `g⁻¹`, which commutes with `f` too. -/
theorem map_eigenSubgroup_of_commute {E : Type*} [Group E]
    (hcomm : ∀ x y : E, x * y = y * x) {f g : MulAut E} (hfg : f * g = g * f) (r : ℤ) :
    (eigenSubgroup hcomm f r).map ((g : MulAut E) : E →* E) = eigenSubgroup hcomm f r := by
  -- The one-sided statement, applied to `g` and to `g⁻¹`.
  have key : ∀ h : MulAut E, f * h = h * f → ∀ x : E, f x = x ^ r → f (h x) = (h x) ^ r := by
    intro h hfh x hx
    have hcomm' : f (h x) = h (f x) := congrArg (fun k : MulAut E => k x) hfh
    rw [hcomm', hx, map_zpow]
  have hfg' : f * g⁻¹ = g⁻¹ * f := (show Commute f g from hfg).inv_right
  refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
  · obtain ⟨x, hx, rfl⟩ := hy
    exact key g hfg x hx
  · exact ⟨g⁻¹ y, key g⁻¹ hfg' y hy, MulAut.apply_inv_self E g y⟩

end OddOrder.BG.AppE
