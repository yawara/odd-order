/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.AppE_ExponentP
import OddOrder.Isaacs.Ch04_Commutators.ForwardFromCh03

/-!
# BG Appendix E, Theorem E.3, Step 4: `B` fixes `R₀`

H. Bender and G. Glauberman, *Local Analysis for the Odd Order Theorem*
(LMS LNS 188, 1994), Appendix E, p. 162 — Step 4 of the proof of Theorem E.3, which is
part (d):

> Let `S = Ω₁(R)` and let `G` be the semidirect product of `S` by `B`.  By (b),
> `|S/S'| = p²` and `|S'| = |S|/p²`.  Note that `Φ(S) = S'`, because `S` has exponent `p`.
> Assume that `B` fixes `R₀S'`.  Let `v ∈ R₀^#`.  For each `x ∈ S`,
> `x⁻¹vx = v·v⁻¹x⁻¹vx ≡ v (mod S')`, so the conjugacy class of `v` in `S` is contained in
> `vS'`.  By (E.15) it has `|S|/p²` elements, and hence is equal to `vS'`, by (E.17).  The
> same is true of `v², v³, …, v^{p-1}`.  Thus every element of the set `R₀S' − S'` is
> conjugate to an element of `R₀^#`.  Since `B` fixes `R₀S'`, it follows that, for each
> `β ∈ B`, `R₀^β = R₀^x` for some `x ∈ S`.  By a variation of the Frattini argument,
> `SB = S·N_G(R₀)`.  By the Schur–Zassenhaus Theorem, `N_G(R₀)` contains a complement `B*`
> to `N_G(R₀) ∩ S`, and `B* = B^y` for some `y ∈ S`.  Therefore `B^y` normalizes `R₀`.
> Then `A` normalizes `R₀` and `R₀^y`. …  `A` fixes at least one element `z` of
> `y·N_S(R₀)`.  Since `A` acts regularly on `R`, `z = 1`.  Therefore `y ∈ N_S(R₀)` and
> `R₀^β = R₀`.

The counting half of Step 4 (`(E.15)`, `(E.17)`, the class/coset identification and
"every element of `R₀S' − S'` is `S`-conjugate into `R₀^#`") is proved upstream in
`OddOrder/BG/AppE_ExponentP.lean` — it belongs there because it consumes Step 2/3's
`(E.15)`.  This leaf carries the *group-theoretic* half: the passage from that statement
to `R₀^β = R₀^x`, the semidirect product `G = S ⋊ B`, the Frattini variation, and the
Schur–Zassenhaus descent.
-/

namespace OddOrder.BG.AppE

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03
open scoped commutatorElement Pointwise

variable {R B : Type*} [Group R] [Group B] {p q : ℕ}

/-! ## The ambient ↔ subtype bridge

BG's Step 4 statement is phrased in the ambient group `R` (`B` fixes `R₀Φ(S)`), while the
counting of Step 4 runs inside `↥S`.  These two lemmas move a `sup` across `S.subtype`. -/

/-- `H ⊔ H'`, for `H ≤ K`, is the image of `H.subgroupOf K ⊔ commutator ↥K` under
`K.subtype`.  This is the bridge between the ambient statement `R₀Φ(S)` and the subtype
computation of `exists_conj_mem_R₀`. -/
theorem map_subtype_sup_commutator {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) :
    (H.subgroupOf K ⊔ _root_.commutator ↥K).map K.subtype = H ⊔ derivedInG K := by
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hHK]
  rfl

/-- Membership form of `map_subtype_sup_commutator`: an element of `K` lies in the ambient
`H ⊔ K'` exactly when its subtype avatar lies in `H.subgroupOf K ⊔ commutator ↥K`. -/
theorem mem_sup_derivedInG_iff {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
    (x : ↥K) : (x : G) ∈ H ⊔ derivedInG K ↔
      x ∈ H.subgroupOf K ⊔ _root_.commutator ↥K := by
  rw [← map_subtype_sup_commutator hHK]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact (Subtype.ext hyx : y = x) ▸ hy
  · exact fun hx => ⟨x, hx, rfl⟩

/-! ## `Ω₁(R)` as BG's `S` -/

/-- The seed `Ω₁(C_R(R₀))` sits inside `Ω₁(R)`: its elements are killed by `p`. -/
theorem RegularOperatorSetup.seed_le_omega [Finite R] (hyp : RegularOperatorSetup R B p q) :
    hyp.seed ≤ Omega R p 1 :=
  fun _ hg => Omega.mem_of_pow_eq_one (by simpa using hg.2)

/-- `Ω₁(R)` has exponent `p`, in the subtype form the Step 4 lemmas take. -/
theorem RegularOperatorSetup.omega_pow_eq_one' [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) (x : ↥(Omega R p 1)) : x ^ p = 1 :=
  Subtype.ext (by simpa using hyp.omega_pow_eq_one x.2)

/-- **BG `(E.14)` for `S = Ω₁(R)`**: `|C_S(R₀)| = p²`.

`inf_centralizer_eq_seed` identifies `S ⊓ C_R(R₀)` with the seed, whose order is `p²`
(`card_seed`). -/
theorem RegularOperatorSetup.card_inf_omega_centralizer [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q) :
    Nat.card ↥(Omega R p 1 ⊓ Subgroup.centralizer (hyp.R₀ : Set R)) = p ^ 2 := by
  rw [hyp.inf_centralizer_eq_seed hyp.seed_le_omega fun _ hx => hyp.omega_pow_eq_one hx]
  exact hyp.card_seed

/-- `(Ω₁(R))'` is `B`-invariant: `Ω₁(R)` is characteristic in `R` and the derived subgroup
of a subgroup is the ambient commutator `⁅S, S⁆`, which any automorphism preserves. -/
theorem RegularOperatorSetup.smul_derivedInG_omega (hyp : RegularOperatorSetup R B p q)
    (b : B) : (hyp.act b) • derivedInG (Omega R p 1) = derivedInG (Omega R p 1) := by
  haveI : (Omega R p 1).Characteristic := Omega.characteristic
  have hS : (Omega R p 1).map ((hyp.act b : MulAut R) : R →* R) = Omega R p 1 :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance (hyp.act b)
  have hd : derivedInG (Omega R p 1) = ⁅Omega R p 1, Omega R p 1⁆ :=
    Subgroup.map_subtype_commutator _
  rw [hd, pointwise_mulAut_smul_eq_map, Subgroup.map_commutator, hS]

/-- `Ω₁(R)` is `B`-invariant (it is characteristic in `R`). -/
theorem RegularOperatorSetup.smul_omega (hyp : RegularOperatorSetup R B p q) (b : B) :
    (hyp.act b) • Omega R p 1 = Omega R p 1 := by
  haveI : (Omega R p 1).Characteristic := Omega.characteristic
  rw [pointwise_mulAut_smul_eq_map]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance (hyp.act b)

/-! ## `R₀^β = R₀^x` -/

/-- **BG Step 4**: *"Since `B` fixes `R₀S'`, it follows that, for each `β ∈ B`,
`R₀^β = R₀^x` for some `x ∈ S`."*

Take a generator `v` of `R₀`.  Then `v^β` lies in `R₀S'` (which `β` fixes by hypothesis)
but outside `S'` (which `β` also fixes, and which meets `R₀` trivially by
`inf_derived_omega_eq_bot`), so `exists_conj_mem_R₀` conjugates `v^β` back into `R₀^#` by
some `x ∈ S`.  Passing to `zpowers` — both `v^β` and its conjugate generate a group of
order `p` — turns that into `R₀^β = R₀^x`. -/
theorem RegularOperatorSetup.exists_conj_smul_R₀ [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q)
    (hB : ∀ b : B, (hyp.act b) • (hyp.R₀ ⊔ derivedInG (Omega R p 1)) =
      hyp.R₀ ⊔ derivedInG (Omega R p 1)) (b : B) :
    ∃ x ∈ Omega R p 1, (hyp.act b) • hyp.R₀ = (MulAut.conj x) • hyp.R₀ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  obtain ⟨v, hgen, hvne⟩ := hyp.exists_zpowers_eq_R₀
  have hvR₀ : v ∈ hyp.R₀ := hgen ▸ Subgroup.mem_zpowers v
  have hvS : v ∈ Omega R p 1 := hyp.R₀_le_omega hvR₀
  -- `v^β ∈ Ω₁(R)`, since `Ω₁(R)` is characteristic.
  have hbvS : hyp.act b v ∈ Omega R p 1 := by
    rw [← hyp.smul_omega b, pointwise_mulAut_smul_eq_map]
    exact ⟨v, hvS, rfl⟩
  -- `v^β ∈ R₀S'`, since `β` fixes `R₀S'`.
  have hbv_mem : hyp.act b v ∈ hyp.R₀ ⊔ derivedInG (Omega R p 1) := by
    rw [← hB b, pointwise_mulAut_smul_eq_map]
    exact ⟨v, Subgroup.mem_sup_left hvR₀, rfl⟩
  -- `v ∉ S'`, because `R₀ ⊓ S' = 1` and `v ≠ 1`.
  have hv_not : v ∉ derivedInG (Omega R p 1) := fun hmem =>
    hvne (Subgroup.mem_bot.mp (hyp.inf_derived_omega_eq_bot ▸ Subgroup.mem_inf.mpr ⟨hvR₀, hmem⟩))
  -- `v^β ∉ S'`, because `β` fixes `S'` and is injective.
  have hbv_not : hyp.act b v ∉ derivedInG (Omega R p 1) := by
    intro hmem
    rw [← hyp.smul_derivedInG_omega b, pointwise_mulAut_smul_eq_map] at hmem
    obtain ⟨w, hw, hwv⟩ := hmem
    exact hv_not ((hyp.act b).injective hwv ▸ hw)
  -- Move to `↥Ω₁(R)` and apply `exists_conj_mem_R₀`.
  set y : ↥(Omega R p 1) := ⟨hyp.act b v, hbvS⟩ with hy_def
  have hy : y ∈ hyp.R₀.subgroupOf (Omega R p 1) ⊔ _root_.commutator ↥(Omega R p 1) :=
    (mem_sup_derivedInG_iff hyp.R₀_le_omega y).mp hbv_mem
  have hyS' : y ∉ _root_.commutator ↥(Omega R p 1) := fun hmem =>
    hbv_not ⟨y, hmem, rfl⟩
  obtain ⟨u, hu, hune, horbit⟩ := hyp.exists_conj_mem_R₀ hyp.R₀_lt_omega
    hyp.omega_pow_eq_one' hyp.card_inf_omega_centralizer hy hyS'
  obtain ⟨g, hg⟩ := horbit
  set x : R := ((ConjAct.ofConjAct g : ↥(Omega R p 1)) : R) with hx_def
  refine ⟨x, (ConjAct.ofConjAct g : ↥(Omega R p 1)).2, ?_⟩
  -- Unpack the conjugation in the ambient group `R`.
  have hconj : x * (u : R) * x⁻¹ = hyp.act b v := by
    have := congrArg (fun z : ↥(Omega R p 1) => (z : R)) hg
    simpa [ConjAct.smul_def, hx_def, hy_def] using this
  -- `u` generates `R₀`.
  have huR₀ : (u : R) ∈ hyp.R₀ := Subgroup.mem_subgroupOf.mp hu
  have hune' : (u : R) ≠ 1 := fun h => hune (Subtype.ext h)
  have hugen : Subgroup.zpowers (u : R) = hyp.R₀ := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huR₀) ?_
    rw [hyp.R₀_card, Nat.card_zpowers]
    have hord : orderOf (u : R) ∣ p := by
      have h := orderOf_dvd_natCard (⟨(u : R), huR₀⟩ : ↥hyp.R₀)
      rw [hyp.R₀_card] at h
      rwa [← Subgroup.orderOf_coe (⟨(u : R), huR₀⟩ : ↥hyp.R₀)] at h
    rcases (Nat.dvd_prime hyp.p_prime).mp hord with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hune'
    · exact le_of_eq h.symm
  calc (hyp.act b) • hyp.R₀
      = (hyp.R₀).map ((hyp.act b : MulAut R) : R →* R) := pointwise_mulAut_smul_eq_map _ _
    _ = Subgroup.zpowers (hyp.act b v) := by
        rw [← hgen]; exact MonoidHom.map_zpowers _ _
    _ = (Subgroup.zpowers (u : R)).map ((MulAut.conj x : MulAut R) : R →* R) := by
        rw [MonoidHom.map_zpowers]
        exact congrArg Subgroup.zpowers hconj.symm
    _ = (MulAut.conj x) • hyp.R₀ := by
        rw [hugen, pointwise_mulAut_smul_eq_map]

/-! ## Glauberman's lemma: a `B`-invariant `S`-conjugate of `R₀`

BG's *"By a variation of the Frattini argument, `SB = S·N_G(R₀)`.  By the Schur–Zassenhaus
Theorem, `N_G(R₀)` contains a complement `B*` to `N_G(R₀) ∩ S`, and `B* = B^y` for some
`y ∈ S`.  Therefore `B^y` normalizes `R₀`."*

That derivation — build `Γ = S ⋊ B`, Frattini, Schur–Zassenhaus existence, Schur–Zassenhaus
conjugacy — is verbatim the proof of **Isaacs Lemma 3.24(a)**, Glauberman's fixed-point
lemma, which is formalized as `OddOrder.Isaacs.Ch04.glauberman_fixed_point_exists`.  So we
apply it to `Ω = ` the set of `S`-conjugates of `R₀` instead of repeating the semidirect
product construction. -/

/-- Conjugation twists across an automorphism: `f • (W^s) = (f • W)^{f s}`.

In `MulAut R` this is the identity `f · conj s · f⁻¹ = conj (f s)`. -/
theorem smul_conj_smul {G : Type*} [Group G] (f : MulAut G) (s : G) (W : Subgroup G) :
    f • ((MulAut.conj s) • W) = (MulAut.conj (f s)) • (f • W) := by
  rw [← mul_smul, ← mul_smul]
  congr 1
  refine MulEquiv.ext fun w => ?_
  change f (s * w * s⁻¹) = f s * f w * (f s)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- **BG Step 4, the Glauberman half**: some `S`-conjugate of `R₀` is `B`-invariant.

`S = Ω₁(R)` acts by conjugation on the set `Ω` of its conjugates of `R₀`, transitively by
construction; `B` acts on the same set because `exists_conj_smul_R₀` says `R₀^β` is again an
`S`-conjugate of `R₀`, and the two actions are compatible.  `p ∤ |B|` and `S` is a `p`-group
(hence solvable), so Glauberman's lemma supplies a `B`-fixed point of `Ω`. -/
theorem RegularOperatorSetup.exists_smul_R₀_invariant [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q)
    (hB : ∀ b : B, (hyp.act b) • (hyp.R₀ ⊔ derivedInG (Omega R p 1)) =
      hyp.R₀ ⊔ derivedInG (Omega R p 1)) :
    ∃ y ∈ Omega R p 1, ∀ b : B,
      (hyp.act b) • ((MulAut.conj y) • hyp.R₀) = (MulAut.conj y) • hyp.R₀ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  have hSinv : IsAInvariant hyp.act (Omega R p 1) := by
    haveI : (Omega R p 1).Characteristic := Omega.characteristic
    exact IsAInvariant.of_characteristic hyp.act
  -- `Ω` = the `S`-conjugates of `R₀`.
  let Ω := { W : Subgroup R // ∃ s : ↥(Omega R p 1), W = (MulAut.conj (s : R)) • hyp.R₀ }
  haveI : Nonempty Ω := ⟨⟨hyp.R₀, 1, by rw [Subgroup.coe_one, map_one, one_smul]⟩⟩
  -- `S` acts by conjugation.
  letI mulS : MulAction ↥(Omega R p 1) Ω :=
    { smul := fun s ω => ⟨(MulAut.conj (s : R)) • ω.val, by
        obtain ⟨t, ht⟩ := ω.property
        exact ⟨s * t, by rw [ht, Subgroup.coe_mul, map_mul, mul_smul]⟩⟩
      one_smul := fun ω => Subtype.ext (by
        change (MulAut.conj (((1 : ↥(Omega R p 1)) : R))) • ω.val = ω.val
        rw [Subgroup.coe_one, map_one, one_smul])
      mul_smul := fun s t ω => Subtype.ext (by
        change (MulAut.conj (((s * t : ↥(Omega R p 1)) : R))) • ω.val =
          (MulAut.conj (s : R)) • ((MulAut.conj (t : R)) • ω.val)
        rw [Subgroup.coe_mul, map_mul, mul_smul]) }
  -- `B` acts through `act`; this is where `exists_conj_smul_R₀` is consumed.
  letI mulB : MulAction B Ω :=
    { smul := fun b ω => ⟨(hyp.act b) • ω.val, by
        obtain ⟨t, ht⟩ := ω.property
        obtain ⟨x, hxS, hx⟩ := hyp.exists_conj_smul_R₀ hB b
        refine ⟨(⟨hyp.act b (t : R), hSinv.smul_mem b t.2⟩ : ↥(Omega R p 1)) * ⟨x, hxS⟩, ?_⟩
        rw [ht, smul_conj_smul, hx, Subgroup.coe_mul, map_mul, mul_smul]⟩
      one_smul := fun ω => Subtype.ext (by
        change (hyp.act 1) • ω.val = ω.val
        rw [map_one, one_smul])
      mul_smul := fun b b' ω => Subtype.ext (by
        change (hyp.act (b * b')) • ω.val = (hyp.act b) • ((hyp.act b') • ω.val)
        rw [map_mul, mul_smul]) }
  -- Compatibility of the two actions.
  have hcompat : OddOrder.Isaacs.Ch04.IsCompatibleMulAction hSinv.restrict Ω := by
    intro b s ω
    refine Subtype.ext ?_
    change (hyp.act b) • ((MulAut.conj (s : R)) • ω.val) =
      (MulAut.conj (((hSinv.restrict b) s : ↥(Omega R p 1)) : R)) • ((hyp.act b) • ω.val)
    rw [smul_conj_smul]
    rfl
  -- `S` is transitive on `Ω` by construction.
  have htrans : MulAction.IsPretransitive ↥(Omega R p 1) Ω := by
    constructor
    intro ω₁ ω₂
    obtain ⟨s₁, h₁⟩ := ω₁.property
    obtain ⟨s₂, h₂⟩ := ω₂.property
    refine ⟨s₂ * s₁⁻¹, Subtype.ext ?_⟩
    change (MulAut.conj (((s₂ * s₁⁻¹ : ↥(Omega R p 1)) : R))) • ω₁.val = ω₂.val
    have hmul : ((s₂ * s₁⁻¹ : ↥(Omega R p 1)) : R) * ((s₁ : ↥(Omega R p 1)) : R) =
        ((s₂ : ↥(Omega R p 1)) : R) := by
      push_cast; group
    rw [h₁, h₂, ← mul_smul, ← map_mul, hmul]
  -- `|B|` is prime to `|S|`, and `S` is solvable.
  have hcop : Nat.Coprime (Nat.card B) (Nat.card ↥(Omega R p 1)) := by
    obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup (Omega R p 1)).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k
      (((Nat.Prime.coprime_iff_not_dvd hyp.p_prime).mpr hyp.p_not_dvd_card_B).symm)
  haveI hSsolv : IsSolvable ↥(Omega R p 1) := by
    haveI : Group.IsNilpotent ↥(Omega R p 1) :=
      IsPGroup.isNilpotent (hyp.R_pGroup.to_subgroup (Omega R p 1))
    infer_instance
  obtain ⟨ω, hω⟩ := OddOrder.Isaacs.Ch04.glauberman_fixed_point_exists
    (G := ↥(Omega R p 1)) (A := B) (φ := hSinv.restrict) hcop (Or.inr hSsolv) (Ω := Ω)
    hcompat htrans
  obtain ⟨y, hy⟩ := ω.property
  refine ⟨(y : R), y.2, fun b => ?_⟩
  have h' : (hyp.act b) • (ω : Subgroup R) = (ω : Subgroup R) := congrArg Subtype.val (hω b)
  rw [← hy]
  exact h'

/-! ## The `A`-fixed point on the coset `y·N_S(R₀)`

BG's closing move: *"Then `A` normalizes `R₀` and `R₀^y`.  Therefore `y^α N_S(R₀) =
y N_S(R₀)`, and `α` (and `A`) fix the coset `y N_S(R₀)`.  Now `|A| = q`, while
`|y N_S(R₀)| = |N_S(R₀)|`, which is a power of `p` and hence not divisible by `q`.
Therefore `A` fixes at least one element `z` of `y N_S(R₀)`.  Since `A` acts regularly on
`R`, `z = 1`.  Therefore `y ∈ N_S(R₀)` and `R₀^β = R₀`."*

The coprime coset fixed-point statement is **Isaacs Theorem 3.27**
(`OddOrder.Isaacs.Ch04.aInvariant_coset_mem_centralizer_of_coprime_subgroup`). -/

/-- **BG Theorem E.3(d)**: if `B` fixes `R₀Φ(Ω₁(R))` then `B` fixes `R₀`.

`Φ(Ω₁(R)) = (Ω₁(R))'` because `Ω₁(R)` has exponent `p` (E.3(b)), so the hypothesis is the
one `exists_smul_R₀_invariant` consumes: it produces `y ∈ S` with `R₀^y` `B`-invariant.
Since `A ≤ B` also normalizes `R₀` itself, `A` fixes the coset `y·N_S(R₀)` setwise; that
coset has `p`-power size while `|A| = q`, so Isaacs Thm 3.27 puts an `A`-fixed point in it,
which regularity forces to be `1`.  Hence `y ∈ N_S(R₀)`, i.e. `R₀^y = R₀`. -/
theorem RegularOperatorSetup.B_fixes_R₀_of_fixes_frattini [Finite R] [Finite B]
    (hyp : RegularOperatorSetup R B p q)
    (hB : ∀ b : B, (hyp.act b) • (hyp.R₀ ⊔ frattiniInG (Omega R p 1)) =
      hyp.R₀ ⊔ frattiniInG (Omega R p 1)) :
    ∀ b : B, (hyp.act b) • hyp.R₀ = hyp.R₀ := by
  haveI : Fact p.Prime := ⟨hyp.p_prime⟩
  rw [hyp.frattiniInG_omega_eq_derivedInG] at hB
  obtain ⟨y, hyS, hyinv⟩ := hyp.exists_smul_R₀_invariant hB
  set φA : ↥hyp.A →* MulAut R := hyp.act.comp hyp.A.subtype with hφA
  set N : Subgroup R := Omega R p 1 ⊓ Subgroup.normalizer hyp.R₀ with hNdef
  have hSinvA : IsAInvariant φA (Omega R p 1) := by
    haveI : (Omega R p 1).Characteristic := Omega.characteristic
    exact IsAInvariant.of_characteristic φA
  have hNinv : IsAInvariant φA N := hSinvA.inf hyp.isAInvariant_R₀.normalizer
  -- The coset `y·N_S(R₀)` is `A`-invariant.
  have hcoset : ∀ a : ↥hyp.A, ∃ n ∈ N, φA a y = y * n := by
    intro a
    -- `A` normalizes both `R₀` and `R₀^y`, so `conj (y^α) • R₀ = conj y • R₀`.
    have hfix : (MulAut.conj (φA a y)) • hyp.R₀ = (MulAut.conj y) • hyp.R₀ := by
      have h1 := hyinv (a : B)
      rw [smul_conj_smul, hyp.A_fixes_R₀ a.val a.property] at h1
      exact h1
    refine ⟨y⁻¹ * φA a y, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by group⟩
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) (hSinvA.smul_mem a hyS)
    · rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← pointwise_mulAut_smul_eq_map, map_mul,
        mul_smul, hfix, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  -- `|A| = q` is prime to `|N_S(R₀)|`, a power of `p`.
  have hCop : Nat.Coprime (Nat.card ↥hyp.A) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := (hyp.R_pGroup.to_subgroup N).exists_card_eq
    rw [hyp.A_card, hk]
    exact Nat.Coprime.pow_right k
      ((Nat.coprime_primes hyp.q_prime hyp.p_prime).mpr (Ne.symm hyp.p_ne_q))
  haveI hNsolv : IsSolvable ↥N := by
    haveI : Group.IsNilpotent ↥N := IsPGroup.isNilpotent (hyp.R_pGroup.to_subgroup N)
    infer_instance
  obtain ⟨c, ⟨n, hn, hcn⟩, hcfix⟩ :=
    OddOrder.Isaacs.Ch04.aInvariant_coset_mem_centralizer_of_coprime_subgroup
      (φ := φA) (N := N) hCop (Or.inr hNsolv) hNinv hcoset
  -- Regularity of `A` pins the fixed point down to `1`.
  have hAne : hyp.A ≠ ⊥ := by
    intro h
    have hc := hyp.A_card
    rw [h, Subgroup.card_bot] at hc
    exact hyp.q_prime.one_lt.ne hc
  haveI : Nontrivial ↥hyp.A := (Subgroup.nontrivial_iff_ne_bot _).mpr hAne
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥hyp.A)
  have hc1 : c = 1 :=
    hyp.A_regular a.val a.property (fun h => ha (Subtype.ext h)) c (hcfix a)
  -- Hence `y ∈ N_S(R₀)`, i.e. `R₀^y = R₀`.
  have hyN : y ∈ N := by
    have hyn : y = n⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hcn, hc1]
    rw [hyn]
    exact Subgroup.inv_mem _ hn
  have hyR₀ : (MulAut.conj y) • hyp.R₀ = hyp.R₀ := by
    rw [pointwise_mulAut_smul_eq_map]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.mem_inf.mp hyN).2
  intro b
  have h := hyinv b
  rwa [hyR₀] at h

end OddOrder.BG.AppE
