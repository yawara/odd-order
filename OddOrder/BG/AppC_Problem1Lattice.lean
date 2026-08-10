/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Algebra.RelationLattice
import OddOrder.BG.AppC_Problem1

/-!
# BG Appendix C, Problem 1: the relation lattice of a witness

Theorem 2 of `notes/bg/appC_problem1_partial_resolution.md` (issue 0180) needs its relation
lattice to be everything:

`L_e = span_{𝔽₃} { (u, u^e, u^{e²}) : u ∈ U } = 𝔽_{3^q}³`,

where `U` is the norm-one subgroup, the exponent `e` describes how `g = x^y` normalizes `σ(U)`,
and Lemma D says this holds exactly when `e` is *not* a power of the Frobenius.

`OddOrder.RelationLattice.span_triples_subgroup_eq_top` proves the field-theoretic half from an
exponent family whose power maps on `𝔽_{3^q}ˣ` are pairwise distinct.  This file supplies the
arithmetic that produces such a family from the group-theoretic hypothesis:

* the exponent `e` only matters modulo `n = |U| = (3^q - 1)/2`, and `n` is *odd*, so `e` may be
  replaced by an odd representative `ẽ`;
* being odd, `ẽ` is invertible modulo `3^q - 1 = 2n` and still satisfies `ẽ³ ≡ 1`; and it is a
  power of `3` modulo `3^q - 1` only if `e` was one modulo `n`;
* so `OddOrder.BG.AppC.Problem1.injective_powHom_pow_mul_pow` applies to the `3q` exponents
  `ẽ^k · 3^j`, which is precisely the hypothesis of Lemma D.

Oddness is what lets the vanishing of a trace form on `U` propagate to all of `𝔽_{3^q}ˣ`: the
units are `U ∪ (-U)` because `-1` is a non-square.

## Main results

* `span_triples_normOne_eq_top` — **Lemma D for `𝔽_{3^q}`**: the relation lattice of a
  non-Frobenius exponent is everything.
-/

namespace OddOrder.BG.AppC.Problem1

open OddOrder.RelationLattice OddOrder.PowerMonomial

section FieldSide

variable {q : ℕ}

/-- **Lemma D for `𝔽_{3^q}`.**  Let `e` be an exponent acting on the norm-one subgroup `U` with
`e³ = 1` and which is not a power of the Frobenius (`u ↦ u^{3^j}`) on `U`.  Then the triples
`(u, u^e, u^{e²})`, `u ∈ U`, span `𝔽_{3^q}³` over the prime field. -/
theorem span_triples_normOne_eq_top (hq : q.Prime) (hq2 : q ≠ 2) {e : ℕ}
    (hcube : ∀ u : NormSet.normOneUnits 3 q, u ^ (e * e * e) = u)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits 3 q, u ^ e ≠ u ^ (3 ^ j)) :
    Submodule.span (ZMod 3)
      {t : GaloisField 3 q × GaloisField 3 q × GaloisField 3 q |
        ∃ u : NormSet.normOneUnits 3 q,
          t = (((u : (GaloisField 3 q)ˣ) : GaloisField 3 q),
               ((u : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ e,
               ((u : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ (e * e))} = ⊤ := by
  classical
  letI : Fintype (GaloisField 3 q) := Fintype.ofFinite _
  have hq0 : q ≠ 0 := hq.pos.ne'
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hq.odd_of_ne_two hq2 with ⟨k, hk⟩
    omega
  -- `|F| = 3^q ≡ 3 (mod 4)`, so `N = 3^q - 1 = 2n` with `n = |U|` odd
  have hcardF' : Nat.card (GaloisField 3 q) = 3 ^ q := GaloisField.card 3 q hq0
  have hcardF : Fintype.card (GaloisField 3 q) = 3 ^ q := by
    rw [← Nat.card_eq_fintype_card]; exact hcardF'
  have hmod4 : 3 ^ q % 4 = 3 := by
    obtain ⟨k, hk⟩ := hq.odd_of_ne_two hq2
    subst hk
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hpow3 : 27 ≤ 3 ^ q := by
    calc (27 : ℕ) = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq3
  set N : ℕ := 3 ^ q - 1 with hNdef
  set n : ℕ := (3 ^ q - 1) / 2 with hndef
  have hN2n : N = 2 * n := by omega
  have hnodd : n % 2 = 1 := by omega
  haveI : NeZero N := ⟨by omega⟩
  have hNcard : Nat.card (GaloisField 3 q)ˣ = N := by rw [Nat.card_units, hcardF']
  have hncard : Nat.card (NormSet.normOneUnits 3 q) = n := by
    rw [NormSet.normOneUnits_card 3 q hq0]
  -- congruent exponents act identically on the norm-one subgroup
  have hpow : ∀ (u : NormSet.normOneUnits 3 q) (m₁ m₂ : ℕ), m₁ ≡ m₂ [MOD n] →
      ((u : (GaloisField 3 q)ˣ)) ^ m₁ = ((u : (GaloisField 3 q)ˣ)) ^ m₂ := by
    intro u m₁ m₂ h
    have hord : orderOf u ∣ n := by rw [← hncard]; exact orderOf_dvd_natCard u
    have hsub : u ^ m₁ = u ^ m₂ := pow_eq_pow_iff_modEq.mpr (h.of_dvd hord)
    exact congrArg (fun z : NormSet.normOneUnits 3 q => ((z : (GaloisField 3 q)ˣ))) hsub
  -- the cube condition, read as a congruence mod `n`
  obtain ⟨u₀, hu₀⟩ := IsCyclic.exists_generator (α := NormSet.normOneUnits 3 q)
  have hord₀ : orderOf u₀ = n := by
    rw [← hncard]
    exact orderOf_eq_card_of_forall_mem_zpowers hu₀
  have hcube' : e * e * e ≡ 1 [MOD n] := by
    have h1 : u₀ ^ (e * e * e) = u₀ ^ 1 := by simpa using hcube u₀
    have h2 := pow_eq_pow_iff_modEq.mp h1
    rwa [hord₀] at h2
  -- an odd representative of `e`
  set ee : ℕ := if e % 2 = 1 then e else e + n with heedef
  have heeodd : ee % 2 = 1 := by
    rw [heedef]
    split_ifs with h
    · exact h
    · omega
  have heemod : ee ≡ e [MOD n] := by
    rw [heedef]
    split_ifs with h
    · rfl
    · exact Nat.add_modEq_left_iff.mpr dvd_rfl
  -- `ẽ³ ≡ 1 (mod N)`: separately mod 2 and mod n
  have hcubeN : ee * ee * ee ≡ 1 [MOD N] := by
    have h2 : Nat.Coprime 2 n := (Nat.prime_two.coprime_iff_not_dvd).mpr (by omega)
    have hmod2 : ee * ee * ee ≡ 1 [MOD 2] := by
      have h : ee ≡ 1 [MOD 2] := by unfold Nat.ModEq; omega
      simpa using (h.mul h).mul h
    have hmodn : ee * ee * ee ≡ 1 [MOD n] :=
      (((heemod.mul heemod).mul heemod)).trans hcube'
    rw [hN2n]
    exact (Nat.modEq_and_modEq_iff_modEq_mul h2).mp ⟨hmod2, hmodn⟩
  have hcubeZ : ((ee : ZMod N)) ^ 3 = 1 := by
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcubeN
    push_cast at h
    linear_combination h
  -- the two units of `ZMod N`
  have hunitE : IsUnit ((ee : ZMod N)) :=
    IsUnit.of_mul_eq_one ((ee : ZMod N) ^ 2) (by rw [← pow_succ']; exact hcubeZ)
  set ε : (ZMod N)ˣ := hunitE.unit with hεdef
  have hεval : ((ε : (ZMod N)ˣ) : ZMod N) = (ee : ZMod N) := hunitE.unit_spec
  have hε3 : ε ^ 3 = 1 := Units.ext (by push_cast [hεval]; exact hcubeZ)
  have h3q : ((3 : ℕ) ^ q : ZMod N) = 1 := by
    have hmod : (3 : ℕ) ^ q ≡ 1 [MOD N] := by
      have hval : (3 : ℕ) ^ q = N + 1 := by omega
      rw [hval]
      exact Nat.add_modEq_right_iff.mpr dvd_rfl
    have h := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
    push_cast at h
    exact h
  have hunitF : IsUnit ((3 : ZMod N)) := by
    refine IsUnit.of_mul_eq_one ((3 : ZMod N) ^ (q - 1)) ?_
    have : (3 : ZMod N) * (3 : ZMod N) ^ (q - 1) = (3 : ZMod N) ^ q := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    simpa using h3q
  set φ : (ZMod N)ˣ := hunitF.unit with hφdef
  have hφval : ((φ : (ZMod N)ˣ) : ZMod N) = (3 : ZMod N) := hunitF.unit_spec
  have hφq : φ ^ q = 1 := Units.ext (by push_cast [hφval]; simpa using h3q)
  have hφne : φ ≠ 1 := by
    intro h
    have hval : (3 : ZMod N) = 1 := by rw [← hφval, h, Units.val_one]
    have h31 : ((3 : ℕ) : ZMod N) = ((1 : ℕ) : ZMod N) := by push_cast; exact hval
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mp h31
    have hdvd : N ∣ 2 := (Nat.modEq_iff_dvd' (by norm_num)).mp this.symm
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hordφ : orderOf φ = q := by
    rcases hq.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one hφq) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hφne
    · exact h1
  -- `ε` is not a power of the Frobenius
  have heφ : ε ∉ Subgroup.zpowers φ := by
    intro hmem
    obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers (x := φ) (y := ε)).mpr hmem
    have hvals : ((3 : ℕ) ^ j : ZMod N) = (ee : ZMod N) := by
      have := congrArg (fun z : (ZMod N)ˣ => (z : ZMod N)) hj
      simp only [Units.val_pow_eq_pow_val, hφval, hεval] at this
      push_cast
      exact this
    have hmodN : (3 : ℕ) ^ j ≡ ee [MOD N] := by
      refine (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_
      push_cast
      exact hvals
    have hmodn : e ≡ 3 ^ j [MOD n] :=
      (((hmodN.of_dvd ⟨2, by omega⟩).trans heemod)).symm
    obtain ⟨u, hu⟩ := hnotfrob j
    refine hu (Subtype.ext ?_)
    push_cast
    exact hpow u e (3 ^ j) hmodn
  -- the `3q` power maps are pairwise distinct
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := (GaloisField 3 q)ˣ)
  have horda : orderOf a = N := by
    rw [← hNcard]
    exact orderOf_eq_card_of_forall_mem_zpowers ha
  have hinj : Function.Injective fun x : Fin 3 × Fin q =>
      powHom (GaloisField 3 q) (ee ^ (x.1 : ℕ) * 3 ^ (x.2 : ℕ)) :=
    injective_powHom_pow_mul_pow a horda hε3 heφ hordφ hεval.symm (by push_cast; exact hφval.symm)
  -- Lemma D, with the odd exponent family `ẽ^i`
  have hfr : Module.finrank (ZMod 3) (GaloisField 3 q) = q := GaloisField.finrank 3 hq0
  have hK : Nat.card (ZMod 3) = 3 := by simp
  have hcov : ∀ a : (GaloisField 3 q)ˣ,
      a ∈ NormSet.normOneUnits 3 q ∨ -a ∈ NormSet.normOneUnits 3 q := by
    intro b
    have hchar2 : ringChar (GaloisField 3 q) ≠ 2 := by
      haveI : CharP (GaloisField 3 q) 3 := by
        rw [← Algebra.charP_iff (ZMod 3) (GaloisField 3 q) 3]
        exact ZMod.charP 3
      rw [ringChar.eq (GaloisField 3 q) 3]
      norm_num
    have h4 : Fintype.card (GaloisField 3 q) % 4 = 3 := by rw [hcardF]; exact hmod4
    rcases Paley.isSquare_or_isSquare_neg hchar2 h4 (b.ne_zero) with h | h
    · exact Or.inl ((mem_normOneUnits_iff_isSquare rfl hq0 b).mpr h)
    · refine Or.inr ((mem_normOneUnits_iff_isSquare rfl hq0 (-b)).mpr ?_)
      simpa using h
  have hdeq : (fun i : Fin 3 => ee ^ (i : ℕ)) = ![1, ee, ee * ee] := by
    funext i
    fin_cases i <;> simp [pow_two]
  have hinj' : Function.Injective fun x : Fin 3 × Fin q =>
      powHom (GaloisField 3 q) (![1, ee, ee * ee] x.1 * 3 ^ (x.2 : ℕ)) := by
    rw [← hdeq]
    exact hinj
  have hodd' : ∀ i : Fin 3, Odd (![1, ee, ee * ee] i) := by
    intro i
    have hee : Odd ee := Nat.odd_iff.mpr heeodd
    fin_cases i
    · exact odd_one
    · exact hee
    · exact hee.mul hee
  have hspan := span_triples_subgroup_eq_top (K := ZMod 3) (F := GaloisField 3 q)
    ![1, ee, ee * ee] hodd' hcov hfr hK hinj'
  -- the exponents `1, ẽ, ẽ²` agree with `1, e, e²` on the norm-one subgroup
  have hpowF : ∀ (a : (GaloisField 3 q)ˣ), a ∈ NormSet.normOneUnits 3 q → ∀ m₁ m₂ : ℕ,
      m₁ ≡ m₂ [MOD n] →
        ((a : GaloisField 3 q)) ^ m₁ = ((a : GaloisField 3 q)) ^ m₂ := by
    intro a ha m₁ m₂ h
    have hval := congrArg (fun z : (GaloisField 3 q)ˣ => (z : GaloisField 3 q))
      (hpow ⟨a, ha⟩ m₁ m₂ h)
    simpa using hval
  have hsets : {t : GaloisField 3 q × GaloisField 3 q × GaloisField 3 q |
        ∃ u : NormSet.normOneUnits 3 q,
          t = (((u : (GaloisField 3 q)ˣ) : GaloisField 3 q),
               ((u : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ e,
               ((u : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ (e * e))}
      = {t : GaloisField 3 q × GaloisField 3 q × GaloisField 3 q |
        ∃ a ∈ NormSet.normOneUnits 3 q,
          t = (((a : GaloisField 3 q)) ^ (![1, ee, ee * ee] 0),
               ((a : GaloisField 3 q)) ^ (![1, ee, ee * ee] 1),
               ((a : GaloisField 3 q)) ^ (![1, ee, ee * ee] 2))} := by
    ext t
    simp only [Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, pow_one]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(u : (GaloisField 3 q)ˣ), u.2, by
        rw [hpowF _ u.2 ee e heemod, hpowF _ u.2 (ee * ee) (e * e) (heemod.mul heemod)]⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, by
        rw [hpowF _ ha ee e heemod, hpowF _ ha (ee * ee) (e * e) (heemod.mul heemod)]⟩
  rw [hsets]
  exact hspan

end FieldSide


section GroupSide

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

/-- **The identification `(𝔽_{p^q}³, +) → σ(P)³`.**  Componentwise `fieldMulEquiv`; it is
bijective, but only surjectivity is used, to transport a spanning statement from the field to the
group. -/
noncomputable def fieldTripleHom (data : FieldNormalizerData p q G) :
    Multiplicative (GaloisField p q × GaloisField p q × GaloisField p q) →*
      (data.P × data.P × data.P) where
  toFun x :=
    (fieldMulEquiv data (Multiplicative.ofAdd (Multiplicative.toAdd x).1),
     fieldMulEquiv data (Multiplicative.ofAdd (Multiplicative.toAdd x).2.1),
     fieldMulEquiv data (Multiplicative.ofAdd (Multiplicative.toAdd x).2.2))
  map_one' := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  map_mul' x y := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      · simp only [Prod.fst_mul, Prod.snd_mul]
        rw [← map_mul]
        rfl

@[simp]
theorem coe_fieldTripleHom_fst (data : FieldNormalizerData p q G)
    (x : Multiplicative (GaloisField p q × GaloisField p q × GaloisField p q)) :
    (((fieldTripleHom data x).1 : data.P) : G) =
      fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd x).1) := rfl

@[simp]
theorem coe_fieldTripleHom_snd_fst (data : FieldNormalizerData p q G)
    (x : Multiplicative (GaloisField p q × GaloisField p q × GaloisField p q)) :
    (((fieldTripleHom data x).2.1 : data.P) : G) =
      fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd x).2.1) := rfl

@[simp]
theorem coe_fieldTripleHom_snd_snd (data : FieldNormalizerData p q G)
    (x : Multiplicative (GaloisField p q × GaloisField p q × GaloisField p q)) :
    (((fieldTripleHom data x).2.2 : data.P) : G) =
      fieldHom data (Multiplicative.ofAdd (Multiplicative.toAdd x).2.2) := rfl

theorem fieldTripleHom_surjective (data : FieldNormalizerData p q G) :
    Function.Surjective (fieldTripleHom data) := by
  rintro ⟨y₁, y₂, y₃⟩
  refine ⟨Multiplicative.ofAdd
    (Multiplicative.toAdd ((fieldMulEquiv data).symm y₁),
     Multiplicative.toAdd ((fieldMulEquiv data).symm y₂),
     Multiplicative.toAdd ((fieldMulEquiv data).symm y₃)), ?_⟩
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [fieldTripleHom]

/-- **The relation triples of a witness.**  For `v ∈ σ(U)` the three conjugates
`x^v`, `x^{v^e}`, `x^{v^{e²}}` of the prime-line generator, read inside `σ(P)`; the twisted
relation family `layered_relation_of_exp` says they satisfy the layered relation. -/
def relationTriples (data : FieldNormalizerData p q G) (e : ℕ) :
    Set (data.P × data.P × data.P) :=
  {t | ∃ v ∈ data.U, ((t.1 : G) = v⁻¹ * data.s * v) ∧
    ((t.2.1 : G) = (v ^ e)⁻¹ * data.s * v ^ e) ∧
    ((t.2.2 : G) = (v ^ (e * e))⁻¹ * data.s * v ^ (e * e))}

/-- **The relation lattice generates `σ(P)³`.**  Lemma D (`span_triples_normOne_eq_top`)
transported through `fieldTripleHom`: the triples coming from `v ∈ σ(U)` generate the whole of
`σ(P) × σ(P) × σ(P)`. -/
theorem closure_relationTriples_eq_top (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hcube : ∀ u : NormSet.normOneUnits p q, u ^ (e * e * e) = u)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j)) :
    Subgroup.closure (relationTriples data e) = ⊤ := by
  subst hp
  have hq0 : q ≠ 0 := data.q_prime.pos.ne'
  have hq2 : q ≠ 2 := by
    intro h2
    exact ((NormSet.conditionA_iff_not_dvd 3 q (by norm_num) data.q_prime).mp
      data.cyclotomic_coprime) (by rw [h2])
  -- the field-side spanning statement, turned into a group closure
  have hspan := span_triples_normOne_eq_top data.q_prime hq2 hcube hnotfrob
  rw [Submodule.span_eq_top_iff_closure_eq_top] at hspan
  refine top_le_iff.mp ?_
  calc (⊤ : Subgroup (data.P × data.P × data.P))
      = Subgroup.map (fieldTripleHom data) ⊤ :=
        (Subgroup.map_top_of_surjective _ (fieldTripleHom_surjective data)).symm
    _ = Subgroup.closure ((fieldTripleHom data) ''
          (Multiplicative.toAdd ⁻¹' {t : GaloisField 3 q × GaloisField 3 q × GaloisField 3 q |
            ∃ u : NormSet.normOneUnits 3 q,
              t = (((u : (GaloisField 3 q)ˣ) : GaloisField 3 q),
                   ((u : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ e,
                   ((u : (GaloisField 3 q)ˣ) : GaloisField 3 q) ^ (e * e))})) := by
        rw [← hspan, MonoidHom.map_closure]
    _ ≤ Subgroup.closure (relationTriples data e) := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨u, hu⟩ := hx
        -- the witness `v = σ(inr u⁻¹)`
        refine ⟨data.sigma (SemidirectProduct.inr u⁻¹), ?_, ?_, ?_, ?_⟩
        · rw [← data.sigma_U_eq_U]
          exact ⟨SemidirectProduct.inr u⁻¹, ⟨u⁻¹, rfl⟩, rfl⟩
        · have hval := inr_inv_mul_primeLineGenerator_mul_inr 3 q u⁻¹
          rw [coe_fieldTripleHom_fst, hu, FieldNormalizerData.s, ← map_inv data.sigma,
            ← map_mul data.sigma, ← map_mul data.sigma, hval]
          simp [fieldHom]
        · have hval := inr_inv_mul_primeLineGenerator_mul_inr 3 q (u⁻¹ ^ e)
          rw [coe_fieldTripleHom_snd_fst, hu, FieldNormalizerData.s, ← map_pow data.sigma,
            ← map_pow (SemidirectProduct.inr), ← map_inv data.sigma, ← map_mul data.sigma,
            ← map_mul data.sigma, hval]
          simp [fieldHom]
        · have hval := inr_inv_mul_primeLineGenerator_mul_inr 3 q (u⁻¹ ^ (e * e))
          rw [coe_fieldTripleHom_snd_snd, hu, FieldNormalizerData.s, ← map_pow data.sigma,
            ← map_pow (SemidirectProduct.inr), ← map_inv data.sigma, ← map_mul data.sigma,
            ← map_mul data.sigma, hval]
          simp [fieldHom]

/-- **Theorem 2, assembled in the ambient group.**  Let `(G, σ, Q, y)` be a witness of BG
Appendix C, hypothesis (B), for `p = 3`, and suppose `g = x^y` normalizes `σ(U)` by `w ↦ w^e`
where `e` is *not* a power of the Frobenius on `U`.  Then

`N = ⟨σ(P), σ(P)^g, σ(P)^{g²}⟩` is perfect.

`N` is non-trivial (`σ` is injective and `σ(P) ≤ N`), so a witness of this shape contains a
non-trivial perfect subgroup and its ambient group cannot be solvable — in particular, by the odd
order theorem, no finite group of odd order is such a witness.

This is Theorem 2 of `notes/bg/appC_problem1_partial_resolution.md` (issue 0180), with its
spanning hypothesis discharged by Lemma D. -/
theorem commutator_layerClosure_eq_top_of_exp (data : FieldNormalizerData p q G) (hp : p = 3)
    {e : ℕ} (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j)) :
    commutator (layerClosure data.P (conjGen data)) = ⊤ := by
  have hx3 : data.s ^ 3 = 1 := by
    subst hp
    rw [FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : conjGen data ^ 3 = 1 := by rw [conjGen_def, ← map_pow, hx3, map_one]
  have step : ∀ z ∈ data.U, conjGen data * z * (conjGen data)⁻¹ = z ^ e := by
    intro z hz
    rw [hexp z hz]
    group
  -- the exponent has order dividing three on `U`
  have hcube : ∀ u : NormSet.normOneUnits p q, u ^ (e * e * e) = u := by
    intro u
    set w := data.sigma (SemidirectProduct.inr u) with hw
    have hwU : w ∈ data.U := by
      rw [← data.sigma_U_eq_U]
      exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩
    have e1 : conjGen data * w * (conjGen data)⁻¹ = w ^ e := step w hwU
    have e2 : conjGen data * w ^ e * (conjGen data)⁻¹ = w ^ (e * e) := by
      rw [step _ (data.U.pow_mem hwU e), ← pow_mul]
    have e3 : conjGen data * w ^ (e * e) * (conjGen data)⁻¹ = w ^ (e * e * e) := by
      rw [step _ (data.U.pow_mem hwU (e * e)), ← pow_mul]
    have key : w ^ (e * e * e) = w := by
      calc w ^ (e * e * e)
          = conjGen data * (conjGen data * (conjGen data * w * (conjGen data)⁻¹) *
              (conjGen data)⁻¹) * (conjGen data)⁻¹ := by rw [e1, e2, e3]
        _ = conjGen data ^ 3 * w * (conjGen data ^ 3)⁻¹ := by
            rw [show conjGen data ^ 3 = conjGen data * conjGen data * conjGen data by
              rw [pow_succ, pow_succ, pow_one]]
            group
        _ = w := by rw [hg3]; group
    refine SemidirectProduct.inr_injective (data.sigma_injective ?_)
    rw [map_pow, map_pow]
    exact key
  -- the layered relation holds for every relation triple
  refine commutator_layerClosure_eq_top data.P (conjGen data) ?_
    (closure_relationTriples_eq_top data hp hcube hnotfrob)
  rintro t ⟨v, hv, h1, h2, h3⟩
  have hrel := layered_relation_of_exp data hp hexp hv
  have hshape :
      ((conjGen data ^ 2)⁻¹ * ((v ^ (e * e))⁻¹ * data.s * v ^ (e * e)) * conjGen data ^ 2) *
        ((conjGen data ^ 1)⁻¹ * ((v ^ e)⁻¹ * data.s * v ^ e) * conjGen data ^ 1) *
        ((conjGen data ^ 0)⁻¹ * (v⁻¹ * data.s * v) * conjGen data ^ 0)
      = (conjGen data)⁻¹ * ((conjGen data)⁻¹ * ((v ^ (e * e))⁻¹ * data.s * v ^ (e * e)) *
            conjGen data) * conjGen data *
          (((conjGen data)⁻¹ * ((v ^ e)⁻¹ * data.s * v ^ e) * conjGen data) *
            (v⁻¹ * data.s * v)) := by
    group
  rw [h1, h2, h3, hshape]
  exact hrel

/-- **Theorem 2, the punchline.**  A witness of BG Appendix C, hypothesis (B), for `p = 3` whose
exponent is not a power of the Frobenius has a *non-solvable* ambient group.

Combined with the odd order theorem this says: no finite group of odd order is such a witness.
Together with `false_of_centralizing` (which disposes of `e = 1`, hence of every `q` with
`3 ∤ φ((3^q-1)/2)`), this is the partial resolution of Problem 1 recorded in
`notes/bg/appC_problem1_partial_resolution.md`. -/
theorem not_isSolvable_of_exp (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j)) :
    ¬ IsSolvable G := by
  intro hsol
  have hperf := commutator_layerClosure_eq_top_of_exp data hp hexp hnotfrob
  -- every term of the derived series of the perfect group `N` is everything
  have hder : ∀ n : ℕ, derivedSeries (layerClosure data.P (conjGen data)) n = ⊤ := by
    intro n
    induction n with
    | zero => exact derivedSeries_zero _
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def]; exact hperf
  -- `x = σ(1)` is a non-trivial element of `N`
  have hsN : data.s ∈ layerClosure data.P (conjGen data) := by
    have := mem_layerClosure data.P (conjGen data) (i := 0) (Or.inl rfl) data.s_mem_P
    simpa using this
  have hsne : data.s ≠ 1 := by
    rw [FieldNormalizerData.s]
    intro h
    exact primeLineGenerator_ne_one p q (data.sigma_injective (by rw [h, map_one]))
  refine not_solvable_of_mem_derivedSeries (G := layerClosure data.P (conjGen data))
    (g := ⟨data.s, hsN⟩) ?_ (fun n => by rw [hder n]; exact Subgroup.mem_top _) inferInstance
  intro h
  exact hsne (congrArg Subtype.val h)

end GroupSide

end OddOrder.BG.AppC.Problem1
