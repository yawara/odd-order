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
  let : Fintype (GaloisField 3 q) := Fintype.ofFinite _
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
  have : NeZero N := ⟨by omega⟩
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
      have : CharP (GaloisField 3 q) 3 := by
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
    simp only [Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
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

/-- **The exponent has order three on `σ(U)`.**  Conjugating three times by `g` is conjugating by
`g³ = 1`, so `w^{e³} = w` for every `w ∈ σ(U)`. -/
theorem pow_three_exp_eq_self (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) {z : G} (hz : z ∈ data.U) :
    z ^ (e * e * e) = z := by
  have hx3 : data.s ^ 3 = 1 := by
    subst hp
    rw [FieldNormalizerData.s, ← map_pow, primeLineGenerator_pow_p, map_one]
  have hg3 : conjGen data ^ 3 = 1 := by rw [conjGen_def, ← map_pow, hx3, map_one]
  have step : ∀ w ∈ data.U, conjGen data * w * (conjGen data)⁻¹ = w ^ e := by
    intro w hw
    rw [hexp w hw]
    group
  have e1 : conjGen data * z * (conjGen data)⁻¹ = z ^ e := step z hz
  have e2 : conjGen data * z ^ e * (conjGen data)⁻¹ = z ^ (e * e) := by
    rw [step _ (data.U.pow_mem hz e), ← pow_mul]
  have e3 : conjGen data * z ^ (e * e) * (conjGen data)⁻¹ = z ^ (e * e * e) := by
    rw [step _ (data.U.pow_mem hz (e * e)), ← pow_mul]
  calc z ^ (e * e * e)
      = conjGen data * (conjGen data * (conjGen data * z * (conjGen data)⁻¹) *
          (conjGen data)⁻¹) * (conjGen data)⁻¹ := by rw [e1, e2, e3]
    _ = conjGen data ^ 3 * z * (conjGen data ^ 3)⁻¹ := by
        rw [show conjGen data ^ 3 = conjGen data * conjGen data * conjGen data by
          rw [pow_succ, pow_succ, pow_one]]
        group
    _ = z := by rw [hg3]; group

/-- **Two layers already generate `N`.**  The third layer `σ(P)^{g²}` lies inside
`⟨σ(P), σ(P)^g⟩`: the relation family writes the `g²`-conjugate of `x^{v^{e²}}` as a product of
one element of each of the first two layers, and those `x^u` (`u ∈ σ(U)`) generate `σ(P)`.

So the perfect group of Theorem 2 is generated by **two** abelian subgroups — the same shape as
`SL(2, 2^q) = ⟨U, U⁻⟩` in the book's `p = 2` example (BG Appendix C, Remark (II)). -/
theorem layerClosure_eq_closure_two (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) :
    layerClosure data.P (conjGen data) =
      Subgroup.closure (layerSet data.P (conjGen data) 0 ∪ layerSet data.P (conjGen data) 1) := by
  refine le_antisymm ?_ (Subgroup.closure_mono Set.subset_union_left)
  refine (Subgroup.closure_le _).mpr ?_
  rintro z (hz | hz)
  · exact Subgroup.subset_closure hz
  obtain ⟨w, hwP, rfl⟩ := hz
  -- the `g²`-conjugate of an orbit point is a product of one element from each of the first
  -- two layers
  have key : ∀ v ∈ data.U,
      ((conjGen data) ^ 2)⁻¹ * (v⁻¹ * data.s * v) * (conjGen data) ^ 2 ∈
        Subgroup.closure (layerSet data.P (conjGen data) 0 ∪
          layerSet data.P (conjGen data) 1) := by
    intro v hv
    have hu : v ^ e ∈ data.U := data.U.pow_mem hv e
    have hcube : (v ^ e) ^ (e * e) = v := by
      rw [← pow_mul, ← mul_assoc]
      exact pow_three_exp_eq_self data hp hexp hv
    have hrel := layered_relation_of_exp data hp hexp hu
    rw [hcube] at hrel
    have hshape : ((conjGen data) ^ 2)⁻¹ * (v⁻¹ * data.s * v) * (conjGen data) ^ 2 =
        (conjGen data)⁻¹ * ((conjGen data)⁻¹ * (v⁻¹ * data.s * v) * conjGen data) *
          conjGen data := by
      rw [show (conjGen data) ^ 2 = conjGen data * conjGen data by rw [pow_succ, pow_one]]
      group
    have hfac : ((conjGen data) ^ 2)⁻¹ * (v⁻¹ * data.s * v) * (conjGen data) ^ 2 =
        (((conjGen data)⁻¹ * (((v ^ e) ^ e)⁻¹ * data.s * (v ^ e) ^ e) * conjGen data) *
          ((v ^ e)⁻¹ * data.s * v ^ e))⁻¹ := by
      rw [hshape, eq_inv_iff_mul_eq_one]
      exact hrel
    rw [hfac]
    refine Subgroup.inv_mem _ (Subgroup.mul_mem _ ?_ ?_)
    · exact Subgroup.subset_closure
        (Or.inr ⟨_, conj_s_mem_P data (data.U.pow_mem hu e), by rw [pow_one]⟩)
    · exact Subgroup.subset_closure (Or.inl ⟨_, conj_s_mem_P data hu, by rw [pow_zero]; group⟩)
  -- the `σ(U)`-orbit of `x` generates `σ(P)`, so the conclusion propagates to the whole layer
  have hsub : data.P ≤ Subgroup.comap (MulAut.conj (((conjGen data) ^ 2)⁻¹)).toMonoidHom
      (Subgroup.closure (layerSet data.P (conjGen data) 0 ∪
        layerSet data.P (conjGen data) 1)) := by
    refine le_trans (le_closure_orbitS data hp) ((Subgroup.closure_le _).mpr ?_)
    rintro z ⟨⟨v, hv, rfl⟩, -⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv]
    exact key v hv
  have hmem := hsub hwP
  simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hmem
  exact hmem

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

/-! ### The relation family in field coordinates

The collision-span computation runs entirely in `𝔽_{3^q}`, so the relation family has to be read
through the identification of `σ(P)` with the field.  `layerFieldHom data i` is the `i`-th layer
`t ↦ (gⁱ)⁻¹ σ(inl t) gⁱ`, and `layered_relation_field` is the relation `d(t^{E²}) b(t^E) a(t) = 1`
of `notes/bg/appC_problem1_partial_resolution.md`. -/

/-- The field element underlying a norm-one unit.  (Notation for the doubly-coerced
`((u : (GaloisField p q)ˣ) : GaloisField p q)`, which the relation family is full of.) -/
def normOneVal (u : NormSet.normOneUnits p q) : GaloisField p q :=
  ((u : (GaloisField p q)ˣ) : GaloisField p q)

@[simp]
theorem normOneVal_mul (u v : NormSet.normOneUnits p q) :
    normOneVal (u * v) = normOneVal u * normOneVal v := rfl

@[simp]
theorem normOneVal_inv (u : NormSet.normOneUnits p q) :
    normOneVal u⁻¹ = (normOneVal u)⁻¹ := by
  simp [normOneVal]

@[simp]
theorem normOneVal_pow (u : NormSet.normOneUnits p q) (k : ℕ) :
    normOneVal (u ^ k) = normOneVal u ^ k := by
  simp only [normOneVal, SubgroupClass.coe_pow, Units.val_pow_eq_pow_val]

/-- The element of `σ(U)` attached to a norm-one unit. -/
noncomputable def unitElt (data : FieldNormalizerData p q G) (u : NormSet.normOneUnits p q) : G :=
  data.sigma (SemidirectProduct.inr u)

theorem unitElt_mem_U (data : FieldNormalizerData p q G) (u : NormSet.normOneUnits p q) :
    unitElt data u ∈ data.U := by
  rw [← data.sigma_U_eq_U]
  exact ⟨SemidirectProduct.inr u, ⟨u, rfl⟩, rfl⟩

theorem unitElt_pow (data : FieldNormalizerData p q G) (u : NormSet.normOneUnits p q) (k : ℕ) :
    unitElt data u ^ k = unitElt data (u ^ k) := by
  rw [unitElt, unitElt, ← map_pow, ← map_pow]

/-- **Conjugating `x = σ(1)` by a norm-one unit is multiplication in the field.** -/
theorem conj_s_unitElt (data : FieldNormalizerData p q G) (u : NormSet.normOneUnits p q) :
    (unitElt data u)⁻¹ * data.s * unitElt data u =
      fieldHom data (Multiplicative.ofAdd
        (((u⁻¹ : NormSet.normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) := by
  have hval := inr_inv_mul_primeLineGenerator_mul_inr p q u
  rw [unitElt, FieldNormalizerData.s, ← map_inv data.sigma, ← map_mul data.sigma,
    ← map_mul data.sigma, hval]
  rfl

/-- The `i`-th layer of `σ(P)`, in field coordinates. -/
noncomputable def layerFieldHom (data : FieldNormalizerData p q G) (i : ℕ) :
    Multiplicative (GaloisField p q) →* G :=
  (MulAut.conj (((conjGen data) ^ i)⁻¹) : G →* G).comp (fieldHom data)

@[simp]
theorem layerFieldHom_apply (data : FieldNormalizerData p q G) (i : ℕ)
    (t : Multiplicative (GaloisField p q)) :
    layerFieldHom data i t =
      ((conjGen data) ^ i)⁻¹ * fieldHom data t * (conjGen data) ^ i := by
  change ((conjGen data) ^ i)⁻¹ * fieldHom data t * (((conjGen data) ^ i)⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Each layer is a faithful copy of `(𝔽_{3^q}, +)`: `fieldHom` is injective because `σ` is, and
conjugation is a bijection. -/
theorem layerFieldHom_injective (data : FieldNormalizerData p q G) (i : ℕ) :
    Function.Injective (layerFieldHom data i) := by
  intro s t hst
  simp only [layerFieldHom_apply] at hst
  exact fieldHom_injective data (mul_left_cancel (mul_right_cancel hst))

/-- **The relation family, in field coordinates.**  For every norm-one `u`,

`d(u^{e²}) · b(u^e) · a(u) = 1`,

where `a`, `b`, `d` are the three layers.  This is the shape in which the collision-span
computation of `notes/bg/appC_problem1_partial_resolution.md` uses hypothesis (B). -/
theorem layered_relation_field (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (u : NormSet.normOneUnits p q) :
    layerFieldHom data 2 (Multiplicative.ofAdd
        (((u ^ (e * e) : NormSet.normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) *
      layerFieldHom data 1 (Multiplicative.ofAdd
        (((u ^ e : NormSet.normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) *
      layerFieldHom data 0 (Multiplicative.ofAdd
        (((u : NormSet.normOneUnits p q) : (GaloisField p q)ˣ) : GaloisField p q)) = 1 := by
  have hrel := layered_relation_of_exp data hp hexp (unitElt_mem_U data u⁻¹)
  have h0 := conj_s_unitElt data u⁻¹
  have h1 := conj_s_unitElt data (u⁻¹ ^ e)
  have h2 := conj_s_unitElt data (u⁻¹ ^ (e * e))
  rw [← unitElt_pow] at h1 h2
  rw [h0, h1, h2] at hrel
  simp only [inv_pow, inv_inv] at hrel
  have hshape : ∀ A B C : G,
      (((conjGen data) ^ 2)⁻¹ * A * (conjGen data) ^ 2) *
          (((conjGen data) ^ 1)⁻¹ * B * (conjGen data) ^ 1) *
          (((conjGen data) ^ 0)⁻¹ * C * (conjGen data) ^ 0)
        = (conjGen data)⁻¹ * ((conjGen data)⁻¹ * A * conjGen data) * conjGen data *
            (((conjGen data)⁻¹ * B * conjGen data) * C) := by
    intro A B C
    rw [show (conjGen data) ^ 2 = conjGen data * conjGen data by rw [pow_succ, pow_one],
      pow_one, pow_zero]
    group
  simp only [layerFieldHom_apply]
  rw [hshape]
  exact hrel


/-- **The exponent cubes to the identity on the norm-one units.**  Read off the `G`-level
statement `pow_three_exp_eq_self` through the injectivity of `σ`. -/
theorem normOneUnits_pow_cube (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (u : NormSet.normOneUnits p q) : u ^ (e * e * e) = u := by
  refine SemidirectProduct.inr_injective (data.sigma_injective ?_)
  rw [map_pow, map_pow]
  exact pow_three_exp_eq_self data hp hexp (unitElt_mem_U data u)

/-- **Relation (1) of the collision-span obstruction.**  Substituting `t = r^e` into the relation
family and using `e³ = 1` on the norm-one units,

`d(r) = a(-r^e) · b(-r^{e²})`,

i.e. the third layer at `r` is a product of one element of the first layer and one of the second.
(`notes/bg/appC_problem1_partial_resolution.md`, step 1 of the criterion.) -/
theorem layerFieldHom_two_eq (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (r : NormSet.normOneUnits p q) :
    layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal r))
      = (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (r ^ e))))⁻¹ *
        (layerFieldHom data 1 (Multiplicative.ofAdd (normOneVal (r ^ (e * e)))))⁻¹ := by
  have hrel := layered_relation_field data hp hexp (r ^ e)
  have h1 : (r ^ e) ^ (e * e) = r := by
    rw [← pow_mul, ← mul_assoc]
    exact normOneUnits_pow_cube data hp hexp r
  have h2 : (r ^ e) ^ e = r ^ (e * e) := by rw [← pow_mul]
  rw [h1, h2] at hrel
  have hone : layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal r)) *
      (layerFieldHom data 1 (Multiplicative.ofAdd (normOneVal (r ^ (e * e)))) *
        layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (r ^ e)))) = 1 := by
    rw [← mul_assoc]
    exact hrel
  rw [eq_inv_iff_mul_eq_one.mpr hone, mul_inv_rev]


/-- **Relation (2) of the collision-span obstruction.**  For `p` in the Paley set
`T = {p ∈ U : p - 1 ∈ U}` (given here as a pair `p₀ = p`, `p₁ = p - 1` of norm-one units) and any
norm-one `z`, splitting `z = p z - (p-1) z` and applying relation (1) twice gives the exact
non-commutative factorisation

`d(z) = a(-p^e z^e) · b(K(p) z^{e²}) · a((p-1)^e z^e)`,  `K(p) = (p-1)^{e²} - p^{e²}`.

The two second-layer factors merge because the layer is the image of a homomorphism from an
abelian group.  This is the identity whose *collisions* drive the whole obstruction. -/
theorem layerFieldHom_two_factor (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (p₀ p₁ z : NormSet.normOneUnits p q) (hpp : normOneVal p₀ = normOneVal p₁ + 1) :
    layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal z))
      = (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (p₀ ^ e * z ^ e))))⁻¹ *
        layerFieldHom data 1 (Multiplicative.ofAdd
          ((normOneVal (p₁ ^ (e * e)) - normOneVal (p₀ ^ (e * e))) * normOneVal (z ^ (e * e)))) *
        layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal (p₁ ^ e * z ^ e))) := by
  -- split `z = p₀ z - p₁ z` in the third layer
  have hsplit : normOneVal z = normOneVal (p₀ * z) + -normOneVal (p₁ * z) := by
    simp only [normOneVal_mul, hpp]
    ring
  have hd : layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal z))
      = layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal (p₀ * z))) *
        (layerFieldHom data 2 (Multiplicative.ofAdd (normOneVal (p₁ * z))))⁻¹ := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add, hsplit]
  rw [hd, layerFieldHom_two_eq data hp hexp (p₀ * z), layerFieldHom_two_eq data hp hexp (p₁ * z)]
  -- merge the two second-layer factors
  simp only [mul_inv_rev, inv_inv, mul_pow, normOneVal_mul, normOneVal_pow]
  have hb : (layerFieldHom data 1 (Multiplicative.ofAdd
        (normOneVal p₀ ^ (e * e) * normOneVal z ^ (e * e))))⁻¹ *
      layerFieldHom data 1 (Multiplicative.ofAdd
        (normOneVal p₁ ^ (e * e) * normOneVal z ^ (e * e)))
      = layerFieldHom data 1 (Multiplicative.ofAdd
        ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * normOneVal z ^ (e * e))) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    ring
  simp only [mul_assoc]
  congr 1
  rw [← mul_assoc, hb]


/-- **Relation (3) of the collision-span obstruction: a collision conjugates one second-layer
element into another.**  If `p` and `r` both lie in the Paley set and *collide*, i.e.

`p^e - (p-1)^e = r^e - (r-1)^e`,

then, with `δ = r^e - p^e`, equating the two factorisations of `d(z)` gives

`b(K(r) z^{e²}) = a(δ z^e) · b(K(p) z^{e²}) · a(-δ z^e)`.

Conjugation by a *first*-layer element therefore maps a second-layer element back into the second
layer — the whole point of the obstruction. -/
theorem layerFieldHom_one_conj (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (p₀ p₁ r₀ r₁ z : NormSet.normOneUnits p q)
    (hpp : normOneVal p₀ = normOneVal p₁ + 1) (hrr : normOneVal r₀ = normOneVal r₁ + 1)
    (hcoll : normOneVal p₀ ^ e - normOneVal p₁ ^ e = normOneVal r₀ ^ e - normOneVal r₁ ^ e) :
    layerFieldHom data 1 (Multiplicative.ofAdd
        ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * normOneVal z ^ (e * e)))
      = layerFieldHom data 0 (Multiplicative.ofAdd
            ((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e)) *
        layerFieldHom data 1 (Multiplicative.ofAdd
            ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * normOneVal z ^ (e * e))) *
        layerFieldHom data 0 (Multiplicative.ofAdd
            (-((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e))) := by
  have hP := layerFieldHom_two_factor data hp hexp p₀ p₁ z hpp
  have hR := layerFieldHom_two_factor data hp hexp r₀ r₁ z hrr
  rw [hP] at hR
  simp only [normOneVal_mul, normOneVal_pow] at hR
  -- solve for the second-layer factor of `r`
  have hsolve : layerFieldHom data 1 (Multiplicative.ofAdd
        ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * normOneVal z ^ (e * e)))
      = layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * normOneVal z ^ e)) *
        ((layerFieldHom data 0 (Multiplicative.ofAdd
              (normOneVal p₀ ^ e * normOneVal z ^ e)))⁻¹ *
          layerFieldHom data 1 (Multiplicative.ofAdd
              ((normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) * normOneVal z ^ (e * e))) *
          layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * normOneVal z ^ e))) *
        (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * normOneVal z ^ e)))⁻¹ := by
    rw [hR]
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  -- the two first-layer differences are `δ z^e` and `-δ z^e`
  have hleft : layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₀ ^ e * normOneVal z ^ e)) *
      (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₀ ^ e * normOneVal z ^ e)))⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd
          ((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e)) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    ring
  have hright : layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal p₁ ^ e * normOneVal z ^ e)) *
      (layerFieldHom data 0 (Multiplicative.ofAdd (normOneVal r₁ ^ e * normOneVal z ^ e)))⁻¹
      = layerFieldHom data 0 (Multiplicative.ofAdd
          (-((normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e))) := by
    rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add]
    congr 2
    linear_combination (-(normOneVal z ^ e)) * hcoll
  rw [hsolve, ← hleft, ← hright]
  simp only [mul_assoc]


/-! ### The collision-span endgame

If `σ(P)` normalizes the second layer `σ(P)^g`, the perfect group `N` of Theorem 2 collapses:
`N = σ(P) ⊔ σ(P)^g` is then metabelian (an abelian normal subgroup with abelian quotient), so its
commutator subgroup is proper — contradicting `commutator N = ⊤`.

This is the endgame of the *collision-span obstruction* of
`notes/bg/appC_problem1_partial_resolution.md`: the relation family produces, for every
"collision" of the map `p ↦ p^E - (p-1)^E`, an element `S` with `b(S)^{a(-1)} ∈ B`; once those `S`
span the field, `a(-1)` — and hence, conjugating by `σ(U)`, all of `σ(P)` — normalizes `B`. -/

/-- The second layer `σ(P)^g`, as a subgroup. -/
noncomputable def layerOne (data : FieldNormalizerData p q G) : Subgroup G :=
  data.P.map (MulAut.conj (conjGen data)⁻¹).toMonoidHom

theorem coe_layerOne (data : FieldNormalizerData p q G) :
    (layerOne data : Set G) = layerSet data.P (conjGen data) 1 := by
  ext z
  simp only [layerOne, layerSet, Subgroup.coe_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv, Set.mem_image, pow_one]

theorem layerOne_mul_comm (data : FieldNormalizerData p q G) {a b : G} (ha : a ∈ layerOne data)
    (hb : b ∈ layerOne data) : a * b = b * a := by
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  rw [← map_mul, ← map_mul, P_mul_comm data ha' hb']

/-- `N = ⟨σ(P), σ(P)^g⟩` is the join of the first two layers (`layerClosure_eq_closure_two`, read
as a supremum of subgroups). -/
theorem layerClosure_eq_sup (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) :
    layerClosure data.P (conjGen data) = data.P ⊔ layerOne data := by
  have h0 : layerSet data.P (conjGen data) 0 = (data.P : Set G) := by
    ext z
    simp only [layerSet, pow_zero, inv_one, one_mul, mul_one, Set.image_id']
  have h1 : layerSet data.P (conjGen data) 1 = (layerOne data : Set G) := (coe_layerOne data).symm
  rw [layerClosure_eq_closure_two data hp hexp, h0, h1, Subgroup.closure_union,
    Subgroup.closure_eq, Subgroup.closure_eq]

/-- **The collision-span endgame.**  If `σ(P)` normalizes the second layer, no witness exists.

`N = σ(P) ⊔ σ(P)^g` has the abelian normal subgroup `σ(P)^g` with abelian quotient, so
`commutator N ≤ σ(P)^g` — but Theorem 2 says `commutator N = ⊤`, which forces `N` itself to be
abelian and hence trivial, contradicting `σ(1) ≠ 1`. -/
theorem false_of_normalizes_layerOne (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j))
    (hnorm : data.P ≤ Subgroup.normalizer ((layerOne data : Subgroup G) : Set G)) : False := by
  set N : Subgroup G := layerClosure data.P (conjGen data) with hN
  have hNsup : N = data.P ⊔ layerOne data := layerClosure_eq_sup data hp hexp
  have hPN : data.P ≤ N := by rw [hNsup]; exact le_sup_left
  have hBN : layerOne data ≤ N := by rw [hNsup]; exact le_sup_right
  -- every element of `N` normalizes the second layer
  have hNnorm : N ≤ Subgroup.normalizer ((layerOne data : Subgroup G) : Set G) := by
    rw [hNsup]
    exact sup_le hnorm Subgroup.le_normalizer
  have hBnormal : ((layerOne data).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBN).mpr hNnorm
  have hPcomm : IsMulCommutative (data.P.subgroupOf N) :=
    ⟨⟨fun a b => Subtype.ext (Subtype.ext (P_mul_comm data a.2 b.2))⟩⟩
  have hsup : (layerOne data).subgroupOf N ⊔ data.P.subgroupOf N = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBN hPN, sup_comm, ← hNsup, Subgroup.subgroupOf_self]
  have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hPcomm
  rw [commutator_layerClosure_eq_top_of_exp data hp hexp hnotfrob, top_le_iff,
    Subgroup.subgroupOf_eq_top] at hle
  -- so `N` lies in the abelian second layer, hence is abelian, hence trivial
  have habel : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := fun a ha b hb =>
    layerOne_mul_comm data (hle ha) (hle hb)
  have hbot : commutator N = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z _
    rw [Subgroup.mem_centralizer_iff]
    intro w _
    exact Subtype.ext (habel w.1 w.2 z.1 z.2)
  have htop := commutator_layerClosure_eq_top_of_exp data hp hexp hnotfrob
  rw [hbot] at htop
  -- `x = σ(1)` is a non-trivial element of `N`
  have hsN : data.s ∈ N := by
    have h := mem_layerClosure data.P (conjGen data) (i := 0) (Or.inl rfl) data.s_mem_P
    rw [pow_zero, inv_one, one_mul, mul_one] at h
    exact h
  have hsne : data.s ≠ 1 := by
    rw [FieldNormalizerData.s]
    intro h
    exact primeLineGenerator_ne_one p q (data.sigma_injective (by rw [h, map_one]))
  have hmem : (⟨data.s, hsN⟩ : N) ∈ (⊥ : Subgroup N) := htop ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hmem
  exact hsne (congrArg Subtype.val hmem)

/-- `σ(U)` normalizes the second layer: conjugation by `v ∈ σ(U)` turns into conjugation by
`v^e` inside the layer, and `σ(U)` normalizes `σ(P)`. -/
theorem U_le_normalizer_layerOne (data : FieldNormalizerData p q G) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data) :
    data.U ≤ Subgroup.normalizer ((layerOne data : Subgroup G) : Set G) := by
  intro v hv
  have hvP : v ^ e ∈ Subgroup.normalizer (data.P : Set G) :=
    data.normalizer_P_sup_U_le_normalizer_P
      (Subgroup.le_normalizer (le_sup_right (a := data.P) (data.U.pow_mem hv e)))
  have hPmap := Subgroup.mem_normalizer_iff_map_conj_eq.mp hvP
  have hcomm : v * (conjGen data)⁻¹ = (conjGen data)⁻¹ * v ^ e := by
    have h := hexp v hv
    calc v * (conjGen data)⁻¹
        = (conjGen data)⁻¹ * (conjGen data * v) * (conjGen data)⁻¹ := by group
      _ = (conjGen data)⁻¹ * (v ^ e * conjGen data) * (conjGen data)⁻¹ := by rw [h]
      _ = (conjGen data)⁻¹ * v ^ e := by group
  have hcomm' : conjGen data * v⁻¹ = (v ^ e)⁻¹ * conjGen data := by
    have := congrArg (fun z : G => z⁻¹) hcomm
    simpa using this
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, layerOne, Subgroup.map_map]
  have hfun : (MulAut.conj v : G →* G).comp (MulAut.conj (conjGen data)⁻¹).toMonoidHom
      = (MulAut.conj (conjGen data)⁻¹).toMonoidHom.comp (MulAut.conj (v ^ e) : G →* G) := by
    ext w
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc v * ((conjGen data)⁻¹ * w * conjGen data) * v⁻¹
        = (v * (conjGen data)⁻¹) * w * (conjGen data * v⁻¹) := by group
      _ = ((conjGen data)⁻¹ * v ^ e) * w * ((v ^ e)⁻¹ * conjGen data) := by rw [hcomm, hcomm']
      _ = (conjGen data)⁻¹ * (v ^ e * w * (v ^ e)⁻¹) * conjGen data := by group
  rw [hfun, ← Subgroup.map_map, hPmap]

/-- **The collision-span criterion, group side.**  If the generator `x = σ(1)` of `σ(P₀)`
normalizes the second layer `σ(P)^g`, then *no witness exists*.

Conjugating by `σ(U)` spreads the normalizing property over the whole orbit of `x`, which
generates `σ(P)` (Lemma B); then `false_of_normalizes_layerOne` applies.

This is the endpoint of the collision-span obstruction: the field-side computation produces
elements `S` with `b(S)^{x⁻¹} ∈ B` whose span is everything, which is exactly the hypothesis
`hx` below. -/
theorem false_of_s_normalizes_layerOne (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j))
    (hx : data.s ∈ Subgroup.normalizer ((layerOne data : Subgroup G) : Set G)) : False := by
  refine false_of_normalizes_layerOne data hp hexp hnotfrob ?_
  have hU := U_le_normalizer_layerOne data hexp
  refine le_trans (le_closure_orbitS data hp) ((Subgroup.closure_le _).mpr ?_)
  rintro z ⟨⟨v, hv, rfl⟩, -⟩
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hU hv)) hx) (hU hv)


/-! ### The criterion, assembled -/

/-- The `S`-values produced by a collision whose difference `δ = r^e - p^e` is a *square* (the
value of a norm-one unit).  Normalising by `z = (δ⁻¹)^{e²}` makes `δ z^e = 1`, so relation (3)
becomes conjugation by the fixed element `x = σ(1)`. -/
def collisionSet (p q e : ℕ) [Fact p.Prime] : Set (GaloisField p q) :=
  {S | ∃ p₀ p₁ r₀ r₁ d₀ : NormSet.normOneUnits p q,
      normOneVal p₀ = normOneVal p₁ + 1 ∧ normOneVal r₀ = normOneVal r₁ + 1 ∧
      normOneVal p₀ ^ e - normOneVal p₁ ^ e = normOneVal r₀ ^ e - normOneVal r₁ ^ e ∧
      normOneVal d₀ = normOneVal r₀ ^ e - normOneVal p₀ ^ e ∧
      S = (normOneVal p₁ ^ (e * e) - normOneVal p₀ ^ (e * e)) *
          normOneVal (d₀⁻¹ ^ (e * e)) ^ (e * e)}

/-- **Relation (4).**  For a collision with square difference, conjugation by `x = σ(1)` carries
the second-layer element `b(S)` back into the second layer. -/
theorem conj_layerFieldHom_one_mem (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    {S : GaloisField p q} (hS : S ∈ collisionSet p q e) :
    data.s * layerFieldHom data 1 (Multiplicative.ofAdd S) * (data.s)⁻¹ ∈ layerOne data := by
  obtain ⟨p₀, p₁, r₀, r₁, d₀, hpp, hrr, hcoll, hd, rfl⟩ := hS
  set z : NormSet.normOneUnits p q := d₀⁻¹ ^ (e * e) with hz
  have hcube := normOneUnits_pow_cube data hp hexp d₀⁻¹
  have hze : normOneVal z ^ e = (normOneVal d₀)⁻¹ := by
    have hstep : normOneVal (z ^ e) = normOneVal (d₀⁻¹) := by
      rw [hz, ← pow_mul, hcube]
    rw [normOneVal_pow] at hstep
    rw [hstep, normOneVal_inv]
  have hone : (normOneVal r₀ ^ e - normOneVal p₀ ^ e) * normOneVal z ^ e = 1 := by
    rw [hze, ← hd]
    exact mul_inv_cancel₀ (Units.ne_zero _)
  have h3 := layerFieldHom_one_conj data hp hexp p₀ p₁ r₀ r₁ z hpp hrr hcoll
  rw [hone] at h3
  have ha1 : layerFieldHom data 0 (Multiplicative.ofAdd (1 : GaloisField p q)) = data.s := by
    simp only [layerFieldHom_apply, pow_zero, inv_one, one_mul, mul_one]
    rfl
  have ha2 : layerFieldHom data 0 (Multiplicative.ofAdd (-1 : GaloisField p q)) = (data.s)⁻¹ := by
    rw [← ha1, ← map_inv]
    rfl
  rw [ha1, ha2] at h3
  rw [← h3]
  exact ⟨fieldHom data (Multiplicative.ofAdd
      ((normOneVal r₁ ^ (e * e) - normOneVal r₀ ^ (e * e)) * normOneVal z ^ (e * e))),
    by rw [← fieldHom_range data]; exact ⟨_, rfl⟩,
    by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, layerFieldHom_apply,
      pow_one]⟩

theorem coe_layerOne_eq_range (data : FieldNormalizerData p q G) :
    (layerOne data : Set G) = Set.range (layerFieldHom data 1) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [← fieldHom_range data] at hw
    obtain ⟨t, rfl⟩ := hw
    exact ⟨t, by simp only [layerFieldHom_apply, pow_one, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨fieldHom data t, by rw [← fieldHom_range data]; exact ⟨t, rfl⟩,
      by simp only [layerFieldHom_apply, pow_one, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        inv_inv]⟩

/-- **The collision-span criterion, fully assembled.**  If the `S`-values coming from collisions
with square difference generate `(𝔽_{3^q}, +)`, hypothesis (B) has no witness.

Conjugation by `x = σ(1)` maps a generating set of the second layer back into it, and the second
layer is finite, so `x` normalizes it; `false_of_s_normalizes_layerOne` finishes.  This is exactly
the criterion verified computationally for `q = 7, 13, 19` in
`notes/meta/gap/verify_collision_span.g`. -/
theorem false_of_collisionSet_spanning (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j))
    (hspan : AddSubgroup.closure (collisionSet p q e) = ⊤) : False := by
  classical
  have : Finite (layerOne data) := by
    have hfin : ((layerOne data : Subgroup G) : Set G).Finite := by
      rw [coe_layerOne_eq_range data]
      exact Set.finite_range _
    exact hfin.to_subtype
  -- conjugation by `x` maps the second layer into itself
  have hmapsto : ∀ z ∈ layerOne data, data.s * z * (data.s)⁻¹ ∈ layerOne data := by
    have hJ : ∀ t : GaloisField p q,
        data.s * layerFieldHom data 1 (Multiplicative.ofAdd t) * (data.s)⁻¹ ∈ layerOne data := by
      have hsub : collisionSet p q e ⊆ {t : GaloisField p q |
          data.s * layerFieldHom data 1 (Multiplicative.ofAdd t) * (data.s)⁻¹ ∈ layerOne data} :=
        fun t ht => conj_layerFieldHom_one_mem data hp hexp ht
      have hgrp : AddSubgroup.closure (collisionSet p q e) ≤
          { carrier := {t : GaloisField p q |
              data.s * layerFieldHom data 1 (Multiplicative.ofAdd t) * (data.s)⁻¹ ∈ layerOne data}
            zero_mem' := by
              simp only [Set.mem_ofPred_eq, ofAdd_zero, map_one, mul_one, mul_inv_cancel]
              exact (layerOne data).one_mem
            add_mem' := fun {a b} ha hb => by
              simp only [Set.mem_ofPred_eq, ofAdd_add, map_mul] at *
              have : data.s * (layerFieldHom data 1 (Multiplicative.ofAdd a) *
                  layerFieldHom data 1 (Multiplicative.ofAdd b)) * (data.s)⁻¹ =
                  (data.s * layerFieldHom data 1 (Multiplicative.ofAdd a) * (data.s)⁻¹) *
                  (data.s * layerFieldHom data 1 (Multiplicative.ofAdd b) * (data.s)⁻¹) := by
                group
              rw [this]
              exact (layerOne data).mul_mem ha hb
            neg_mem' := fun {a} ha => by
              simp only [Set.mem_ofPred_eq, ofAdd_neg, map_inv] at *
              have : data.s * (layerFieldHom data 1 (Multiplicative.ofAdd a))⁻¹ * (data.s)⁻¹ =
                  (data.s * layerFieldHom data 1 (Multiplicative.ofAdd a) * (data.s)⁻¹)⁻¹ := by
                group
              rw [this]
              exact (layerOne data).inv_mem ha } :=
        (AddSubgroup.closure_le _).mpr hsub
      intro t
      have := hgrp (by rw [hspan]; trivial : t ∈ AddSubgroup.closure (collisionSet p q e))
      exact this
    intro z hz
    rw [← SetLike.mem_coe, coe_layerOne_eq_range data] at hz
    obtain ⟨t, rfl⟩ := hz
    exact hJ (Multiplicative.toAdd t)
  -- finiteness upgrades this to normalizing
  have hmap_le : (layerOne data).map (MulAut.conj data.s : G →* G) ≤ layerOne data := by
    rintro _ ⟨z, hz, rfl⟩
    exact hmapsto z hz
  have hcard : Nat.card ((layerOne data).map (MulAut.conj data.s : G →* G))
      = Nat.card (layerOne data) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj data.s : G →* G))
      (MulAut.conj data.s).injective
  exact false_of_s_normalizes_layerOne data hp hexp hnotfrob
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (Subgroup.eq_of_le_of_card_ge hmap_le (le_of_eq hcard.symm)))


/-- **Theorem 2, the punchline.**  A witness of BG Appendix C, hypothesis (B), for `p = 3` whose
exponent is not a power of the Frobenius has a *non-solvable* ambient group.

Combined with the odd order theorem this says: no finite group of odd order is such a witness.
Together with `false_of_centralizing` (which disposes of `e = 1`, hence of every `q` with
`3 ∤ φ((3^q-1)/2)`), this is the partial resolution of Problem 1 recorded in
`notes/bg/appC_problem1_partial_resolution.md`. -/
theorem not_isSolvable_of_exp (data : FieldNormalizerData p q G) (hp : p = 3) {e : ℕ}
    (hexp : ∀ w ∈ data.U, conjGen data * w = w ^ e * conjGen data)
    (hnotfrob : ∀ j : ℕ, ∃ u : NormSet.normOneUnits p q, u ^ e ≠ u ^ (3 ^ j)) :
    ¬ Group.IsSolvable G := by
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
  refine not_isSolvable_of_mem_derivedSeries (G := layerClosure data.P (conjGen data))
    (g := ⟨data.s, hsN⟩) ?_ (fun n => by rw [hder n]; exact Subgroup.mem_top _) inferInstance
  intro h
  exact hsne (congrArg Subtype.val h)

end GroupSide

end OddOrder.BG.AppC.Problem1
