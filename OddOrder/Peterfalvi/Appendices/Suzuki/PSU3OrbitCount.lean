/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3Preliminary
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3FieldArithmetic
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3CenterCoordinate
import OddOrder.Peterfalvi.Appendices.Suzuki.QuotientKWField
import OddOrder.Peterfalvi.Appendices.Suzuki.ModelIsomorphism

/-!
# Peterfalvi Part II, Ch. IV §2: the orbit count of step (8)

The model-dependent half of step (8) (p. 124).  `PSU3Preliminary` supplies the purely
group-theoretic content — steps (1)–(7), the two fibre bounds, `D = K W` — and this
file adds what needs the standard model of Ch. III §3 (`QuotientFieldModel`):

* the scalar group `μ(KW) ≤ E^×` and its order `(q − 1)|W|`;
* the orbit count `n = |E^×| / |μ(KW)| = (q + 1)/|W|`;
* the map `Φ = orbitOfF : Q₀ → E^× ⧸ μ(KW)` sending `x` to the `KW`-orbit of
  `f(ω x)`, together with the translation of its fibres into the shape the bounds of
  `PSU3Preliminary` consume;
* the two fibre bounds `m_i ≤ |V|` and `m₁ ≤ |V| − 1` in terms of `Φ`.

The field arithmetic of `E/F` that §2 also needs — steps (12)–(14), (16) and the
book's `τ` — is in `PSU3FieldArithmetic`, which this file imports.

## Main results

* `Hypothesis.index_range_mu` — `n = (q + 1)/|W|`.
* `Hypothesis.orbitOfF` — the map `Φ` of step (8).
* `Hypothesis.ncard_fiber_orbitOfF_le`, `Hypothesis.ncard_fiber_orbitOfF_base_le` —
  the fibre bounds.

The squeeze that turns those bounds into equalities (`card_fiber_eq_of_card_eq`) is a
general counting lemma and lives in `PSU3FieldArithmetic` alongside the rest.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp
/-! ## The scalar group `μ(KW)` inside `E^×`

Step (8) counts the `KW`-orbits on `(Q/Q₀)^# ≅ E^×`, i.e. the index of `μ(KW)` in
`E^×`.  The two containments recorded in `QuotientFieldModel` — `μ(K) ⊆ F^×` and
`μ(W)` in the norm-one subgroup — pin its order down to `(q − 1) · |W|`.
-/

/-- `μ(k)^{q−1} = 1`: `μ(K)` lies in `F^× = 𝐅_q^×`
(`QuotientFieldModel.mu_K_frobFixed` says `μ(k)^q = μ(k)`). -/
theorem mu_K_pow_two_pow_sub_one {m : ℕ} (M : hyp.QuotientFieldModel m)
    (k : ↥hyp.actualKActor) : M.mu (k, 1) ^ (2 ^ m - 1) = 1 := by
  have hfix : M.mu (k, 1) ^ (2 ^ m) = M.mu (k, 1) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact M.mu_K_frobFixed k
  have hle : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have e : (2 : ℕ) ^ m = 1 + (2 ^ m - 1) := by omega
  rw [e, pow_add, pow_one] at hfix
  have h2 : M.mu (k, 1) * M.mu (k, 1) ^ (2 ^ m - 1) = M.mu (k, 1) * 1 := by
    rw [mul_one]; exact hfix
  exact mul_left_cancel h2

/-- **`|K| = q − 1`**: `μ` maps `K` bijectively onto `F^× = 𝐅_q^×`.

Injectivity is `QuotientFieldModel.mu_K_injective`; surjectivity is
`exists_actualKActor_mu_eq`; and `|F| = q` is
`OddOrder.FiniteField.natCard_frobFixedSubfield`. -/
theorem card_actualKActor_eq {m : ℕ} (s : hyp.LemmaFiveSetup m)
    (M : hyp.QuotientFieldModel m) (hm : m ≠ 0)
    (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m) :
    Nat.card ↥hyp.actualKActor = 2 ^ m - 1 := by
  classical
  set f : ↥hyp.actualKActor → M.E := fun k => ((M.mu (k, 1) : M.Eˣ) : M.E) with hf
  have hinj : Function.Injective f := fun k k' h => M.mu_K_injective (Units.ext h)
  have hrange : Set.range f
      = ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨k, rfl⟩
      exact ⟨OddOrder.FiniteField.mem_frobFixedSubfield.mpr (M.mu_K_frobFixed k),
        Units.ne_zero _⟩
    · rintro a ⟨haF, ha0⟩
      obtain ⟨k, hk⟩ := hyp.exists_actualKActor_mu_eq s M hm hQ0card haF
        (by simpa using ha0)
      exact ⟨k, hk⟩
  have hcardF : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E)).ncard
      = 2 ^ m := by
    rw [← Nat.card_coe_set_eq]
    exact OddOrder.FiniteField.natCard_frobFixedSubfield M.card hm
  have hT : ((OddOrder.FiniteField.frobFixedSubfield M.E 2 m : Set M.E) \ {0}).ncard
      = 2 ^ m - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem
      (OddOrder.FiniteField.frobFixedSubfield M.E 2 m).zero_mem, hcardF]
  have hcard : Nat.card ↥hyp.actualKActor = (Set.range f).ncard := by
    rw [← Nat.card_coe_set_eq]
    exact (Nat.card_range_of_injective hinj).symm
  rw [hcard, hrange, hT]

/-- **`μ(K) ∩ μ(W) = 1`**: a common value is killed by both `q − 1` and `q + 1`, which
are coprime. -/
theorem mu_K_eq_mu_W_imp_eq_one {m : ℕ} (hm : m ≠ 0) (M : hyp.QuotientFieldModel m)
    {k : ↥hyp.actualKActor} {v : ↥hyp.W} (heq : M.mu (k, 1) = M.mu (1, v)) :
    M.mu (k, 1) = 1 :=
  eq_one_of_pow_two_pow_sub_one_of_pow_two_pow_add_one hm
    (hyp.mu_K_pow_two_pow_sub_one M k)
    (by rw [heq]; exact M.mu_W_normOne v)

/-- **The number of `KW`-orbits on `(Q/Q₀)^#` is `n = (q + 1)/|W|`.**

Since `KW` acts on `Q/Q₀ ≅ E` by scalars, its orbits on `E^×` are the cosets of the
subgroup `μ(KW) ≤ E^×`, so their number is the index of that subgroup.  Its order is
`|K| · |W| = (q − 1)|W|` (by injectivity of `μ`), and `|E^×| = q² − 1`. -/
theorem index_range_mu {m : ℕ} (hm : m ≠ 0) (M : hyp.QuotientFieldModel m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1) :
    (MonoidHom.range M.mu).index = (2 ^ m + 1) / Nat.card ↥hyp.W := by
  classical
  haveI : Fintype M.E := Fintype.ofFinite _
  have hrange : Nat.card ↥(MonoidHom.range M.mu)
      = (2 ^ m - 1) * Nat.card ↥hyp.W := by
    have e1 : Nat.card (↥hyp.actualKActor × ↥hyp.W) = Nat.card ↥(MonoidHom.range M.mu) :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← e1, Nat.card_prod, hK]
  have hunits : Nat.card M.Eˣ = (2 ^ m) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, M.card]
  have hidx := (MonoidHom.range M.mu).index_mul_card
  rw [hrange, hunits] at hidx
  have hpos : 0 < (2 ^ m - 1) * Nat.card ↥hyp.W := by
    have h2 : (2 : ℕ) ≤ 2 ^ m := by
      calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm)
    have hW : 0 < Nat.card ↥hyp.W := Nat.card_pos
    have h1 : 0 < 2 ^ m - 1 := by omega
    exact Nat.mul_pos h1 hW
  rw [← two_pow_sq_sub_one_div (e := m) (m := Nat.card ↥hyp.W) hm]
  rw [← hidx, Nat.mul_div_cancel _ hpos]

/-- The coordinate of an element of `Q − Q₀` is a **nonzero** element of `E`.

`coord` is an additive isomorphism `Q/Z(Q) ≃+ E`, and under `Z(Q) = Q₀` (the
`LemmaFiveSetup` hypothesis) an element of `Q` has trivial image in the quotient
exactly when it lies in `Q₀`.  This is what lets step (8) send `x ∈ Q₀` to a *unit*
of `E`, hence to a coset of `μ(KW)`. -/
theorem coord_ne_zero_of_not_mem_Q0 {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z : G} (hzQ : z ∈ hyp.Q) (hzQ0 : z ∉ hyp.Q0) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) ≠ 0 := by
  intro hc
  refine hzQ0 ?_
  have hzero : (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 :=
    (AddEquiv.map_eq_zero_iff M.coord).mp hc
  have hone : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = 1 := hzero
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q :=
    QuotientGroup.eq_one_iff _ |>.mp hone
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  exact hmem

/-- `f(ω x) ∈ Q` for `x ∈ Q₀` — named so that it can serve as the coercion proof in
`fUnit`, making `fUnit_val` hold by `rfl`. -/
theorem f_mul_mem_Q {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    f (ω * (x : G)) ∈ hyp.Q :=
  (hyp.f_mem_sdiff_Q0 H hC2 (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).1
    (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).2).1

/-- `f(ω x) ∉ Q₀` for `x ∈ Q₀`. -/
theorem f_mul_not_mem_Q0 {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    f (ω * (x : G)) ∉ hyp.Q0 :=
  (hyp.f_mem_sdiff_Q0 H hC2 (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).1
    (hyp.mul_mem_sdiff_Q0 hωQ hωQ0 x.2).2).2

/-- The coordinate of `f(ω x)` as a **unit** of `E`. -/
noncomputable def fUnit {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) : M.Eˣ :=
  Units.mk0 (M.coord (Additive.ofMul (QuotientGroup.mk
      (⟨f (ω * (x : G)), hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x⟩ : ↥hyp.Q))))
    (hyp.coord_ne_zero_of_not_mem_Q0 M hZ _ (hyp.f_mul_not_mem_Q0 H hC2 hωQ hωQ0 x))

@[simp] theorem fUnit_val {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    ((hyp.fUnit M hZ H hC2 hωQ hωQ0 x : M.Eˣ) : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk
          (⟨f (ω * (x : G)), hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x⟩ : ↥hyp.Q))) := rfl

/-- Elements of `Q₀` have **zero** coordinate in `E` — the `(0, ·)` half of the book's
`y = (0, α)` (p. 125).

Converse of `coord_ne_zero_of_not_mem_Q0`: under `Z(Q) = Q₀` an element of `Q₀` is
trivial in `Q/Z(Q)`, so its coordinate vanishes.  Step (10) needs this to speak of the
second coordinate `α` of `y` at all. -/
theorem coord_eq_zero_of_mem_Q0 {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z : G} (hzQ : z ∈ hyp.Q) (hzQ0 : z ∈ hyp.Q0) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 := by
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q := by
    rw [hZ, Subgroup.mem_subgroupOf]
    exact hzQ0
  have hone : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  have hzero : (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 := hone
  rw [hzero, map_zero]

/-- **The map of step (8)**: `x ∈ Q₀ ↦` the `μ(KW)`-coset of the coordinate of
`f(ω x)`.

Because `KW` acts on `Q/Q₀ ≅ E` by scalars, this coset is exactly the `KW`-orbit the
book refers to. -/
noncomputable def orbitOfF {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (x : ↥hyp.Q0) :
    M.Eˣ ⧸ (MonoidHom.range M.mu) :=
  QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x)

/-- **`conjQHom kv` is conjugation by an element of `D`.**

`actualKActor` is the range of `conjQByK`, and both `conjQByK k` and `conjQByW v` are
literally `x ↦ k x k⁻¹` and `x ↦ v x v⁻¹`; composing them gives conjugation by `k v`,
which lies in `D` since `K ≤ D` and `W ≤ V ≤ D`.

This is what turns the `KW`-orbit of step (8) into a `D`-conjugacy class, so that
`exists_conj_mul_Q0_iff` applies. -/
theorem exists_mem_D_conjQHom (kv : ↥hyp.actualKActor × ↥hyp.W) :
    ∃ d ∈ hyp.D, ∀ x : ↥hyp.Q,
      ((hyp.conjQHom kv x : ↥hyp.Q) : G) = d * (x : G) * d⁻¹ := by
  obtain ⟨k, hk⟩ := (MonoidHom.mem_range).mp kv.1.2
  have hWD : hyp.W ≤ hyp.D := le_trans inf_le_left hyp.V_le_D
  refine ⟨(k : G) * (kv.2 : G),
    hyp.D.mul_mem (hyp.K_le_D k.2) (hWD kv.2.2), fun x => ?_⟩
  rw [hyp.conjQHom_apply, MulAut.mul_apply]
  simp only [Subgroup.coe_subtype]
  rw [← hk]
  change (k : G) * ((kv.2 : G) * (x : G) * (kv.2 : G)⁻¹) * (k : G)⁻¹ = _
  group

/-- Two elements of `Q` with the same image in `Q/Z(Q)` differ by an element of `Q₀`.

Step 6 of the fibre translation: the quotient equality coming from `coord` is turned
into an honest product `z' = z · w` with `w ∈ Q₀`, which is what
`exists_conj_mul_Q0_iff` consumes. -/
theorem exists_mem_Q0_mul_of_quotient_eq
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q)
    (heq : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) : ↥hyp.Q ⧸ Subgroup.center hyp.Q)
      = QuotientGroup.mk ⟨z', hz'Q⟩) :
    ∃ w ∈ hyp.Q0, z' = z * w := by
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q)⁻¹ * ⟨z', hz'Q⟩ ∈ Subgroup.center hyp.Q :=
    QuotientGroup.eq.mp heq
  rw [hZ, Subgroup.mem_subgroupOf] at hmem
  refine ⟨z⁻¹ * z', hmem, by group⟩

/-- Steps 1–4 of the fibre translation: if the coordinates of `z, z' ∈ Q` lie in the
same coset of `μ(KW)` in `E^×`, then `z'` and a `KW`-translate of `z` agree in
`Q/Z(Q)`.

`coord_act` turns multiplication by `μ(kv)` in `E` into the action of `kv` on the
quotient, and `quotientKWHom_mk` re-expresses that action as `conjQHom`. -/
theorem exists_conjQHom_quotient_eq_of_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q) {u u' : M.Eˣ}
    (hu : (u : M.E) = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))))
    (hu' : (u' : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q))))
    (heq : (QuotientGroup.mk u : M.Eˣ ⧸ MonoidHom.range M.mu) = QuotientGroup.mk u') :
    ∃ kv, (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q) : ↥hyp.Q ⧸ Subgroup.center hyp.Q)
      = QuotientGroup.mk (hyp.conjQHom kv ⟨z, hzQ⟩) := by
  obtain ⟨kv, hkv⟩ := MonoidHom.mem_range.mp (QuotientGroup.eq.mp heq)
  refine ⟨kv, ?_⟩
  -- `u' = u * μ kv`, hence the same relation between the coordinates in `E`
  have hprod : u' = u * M.mu kv := by
    rw [hkv]
    group
  have hE : M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q)))
      = ((M.mu kv : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) := by
    rw [← hu, ← hu', hprod, Units.val_mul, mul_comm]
  -- `coord_act` identifies the right-hand side with the action of `kv`
  rw [← M.coord_act kv (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))] at hE
  have := M.coord.injective hE
  have h2 := Additive.ofMul.injective this
  rw [h2, hyp.quotientKWHom_mk]

/-- **The fibre translation** (step 7, assembling steps 1–6): if the coordinates of
`z, z' ∈ Q` lie in the same coset of `μ(KW)` in `E^×`, then

  `z' = (z · y)^a`  for some `y ∈ Q₀` and `a ∈ D`,

which is exactly the hypothesis shape of `ncard_le_card_V_of_f_eq_conj` and
`not_mem_K_of_f_eq_conj_self`. -/
theorem exists_conj_of_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q) {u u' : M.Eˣ}
    (hu : (u : M.E) = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))))
    (hu' : (u' : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q))))
    (heq : (QuotientGroup.mk u : M.Eˣ ⧸ MonoidHom.range M.mu) = QuotientGroup.mk u') :
    ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D, z' = a⁻¹ * (z * y) * a := by
  obtain ⟨kv, hkv⟩ :=
    hyp.exists_conjQHom_quotient_eq_of_coset_eq M hzQ hz'Q hu hu' heq
  obtain ⟨d, hd, hconj⟩ := hyp.exists_mem_D_conjQHom kv
  obtain ⟨w, hw, hzw⟩ := hyp.exists_mem_Q0_mul_of_quotient_eq hZ
    (hyp.conjQHom kv ⟨z, hzQ⟩).2 hz'Q hkv.symm
  rw [hconj ⟨z, hzQ⟩] at hzw
  refine hyp.exists_conj_mul_Q0_iff.mp ⟨d⁻¹, hyp.D.inv_mem hd, w, hw, ?_⟩
  rw [hzw]
  group

/-- **Each fibre of `orbitOfF` has at most `|V|` elements.**

If the fibre over `c` is nonempty, pick `x₀` in it and set `ω' = f(ω x₀)`.  For any
other `x` in the fibre, `exists_conj_of_coset_eq` gives `f(ω x) = (ω' y)^a`, so the
fibre embeds in the set bounded by `ncard_le_card_V_of_f_eq_conj`.

Under Chapter IV's `V = W` this is the book's `m_i ≤ m`. -/
theorem ncard_fiber_orbitOfF_le {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (c : M.Eˣ ⧸ (MonoidHom.range M.mu)) :
    {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
      ≤ Nat.card ↥hyp.V := by
  classical
  rcases Set.eq_empty_or_nonempty
      {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c} with he | ⟨x₀, hx₀⟩
  · rw [he, Set.ncard_empty]
    exact Nat.zero_le _
  · have hsub : ((↑) : ↥hyp.Q0 → G) ''
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}
        ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
            f (ω * z) = a⁻¹ * (f (ω * (x₀ : G)) * y) * a} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have hcoset :
          (QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x₀) :
            M.Eˣ ⧸ MonoidHom.range M.mu)
            = QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x) :=
        hx₀.trans hx.symm
      exact hyp.exists_conj_of_coset_eq M hZ
        (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x₀) (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x)
        rfl rfl hcoset
    calc {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
        = (((↑) : ↥hyp.Q0 → G) ''
            {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
            f (ω * z) = a⁻¹ * (f (ω * (x₀ : G)) * y) * a}.ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Nat.card ↥hyp.V := hyp.ncard_le_card_V_of_f_eq_conj H hC2 hωQ hωQ0

/-- The coordinate of `ω` itself as a unit of `E`; its coset is the distinguished
orbit `b₀` of step (8) (the book's `ω̄₁`). -/
noncomputable def baseUnit {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) : M.Eˣ :=
  Units.mk0 (M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))))
    (hyp.coord_ne_zero_of_not_mem_Q0 M hZ hωQ hωQ0)

@[simp] theorem baseUnit_val {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    ((hyp.baseUnit M hZ hωQ hωQ0 : M.Eˣ) : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))) := rfl

/-- **The distinguished fibre has at most `|V| − 1` elements** — the book's
`m₁ ≤ m − 1`.

Here no representative is needed: `ω` itself is the reference point, so
`exists_conj_of_coset_eq` applies with `z = ω` directly and the target set is the one
bounded by `ncard_le_card_V_sub_one_of_f_eq_conj_self`. -/
theorem ncard_fiber_orbitOfF_base_le {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
      ≤ Nat.card ↥hyp.V - 1 := by
  classical
  have hsub : ((↑) : ↥hyp.Q0 → G) ''
      {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}
      ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
          f (ω * z) = a⁻¹ * (ω * y) * a} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    exact hyp.exists_conj_of_coset_eq M hZ hωQ
      (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x) rfl rfl hx.symm
  calc {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
      = (((↑) : ↥hyp.Q0 → G) ''
          {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
            = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
          f (ω * z) = a⁻¹ * (ω * y) * a}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card ↥hyp.V - 1 :=
        hyp.ncard_le_card_V_sub_one_of_f_eq_conj_self H hC2 hωQ hωQ0

/-- **Peterfalvi Part II, Ch. IV §2, step (8)** (p. 124):

> The number of elements `x ∈ Q₀` such that `f(ω₁ x)‾` is in the orbit of `ω̄_i` under
> `KW` is `m` if `i > 1` and `m − 1` if `i = 1`.

All the inequalities are equalities: every fibre of `Φ = orbitOfF` other than the one
over `ω`'s own orbit has exactly `|W|` elements, and that distinguished fibre has
exactly `|W| − 1`.

The bounds are `ncard_fiber_orbitOfF_le` and `ncard_fiber_orbitOfF_base_le` (which
give `|V|`, equal to `|W|` under Chapter IV's `V = W`); the counting is
`card_fiber_eq_of_card_eq` with `|Q₀| = q` and `|E^× ⧸ μ(KW)| = (q + 1)/|W|`, so that
`q = ((q+1)/|W|) · |W| − 1`. -/
theorem stepEight {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    (∀ c, c ≠ QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0) →
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
          = Nat.card ↥hyp.W)
      ∧ {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
          = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
          = Nat.card ↥hyp.W - 1 := by
  have hβ : Nat.card (M.Eˣ ⧸ MonoidHom.range M.mu) = (2 ^ m + 1) / Nat.card ↥hyp.W := by
    rw [← Subgroup.index_eq_card, hyp.index_range_mu hm M hinj hK]
  have hcard : Nat.card ↥hyp.Q0
      = Nat.card (M.Eˣ ⧸ MonoidHom.range M.mu) * Nat.card ↥hyp.W - 1 := by
    rw [hβ, Nat.div_mul_cancel hWdvd, hQ0card]
    omega
  refine card_fiber_eq_of_card_eq (hyp.orbitOfF M hZ H hC2 hωQ hωQ0) Nat.card_pos _
    (fun c => ?_) ?_ hcard
  · have := hyp.ncard_fiber_orbitOfF_le M hZ H hC2 hωQ hωQ0 c
    rwa [hVW] at this
  · have := hyp.ncard_fiber_orbitOfF_base_le M hZ H hC2 hωQ hωQ0
    rwa [hVW] at this

/-- **Every `K W`-orbit is attained on the fibre `ρ Q₀`** (Peterfalvi Part II, Ch. IV
§3 (5), p. 131: "possibly on replacing `ρ` by an element of `ρ Q₀`, we may assume by (8)
of §2 that `f(ρ)` is in the orbit of `ω̄` under `K W`").

Step (8) counts every fibre of `orbitOfF` as `|W|` — or `|W| − 1` on the distinguished
orbit — and `|W| > 1`, so no fibre is empty.  That is exactly the freedom stage (5) uses
in its second case. -/
theorem exists_mem_Q0_orbitOfF_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (c : M.Eˣ ⧸ (MonoidHom.range M.mu)) :
    ∃ x : ↥hyp.Q0, hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c := by
  obtain ⟨hgen, hbase⟩ :=
    hyp.stepEight M hZ H hC2 hVW hm hQ0card hinj hK hWdvd hωQ hωQ0
  have hne : {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard ≠ 0 := by
    by_cases hc : c = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)
    · rw [hc, hbase]
      omega
    · rw [hgen c hc]
      omega
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨x, hx⟩

/-- **The set-level count is exact**: `|S| = |W| − 1`, where

  `S = {z ∈ Q₀ | ∃ y ∈ Q₀, ∃ a ∈ D, f(ω z) = (ω y)^a}`.

`≤` is `ncard_le_card_V_sub_one_of_f_eq_conj_self`; `≥` comes from step (8), which
pins the distinguished fibre at exactly `|W| − 1` and whose image lies in `S`.

Exactness is what makes the coset map on `S` *surjective* onto the nontrivial cosets
of `K`, which is how step (9) produces its `kζ`. -/
theorem ncard_eq_card_W_sub_one_of_f_eq_conj_self {m : ℕ}
    (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
        f (ω * z) = a⁻¹ * (ω * y) * a}.ncard = Nat.card ↥hyp.W - 1 := by
  classical
  refine le_antisymm ?_ ?_
  · have hle := hyp.ncard_le_card_V_sub_one_of_f_eq_conj_self H hC2 hωQ hωQ0
    rwa [hVW] at hle
  · have hstep := (hyp.stepEight M hZ H hC2 hVW hm hQ0card hinj hK hWdvd hωQ hωQ0).2
    have hsub : ((↑) : ↥hyp.Q0 → G) ''
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
          = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}
        ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
            f (ω * z) = a⁻¹ * (ω * y) * a} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      exact hyp.exists_conj_of_coset_eq M hZ hωQ
        (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x) rfl rfl hx.symm
    calc Nat.card ↥hyp.W - 1
        = {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
            = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard := hstep.symm
      _ = (((↑) : ↥hyp.Q0 → G) ''
            {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
              = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- **The witnesses realize every nontrivial coset of `K`.**

The coset map on `S` is injective (step (7)), avoids the identity coset
(`not_mem_K_of_f_eq_conj_self`), and `|S| = |W| − 1 = |D : K| − 1`
(`ncard_eq_card_W_sub_one_of_f_eq_conj_self`) — so its image is *all* of
`(D/K) ∖ {1}`.

This is what lets step (9) choose the witness with `a ∈ Kζ`: `ζ ≠ 1` by (C2). -/
theorem exists_witness_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {d : G} (hdD : d ∈ hyp.D) (hdK : d ∉ hyp.K) :
    ∃ z ∈ hyp.Q0, ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
      a⁻¹ * d ∈ hyp.K ∧ f (ω * z) = a⁻¹ * (ω * y) * a := by
  classical
  set S : Set G := {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ a ∈ hyp.D,
    f (ω * z) = a⁻¹ * (ω * y) * a} with hSdef
  have key : ∀ z ∈ S, ∃ a, a ∈ hyp.D ∧ ∃ b, b ∈ hyp.Q0 ∧
      f (ω * z) = a⁻¹ * (ω * b) * a := by
    rintro z ⟨-, b, hb, a, ha, heq⟩
    exact ⟨a, ha, b, hb, heq⟩
  choose! A hAD B hBQ0 hAeq using key
  set A' : G → ↥hyp.D := fun z => if hh : A z ∈ hyp.D then ⟨A z, hh⟩ else 1 with hA'def
  have hA'val : ∀ z ∈ S, (A' z : G) = A z := by
    intro z hz
    simp only [hA'def, dif_pos (hAD z hz)]
  set Ψ : G → ↥hyp.D ⧸ hyp.K.subgroupOf hyp.D := fun z => QuotientGroup.mk (A' z)
    with hΨdef
  have hinjOn : Set.InjOn Ψ S := by
    intro z₁ hz₁ z₂ hz₂ hzz
    have hmem : (A' z₁)⁻¹ * A' z₂ ∈ hyp.K.subgroupOf hyp.D := QuotientGroup.eq.mp hzz
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : (A z₁)⁻¹ * A z₂ ∈ hyp.K := by
      have e : (((A' z₁)⁻¹ * A' z₂ : ↥hyp.D) : G) = (A z₁)⁻¹ * A z₂ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hA'val z₁ hz₁, hA'val z₂ hz₂]
      rwa [e] at hmem
    exact hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hz₁.1 hz₂.1
      (hBQ0 z₁ hz₁) (hBQ0 z₂ hz₂) (hAD z₁ hz₁) (hAD z₂ hz₂)
      (hAeq z₁ hz₁) (hAeq z₂ hz₂) hmem'
  have hmaps : Ψ '' S ⊆ (Set.univ \ {1} : Set (↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)) := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨Set.mem_univ _, fun hc => ?_⟩
    have hone : A' z ∈ hyp.K.subgroupOf hyp.D := (QuotientGroup.eq_one_iff (A' z)).mp hc
    rw [Subgroup.mem_subgroupOf, hA'val z hz] at hone
    exact hyp.not_mem_K_of_f_eq_conj_self H hC2 hωQ hωQ0 hz.1 (hBQ0 z hz)
      (hAD z hz) (hAeq z hz) hone
  have hScard := hyp.ncard_eq_card_W_sub_one_of_f_eq_conj_self M hZ H hC2 hVW hm
    hQ0card hinj hKcard hWdvd hωQ hωQ0
  have hdiff : (Set.univ \ {1} : Set (↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)).ncard
      = Nat.card ↥hyp.W - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ,
      ← Subgroup.index_eq_card, hyp.index_K_subgroupOf_D, hVW]
  have heq : Ψ '' S = (Set.univ \ {1} : Set (↥hyp.D ⧸ hyp.K.subgroupOf hyp.D)) :=
    Set.eq_of_subset_of_ncard_le hmaps
      (by rw [hinjOn.ncard_image, hScard, hdiff]) (Set.toFinite _)
  have hdne : (QuotientGroup.mk (⟨d, hdD⟩ : ↥hyp.D) :
      ↥hyp.D ⧸ hyp.K.subgroupOf hyp.D) ≠ 1 := by
    intro hc
    have hmm := (QuotientGroup.eq_one_iff (⟨d, hdD⟩ : ↥hyp.D)).mp hc
    rw [Subgroup.mem_subgroupOf] at hmm
    exact hdK hmm
  obtain ⟨z, hz, hzd⟩ : (QuotientGroup.mk (⟨d, hdD⟩ : ↥hyp.D)) ∈ Ψ '' S := by
    rw [heq]
    exact ⟨Set.mem_univ _, hdne⟩
  refine ⟨z, hz.1, B z, hBQ0 z hz, A z, hAD z hz, ?_, hAeq z hz⟩
  have hmm := QuotientGroup.eq.mp hzd
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hA'val z hz] at hmm
  exact hmm

/-- **Peterfalvi Part II, Ch. IV §2, step (9)** (p. 124–125):

> For all `i`, there are elements `ω'_i ∈ Q − Q₀` and `y_i ∈ Q₀^#` such that `ω̄'_i` is
> in the orbit of `ω̄_i` under `KW` and `f(ω'_i) = (ω'_i y_i)^ζ`.

Here `ζ` is any nontrivial element of `W` (the book takes a generator, nontrivial by
(C2)).  The witness for the coset `ζK` exists by `exists_witness_coset_eq`, its
`K`-part has a square root by `exists_sq_eq_of_mem_K`, and `f_conj_collapse` turns the
exponent into `ζ`. -/
theorem stepNine {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {f g h : G → G} (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hVW : hyp.V = hyp.W) (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hKcard : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    {ζ : G} (hζW : ζ ∈ hyp.W) (hζ1 : ζ ≠ 1) :
    ∃ ω' ∈ hyp.Q, ω' ∉ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, y ≠ 1 ∧
      f ω' = ζ⁻¹ * (ω' * y) * ζ := by
  have hWD : hyp.W ≤ hyp.D := le_trans inf_le_left hyp.V_le_D
  have hζD : ζ ∈ hyp.D := hWD hζW
  have hζK : ζ ∉ hyp.K := by
    intro hc
    refine hζ1 ?_
    have : ζ ∈ hyp.K ⊓ hyp.W := ⟨hc, hζW⟩
    rwa [hyp.K_inf_W_eq_bot, Subgroup.mem_bot] at this
  obtain ⟨z, hzQ0, b, hbQ0, a, haD, haζ, heq⟩ :=
    hyp.exists_witness_coset_eq M hZ H hC2 hVW hm hQ0card hinj hKcard hWdvd
      hωQ hωQ0 hζD hζK
  -- `a = k ζ` with `k ∈ K`, using that `W` centralizes `K`
  have hkK : ζ⁻¹ * a ∈ hyp.K := by
    have := hyp.K.inv_mem haζ
    simpa using this
  obtain ⟨c, hcK, hcsq⟩ := hyp.exists_sq_eq_of_mem_K hkK
  have hcKSet : c ∈ hyp.KSet := by
    have hh : c ∈ (hyp.K : Set G) := hcK
    rwa [hyp.coe_K] at hh
  have haeq : a = c ^ 2 * ζ := by
    rw [hcsq]
    have hcm : ζ * (ζ⁻¹ * a) = a := by group
    rw [← hyp.commute_of_mem_W_of_mem_K hζW hkK] at hcm
    exact hcm.symm
  obtain ⟨hωzQ, hωzQ0⟩ := hyp.mul_mem_sdiff_Q0 hωQ hωQ0 hzQ0
  have hωz1 : ω * z ≠ 1 := fun hc => hωzQ0 (hc ▸ hyp.Q0.one_mem)
  rw [haeq] at heq
  have hcoll := hyp.f_conj_collapse H hωzQ hωz1 hzQ0 hcKSet hζW heq
  -- package the result
  have hcD : c ∈ hyp.D := hyp.K_le_D hcK
  have hω'Q : c⁻¹ * (ω * z) * c ∈ hyp.Q := hyp.rankOneSetup.DQ c hcD _ hωzQ
  have hω'Q0 : c⁻¹ * (ω * z) * c ∉ hyp.Q0 := by
    intro hcc
    refine hωzQ0 ?_
    have e : ω * z = c * (c⁻¹ * (ω * z) * c) * c⁻¹ := by group
    rw [e]
    exact hyp.conj_mem_Q0_of_mem_H (hyp.D_le_H hcD) hcc
  have hyQ0 : c⁻¹ * (z * b) * c ∈ hyp.Q0 := by
    have := hyp.conj_mem_Q0_of_mem_H (hyp.H.inv_mem (hyp.D_le_H hcD))
      (hyp.Q0.mul_mem hzQ0 hbQ0)
    rwa [inv_inv] at this
  refine ⟨_, hω'Q, hω'Q0, _, hyQ0, ?_, hcoll⟩
  exact hyp.ne_one_of_f_eq_conj H hC2 hω'Q hω'Q0 hζD hcoll

/-- **Step (15)'s conclusion, group side** (Peterfalvi Part II, p. 126).

By (14) the last term of the sequence is `d_{m₁} = ζ^{m₁} (c_{m₁}/α)^{2τ}`, and step (15)
identifies it with `ζ⁻¹`; rearranged, that says `κ · ζ^{m₁+1} = 1` where `κ ∈ K` is the
image of `(c_{m₁}/α)^{2τ}` and `ζ^{m₁+1} ∈ W`.  Since `K ∩ W = 1`, both factors are
trivial, and `ζ` having order `m` with `m₁ + 1 ≤ m` pins the length:

* `m₁ + 1 = m`, the book's `m₁ = m − 1`;
* `κ = 1`, which transported back through `K ↪ E^×` is the book's `c_{m₁} = α`
  (`eq_one_of_frobNormEquiv_symm_sq_eq_one`). -/
theorem stepFifteen_length {ζ κ : G} {m m₁ : ℕ} (hζ : ζ ∈ hyp.W) (hκK : κ ∈ hyp.K)
    (hprod : κ * ζ ^ (m₁ + 1) = 1) (hord : orderOf ζ = m) (hle : m₁ + 1 ≤ m) :
    m₁ + 1 = m ∧ κ = 1 := by
  obtain ⟨hκ1, hζ1⟩ :=
    hyp.eq_one_of_mul_eq_one_of_mem_K_of_mem_W hκK (hyp.W.pow_mem hζ _) hprod
  exact ⟨eq_of_pow_succ_eq_one_of_le hord hζ1 hle, hκ1⟩

/-- **Step (15)'s other conclusion**: `c_{m₁} = α` (Peterfalvi Part II, p. 126).

`stepFifteen_length` gives `κ = 1` for the `K`-part of `d_{m₁} = ζ⁻¹`.  Transporting that
across `μ` — a homomorphism, and `kActor 1 = 1` — makes the scalar `1`, so the square
`(c_{m₁}/α)^{2τ}` is `1` and `eq_one_of_frobNormEquiv_symm_sq_eq_one` reads off
`c_{m₁}/α = 1`.

The identification of `μ(κ)` with that square is passed in: it is exactly what the closed
form (14) asserts once `d_{m₁}` is written inside `KW`. -/
theorem eq_one_of_kPart_eq_one {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hchar : (2 : M.E) = 0) {θ : M.E ≃+* M.E} (hodd : Odd (orderOf θ))
    {κ : G} (hκK : κ ∈ hyp.K) (hκ1 : κ = 1) {u : M.E}
    (hid : ((M.mu (hyp.kActor hκK, 1) : M.Eˣ) : M.E)
      = ((frobNormEquiv hchar hodd).symm u) ^ 2) : u = 1 := by
  subst hκ1
  rw [hyp.kActor_one hκK,
    show ((1 : ↥hyp.actualKActor), (1 : ↥hyp.W)) = 1 from rfl, map_one,
    Units.val_one] at hid
  exact eq_one_of_frobNormEquiv_symm_sq_eq_one hchar hodd hid.symm

/-! ## Freeness of the `D`-action on `(Q/Q₀)^#`

Steps (15), (18) and (20) all need the same fact: an element of `D` fixing the class
of some `ω ∈ Q − Q₀` modulo `Q₀` is trivial.  For `c ∈ K` this is group-theoretic —
`eq_one_of_conj_eq_mul_Q0` in `PSU3PairComparison` derives it from the fixed-point
freeness of `K` on `Q` — but the elements of `W` centralize `Q₀`, so that argument
cannot reach the whole of `D`.  The model does: `D = KW` acts on `Q/Q₀ ≅ E` by the
scalars `μ(k, v)`, and `μ` is injective.
-/

/-- Conjugation by `k v` (`k ∈ K`, `v ∈ W`) is the action of the actor pair
`(kActor k, v)` on `Q`.

Both `conjQByK k` and `conjQByW v` are literally `x ↦ k x k⁻¹` and `x ↦ v x v⁻¹`, and
`conjQHom` is their (commuting) product, so this is the definitional unfolding.  It is
the converse direction of `exists_mem_D_conjQHom`, which starts from the actor pair;
here the group element is given first, as `exists_mem_K_mem_W_mul` produces it. -/
theorem conjQHom_kActor_apply_val {k v : G} (hk : k ∈ hyp.K) (hv : v ∈ hyp.W)
    (x : ↥hyp.Q) :
    ((hyp.conjQHom (hyp.kActor hk, ⟨v, hv⟩) x : ↥hyp.Q) : G)
      = (k * v) * (x : G) * (k * v)⁻¹ := by
  have hval : ((hyp.conjQHom (hyp.kActor hk, ⟨v, hv⟩) x : ↥hyp.Q) : G)
      = k * (v * (x : G) * v⁻¹) * k⁻¹ := rfl
  rw [hval]
  group

/-- The coordinate of `Q ⧸ Z(Q) ≅ E` is additive along products in `Q`. -/
theorem coord_mk_mul {m : ℕ} (M : hyp.QuotientFieldModel m) {x y : G}
    (hxQ : x ∈ hyp.Q) (hyQ : y ∈ hyp.Q) (hxyQ : x * y ∈ hyp.Q) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨x * y, hxyQ⟩ : ↥hyp.Q)))
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q)))
        + M.coord (Additive.ofMul (QuotientGroup.mk (⟨y, hyQ⟩ : ↥hyp.Q))) := by
  have hmul : (⟨x * y, hxyQ⟩ : ↥hyp.Q) = (⟨x, hxQ⟩ : ↥hyp.Q) * ⟨y, hyQ⟩ := rfl
  rw [hmul, QuotientGroup.mk_mul, ofMul_mul, map_add]

/-- Elements of `Q₀` have coordinate `0`: they are exactly the kernel of `Q → Q ⧸ Z(Q)`.
This is the converse of `coord_ne_zero_of_not_mem_Q0`. -/
theorem coord_mk_eq_zero_of_mem_Q0 {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z : G} (hzQ0 : z ∈ hyp.Q0) (hzQ : z ∈ hyp.Q) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))) = 0 := by
  have hmem : (⟨z, hzQ⟩ : ↥hyp.Q) ∈ Subgroup.center hyp.Q := by
    rw [hZ, Subgroup.mem_subgroupOf]
    exact hzQ0
  have hone : (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q) :
      ↥hyp.Q ⧸ Subgroup.center hyp.Q) = 1 := QuotientGroup.eq_one_iff _ |>.mpr hmem
  rw [hone]
  exact map_zero M.coord

/-- **The `D`-action on `Q/Q₀` in coordinates**: conjugation by `c = κ v` (`κ ∈ K`,
`v ∈ W`) multiplies the coordinate of `Q ⧸ Z(Q) ≅ E` by the scalar `μ(κ, v)`.

This is the `Q/Q₀`-level counterpart of `centerCoord_conj` (which does the same on `Q₀`):
`conjQHom_kActor_apply_val` identifies the actor pair's action with conjugation by `κ v`,
`quotientKWHom_mk` pushes it to the quotient, and `coord_act` reads it as a scalar.

Chapter IV §3 runs on it: its stage (2) turns the group identity of stage (1) into the
linear equation `(a² + ζ⁻¹) · f(ω s^a)‾ = ω̄` in `E`. -/
theorem coord_conj_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    {κ v : G} (hκ : κ ∈ hyp.K) (hv : v ∈ hyp.W)
    {x w : G} (hxQ : x ∈ hyp.Q) (hwQ : w ∈ hyp.Q)
    (hval : (κ * v) * x * (κ * v)⁻¹ = w) :
    M.coord (Additive.ofMul (QuotientGroup.mk (⟨w, hwQ⟩ : ↥hyp.Q)))
      = ((M.mu (hyp.kActor hκ, ⟨v, hv⟩) : M.Eˣ) : M.E)
        * M.coord (Additive.ofMul (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q))) := by
  have hact : hyp.conjQHom (hyp.kActor hκ, ⟨v, hv⟩) ⟨x, hxQ⟩ = (⟨w, hwQ⟩ : ↥hyp.Q) := by
    apply Subtype.ext
    rw [hyp.conjQHom_kActor_apply_val hκ hv ⟨x, hxQ⟩]
    exact hval
  have hq := M.coord_act (hyp.kActor hκ, ⟨v, hv⟩)
    (QuotientGroup.mk (⟨x, hxQ⟩ : ↥hyp.Q))
  rw [hyp.quotientKWHom_mk, hact] at hq
  exact hq

/-- **`D` acts freely on `(Q/Q₀)^#`** (Peterfalvi Part II, Ch. IV §2, used at pp. 126–128).

If `c ∈ D` fixes the class of `ω ∈ Q − Q₀` modulo `Q₀` — i.e. `ω^c = ω y` for some
`y ∈ Q₀` — then `c = 1`.

Under Chapter IV's standing hypothesis `V = W` every `c ∈ D` factors as `k v` with
`k ∈ K` and `v ∈ W` (`exists_mem_K_mem_W_mul`), and conjugation by it induces the
action of the actor pair `(kActor k, v)` on `Q/Z(Q)`.  In the standard model of
Ch. III §3 that action is multiplication by the scalar `μ(k, v)` on `E`, and the
coordinate of `ω` is a *unit* because `ω ∉ Q₀ = Z(Q)`; so the fixed-point equation
reads `μ(k, v) · α = α` with `α ≠ 0`, forcing `μ(k, v) = 1`.  Injectivity of `μ`
then makes the pair trivial, and `conjQByK` is faithful, so `k = v = 1`.

The `K`-part alone is `eq_one_of_conj_eq_mul_Q0`, proved without the model; the model
is what covers the `W`-part, whose elements centralize `Q₀` and hence are invisible to
the fixed-point-freeness argument used there.

This is the fact behind step (15)'s "the `u_i` exhaust the orbit", step (18)'s
`d_{m−1} = ζ⁻¹`, and the general form of step (20)'s (∗∗∗). -/
theorem eq_one_of_conj_eq_mul_Q0_of_decomp {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    {ω c y k v : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (hk : k ∈ hyp.K) (hv : v ∈ hyp.W) (hkv : c⁻¹ = k * v)
    (hy : y ∈ hyp.Q0) (hconj : c⁻¹ * ω * c = ω * y) : c = 1 := by
  set kv : ↥hyp.actualKActor × ↥hyp.W := (hyp.kActor hk, ⟨v, hv⟩) with hkvdef
  -- the actor pair acts as conjugation by `c⁻¹ = k v`
  have hact : ∀ x : ↥hyp.Q, ((hyp.conjQHom kv x : ↥hyp.Q) : G) = c⁻¹ * (x : G) * c := by
    intro x
    rw [hkvdef, hyp.conjQHom_kActor_apply_val hk hv x, ← hkv, inv_inv]
  -- hence it fixes the class of `ω` in `Q ⧸ Z(Q)`
  have hfix : hyp.quotientKWHom kv (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))
      = QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q) := by
    rw [hyp.quotientKWHom_mk]
    refine QuotientGroup.eq.mpr ?_
    rw [hZ, Subgroup.mem_subgroupOf]
    have hval : (((hyp.conjQHom kv ⟨ω, hωQ⟩ : ↥hyp.Q)⁻¹ * ⟨ω, hωQ⟩ : ↥hyp.Q) : G)
        = y⁻¹ := by
      change ((hyp.conjQHom kv ⟨ω, hωQ⟩ : ↥hyp.Q) : G)⁻¹ * ω = y⁻¹
      rw [hact ⟨ω, hωQ⟩, hconj]
      group
    rw [hval]
    exact hyp.Q0.inv_mem hy
  -- in coordinates: `μ(kv) · α = α` with `α ≠ 0`
  have hcoord := M.coord_act kv (QuotientGroup.mk (⟨ω, hωQ⟩ : ↥hyp.Q))
  rw [hfix] at hcoord
  have hne := hyp.coord_ne_zero_of_not_mem_Q0 M hZ hωQ hωQ0
  have hmu1 : M.mu kv = 1 := by
    apply Units.ext
    rw [Units.val_one]
    refine mul_right_cancel₀ hne ?_
    rw [one_mul]
    exact hcoord.symm
  -- injectivity of `μ` and faithfulness of `conjQByK` kill both factors
  have hkv1 : kv = 1 := hmu (by rw [hmu1, map_one])
  have hv1 : v = 1 := congrArg Subtype.val (congrArg Prod.snd hkv1)
  have hk1 : k = 1 := by
    have hactor : hyp.conjQByK (⟨k, hk⟩ : ↥hyp.K) = 1 :=
      congrArg Subtype.val (congrArg Prod.fst hkv1)
    have : (⟨k, hk⟩ : ↥hyp.K) = 1 := hyp.conjQByK_injective (by rw [hactor, map_one])
    exact congrArg Subtype.val this
  have : c⁻¹ = 1 := by rw [hkv, hk1, hv1, mul_one]
  rw [← inv_inv c, this, inv_one]

/-- **`D` acts fixed-point-freely on `(Q/Q₀)^#`** (the `V = W` case).

`exists_mem_K_mem_W_mul` decomposes `c⁻¹` as `k v`; the content is
`eq_one_of_conj_eq_mul_Q0_of_decomp`. -/
theorem eq_one_of_conj_eq_mul_Q0_of_mem_D {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu) (hVW : hyp.V = hyp.W)
    {ω c y : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hcD : c ∈ hyp.D)
    (hy : y ∈ hyp.Q0) (hconj : c⁻¹ * ω * c = ω * y) : c = 1 := by
  obtain ⟨k, hk, v, hv, hkv⟩ := hyp.exists_mem_K_mem_W_mul hVW (hyp.D.inv_mem hcD)
  exact hyp.eq_one_of_conj_eq_mul_Q0_of_decomp M hZ hmu hωQ hωQ0 hk hv hkv hy hconj

/-- **`W` acts fixed-point-freely on `(Q/Q₀)^#`** — no `V = W` needed.

An element of `W` is already its own `K W`-decomposition (`k = 1`), so
`eq_one_of_conj_eq_mul_Q0_of_decomp` applies directly.  Ch. IV §4 works in the case
`V ≠ W` (p. 132), where the `D`-version above is unavailable but this one still holds;
it is what gives `P ∩ W = 1` there, and what forces `P Z(U) ∩ W = 1` in step (1). -/
theorem eq_one_of_conj_eq_mul_Q0_of_mem_W {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (hmu : Function.Injective M.mu)
    {ω c y : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) (hcW : c ∈ hyp.W)
    (hy : y ∈ hyp.Q0) (hconj : c⁻¹ * ω * c = ω * y) : c = 1 :=
  hyp.eq_one_of_conj_eq_mul_Q0_of_decomp M hZ hmu hωQ hωQ0 hyp.K.one_mem
    (hyp.W.inv_mem hcW) (one_mul _).symm hy hconj

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
