/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.PSU3OrbitCount

/-!
# Peterfalvi Part II, Ch. IV §2, step (8), without `V = W`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272, 2000),
Part II, Ch. IV §2 (7)–(8), p. 124.

Step (8) counts, for each `KW`-orbit on `(Q/Q₀)^#`, how many `x ∈ Q₀` send `f(ω x)` into
it, and the squeeze `q = Σ mᵢ ≤ n m − 1 = q` forces every bound to be an equality.  The
book's bound is `mᵢ ≤ m = |W|`, and the counting only closes with that constant, since
`n m = q + 1` exactly.

`PSU3OrbitCount` proves the weaker `mᵢ ≤ |V|`: the conjugator produced by the fibre
translation is only recorded as an element of `D`, and `x ↦ a K` injects into `D/K`, of
size `|D : K| = |V|`.  Chapter IV §3 then had to carry `V = W` throughout — which is
exactly the hypothesis §4 does **not** have, and §3's Corollary 1 is what §4 hands its
conclusion to.

The fix is to keep the information the orbit already carries: the fibre condition is
membership in a `K W`-orbit, so the conjugator is `k v` with `k ∈ K` and `v ∈ W`, and
`x ↦ v` injects into `W` because two conjugators with the same `W`-part differ by an
element of `K` (they commute, `W = C_V(K)`), which is step (7).  No hypothesis on `V`
is used.

## Main results

* `Hypothesis.K_inf_W_eq_bot` — `K ∩ W = 1`.
* `Hypothesis.exists_mem_K_mem_W_conjQHom` — the conjugator realizing `conjQHom kv` is
  `k v` with `k ∈ K`, `v ∈ W`.
* `Hypothesis.exists_conj_KW_of_coset_eq` — the fibre translation, keeping `k` and `v`.
* `Hypothesis.ncard_le_card_W_of_f_eq_conj`,
  `Hypothesis.ncard_le_card_W_sub_one_of_f_eq_conj_self` — the book's bounds `mᵢ ≤ m`
  and `m₁ ≤ m − 1`.
* `Hypothesis.stepEight_of_KW`, `Hypothesis.exists_mem_Q0_orbitOfF_eq_of_KW` — step (8)
  and its consequence, with `V = W` removed.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory.RankOneBNPair

namespace Hypothesis

variable {G Ω : Type*} [Group G] [MulAction G Ω] [Finite G]
  (hyp : Hypothesis G Ω) {f g h : G → G}

include hyp

section /- Ch. IV §2 (7): the conjugator lies in `K W` (p. 124) -/

/-- `W ≤ D`, through `W ≤ V ≤ D`. -/
theorem W_le_D : hyp.W ≤ hyp.D := le_trans hyp.W_le_V hyp.V_le_D

/-- An element of `W` is trivial as soon as `k v ∈ K` for some `k ∈ K`. -/
theorem eq_one_of_mul_mem_K {k v : G} (hk : k ∈ hyp.K) (hv : v ∈ hyp.W)
    (hkv : k * v ∈ hyp.K) : v = 1 := by
  have hvK : v ∈ hyp.K := by
    have : k⁻¹ * (k * v) ∈ hyp.K := hyp.K.mul_mem (hyp.K.inv_mem hk) hkv
    simpa using this
  have : v ∈ hyp.K ⊓ hyp.W := ⟨hvK, hv⟩
  rwa [hyp.K_inf_W_eq_bot, Subgroup.mem_bot] at this

/-- **`conjQHom kv` is conjugation by `k v` with `k ∈ K` and `v ∈ W`.**

This is `exists_mem_D_conjQHom` with the two factors kept apart: `actualKActor` is the
range of `conjQByK`, so the first is honestly an element of `K`, and the second is the
`W`-component of the pair. -/
theorem exists_mem_K_mem_W_conjQHom (kv : ↥hyp.actualKActor × ↥hyp.W) :
    ∃ k ∈ hyp.K, ∃ v ∈ hyp.W, ∀ x : ↥hyp.Q,
      ((hyp.conjQHom kv x : ↥hyp.Q) : G) = (k * v) * (x : G) * (k * v)⁻¹ := by
  obtain ⟨k, hk⟩ := (MonoidHom.mem_range).mp kv.1.2
  refine ⟨(k : G), k.2, (kv.2 : G), kv.2.2, fun x => ?_⟩
  rw [hyp.conjQHom_apply, MulAut.mul_apply]
  simp only [Subgroup.coe_subtype]
  rw [← hk]
  change (k : G) * ((kv.2 : G) * (x : G) * (kv.2 : G)⁻¹) * (k : G)⁻¹ = _
  group

/-- The `Q₀`-shuffle of `exists_conj_mul_Q0_iff`, for one fixed conjugator. -/
theorem exists_conj_mul_Q0_iff_of_mem_H {ω' z a : G} (haH : a ∈ hyp.H) :
    (∃ w ∈ hyp.Q0, z = a⁻¹ * ω' * a * w) ↔ ∃ y ∈ hyp.Q0, z = a⁻¹ * (ω' * y) * a := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨a * w * a⁻¹, hyp.conj_mem_Q0_of_mem_H haH hw, by group⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨a⁻¹ * y * a, ?_, by group⟩
    have := hyp.conj_mem_Q0_of_mem_H (hyp.H.inv_mem haH) hy
    rwa [inv_inv] at this

/-- **The fibre translation, keeping the `K W`-presentation of the conjugator**
(Peterfalvi Part II, Ch. IV §2 (7), p. 124).

Same statement as `exists_conj_of_coset_eq`, except that the conjugator is delivered as
`k v` with `k ∈ K` and `v ∈ W` rather than as an opaque element of `D`.  That is the
information the book's bound `mᵢ ≤ |W|` runs on. -/
theorem exists_conj_KW_of_coset_eq {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    {z z' : G} (hzQ : z ∈ hyp.Q) (hz'Q : z' ∈ hyp.Q) {u u' : M.Eˣ}
    (hu : (u : M.E) = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z, hzQ⟩ : ↥hyp.Q))))
    (hu' : (u' : M.E)
      = M.coord (Additive.ofMul (QuotientGroup.mk (⟨z', hz'Q⟩ : ↥hyp.Q))))
    (heq : (QuotientGroup.mk u : M.Eˣ ⧸ MonoidHom.range M.mu) = QuotientGroup.mk u') :
    ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
      z' = (k * v)⁻¹ * (z * y) * (k * v) := by
  obtain ⟨kv, hkv⟩ :=
    hyp.exists_conjQHom_quotient_eq_of_coset_eq M hzQ hz'Q hu hu' heq
  obtain ⟨k, hk, v, hv, hconj⟩ := hyp.exists_mem_K_mem_W_conjQHom kv
  obtain ⟨w, hw, hzw⟩ := hyp.exists_mem_Q0_mul_of_quotient_eq hZ
    (hyp.conjQHom kv ⟨z, hzQ⟩).2 hz'Q hkv.symm
  rw [hconj ⟨z, hzQ⟩] at hzw
  -- the conjugator we want is `(k v)⁻¹ = k⁻¹ v⁻¹`, since `K` and `W` commute
  have hcomm : k⁻¹ * v⁻¹ = (k * v)⁻¹ := by
    rw [mul_inv_rev]
    exact hyp.commute_of_mem_W_of_mem_K (hyp.W.inv_mem hv) (hyp.K.inv_mem hk)
  have haH : (k * v)⁻¹ ∈ hyp.H :=
    hyp.H.inv_mem (hyp.H.mul_mem (hyp.D_le_H (hyp.K_le_D hk)) (hyp.D_le_H (hyp.W_le_D hv)))
  obtain ⟨y, hy, hzy⟩ :=
    (hyp.exists_conj_mul_Q0_iff_of_mem_H (ω' := z) (z := z') haH).mp
      ⟨w, hw, by rw [hzw]; group⟩
  refine ⟨y, hy, k⁻¹, hyp.K.inv_mem hk, v⁻¹, hyp.W.inv_mem hv, ?_⟩
  rw [hcomm, hzy]

end

section /- Ch. IV §2 (8): the bounds `mᵢ ≤ m` and `m₁ ≤ m − 1` (p. 124) -/

/-- **The book's bound behind step (8)**: for fixed `ω, ω' ∈ Q − Q₀`, at most
`m = |W|` elements `x ∈ Q₀` satisfy `f(ω x) = (ω' y)^{k v}` with `k ∈ K` and `v ∈ W`.

The map `x ↦ v` is injective: if two witnesses share their `W`-part `v`, then
`(k₁ v)⁻¹ (k₂ v) = k₁⁻¹ k₂ ∈ K` — `W` centralizes `K` — and step (7)
(`eq_of_inv_mul_mem_K`) forces the two `x` to agree. -/
theorem ncard_le_card_W_of_f_eq_conj (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω ω' : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {x : G | x ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
        f (ω * x) = (k * v)⁻¹ * (ω' * y) * (k * v)}.ncard ≤ Nat.card ↥hyp.W := by
  classical
  set S : Set G := {x : G | x ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
    f (ω * x) = (k * v)⁻¹ * (ω' * y) * (k * v)} with hSdef
  have key : ∀ x ∈ S, ∃ v, v ∈ hyp.W ∧ ∃ k, k ∈ hyp.K ∧ ∃ b, b ∈ hyp.Q0 ∧
      f (ω * x) = (k * v)⁻¹ * (ω' * b) * (k * v) := by
    rintro x ⟨-, b, hb, k, hk, v, hv, heq⟩
    exact ⟨v, hv, k, hk, b, hb, heq⟩
  choose! Vf hVfW Kf hKfK Bf hBfQ0 hAeq using key
  set V' : G → ↥hyp.W := fun x => if hx : Vf x ∈ hyp.W then ⟨Vf x, hx⟩ else 1 with hV'def
  have hV'val : ∀ x ∈ S, (V' x : G) = Vf x := by
    intro x hx
    simp only [hV'def, dif_pos (hVfW x hx)]
  have hinj : Set.InjOn V' S := by
    intro x₁ hx₁ x₂ hx₂ hxy
    have hveq : Vf x₁ = Vf x₂ := by
      rw [← hV'val x₁ hx₁, ← hV'val x₂ hx₂, hxy]
    -- the two conjugators differ by `k₁⁻¹ k₂ ∈ K`
    have hmem : (Kf x₁ * Vf x₁)⁻¹ * (Kf x₂ * Vf x₂) ∈ hyp.K := by
      have hc : (Kf x₁ * Vf x₁)⁻¹ * (Kf x₂ * Vf x₂)
          = (Vf x₁)⁻¹ * ((Kf x₁)⁻¹ * Kf x₂) * Vf x₁ := by
        rw [hveq]; group
      have hK' : (Kf x₁)⁻¹ * Kf x₂ ∈ hyp.K :=
        hyp.K.mul_mem (hyp.K.inv_mem (hKfK x₁ hx₁)) (hKfK x₂ hx₂)
      have hcm := hyp.commute_of_mem_W_of_mem_K (hVfW x₁ hx₁) hK'
      have hsimp : (Vf x₁)⁻¹ * ((Kf x₁)⁻¹ * Kf x₂) * Vf x₁ = (Kf x₁)⁻¹ * Kf x₂ := by
        rw [mul_assoc, hcm]
        group
      rw [hc, hsimp]
      exact hK'
    refine hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hx₁.1 hx₂.1
      (hBfQ0 x₁ hx₁) (hBfQ0 x₂ hx₂)
      (hyp.D.mul_mem (hyp.K_le_D (hKfK x₁ hx₁)) (hyp.W_le_D (hVfW x₁ hx₁)))
      (hyp.D.mul_mem (hyp.K_le_D (hKfK x₂ hx₂)) (hyp.W_le_D (hVfW x₂ hx₂)))
      (hAeq x₁ hx₁) (hAeq x₂ hx₂) hmem
  have hbound := Set.ncard_le_ncard_of_injOn V'
    (fun _ _ => Set.mem_univ _) hinj Set.finite_univ
  rwa [Set.ncard_univ] at hbound

/-- **The sharpening for `i = 1`** (Peterfalvi Part II, Ch. IV §2 (8), p. 124): at most
`m − 1 = |W| − 1` elements `x ∈ Q₀` satisfy `f(ω x) = (ω y)^{k v}`.

`not_mem_K_of_f_eq_conj_self` says the conjugator never lies in `K`, and `k v ∈ K` would
force `v = 1` since `K ∩ W = 1`; so the injection of the previous bound misses the
identity of `W`. -/
theorem ncard_le_card_W_sub_one_of_f_eq_conj_self
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {x : G | x ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
        f (ω * x) = (k * v)⁻¹ * (ω * y) * (k * v)}.ncard
      ≤ Nat.card ↥hyp.W - 1 := by
  classical
  set S : Set G := {x : G | x ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
    f (ω * x) = (k * v)⁻¹ * (ω * y) * (k * v)} with hSdef
  have key : ∀ x ∈ S, ∃ v, v ∈ hyp.W ∧ ∃ k, k ∈ hyp.K ∧ ∃ b, b ∈ hyp.Q0 ∧
      f (ω * x) = (k * v)⁻¹ * (ω * b) * (k * v) := by
    rintro x ⟨-, b, hb, k, hk, v, hv, heq⟩
    exact ⟨v, hv, k, hk, b, hb, heq⟩
  choose! Vf hVfW Kf hKfK Bf hBfQ0 hAeq using key
  set V' : G → ↥hyp.W := fun x => if hx : Vf x ∈ hyp.W then ⟨Vf x, hx⟩ else 1 with hV'def
  have hV'val : ∀ x ∈ S, (V' x : G) = Vf x := by
    intro x hx
    simp only [hV'def, dif_pos (hVfW x hx)]
  have hinj : Set.InjOn V' S := by
    intro x₁ hx₁ x₂ hx₂ hxy
    have hveq : Vf x₁ = Vf x₂ := by
      rw [← hV'val x₁ hx₁, ← hV'val x₂ hx₂, hxy]
    have hmem : (Kf x₁ * Vf x₁)⁻¹ * (Kf x₂ * Vf x₂) ∈ hyp.K := by
      have hc : (Kf x₁ * Vf x₁)⁻¹ * (Kf x₂ * Vf x₂)
          = (Vf x₁)⁻¹ * ((Kf x₁)⁻¹ * Kf x₂) * Vf x₁ := by
        rw [hveq]; group
      have hK' : (Kf x₁)⁻¹ * Kf x₂ ∈ hyp.K :=
        hyp.K.mul_mem (hyp.K.inv_mem (hKfK x₁ hx₁)) (hKfK x₂ hx₂)
      have hcm := hyp.commute_of_mem_W_of_mem_K (hVfW x₁ hx₁) hK'
      have hsimp : (Vf x₁)⁻¹ * ((Kf x₁)⁻¹ * Kf x₂) * Vf x₁ = (Kf x₁)⁻¹ * Kf x₂ := by
        rw [mul_assoc, hcm]
        group
      rw [hc, hsimp]
      exact hK'
    refine hyp.eq_of_inv_mul_mem_K H hC2 hωQ hωQ0 hx₁.1 hx₂.1
      (hBfQ0 x₁ hx₁) (hBfQ0 x₂ hx₂)
      (hyp.D.mul_mem (hyp.K_le_D (hKfK x₁ hx₁)) (hyp.W_le_D (hVfW x₁ hx₁)))
      (hyp.D.mul_mem (hyp.K_le_D (hKfK x₂ hx₂)) (hyp.W_le_D (hVfW x₂ hx₂)))
      (hAeq x₁ hx₁) (hAeq x₂ hx₂) hmem
  have hmaps : ∀ x ∈ S, V' x ∈ (Set.univ \ {1} : Set ↥hyp.W) := by
    intro x hx
    refine ⟨Set.mem_univ _, fun hc => ?_⟩
    have hv1 : Vf x = 1 := by
      rw [← hV'val x hx, hc]
      rfl
    have hmemK : Kf x * Vf x ∈ hyp.K := by
      rw [hv1, mul_one]
      exact hKfK x hx
    exact hyp.not_mem_K_of_f_eq_conj_self H hC2 hωQ hωQ0 hx.1 (hBfQ0 x hx)
      (hyp.D.mul_mem (hyp.K_le_D (hKfK x hx)) (hyp.W_le_D (hVfW x hx)))
      (hAeq x hx) hmemK
  have hbound := Set.ncard_le_ncard_of_injOn V' hmaps hinj (Set.toFinite _)
  have hdiff : (Set.univ \ {1} : Set ↥hyp.W).ncard = Nat.card ↥hyp.W - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ]
  rwa [hdiff] at hbound

end

section /- Ch. IV §2 (8): the count itself, with `V = W` removed (p. 124) -/

/-- **Each fibre of `orbitOfF` has at most `m = |W|` elements** — the book's `mᵢ ≤ m`,
with no hypothesis relating `V` and `W`. -/
theorem ncard_fiber_orbitOfF_le_W {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (c : M.Eˣ ⧸ (MonoidHom.range M.mu)) :
    {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
      ≤ Nat.card ↥hyp.W := by
  classical
  rcases Set.eq_empty_or_nonempty
      {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c} with he | ⟨x₀, hx₀⟩
  · rw [he, Set.ncard_empty]
    exact Nat.zero_le _
  · have hsub : ((↑) : ↥hyp.Q0 → G) ''
        {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}
        ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
            f (ω * z) = (k * v)⁻¹ * (f (ω * (x₀ : G)) * y) * (k * v)} := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have hcoset :
          (QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x₀) :
            M.Eˣ ⧸ MonoidHom.range M.mu)
            = QuotientGroup.mk (hyp.fUnit M hZ H hC2 hωQ hωQ0 x) :=
        hx₀.trans hx.symm
      exact hyp.exists_conj_KW_of_coset_eq M hZ
        (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x₀) (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x)
        rfl rfl hcoset
    calc {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard
        = (((↑) : ↥hyp.Q0 → G) ''
            {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}).ncard :=
          (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
            f (ω * z) = (k * v)⁻¹ * (f (ω * (x₀ : G)) * y) * (k * v)}.ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ Nat.card ↥hyp.W := hyp.ncard_le_card_W_of_f_eq_conj H hC2 hωQ hωQ0

/-- **The distinguished fibre has at most `m − 1` elements** — the book's `m₁ ≤ m − 1`,
with no hypothesis relating `V` and `W`. -/
theorem ncard_fiber_orbitOfF_base_le_W {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0) :
    {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
      ≤ Nat.card ↥hyp.W - 1 := by
  classical
  have hsub : ((↑) : ↥hyp.Q0 → G) ''
      {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
        = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}
      ⊆ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
          f (ω * z) = (k * v)⁻¹ * (ω * y) * (k * v)} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    exact hyp.exists_conj_KW_of_coset_eq M hZ hωQ
      (hyp.f_mul_mem_Q H hC2 hωQ hωQ0 x) rfl rfl hx.symm
  calc {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
          = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}.ncard
      = (((↑) : ↥hyp.Q0 → G) ''
          {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x
            = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)}).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ {z : G | z ∈ hyp.Q0 ∧ ∃ y ∈ hyp.Q0, ∃ k ∈ hyp.K, ∃ v ∈ hyp.W,
          f (ω * z) = (k * v)⁻¹ * (ω * y) * (k * v)}.ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ Nat.card ↥hyp.W - 1 :=
        hyp.ncard_le_card_W_sub_one_of_f_eq_conj_self H hC2 hωQ hωQ0

/-- **Step (8)** (Peterfalvi Part II, Ch. IV §2, p. 124), with `V = W` removed:
every fibre of `orbitOfF` has exactly `m = |W|` elements, except the distinguished one,
which has `m − 1`.

`q = Σ mᵢ ≤ n m − 1 = q` with `n m = q + 1`, so both bounds are equalities. -/
theorem stepEight_of_KW {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
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
  exact card_fiber_eq_of_card_eq (hyp.orbitOfF M hZ H hC2 hωQ hωQ0) Nat.card_pos _
    (fun c => hyp.ncard_fiber_orbitOfF_le_W M hZ H hC2 hωQ hωQ0 c)
    (hyp.ncard_fiber_orbitOfF_base_le_W M hZ H hC2 hωQ hωQ0) hcard

/-- **Every `K W`-orbit is attained on the fibre `ρ Q₀`** (Peterfalvi Part II, Ch. IV
§3 (5), p. 131), with `V = W` removed — this is what stage (5)'s second case uses. -/
theorem exists_mem_Q0_orbitOfF_eq_of_KW {m : ℕ} (M : hyp.QuotientFieldModel m)
    (hZ : Subgroup.center hyp.Q = hyp.Q0.subgroupOf hyp.Q)
    (H : IsFGH hyp.H hyp.Q hyp.D hyp.t f g h)
    (hC2 : hyp.t * hyp.distinguishedInvolution * hyp.t
      = hyp.distinguishedInvolution * hyp.t * hyp.distinguishedInvolution)
    (hm : m ≠ 0) (hQ0card : Nat.card ↥hyp.Q0 = 2 ^ m)
    (hinj : Function.Injective M.mu)
    (hK : Nat.card ↥hyp.actualKActor = 2 ^ m - 1)
    (hWdvd : Nat.card ↥hyp.W ∣ 2 ^ m + 1) (hW1 : 1 < Nat.card ↥hyp.W)
    {ω : G} (hωQ : ω ∈ hyp.Q) (hωQ0 : ω ∉ hyp.Q0)
    (c : M.Eˣ ⧸ (MonoidHom.range M.mu)) :
    ∃ x : ↥hyp.Q0, hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c := by
  obtain ⟨hgen, hbase⟩ :=
    hyp.stepEight_of_KW M hZ H hC2 hm hQ0card hinj hK hWdvd hωQ hωQ0
  have hne : {x : ↥hyp.Q0 | hyp.orbitOfF M hZ H hC2 hωQ hωQ0 x = c}.ncard ≠ 0 := by
    by_cases hc : c = QuotientGroup.mk (hyp.baseUnit M hZ hωQ hωQ0)
    · rw [hc, hbase]
      omega
    · rw [hgen c hc]
      omega
  obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero hne
  exact ⟨x, hx⟩

end

end Hypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
