/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.OrbitalGraph
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-!
# Isaacs, Finite Group Theory — Ch. 8: subdegrees (Thm 8.37, 8.38, Lem 8.39)

Formalizes **Isaacs Thm 8.37** (p. 246): if `G` acts primitively on `Ω`
with subdegrees `1 = m₁ ≤ m₂ ≤ ⋯ ≤ m_r`, then `m_{i+1} ≤ m₂ · m_i`;
**Isaacs Lem 8.39** (p. 248), clauses (a) and (b) — the "arrow" index
arithmetic (`relIndex_le_and_dvd_of_coprime`); and **Isaacs Thm 8.38**
(p. 247, Weiss) — a subdegree coprime to the largest subdegree is `1`
(`subdegree_eq_one_of_coprime_of_max`).

We state the gap form (`subdegree_gap_le`): if `s ≥ 1`, some suborbit at
`α` has size `> s`, and no suborbit size lies strictly between `s` and `t`,
then `t ≤ |Δ(α)| · s` for *every* non-diagonal orbital `Δ` (the book's
bound follows by instantiating `Δ` with an orbital of size `m₂`, `s = mᵢ`,
`t = m_{i+1}`; Isaacs's proof never uses the minimality of `m₂`).

Proof: grade the `Δ`-graph reachability by path length (`reachIn`);
connectivity (Thm 8.35) makes every point reachable.  Choose `β` with
suborbit size `> s` at minimal distance `d`.  If `d ≤ 1` then the suborbit
of `β` is trivial or equal to `Δ(α)`, and the bound is direct.  Otherwise
the predecessor `γ` of `β` has suborbit size `≤ s` by minimality, every
point of the suborbit of `β` is reached by a `Δ`-arrow from the suborbit of
`γ`, and all the sets `Δ(c)` have size `|Δ(α)|`, so
`t ≤ |orbit β| ≤ |orbit γ| · |Δ(α)| ≤ s · |Δ(α)|`.
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

section ReachIn

/-- Reachability in exactly `n` steps of a relation. -/
private def reachIn (r : Ω → Ω → Prop) (α : Ω) : ℕ → Ω → Prop
  | 0, γ => γ = α
  | (n + 1), γ => ∃ c, reachIn r α n c ∧ r c γ

private lemma exists_reachIn_of_reflTransGen {r : Ω → Ω → Prop} {α β : Ω}
    (h : Relation.ReflTransGen r α β) : ∃ n, reachIn r α n β := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ h₂ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, _, hn, h₂⟩

end ReachIn

section Theorem837

variable [Finite Ω]

omit [Finite Ω] in
/-- The suborbit of `α` at `α` itself is `{α}`. -/
private lemma orbit_stabilizer_self (α : Ω) :
    orbit (stabilizer G α) α = {α} := by
  ext γ
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    exact mem_stabilizer_iff.mp hh
  · rintro rfl
    exact mem_orbit_self _

omit [Finite Ω] in
/-- All orbital functions of one orbital have equal size (transitivity). -/
private lemma ncard_orbitalAt_eq [IsPretransitive G Ω] (p : Ω × Ω)
    (α c : Ω) :
    Set.ncard (orbitalAt (orbit G p) c) =
      Set.ncard (orbitalAt (orbit G p) α) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α c
  rw [orbitalAt_orbit_smul]
  have himg : (g • orbitalAt (orbit G p) α) =
      (fun β => g • β) '' orbitalAt (orbit G p) α := rfl
  rw [himg, Set.ncard_image_of_injective _ (MulAction.injective g)]

/-- **Isaacs Thm 8.37**, gap form — let `G` act primitively on the finite
set `Ω`, let `α : Ω`, and let `Δ` be a non-diagonal orbital.  If `s ≥ 1`,
some suborbit at `α` has size `> s`, and every suborbit size is `≤ s` or
`≥ t`, then `t ≤ |Δ(α)| · s`.  (With `Δ` an orbital of minimal non-trivial
size `m₂`, `s = mᵢ` and `t = m_{i+1}` this is the book's
`m_{i+1} ≤ m₂ · mᵢ`.) -/
theorem subdegree_gap_le [IsPreprimitive G Ω] (α : Ω)
    {q : Ω × Ω} (hq : q.1 ≠ q.2) {s t : ℕ} (hs : 1 ≤ s)
    (hex : ∃ β : Ω, s < Set.ncard (orbit (stabilizer G α) β))
    (hgap : ∀ γ : Ω, Set.ncard (orbit (stabilizer G α) γ) ≤ s ∨
      t ≤ Set.ncard (orbit (stabilizer G α) γ)) :
    t ≤ Set.ncard (orbitalAt (orbit G q) α) * s := by
  classical
  set r : Ω → Ω → Prop := fun a b => (a, b) ∈ orbit G q with hrdef
  set M : ℕ := Set.ncard (orbitalAt (orbit G q) α) with hM
  -- the set of distances of points with large suborbits is nonempty
  have hDex : ∃ n : ℕ, ∃ γ : Ω,
      s < Set.ncard (orbit (stabilizer G α) γ) ∧ reachIn r α n γ := by
    obtain ⟨β, hβ⟩ := hex
    obtain ⟨n, hn⟩ := exists_reachIn_of_reflTransGen
      (orbital_connected_of_isPreprimitive (G := G) hq α β)
    exact ⟨n, β, hβ, hn⟩
  obtain ⟨β, hβs, hβreach⟩ := Nat.find_spec hDex
  have hmin : ∀ n < Nat.find hDex, ∀ γ : Ω, reachIn r α n γ →
      Set.ncard (orbit (stabilizer G α) γ) ≤ s := by
    intro n hn γ hγ
    by_contra hc
    exact Nat.find_min hDex hn ⟨γ, lt_of_not_ge hc, hγ⟩
  -- `t ≤ ncard (orbit β)` from the gap
  have htβ : t ≤ Set.ncard (orbit (stabilizer G α) β) :=
    (hgap β).resolve_left (not_le.mpr hβs)
  -- case on the distance
  match hd' : Nat.find hDex, hβreach with
  | 0, hreach =>
    -- `β = α` has suborbit `{α}` of size `1 ≤ s`
    exfalso
    have hβα : β = α := hreach
    rw [hβα, orbit_stabilizer_self, Set.ncard_singleton] at hβs
    omega
  | (n + 1), hreach =>
    obtain ⟨γ, hγreach, hγβ⟩ := hreach
    -- the suborbit of `γ` is small (its distance is below the minimum)
    have hγs : Set.ncard (orbit (stabilizer G α) γ) ≤ s := by
      apply hmin n _ γ hγreach
      omega
    -- the suborbit of `β` is covered by `Δ`-arrows from the suborbit of `γ`
    have hcover : orbit (stabilizer G α) β ⊆
        ⋃ c ∈ orbit (stabilizer G α) γ, orbitalAt (orbit G q) c := by
      rintro u ⟨h, rfl⟩
      refine Set.mem_biUnion (mem_orbit γ h) ?_
      rw [mem_orbitalAt_iff]
      exact smul_pair_mem_orbit ((h : G)) hγβ
    -- cardinality bookkeeping
    haveI := Fintype.ofFinite Ω
    have hU2 : Set.ncard (⋃ c ∈ orbit (stabilizer G α) γ,
        orbitalAt (orbit G q) c) ≤
        Set.ncard (orbit (stabilizer G α) γ) * M := by
      have hfin : (⋃ c ∈ orbit (stabilizer G α) γ,
          orbitalAt (orbit G q) c).toFinset ⊆
          (orbit (stabilizer G α) γ).toFinset.biUnion
            (fun c => (orbitalAt (orbit G q) c).toFinset) := by
        intro z hz
        rw [Set.mem_toFinset, Set.mem_iUnion₂] at hz
        obtain ⟨c, hc, hzc⟩ := hz
        rw [Finset.mem_biUnion]
        exact ⟨c, Set.mem_toFinset.mpr hc, Set.mem_toFinset.mpr hzc⟩
      calc Set.ncard (⋃ c ∈ orbit (stabilizer G α) γ,
            orbitalAt (orbit G q) c)
          = (⋃ c ∈ orbit (stabilizer G α) γ,
              orbitalAt (orbit G q) c).toFinset.card := by
            rw [Set.ncard_eq_toFinset_card']
        _ ≤ ((orbit (stabilizer G α) γ).toFinset.biUnion
              (fun c => (orbitalAt (orbit G q) c).toFinset)).card :=
            Finset.card_le_card hfin
        _ ≤ ∑ c ∈ (orbit (stabilizer G α) γ).toFinset,
              (orbitalAt (orbit G q) c).toFinset.card :=
            Finset.card_biUnion_le
        _ = ∑ _c ∈ (orbit (stabilizer G α) γ).toFinset, M := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← Set.ncard_eq_toFinset_card', hM, ncard_orbitalAt_eq]
        _ = (orbit (stabilizer G α) γ).toFinset.card * M := by
            rw [Finset.sum_const, smul_eq_mul]
        _ = Set.ncard (orbit (stabilizer G α) γ) * M := by
            rw [Set.ncard_eq_toFinset_card']
    have hchain : t ≤ Set.ncard (orbit (stabilizer G α) γ) * M :=
      le_trans htβ (le_trans
        (Set.ncard_le_ncard hcover (Set.toFinite _)) hU2)
    calc t ≤ Set.ncard (orbit (stabilizer G α) γ) * M := hchain
      _ ≤ s * M := Nat.mul_le_mul_right M hγs
      _ = M * s := Nat.mul_comm s M

end Theorem837

/-! ### Isaacs Lem 8.39 (a), (b) — arrow arithmetic -/

section Lemma839

/-- **Isaacs Lem 8.39 (a), (b)** — in a finite group, write `m = |A : A∩B|`,
`n = |A : A∩C|` and `u = |B : B∩C|` (the `m`-, `n`- and `u`-arrows of the
book, with `A, B, C` the three point stabilizers).  If `|A| = |B|` and
`m, n` are coprime, then `n ≤ u` and `u ∣ m n`.  (Clause (c),
`C A ⊆ C B`, is deferred to its use in Thm 8.42.) -/
theorem relIndex_le_and_dvd_of_coprime {M : Type*} [Group M] [Finite M]
    {A B C : Subgroup M} (hAB : Nat.card A = Nat.card B)
    (hcop : Nat.Coprime (B.relIndex A) (C.relIndex A)) :
    C.relIndex A ≤ C.relIndex B ∧
      C.relIndex B ∣ B.relIndex A * C.relIndex A := by
  set m := B.relIndex A with hm
  set n := C.relIndex A with hn
  have hne : ∀ (X Y : Subgroup M), X.relIndex Y ≠ 0 := by
    intro X Y
    exact Subgroup.index_ne_zero_of_finite
  -- `q = |A∩B : A∩B∩C| = n` by coprimality
  set q := C.relIndex (B ⊓ A) with hq
  have hchain : q * m = (C ⊓ B).relIndex A :=
    Subgroup.relIndex_inf_mul_relIndex C B A
  have hndvd : n ∣ q * m := by
    rw [hchain]
    exact Subgroup.relIndex_dvd_of_le_left A inf_le_left
  have hnq : n ∣ q := (Nat.Coprime.dvd_of_dvd_mul_right
    (Nat.Coprime.symm hcop) hndvd)
  have hqn : q ≤ n := by
    have h2 := Subgroup.relIndex_le_of_le_right (H := C)
      (inf_le_right : B ⊓ A ≤ A) (hne C A)
    rw [← hq, ← hn] at h2
    exact h2
  have hqeq : q = n := Nat.le_antisymm hqn
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (by rw [hq]; exact hne _ _)) hnq)
  constructor
  · -- (a): `n = q ≤ u`
    rw [← hqeq, hq]
    have h2 := Subgroup.relIndex_le_of_le_right (H := C)
      (inf_le_left : B ⊓ A ≤ B) (hne C B)
    exact h2
  · -- (b): `u ∣ |B : W| = |A : W| = m n` with `W = C ⊓ B ⊓ A`
    set W := C ⊓ B ⊓ A with hW
    have hWB : W ≤ B := le_trans inf_le_left inf_le_right
    have hWA : W ≤ A := inf_le_right
    have hu_dvd : C.relIndex B ∣ W.relIndex B := by
      have h2 : W ≤ C := le_trans inf_le_left inf_le_left
      exact Subgroup.relIndex_dvd_of_le_left B h2
    have hWrel : W.relIndex A = n * m := by
      have h2 : (C ⊓ B).relIndex A = W.relIndex A := by
        rw [hW, ← Subgroup.inf_relIndex_right (C ⊓ B) A]
      rw [← h2, ← hchain, hqeq]
    -- `|B : W| = |A : W|` from `|A| = |B|`
    have hcardrel : ∀ (X : Subgroup M) (hWX : W ≤ X),
        W.relIndex X * Nat.card W = Nat.card X := by
      intro X hWX
      have h2 : (W.subgroupOf X).index * Nat.card (W.subgroupOf X) =
          Nat.card X := Subgroup.index_mul_card _
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv] at h2
    have hWeq : W.relIndex B = W.relIndex A := by
      have h1 := hcardrel B hWB
      have h2 := hcardrel A hWA
      rw [← hAB] at h1
      have hpos : 0 < Nat.card W := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
    rw [Nat.mul_comm]
    rw [← hWrel, ← hWeq]
    exact hu_dvd

end Lemma839

/-! ### Isaacs Thm 8.38 — Weiss's theorem -/

section Theorem838

variable [Finite Ω]

omit [Finite Ω] in
/-- The size of a suborbit is a relative index of stabilizers. -/
private lemma ncard_suborbit_eq_relIndex (α β : Ω) :
    Set.ncard (orbit (stabilizer G α) β) =
      (stabilizer G β).relIndex (stabilizer G α) := by
  have hstab : stabilizer (↥(stabilizer G α)) β =
      (stabilizer G β).subgroupOf (stabilizer G α) := by
    ext h
    rfl
  rw [← Nat.card_coe_set_eq,
    Nat.card_congr (orbitEquivQuotientStabilizer (↥(stabilizer G α)) β),
    hstab]
  rfl

omit [Finite Ω] in
/-- Suborbit sizes are invariant under translation. -/
private lemma ncard_suborbit_smul_eq (g : G) (α β : Ω) :
    Set.ncard (orbit (stabilizer G (g • α)) (g • β)) =
      Set.ncard (orbit (stabilizer G α) β) := by
  have horb : orbit (stabilizer G (g • α)) (g • β) =
      (fun x => g • x) '' orbit (stabilizer G α) β := by
    ext z
    constructor
    · rintro ⟨⟨h, hh⟩, rfl⟩
      refine ⟨(g⁻¹ * h * g) • β, ⟨⟨g⁻¹ * h * g, ?_⟩, rfl⟩, ?_⟩
      · rw [mem_stabilizer_iff] at hh ⊢
        rw [mul_smul, mul_smul, hh, inv_smul_smul]
      · change g • (g⁻¹ * h * g) • β = h • g • β
        rw [smul_smul, smul_smul, mul_assoc g⁻¹ h g, mul_inv_cancel_left]
    · rintro ⟨w, ⟨⟨h, hh⟩, rfl⟩, rfl⟩
      refine ⟨⟨g * h * g⁻¹, ?_⟩, ?_⟩
      · rw [mem_stabilizer_iff] at hh ⊢
        rw [mul_smul, mul_smul, inv_smul_smul, hh]
      · change (g * h * g⁻¹) • g • β = g • h • β
        rw [smul_smul, smul_smul, inv_mul_cancel_right]
  rw [horb, Set.ncard_image_of_injective _ (MulAction.injective g)]

omit [Finite Ω] in
/-- Conjugate stabilizers have equal cardinality. -/
private lemma card_stabilizer_eq [IsPretransitive G Ω] (α β : Ω) :
    Nat.card (stabilizer G α) = Nat.card (stabilizer G β) := by
  obtain ⟨g, rfl⟩ := exists_smul_eq G α β
  rw [stabilizer_smul_eq_stabilizer_map_conj]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (MulEquiv.injective (MulAut.conj g))).toEquiv

/-- Relative indices of equal-order subgroups are symmetric:
`|K : H ∩ K| = |H : K ∩ H|` when `|H| = |K|`. -/
private lemma relIndex_comm_of_card_eq {M : Type*} [Group M] [Finite M]
    {H K : Subgroup M} (hcard : Nat.card H = Nat.card K) :
    H.relIndex K = K.relIndex H := by
  have key : ∀ A B : Subgroup M,
      A.relIndex B * Nat.card ↥(A ⊓ B) = Nat.card B := by
    intro A B
    have h2 := Subgroup.index_mul_card ((A ⊓ B).subgroupOf B)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : A ⊓ B ≤ B)).toEquiv] at h2
    rw [← Subgroup.inf_relIndex_right A B]
    exact h2
  have h1 := key H K
  have h2 := key K H
  rw [inf_comm K H, hcard] at h2
  have hpos : 0 < Nat.card ↥(H ⊓ K) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

/-- **Isaacs Thm 8.38** (Weiss; p. 247) — let a finite group `G` act
primitively on `Ω`, let `n` be the largest subdegree at `α` (attained on
the suborbit of `β₀`), and let `m` be a subdegree at `α` coprime to `n`.
Then `m = 1`.

Proof: by Lem 8.34/8.35 the orbital `Δ` of `(α, γ₀)` is non-diagonal and
its graph is connected; every `Δ`-arrow `δ → γ` is an "`m`-arrow"
(`|G_δ : G_δ ∩ G_γ| = m`).  By induction along paths from `α`, using
Lem 8.39(a) with `A = G_δ`, `B = G_γ`, `C = G_{β₀}` and maximality of `n`,
every reachable `γ` has `|G_γ : G_γ ∩ G_{β₀}| = n`.  An out-neighbor `ε`
of `β₀` then gives `m = |G_{β₀} : G_{β₀} ∩ G_ε| = |G_ε : G_ε ∩ G_{β₀}| = n`
by index symmetry, so `m = n` and coprimality forces `m = 1`. -/
theorem subdegree_eq_one_of_coprime_of_max [Finite G] [IsPreprimitive G Ω]
    (α : Ω) {n m : ℕ} {β₀ γ₀ : Ω}
    (hn : Set.ncard (orbit (stabilizer G α) β₀) = n)
    (hmax : ∀ δ : Ω, Set.ncard (orbit (stabilizer G α) δ) ≤ n)
    (hm : Set.ncard (orbit (stabilizer G α) γ₀) = m)
    (hcop : Nat.Coprime m n) : m = 1 := by
  classical
  by_contra hm1
  -- `γ₀ ≠ α`, so the orbital of `(α, γ₀)` is non-diagonal
  have hγ₀α : γ₀ ≠ α := by
    rintro rfl
    rw [orbit_stabilizer_self, Set.ncard_singleton] at hm
    exact hm1 hm.symm
  have hq : (α, γ₀).1 ≠ (α, γ₀).2 := Ne.symm hγ₀α
  have hm1' : 1 ≤ m := by
    have h2 : 0 < Set.ncard (orbit (stabilizer G α) γ₀) :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨γ₀, mem_orbit_self _⟩
    omega
  -- the largest subdegree bounds the suborbits at every point
  have hmaxall : ∀ γ δ : Ω, Set.ncard (orbit (stabilizer G γ) δ) ≤ n := by
    intro γ δ
    obtain ⟨g, rfl⟩ := exists_smul_eq G α γ
    have h2 := ncard_suborbit_smul_eq g α (g⁻¹ • δ)
    rw [smul_inv_smul] at h2
    rw [h2]
    exact hmax _
  -- every arrow of the orbital of `(α, γ₀)` is an `m`-arrow
  have harrow : ∀ γ δ : Ω, (γ, δ) ∈ orbit G (α, γ₀) →
      Set.ncard (orbit (stabilizer G γ) δ) = m := by
    intro γ δ hδ
    have h3 : orbit G (α, γ₀) = orbit G (γ, δ) := (orbit_eq_iff.mpr hδ).symm
    have h2 : orbitalAt (orbit G (α, γ₀)) γ = orbit (stabilizer G γ) δ := by
      rw [h3, orbitalAt_orbit_eq]
    rw [← h2, ncard_orbitalAt_eq (α := α) (p := (α, γ₀)), orbitalAt_orbit_eq]
    exact hm
  -- induction along paths: every reachable point sees `β₀` in an `n`-suborbit
  have hclaim : ∀ k : ℕ, ∀ γ : Ω,
      reachIn (fun a b => (a, b) ∈ orbit G (α, γ₀)) α k γ →
      Set.ncard (orbit (stabilizer G γ) β₀) = n := by
    intro k
    induction k with
    | zero =>
      intro γ hγ
      obtain rfl : γ = α := hγ
      exact hn
    | succ k ih =>
      rintro γ ⟨δ, hδ, hδγ⟩
      have hmδγ : Set.ncard (orbit (stabilizer G δ) γ) = m := harrow δ γ hδγ
      have hnδ : Set.ncard (orbit (stabilizer G δ) β₀) = n := ih δ hδ
      -- Lem 8.39(a) with `A = G_δ`, `B = G_γ`, `C = G_{β₀}`
      have hcardAB : Nat.card (stabilizer G δ) = Nat.card (stabilizer G γ) :=
        card_stabilizer_eq δ γ
      have hcop' : Nat.Coprime
          ((stabilizer G γ).relIndex (stabilizer G δ))
          ((stabilizer G β₀).relIndex (stabilizer G δ)) := by
        rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
          hmδγ, hnδ]
        exact hcop
      obtain ⟨hge, -⟩ := relIndex_le_and_dvd_of_coprime hcardAB hcop'
      rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
        hnδ] at hge
      exact Nat.le_antisymm (hmaxall γ β₀) hge
  -- an out-neighbor `ε` of `β₀` (the orbital function at `β₀` has size `m`)
  have hεex : (orbitalAt (orbit G (α, γ₀)) β₀).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [ncard_orbitalAt_eq (α := α) (p := (α, γ₀)), orbitalAt_orbit_eq, hm]
    omega
  obtain ⟨ε, hε⟩ := hεex
  rw [mem_orbitalAt_iff] at hε
  have hmε : Set.ncard (orbit (stabilizer G β₀) ε) = m := harrow β₀ ε hε
  -- `ε` is reachable, so its suborbit of `β₀` has size `n`
  obtain ⟨k, hk⟩ := exists_reachIn_of_reflTransGen
    (orbital_connected_of_isPreprimitive (G := G) hq α ε)
  have hnε : Set.ncard (orbit (stabilizer G ε) β₀) = n := hclaim k ε hk
  -- index symmetry: the `β₀ → ε` and `ε → β₀` suborbits have equal size
  have hsym : Set.ncard (orbit (stabilizer G β₀) ε) =
      Set.ncard (orbit (stabilizer G ε) β₀) := by
    rw [ncard_suborbit_eq_relIndex, ncard_suborbit_eq_relIndex]
    exact relIndex_comm_of_card_eq (card_stabilizer_eq ε β₀)
  rw [hmε, hnε] at hsym
  rw [hsym] at hm1 hcop
  have h9 : Nat.gcd n n = 1 := hcop
  rw [Nat.gcd_self] at h9
  exact hm1 h9

end Theorem838

end OddOrder.Isaacs.Ch08
