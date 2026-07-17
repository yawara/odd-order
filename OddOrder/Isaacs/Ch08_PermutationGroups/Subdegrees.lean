/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.OrbitalGraph

/-!
# Isaacs, Finite Group Theory — Ch. 8: subdegree growth (Thm 8.37)

Formalizes **Isaacs Thm 8.37** (p. 246): if `G` acts primitively on `Ω`
with subdegrees `1 = m₁ ≤ m₂ ≤ ⋯ ≤ m_r`, then `m_{i+1} ≤ m₂ · m_i`.

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

end OddOrder.Isaacs.Ch08
