/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch08_PermutationGroups.Subdegrees

/-!
# Isaacs, Finite Group Theory — Ch. 8: `m`-arrows and the subgroups `K_m` (§8D)

Machinery for **Isaacs Thm 8.41–8.43** (pp. 249–251): `m`-arrows, the
`m`-graph components `[α]_m`, and the subgroups
`K_m(α) = ⟨G_β : β ∈ [α]_m⟩` whose indices `k_m = |K_m(α) : G_α|` drive
the common-divisor-graph theorems.

* `IsArrow G m α β` — `α → β` is an *`m`-arrow*: `β` lies in a `G_α`-orbit
  of size `m` (p. 247).  For a transitive action of a finite group this is
  symmetric (`IsArrow.symm`): equivalently `α` lies in a `G_β`-orbit of
  size `m`.
* `arrowComponent G m α` — the component `[α]_m` of `α` in the `m`-graph
  (p. 249).
* `arrowKernel G m α` — the subgroup `K_m(α) = ⟨G_β : β ∈ [α]_m⟩`.

The theorems 8.41–8.43 themselves are formalized on top of this machinery
(Thm 8.42 first, since 8.41 and 8.43 are corollaries of it).
-/

namespace OddOrder.Isaacs.Ch08

open MulAction

open scoped Pointwise

variable {G Ω : Type*} [Group G] [MulAction G Ω]

section ArrowMachinery

variable (G) in
/-- `α → β` is an *`m`-arrow* if `β` lies in a `G_α`-orbit of size `m`
(Isaacs p. 247). -/
def IsArrow (m : ℕ) (α β : Ω) : Prop :=
  Set.ncard (orbit (stabilizer G α) β) = m

lemma isArrow_iff {m : ℕ} {α β : Ω} :
    IsArrow G m α β ↔ Set.ncard (orbit (stabilizer G α) β) = m :=
  Iff.rfl

/-- For a transitive action of a finite group the `m`-arrow relation is
symmetric (Isaacs p. 247: `α → β` is an `m`-arrow iff `α` lies in a
`G_β`-orbit of size `m`). -/
lemma IsArrow.symm [Finite G] [IsPretransitive G Ω] {m : ℕ} {α β : Ω}
    (h : IsArrow G m α β) : IsArrow G m β α := by
  rw [isArrow_iff, ncard_suborbit_eq_relIndex] at h ⊢
  rw [relIndex_comm_of_card_eq (card_stabilizer_eq α β)]
  exact h

variable (G) in
/-- The component `[α]_m` of `α` in the `m`-graph (Isaacs p. 249): `α`
together with the points reachable from `α` along `m`-arrows. -/
def arrowComponent (m : ℕ) (α : Ω) : Set Ω :=
  {β | Relation.ReflTransGen (IsArrow G m) α β}

lemma mem_arrowComponent_self (m : ℕ) (α : Ω) :
    α ∈ arrowComponent G m α :=
  Relation.ReflTransGen.refl

lemma mem_arrowComponent_of_isArrow {m : ℕ} {α β γ : Ω}
    (hβ : β ∈ arrowComponent G m α) (h : IsArrow G m β γ) :
    γ ∈ arrowComponent G m α :=
  Relation.ReflTransGen.tail hβ h

/-- Induction along the component `[α]_m`: a predicate holding at `α` and
propagating along `m`-arrows holds on all of `[α]_m`. -/
lemma arrowComponent_induction {m : ℕ} {α : Ω} {p : Ω → Prop}
    (hα : p α) (hstep : ∀ β γ : Ω, p β → IsArrow G m β γ → p γ)
    {β : Ω} (hβ : β ∈ arrowComponent G m α) : p β := by
  induction hβ with
  | refl => exact hα
  | tail _ harrow ih => exact hstep _ _ ih harrow

variable (G) in
/-- The subgroup `K_m(α) = ⟨G_β : β ∈ [α]_m⟩` (Isaacs p. 249). -/
def arrowKernel (m : ℕ) (α : Ω) : Subgroup G :=
  Subgroup.closure (⋃ β ∈ arrowComponent G m α, (stabilizer G β : Set G))

lemma stabilizer_le_arrowKernel {m : ℕ} {α β : Ω}
    (h : β ∈ arrowComponent G m α) :
    stabilizer G β ≤ arrowKernel G m α :=
  fun _x hx => Subgroup.subset_closure (Set.mem_biUnion h hx)

lemma stabilizer_le_arrowKernel_self (m : ℕ) (α : Ω) :
    stabilizer G α ≤ arrowKernel G m α :=
  stabilizer_le_arrowKernel (mem_arrowComponent_self m α)

lemma arrowKernel_le {m : ℕ} {α : Ω} {K : Subgroup G}
    (h : ∀ β ∈ arrowComponent G m α, stabilizer G β ≤ K) :
    arrowKernel G m α ≤ K :=
  (Subgroup.closure_le K).mpr
    (Set.iUnion₂_subset fun β hβ _x hx => h β hβ hx)

lemma arrowKernel_le_arrowKernel {m n : ℕ} {α γ : Ω}
    (h : arrowComponent G m α ⊆ arrowComponent G n γ) :
    arrowKernel G m α ≤ arrowKernel G n γ :=
  arrowKernel_le fun _β hβ => stabilizer_le_arrowKernel (h hβ)

end ArrowMachinery

/-! ### Isaacs Thm 8.42 (a) -/

section Theorem842

variable [Finite G] [IsPretransitive G Ω]

/-- Every point of `[α]_m` has an `n`-arrow to `γ` when `α` does — the
`S`-closure step of Isaacs Thm 8.42, via Lem 8.39 (a), (b). -/
private lemma isArrow_of_mem_arrowComponent {m n : ℕ} {α γ : Ω}
    (hmn : m < n) (hαγ : IsArrow G n α γ)
    (hcop : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) m ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) n)
    {β : Ω} (hβ : β ∈ arrowComponent G m α) : IsArrow G n β γ := by
  refine arrowComponent_induction (p := fun β => IsArrow G n β γ) hαγ ?_ hβ
  intro δ β' hδ harrow
  rw [isArrow_iff] at harrow
  have hδ' : Set.ncard (orbit (stabilizer G δ) γ) = n := hδ
  -- `m` and `n` are coprime
  have hcopmn : Nat.Coprime m n := by
    rcases hcop δ β' with h2 | h2 <;> rw [harrow] at h2
    · have h3 : Nat.gcd m m = 1 := h2
      rw [Nat.gcd_self] at h3
      rw [h3]
      exact Nat.coprime_one_left n
    · exact h2
  -- Lem 8.39 (a), (b) at `A = G_δ`, `B = G_{β'}`, `C = G_γ`
  have hcard : Nat.card (stabilizer G δ) = Nat.card (stabilizer G β') :=
    card_stabilizer_eq δ β'
  have hcop' : Nat.Coprime ((stabilizer G β').relIndex (stabilizer G δ))
      ((stabilizer G γ).relIndex (stabilizer G δ)) := by
    rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
      harrow, hδ']
    exact hcopmn
  obtain ⟨hge, hdvd⟩ := relIndex_le_and_dvd_of_coprime hcard hcop'
  rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex, hδ']
    at hge
  rw [← ncard_suborbit_eq_relIndex, ← ncard_suborbit_eq_relIndex,
    ← ncard_suborbit_eq_relIndex, harrow, hδ'] at hdvd
  -- the arrow value `β' → γ` is a subdegree coprime to `m` or `n`
  rw [isArrow_iff]
  rcases hcop β' γ with h2 | h2
  · -- coprime to `m`: it divides `n`, and is `≥ n`
    have h3 := Nat.Coprime.dvd_of_dvd_mul_left h2 hdvd
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) h3) hge
  · -- coprime to `n`: it divides `m`, contradicting `≥ n > m`
    exfalso
    have h3 := Nat.Coprime.dvd_of_dvd_mul_right h2 hdvd
    have h4 : 0 < m := by
      have h5 : (orbit (stabilizer G δ) β').Finite := Set.finite_range _
      have h6 := (Set.ncard_pos h5).mpr ⟨β', mem_orbit_self _⟩
      omega
    have h7 := Nat.le_of_dvd h4 h3
    omega

/-- **Isaacs Thm 8.42 (a)** (p. 250) — let a finite group `G` act
transitively on `Ω`, let `m < n` be subdegrees such that every subdegree
is coprime to `m` or to `n`, and let `α → γ` be an `n`-arrow.  Then
`k_m = |K_m(α) : G_α|` divides `k_n = |K_n(γ) : G_γ|`. -/
theorem relIndex_arrowKernel_dvd_relIndex_arrowKernel {m n : ℕ} {α γ : Ω}
    (hmn : m < n) (hαγ : IsArrow G n α γ)
    (hcop : ∀ δ ε : Ω,
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) m ∨
      Nat.Coprime (Set.ncard (orbit (stabilizer G δ) ε)) n) :
    (stabilizer G α).relIndex (arrowKernel G m α) ∣
      (stabilizer G γ).relIndex (arrowKernel G n γ) := by
  -- `[α]_m ⊆ [γ]_n`, hence `K_m(α) ≤ K_n(γ)`
  have hcompsub : arrowComponent G m α ⊆ arrowComponent G n γ := by
    intro β hβ
    exact mem_arrowComponent_of_isArrow (mem_arrowComponent_self n γ)
      (isArrow_of_mem_arrowComponent hmn hαγ hcop hβ).symm
  have hK : arrowKernel G m α ≤ arrowKernel G n γ :=
    arrowKernel_le_arrowKernel hcompsub
  set Km := arrowKernel G m α
  set Kn := arrowKernel G n γ
  -- index tower: `k_n = |K_n : K_m| · k_m`
  have h1 : (stabilizer G α).relIndex Km * Nat.card (stabilizer G α) =
      Nat.card Km := by
    have h4 := relIndex_mul_card_inf (stabilizer G α) Km
    rwa [inf_eq_left.mpr (stabilizer_le_arrowKernel_self m α)] at h4
  have h2 : (stabilizer G γ).relIndex Kn * Nat.card (stabilizer G γ) =
      Nat.card Kn := by
    have h4 := relIndex_mul_card_inf (stabilizer G γ) Kn
    rwa [inf_eq_left.mpr (stabilizer_le_arrowKernel_self n γ)] at h4
  have h3 : Km.relIndex Kn * Nat.card Km = Nat.card Kn := by
    have h4 := relIndex_mul_card_inf Km Kn
    rwa [inf_eq_left.mpr hK] at h4
  have hstab : Nat.card (stabilizer G α) = Nat.card (stabilizer G γ) :=
    card_stabilizer_eq α γ
  have hpos : 0 < Nat.card (stabilizer G γ) := Nat.card_pos
  have h6 : (stabilizer G γ).relIndex Kn * Nat.card (stabilizer G γ) =
      Km.relIndex Kn * (stabilizer G α).relIndex Km *
        Nat.card (stabilizer G γ) := by
    rw [h2, ← h3, ← h1, hstab, mul_assoc]
  have h7 : (stabilizer G γ).relIndex Kn =
      Km.relIndex Kn * (stabilizer G α).relIndex Km :=
    Nat.eq_of_mul_eq_mul_right hpos h6
  exact Dvd.intro_left _ h7.symm

end Theorem842

end OddOrder.Isaacs.Ch08
