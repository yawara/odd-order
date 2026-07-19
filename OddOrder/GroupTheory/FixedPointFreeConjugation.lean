/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Group

/-!
# Fixed-point-free conjugation: the twisted map, quotient descent, and involutions

Elementary theory of an element `x` acting by conjugation on a finite subgroup `F` without
nonidentity fixed points, after D. Gorenstein, *Finite Groups* (2nd ed.), Ch. 10 §1.

* Lemma 10.1.1 (the *twisted map*): `f ↦ f⁻¹ · (x f x⁻¹)` is a bijection of `F`; here we
  record the surjectivity statement `exists_inv_mul_conj_eq`.
* Lemma 10.1.3 (*descent to quotients*): if `x` acts fixed-point-freely on `K` and `F ≤ K` is
  `x`-invariant, the induced action on `K/F` is again fixed-point-free.  Stated in coset form
  (`mem_of_inv_mul_conj_mem_of_fixedPointFree`) to avoid quotient automorphisms: a coset fixed
  by `x` is the trivial coset.
* Lemma 10.1.4 (*involutions invert*): a fixed-point-free involution inverts every element of
  `F` (`conj_eq_inv_of_orderTwo_of_fixedPointFree`); consequently each commutator `⁅t, g⁆`
  centralizes `F` (`commutatorElement_mem_centralizer_of_orderTwo_of_fixedPointFree`) — the
  inversion is central in the automorphism group of the (necessarily abelian) `F`.

These are general finite-group lemmas with no dependence on any of the three books; they were
written for Gorenstein Ch. 12 §1 Theorem 1.5 (`OddOrder.GroupTheory.CNGroupStructure`).
-/

namespace OddOrder.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- If two twisted-map values agree, the quotient of the arguments is a fixed point:
`a⁻¹·(x a x⁻¹) = b⁻¹·(x b x⁻¹)` forces `x` to centralize `b * a⁻¹`. -/
private theorem conj_eq_of_inv_mul_conj_eq {x a b : G}
    (h : a⁻¹ * (x * a * x⁻¹) = b⁻¹ * (x * b * x⁻¹)) :
    x * (b * a⁻¹) * x⁻¹ = b * a⁻¹ := by
  have key : (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ = b * a⁻¹ := by
    have h' := congrArg (fun y => b * y * (x * a * x⁻¹)⁻¹) h
    simpa [mul_assoc] using h'.symm
  have expand : x * (b * a⁻¹) * x⁻¹ = (x * b * x⁻¹) * (x * a * x⁻¹)⁻¹ := by group
  rw [expand, key]

/-- **Gorenstein Ch. 10 §1, Lemma 1.1** (surjectivity of the twisted map): if `x` acts on the
finite subgroup `F` by conjugation with no nonidentity fixed points, every element of `F` has
the form `f⁻¹ · (x f x⁻¹)`. -/
theorem exists_inv_mul_conj_eq {F : Subgroup G} [Finite ↥F] {x : G}
    (hxF : ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hfpf : ∀ f ∈ F, x * f * x⁻¹ = f → f = 1)
    {c : G} (hc : c ∈ F) : ∃ f ∈ F, f⁻¹ * (x * f * x⁻¹) = c := by
  set ψ : ↥F → ↥F := fun f => ⟨(f : G)⁻¹ * (x * f * x⁻¹),
    F.mul_mem (F.inv_mem f.2) (hxF f f.2)⟩ with hψdef
  have hinj : Function.Injective ψ := by
    intro f₁ f₂ hf
    have h12 : (f₁ : G)⁻¹ * (x * f₁ * x⁻¹) = (f₂ : G)⁻¹ * (x * f₂ * x⁻¹) := by
      have := congrArg (Subtype.val) hf
      simpa [hψdef] using this
    have hfix := conj_eq_of_inv_mul_conj_eq h12
    have h1 : (f₂ : G) * (f₁ : G)⁻¹ = 1 :=
      hfpf _ (F.mul_mem f₂.2 (F.inv_mem f₁.2)) hfix
    have : (f₂ : G) = f₁ := by
      have := congrArg (fun y => y * (f₁ : G)) h1
      simpa [mul_assoc] using this
    exact (Subtype.ext this).symm
  obtain ⟨f, hf⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨c, hc⟩
  exact ⟨f, f.2, congrArg Subtype.val hf⟩

/-- **Gorenstein Ch. 10 §1, Lemma 1.3** (fixed-point-freeness descends to quotients), in coset
form: if `x` acts by conjugation on `K` with no nonidentity fixed points and `F ≤ K` is
`x`-invariant, then any `k ∈ K` whose coset `kF` is fixed by `x` (i.e. `k⁻¹·(x k x⁻¹) ∈ F`)
already lies in `F`.

By surjectivity of the twisted map on `F`, write `k⁻¹·(x k x⁻¹) = f⁻¹·(x f x⁻¹)` with `f ∈ F`;
then `x` centralizes `k * f⁻¹ ∈ K`, so `k = f ∈ F`. -/
theorem mem_of_inv_mul_conj_mem_of_fixedPointFree {K F : Subgroup G} [Finite ↥F]
    (hFK : F ≤ K) {x : G}
    (hxF : ∀ f ∈ F, x * f * x⁻¹ ∈ F)
    (hfpf : ∀ k ∈ K, x * k * x⁻¹ = k → k = 1)
    {k : G} (hk : k ∈ K) (hmem : k⁻¹ * (x * k * x⁻¹) ∈ F) : k ∈ F := by
  obtain ⟨f, hfF, hψ⟩ :=
    exists_inv_mul_conj_eq hxF (fun f hf => hfpf f (hFK hf)) hmem
  have hfix := conj_eq_of_inv_mul_conj_eq hψ
  have h1 : k * f⁻¹ = 1 := hfpf _ (K.mul_mem hk (K.inv_mem (hFK hfF))) hfix
  have : k = f := by
    have := congrArg (fun y => y * f) h1
    simpa [mul_assoc] using this
  exact this ▸ hfF

/-- **Gorenstein Ch. 10 §1, Lemma 1.4** (fixed-point-free involutions invert): if the
involution `t` acts by conjugation on the finite subgroup `F` with no nonidentity fixed
points, then `t f t⁻¹ = f⁻¹` for every `f ∈ F`.

Write `f = g⁻¹·(t g t⁻¹)` by surjectivity of the twisted map; conjugating by `t` and using
`t² = 1` swaps the two factors, which is inversion. -/
theorem conj_eq_inv_of_orderTwo_of_fixedPointFree {F : Subgroup G} [Finite ↥F]
    {t : G} (ht : t * t = 1)
    (htF : ∀ f ∈ F, t * f * t⁻¹ ∈ F)
    (hfpf : ∀ f ∈ F, t * f * t⁻¹ = f → f = 1)
    {f : G} (hf : f ∈ F) : t * f * t⁻¹ = f⁻¹ := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  obtain ⟨g, hgF, hψ⟩ := exists_inv_mul_conj_eq htF hfpf hf
  rw [← hψ, htinv]
  calc t * (g⁻¹ * (t * g * t)) * t
      = t * g⁻¹ * (t * g) * (t * t) := by group
    _ = t * g⁻¹ * (t * g) := by rw [ht, mul_one]
    _ = (g⁻¹ * (t * g * t))⁻¹ := by
        rw [show (g⁻¹ * (t * g * t))⁻¹ = t⁻¹ * (g⁻¹ * t⁻¹) * g by group, htinv]
        group

/-- If the involution `t` acts fixed-point-freely on the finite normal subgroup `F`, then every
commutator `⁅t, g⁆` centralizes `F`.

`t` inverts `F` (Lemma 10.1.4), so `F` is abelian and inversion is a central automorphism:
conjugation by `t g t⁻¹ g⁻¹` acts on `F` as the composite of two inversions and two mutually
inverse conjugations, i.e. trivially.  This is the engine that pushes the image of `t` into the
center of `G/F`. -/
theorem commutatorElement_mem_centralizer_of_orderTwo_of_fixedPointFree
    {F : Subgroup G} [Finite ↥F] [F.Normal] {t : G} (ht : t * t = 1)
    (hfpf : ∀ f ∈ F, t * f * t⁻¹ = f → f = 1) (g : G) :
    ⁅t, g⁆ ∈ Subgroup.centralizer (F : Set G) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htF : ∀ f ∈ F, t * f * t⁻¹ ∈ F := fun f hf =>
    Subgroup.Normal.conj_mem ‹F.Normal› f hf t
  have hinv : ∀ f ∈ F, t * f * t = f⁻¹ := by
    intro f hf
    have := conj_eq_inv_of_orderTwo_of_fixedPointFree ht htF hfpf hf
    rwa [htinv] at this
  rw [Subgroup.mem_centralizer_iff]
  intro f hf
  -- It suffices that conjugation by `⁅t, g⁆` fixes `f`.
  suffices hfix : ⁅t, g⁆ * f * ⁅t, g⁆⁻¹ = f by
    calc f * ⁅t, g⁆ = (⁅t, g⁆ * f * ⁅t, g⁆⁻¹) * ⁅t, g⁆ := by rw [hfix]
      _ = ⁅t, g⁆ * f := by group
  have hf₁ : g⁻¹ * f * g ∈ F := by
    simpa using Subgroup.Normal.conj_mem ‹F.Normal› f hf g⁻¹
  have e1 : t * (g⁻¹ * f * g) * t = (g⁻¹ * f * g)⁻¹ := hinv _ hf₁
  have e2 : t * f⁻¹ * t = f := by
    have h' := congrArg (·⁻¹) (hinv f hf)
    rw [show (t * f * t)⁻¹ = t⁻¹ * f⁻¹ * t⁻¹ by group, htinv, inv_inv] at h'
    exact h'
  -- Rewrite the commutator and its inverse with `t⁻¹ = t` before any normalization.
  have hw : ⁅t, g⁆ = t * g * t * g⁻¹ := by rw [commutatorElement_def, htinv]
  have hwinv : ⁅t, g⁆⁻¹ = g * t * g⁻¹ * t := by
    rw [hw, show (t * g * t * g⁻¹)⁻¹ = g * t⁻¹ * g⁻¹ * t⁻¹ by group, htinv]
  calc ⁅t, g⁆ * f * ⁅t, g⁆⁻¹
      = t * g * t * g⁻¹ * f * (g * t * g⁻¹ * t) := by rw [hwinv, hw]
    _ = t * (g * (t * (g⁻¹ * f * g) * t) * g⁻¹) * t := by group
    _ = t * (g * (g⁻¹ * f * g)⁻¹ * g⁻¹) * t := by rw [e1]
    _ = t * f⁻¹ * t := by group
    _ = f := e2
end OddOrder.GroupTheory
