/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.RepresentationTheory.Basic

/-!
# Reducibility of a faithful non-cyclic commutative representation over `𝔽_p`

`SingerField.isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible` says that a commutative
group acting faithfully and *irreducibly* on a finite `𝔽_p`-module is cyclic — it embeds in the
multiplicative group of the Singer field, which is cyclic.  Read contrapositively, a **non-cyclic**
commutative group cannot act faithfully and irreducibly:

* `Representation.faithful_asModule_of_injective` — the faithfulness bridge, turning
  `Function.Injective ρ` into the `MonoidAlgebra`-scalar form the Singer theorem consumes;
* `Representation.not_isSimpleModule_asModule_of_not_isCyclic` — the contrapositive itself.

Over an algebraically closed field this direction is Schur's lemma (a commutative group acts by
scalars, so an irreducible module is a line and *every* commutative group qualifies); over `𝔽_p`
it is genuinely a statement about `𝔽_{p^n}^×` being cyclic, which is why the Singer field is
needed.

The intended consumer is **BG Lemma 2.7** (`(ℤ/q)²` acting faithfully on `(ℤ/p)²`, `p ≠ q`): the
acting group is elementary abelian of rank `2`, hence non-cyclic, so the `2`-dimensional module
splits as a sum of two lines — the starting point of the eigenvalue analysis that produces
`q ∣ p - 1` and the power-map automorphism (issue 0150).
-/

namespace OddOrder.RepresentationTheory

open scoped MonoidAlgebra

universe u

variable {p : ℕ} [Fact p.Prime] {M : Type u} [AddCommGroup M] [Module (ZMod p) M] [Finite M]
variable {Q : Type u} [CommGroup Q] [Finite Q]

omit [Finite M] [Finite Q] in
/-- **Faithfulness bridge for the Singer theorems.**  An injective representation
`ρ : Representation (ZMod p) Q M` is faithful in the `MonoidAlgebra`-scalar sense used by
`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`: if `c` acts as the identity on
`ρ.asModule`, then `c = 1`.

`ρ.asModule` is a type synonym for `M` carrying the `MonoidAlgebra (ZMod p) Q`-action, and
`Representation.asModuleEquiv_symm_map_rho` identifies the scalar action of `of c` with applying
`ρ c`; injectivity of the equivalence then turns the fixed-point hypothesis into `ρ c = 1`. -/
theorem Representation.faithful_asModule_of_injective (ρ : Representation (ZMod p) Q M)
    (hfaith : Function.Injective ρ) :
    ∀ c : Q, (∀ x : ρ.asModule, (MonoidAlgebra.of (ZMod p) Q) c • x = x) → c = 1 := by
  intro c hc
  apply hfaith
  ext x
  have h := hc (ρ.asModuleEquiv.symm x)
  rw [← Representation.asModuleEquiv_symm_map_rho] at h
  have hx : (ρ c) x = x := ρ.asModuleEquiv.symm.injective h
  rw [hx, map_one]
  rfl

omit [Finite Q] in
/-- **A faithful representation of a non-cyclic commutative group over `𝔽_p` is reducible.**

Contrapositive of the Singer order bound
(`isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible`): were `ρ.asModule` simple, the
Singer field realization would embed `Q` into the cyclic group `𝔽_{p^n}^×`, forcing `Q` cyclic.

This is the reducibility input of BG Lemma 2.7 (issue 0150), where `Q ≅ (ℤ/q)²` is elementary
abelian of rank `2`. -/
theorem Representation.not_isSimpleModule_asModule_of_not_isCyclic
    (ρ : Representation (ZMod p) Q M) (hfaith : Function.Injective ρ) (hQ : ¬ IsCyclic Q) :
    ¬ IsSimpleModule (MonoidAlgebra (ZMod p) Q) ρ.asModule := by
  intro hsimple
  haveI : Finite ρ.asModule := inferInstanceAs (Finite M)
  exact hQ (isCyclic_and_card_dvd_card_sub_one_of_faithful_irreducible
    (p := p) (C := Q) (M := ρ.asModule)
    (Representation.faithful_asModule_of_injective ρ hfaith)).1

omit [Finite Q] in
/-- **A group of prime-square order and prime exponent is not cyclic.**  If `x ^ q = 1` for every
`x` in a group of order `q²` (`q` prime), no element can generate: a generator would have order
`q²`, but the exponent hypothesis bounds every order by `q`.

This is the rank-`2` elementary abelian hypothesis of BG Lemma 2.7 in the form
`Representation.not_isSimpleModule_asModule_of_not_isCyclic` consumes. -/
theorem not_isCyclic_of_exponent_of_card_sq {q : ℕ} (hq : q.Prime)
    (hQexp : ∀ x : Q, x ^ q = 1) (hQcard : Nat.card Q = q ^ 2) :
    ¬ IsCyclic Q := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have hdvd : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one (hQexp g)
  rw [hg, hQcard] at hdvd
  have hle := Nat.le_of_dvd hq.pos hdvd
  nlinarith [hq.two_le]

open Module in
/-- **A semisimple module of `K`-rank `2` that is not simple splits as two lines.**

`R`-semisimplicity supplies a simple submodule `N₁`; it is neither `⊥` (simple modules are
nontrivial) nor `⊤` (that would make the whole module simple), so as a `K`-subspace its rank is
strictly between `0` and `2`, i.e. `1`.  A complement `N₂` exists by semisimplicity
(`IsSemisimpleModule` *is* `ComplementedLattice (Submodule R _)`), and restricting scalars turns
`IsCompl` into `⊔ = ⊤`, `⊓ = ⊥` for the `K`-subspaces, so `finrank K N₂ = 2 - 1 = 1`.

Stated for an arbitrary field `K` and ring `R` over a scalar tower; the `BG` Lemma 2.7 instance is
`K = ZMod p`, `R = MonoidAlgebra (ZMod p) Q` acting on the `2`-dimensional `ρ.asModule`
(issue 0150). -/
theorem exists_isCompl_finrank_one_of_not_isSimpleModule
    {K R N : Type*} [Field K] [Ring R] [AddCommGroup N] [Module K N] [Module R N]
    [SMul K R] [IsScalarTower K R N] [IsSemisimpleModule R N]
    (hrank : Module.finrank K N = 2) (hnot : ¬ IsSimpleModule R N) :
    ∃ N₁ N₂ : Submodule R N, IsCompl N₁ N₂ ∧
      Module.finrank K (N₁.restrictScalars K) = 1 ∧
      Module.finrank K (N₂.restrictScalars K) = 1 := by
  haveI : FiniteDimensional K N :=
    FiniteDimensional.of_finrank_pos (K := K) (V := N) (by omega)
  haveI : Nontrivial N := Module.nontrivial_of_finrank_pos (R := K) (M := N) (by omega)
  obtain ⟨N₁, hN₁simple⟩ := IsSemisimpleModule.exists_simple_submodule R N
  haveI := hN₁simple
  have hbot : N₁ ≠ ⊥ := by
    intro h
    haveI : Nontrivial ↥N₁ := IsSimpleModule.nontrivial R ↥N₁
    rw [h] at this
    exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance)) this
  have htop : N₁ ≠ ⊤ := fun h => hnot (IsSimpleModule.congr
    ((Submodule.topEquiv (R := R) (M := N)).symm.trans (LinearEquiv.ofEq _ _ h.symm)))
  obtain ⟨N₂, hcompl⟩ := exists_isCompl N₁
  have hsup : N₁.restrictScalars K ⊔ N₂.restrictScalars K = ⊤ := by
    rw [← Submodule.restrictScalars_sup, hcompl.sup_eq_top]; rfl
  have hinf : N₁.restrictScalars K ⊓ N₂.restrictScalars K = ⊥ := by
    rw [← Submodule.restrictScalars_inf, hcompl.inf_eq_bot]; rfl
  have h1ne : N₁.restrictScalars K ≠ ⊤ := fun h => htop (by
    ext x; exact ⟨fun _ => trivial, fun _ => by
      have : x ∈ N₁.restrictScalars K := h ▸ Submodule.mem_top
      exact this⟩)
  have h1bot : N₁.restrictScalars K ≠ ⊥ := fun h => hbot (by
    ext x
    constructor
    · intro hx
      have : x ∈ N₁.restrictScalars K := hx
      rw [h] at this; exact this
    · intro hx; rw [Submodule.mem_bot] at hx; exact hx ▸ N₁.zero_mem)
  have hlt : Module.finrank K (N₁.restrictScalars K) < 2 := by
    rw [← hrank]; exact Submodule.finrank_lt h1ne
  have hpos : 0 < Module.finrank K (N₁.restrictScalars K) := by
    rcases Nat.eq_zero_or_pos (Module.finrank K (N₁.restrictScalars K)) with h | h
    · exact absurd (Submodule.finrank_eq_zero.mp h) h1bot
    · exact h
  have hone : Module.finrank K (N₁.restrictScalars K) = 1 := by omega
  refine ⟨N₁, N₂, hcompl, hone, ?_⟩
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq
    (N₁.restrictScalars K) (N₂.restrictScalars K)
  rw [hsup, hinf, finrank_top, hrank, hone] at hadd
  simp only [finrank_bot] at hadd
  omega

open Module in
/-- **A linear map preserving a line acts on it by a scalar.**  If `W` is a `1`-dimensional
`K`-subspace and `f` maps `W` into `W`, then `f x = c • x` for a single `c : K` and all `x ∈ W`.

Pick a nonzero `v` spanning `W` (`finrank_eq_one_iff'`); `f v` lies in `W`, hence is `c • v`, and
every `x ∈ W` is `a • v`, so `f x = a • (c • v) = c • x`.

This is the eigenvalue step of BG Lemma 2.7 (issue 0150): on each of the two lines produced by
`exists_isCompl_finrank_one_of_not_isSimpleModule` the acting group operates through a scalar,
which is what turns the rank-`2` action into a pair of characters `Q →* Kˣ`.

(mathlib's `exists_smul_eq_of_finrank_eq_one` is a different statement — that any two vectors of a
rank-`1` space are proportional; here the point is that the *scalar does not depend on `x`*.) -/
theorem exists_scalar_of_finrank_eq_one_of_mapsTo
    {K N : Type*} [Field K] [AddCommGroup N] [Module K N]
    {W : Submodule K N} (hW : finrank K W = 1)
    (f : N →ₗ[K] N) (hf : ∀ x ∈ W, f x ∈ W) :
    ∃ c : K, ∀ x ∈ W, f x = c • x := by
  obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.mp hW
  obtain ⟨c, hc⟩ := hspan ⟨f v, hf v v.2⟩
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨a, ha⟩ := hspan ⟨x, hx⟩
  have hav : a • (v : N) = x := congrArg Subtype.val ha
  have hcv : c • (v : N) = f v := congrArg Subtype.val hc
  calc f x = f (a • (v : N)) := by rw [hav]
    _ = a • f (v : N) := by rw [map_smul]
    _ = a • (c • (v : N)) := by rw [hcv]
    _ = c • (a • (v : N)) := by rw [smul_comm]
    _ = c • x := by rw [hav]

open Module in
/-- **The character of an invariant line.**  If every `ρ g` maps the `1`-dimensional subspace `W`
into itself, the scalars supplied by `exists_scalar_of_finrank_eq_one_of_mapsTo` assemble into a
monoid homomorphism `χ : Q →* K` with `ρ g x = χ g • x` for all `x ∈ W`.

The scalar is unique because `W` contains a nonzero vector, and uniqueness upgrades
`ρ 1 = 1` and `ρ (g * h) = ρ g ∘ ρ h` to `χ 1 = 1` and `χ (g * h) = χ g * χ h`.  (`χ` lands in
`K` as a multiplicative monoid; each value is a unit since `χ g * χ g⁻¹ = χ 1 = 1`.)

This is BG Lemma 2.7's pair of characters `χ₁, χ₂ : Q →* 𝔽_p^×`, one for each line of the
decomposition `exists_isCompl_finrank_one_of_not_isSimpleModule` (issue 0150). -/
theorem exists_monoidHom_scalar_of_finrank_eq_one
    {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {Q : Type*} [Group Q]
    (ρ : Representation K Q N) {W : Submodule K N} (hW : finrank K W = 1)
    (hinv : ∀ g : Q, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ χ : Q →* K, ∀ (g : Q) (x : N), x ∈ W → ρ g x = χ g • x := by
  classical
  obtain ⟨v, hv0, -⟩ := finrank_eq_one_iff'.mp hW
  have hvW : (v : N) ∈ W := v.2
  have hvne : (v : N) ≠ 0 := fun h => hv0 (Subtype.ext h)
  have huniq : ∀ c c' : K, c • (v : N) = c' • (v : N) → c = c' := by
    intro c c' h
    have hsub : (c - c') • (v : N) = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with h1 | h2
    · linear_combination (norm := ring_nf) h1
    · exact absurd h2 hvne
  have hex : ∀ g : Q, ∃ c : K, ∀ x ∈ W, ρ g x = c • x := fun g =>
    exists_scalar_of_finrank_eq_one_of_mapsTo hW (ρ g) (hinv g)
  set c : Q → K := fun g => (hex g).choose with hc_def
  have hc : ∀ (g : Q) (x : N), x ∈ W → ρ g x = c g • x := fun g => (hex g).choose_spec
  have hone : c 1 = 1 := by
    refine huniq _ _ ?_
    rw [← hc 1 v hvW, map_one]
    simp
  have hmul : ∀ g h : Q, c (g * h) = c g * c h := by
    intro g h
    refine huniq _ _ ?_
    have h1 : ρ (g * h) (v : N) = c (g * h) • (v : N) := hc _ v hvW
    have h2 : ρ (g * h) (v : N) = ρ g (ρ h (v : N)) := by rw [map_mul]; rfl
    have h3 : ρ h (v : N) = c h • (v : N) := hc h v hvW
    have h4 : ρ g (c h • (v : N)) = c h • (c g • (v : N)) := by
      rw [map_smul, hc g v hvW]
    rw [← h1, h2, h3, h4, smul_smul, mul_comm]
  exact ⟨⟨⟨c, hone⟩, fun {g h} => hmul g h⟩, hc⟩

end OddOrder.RepresentationTheory
