/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.SingerField
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Maschke

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

/-- **Two line-characters detect the whole action.**  If `W₁ ⊔ W₂ = ⊤` and `ρ g` acts on `Wᵢ` by
the scalar `χᵢ g`, then `χ₁ g = χ₂ g = 1` forces `ρ g = 1`: every `x` is `y + z` with `y ∈ W₁`,
`z ∈ W₂`, and both summands are fixed.

Combined with faithfulness this is what makes the pair `(χ₁, χ₂)` injective on `Q` — the step that
turns BG Lemma 2.7's rank-`2` action into an embedding `Q ↪ μ_q × μ_q` (issue 0150). -/
theorem eq_one_of_scalars_eq_one_of_sup_eq_top
    {K N : Type*} [Field K] [AddCommGroup N] [Module K N] {Q : Type*} [Group Q]
    (ρ : Representation K Q N) {W₁ W₂ : Submodule K N} (hsup : W₁ ⊔ W₂ = ⊤)
    {χ₁ χ₂ : Q →* K}
    (h₁ : ∀ (g : Q) (x : N), x ∈ W₁ → ρ g x = χ₁ g • x)
    (h₂ : ∀ (g : Q) (x : N), x ∈ W₂ → ρ g x = χ₂ g • x)
    {g : Q} (hg₁ : χ₁ g = 1) (hg₂ : χ₂ g = 1) :
    ρ g = 1 := by
  ext x
  have hx : x ∈ W₁ ⊔ W₂ := hsup ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, h₁ g y hy, h₂ g z hz, hg₁, hg₂, one_smul, one_smul]
  simp

/-- **A nontrivial `q`-th root of unity in `𝔽_p` forces `q ∣ p - 1`.**  If `c ^ q = 1` with
`c ≠ 1` and `q` prime, then `c` is a unit of multiplicative order exactly `q` (the order divides
the prime `q` and is not `1`), so `q` divides `|𝔽_p^×| = p - 1`.

This is conclusion (a) of BG Lemma 2.7 once a nontrivial line-character has been produced: the
character values are `q`-th roots of unity because `Q` has exponent `q` (issue 0150). -/
theorem prime_dvd_sub_one_of_pow_eq_one {p q : ℕ} [Fact p.Prime] (hq : q.Prime) {c : ZMod p}
    (hcq : c ^ q = 1) (hc1 : c ≠ 1) : q ∣ p - 1 := by
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_pow hq.ne_zero] at hcq
    exact zero_ne_one hcq
  lift c to (ZMod p)ˣ using isUnit_iff_ne_zero.mpr hc0 with u hu
  have huq : u ^ q = 1 := by ext; push_cast; exact hcq
  have hu1 : u ≠ 1 := fun h => hc1 (by rw [h]; rfl)
  have hord : orderOf u = q := by
    have hdvd : orderOf u ∣ q := orderOf_dvd_of_pow_eq_one huq
    rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hu1
    · exact h
  have hdvd := orderOf_dvd_natCard u
  rwa [hord, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (Fact.out : p.Prime)] at hdvd

-- `[Finite M]` *is* used (it feeds `Module.Finite.of_finite` for `M` and, through
-- `inferInstanceAs`, for the type synonym `ρ.asModule`, which is what Maschke's
-- `IsSemisimpleModule` instance needs); the linter only inspects the statement, so it
-- reports a false positive here.  Verified: adding `omit [Finite M]` breaks the build.
set_option linter.unusedSectionVars false in
open Module in
/-- **Transport of the two lines from `ρ.asModule` to `M`.**  Under Maschke's hypothesis
(`NeZero (Nat.card Q : ZMod p)`, i.e. `|Q|` invertible in the coefficient field), a `2`-dimensional
representation whose group-algebra module is *not* simple decomposes as two `ρ`-invariant lines of
`M` spanning it.

`exists_isCompl_finrank_one_of_not_isSimpleModule` produces the pair inside the type synonym
`ρ.asModule`; `Representation.asModuleEquiv` carries them back to `M`, preserving `finrank`
(`LinearEquiv.finrank_map_eq`) and `⊔` (`Submodule.map_sup` + `Submodule.map_top`).  Invariance
under `ρ g` is the group-algebra action of `MonoidAlgebra.of _ _ g`, matched via
`asModuleEquiv_map_smul` and `asAlgebraHom_single_one`.

This is the `M`-side form BG Lemma 2.7 works with: the two lines carry the characters `χ₁, χ₂`
of `exists_monoidHom_scalar_of_finrank_eq_one` (issue 0150). -/
theorem exists_invariant_lines_of_not_isSimpleModule
    (ρ : Representation (ZMod p) Q M) [NeZero (Nat.card Q : ZMod p)]
    (hrank : finrank (ZMod p) M = 2)
    (hnot : ¬ IsSimpleModule (MonoidAlgebra (ZMod p) Q) ρ.asModule) :
    ∃ W₁ W₂ : Submodule (ZMod p) M, W₁ ⊔ W₂ = ⊤ ∧
      finrank (ZMod p) W₁ = 1 ∧ finrank (ZMod p) W₂ = 1 ∧
      (∀ g : Q, ∀ x ∈ W₁, ρ g x ∈ W₁) ∧ (∀ g : Q, ∀ x ∈ W₂, ρ g x ∈ W₂) := by
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  haveI : Finite ρ.asModule := inferInstanceAs (Finite M)
  haveI : Module.Finite (ZMod p) ρ.asModule := Module.Finite.of_finite
  have hrank' : finrank (ZMod p) ρ.asModule = 2 := by
    rw [ρ.asModuleEquiv.finrank_eq]; exact hrank
  obtain ⟨N₁, N₂, hcompl, h1, h2⟩ :=
    exists_isCompl_finrank_one_of_not_isSimpleModule (K := ZMod p)
      (R := MonoidAlgebra (ZMod p) Q) (N := ρ.asModule) hrank' hnot
  refine ⟨Submodule.map (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod p] M)
            (N₁.restrictScalars (ZMod p)),
          Submodule.map (ρ.asModuleEquiv : ρ.asModule →ₗ[ZMod p] M)
            (N₂.restrictScalars (ZMod p)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Submodule.map_sup]
    have hsup : N₁.restrictScalars (ZMod p) ⊔ N₂.restrictScalars (ZMod p) = ⊤ := by
      rw [← Submodule.restrictScalars_sup, hcompl.sup_eq_top]; rfl
    rw [hsup, Submodule.map_top, LinearEquiv.range]
  · rw [LinearEquiv.finrank_map_eq]; exact h1
  · rw [LinearEquiv.finrank_map_eq]; exact h2
  · intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MonoidAlgebra.of (ZMod p) Q) g • y, N₁.smul_mem _ hy, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one]
  · intro g x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MonoidAlgebra.of (ZMod p) Q) g • y, N₂.smul_mem _ hy, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [Representation.asModuleEquiv_map_smul, MonoidAlgebra.of_apply,
      Representation.asAlgebraHom_single_one]

open Module in
/-- **BG Lemma 2.7(a)** (Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, p. 31).
Let `p ≠ q` be primes and let a group `Q` of order `q²` and exponent `q` — i.e. `Q ≅ (ℤ/q)²` —
act faithfully and `𝔽_p`-linearly on a `2`-dimensional `𝔽_p`-space `M`.  Then `q ∣ p - 1`.

The book's argument, assembled from the pieces above:

* `Q` is not cyclic (`not_isCyclic_of_exponent_of_card_sq`), so by the Singer order bound the
  action is *reducible* (`Representation.not_isSimpleModule_asModule_of_not_isCyclic`);
* `q ≠ p` makes `|Q| = q²` invertible in `𝔽_p`, so Maschke splits `M` into two invariant lines
  (`exists_invariant_lines_of_not_isSimpleModule`), each carrying a character
  `χᵢ : Q →* 𝔽_p` (`exists_monoidHom_scalar_of_finrank_eq_one`);
* the characters cannot both be trivial — that would make the action trivial and `Q` a one-element
  group (`eq_one_of_scalars_eq_one_of_sup_eq_top` plus faithfulness), contradicting `|Q| = q²`;
* a nontrivial value is a `q`-th root of unity (`Q` has exponent `q`), so `q ∣ p - 1`
  (`prime_dvd_sub_one_of_pow_eq_one`).

Part (b) — some `α ∈ Q^#` acts as a power map `x ↦ x^r` — is the diagonal element of the
resulting isomorphism `Q ≅ μ_q × μ_q` (issue 0150). -/
theorem prime_dvd_sub_one_of_faithful_rank_two {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hrank : finrank (ZMod p) M = 2)
    (hQexp : ∀ x : Q, x ^ q = 1) (hQcard : Nat.card Q = q ^ 2)
    (ρ : Representation (ZMod p) Q M) (hfaith : Function.Injective ρ) :
    q ∣ p - 1 := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (Nat.card Q : ZMod p) := by
    refine ⟨?_⟩
    rw [hQcard, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm
  have hnc := not_isCyclic_of_exponent_of_card_sq hq hQexp hQcard
  have hnot := Representation.not_isSimpleModule_asModule_of_not_isCyclic ρ hfaith hnc
  obtain ⟨W₁, W₂, hsup, h1, h2, hinv1, hinv2⟩ :=
    exists_invariant_lines_of_not_isSimpleModule ρ hrank hnot
  obtain ⟨χ₁, hχ₁⟩ := exists_monoidHom_scalar_of_finrank_eq_one ρ h1 hinv1
  obtain ⟨χ₂, hχ₂⟩ := exists_monoidHom_scalar_of_finrank_eq_one ρ h2 hinv2
  have hpow : ∀ (χ : Q →* ZMod p) (g : Q), (χ g) ^ q = 1 := by
    intro χ g
    rw [← map_pow, hQexp g, map_one]
  by_cases hboth : ∀ g : Q, χ₁ g = 1 ∧ χ₂ g = 1
  · exfalso
    have hall : ∀ g : Q, g = 1 := fun g => hfaith (by
      rw [eq_one_of_scalars_eq_one_of_sup_eq_top ρ hsup hχ₁ hχ₂ (hboth g).1 (hboth g).2, map_one])
    haveI hss : Subsingleton Q := ⟨fun a b => by rw [hall a, hall b]⟩
    have hcard1 : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hss, ⟨1⟩⟩
    rw [hQcard] at hcard1
    nlinarith [hq.two_le]
  · push Not at hboth
    obtain ⟨g, hg⟩ := hboth
    by_cases h1' : χ₁ g = 1
    · exact prime_dvd_sub_one_of_pow_eq_one hq (hpow χ₂ g) (hg h1')
    · exact prime_dvd_sub_one_of_pow_eq_one hq (hpow χ₁ g) h1'

open Module in
/-- **BG Lemma 2.7(b)** (Bender–Glauberman, p. 31).  In the situation of
`prime_dvd_sub_one_of_faithful_rank_two`, some `α ∈ Q^#` acts as a **power map**: there is
`r : 𝔽_p` with `r ^ q = 1`, `r ≠ 1` and `ρ α x = r • x` for *every* `x` (not just on one line).

Rather than building the isomorphism `Q ≅ μ_q × μ_q` and taking its diagonal, the proof looks at
the quotient character `ψ = χ₁ / χ₂ : Q →* 𝔽_p^×`.  Its values are `q`-th roots of unity, so its
range — a subgroup of the cyclic group `𝔽_p^×` — has order dividing `q`; with `|Q| = q²` the
kernel therefore has order at least `q ≥ 2`.  Any `α ≠ 1` in that kernel has `χ₁ α = χ₂ α =: r`,
hence acts as `r` on both lines and so on all of `M = W₁ ⊔ W₂`; and `r ≠ 1`, since `r = 1` would
make `ρ α = 1` and `α = 1` by faithfulness.

Together with part (a) this completes BG Lemma 2.7 (issue 0150). -/
theorem exists_powerMap_of_faithful_rank_two {q : ℕ}
    (hq : q.Prime) (hqp : q ≠ p) (hrank : finrank (ZMod p) M = 2)
    (hQexp : ∀ x : Q, x ^ q = 1) (hQcard : Nat.card Q = q ^ 2)
    (ρ : Representation (ZMod p) Q M) (hfaith : Function.Injective ρ) :
    ∃ α : Q, α ≠ 1 ∧ ∃ r : ZMod p, r ^ q = 1 ∧ r ≠ 1 ∧ ∀ x : M, ρ α x = r • x := by
  have hp := (Fact.out : p.Prime)
  haveI : NeZero (Nat.card Q : ZMod p) := by
    refine ⟨?_⟩
    rw [hQcard, Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm
  have hnc := not_isCyclic_of_exponent_of_card_sq hq hQexp hQcard
  have hnot := Representation.not_isSimpleModule_asModule_of_not_isCyclic ρ hfaith hnc
  obtain ⟨W₁, W₂, hsup, h1, h2, hinv1, hinv2⟩ :=
    exists_invariant_lines_of_not_isSimpleModule ρ hrank hnot
  obtain ⟨χ₁, hχ₁⟩ := exists_monoidHom_scalar_of_finrank_eq_one ρ h1 hinv1
  obtain ⟨χ₂, hχ₂⟩ := exists_monoidHom_scalar_of_finrank_eq_one ρ h2 hinv2
  set u₁ := χ₁.toHomUnits with hu₁
  set u₂ := χ₂.toHomUnits with hu₂
  set ψ : Q →* (ZMod p)ˣ := u₁ / u₂ with hψ
  -- every value of `ψ` is a `q`-th root of unity
  have hψq : ∀ g : Q, (ψ g) ^ q = 1 := by
    intro g
    have h1' : (u₁ g) ^ q = 1 := by rw [← map_pow, hQexp g, map_one]
    have h2' : (u₂ g) ^ q = 1 := by rw [← map_pow, hQexp g, map_one]
    rw [hψ]
    simp only [MonoidHom.div_apply, div_pow, h1', h2', div_one]
  -- so the range has order dividing `q`
  have hrange : Nat.card ψ.range ∣ q := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ψ.range)
    rw [← hg]
    refine orderOf_dvd_of_pow_eq_one ?_
    obtain ⟨x, hx⟩ := g.2
    ext
    push_cast
    rw [← hx]
    exact congrArg Units.val (hψq x)
  -- `|ker ψ| · |range ψ| = q²` with `|range ψ| ≤ q`, so `|ker ψ| ≥ q ≥ 2`
  have hcard : Nat.card ψ.ker * Nat.card ψ.range = q ^ 2 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hQcard]
  have hle : Nat.card ψ.range ≤ q := Nat.le_of_dvd hq.pos hrange
  have hkerge : q ≤ Nat.card ψ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card ψ.ker * Nat.card ψ.range < q * q := by
      exact Nat.mul_lt_mul_of_lt_of_le hlt hle hq.pos
    rw [hcard, pow_two] at this
    omega
  have hex : ∃ x : ψ.ker, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    haveI hss : Subsingleton ψ.ker := ⟨fun a b => by rw [hcon a, hcon b]⟩
    have h1card : Nat.card ψ.ker = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hss, ⟨1⟩⟩
    have := hq.two_le
    omega
  obtain ⟨⟨α, hαker⟩, hα1⟩ := hex
  have hαne : α ≠ 1 := fun h => hα1 (Subtype.ext h)
  -- on the kernel the two characters agree
  have hagree : χ₁ α = χ₂ α := by
    have : ψ α = 1 := hαker
    rw [hψ] at this
    simp only [MonoidHom.div_apply, div_eq_one] at this
    exact congrArg Units.val this
  refine ⟨α, hαne, χ₁ α, by rw [← map_pow, hQexp α, map_one], ?_, ?_⟩
  · intro hr
    exact hαne (hfaith (by
      rw [eq_one_of_scalars_eq_one_of_sup_eq_top ρ hsup hχ₁ hχ₂ hr (hagree ▸ hr), map_one]))
  · intro x
    have hx : x ∈ W₁ ⊔ W₂ := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hχ₁ α y hy, hχ₂ α z hz, ← hagree, smul_add]

end OddOrder.RepresentationTheory
