/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.RepresentationTheory.WielandtKernelFPF
import OddOrder.GroupTheory.RepresentationTheory.BaseChange
import OddOrder.GroupTheory.WielandtPerFactorDischarge
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Field.ZMod

/-!
# Peterfalvi (9.1): the kernel-FPF identity (†) over `𝔽_p`, via base change

The chief-factor dimension identity (⋆) `WielandtCounting.finrank_elab_identity` reduces to the
kernel-FPF fact (†) over the prime field `𝔽_p = ZMod p`:

`dim [V,U] = |E| · dim ([V,U] ⊓ Vᴱ)`            (the `htag` of `finrank_elab_identity`).

But the Brauer-free free-orbit count
`WielandtKernelFPF.finrank_eq_card_mul_finrank_invariants_kernelFPF` needs the field to be
**algebraically closed** (so `𝔽̄_p[U]` is split semisimple).  This file bridges the two by **base
change** along `𝔽_p → 𝔽̄_p = AlgebraicClosure (ZMod p)`:

* the augmentation submodule `[V,U] = ker (averageMap ρ|_U)` is `L`-invariant, so it is a
  subrepresentation `ρ_W`;
* `ρ_W` has no `U`-invariants (`[V,U]ᵁ = 0`), a property preserved by base change
  (`invariants_baseChangeRepresentation_eq_bot`);
* (†) over `𝔽̄_p` gives `dim_{𝔽̄_p} (𝔽̄_p ⊗ [V,U]) = |E| · dim_{𝔽̄_p} (𝔽̄_p ⊗ [V,U])ᴱ`, and base
  change preserves both dimensions (`Module.finrank_baseChange`,
  `finrank_invariants_baseChangeRepresentation`);
* a `Submodule.map` of the `E`-invariants of `ρ_W` identifies `[V,U]ᴱ` with `[V,U] ⊓ Vᴱ`.

`htag_of_frobenius` is the resulting (†) over `𝔽_p`; `WielandtCounting.finrank_elab_identity` then
yields the per-chief-factor identity, closing the lone `sorry` of `wielandt_fixedPoint_frobenius`.

`notes/peterfalvi/s11_wielandt_91_design.md` (NEXT — carrier-level, items 3 + assembly), issue 2014.
-/

namespace OddOrder.GroupTheory.WielandtKernelFPF

open Module Representation
open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_comp
  invariants_baseChangeRepresentation_eq_bot finrank_invariants_baseChangeRepresentation)
open OddOrder.GroupTheory.WielandtCounting (ker_averageMap_comp_invariant
  eq_zero_of_mem_ker_averageMap_of_mem_invariants)

variable {L : Type*} [Group L] [Finite L]

/-- **The kernel-FPF dimension identity (†) over the prime field `𝔽_p`, full-module form.**  For
`U ◁ L` with `p ∤ |U|`, `E ≤ L` with `U ⊔ E = ⊤`, `|E| ⟂ |U|`, the conjugation action of `E` on `U`
fixed-point-free, and a finite-dimensional `𝔽_p[L]`-module `V` with no `U`-invariants (`Vᵁ = 0`):

`dim V = |E| · dim Vᴱ`.

No hypothesis relates `p` and `|E|` (the underlying count is characteristic-free).  This is the
form consumed by Peterfalvi Part II, Ch. II step (3) ([Is] Theorem 15.16 there): `M` a minimal
`KP`-invariant elementary abelian `r`-subgroup with the Frobenius kernel `K` acting
fixed-point-freely, so `dim M = |P| · dim C_M(P)` — where `r ≠ |P|` is a *conclusion* of step (3),
not an available hypothesis.  Proved by base change to `𝔽̄_p`, where
`finrank_eq_card_mul_finrank_invariants_kernelFPF` applies. -/
theorem finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod {U E : Subgroup L} [U.Normal]
    [Fintype ↥E] {p : ℕ} [Fact p.Prime]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (ρV : Representation (ZMod p) L V)
    (hVU : invariants (ρV.comp U.subtype) = ⊥) :
    Module.finrank (ZMod p) V =
      Fintype.card ↥E * Module.finrank (ZMod p) ↥(invariants (ρV.comp E.subtype)) := by
  let K := AlgebraicClosure (ZMod p)
  haveI : NeZero (Nat.card ↥U : K) :=
    ⟨fun h => hpU ((CharP.cast_eq_zero_iff K p _).mp h)⟩
  have hbarU : invariants ((baseChangeRepresentation K ρV).comp U.subtype) = ⊥ := by
    rw [← baseChangeRepresentation_comp]
    exact invariants_baseChangeRepresentation_eq_bot K (ρV.comp U.subtype) hVU
  have hkey := finrank_eq_card_mul_finrank_invariants_kernelFPF (baseChangeRepresentation K ρV)
    (U := U) (E := E) hsup hcopUE hEnt hfpf hbarU
  rwa [Module.finrank_baseChange, ← baseChangeRepresentation_comp,
    finrank_invariants_baseChangeRepresentation] at hkey

/-- **Peterfalvi (9.1), the kernel-FPF identity (†) over `𝔽_p`.**  For `U ◁ L` a `p′`-group, `E ≤ L`
with `U ⊔ E = ⊤`, `|E| ⟂ |U|`, the conjugation action of `E` on `U` fixed-point-free, and a
finite-dimensional `𝔽_p[L]`-module `V`:

`dim [V,U] = |E| · dim ([V,U] ⊓ Vᴱ)`,   where `[V,U] = ker (averageMap ρ|_U)`.

This is the `htag` hypothesis of `WielandtCounting.finrank_elab_identity`.  Proved by base change to
`𝔽̄_p`, where `finrank_eq_card_mul_finrank_invariants_kernelFPF` applies. -/
theorem htag_of_frobenius {U E : Subgroup L} [U.Normal] [Fintype ↥E]
    {p : ℕ} [Fact p.Prime] [Fintype ↥U] [Invertible (Fintype.card ↥U : ZMod p)]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρV : Representation (ZMod p) L V) :
    Module.finrank (ZMod p) ↥(LinearMap.ker (averageMap (ρV.comp U.subtype))) =
      Fintype.card ↥E * Module.finrank (ZMod p)
        ↥(LinearMap.ker (averageMap (ρV.comp U.subtype)) ⊓ invariants (ρV.comp E.subtype)) := by
  classical
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  -- Make the augmentation submodule `[V,U]` opaque (its defining `averageMap` is `whnf`-heavy).
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : Submodule (ZMod p) V,
      W₀ = LinearMap.ker (averageMap (ρV.comp U.subtype)) := ⟨_, rfl⟩
  rw [← hW₀]
  -- `W₀ = [V,U]` is `L`-invariant, so it is a subrepresentation `ρ_W`.
  have hinv : ∀ g : L, W₀ ≤ W₀.comap (ρV g) := by
    intro g x hx
    rw [hW₀] at hx ⊢
    rw [Submodule.mem_comap]
    exact ker_averageMap_comp_invariant ρV U g x hx
  let ρW : Representation (ZMod p) L ↥W₀ := ρV.subrepresentation W₀ hinv
  -- The action of `ρ_W` reads off the ambient action on representatives.
  have hρWval : ∀ (g : L) (w : ↥W₀), ((ρW g w : ↥W₀) : V) = ρV g (w : V) := fun g w => rfl
  -- (B) `W₀ = [V,U]` has no `U`-invariants.
  have hWUbot : invariants (ρW.comp U.subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    have hwV_inv : (w : V) ∈ invariants (ρV.comp U.subtype) := fun u => by
      have h : ((ρW (U.subtype u) w : ↥W₀) : V) = (w : V) := congrArg Subtype.val (hw u)
      rw [hρWval] at h; exact h
    have hwV_ker : (w : V) ∈ LinearMap.ker (averageMap (ρV.comp U.subtype)) := hW₀ ▸ w.2
    exact Subtype.ext (eq_zero_of_mem_ker_averageMap_of_mem_invariants
      (ρV.comp U.subtype) hwV_ker hwV_inv)
  -- (†) over `𝔽_p` for the subrepresentation `ρ_W` (base change happens inside).
  have hkey := finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod
    hsup hcopUE hEnt hfpf hpU ρW hWUbot
  -- `dim [V,U] = |E| · dim ([V,U]ᴱ)`; identify `[V,U]ᴱ` with `[V,U] ⊓ Vᴱ`.
  have hbridge : (invariants (ρW.comp E.subtype)).map W₀.subtype
      = W₀ ⊓ invariants (ρV.comp E.subtype) := by
    ext v
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, fun e => ?_⟩
      have h : ((ρW (E.subtype e) w : ↥W₀) : V) = (w : V) := congrArg Subtype.val (hw e)
      rw [hρWval] at h; exact h
    · rintro ⟨hvW, hvE⟩
      refine ⟨⟨v, hvW⟩, fun e => ?_, rfl⟩
      apply Subtype.ext
      change ((ρW (E.subtype e) ⟨v, hvW⟩ : ↥W₀) : V) = v
      rw [hρWval]; exact hvE e
  rw [hkey, ← Submodule.finrank_map_subtype_eq W₀ (invariants (ρW.comp E.subtype)), hbridge]

open OddOrder.GroupTheory (fixedSubgroup elabRepresentation elabRepresentation_apply
  card_fixedSubgroup_eq_pow_finrank) in
/-- **Group-cardinality form of the kernel-FPF identity (†)** ([Is] Theorem 15.16).  For a
finite group `L`, `U ◁ L` with `p ∤ |U|`, `E ≤ L` with `U ⊔ E = ⊤` and `|E| ⟂ |U|` acting
fixed-point-freely on `U`, and an elementary abelian `p`-group `V` (its `ZMod p`-module
structure on `Additive V` given as an instance) acted on by `φ : L →* MulAut V` with
`C_V(U) = 1`:

`|V| = |C_V(E)|^{|E|}`.

No hypothesis relates `p` and `|E|`.  This is the form consumed by Peterfalvi Part II, Ch. II
step (3): `M` a `KP`-invariant elementary abelian `r`-subgroup with the Frobenius kernel `K`
acting fixed-point-freely gives `|M| = |C_M(P)|^{|P|}` — with `r ≠ |P|` only a *conclusion* of
step (3), not an available hypothesis. -/
theorem card_eq_card_fixedSubgroup_pow_of_frobenius {U E : Subgroup L} [U.Normal]
    {p : ℕ} [Fact p.Prime]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U))
    (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [CommGroup V] [Module (ZMod p) (Additive V)] [Finite V]
    (φ : L →* MulAut V)
    (hVU : fixedSubgroup φ U = ⊥) :
    Nat.card V = Nat.card ↥(fixedSubgroup φ E) ^ Nat.card ↥E := by
  classical
  haveI : Fintype ↥E := Fintype.ofFinite _
  haveI : FiniteDimensional (ZMod p) (Additive V) := Module.Finite.of_finite
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  -- `V^U = 0` in module form, from `C_V(U) = 1`.
  have hinvU : invariants ((elabRepresentation p φ).comp U.subtype) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hmem : Additive.toMul v ∈ fixedSubgroup φ U := by
      intro l hl
      have h1 := (mem_invariants _ _).mp hv ⟨l, hl⟩
      have h2 : (elabRepresentation p φ) l (Additive.ofMul (Additive.toMul v)) =
          Additive.ofMul (φ l (Additive.toMul v)) :=
        elabRepresentation_apply p φ l (Additive.toMul v)
      rw [ofMul_toMul] at h2
      have h3 : Additive.ofMul (φ l (Additive.toMul v)) = v := by
        rw [← h2]; exact h1
      have h4 := congrArg Additive.toMul h3
      rwa [toMul_ofMul] at h4
    rw [hVU, Subgroup.mem_bot] at hmem
    calc v = Additive.ofMul (Additive.toMul v) := (ofMul_toMul v).symm
      _ = Additive.ofMul (1 : V) := by rw [hmem]
      _ = 0 := ofMul_one
  -- (†) over `𝔽_p` and the cardinality bridges.
  have hkey := finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod
    hsup hcopUE hEnt hfpf hpU (elabRepresentation p φ) hinvU
  haveI : Fintype (Additive V) := Fintype.ofFinite _
  have hcardV : Nat.card V = p ^ Module.finrank (ZMod p) (Additive V) := by
    rw [Nat.card_congr (Additive.ofMul (α := V)), Nat.card_eq_fintype_card,
      Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hfixE := card_fixedSubgroup_eq_pow_finrank p φ E
  rw [hcardV, hkey, pow_mul', ← hfixE, Nat.card_eq_fintype_card (α := ↥E)]

/-- **Peterfalvi (9.1), the per-chief-factor dimension identity (⋆)** from the Frobenius data.  For
the elementary-abelian representation `elabRepresentation p φ` of `L = U ⋊ E` (Frobenius) on a
finite
`𝔽_p`-module `V` (`p ∤ |U|, |E|`), the dimension identity `WielandtDimIdentity p φ U E` holds.

This is `WielandtCounting.finrank_elab_identity` discharged by the kernel-FPF fact (†)
`htag_of_frobenius`.  Stated with the `𝔽_p`-module as an instance *binder* (not `letI`-bound) so the
`↥(Submodule …)` coercions resolve once here and survive substitution of the concrete chief-factor
module `Additive ↥N` — the same device piece C uses for `WielandtDimIdentity` (avoiding the
`Additive ↥N` diamond). -/
theorem wielandtDimIdentity_of_frobenius {U E : Subgroup L} [U.Normal] [Fintype ↥E]
    {p : ℕ} [Fact p.Prime] [Fintype ↥U] [Invertible (Fintype.card ↥U : ZMod p)]
    (hsup : U ⊔ E = ⊤) (hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U)) (hEnt : 1 < Nat.card ↥E)
    (hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1)
    (hpU : ¬ p ∣ Nat.card ↥U)
    {V : Type*} [CommGroup V] [Module (ZMod p) (Additive V)] [Finite V] (φ : L →* MulAut V) :
    WielandtDimIdentity p φ U E :=
  WielandtCounting.finrank_elab_identity (elabRepresentation p φ) U E hsup
    (htag_of_frobenius hsup hcopUE hEnt hfpf hpU (elabRepresentation p φ))

end OddOrder.GroupTheory.WielandtKernelFPF
