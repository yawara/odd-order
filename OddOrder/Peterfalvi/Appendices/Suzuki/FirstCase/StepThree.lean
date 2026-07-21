/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepOne
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.StepTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.Q1MinimalInvariant
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabFrobenius
import OddOrder.GroupTheory.RepresentationTheory.WielandtElabBridge
import OddOrder.Peterfalvi.Appendices.Huppert

/-!
# Peterfalvi Part II, Ch. II, step (3): the dimension identity for `M`

T. Peterfalvi, *Character Theory for the Odd Order Theorem* (LMS LNS 272,
2000), Part II, Ch. II, (3), p. 109.

For an elementary abelian `r`-subgroup `M ≤ Q` normalized by `KP`, the
kernel-FPF dimension identity ([Is] Theorem 15.16; here
`finrank_eq_card_mul_finrank_invariants_kernelFPF_zmod`) gives

`dim M = p · dim C_M(P)`,   i.e.   `|M| = |C_M(P)|^p`.

The hypotheses of the identity are supplied by Chapter I and step (1):

* `KP` is a Frobenius group with kernel `K`: `C_K(a) = 1` for `a ∈ P^#`
  is step (1)'s `C_K(P) = 1` (`K_inf_centralizer_eq_bot`), since `P` has
  prime order;
* `K` acts fixed-point-freely on `M ≤ Q` (§2 Proposition 1(a),
  `conjQByK_fixed_eq_one`), so `M^K = 0`;
* `(|E|, |U|) = (p, 2^p - 1)` are coprime (Fermat: `p ∤ 2^p - 1`);
* `r ∤ |K|`, since `r ∣ |M| ∣ |Q|` and `(|Q|, |K|) = 1`
  (`coprime_card_Q_K`).

No `r ≠ p` hypothesis is needed — the identity is characteristic-free in
`|E|`; the book obtains `r ≠ p` only as a *consequence* of the congruence
`r ≡ 2^i (mod 2^p - 1)` at the end of step (3).

As a corollary, `C_M(P) ≠ 1` for `M ≠ 1` — the book's opening Frobenius
argument for `C_M(P) ≠ 0` is subsumed by the identity itself.
-/

set_option autoImplicit false

namespace OddOrder.Peterfalvi.Appendices.Suzuki

open OddOrder.GroupTheory (IsElementaryAbelian fixedSubgroup elabRepresentation)
open OddOrder.Isaacs.Ch01 (fitting)
open Representation

/-! ## Clifford counting: `|M| = |V|^t` for a minimal `K`-invariant subgroup

The counting content of Clifford's theorem ([Is] Theorem 6.5) needed by step
(3), with no semisimple-module machinery: for an action `φ : L →* MulAut M`
on a finite abelian group `M` admitting no proper nontrivial invariant
subgroup, `K ◁ L`, and `V` a *minimal* nontrivial `K`-invariant subgroup,
every `L`-translate of `V` is again a minimal nontrivial `K`-invariant
subgroup; a maximal `K`-invariant subgroup of `|V|`-power order absorbs every
translate (a missed translate meets it trivially by minimality, and the join
would have strictly larger `|V|`-power order), and the join of all translates
is `L`-invariant, hence everything.  Thus `|M| = |V|^t`. -/

section CliffordCounting

open OddOrder.Isaacs.Ch03
open Pointwise

variable {M : Type*} [CommGroup M] [Finite M]
variable {L : Type*} [Group L] {φ : L →* MulAut M} {K : Subgroup L}

omit [Finite M] in
/-- Cancellation of a translate pair `g * h = 1`:
`(B^{φ h})^{φ g} = B`. -/
theorem map_aut_map_aut_of_mul_eq_one {g h : L} (hgh : g * h = 1)
    (B : Subgroup M) :
    (B.map (φ h).toMonoidHom).map (φ g).toMonoidHom = B := by
  have hcancel : ∀ x : M, (φ g) ((φ h) x) = x := by
    intro x
    rw [← MulAut.mul_apply, ← map_mul, hgh, map_one, MulAut.one_apply]
  ext x
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    simpa only [MulEquiv.coe_toMonoidHom, hcancel, SetLike.mem_coe] using hb
  · intro hx
    exact ⟨(φ h) x, ⟨x, hx, rfl⟩, hcancel x⟩

omit [Finite M] in
/-- The `φ g`-translate of a `K`-invariant subgroup is `K`-invariant when
`K ◁ L`. -/
theorem isAInvariant_map_of_normal [K.Normal] {V : Subgroup M}
    (hV : IsAInvariant (φ.comp K.subtype) V) (g : L) :
    IsAInvariant (φ.comp K.subtype) (V.map (φ g).toMonoidHom) := by
  rw [isAInvariant_iff_smul_mem]
  rintro k _ ⟨v, hv, rfl⟩
  have hk' : g⁻¹ * (k : L) * g ∈ K :=
    Subgroup.Normal.conj_mem' ‹K.Normal› _ k.2 g
  refine ⟨(φ (g⁻¹ * (k : L) * g)) v,
    hV.smul_mem (⟨_, hk'⟩ : ↥K) hv, ?_⟩
  change (φ g) ((φ (g⁻¹ * (k : L) * g)) v) = (φ ((k : L))) ((φ g) v)
  rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul]
  congr 1
  group

omit [Finite M] in
/-- Minimality among nontrivial `K`-invariant subgroups transports along
`φ g`-translates. -/
theorem minimal_map_of_normal [K.Normal] {V : Subgroup M}
    (hVmin : ∀ B ≤ V, IsAInvariant (φ.comp K.subtype) B → B ≠ ⊥ → B = V)
    (g : L) :
    ∀ B ≤ V.map (φ g).toMonoidHom, IsAInvariant (φ.comp K.subtype) B →
      B ≠ ⊥ → B = V.map (φ g).toMonoidHom := by
  intro B hBle hBinv hBne
  have hg1 : g⁻¹ * g = 1 := inv_mul_cancel g
  have hg2 : g * g⁻¹ = 1 := mul_inv_cancel g
  have h1 : B.map (φ g⁻¹).toMonoidHom ≤ V := by
    have hmono := Subgroup.map_mono (f := (φ g⁻¹).toMonoidHom) hBle
    rwa [map_aut_map_aut_of_mul_eq_one hg1] at hmono
  have h2 : IsAInvariant (φ.comp K.subtype) (B.map (φ g⁻¹).toMonoidHom) :=
    isAInvariant_map_of_normal hBinv g⁻¹
  have h3 : B.map (φ g⁻¹).toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hBne
    have := congrArg (Subgroup.map (φ g).toMonoidHom) hbot
    rwa [map_aut_map_aut_of_mul_eq_one hg2, Subgroup.map_bot] at this
  have h4 := hVmin _ h1 h2 h3
  have := congrArg (Subgroup.map (φ g).toMonoidHom) h4
  rwa [map_aut_map_aut_of_mul_eq_one hg2] at this

omit [Finite M] in
/-- Translates have the same cardinality. -/
theorem card_map_aut (V : Subgroup M) (g : L) :
    Nat.card ↥(V.map (φ g).toMonoidHom) = Nat.card ↥V :=
  (Nat.card_congr
    (Subgroup.equivMapOfInjective V _ (φ g).injective).toEquiv).symm

/-- **Clifford counting** ([Is] Theorem 6.5, counting form).  If the finite
abelian group `M` has no proper nontrivial `φ`-invariant subgroup and `V` is
a minimal nontrivial `K`-invariant subgroup for a normal `K ◁ L`, then
`|M| = |V|^t` for some `t`. -/
theorem exists_card_eq_pow_of_minimal_invariant [K.Normal]
    (hM : ∀ B : Subgroup M, IsAInvariant φ B → B ≠ ⊥ → B = ⊤)
    {V : Subgroup M} (hVne : V ≠ ⊥)
    (hVinv : IsAInvariant (φ.comp K.subtype) V)
    (hVmin : ∀ B ≤ V, IsAInvariant (φ.comp K.subtype) B → B ≠ ⊥ → B = V) :
    ∃ t : ℕ, Nat.card M = Nat.card ↥V ^ t := by
  classical
  haveI : Finite (Subgroup M) :=
    Finite.of_injective _ SetLike.coe_injective
  -- the family of `K`-invariant subgroups of `|V|`-power order
  set S : Set (Subgroup M) :=
    {J | IsAInvariant (φ.comp K.subtype) J ∧
      ∃ t : ℕ, Nat.card ↥J = Nat.card ↥V ^ t} with hSdef
  have hbotS : (⊥ : Subgroup M) ∈ S :=
    ⟨IsAInvariant.bot _, 0, by rw [Subgroup.card_bot, pow_zero]⟩
  obtain ⟨J, -, hJmax⟩ := Set.Finite.exists_le_maximal (Set.toFinite S) hbotS
  obtain ⟨hJinv, t, hJcard⟩ := hJmax.prop
  -- every translate is contained in the maximal `J`
  have htrans : ∀ g : L, V.map (φ g).toMonoidHom ≤ J := by
    intro g
    by_contra hng
    -- the missed translate meets `J` trivially, by transported minimality
    have hint : V.map (φ g).toMonoidHom ⊓ J = ⊥ := by
      by_contra hne
      have heq := minimal_map_of_normal hVmin g _ inf_le_left
        ((isAInvariant_map_of_normal hVinv g).inf hJinv) hne
      exact hng (heq ▸ inf_le_right)
    -- so the join has strictly larger `|V|`-power order: maximality violated
    have hprod : Nat.card ↥(J ⊔ V.map (φ g).toMonoidHom) *
        Nat.card ↥(J ⊓ V.map (φ g).toMonoidHom) =
        Nat.card ↥J * Nat.card ↥(V.map (φ g).toMonoidHom) := by
      have h_hk := Subgroup.card_HK_mul_card_inf_eq_card_mul_card
        J (V.map (φ g).toMonoidHom)
      rwa [show ((J : Set M) * (V.map (φ g).toMonoidHom : Set M)) =
          ((J ⊔ V.map (φ g).toMonoidHom : Subgroup M) : Set M) from
        (Subgroup.mul_normal J _).symm] at h_hk
    have hcard_sup : Nat.card ↥(J ⊔ V.map (φ g).toMonoidHom) =
        Nat.card ↥V ^ (t + 1) := by
      rw [inf_comm, hint, Subgroup.card_bot, mul_one, hJcard, card_map_aut]
        at hprod
      rw [hprod, pow_succ]
    have hSup_mem : (J ⊔ V.map (φ g).toMonoidHom) ∈ S :=
      ⟨hJinv.sup (isAInvariant_map_of_normal hVinv g), t + 1, hcard_sup⟩
    exact hng (le_sup_right.trans (hJmax.2 hSup_mem le_sup_left))
  -- the join of all translates is `φ`-invariant and nontrivial, hence `⊤`
  have hWtop : (⨆ g : L, V.map (φ g).toMonoidHom) = ⊤ := by
    apply hM
    · rw [isAInvariant_iff_smul_mem]
      intro a x hx
      refine Subgroup.iSup_induction
        (C := fun y => (φ a) y ∈ ⨆ g : L, V.map (φ g).toMonoidHom)
        _ hx (fun g y hy => ?_) ?_ ?_
      · -- `(φ a)` maps the `g`-translate into the `a * g`-translate
        obtain ⟨v, hv, rfl⟩ := hy
        refine Subgroup.mem_iSup_of_mem (a * g) ⟨v, hv, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, map_mul, MulAut.mul_apply]
      · rw [map_one]
        exact Subgroup.one_mem _
      · intro y z hy hz
        rw [map_mul]
        exact Subgroup.mul_mem _ hy hz
    · intro hbot
      apply hVne
      rw [eq_bot_iff]
      intro v hv
      have hmem : v ∈ V.map (φ (1 : L)).toMonoidHom := by
        refine ⟨v, hv, ?_⟩
        simp only [map_one, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
      have : v ∈ (⨆ g : L, V.map (φ g).toMonoidHom) :=
        Subgroup.mem_iSup_of_mem 1 hmem
      rw [hbot] at this
      exact this
  have hJtop : J = ⊤ :=
    le_antisymm le_top (hWtop ▸ iSup_le htrans)
  refine ⟨t, ?_⟩
  rw [← hJcard, hJtop]
  exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm

/-- A nontrivial invariant subgroup contains a *minimal* nontrivial invariant
subgroup (finiteness). -/
theorem exists_minimal_aInvariant_le {A : Type*} [Group A]
    {ψ : A →* MulAut M} {W : Subgroup M} (hWne : W ≠ ⊥)
    (hWinv : IsAInvariant ψ W) :
    ∃ V ≤ W, V ≠ ⊥ ∧ IsAInvariant ψ V ∧
      ∀ B ≤ V, IsAInvariant ψ B → B ≠ ⊥ → B = V := by
  classical
  haveI : Finite (Subgroup M) :=
    Finite.of_injective _ SetLike.coe_injective
  set S : Set (Subgroup M) := {B | B ≤ W ∧ B ≠ ⊥ ∧ IsAInvariant ψ B}
  have hWS : W ∈ S := ⟨le_rfl, hWne, hWinv⟩
  obtain ⟨V, -, hVmin⟩ := Set.Finite.exists_le_minimal (Set.toFinite S) hWS
  obtain ⟨hVle, hVne, hVinv⟩ := hVmin.prop
  refine ⟨V, hVle, hVne, hVinv, fun B hBV hBinv hBne => ?_⟩
  exact le_antisymm hBV (hVmin.2 ⟨hBV.trans hVle, hBne, hBinv⟩ hBV)

end CliffordCounting

/-! ## The Frobenius exponent: `Aut(𝔽_{2^p}) = ⟨x ↦ x²⟩`

The `𝔽_{2^p}`-side input to step (3)'s second branch: every ring automorphism
of a field of order `2^p` is a power of the Frobenius. -/

section FiniteFieldFrobenius

/-- Every ring automorphism of a finite field of order `2^p` is a power of the
Frobenius `x ↦ x²`, i.e. `σ x = x^(2^i)` for some `i`.

`σ` fixes the prime field `𝔽₂`, so it is a `ZMod 2`-algebra automorphism — an
element of `Gal(F/𝔽₂)`.  That group is cyclic of order `[F : 𝔽₂] = p` generated
by the Frobenius (`FiniteField.frobeniusAlgEquivOfAlgebraic`, whose order equals
`finrank`), so `σ = Frobenius^i` and hence `σ x = x^(2^i)`. -/
theorem ringAut_card_two_pow_eq_pow {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hcard : Nat.card F = 2 ^ p) (σ : RingAut F) :
    ∃ i : ℕ, ∀ x : F, σ x = x ^ (2 ^ i) := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFcard : Fintype.card F = 2 ^ p := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  haveI hchar : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := p) hFcard
  letI algF : Algebra (ZMod 2) F := ZMod.algebra F 2
  haveI : Algebra.IsAlgebraic (ZMod 2) F := Algebra.IsAlgebraic.of_finite (ZMod 2) F
  haveI : IsGalois (ZMod 2) F := inferInstance
  -- `σ` as a `ZMod 2`-algebra automorphism (it fixes the prime field `𝔽₂`).
  let σ' : F ≃ₐ[ZMod 2] F := AlgEquiv.ofRingEquiv (f := σ) (fun z => by
    have h := RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod 2) F))
      (algebraMap (ZMod 2) F)
    exact DFunLike.congr_fun h z)
  set frob := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F with hfrob
  have hord : orderOf frob = Module.finrank (ZMod 2) F :=
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod 2) F
  have hcardaut : Nat.card (F ≃ₐ[ZMod 2] F) = Module.finrank (ZMod 2) F :=
    IsGalois.card_aut_eq_finrank (ZMod 2) F
  -- the Frobenius generates `Gal(F/𝔽₂)` (its order equals the group's cardinality)
  have htop : Subgroup.zpowers frob = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, hcardaut]
  have hmem : σ' ∈ Submonoid.powers frob := by
    rw [mem_powers_iff_mem_zpowers, htop]; exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := hmem
  refine ⟨n, fun x => ?_⟩
  have hcoe : (σ : F → F) x = σ' x := rfl
  rw [hcoe, ← hn]
  have hiter : (⇑frob)^[n] = (· ^ (Fintype.card (ZMod 2) ^ n)) :=
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate (ZMod 2) F n
  have hpow : ⇑(frob ^ n) = (⇑frob)^[n] := AlgEquiv.coe_pow frob n
  have hval : (frob ^ n) x = x ^ (Fintype.card (ZMod 2) ^ n) := by
    rw [show ((frob ^ n) x) = (⇑(frob ^ n)) x from rfl, hpow, hiter]
  rw [hval, ZMod.card 2]

end FiniteFieldFrobenius

namespace FirstCaseHypothesis

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ} [Group G] [MulAction G Ω] [Finite G]
  (fc : FirstCaseHypothesis G Ω)

/-- **Peterfalvi Part II, Ch. II, step (3), the dimension identity**
(p. 109): for a nontrivial elementary abelian `r`-subgroup `M ≤ Q`
normalized by `KP`, `|M| = |C_M(P)|^p` (equivalently
`dim_{𝔽_r} M = p · dim_{𝔽_r} C_M(P)`, [Is] Theorem 15.16 applied to the
Frobenius group `KP` acting on `M` with `M^K = 0`). -/
theorem card_eq_card_inf_centralizer_pow {r : ℕ} (hr : r.Prime)
    {M : Subgroup G} (hMQ : M ≤ fc.toHypothesis.Q) (hMne : M ≠ ⊥)
    (helab : IsElementaryAbelian r ↥M)
    (hinv : ∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    Nat.card ↥M =
      Nat.card ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) ^ fc.p := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  -- `L = KP` normalizes `M`, giving the conjugation action `φ`.
  have hLnorm : fc.toHypothesis.K ⊔ fc.P ≤
      Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hinv g hg x hx
    · intro hx
      have h2 := hinv g⁻¹ (inv_mem hg) _ hx
      simpa [mul_assoc] using h2
  set L : Subgroup G := fc.toHypothesis.K ⊔ fc.P with hLdef
  set φ : ↥L →* MulAut ↥M :=
    M.normalizerMonoidHom.comp (Subgroup.inclusion hLnorm) with hφdef
  have hφval : ∀ (a : ↥L) (m : ↥M),
      ((φ a m : ↥M) : G) = (a : G) * (m : G) * (a : G)⁻¹ := fun _ _ => rfl
  have hKL : fc.toHypothesis.K ≤ L := le_sup_left
  have hPL : fc.P ≤ L := le_sup_right
  set U : Subgroup ↥L := fc.toHypothesis.K.subgroupOf L with hUdef
  set E : Subgroup ↥L := fc.P.subgroupOf L with hEdef
  have hcardU : Nat.card ↥U = Nat.card ↥fc.toHypothesis.K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv
  have hcardE : Nat.card ↥E = fc.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv, fc.card_P]
  -- `U ◁ L`: `K` is normal in `D ⊇ L`.
  have hLD : L ≤ fc.toHypothesis.D :=
    sup_le fc.toHypothesis.K_le_D
      (fc.P_le_V.trans fc.toHypothesis.V_le_D)
  haveI hUnormal : U.Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ fc.toHypothesis.K := hn
    have h := (inferInstance :
        (fc.toHypothesis.K.subgroupOf fc.toHypothesis.D).Normal).conj_mem
      (⟨(n : G), hLD n.2⟩ : ↥fc.toHypothesis.D)
      (Subgroup.mem_subgroupOf.mpr hn') ⟨(g : G), hLD g.2⟩
    exact Subgroup.mem_subgroupOf.mp h
  -- `U ⊔ E = ⊤` in `L = K ⊔ P`.
  have hsup : U ⊔ E = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, hUdef, hEdef,
      Subgroup.map_subgroupOf_eq_of_le hKL,
      Subgroup.map_subgroupOf_eq_of_le hPL,
      ← MonoidHom.range_eq_map, L.range_subtype]
  -- `|K| = 2^p - 1`, and `p ∤ 2^p - 1` (Fermat), so `(|E|, |U|) = 1`.
  have hcardK : Nat.card ↥fc.toHypothesis.K = 2 ^ fc.p - 1 := by
    rw [fc.toHypothesis.card_K_eq_card_Q0_sub_one, fc.card_Q0_eq_two_pow]
  have hfermat : ¬ fc.p ∣ 2 ^ fc.p - 1 := by
    intro hdvd
    have hcast : ((2 ^ fc.p - 1 : ℕ) : ZMod fc.p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod fc.p) fc.p _).mpr hdvd
    rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat,
      ZMod.pow_card, Nat.cast_one, sub_eq_zero] at hcast
    -- `hcast : (2 : ZMod p) = 1`, so `1 = 0` in the field `ZMod p`
    exact one_ne_zero (α := ZMod fc.p) (by linear_combination hcast)
  have hcopUE : Nat.Coprime (Nat.card ↥E) (Nat.card ↥U) := by
    rw [hcardE, hcardU, hcardK]
    exact (Nat.Prime.coprime_iff_not_dvd fc.p_prime).mpr hfermat
  have hEnt : 1 < Nat.card ↥E := by
    rw [hcardE]; exact fc.p_prime.one_lt
  -- `E` acts fixed-point-freely on `U`: step (1)'s `C_K(P) = 1`.
  have hfpf : ∀ e ∈ E, e ≠ 1 → ∀ u ∈ U, e * u * e⁻¹ = u → u = 1 := by
    intro e he hne u hu hconj
    have heP : ((e : ↥L) : G) ∈ fc.P := he
    have huK : ((u : ↥L) : G) ∈ fc.toHypothesis.K := hu
    have heG1 : ((e : ↥L) : G) ≠ 1 := fun h => hne (Subtype.ext h)
    -- `⟨e⟩ = P` since `P` has prime order.
    have hzpow : Subgroup.zpowers ((e : ↥L) : G) = fc.P := by
      have hle : Subgroup.zpowers ((e : ↥L) : G) ≤ fc.P :=
        (Subgroup.zpowers_le).mpr heP
      have horder : orderOf ((e : ↥L) : G) = fc.p := by
        have hdvd : orderOf ((e : ↥L) : G) ∣ fc.p := by
          rw [← fc.card_P]
          have h1 : orderOf ((e : ↥L) : G) =
              orderOf (⟨((e : ↥L) : G), heP⟩ : ↥fc.P) :=
            orderOf_injective fc.P.subtype fc.P.subtype_injective
              ⟨((e : ↥L) : G), heP⟩
          rw [h1]
          exact orderOf_dvd_natCard _
        rcases (fc.p_prime.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) heG1
        · exact h1
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [fc.card_P, Nat.card_zpowers, horder]
    -- `u` commutes with `e`, hence with all of `P = ⟨e⟩`.
    have hcomm : Commute ((e : ↥L) : G) ((u : ↥L) : G) := by
      have h := congrArg (fun z : ↥L => (z : G)) hconj
      have h' : ((e : ↥L) : G) * ((u : ↥L) : G) * ((e : ↥L) : G)⁻¹ =
          ((u : ↥L) : G) := h
      calc ((e : ↥L) : G) * ((u : ↥L) : G)
          = (((e : ↥L) : G) * ((u : ↥L) : G) * ((e : ↥L) : G)⁻¹) *
            ((e : ↥L) : G) := by group
        _ = ((u : ↥L) : G) * ((e : ↥L) : G) := by rw [h']
    have huC : ((u : ↥L) : G) ∈ Subgroup.centralizer (fc.P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hzpow] at hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (hcomm.zpow_left n).eq
    have hmem : ((u : ↥L) : G) ∈
        fc.toHypothesis.K ⊓ Subgroup.centralizer (fc.P : Set G) :=
      ⟨huK, huC⟩
    rw [fc.K_inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  -- `r ∤ |U| = |K|`: `r ∣ |M| ∣ |Q|` and `(|Q|, |K|) = 1`.
  have hrM : r ∣ Nat.card ↥M := by
    haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥M)
    have hxr : orderOf x = r := orderOf_eq_prime (helab.pow_eq_one x) hx1
    exact hxr ▸ orderOf_dvd_natCard x
  have hpU : ¬ r ∣ Nat.card ↥U := by
    rw [hcardU]
    intro hdvd
    have hrQ : r ∣ Nat.card ↥fc.toHypothesis.Q :=
      hrM.trans (Subgroup.card_dvd_of_le hMQ)
    have hr1 : r ∣ 1 :=
      fc.toHypothesis.coprime_card_Q_K ▸ Nat.dvd_gcd hrQ hdvd
    exact hr.ne_one (Nat.dvd_one.mp hr1)
  -- `C_M(K) = 1`: `K` acts fixed-point-freely on `Q ⊇ M` (§2 Prop 1(a)).
  have hfixU : fixedSubgroup φ U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    obtain ⟨k₀, hk₀K, hk₀1⟩ := fc.toHypothesis.exists_ne_one_mem_KSet
    have hk₀mem : k₀ ∈ fc.toHypothesis.K := by
      change k₀ ∈ (fc.toHypothesis.K : Set G)
      rw [fc.toHypothesis.coe_K]
      exact hk₀K
    have hφfix := hx (⟨k₀, hKL hk₀mem⟩ : ↥L)
      (Subgroup.mem_subgroupOf.mpr hk₀mem)
    have hxQ : ((x : ↥M) : G) ∈ fc.toHypothesis.Q := hMQ x.2
    have hQfix : fc.toHypothesis.conjQByK ⟨k₀, hk₀mem⟩
        ⟨((x : ↥M) : G), hxQ⟩ = ⟨((x : ↥M) : G), hxQ⟩ := by
      apply Subtype.ext
      rw [fc.toHypothesis.conjQByK_apply_val]
      exact congrArg (fun z : ↥M => (z : G)) hφfix
    have hk₀ne : (⟨k₀, hk₀mem⟩ : ↥fc.toHypothesis.K) ≠ 1 :=
      fun h => hk₀1 (congrArg Subtype.val h)
    have hxone := fc.toHypothesis.conjQByK_fixed_eq_one hk₀ne hQfix
    have hxG := congrArg (fun z : ↥fc.toHypothesis.Q => (z : G)) hxone
    exact Subtype.ext hxG
  -- The kernel-FPF identity in group-cardinality form ([Is] Thm 15.16).
  letI : CommGroup ↥M := helab.subgroupCommGroup
  letI : Module (ZMod r) (Additive ↥M) := helab.subgroupZmodModule
  have hkey := OddOrder.GroupTheory.WielandtKernelFPF.card_eq_card_fixedSubgroup_pow_of_frobenius
    hsup hcopUE hEnt hfpf hpU φ hfixU
  -- `C_M(P)` as an ambient subgroup: `fixedSubgroup φ E ≃ M ⊓ C_G(P)`.
  have hfixinf : Nat.card ↥(fixedSubgroup φ E) =
      Nat.card ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) := by
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun x => ⟨((x : ↥M) : G), (x : ↥M).2, ?_⟩) ⟨?_, ?_⟩
    · -- centralizer membership
      change ((x : ↥M) : G) ∈ Subgroup.centralizer (fc.P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgL : g ∈ L := hPL hg
      have hfix := x.2 (⟨g, hgL⟩ : ↥L) (Subgroup.mem_subgroupOf.mpr hg)
      have hval : g * ((x : ↥M) : G) * g⁻¹ = ((x : ↥M) : G) :=
        congrArg (fun z : ↥M => (z : G)) hfix
      calc g * ((x : ↥M) : G)
          = (g * ((x : ↥M) : G) * g⁻¹) * g := by group
        _ = ((x : ↥M) : G) * g := by rw [hval]
    · -- injective
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) =>
        (z : G)) hab
    · -- surjective
      rintro ⟨g, hgM, hgC⟩
      refine ⟨⟨⟨g, hgM⟩, ?_⟩, rfl⟩
      intro l hl
      apply Subtype.ext
      have hlP : ((l : ↥L) : G) ∈ fc.P := hl
      have hcomm := Subgroup.mem_centralizer_iff.mp hgC _ hlP
      change ((l : ↥L) : G) * g * ((l : ↥L) : G)⁻¹ = g
      rw [hcomm]
      group
  -- Assemble: `|M| = |C_M(P)|^{|E|} = |M ⊓ C_G(P)|^p`.
  exact hkey.trans (by rw [hfixinf, hcardE])

/-- **Peterfalvi Part II, Ch. II, step (3), `C_M(P) ≠ 1`** (p. 109): the
fixed points of `P` on a nontrivial `KP`-invariant elementary abelian
subgroup `M ≤ Q` are nontrivial — immediate from the dimension identity. -/
theorem inf_centralizer_ne_bot_of_invariant {r : ℕ} (hr : r.Prime)
    {M : Subgroup G} (hMQ : M ≤ fc.toHypothesis.Q) (hMne : M ≠ ⊥)
    (helab : IsElementaryAbelian r ↥M)
    (hinv : ∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    M ⊓ Subgroup.centralizer (fc.P : Set G) ≠ ⊥ := by
  intro hbot
  apply hMne
  have hcard := fc.card_eq_card_inf_centralizer_pow hr hMQ hMne helab hinv
  rw [hbot, Subgroup.card_bot, one_pow] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

/-- **Peterfalvi Part II, Ch. II, step (3), `|C_M(P)| = r`** (p. 109): for a
nontrivial `KP`-invariant elementary abelian `r`-subgroup `M ≤ Q₁`, the
`P`-fixed points have order exactly `r` (`dim_{𝔽_r} C_M(P) = 1`).

Via the near-field model of step (2)(b), `C_M(P) ≤ C_Q(P)` embeds into `F^*`,
which acts on `(F, +)` fixed-point-freely by right multiplication; by the
Appendix B Lemma (`isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian`) the
`r`-group `C_M(P)` is then cyclic, and an elementary abelian nontrivial cyclic
group has order `r`.  (This subsumes the book's citation of [H] V Satz 8.15 —
subgroups of order `r²` of a Frobenius complement are cyclic.)

Inherits the step (2)(b) `sorry` (Appendix C Prop 1 behind Brauer–Suzuki,
issue 9318); everything else is proved. -/
theorem card_inf_centralizer_eq_prime {r : ℕ} (hr : r.Prime)
    {M : Subgroup G} (hMQ1 : M ≤ fc.toHypothesis.Q1) (hMne : M ≠ ⊥)
    (helab : IsElementaryAbelian r ↥M)
    (hinv : ∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ M, g * m * g⁻¹ ∈ M) :
    Nat.card ↥(M ⊓ Subgroup.centralizer (fc.P : Set G)) = r := by
  classical
  letI := fc.toHypothesis.centralizerQuotientMulAction fc.P_le_V
  haveI : Fact r.Prime := ⟨hr⟩
  have hMQ : M ≤ fc.toHypothesis.Q := hMQ1.trans fc.toHypothesis.Q1_le_Q
  set M₀ : Subgroup G := M ⊓ Subgroup.centralizer (fc.P : Set G) with hM₀def
  have hM₀ne : M₀ ≠ ⊥ :=
    fc.inf_centralizer_ne_bot_of_invariant hr hMQ hMne helab hinv
  haveI : Nontrivial ↥M₀ := (Subgroup.nontrivial_iff_ne_bot M₀).mpr hM₀ne
  -- `r` is odd: `r ∣ |M| ∣ |Q₁|` and `2 ∤ |Q₁|`.
  have hrodd : Odd r := by
    haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥M)
    have hxr : orderOf x = r := orderOf_eq_prime (helab.pow_eq_one x) hx1
    have hrM : r ∣ Nat.card ↥M := hxr ▸ orderOf_dvd_natCard x
    have hrQ1 : r ∣ Nat.card ↥fc.toHypothesis.Q1 :=
      hrM.trans (Subgroup.card_dvd_of_le hMQ1)
    have h2 : ¬ 2 ∣ Nat.card ↥fc.toHypothesis.Q1 := by
      rw [fc.toHypothesis.card_Q1]
      exact fc.toHypothesis.two_not_dvd_card_Q1Subgroup
    refine hr.odd_of_ne_two ?_
    rintro rfl
    exact h2 hrQ1
  -- `M₀` is elementary abelian of exponent `r`.
  have helab₀ : IsElementaryAbelian r ↥M₀ := by
    constructor
    · intro x y
      have h := helab.comm ⟨(x : G), x.2.1⟩ ⟨(y : G), y.2.1⟩
      have hval := congrArg (fun z : ↥M => (z : G)) h
      exact Subtype.ext hval
    · intro x
      have h := helab.pow_eq_one (⟨(x : G), x.2.1⟩ : ↥M)
      have hval := congrArg (fun z : ↥M => (z : G)) h
      apply Subtype.ext
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hval ⊢
      exact hval
  -- The near-field model of step (2)(b).
  obtain ⟨F, hNF, ⟨model⟩⟩ := fc.exists_affineNearFieldModel
  letI : NearFields.NearField F := hNF
  haveI : Finite F := by
    have hinj : Function.Injective
        (fun x : F => model.emb (Multiplicative.ofAdd x)) :=
      fun a b hab => Multiplicative.ofAdd.injective (model.emb_injective hab)
    exact Finite.of_injective _ hinj
  -- The embedding `M₀ ↪ F^*` through the quotient `L/N` and `qEquiv`.
  set L : Subgroup G := Subgroup.centralizer (fc.P : Set G) with hLdef
  set N : Subgroup ↥L := (fc.toHypothesis.H.subgroupOf L).normalCore
    with hNdef
  have hM₀L : M₀ ≤ L := inf_le_right
  have hQbar : fc.rankOneQuotient.Q =
      (fc.toHypothesis.Q.subgroupOf L).map (QuotientGroup.mk' N) := rfl
  have hmemQ : ∀ m : ↥M₀,
      ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)) m ∈
        fc.rankOneQuotient.Q := by
    intro m
    rw [hQbar]
    exact Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (hMQ m.2.1))
  set ι : ↥M₀ →* Fˣ :=
    model.qEquiv.toMonoidHom.comp
      (((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L)).codRestrict
        fc.rankOneQuotient.Q hmemQ) with hιdef
  have hιinj : Function.Injective ι := by
    intro a b hab
    have h1 : ι (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    -- the quotient class of `a * b⁻¹` is trivial, so `a * b⁻¹ ∈ N ≤ D_L`
    have h2 : ((QuotientGroup.mk' N).comp (Subgroup.inclusion hM₀L))
        (a * b⁻¹) = 1 := by
      have h2' := model.qEquiv.injective (h1.trans (map_one _).symm)
      exact congrArg Subtype.val h2'
    have h4 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact h2
    have h5 : Subgroup.inclusion hM₀L (a * b⁻¹) ∈
        fc.toHypothesis.D.subgroupOf L := by
      have hND : N ≤ fc.toHypothesis.D.subgroupOf L := by
        rw [hNdef, fc.toHypothesis.normalCore_cH_eq_centralizer_cQ fc.P_le_V]
        exact inf_le_left
      exact hND h4
    have h6 : ((a * b⁻¹ : ↥M₀) : G) ∈
        fc.toHypothesis.Q ⊓ fc.toHypothesis.D :=
      ⟨hMQ (a * b⁻¹).2.1, Subgroup.mem_subgroupOf.mp h5⟩
    rw [fc.toHypothesis.Q_inf_D_eq_bot, Subgroup.mem_bot] at h6
    have h7 : (a * b⁻¹ : ↥M₀) = 1 := Subtype.ext h6
    exact mul_inv_eq_one.mp h7
  -- The right-multiplication action of the image of `M₀` on `(F, +)`.
  have hcomm : ∀ u v : ι.range, (u : Fˣ) * (v : Fˣ) = (v : Fˣ) * (u : Fˣ) := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    have h := helab₀.comm a b
    calc ι a * ι b = ι (a * b) := (map_mul ι a b).symm
      _ = ι (b * a) := by rw [h]
      _ = ι b * ι a := map_mul ι b a
  set ψ : ↥M₀ →* MulAut (Multiplicative F) :=
    (NearFields.rightMulAction ι.range hcomm).comp ι.rangeRestrict with hψdef
  have hψval : ∀ (m : ↥M₀) (x : Multiplicative F),
      ψ m x = Multiplicative.ofAdd (x.toAdd * ((ι m : Fˣ) : F)) :=
    fun _ _ => rfl
  -- fixed-point-freeness: `x * u = x` with `x ≠ 0` forces `u = 1`.
  have hfpf : ∀ m : ↥M₀, m ≠ 1 →
      OddOrder.Isaacs.Ch06.actionFixedBy ψ m = ⊥ := by
    intro m hm
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hfix : x.toAdd * ((ι m : Fˣ) : F) = x.toAdd := by
      have h := (OddOrder.Isaacs.Ch06.mem_actionFixedBy).mp hx
      rw [hψval] at h
      exact congrArg Multiplicative.toAdd h
    by_contra hxne
    have hx0 : x.toAdd ≠ 0 := by
      intro h0
      apply hxne
      apply Multiplicative.toAdd.injective
      exact h0
    have hu1 : ((ι m : Fˣ) : F) = 1 := by
      have hcancel := mul_left_cancel₀ hx0
        (hfix.trans (mul_one x.toAdd).symm)
      exact hcancel
    have : ι m = 1 := Units.ext hu1
    exact hm (hιinj (this.trans (map_one ι).symm))
  -- Appendix B Lemma: the `r`-group `M₀` acting f.p.f. on `(F, +)` is cyclic.
  obtain ⟨f, hf, hEA⟩ :=
    NearFields.isElementaryAbelian_multiplicative (F := F)
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Nontrivial (Multiplicative F) :=
    inferInstanceAs (Nontrivial F)
  haveI hcyc : IsCyclic ↥M₀ :=
    Huppert.isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian
      hf helab₀.isPGroup hrodd hEA ψ hfpf
  -- an elementary abelian nontrivial cyclic group has order `r`
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have htop : Subgroup.zpowers g = ⊤ := by
    rw [Subgroup.eq_top_iff']
    exact hg
  have hcardord : Nat.card ↥M₀ = orderOf g := by
    rw [← Nat.card_zpowers, htop]
    exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
  have hdvd : orderOf g ∣ r :=
    orderOf_dvd_of_pow_eq_one (helab₀.pow_eq_one g)
  rcases hr.eq_one_or_self_of_dvd _ hdvd with h | h
  · exfalso
    rw [orderOf_eq_one_iff] at h
    rw [h, Subgroup.zpowers_one_eq_bot] at htop
    exact absurd htop bot_ne_top
  · rw [hcardord, h]

/-- **Peterfalvi Part II, Ch. II, step (3), the Clifford dichotomy** (p. 109):
a *minimal* nontrivial `KP`-invariant elementary abelian `r`-subgroup
`M ≤ Q₁` either contains a `K`-invariant subgroup of order `r` (a
`1`-dimensional `𝔽_r[K]`-submodule) or is `K`-irreducible.

By the dimension identity and `|C_M(P)| = r`, `|M| = r^p`; by Clifford
counting, a minimal nontrivial `K`-invariant subgroup `V` has `|M| = |V|^t`,
so `|V| = r^d` with `d · t = p`; `d = 1` gives the first branch and `d = p`
forces `V = M`, giving the second.

Inherits the step (2)(b) `sorry` through `|C_M(P)| = r` (issue 9318). -/
theorem exists_prime_order_invariant_or_irreducible {r : ℕ} (hr : r.Prime)
    {M : Subgroup G} (hMQ1 : M ≤ fc.toHypothesis.Q1) (hMne : M ≠ ⊥)
    (helab : IsElementaryAbelian r ↥M)
    (hinv : ∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (hmin : ∀ B ≤ M,
      (∀ g ∈ fc.toHypothesis.K ⊔ fc.P, ∀ m ∈ B, g * m * g⁻¹ ∈ B) →
      B ≠ ⊥ → B = M) :
    (∃ V ≤ M, V ≠ ⊥ ∧ Nat.card ↥V = r ∧
      (∀ k ∈ fc.toHypothesis.K, ∀ v ∈ V, k * v * k⁻¹ ∈ V)) ∨
    (∀ B ≤ M, (∀ k ∈ fc.toHypothesis.K, ∀ m ∈ B, k * m * k⁻¹ ∈ B) →
      B ≠ ⊥ → B = M) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact fc.p.Prime := ⟨fc.p_prime⟩
  have hMQ : M ≤ fc.toHypothesis.Q := hMQ1.trans fc.toHypothesis.Q1_le_Q
  -- `|M| = r^p` from the dimension identity and `|C_M(P)| = r`.
  have hcardM : Nat.card ↥M = r ^ fc.p := by
    rw [fc.card_eq_card_inf_centralizer_pow hr hMQ hMne helab hinv,
      fc.card_inf_centralizer_eq_prime hr hMQ1 hMne helab hinv]
  -- The conjugation action of `L = KP` on `M`, as in the identity proof.
  have hLnorm : fc.toHypothesis.K ⊔ fc.P ≤
      Subgroup.normalizer (M : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hinv g hg x hx
    · intro hx
      have h2 := hinv g⁻¹ (inv_mem hg) _ hx
      simpa [mul_assoc] using h2
  set L : Subgroup G := fc.toHypothesis.K ⊔ fc.P with hLdef
  set φ : ↥L →* MulAut ↥M :=
    M.normalizerMonoidHom.comp (Subgroup.inclusion hLnorm) with hφdef
  have hφval : ∀ (a : ↥L) (m : ↥M),
      ((φ a m : ↥M) : G) = (a : G) * (m : G) * (a : G)⁻¹ := fun _ _ => rfl
  have hKL : fc.toHypothesis.K ≤ L := le_sup_left
  set U : Subgroup ↥L := fc.toHypothesis.K.subgroupOf L with hUdef
  haveI hUnormal : U.Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ fc.toHypothesis.K := hn
    have hLD : L ≤ fc.toHypothesis.D :=
      sup_le fc.toHypothesis.K_le_D
        (fc.P_le_V.trans fc.toHypothesis.V_le_D)
    have h := (inferInstance :
        (fc.toHypothesis.K.subgroupOf fc.toHypothesis.D).Normal).conj_mem
      (⟨(n : G), hLD n.2⟩ : ↥fc.toHypothesis.D)
      (Subgroup.mem_subgroupOf.mpr hn') ⟨(g : G), hLD g.2⟩
    exact Subgroup.mem_subgroupOf.mp h
  haveI : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  letI : CommGroup ↥M := helab.subgroupCommGroup
  -- Ambient ↔ subtype invariance bridges.
  have hbridgeK : ∀ B' : Subgroup ↥M,
      OddOrder.Isaacs.Ch03.IsAInvariant (φ.comp U.subtype) B' ↔
      (∀ k ∈ fc.toHypothesis.K, ∀ m ∈ B'.map M.subtype,
        k * m * k⁻¹ ∈ B'.map M.subtype) := by
    intro B'
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    constructor
    · rintro h k hk _ ⟨m, hm, rfl⟩
      have hkL : k ∈ L := hKL hk
      have hmem := h (⟨⟨k, hkL⟩, Subgroup.mem_subgroupOf.mpr hk⟩ : ↥U) m hm
      exact ⟨_, hmem, hφval ⟨k, hkL⟩ m⟩
    · intro h u m hm
      have hu : ((u : ↥L) : G) ∈ fc.toHypothesis.K := u.2
      obtain ⟨m', hm', hval⟩ := h _ hu _ ⟨m, hm, rfl⟩
      have heq : φ (u : ↥L) m = m' := by
        apply Subtype.ext
        rw [hφval]
        exact hval.symm
      change φ (u : ↥L) m ∈ B'
      rw [heq]
      exact hm'
  by_cases hirr : ∀ B' : Subgroup ↥M,
      OddOrder.Isaacs.Ch03.IsAInvariant (φ.comp U.subtype) B' →
        B' = ⊥ ∨ B' = ⊤
  · -- second branch: `M` is `K`-irreducible
    right
    intro B hBM hBinv hBne
    have hB' := hirr (B.subgroupOf M) (by
      rw [hbridgeK, Subgroup.map_subgroupOf_eq_of_le hBM]
      exact hBinv)
    rcases hB' with h | h
    · exfalso
      apply hBne
      rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨x, hBM hx⟩ : ↥M) ∈ B.subgroupOf M :=
        Subgroup.mem_subgroupOf.mpr hx
      rw [h, Subgroup.mem_bot] at hmem
      have hx1 : x = 1 := congrArg Subtype.val hmem
      rw [hx1]
      exact Subgroup.one_mem ⊥
    · rw [Subgroup.subgroupOf_eq_top] at h
      exact le_antisymm hBM h
  · -- first branch: a `1`-dimensional `K`-submodule exists
    left
    push Not at hirr
    obtain ⟨B', hB'inv, hB'ne, hB'top⟩ := hirr
    obtain ⟨V', hV'le, hV'ne, hV'inv, hV'min⟩ :=
      exists_minimal_aInvariant_le hB'ne hB'inv
    -- the ambient minimality of `M` in subtype form
    have hMtop : ∀ C : Subgroup ↥M,
        OddOrder.Isaacs.Ch03.IsAInvariant φ C → C ≠ ⊥ → C = ⊤ := by
      intro C hCinv hCne
      have hCamb : C.map M.subtype = M := by
        apply hmin _ (Subgroup.map_subtype_le C)
        · intro g hg m hm
          obtain ⟨m', hm', rfl⟩ := hm
          have hgL : g ∈ L := hg
          have hmem :=
            (OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem.mp hCinv)
              ⟨g, hgL⟩ m' hm'
          exact ⟨_, hmem, hφval ⟨g, hgL⟩ m'⟩
        · intro hbot
          apply hCne
          rw [eq_bot_iff]
          intro x hx
          have hmem : (x : G) ∈ C.map M.subtype := ⟨x, hx, rfl⟩
          rw [hbot, Subgroup.mem_bot] at hmem
          rw [Subgroup.mem_bot]
          exact Subtype.ext hmem
      rw [Subgroup.eq_top_iff']
      intro x
      have hmem : (x : G) ∈ C.map M.subtype := by
        rw [hCamb]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hmem
      rwa [show y = x from Subtype.ext hyx] at hy
    -- Clifford counting: `|M| = |V'|^t`
    obtain ⟨t, ht⟩ :=
      exists_card_eq_pow_of_minimal_invariant hMtop hV'ne hV'inv hV'min
    -- `|V'| = r^d` with `d * t = p`
    have hV'dvd : Nat.card ↥V' ∣ r ^ fc.p := by
      rw [← hcardM]
      exact Subgroup.card_subgroup_dvd_card V'
    obtain ⟨d, hdle, hdcard⟩ := (Nat.dvd_prime_pow hr).mp hV'dvd
    have hdt : d * t = fc.p := by
      apply Nat.pow_right_injective hr.two_le
      change r ^ (d * t) = r ^ fc.p
      rw [pow_mul, ← hdcard, ← ht, hcardM]
    rcases fc.p_prime.eq_one_or_self_of_dvd d ⟨t, hdt.symm⟩ with hd | hd
    · -- `d = 1`: `|V'| = r`, push down to the ambient group
      refine ⟨V'.map M.subtype, Subgroup.map_subtype_le V', ?_, ?_, ?_⟩
      · intro hbot
        apply hV'ne
        exact Subgroup.map_injective M.subtype_injective
          (hbot.trans (Subgroup.map_bot M.subtype).symm)
      · rw [Nat.card_congr (Subgroup.equivMapOfInjective V' M.subtype
          M.subtype_injective).toEquiv.symm, hdcard, hd, pow_one]
      · exact (hbridgeK V').mp hV'inv
    · -- `d = p`: `V' = ⊤`, contradicting `B' ≠ ⊤`
      exfalso
      apply hB'top
      have hV'top : V' = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hdcard, hd, ← hcardM]
      exact le_antisymm le_top (hV'top ▸ hV'le)

/-- **Peterfalvi Part II, Ch. II, step (3), the first Clifford branch**
(p. 109): if a `K`-invariant subgroup `V ≤ Q` of prime order `r` exists
(a `1`-dimensional `𝔽_r[K]`-submodule), then `|K| = 2^p − 1` divides
`r − 1`, i.e. `r ≡ 1 (mod 2^p − 1)`: `K` acts on `V` by conjugation
faithfully (it acts fixed-point-freely on `Q ⊇ V`), so it embeds into
`Aut(V) ≅ (ℤ/r)^*` of order `r − 1`.  Sorry-free. -/
theorem card_K_dvd_sub_one_of_prime_order_invariant {r : ℕ} (hr : r.Prime)
    {V : Subgroup G} (hVQ : V ≤ fc.toHypothesis.Q) (hVne : V ≠ ⊥)
    (hVcard : Nat.card ↥V = r)
    (hVinv : ∀ k ∈ fc.toHypothesis.K, ∀ v ∈ V, k * v * k⁻¹ ∈ V) :
    (2 ^ fc.p - 1) ∣ (r - 1) := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  -- `K` normalizes `V`, giving the conjugation action.
  have hKnorm : fc.toHypothesis.K ≤ Subgroup.normalizer (V : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hVinv k hk x hx
    · intro hx
      have h2 := hVinv k⁻¹ (inv_mem hk) _ hx
      simpa [mul_assoc] using h2
  set φV : ↥fc.toHypothesis.K →* MulAut ↥V :=
    V.normalizerMonoidHom.comp (Subgroup.inclusion hKnorm) with hφVdef
  have hφVval : ∀ (k : ↥fc.toHypothesis.K) (v : ↥V),
      ((φV k v : ↥V) : G) = (k : G) * (v : G) * (k : G)⁻¹ := fun _ _ => rfl
  -- faithfulness: `K` acts fixed-point-freely on `Q ⊇ V` (§2 Prop 1(a)).
  have hinj : Function.Injective φV := by
    rw [injective_iff_map_eq_one]
    intro k hk
    by_contra hkne
    haveI : Nontrivial ↥V := (Subgroup.nontrivial_iff_ne_bot V).mpr hVne
    obtain ⟨v, hv1⟩ := exists_ne (1 : ↥V)
    have hfix : φV k v = v := by rw [hk]; rfl
    have hvQ : ((v : ↥V) : G) ∈ fc.toHypothesis.Q := hVQ v.2
    have hQfix : fc.toHypothesis.conjQByK k ⟨(v : G), hvQ⟩ =
        ⟨(v : G), hvQ⟩ := by
      apply Subtype.ext
      rw [fc.toHypothesis.conjQByK_apply_val]
      exact congrArg (fun z : ↥V => (z : G)) hfix
    have hvone := fc.toHypothesis.conjQByK_fixed_eq_one hkne hQfix
    have hvG := congrArg
      (fun z : ↥fc.toHypothesis.Q => (z : G)) hvone
    exact hv1 (Subtype.ext hvG)
  -- `|K| ∣ |Aut(V)| = r − 1`.
  haveI : IsCyclic ↥V := isCyclic_of_prime_card hVcard
  have hAut : Nat.card (MulAut ↥V) = r - 1 := by
    rw [IsCyclic.card_mulAut, hVcard, Nat.totient_prime hr]
  have hKcard : Nat.card ↥fc.toHypothesis.K = 2 ^ fc.p - 1 := by
    rw [fc.toHypothesis.card_K_eq_card_Q0_sub_one, fc.card_Q0_eq_two_pow]
  rw [← hKcard, ← hAut]
  exact Subgroup.card_dvd_of_injective φV hinj

/-- **Step (3), second branch — Half A** (the `𝔽_{2^p}`-side, p. 109): for any
`a ∈ P`, conjugation by `a` on the Fitting subgroup `F(D̄) ≅ 𝔽_{2^p}ˣ` (the image
of `K`) is a power-of-two map `t ↦ t^(2^i)`.

This is `Aut(𝔽_{2^p}) = ⟨Frobenius⟩` (`ringAut_card_two_pow_eq_pow`) read through
the adapted field model (`exists_adapted_field_model`): the model intertwines
`fittingConjAction (toVbar a)` on `F(D̄)` with the field automorphism `σhom a`
acting on `𝔽_{2^p}ˣ` via `μ`, and `σhom a` is a power of the Frobenius. -/
theorem exists_pow_two_fittingConjAction (a : ↥fc.P) :
    ∃ i : ℕ, ∀ t : ↥(fitting fc.toHypothesis.Dbar),
      fc.toHypothesis.fittingConjAction (fc.toVbar a) t = t ^ (2 ^ i) := by
  obtain ⟨F, hFld, hFin, eQ, μ, σhom, hcardF, hσinj, hlawQ, hlawμ, hfix⟩ :=
    fc.exists_adapted_field_model
  letI : Field F := hFld
  letI : Finite F := hFin
  have hcard2 : Nat.card F = 2 ^ fc.p := hcardF.trans fc.card_Q0_eq_two_pow
  obtain ⟨i, hi⟩ := ringAut_card_two_pow_eq_pow hcard2 (σhom a)
  refine ⟨i, fun t => ?_⟩
  refine μ.injective ?_
  rw [hlawμ a t, map_pow]
  refine Units.ext ?_
  rw [fieldRingAutOnUnits_apply_val, Units.val_pow_eq_pow_val]
  exact hi _

/-- **Step (3), second branch — the conjugation bridge (A2 + surjectivity).**
If conjugation by `a ∈ P` raises every `k ∈ K` to the `r`-th power, then the
induced action on the Fitting subgroup `F(D̄) = K̄` is `t ↦ t^r`.

`K̄ = F(D̄)` is the image of `K` under `D ↠ D̄ = D/W` (`Kbar_eq_fitting`), so
every `t ∈ F(D̄)` is `mk k` for some `k ∈ K`; conjugation commutes with the
quotient map, so `fittingConjAction (toVbar a) (mk k) = mk (a k a⁻¹) = mk (k^r)
= (mk k)^r`.  (This packages the `M`-side `r`-power law — supplied later — into
the cyclic group `F(D̄)`, where it is compared with Half A.) -/
theorem fittingConjAction_pow_of_K_conj (a : ↥fc.P) {r : ℕ}
    (hB : ∀ k ∈ fc.toHypothesis.K, (a : G) * k * (a : G)⁻¹ = k ^ r)
    (t : ↥(fitting fc.toHypothesis.Dbar)) :
    fc.toHypothesis.fittingConjAction (fc.toVbar a) t = t ^ r := by
  -- `t ∈ fitting D̄ = K̄`, so `t = mk kd` for some `kd ∈ K` (as a subgroup of D).
  have ht : (t : fc.toHypothesis.Dbar) ∈ fc.toHypothesis.Kbar := by
    rw [fc.toHypothesis.Kbar_eq_fitting]; exact t.2
  obtain ⟨kd, hkd, hmk⟩ := ht
  have hkK : (kd : G) ∈ fc.toHypothesis.K := Subgroup.mem_subgroupOf.mp hkd
  apply Subtype.ext
  -- coe of LHS via the conjugation formula (as an element of `D̄`)
  have hLHS : ((fc.toHypothesis.fittingConjAction (fc.toVbar a) t :
        ↥(fitting fc.toHypothesis.Dbar)) : fc.toHypothesis.Dbar)
      = QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)
            ⟨(a : G), fc.toHypothesis.V_le_D (fc.P_le_V a.2)⟩
          * (t : fc.toHypothesis.Dbar)
          * (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)
            ⟨(a : G), fc.toHypothesis.V_le_D (fc.P_le_V a.2)⟩)⁻¹ := by
    unfold Hypothesis.fittingConjAction
    simp only [MonoidHom.comp_apply,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion, toVbar_coe,
      QuotientGroup.mk'_apply]
  rw [hLHS, SubmonoidClass.coe_pow, ← hmk]
  -- reduce through the quotient hom `mk'`
  rw [← map_inv (QuotientGroup.mk' (fc.toHypothesis.W.subgroupOf fc.toHypothesis.D)),
    ← map_mul, ← map_mul, ← map_pow]
  congr 1
  -- `⟨a⟩ * kd * ⟨a⟩⁻¹ = kd ^ r` in D, checked on the underlying elements of G
  apply Subtype.ext
  push_cast
  simpa using hB (kd : G) hkK

/-- **Step (3), second branch — the combine** (p. 109): if conjugation by
`a ∈ P` raises every `k ∈ K` to the `r`-th power, then `r ≡ 2^i (mod 2^p − 1)`
for some `i`.

Half A gives an `i` with `t ↦ t^(2^i)` on `F(D̄)`; A2 gives `t ↦ t^r`; so
`t^(2^i) = t^r` for every `t ∈ F(D̄)`.  As `F(D̄)` is cyclic of order `2^p − 1`
(`fitting_Dbar_cyclic_fpf_abelian`, `card_fitting_Dbar_eq_ncard_KSet`), taking a
generator gives `2^i ≡ r (mod 2^p − 1)`.  (The `M`-side hypothesis `hB` — the
`r`-power law — is supplied by Half B.) -/
theorem exists_pow_two_modEq_of_K_conj (a : ↥fc.P) {r : ℕ}
    (hB : ∀ k ∈ fc.toHypothesis.K, (a : G) * k * (a : G)⁻¹ = k ^ r) :
    ∃ i : ℕ, r ≡ 2 ^ i [MOD 2 ^ fc.p - 1] := by
  classical
  haveI : Fintype ↥(fitting fc.toHypothesis.Dbar) := Fintype.ofFinite _
  obtain ⟨i, hHalfA⟩ := fc.exists_pow_two_fittingConjAction a
  refine ⟨i, ?_⟩
  -- `t^(2^i) = t^r` for every `t ∈ F(D̄)` (Half A meets A2)
  have hpow : ∀ t : ↥(fitting fc.toHypothesis.Dbar), t ^ (2 ^ i) = t ^ r := fun t => by
    rw [← hHalfA t, fc.fittingConjAction_pow_of_K_conj a hB t]
  haveI : IsCyclic ↥(fitting fc.toHypothesis.Dbar) :=
    fc.toHypothesis.fitting_Dbar_cyclic_fpf_abelian.1
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(fitting fc.toHypothesis.Dbar))
  have hcardK : Nat.card ↥(fitting fc.toHypothesis.Dbar) = Nat.card fc.toHypothesis.K := by
    rw [fc.toHypothesis.card_fitting_Dbar_eq_ncard_KSet, ← fc.toHypothesis.coe_K]
    exact (Nat.card_coe_set_eq _).symm
  have horder : orderOf g = 2 ^ fc.p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardK,
      fc.toHypothesis.card_K_eq_card_Q0_sub_one, fc.card_Q0_eq_two_pow]
  have hmod : (2 ^ i) ≡ r [MOD orderOf g] := pow_eq_pow_iff_modEq.mp (hpow g)
  rw [horder] at hmod
  exact hmod.symm

end FirstCaseHypothesis

end OddOrder.Peterfalvi.Appendices.Suzuki
