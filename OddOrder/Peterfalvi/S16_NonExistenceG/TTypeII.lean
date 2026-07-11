import OddOrder.Peterfalvi.S16_NonExistenceG.TTypeIICoherence
import OddOrder.Peterfalvi.S16_NonExistenceG.TGapGalois

/-!
# Peterfalvi (14.9): the T-side Type-II theorem

The T-side type-III character estimate and the deduction that `T` is of Type II.
Topic-split from `OddOrder.Peterfalvi.S16_NonExistenceG.SubgroupL`.
-/
namespace OddOrder.Peterfalvi.S16
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise
open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical in
/-- **Peterfalvi (14.9), the Γ-Bessel assembly skeleton** — the *proven* structural core of the
character body, isolating the char-cascade carriers as precisely-named hypotheses.  Coq
`FTtypeP_min_typeII` (PFsection14.v:764--853): given the coherent `τ₁`-image family `calT1`
(orthonormal degree-`p` induced characters, whose `|calT1| = (v−1)/p` count is the proven
`T_typeIII_calT1_card` after the (13.12) `d = 1` substitution `v = |V|`) and the `S`-side `βₛ`
bridge gap `Γ`, the parity fact `⟨Γ, τ₁ζ⟩ ≡ 1 (mod 2)` per `ζ` (`S09.cfdot_real_vchar_even`) makes
each integer pairing coefficient `x ζ = ⟨Γ, τ₁ζ⟩` **nonzero**; then the orthogonal-integer Bessel
bridge `S09.sum_rat_weights_le_of_orthogonal_integer_decomposition` (Coq's `orthogonal_split` +
Bessel over `‖Γ‖² ≤ (u−1)/q`) gives `∑_{ζ ∈ calT1} 1 ≤ ⟨Γ,Γ⟩ ≤ (u−1)/q`, i.e.
`|calT1| = (v−1)/p ≤ (u−1)/q`.

This is the **genuinely-available** arithmetic of (14.9): everything downstream of the carriers is
proven here (the orthonormal-family Bessel step with unit weights `m ζ = 1`, the `∑ 1 = |calT1|`
count-collapse, and the `⟨Γ,Γ⟩ ≤ (u−1)/q` chaining).  The four hypotheses package exactly the deep
carriers that the honest §16 build still owes, each cited from its own construction at the
`T_typeIII_ratio_le` call site:

* `hcount : (calT1.card : ℚ) = (v−1)/p` — the coherent count (proven `T_typeIII_calT1_card` in `|V|`
  form) **after** the (13.12) `d = 1` substitution `v = |V|` (`S15.V_inf_centralizer_Q_eq_bot`, lane-b);
* `horth` — orthonormality of the `τ₁`-images (the `calT1` **coherence** carrier, proven skeleton
  `T_typeIII_calT1_coherent` fed a T-side `S07.Hypothesis` Dade package);
* `hdecomp`/`hΓ₁`/`hx` — the `S`-side `βₛ` bridge gap `Γ = ∑ x_ζ·τ₁ζ + Γ₁` (`Γ₁ ⊥ τ₁ζ`), with the
  parity nonzeroness `x_ζ ≠ 0` (Coq `nzT1_Ga` via `cfdot_real_vchar_even`);
* `hnorm : ⟨Γ,Γ⟩.re ≤ (u−1)/q` — the `S`-side norm bound on the bridge gap.

Its output `(v−1)/p ≤ (u−1)/q` is exactly the (14.9) `≤` whose `>` counterpart (14.8)
`key_inequality` contradicts. -/
theorem T_typeIII_ratio_le_of_gamma_bridge [Finite G]
    [Fintype G] [Invertible (Nat.card G : ℂ)] (hyp : Hypothesis (G := G))
    (calT1 : Finset (ClassFunction G ℂ)) (Γ Γ₁ : ClassFunction G ℂ)
    (x : ClassFunction G ℂ → ℤ)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁)
    (hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0)
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (hnorm : (ClassFunction.inner Γ Γ).re ≤
      ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  -- Bessel over the orthonormal `calT1` (unit weights `m a = 1`, integer coeffs `x a ≠ 0`),
  -- against the norm bound `⟨Γ,Γ⟩ ≤ (u−1)/q`: yields `∑_{a ∈ calT1} 1 ≤ (u−1)/q`.
  have hbessel := OddOrder.Peterfalvi.S09.sum_rat_weights_le_of_orthogonal_integer_decomposition
    (ι := ClassFunction G ℂ) calT1 (fun a => a) x (fun _ => (1 : ℚ)) Γ Γ₁
    (((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ))
    hdecomp
    (fun a ha b hb => by rw [horth a ha b hb]; split <;> simp)
    hΓ₁
    (fun _ _ => zero_le_one)
    hx
    hnorm
  -- `∑_{a ∈ calT1} 1 = |calT1|`, and `|calT1| = (v−1)/p` by the coherent count.
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hcount] at hbessel
  exact hbessel

open scoped Classical in
/-- **(14.9) Γ-bridge extraction engine.**  Given the `S`-side gap `Γ`, its integral nonzero
coefficients on the orthonormal coherent family `calT1`, and the orthogonality of that family to the
η-grid, define the complementary term `Γ₁ := Γ - ∑_ζ x_ζ·ζ`.  Orthonormality makes `Γ₁`
orthogonal to every family member, hence to the projection sum.  The projection sum is η-grid
orthogonal by hypothesis, so the genuine **Peterfalvi (13.18.d)** field `BetaData.Y_norm_bound`
applies to the split `Γ = Γ₁ + ∑_ζ x_ζ·ζ`.

The resulting bound is on the projection sum—not on `Γ` itself—and feeds the proven Bessel skeleton
`T_typeIII_ratio_le_of_gamma_bridge`.  Thus this theorem exactly matches the corrected (13.18.d)
statement and assumes no overstrong full-gap norm bound. -/
theorem T_typeIII_ratio_le_of_sSide_gap [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hyp : Hypothesis (G := G)) (calT1 : Finset (ClassFunction G ℂ))
    (horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0)
    (hcount : (calT1.card : ℚ) = ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ))
    (Γ : ClassFunction G ℂ) (x : ClassFunction G ℂ → ℤ)
    (hxcoe : ∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ))
    (hx : ∀ a ∈ calT1, x a ≠ 0)
    (heta : ∀ a ∈ calT1, ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner a (hyp.base.eta i k) = 0)
    (hYnorm : ∀ (X Y : ClassFunction G ℂ), Γ = X + Y →
      ClassFunction.inner X Y = 0 →
      (∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
        ClassFunction.inner Y (hyp.base.eta i k) = 0) →
      (ClassFunction.inner Y Y).re ≤
        ((hyp.base.u : ℚ) - 1) / (hyp.base.q : ℚ)) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  classical
  set Γ₁ : ClassFunction G ℂ := Γ - ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a with hΓ₁def
  have hdecomp : Γ = (∑ a ∈ calT1, (((x a : ℝ) : ℂ) • a)) + Γ₁ := by rw [hΓ₁def]; abel
  -- `Γ₁` is orthogonal to every member: `⟨Γ₁, b⟩ = ⟨Γ, b⟩ − ∑_a x_a·⟨a,b⟩ = x_b − x_b = 0`
  -- (inner is linear in the first argument, `inner_smul_left : ⟨c•φ,ψ⟩ = c·⟨φ,ψ⟩`).
  have hΓ₁ : ∀ a ∈ calT1, ClassFunction.inner Γ₁ a = 0 := by
    intro b hb
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) b
          = ∑ a ∈ s, ClassFunction.inner (((x a : ℝ) : ℂ) • a) b := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hΓ₁def, ClassFunction.inner_sub_left, hsum_left calT1, hxcoe b hb,
      Finset.sum_eq_single b
        (fun a ha hab => by
          rw [ClassFunction.inner_smul_left, horth a ha b hb, if_neg hab, mul_zero])
        (fun hbni => absurd hb hbni),
      ClassFunction.inner_smul_left, horth b hb b hb, if_pos rfl, mul_one, sub_self]
  -- The projection sum is the `Y` in (13.18.d).  Its complement `Γ₁` is orthogonal to it
  -- because `Γ₁` is orthogonal to every member of `calT1`.
  have hΓ₁sum : ClassFunction.inner Γ₁
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) = 0 := by
    have hsum_right : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner Γ₁ (∑ a ∈ s, ((x a : ℝ) : ℂ) • a)
          = ∑ a ∈ s, ClassFunction.inner Γ₁ (((x a : ℝ) : ℂ) • a) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_right, ih, Finset.sum_insert hc]
    rw [hsum_right calT1]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ClassFunction.inner_smul_right, hΓ₁ a ha, mul_zero]
  have hsum_eta : ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)
        (hyp.base.eta i k) = 0 := by
    intro i k
    have hsum_left : ∀ (s : Finset (ClassFunction G ℂ)),
        ClassFunction.inner (∑ a ∈ s, ((x a : ℝ) : ℂ) • a) (hyp.base.eta i k)
          = ∑ a ∈ s,
            ClassFunction.inner (((x a : ℝ) : ℂ) • a) (hyp.base.eta i k) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert c s hc ih =>
          rw [Finset.sum_insert hc, ClassFunction.inner_add_left, ih, Finset.sum_insert hc]
    rw [hsum_left calT1]
    apply Finset.sum_eq_zero
    intro a ha
    rw [ClassFunction.inner_smul_left, heta a ha i k, mul_zero]
  have hdecomp' : Γ = Γ₁ + ∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a := by
    rw [hdecomp]
    abel
  have hnormRaw := hYnorm Γ₁
    (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) hdecomp' hΓ₁sum hsum_eta
  have hu1 : 1 ≤ hyp.base.u := by
    have huc : 0 < hyp.base.u * hyp.base.c := by
      rw [← hyp.base.card_U_eq_uc]
      exact Nat.card_pos
    exact (CanonicallyOrderedAdd.mul_pos.mp huc).1
  have hsubcast : ((hyp.base.u - 1 : ℕ) : ℚ) = (hyp.base.u : ℚ) - 1 := by
    rw [Nat.cast_sub hu1]
    norm_num
  have hnorm : (ClassFunction.inner
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)
      (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a)).re ≤
        ((((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) : ℚ) : ℝ) := by
    rw [hsubcast]
    simpa using hnormRaw
  exact T_typeIII_ratio_le_of_gamma_bridge hyp calT1
    (∑ a ∈ calT1, ((x a : ℝ) : ℂ) • a) 0 x hcount horth (by simp) (by simp) hx hnorm
/-- **Peterfalvi (13.4)/(14.4), `T`-side case (9.7.b)**: the `T`-side centralizer parameter
vanishes and `v` has its full cyclotomic value.  This is obtained directly from the (13.3)
character-degree package and the (13.4) cross-expansion, before the (14.9) type-II conclusion.

Keeping this producer upstream of `T_typeIII_ratio_le` is essential: (13.4) is an input to the
(14.9) contradiction, whereas deriving the same facts from `T_typeII` would create the cycle
`T_isTypeP2 → T_typeIII_ratio_le → T_side_caseB_facts → T_typeII → T_isTypeP2`. -/
theorem T_side_caseB_facts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    hyp.base.D = ⊥ ∧
      hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
  obtain ⟨chars⟩ := OddOrder.Peterfalvi.S15.character_degree_analysis hG hyp.base
  obtain ⟨hD, hv, _hQ⟩ := OddOrder.Peterfalvi.S15.lambda_forces_T_caseB hG chars
  exact ⟨hD, hv⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The (13.18) gap `Γ` is a virtual character.  Its Dade term is virtual because
`β_{#1} = Ind_{PW₁}^S 1 - μ_{0,#1}` is virtual and has the (13.18.a) `A₀(S)` support;
subtracting `1_G` and adding `η_{0,#1}` preserves `ZIrr` membership.

This proof deliberately exposes its existing upstream gate: the only non-formal input is
`S15.betaGrid_A0_support`, whose prime-TI value producer is lane-b's (13.18) frontier. -/
private theorem sSideGamma_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S15.GammaGrid hG hyp.base ∈ ZIrr G := by
  classical
  let PW1 := (hyp.base.P ⊔ hyp.base.W1).subgroupOf hyp.base.S
  have htrivZ : trivialClassFunction ↥PW1 ∈ ZIrr ↥PW1 := by
    simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using
      (trivialIrreducibleCharacter ↥PW1).mem_ZIrr
  have hindZ : ClassFunction.induce PW1 (trivialClassFunction ↥PW1) ∈
      ZIrr ↥hyp.base.S :=
    ClassFunction.induce_mem_ZIrr PW1 htrivZ
  let j : Fin hyp.base.p := ⟨1, by have := hyp.base.three_le_p; omega⟩
  have hbetaZ : OddOrder.Peterfalvi.S15.betaGrid hyp.base j ∈ ZIrr ↥hyp.base.S := by
    rw [OddOrder.Peterfalvi.S15.betaGrid, OddOrder.Peterfalvi.S15.indPW1]
    exact (ZIrr ↥hyp.base.S).sub_mem hindZ
      (hyp.base.mu_irreducible ⟨0, hyp.base.q_prime.pos⟩ j).mem_ZIrr
  have htauZ : OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base ∈ ZIrr G := by
    simpa [OddOrder.Peterfalvi.S15.tauSbetaGrid, j] using
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.base.dadeHypS0 hG) (hyp.base.dadeHypS0_hconj hG)
        (OddOrder.Peterfalvi.S15.betaGrid_A0_support hG hyp.base j (by simp [j])) hbetaZ)
  have honeZ : (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∈ ZIrr G :=
    (trivialIrreducibleCharacter G).mem_ZIrr
  have hetaZ : hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j ∈ ZIrr G :=
    eta_mem_ZIrr hyp.base _ _
  change OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base -
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) + hyp.base.eta _ j ∈ ZIrr G
  exact (ZIrr G).add_mem ((ZIrr G).sub_mem htauZ honeZ) hetaZ

open scoped Classical in
/-- **Peterfalvi (14.9), `nzT1_Ga` parity extraction.**  Let `Γ` and every member of the coherent
`calT1` image be virtual characters.  If each member `a` admits the real virtual residual `Δ_a`
from the (14.9) expansion, with both `Δ_a` and `Γ` orthogonal to `1_G` and
`⟨Γ,a⟩ = 1 + ⟨Δ_a,Γ⟩`, then `⟨Γ,a⟩` is an odd integer and hence nonzero.

The parity statement is exactly `RepresentationTheory.cfdot_real_vchar_even`: `⟨Δ_a,Γ⟩` is even because
trivial coefficients vanish.  This theorem performs all integrality/parity bookkeeping after the
genuine `Δ_a` construction; no prime-TI or Dade hypothesis is hidden in its conclusion. -/
theorem gap_coefficients_nonzero_of_delta_parity [Fintype G]
    [Invertible (Nat.card G : ℂ)] (hodd : Odd (Nat.card G))
    (calT1 : Finset (ClassFunction G ℂ)) (Γ : ClassFunction G ℂ)
    (hΓZ : Γ ∈ ZIrr G) (hΓR : ClassFunction.IsReal Γ)
    (hΓ1 : ClassFunction.inner Γ
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0)
    (hmemZ : ∀ a ∈ calT1, a ∈ ZIrr G)
    (hDelta : ∀ a ∈ calT1, ∃ Δ : ClassFunction G ℂ,
      Δ ∈ ZIrr G ∧ ClassFunction.IsReal Δ ∧
        ClassFunction.inner Δ
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 ∧
        ClassFunction.inner Γ a = 1 + ClassFunction.inner Δ Γ) :
    ∃ x : ClassFunction G ℂ → ℤ,
      (∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ)) ∧
        ∀ a ∈ calT1, x a ≠ 0 := by
  let x : ClassFunction G ℂ → ℤ := fun a =>
    if ha : a ∈ calT1 then
      (ClassFunction.inner_mem_ZIrr_int hΓZ (hmemZ a ha)).choose
    else 0
  have hxcoe : ∀ a ∈ calT1, ClassFunction.inner Γ a = ((x a : ℝ) : ℂ) := by
    intro a ha
    rw [show x a = (ClassFunction.inner_mem_ZIrr_int hΓZ (hmemZ a ha)).choose by
      simp only [x, dif_pos ha]]
    exact_mod_cast (ClassFunction.inner_mem_ZIrr_int hΓZ (hmemZ a ha)).choose_spec
  refine ⟨x, hxcoe, ?_⟩
  intro a ha hxa0
  obtain ⟨Δ, hΔZ, hΔR, hΔ1, hrelation⟩ := hDelta a ha
  obtain ⟨m, c, d, hm, hc, hd, heven⟩ :=
    OddOrder.RepresentationTheory.cfdot_real_vchar_even hodd hΔZ hΔR hΓZ hΓR
  have hc0 : c = 0 := by
    rw [hΔ1] at hc
    exact_mod_cast hc
  have hd0 : d = 0 := by
    rw [hΓ1] at hd
    exact_mod_cast hd
  have hm_even : Even m := by
    simpa [hc0, hd0] using heven
  have hcast : ((x a : ℤ) : ℂ) = ((1 + m : ℤ) : ℂ) := by
    calc
      ((x a : ℤ) : ℂ) = ClassFunction.inner Γ a := by
        exact_mod_cast (hxcoe a ha).symm
      _ = 1 + ClassFunction.inner Δ Γ := hrelation
      _ = ((1 + m : ℤ) : ℂ) := by rw [← hm]; push_cast; ring
  have hxint : x a = 1 + m := by
    exact_mod_cast hcast
  rcases hm_even with ⟨k, hk⟩
  omega

/-- **Peterfalvi (14.9), the character body** — the structural `≤` half of the ratio comparison, the
sole deep obligation of (14.9).  Coq `PFsection14` `FTtypeP_min_typeII`, lines 737--853: assuming `T`
is type III, build `calT1 = seqIndD QV T QV Q` (the degree-`p` induced characters of `T`, from
`T' = Q ⊔ V` via `T_deriv_eq_QV`), coherent by uniform-degree coherence
(`S07.coherent_of_constant_degree` / Coq `uniform_degree_coherence`).

The T-side family data are constructed: `T_typeIII_calT1_family_galois` and its orbit count give
`|calT1| = (|V|−1)/p`; `T_typeIII_calT1_isCoherent` supplies the coherent extension; the direct
(13.4) producer `T_side_caseB_facts` gives `D = ⊥`, hence `|V| = v`; and
`T_typeIII_coherent_image_inner_eta_eq_zero` proves every coherent image orthogonal to the shared
`eta`-grid by restricting the full type-P1 Dade map and applying the norm-two rigidity engine.

The prime-TI anchor is fixed by coefficient Galois automorphisms, so the full eta-axis orbits now
give axis constancy and the sharp norm gives the column-or-row projection dichotomy.  The sole
remaining local residual in this ratio theorem is Coq (11.8)
`FTtype34_not_ortho_cycTIiso`, which excludes the wrong zero-row alternative.  After it, the proven
Γ-Bessel skeleton `T_typeIII_ratio_le_of_sSide_gap` combines orthogonality, the exact count, and
the concrete (13.18.d) bound `betaData.Y_norm_bound` to obtain
`(v − 1)/p ≤ (u − 1)/q`, contradicting the strict (14.8) inequality. -/
theorem T_typeIII_ratio_le [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T) :
    ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
  -- Coq `FTtypeP_min_typeII` body (PFsection14.v:737--853): `calT1`/coherence + Γ-Bessel.
  -- Reduced to the proven Γ-Bessel skeleton `T_typeIII_ratio_le_of_gamma_bridge`; its inputs are
  -- the precisely-named char-cascade carriers, each a genuinely-missing construction kept as a
  -- documented residual `sorry` here (NOT a gate on `T_typeIII_ratio_le`'s honest structure — the
  -- Bessel/orthonormality/count arithmetic is fully proven in the skeleton).
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI := hyp.base.finiteG
  haveI : Fintype ↥hyp.base.T := Fintype.ofFinite _
  haveI : Fintype ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) := Fintype.ofFinite _
  haveI : Invertible (Nat.card ↥hyp.base.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  haveI : Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- **Carrier 1 (the coherent `τ₁`-image family, now DISCHARGED from the (14.9) coherence).**
  -- The intrinsic type-III datum builds the degree-`p` `Ind_{QV}^T`-family `calT1_set` with all
  -- coherence inputs (`T_typeIII_calT1_family`); the T-side Dade package + coherence engine
  -- (`T_typeIII_calT1_isCoherent`, i.e. `T_typeIII_hyp07` ∘ `T_typeIII_calT1_coherent`) then produce
  -- the coherent map `τ₁ = hτ.extension`.  Its image `calT1 := τ₁(calT1_set)` is an **orthonormal**
  -- set of `G`-class functions (`horth`), because `τ₁` is an isometry on `ℤ[calT1_set]`
  -- (`IsCoherent.extension_inner_eq`) and the source members are orthonormal irreducibles.
  obtain ⟨𝒯, hinertia, hne, hlinear, hconj𝒯, hgalois𝒯, hcount_V⟩ :=
    T_typeIII_calT1_family_galois hyp hIII.some
  set calT1_set : Set (ClassFunction ↥hyp.base.T ℂ) :=
    ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)) with hcalT1
  -- Members of `calT1_set` are orthonormal irreducibles of `T` (irreducible + pairwise orthogonal
  -- via `T_typeIII_hyp07`'s family predicates), reused below for `horth`.
  have hirr : ∀ χ ∈ calT1_set, IsIrreducibleCharacter χ := by
    intro χ hχ
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at hχ
    obtain ⟨θ, hθ, rfl⟩ := hχ
    exact isIrreducibleCharacter_induce_of_inertia_eq
      (G := ↥hyp.base.T) (H := (derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hinertia θ hθ)
  -- `hcard2 : 2 ≤ |calT1_set|` — the crude size bound `(|V|−1)/p ≥ 2`, **ungated**: from the
  -- intrinsic `2p + 1 ≤ |V|` (`T_typeIII_two_p_add_one_le_card_V`, odd-order Frobenius `U ⋊ W₁`)
  -- and the count `|calT1_set| = (|V|−1)/p` (`hcount_V`), via `2 ≤ (|V|−1)/p ⟺ 2p ≤ |V|−1`.  The
  -- lane-b `|V|`-lower-bound (`v = (q^p−1)/(q−1)`, 13.15) is only needed for the *exact* count, not
  -- this `≥ 2`.
  have hcard2 : 2 ≤ calT1_set.ncard := by
    have hV := T_typeIII_two_p_add_one_le_card_V hG hyp hIII.some
    have hncard : calT1_set.ncard = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
      rw [hcalT1, Set.ncard_coe_finset]; exact hcount_V
    rw [hncard, Nat.le_div_iff_mul_le hyp.base.p_prime.pos]
    omega
  -- The T-side coherence: `τ₁ = hτ.extension`, `IsCoherent (tSideDadeMap) calT1_set A₁(T)`.
  obtain ⟨hyp07, htau, ⟨hτ⟩⟩ :=
    T_typeIII_calT1_isCoherent hyp hG hIII 𝒯 hinertia hlinear hne hconj𝒯 calT1_set hcalT1 hcard2
  rw [htau] at hτ
  -- `calT1 := τ₁(calT1_set)`, the coherent-image `Finset` in `CF(G)`.
  set calT1 : Finset (ClassFunction G ℂ) :=
    calT1_set.toFinset.image (⇑hτ.extension) with hcalT1img
  -- **`horth`: the coherent images are orthonormal** — the discharged coherence carrier.
  have horth : ∀ a ∈ calT1, ∀ b ∈ calT1,
      ClassFunction.inner a b = if a = b then (1 : ℂ) else 0 := by
    intro a ha b hb
    rw [hcalT1img, Finset.mem_image] at ha hb
    obtain ⟨ζ, hζT, rfl⟩ := ha
    obtain ⟨ζ', hζ'T, rfl⟩ := hb
    rw [Set.mem_toFinset] at hζT hζ'T
    -- `⟨τ₁ζ, τ₁ζ'⟩ = ⟨ζ, ζ'⟩` (coherent isometry on `ℤ[calT1_set]`).
    have hiso : ClassFunction.inner (hτ.extension ζ) (hτ.extension ζ')
        = ClassFunction.inner ζ ζ' :=
      hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζT) (Submodule.subset_span hζ'T)
    -- `⟨ζ, ζ'⟩ = if ζ = ζ' then 1 else 0` (orthonormal irreducibles).
    have hsrc : ClassFunction.inner ζ ζ' = if ζ = ζ' then (1 : ℂ) else 0 := by
      by_cases hζζ' : ζ = ζ'
      · subst hζζ'; rw [if_pos rfl]; exact (hirr ζ hζT).inner_self_eq_one
      · rw [if_neg hζζ']; exact hyp07.pairwise_orthogonal hζT hζ'T hζζ'
    rw [hiso, hsrc]
    -- The image equality `τ₁ζ = τ₁ζ'` iff `ζ = ζ'` (injectivity from the isometry).
    by_cases hζζ' : ζ = ζ'
    · rw [if_pos hζζ', if_pos (by rw [hζζ'])]
    · rw [if_neg hζζ', if_neg ?_]
      -- if `τ₁ζ = τ₁ζ'` then `⟨ζ,ζ'⟩ = ⟨τ₁ζ,τ₁ζ⟩ = ⟨ζ,ζ⟩ = 1 ≠ 0 = ⟨ζ,ζ'⟩`, contradiction.
      intro hab
      have h1 : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
        rw [← hiso, ← hab,
          hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζT) (Submodule.subset_span hζT)]
      rw [hsrc, if_neg hζζ', (hirr ζ hζT).inner_self_eq_one] at h1
      exact one_ne_zero h1.symm
  -- The coherent extension is injective on `calT1_set`: equality of two images would turn the
  -- source cross-inner-product `0` into the source self-inner-product `1`.
  have hinj : Set.InjOn (⇑hτ.extension) (↑calT1_set.toFinset : Set _) := by
    intro ζ hζ ζ' hζ' heq
    have hζS : ζ ∈ calT1_set := by simpa using hζ
    have hζ'S : ζ' ∈ calT1_set := by simpa using hζ'
    by_contra hne
    have hEq : ClassFunction.inner ζ ζ' = ClassFunction.inner ζ ζ := by
      rw [← hτ.extension_inner_eq ζ ζ' (Submodule.subset_span hζS)
          (Submodule.subset_span hζ'S), ← heq,
        hτ.extension_inner_eq ζ ζ (Submodule.subset_span hζS) (Submodule.subset_span hζS)]
    rw [hyp07.pairwise_orthogonal hζS hζ'S hne, (hirr ζ hζS).inner_self_eq_one] at hEq
    exact zero_ne_one hEq
  have hcalcard : calT1.card = calT1_set.toFinset.card := by
    rw [hcalT1img, Finset.card_image_of_injOn hinj]
  have hsourcecard :
      calT1_set.toFinset.card = (Nat.card ↥hyp.base.V - 1) / hyp.base.p := by
    rw [← Set.ncard_eq_toFinset_card' calT1_set, hcalT1, Set.ncard_coe_finset]
    exact hcount_V
  -- (13.4) gives `D = ⊥`; hence `d = |D| = 1` and `|V| = v d = v`.
  have hDbot : hyp.base.D = ⊥ := (T_side_caseB_facts hG hyp).1
  have hd1 : hyp.base.d = 1 := by
    rw [hyp.base.d_eq_card_D, hDbot, Subgroup.card_bot]
  have hVcard : Nat.card ↥hyp.base.V = hyp.base.v := by
    rw [hyp.base.card_V_eq_vd, hd1, mul_one]
  -- The same (13.4) value makes `v ≡ 1 (mod p)`, so the exact Nat quotient casts to the
  -- rational ratio used by the Bessel engine.
  have hvfull := (T_side_caseB_facts hG hyp).2
  have hvodd : Odd hyp.base.v := by
    rw [hvfull]
    exact hyp.tSide_cyclotomic_quotient_odd
  have hvdvd :
      hyp.base.v ∣ (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) := by
    rw [hvfull]
  have hvmod : hyp.base.v ≡ 1 [MOD hyp.base.p] :=
    hyp.tSide_cyclotomic_quotient_divisor_modEq_one
      hyp.base.v hvodd.pos.ne' hvdvd
  have hpdiv : hyp.base.p ∣ hyp.base.v - 1 :=
    (Nat.modEq_iff_dvd' hvodd.pos).mp hvmod.symm
  have hcount : (calT1.card : ℚ) =
      ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) := by
    rw [hcalcard, hsourcecard, hVcard]
    exact Nat.cast_div hpdiv (Nat.cast_ne_zero.mpr hyp.base.p_prime.ne_zero)
  -- The genuine (13.18) gap is the concrete `GammaGrid`.  Its virtuality follows from the
  -- supported S-side Dade image; reality and principal orthogonality are the faithful BetaData
  -- fields.  The coherent images are virtual characters by the coherent-extension contract.
  let betaData := OddOrder.Peterfalvi.S15.betaData_of_grid hG hyp.base
    ⟨1, hyp.base.p_prime.one_lt⟩ (by simp)
  have hGammaZ : betaData.Gamma ∈ ZIrr G := by
    simpa [betaData, OddOrder.Peterfalvi.S15.betaData_of_grid] using
      (sSideGamma_mem_ZIrr hG hyp)
  have hGammaR : ClassFunction.IsReal betaData.Gamma :=
    betaData.Gamma_real
  have hGamma1 : ClassFunction.inner betaData.Gamma
      (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
    exact betaData.Gamma_orthogonal_one
  have hmemZ : ∀ a ∈ calT1, a ∈ ZIrr G := by
    intro a ha
    rw [hcalT1img, Finset.mem_image] at ha
    obtain ⟨ζ, hζT, rfl⟩ := ha
    rw [Set.mem_toFinset] at hζT
    exact hτ.extension_mem_ZIrr ζ (Submodule.subset_span hζT)
  have hdiff_supp := T_typeIII_calT1_difference_support
    hyp hG hIII 𝒯 hlinear calT1_set hcalT1
  have hgaloisT : ∀ (sigma : ℂ ≃+* ℂ) ξ, ξ ∈ calT1_set →
      ClassFunction.mapRingEquiv sigma ξ ∈ calT1_set := by
    intro sigma ξ hξ
    rw [hcalT1] at hξ ⊢
    exact inducedFamily_mapRingEquiv_mem
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) 𝒯 hgalois𝒯 sigma hξ
  -- This is now the exact remaining (14.9) character construction: for each coherent image
  -- `a = τ₁ζ`, build `Δ_a = τ_T(ν₀ - ζ) - 1_G + a`, prove it real/virtual and orthogonal
  -- to `1_G`, and establish the expansion `⟨Γ,a⟩ = 1 + ⟨Δ_a,Γ⟩`.  All integrality and
  -- parity bookkeeping after this witness is discharged by the theorem below.
  have hDelta : ∀ a ∈ calT1, ∃ Δ : ClassFunction G ℂ,
      Δ ∈ ZIrr G ∧ ClassFunction.IsReal Δ ∧
        ClassFunction.inner Δ
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 ∧
        ClassFunction.inner betaData.Gamma a =
          1 + ClassFunction.inner Δ betaData.Gamma := by
    intro a ha
    rw [hcalT1img, Finset.mem_image] at ha
    obtain ⟨ζ, hζT, rfl⟩ := ha
    rw [Set.mem_toFinset] at hζT
    have hζform := hζT
    rw [hcalT1, Finset.mem_coe, Finset.mem_image] at hζform
    obtain ⟨θ, hθ, hζeq⟩ := hζform
    have hζ1_ind :=
      typeIII_induced_source_degree hyp θ (hlinear θ hθ)
    have hζ1 : ζ 1 = (hyp.base.p : ℂ) :=
      hζeq ▸ hζ1_ind
    have hζirr_ind : IsIrreducibleCharacter (ClassFunction.induce
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction) := by
      simpa only [hζeq] using hirr ζ hζT
    obtain ⟨ν0, hνZ, hνR, hβZ, hβsupp, hτβZ, hτβ1, hβconj,
        hνinner, hνζ, hνζc, hβnorm, hτβnorm, hνfixed⟩ :=
      exists_typeIII_induced_primeTIDifference_with_norm_anchor_orthogonality_and_galois
        hG hyp hIII θ (hne θ hθ) hζirr_ind hζ1_ind
    rw [hζeq] at hβZ hβsupp hτβZ hτβ1 hβconj hνζ hνζc hβnorm hτβnorm
    have hζone : ClassFunction.inner ζ
        (trivialClassFunction ↥hyp.base.T) = 0 := by
      rw [← hζeq]
      exact OddOrder.Peterfalvi.S09.Cert.inner_induce_constOne_eq_zero
        ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ (hne θ hθ)
    have hβinner : ClassFunction.inner (ν0 - ζ)
        (trivialClassFunction ↥hyp.base.T) = 1 := by
      rw [ClassFunction.inner_sub_left, hνinner, hζone, sub_zero]
    obtain ⟨mT, hmT, hpythT, hboundT, hprincipalT, hrelationT⟩ :=
      exists_tSide_etaGrid_intProjection_with_relation hG hyp hIII hβsupp hβinner hτβZ hτβnorm
    have hperpT := tSide_etaGridProjection_residual_ne_zero_of_anchor_orthogonal
      hG hyp hIII hyp07 hτ
      (fun ξ hξ => hdiff_supp ξ hξ ξ.conj (hyp07.conjugate_closed hξ))
      hζT (hirr ζ hζT) hβsupp hνζ hνζc mT
    have hsumSqT :
        (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (mT i j) ^ 2 : ℤ) ≤
          (hyp.base.p : ℤ) :=
      etaGrid_projection_sum_sq_le_of_residual_ne_zero
        hyp.base hτβZ hτβnorm mT hmT hperpT
    have horbits := eta_axis_galois_orbits_of_hypothesis hyp.base
    have haxis := tSideDadeMap_eta_axis_coefficients_constant
      hG hyp hβZ hβsupp hτ hζT hgaloisT hdiff_supp
      (fun ξ hξ i j =>
        T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
          hyp07.conjugate_closed hyp07.no_real_characters
          (fun χ hχ => hdiff_supp χ hχ χ.conj (hyp07.conjugate_closed hχ))
          hτ hξ (hirr ξ hξ) i j)
      mT hmT hνfixed horbits.1 horbits.2
    have hshape := etaGrid_coefficients_eq_column_or_row_of_sum_sq_le
      hyp.base hyp.q_lt_p mT hprincipalT haxis.1 haxis.2 hrelationT hsumSqT
    have hτβinner : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 1 := by
      change ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
        (trivialClassFunction G) = 1
      rw [tSideDadeMap_inner_trivial hyp hG hβsupp, hβinner]
    have htrivSelf : ClassFunction.inner
        (trivialIrreducibleCharacter G : ClassFunction G ℂ)
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 1 :=
      (trivialIrreducibleCharacter G).isIrreducible.inner_self_eq_one
    have hζcT : ζ.conj ∈ calT1_set := hyp07.conjugate_closed hζT
    have hExtOne : ClassFunction.inner (hτ.extension ζ)
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
      change ClassFunction.inner (hτ.extension ζ)
        (trivialClassFunction G) = 0
      exact tSideCoherentExtension_inner_trivial hyp hG hyp07 hτ hζT
        (hirr ζ hζT) hζone
        (hdiff_supp ζ.conj hζcT ζ hζT)
    have hExtConj : (hτ.extension ζ).conj = hτ.extension ζ.conj :=
      tSideCoherentExtension_conj hyp hG hIII 𝒯 hne calT1_set hcalT1
        hyp07 hτ hirr hζT
    have hζdiffSupp : (ζ - ζ.conj).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T :=
      hdiff_supp ζ hζT ζ.conj hζcT
    let Δ : ClassFunction G ℂ :=
      tSideDadeMap hyp hG (ν0 - ζ) -
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        hτ.extension ζ
    have hOneZ :
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) ∈ ZIrr G :=
      (trivialIrreducibleCharacter G).mem_ZIrr
    have hExtZ : hτ.extension ζ ∈ ZIrr G :=
      hτ.extension_mem_ZIrr ζ (Submodule.subset_span hζT)
    have hΔZ : Δ ∈ ZIrr G := by
      change tSideDadeMap hyp hG (ν0 - ζ) -
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        hτ.extension ζ ∈ ZIrr G
      exact (ZIrr G).add_mem ((ZIrr G).sub_mem hτβZ hOneZ) hExtZ
    have hΔreal : ClassFunction.IsReal Δ := by
      change ClassFunction.IsReal
        (tSideDadeMap hyp hG (ν0 - ζ) -
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
          hτ.extension ζ)
      exact tSideDelta_isReal hyp hG hτ hζT hζcT hβsupp hζdiffSupp
        hβconj hExtConj
    have hΔone : ClassFunction.inner Δ
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0 := by
      change ClassFunction.inner
          (tSideDadeMap hyp hG (ν0 - ζ) -
              (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
            hτ.extension ζ)
          (trivialIrreducibleCharacter G : ClassFunction G ℂ) = 0
      rw [ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
        hτβinner, htrivSelf]
      rw [hExtOne]
      norm_num
    have hrelation : ClassFunction.inner betaData.Gamma (hτ.extension ζ) =
        1 + ClassFunction.inner Δ betaData.Gamma := by
      -- The remaining deep input is now exact: Coq (11.8) rules out the
      -- zero-row branch of the proven (11.9) column-or-row dichotomy.
      -- The S/T cross orthogonality is no longer assumed: the landed exact-support
      -- consumer proves it from prime-TI support, Type-P₁ normed-TI, and order separation.
      have hresidual :
          (∑ i : Fin hyp.base.q, ∑ j : Fin hyp.base.p, (mT i j) ^ 2 : ℤ) ≤
              (hyp.base.p : ℤ) ∧
          (∀ j : Fin hyp.base.p,
            ClassFunction.inner
                (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)
                (tSideDadeMap hyp hG (ν0 - ζ)) =
              ClassFunction.inner
                (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ j)
                (∑ i : Fin hyp.base.q,
                  hyp.base.eta i ⟨0, hyp.base.p_prime.pos⟩)) := by
        refine ⟨hsumSqT, ?_⟩
        rcases hshape with hcolumn | hrow
        · exact etaGrid_zeroColumn_projection_of_coefficients_eq_column
            hyp.base (tSideDadeMap hyp hG (ν0 - ζ)) mT hmT hcolumn
        · -- Coq (11.8): exclude the zero-row projection.
          exfalso
          sorry
      have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := by
        obtain ⟨_, _, hcIII_IV, _, _, _⟩ :=
          OddOrder.BG.Ch4.S16.proposition_type_classification
            hG hyp.base.T_maximal
        exact (hcIII_IV.mp (Or.inl hIII)).1
      let dataT :=
        (OddOrder.Peterfalvi.S15.reconciled_typePData_T hG hyp.base).choose
      have hcross :
          ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
            (OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base) = 0 :=
        tSideDadeMap_inner_tauSbetaGrid_eq_zero hG hyp dataT hP1 hβsupp
      have hτβeta : ClassFunction.inner (tSideDadeMap hyp hG (ν0 - ζ))
          (hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩
            ⟨1, by have := hyp.base.three_le_p; omega⟩) = 0 := by
        have hne0 :
            (⟨1, by have := hyp.base.three_le_p; omega⟩ : Fin hyp.base.p) ≠
              ⟨0, hyp.base.p_prime.pos⟩ := by
          intro h
          have hv := congrArg Fin.val h
          norm_num at hv
        have hrow := tSide_beta_inner_eta_of_zeroColumn_projection
          hyp.base (tSideDadeMap hyp hG (ν0 - ζ)) hresidual.2
          ⟨1, by have := hyp.base.three_le_p; omega⟩
        simpa only [if_neg hne0] using hrow
      have hΓdef : betaData.Gamma =
          OddOrder.Peterfalvi.S15.tauSbetaGrid hG hyp.base -
              (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
            hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩
              ⟨1, by have := hyp.base.three_le_p; omega⟩ := by
        rfl
      have hΔdef : Δ =
          tSideDadeMap hyp hG (ν0 - ζ) -
              (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
            hτ.extension ζ := by
        rfl
      exact gap_cross_inner_identity hGammaZ hExtZ hOneZ hΓdef hΔdef
        hτβinner hcross hτβeta hGamma1
    exact ⟨Δ, hΔZ, hΔreal, hΔone, hrelation⟩
  obtain ⟨x, hxcoe, hx⟩ :
      ∃ (x : ClassFunction G ℂ → ℤ),
        (∀ a ∈ calT1, ClassFunction.inner betaData.Gamma a = ((x a : ℝ) : ℂ)) ∧
        (∀ a ∈ calT1, x a ≠ 0) := by
    exact gap_coefficients_nonzero_of_delta_parity hG.odd calT1 betaData.Gamma
      hGammaZ hGammaR hGamma1 hmemZ hDelta
  have heta : ∀ a ∈ calT1, ∀ (i : Fin hyp.base.q) (k : Fin hyp.base.p),
      ClassFunction.inner a (hyp.base.eta i k) = 0 := by
    intro a ha i k
    rw [hcalT1img, Finset.mem_image] at ha
    obtain ⟨ζ, hζT, rfl⟩ := ha
    rw [Set.mem_toFinset] at hζT
    exact T_typeIII_coherent_image_inner_eta_eq_zero hG hyp hIII
      hyp07.conjugate_closed hyp07.no_real_characters
      (fun χ hχ => hdiff_supp χ hχ χ.conj (hyp07.conjugate_closed hχ))
      hτ hζT (hirr ζ hζT) i k
  exact T_typeIII_ratio_le_of_sSide_gap hyp calT1 horth hcount
    betaData.Gamma x hxcoe hx heta betaData.Y_norm_bound

/-- **Complement-conjugacy transfer of commutativity `V → d.U`** (`T`-side, ungated by (14.9)).
Given that the `κ`-Hall complement `V` of `Q = T_F` in `T' = [T,T]` is abelian, *any* type-`P`
witness `d` on `T` has its own derived complement `d.U` (the `H = M_F` complement in `T'`) abelian
too.  Both `V` and `d.U` complement the *same* normal Hall subgroup `Q = d.H` in `T'` (`Q ⋊ V = T' =
Q ⋊ d.U`), so Schur–Zassenhaus conjugacy inside `↥T'` (`IsComplement'.exists_conj_of_coprime`,
coprimality from `Q` being Hall in `T`) conjugates `V` onto `d.U`, transporting `IsMulCommutative`.

Structurally the mirror of `S15.isMulCommutative_V` (which runs `d.U → V`); the sole difference is
that the `(|Q|, |V|)`-coprimality is sourced from `maxNilpotentNormalHall_isHall` +
`IsHallSubgroup.coprime_index` (with `|V| = [T':Q] ∣ [T:Q]` via the tower law) rather than from a
`TypeIIData`, so it is available for a *generic* `TypePData d`. -/
theorem isMulCommutative_typePData_U_of_V [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (d : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hVcomm : IsMulCommutative ↥hyp.base.V) :
    IsMulCommutative ↥d.U := by
  have hdisj : hyp.base.Q ⊓ hyp.base.V = ⊥ := hyp.base.Q_inf_V_eq_bot
  have hQH : hyp.base.Q = d.H := by rw [hyp.base.Q_eq_TF, d.H_eq]
  have hQ_le : hyp.base.Q ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_left
  have hV_le : hyp.base.V ≤ derivedInG hyp.base.T := by
    rw [hyp.base.T_deriv_eq_QV]; exact le_sup_right
  have hM'_le_T : derivedInG hyp.base.T ≤ hyp.base.T := Subgroup.map_subtype_le _
  have hQ_le_T : hyp.base.Q ≤ hyp.base.T := by
    rw [hyp.base.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.base.T
  have hT_le_NQ : hyp.base.T ≤ Subgroup.normalizer (hyp.base.Q : Set G) := by
    rw [hyp.base.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.base.T
  haveI hQn_normal : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).mpr (hM'_le_T.trans hT_le_NQ)
  have hVcompl : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).IsComplement'
      (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
        OneMemClass.coe_one]
      refine ⟨fun ⟨hxQ, hxV⟩ => ?_, fun h => by simp [h]⟩
      have hxQV : x ∈ (hyp.base.Q ⊓ hyp.base.V : Subgroup G) := ⟨hxQ, hxV⟩
      rwa [hdisj, Subgroup.mem_bot] at hxQV
    · have hsup : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ⊔
          (hyp.base.V.subgroupOf (derivedInG hyp.base.T)) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hQ_le hV_le, hyp.base.T_deriv_eq_QV.symm,
          Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul (hyp.base.Q.subgroupOf (derivedInG hyp.base.T))
        (hyp.base.V.subgroupOf (derivedInG hyp.base.T))
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hV'compl : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).IsComplement'
      (d.U.subgroupOf (derivedInG hyp.base.T)) := by
    rw [hQH]; exact d.derived_complement
  have hcop : Nat.Coprime (Nat.card ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)))
      ((hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).index) := by
    -- `|Q|` (Hall in `T`) is coprime to `[T:Q]`; and `[T':Q] ∣ [T:Q]` by the tower law
    -- (`Q ≤ T' ≤ T`).  `(Q.subgroupOf T').index = Q.relIndex T' ∣ Q.relIndex T`.
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.base.T
    rw [← hyp.base.Q_eq_TF] at hHall
    have h0 := OddOrder.Isaacs.Ch03.IsHallSubgroup.coprime_index hHall
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_T).toEquiv] at h0
    -- `h0 : Nat.Coprime (Nat.card ↥Q) (Q.relIndex T)`
    have hcard : Nat.card ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) = Nat.card ↥hyp.base.Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv
    have hdvd : (hyp.base.Q.subgroupOf (derivedInG hyp.base.T)).index ∣
        (hyp.base.Q.subgroupOf hyp.base.T).index := by
      have htower : hyp.base.Q.relIndex (derivedInG hyp.base.T) *
          (derivedInG hyp.base.T).relIndex hyp.base.T = hyp.base.Q.relIndex hyp.base.T :=
        Subgroup.relIndex_mul_relIndex hyp.base.Q (derivedInG hyp.base.T) hyp.base.T hQ_le hM'_le_T
      show hyp.base.Q.relIndex (derivedInG hyp.base.T) ∣ hyp.base.Q.relIndex hyp.base.T
      exact ⟨(derivedInG hyp.base.T).relIndex hyp.base.T, htower.symm⟩
    rw [hcard]
    exact Nat.Coprime.coprime_dvd_right hdvd h0
  have hQ_lt_top : hyp.base.Q < ⊤ :=
    lt_of_le_of_lt hQ_le_T (lt_top_iff_ne_top.mpr (mem_maximalSubgroups.mp hyp.base.T_maximal).1)
  haveI hQsolv : IsSolvable ↥hyp.base.Q := hG.solvable_of_lt_top hyp.base.Q hQ_lt_top
  have hsolv : IsSolvable ↥(hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) ∨
      IsSolvable (↥(derivedInG hyp.base.T) ⧸ hyp.base.Q.subgroupOf (derivedInG hyp.base.T)) :=
    Or.inl (solvable_of_solvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQ_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hQ_le).injective)
  obtain ⟨n, _hnQ, hn⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop hsolv hVcompl hV'compl
  -- `hn : (V.subgroupOf T').map (conj n) = d.U.subgroupOf T'`.  Push `V` commutative forward.
  have hVsub : IsMulCommutative ↥(hyp.base.V.subgroupOf (derivedInG hyp.base.T)) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hV_le).symm hVcomm
  have hmapped : IsMulCommutative
      ↥((hyp.base.V.subgroupOf (derivedInG hyp.base.T)).map (MulAut.conj n).toMonoidHom) :=
    OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.equivMapOfInjective _ _ (MulAut.conj n).injective) hVsub
  rw [hn] at hmapped
  exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe d.U_le) hmapped

/-- **Peterfalvi (11.9)/(14.9), the Type-IV exclusion residual** — the genuine deep content of the
type determination.  Coq `FTtype34_structure` (Peterfalvi (11.9), `PFsection11.v:1001`, consumed at
`PFsection14.v:735`) pins a non-type-II type-`P` maximal `T` to Type III (not IV) via the
character/Galois argument `suffices galM : typeP_Galois MtypeP` (`PFsection11.v:1139`) — the
`η`-grid projection computation `a₁₁ = a₁₀ = 0`.  In this formalisation the III/IV discriminator is
`IsMulCommutative U` (`TypeIIIData` carries `U_commutative`, `TypeIVData` its negation), so the
(11.9) content is exactly: *`T`'s derived complement `U`-factor (`= V`) is abelian*.

This is genuine §11 character theory — **not** a σ-structural config fact — and is formalised
nowhere in this repo (the §11/§13 layer `S13_MaximalIII_IV` only ever *posits* `IsTypeIII M ∨
IsTypeIV M`, and there is no universal Type-IV exclusion analogous to the proven Type-V one
`no_typeV_maximal`).  Isolated here as the *single* residual of the (14.9) type determination:
everything else (Type-V exclusion, the III/IV structural wiring incl. `normalizer_le`) is proven in
`T_isTypeIII_of_isTypeP1` below. -/
theorem T_not_isTypeIV_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    ¬ OddOrder.GroupTheory.IsTypeIV hyp.base.T := by
  -- Coq (11.9) `FTtype34_structure` ⟹ `typeP_Galois T` ⟹ (in the `IsMulCommutative U` presentation)
  -- the `U = V` factor is abelian, so `T` is Type III not IV.  The deep character/projection argument
  -- is now isolated to the single residual `hVcomm` (`V` abelian); everything else is the honest
  -- complement-conjugacy transfer `isMulCommutative_typePData_U_of_V`.
  --
  -- EXACT REDUCTION of `IsMulCommutative V` (verified against Coq `PFsection{9,11}.v`, 2026-07-06):
  --   V abelian  ⟸  `cyclic V`  ⟸  `typeP_Galois T`  (the genuine (11.9) content).
  -- Coq chain (`FTtype34_structure`, `PFsection11.v:1139-1144`):
  --   `suffices galM : typeP_Galois MtypeP` (`:1139`); then
  --   `typeP_Galois_P` (`PFsection9.v:501-511`) extracts `cyclic Ubar` (`:1140`), and
  --   `cyclic V` + `nilpotent V` ⟹ `cyclic V` ⟹ `abelian V`
  --   (`cyclic_nilpotent_quo_der1_cyclic`/`cyclic_abelian`, `:1144`).
  -- `typeP_Galois := acts_irreducibly U Hbar 'Q` (`PFsection9.v:323`): `V` acts IRREDUCIBLY on
  -- `Hbar = Q/Φ(Q)`.  Proving THAT is the `η`-grid projection `a₁₁ = a₁₀ = 0` (`PFsection11.v:1041-
  -- 1126`), whose inputs are the FULL §3–§11 apparatus: `S₁`-coherence (`cohS1`), the Dade isometry
  -- (`Dade_isometry`/`Dade_reciprocity`, §4/§5), the cyclic-TI isometry (`cycTIiso`,
  -- `coherent_ortho_cycTIiso`, §3), and prime-TI reducibles (`prTIred`) — via the norm bound
  -- `⟨X,X⟩ ≤ q` and odd-order parity.  So this is genuinely (11.9)-GATED, NOT σ-theory: the §9/§13
  -- σ-engine (`card_le_cyclotomicQuotient_of_faithful_fpf`, `TypePGaloisUBound.lean`) is the (13.2.c)
  -- `u`-bound `|V| ≤ (p^q−1)/(p−1)` which CARRIES `[CommGroup V]` as a hypothesis — it consumes
  -- commutativity, never proves it.
  --
  -- WHY NOT STRUCTURALLY FREE (contrast S-side): the S-side `U` is abelian for free via BG 15.1(b)
  -- (`typeP_hall_derived_eq_and_abelian`, `⁅U,U⁆ ≤ U ⊓ M_σ = ⊥`) BECAUSE `U` is the `(κ∪σ)'`-Hall
  -- of `S`.  For type `P₁` (`IsTypeP1 T ⟺ κ(T) = σ'(T) = π(T) ∖ σ(T)`, `S14.IsTypeP1`), the
  -- `(κ∪σ)'`-Hall is TRIVIAL (`κ ∪ σ = π`) and `V` is instead the κ-Hall complement to `Q = T_F` in
  -- `T' = Q ⋊ V`; with `T_F ⊊ M_σ` (III/IV case) one gets `V ⊓ M_σ ≠ ⊥` (exactly the σ-part that,
  -- at type IV, is where non-commutativity lives), so the `⁅V,V⁆ ≤ V ⊓ M_σ = ⊥` mechanism FAILS.
  -- Structurally `V` is only known to be a nilpotent Frobenius kernel (`Hypothesis.isNilpotent_V`,
  -- `V ⋊ W₂` Frobenius with `C_V(W₂) = ⊥`) — nilpotent ⇏ abelian.  No lane-c-doable sub-part
  -- advances this: even the final `nilpotent + cyclic V/V' ⟹ abelian` step needs `cyclic V`, which
  -- is downstream of `typeP_Galois`.  Missing bridge (Lean): a `typeP_Galois`/`cyclic V` producer,
  -- itself requiring the §5–§11 coherence/Dade layer (S05/S06/S07 Dade + coherence, still sorried).
  have hVcomm : IsMulCommutative ↥hyp.base.V := sorry  -- (11.9)-gated: V (=T's U-factor) abelian ⟸ `cyclic V` ⟸ `typeP_Galois T`
  rintro ⟨d⟩
  exact d.U_not_commutative (isMulCommutative_typePData_U_of_V hG hyp d.typeP hVcomm)

/-- **Peterfalvi (14.9), the type determination** — Coq `PFsection14`
`have [_ _ [Ttype3 _]] := FTtype34_structure maxT TtypeP notTtype2` (line 735): a type-`P` maximal
subgroup that is *not* type II is type III.  In σ-theoretic terms, `IsTypeP1 T` (equivalently
`¬ IsTypeP2 T` given `IsTypeP T`) forces `T` to be structurally Type III.

**Fully reduced to the single (11.9) residual `T_not_isTypeIV_of_isTypeP1`.**  The type dictionary
`proposition_type_classification` (BG Prop 16.1, proven) gives, from `IsTypeP1 T`, either Type III/IV
(if `M_F ≠ M_σ`) or Type V (if `M_F = M_σ`).  **Type V is excluded outright** by Peterfalvi (10.10)
`no_typeV_maximal` (proven — no maximal subgroup of a minimal simple group of odd order is Type V),
so `M_F ≠ M_σ` and `T` is Type III or IV.  Excluding Type IV — the genuine (11.9) Galois/character
content — is the isolated residual `T_not_isTypeIV_of_isTypeP1`.  The Type-V exclusion and the III/IV
structural wiring (incl. the `TypeIIIData.normalizer_le` field, bundled into the clause-(c)
disjunction) are proven here. -/
theorem T_isTypeIII_of_isTypeP1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T) :
    OddOrder.GroupTheory.IsTypeIII hyp.base.T := by
  -- Type dictionary (BG Prop 16.1): `IsTypeP1 T` ⟹ III/IV (`M_F ≠ M_σ`) or V (`M_F = M_σ`).
  obtain ⟨_, _, hcIII_IV, hdV, _, _⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.base.T_maximal
  -- Type V excluded universally by Peterfalvi (10.10) `no_typeV_maximal`, so `M_F ≠ M_σ`.
  have hMF : OddOrder.BG.Ch4.S15.MF hyp.base.T ≠ OddOrder.BG.Ch3.S10.Msigma hyp.base.T := fun h =>
    OddOrder.Peterfalvi.S12.no_typeV_maximal hG ⟨hyp.base.T, hyp.base.T_maximal, hdV.mpr ⟨hP1, h⟩⟩
  -- `T` is Type III or IV; exclude IV by the (11.9) residual.
  exact (hcIII_IV.mpr ⟨hP1, hMF⟩).resolve_right (T_not_isTypeIV_of_isTypeP1 hG hyp hP1)

/-- **Peterfalvi (14.9), reduced to its canonical residual** — the `T`-side dual of the `S`-side
`(13.2.a)` carrier field `S_typeP2`.  `T` is of BG type `P₂` (`κ(T) ≠ σ'(T)`; Coq `PFsection14`
`FTtypeP_min_typeII : FTtype T == 2`).  The `IsTypeP T` conjunct is discharged honestly from `T_nonI`
(`isTypeP_of_isTypeNonI`).

The residual `κ(T) ≠ σ'(T)` is proved by the (14.9) contradiction, following Coq
`FTtypeP_min_typeII` (`apply: contraLR v1p_gt_u1q => notTtype2`): were `κ(T) = σ'(T)` (i.e.
`IsTypeP1 T`), then `T` is Type III (`T_isTypeIII_of_isTypeP1`, the `FTtype34_structure`
determination), whence the character body forces `(v − 1)/p ≤ (u − 1)/q` (`T_typeIII_ratio_le`) —
contradicting (14.8) `key_inequality`'s `(v − 1)/p > (u − 1)/q`.

The two deep pieces are isolated as `T_typeIII_ratio_le` (character body) and
`T_isTypeIII_of_isTypeP1` (type determination), both consumed below.  The `>` half is (14.8): its
pure cyclotomic comparison lives upstream in `KeyInequalityArithmetic`, while the two group-theoretic
order inputs are the direct (13.4) producer `T_side_caseB_facts` and the (13.15) producer
`S15.caseB_order_u_data`.  Thus no forward reference through the later `key_inequality` theorem is
needed. -/
theorem T_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP2 hyp.base.T := by
  have hP : OddOrder.BG.Ch4.S14.IsTypeP hyp.base.T :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.base.T_maximal hyp.base.T_nonI
  refine ⟨hP, ?_⟩
  -- (14.9), by contradiction (Coq `contraLR v1p_gt_u1q => notTtype2`): assume `κ(T) = σ'(T)`.
  intro hκeq
  -- Then `T` is type `P₁`, hence (Coq `FTtype34_structure`) structurally Type III.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T := ⟨hP, hκeq⟩
  have hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T := T_isTypeIII_of_isTypeP1 hG hyp hP1
  -- The character body then gives the type-III Γ-bridge estimate `(v − 1)/p ≤ (u − 1)/q`.
  have hle : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) ≤
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := T_typeIII_ratio_le hG hyp hIII
  -- The arithmetic half of (14.8), separated from the later `key_inequality` packaging.
  have hratio := cyclotomic_ratio_gt_of_q_lt_p
    hyp.base.p_prime hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p
  -- Its T-side order input is the direct (13.4) producer, which is upstream of `T_isTypeP2`.
  have hvfull := (T_side_caseB_facts hG hyp).2
  -- The S-side order input is exactly the two-branch conclusion of (13.15).
  let Sord := OddOrder.Peterfalvi.S15.caseB_order_u_data hG hyp.base (caseB_for_S := True) trivial
  have hu_le_full :
      hyp.base.u ≤ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) := by
    by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
    · rw [Sord.u_eq_of_p_modEq_one hmod]
      have hp1_pos : 0 < hyp.base.p - 1 := by
        have hp2 : 2 ≤ hyp.base.p := hyp.base.p_prime.two_le
        omega
      have hden_le : hyp.base.p - 1 ≤ hyp.base.q * (hyp.base.p - 1) := by
        have hqpos : 1 ≤ hyp.base.q := hyp.base.q_prime.one_le
        nlinarith [Nat.mul_le_mul_right (hyp.base.p - 1) hqpos]
      exact Nat.div_le_div_left hden_le hp1_pos
    · rw [Sord.u_eq_of_not_modEq_one hmod]
  have hqpos : (0 : ℚ) < hyp.base.q := by
    exact_mod_cast hyp.base.q_prime.pos
  have hu_sub : ((hyp.base.u - 1 : ℕ) : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le_sub_right hu_le_full 1
  have hu_div : ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) ≤
      (((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 : ℕ) : ℚ) /
        (hyp.base.q : ℚ) :=
    div_le_div_of_nonneg_right hu_sub (le_of_lt hqpos)
  have hgt : ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
      ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ) := by
    rw [hvfull]
    exact lt_of_le_of_lt hu_div hratio
  exact absurd hle (not_le.mpr hgt)

/-- **Peterfalvi (14.9)**: the subgroup `T` is of Type II.  Dual to the `S`-side `(13.2.a)` line
`isTypeII_of_isTypeP2 … S_maximal S_typeP2`: `T` is of type `P₂` (`T_isTypeP2`), and *every* type-`P₂`
maximal subgroup is type II by the proven BG bridge `isTypeII_of_isTypeP2`.  That bridge discharges
the deep `M'`-type-`F` structure — `IsTypeF (derivedInG T)` and `(T')_F = T_F` — internally
(`isTypeF_derivedInG_of_isTypeP2`), so the sole residual of (14.9) is the type-`P₂` fact `T_isTypeP2`.
(Placed ahead of `exists_LHypothesis` so the §14 `T`-side chain — `typeII_overNormalizer_frobenius`
etc. — can cite `IsTypeII T` locally.) -/
theorem T_typeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    IsTypeII hyp.base.T :=
  OddOrder.BG.Ch4.S16.isTypeII_of_isTypeP2 hG hyp.base.T_maximal (T_isTypeP2 hG hyp)

end OddOrder.Peterfalvi.S16
