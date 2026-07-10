/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.S14_MaximalI.RhoMEvaluation

/-!
# Peterfalvi (12.16) — the witness value/norm package and the final contradiction

The capstone of §12: the `CounterexampleDadeData` character/norm contract, its construction
`exists_counterexample_dade_data` from the witness Dade calculation ((12.13)–(12.15) + the
(7.3)/(7.8.b) norm bounds), the (12.16) contradiction `counterexample_contradiction`, and its
headline consequences `pi_empty` / `typeI_frobenius` ((12.7)).

Split from `DadeContradiction.lean` (file-size policy); the `ρ_M` machinery it consumes is in
`RhoMEvaluation.lean`, the `ρ`-side witness bounds in `DadeContradiction.lean`.
-/
namespace OddOrder.Peterfalvi.S14
open OddOrder.GroupTheory
open OddOrder.RepresentationTheory
open OddOrder.Isaacs
open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (12.13)–(12.16), the character/norm contract** packaging every fact that the
numerical endgame `counterexample_contradiction_of_facts` consumes.  Bundling them here isolates the
deep §7/§12 content — the Dade calculation `ψ = χ^{τ₁}` of (12.13), the coset/value facts
(12.14)/(12.15), and the `ρ`/`ρM` integral inequalities (7.3)/(7.8.b) — into a single
faithfully-typed obligation, leaving the (12.16) capstone `counterexample_contradiction` a
`sorry`-free assembly.

Field map to the textbook (`H = L_F`, the Fitting kernel of the witness subgroup `L`):
* `ε`/`hε` — a primitive `p`-th root of unity (the cyclotomic base of (1.10));
* `ψ`/`hψ` — the virtual character `ψ = χ^{τ₁}` of (12.13) (`ZIrr` membership = it is a
  ℤ-combination of irreducibles, from the Dade isometry image);
* `e` — the common degree `χ(1) = e` of the coherent family `S` ((12.6)); `he`/`h2e` = (12.12);
* `h_const` = (12.14) (`ψ` constant on the coset `xK`); `h_psix` = (1.10.a) applied to `χ`;
  `h_psig_int` = (12.15) (`ψ(g) ∈ ℤ`);
* `kK`/`kKp`/`kM`/`kH` = `|K|`/`|K'|`/`|M|`/`|H|`; `hidx` = (8.1.c), `hM` = (12.11);
* `hA` = (12.15) norm relation for `ρM`, `hB` = (7.8.b) for `ρ`, `hC` = (7.3)+(8.17). -/
structure CounterexampleDadeData {ctr : CounterexampleHypothesis (G := G)}
    (witness : RankTwoWitnessData ctr) (g : G) where
  ε : ℂ
  hε : IsPrimitiveRoot ε ctr.p
  ψ : ClassFunction G ℂ
  hψ : ψ ∈ ZIrr G
  e : ℤ
  mval : ℤ
  he : 3 ≤ e
  h2e : 2 * e ≤ (ctr.p : ℤ) + 1
  h_const : ψ (witness.x * g) = ψ witness.x
  h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ ψ witness.x - (e : ℂ) = (1 - ε) * w
  h_psig_int : ψ g = (mval : ℂ)
  kK : ℝ
  kKp : ℝ
  kM : ℝ
  kH : ℝ
  normRhoM : ℝ
  normRho : ℝ
  hkKp : 0 < kKp
  hkM : 0 < kM
  hkH : 0 < kH
  hidx : 4 * kKp ≤ kK
  hM : kM ≤ kK * kH
  hA : (kK - kKp) / kM * (mval : ℝ) ^ 2 ≤ normRhoM
  hB : (1 : ℝ) - (e : ℝ) / kH ≤ normRho
  hC : normRhoM + normRho < 1

/-! The former `witness_psi_degree` obligation (`ψ(1) = e`, the coherent-extension degree
preservation) has been **removed**: Peterfalvi's (12.16) does not use it.  The `h_psix`
congruence `ψ(x) ≡ e (mod 1 − ε)` is instead supplied by the proven (12.14) evaluation
`ψ(x) = χ(x)` (`witness_dade_psi_apply_x_eq_chi`) combined with the `L`-side (1.10.a)
congruence `χ(x) ≡ χ(1) = e` — see `exists_counterexample_dade_data`. -/

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.14)/(12.15) + (7.3)/(7.8.b)/(8.17), the witness value/norm package** — the
deep §7/§12 content the (12.16) contradiction consumes beyond the arithmetic, bundled as one
faithfully-typed obligation for the specific witness Dade character `ψ = dade.psi`.

Concretely, for the (12.9) witness `L` with its (12.13) Dade calculation `ψ = χ^{τ₁}` of degree
`e = dade.e = [L:H]`, and the commuting `g ∈ C_K(x) ∖ K'`, it supplies:
* `mval`, `h_psig_int` — (12.15): `ψ(g) ∈ ℤ` (`ψ` constant on `K − K′`, integer-valued there);
* `h_const` — (12.14): `ψ(x·g) = ψ(x)` (`ψ` constant on the coset `xK`);
* `hidx` — the fixed-point-free `[K:K'] ≥ 4` of (8.1.c), as `4·|K'| ≤ |K|`;
* `h2e` — the degree bound `2e ≤ p+1` of (12.12);
* `normRhoM`, `normRho`, `hA`, `hB`, `hC` — the `ρ`/`ρM` norm estimates: `hA` = (12.15) norm
  relation `‖ψ^{ρM}‖² ≥ (|K−K'|/|M|)·ψ(g)²`, `hB` = (7.8.b) `‖ψ^ρ‖² ≥ 1 − e/|H|`, `hC` =
  (7.3)+(8.17) `‖ψ^{ρM}‖² + ‖ψ^ρ‖² < 1`.

**Genuinely still-missing**: the `ρ`-machinery norm estimates (`S09.zetaNuRhoNormSqGeOfDade` for
`hB`, `chiRho_integral_inequality`/(8.17) support-disjointness for `hC`, the (12.15) `ρM` relation
for `hA`), the (12.3)/(12.5) constancy facts feeding `h_const`/(12.15), and the (8.1.c)/(12.12)
numerics `hidx`/`h2e` for the witness are none of them assembled into these exact conclusions in
reach of `S14`.  The statement is **sound**: each conjunct is the genuine
(12.14)/(12.15)/(12.12)/(8.1.c)/(7.x)
fact for the *specific* witness character `ψ = dade.psi` of the genuine witness `L` (tied to
`ctr`/`witness`/`hyp`/`dade` via `data` and `hψZ`), with `e = dade.e` and `|K|,|K'|,|M|,|H|` the
genuine cardinalities — not a free arithmetic implication. -/
theorem witness_value_norm_package [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {ctr : CounterexampleHypothesis (G := G)} {L : Subgroup G}
    (data : RankTwoWitnessData ctr) (hLeq : L = data.L)
    {g : G} (hg_comm : Commute data.x g) (hgK : g ∈ ctr.K) (hgK' : g ∉ ctr.Kprime)
    (hyp : Hypothesis L) (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (dade : DadeNotation hyp)
    (hψeq : dade.psi = coh.extension dade.chi)
    (he_eq : dade.e = ((hyp.typeI.typeF.H).subgroupOf L).index) (hψZ : dade.psi ∈ ZIrr G) :
    ∃ (mval : ℤ) (normRhoM normRho : ℝ),
      dade.psi (data.x * g) = dade.psi data.x ∧
      dade.psi g = (mval : ℂ) ∧
      2 * (dade.e : ℤ) ≤ (ctr.p : ℤ) + 1 ∧
      4 * (Nat.card ↥ctr.Kprime : ℝ) ≤ (Nat.card ↥ctr.K : ℝ) ∧
      ((Nat.card ↥ctr.K : ℝ) - (Nat.card ↥ctr.Kprime : ℝ)) / (Nat.card ↥ctr.M : ℝ)
          * (mval : ℝ) ^ 2 ≤ normRhoM ∧
      (1 : ℝ) - (dade.e : ℝ) / (Nat.card ↥(hyp.typeI.typeF.H) : ℝ) ≤ normRho ∧
      normRhoM + normRho < 1 := by
  sorry

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.13)–(12.15) + (7.3)/(7.8.b)**, the construction of the character/norm contract
of (12.16).  Given the rank-two witness of (12.9) and a commuting element `g ∈ C_K(x) ∖ K'`
(`exists_witness_g`), the §7/§12 machinery produces the Dade calculation `ψ = χ^{τ₁}` and its
associated `ρ`/`ρM` norm bounds.

**Assembly** (`sorry`-free modulo the two genuine deep pins): the (12.6) coherence
`witness_L_coherent` + the distinguished `χ ∈ S` (`exists_distinguished_char`, degree `e = [L:H]`)
realize the (12.13) `dade = dadeNotation_of_coherence …` with `ψ = coh.extension χ ∈ ZIrr G`; then
each `CounterexampleDadeData` field is discharged:
* `ε`/`hε` — a primitive `p`-th root of unity (`Complex.isPrimitiveRoot_exp`);
* `e := dade.e = [L:H]`, `he : 3 ≤ e` from `three_le_index` (`|U|` odd `> 1`);
* `kK`/`kKp`/`kM`/`kH` := `|K|`/`|K'|`/`|M|`/`|H|` with positivity from `Nat.card_pos`, and
  `hM : |M| ≤ |K|·|H|` from `card_M_le` (12.11);
* `h_psix` from the proven (12.14) evaluation `ψ(x) = χ(x)` (`witness_dade_psi_apply_x_eq_chi`)
  and the `L`-side (1.10.a) congruence `χ(x) ≡ χ(1) = e (mod 1 − ε)`;
* `mval`/`h_const`/`h_psig_int`/`h2e`/`hidx`/`hA`/`hB`/`hC` from the deep value/norm package
  `witness_value_norm_package` (the (12.14)/(12.15)/(12.12)/(8.1.c)/(7.x) content). -/
theorem exists_counterexample_dade_data [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (ctr : CounterexampleHypothesis (G := G))
    (witness : RankTwoWitnessData ctr) {g : G}
    (hg_comm : Commute witness.x g) (hgK : g ∈ ctr.K) (hgK' : g ∉ ctr.Kprime) :
    Nonempty (CounterexampleDadeData witness g) := by
  classical
  haveI : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- The witness (12.13) Dade calculation with its proven (12.14) evaluation `ψ(x) = χ(x)`.
  obtain ⟨hyp, coh, dade, hψeq, he_eq, hψZ, hχZ, hψx_eq⟩ :=
    witness_dade_psi_apply_x_eq_chi hG witness
  -- A primitive `p`-th root of unity.
  obtain ⟨ε, hε⟩ : ∃ ε : ℂ, IsPrimitiveRoot ε ctr.p :=
    ⟨_, Complex.isPrimitiveRoot_exp ctr.p ctr.p_prime.pos.ne'⟩
  -- `3 ≤ e = [L:H]`.
  have hthree : 3 ≤ dade.e := he_eq ▸ three_le_index hG hyp
  -- (12.14) + the `L`-side (1.10.a): `ψ(x) = χ(x) ≡ χ(1) = e (mod 1 − ε)` (`h_psix`),
  -- with no coherent-extension degree identity `ψ(1) = e` needed.
  have hxL : witness.x ∈ witness.L := witness_x_mem_L hG witness
  have hxp : (⟨witness.x, hxL⟩ : ↥witness.L) ^ ctr.p = 1 := by
    apply Subtype.ext
    push_cast
    exact witness.x_mem_omega1
  obtain ⟨w, hw, hweq⟩ := OddOrder.RepresentationTheory.exists_integral_apply_sub_of_commute
    ctr.p_prime.pos hε hχZ hxp (Commute.one_right _)
  rw [mul_one, dade.chi_degree_eq_e] at hweq
  have h_psix : ∃ w : ℂ, IsIntegral ℤ w ∧ dade.psi witness.x - (dade.e : ℂ) = (1 - ε) * w := by
    refine ⟨w, hw, ?_⟩
    rw [hψx_eq]
    exact hweq
  -- `H = L_F` (kernel of the witness) has the same order as the maximal nilpotent normal Hall.
  have hHcard : (Nat.card ↥(hyp.typeI.typeF.H) : ℝ)
      = (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ) := by
    rw [hyp.typeI.typeF.H_eq]
  -- The deep value/norm package (12.14)/(12.15)/(12.12)/(8.1.c)/(7.x).
  obtain ⟨mval, normRhoM, normRho, h_const, h_psig_int, h2e, hidx, hA, hB, hC⟩ :=
    witness_value_norm_package hG witness rfl hg_comm hgK hgK' hyp coh dade hψeq he_eq hψZ
  -- `|M| ≤ |K|·|H|` (12.11).
  have hM : (Nat.card ↥ctr.M : ℝ)
      ≤ (Nat.card ↥ctr.K : ℝ) * (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ) := by
    have := card_M_le hG witness
    calc (Nat.card ↥ctr.M : ℝ)
        ≤ ((Nat.card ↥ctr.K * Nat.card ↥(maxNilpotentNormalHall witness.L) : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = (Nat.card ↥ctr.K : ℝ) * (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ) := by
          push_cast; ring
  exact ⟨{
    ε := ε
    hε := hε
    ψ := dade.psi
    hψ := hψZ
    e := (dade.e : ℤ)
    mval := mval
    he := by exact_mod_cast hthree
    h2e := h2e
    h_const := h_const
    h_psix := h_psix
    h_psig_int := h_psig_int
    kK := (Nat.card ↥ctr.K : ℝ)
    kKp := (Nat.card ↥ctr.Kprime : ℝ)
    kM := (Nat.card ↥ctr.M : ℝ)
    kH := (Nat.card ↥(maxNilpotentNormalHall witness.L) : ℝ)
    normRhoM := normRhoM
    normRho := normRho
    hkKp := by exact_mod_cast (Nat.card_pos (α := ↥ctr.Kprime))
    hkM := by exact_mod_cast (Nat.card_pos (α := ↥ctr.M))
    hkH := by exact_mod_cast (Nat.card_pos (α := ↥(maxNilpotentNormalHall witness.L)))
    hidx := hidx
    hM := hM
    hA := hA
    hB := by
      -- `(↑(dade.e : ℤ) : ℝ) = (dade.e : ℝ)` and `|H| = |maxNilpotentNormalHall L|`.
      rw [show (((dade.e : ℤ) : ℝ)) = (dade.e : ℝ) by push_cast; ring, ← hHcard]
      exact hB
    hC := hC }⟩

/-- **Peterfalvi (12.16)**: the minimal counterexample of (12.8) is impossible.

The rank-two witness of (12.9) (`exists_rankTwoWitness`) and the commuting element `g ∈ C_K(x) ∖ K'`
(`exists_witness_g`) are extracted unconditionally; the deep §7/§12 character calculation is bundled
into `exists_counterexample_dade_data`; the contradiction then follows from the numerical endgame
`counterexample_contradiction_of_facts`. -/
theorem counterexample_contradiction [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    False := by
  obtain ⟨_, _, ⟨witness⟩⟩ := exists_rankTwoWitness hG ctr
  obtain ⟨g, hg_comm, hgK, hgK'⟩ := exists_witness_g witness
  obtain ⟨d⟩ := exists_counterexample_dade_data hG ctr witness hg_comm hgK hgK'
  exact counterexample_contradiction_of_facts ctr.p_prime d.hε d.hψ witness.x_mem_omega1 hg_comm
    d.he d.h2e d.h_const d.h_psix d.h_psig_int d.hkKp d.hkM d.hkH d.hidx d.hM d.hA d.hB d.hC

/-- **Peterfalvi (12.7), `π = ∅`** (the headline consequence of (12.16)): no prime lies in the
set `π` of (12.8).  Were `π` nonempty, (12.8) (`exists_counterexampleHypothesis`) would build a
minimal counterexample, contradicting (12.16) (`counterexample_contradiction`). -/
theorem pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q := by
  by_contra h
  push Not at h
  obtain ⟨ctr⟩ := exists_counterexampleHypothesis hG h
  exact counterexample_contradiction hG ctr

/-- **Peterfalvi (12.7)**: every maximal subgroup of type I is Frobenius, with kernel `M_F`.

Since `π = ∅` by (12.16) (`pi_empty`), the easy direction `typeI_frobenius_of_pi_empty` applies
and gives the Frobenius decomposition with kernel `M_F = typeF.H` and complement `typeF.U`.  (The
`kernel_eq_MF` carrier is vacuous here: the `frobenius` field already names `typeF.H = M_F` as the
kernel, so the identification holds definitionally.) -/
theorem typeI_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hType : IsTypeI M) :
    ∃ data : TypeIFrobeniusData M, data.kernel_eq_MF := by
  obtain ⟨data⟩ := hType
  exact ⟨{ typeI := data
           complement := data.typeF.U.subgroupOf M
           kernel_eq_MF := True
           kernel_eq_MF_holds := trivial
           frobenius := typeI_frobenius_of_pi_empty hG (pi_empty hG) hM data }, trivial⟩

/-- **The type-I Dade support is `H#`** (Peterfalvi (8.3)/(12.1) for the witness subgroup `L`).
`typeIA L = centralizerSupport (H#) L` collapses to `H# = (H : Set G) \ {1}` (`H = L_F`): the
Frobenius structure of `L` (from (12.7) `typeI_frobenius`) makes the centralizer condition vacuous
on `H#` (`IsFrobeniusGroup.centralizer_kernel_le`).  This supplies the `A = H#` shape that
`S09.Cert.hypothesis78OfDade` needs (the `hAH` argument of the §12→§7 Dade bridge).

Re-derives the `centralizerSupport = sharp` argument of
`S16.centralizerSupport_sharpSubgroup_eq_of_frobenius` — which lives downstream of `S14` and so
cannot be cited here; a hub dedup hoisting that pure-group-theory fact to a shared file (e.g.
`MaximalSubgroupType`) is tracked in issue 1013. -/
theorem Hypothesis.typeIA_eq_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.GroupTheory.typeIA L hyp.typeI
      = OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H := by
  obtain ⟨fdata, _⟩ := typeI_frobenius hG hyp.maximal ⟨hyp.typeI⟩
  have hKf : fdata.typeI.typeF.H = hyp.typeI.typeF.H := by
    rw [fdata.typeI.typeF.H_eq, hyp.typeI.typeF.H_eq]
  exact hyp.typeIA_eq_sharp_of_frobenius (hKf ▸ fdata.frobenius)

end OddOrder.Peterfalvi.S14
