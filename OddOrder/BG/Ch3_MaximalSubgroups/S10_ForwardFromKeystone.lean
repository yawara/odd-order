/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.BG.Ch3_MaximalSubgroups.S10_HallStructure
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# BG §10 forward dependencies on the representation-theory keystone (BG Thm 3.6)

Bender–Glauberman, *Local Analysis for the Odd Order Theorem* (LMS LNS 188, 1994).

The §10 → §16 spine of the Feit–Thompson proof is gated by the representation-theory
**keystone** BG Theorem 3.6 (`references/bg/local-analysis.mmd` L955), whose own proof needs
BG Theorem 3.4/3.5 = algebraically-closed extraspecial representation theory (lane `a-keystone`).
This file declares that keystone — together with the local input BG Lemma 10.4(b) — as
**provisional forward axioms**, so that the §10 spine (Theorem 10.6 → Corollary 10.7 → … →
Proposition 10.14) and the §11–§16 cascade can be wired as *genuine, type-checked reductions*
right now.

## Honesty boundary

A theorem proved via these axioms is **`sorry`-free but mathematically unproven**: its truth is
contingent on the constructibility of the axioms, not on `#print axioms` (see
`scaffold-sorry-free-not-done`). The value delivered here is twofold:

1. the reduction Thm 3.6 ⟹ Thm 10.6 ⟹ (Cor 10.7, …) is a *real* Lean proof — only the keystone
   is taken on faith;
2. de-axiomatization is a **name swap**: when lane `a-keystone` lands BG Theorem 3.6 and lane
   `a1`/this lane lands BG Lemma 10.4(b), each axiom below is replaced by the corresponding
   theorem (with the *same statement*), and the entire §10–§16 spine turns genuinely green with
   no change to the downstream proofs.

Both axioms are registered as an *expected island* in `OddOrder/AxiomsCheck.lean`.

## Resolution conditions

* `pLengthOne_commutator_of_zgroupCentralizer` — BG **Theorem 3.6**. **keystone-gated.**
  Resolved when lane `a-keystone` completes BG Theorem 3.6 (which currently waits on BG
  Theorem 3.4 = algebraically-closed extraspecial representation theory). The statement below is
  the intended interface; lane `a-keystone`'s eventual theorem should match it verbatim.
* `exists_prime_orderOf_zgroupCentralizer_of_complement` — BG **Lemma 10.4(b)**, specialized to
  the Theorem 10.6 application. **grounded (not keystone-gated), deferred.** BG Lemma 10.4(b)
  (mmd p.87, recovered 2026-06-08) is provable from BG Lemma 10.3 + the `Ω₁(Z(P))` machinery
  (lane `a1`, `S10_LocalLemmas`); it is forward-axiomatized here only to keep the spine moving.
  Resolved when the general Lemma 10.4(b) lands and the `q ∈ π(K/K') ⟹ q ∉ σ(M)` reduction
  (via Lemma 10.4(a) = `alpha_criterion`) is supplied.
-/

namespace OddOrder.BG.Ch3.S10

open OddOrder.GroupTheory
open OddOrder.Isaacs

/-! ## BG Theorem 3.6 — the representation-theory keystone (forward axiom) -/

/-- **BG Theorem 3.6** (mmd L955), as a provisional forward axiom (**keystone-gated**).

Let `Γ` be a solvable group of odd order, `H` a normal Hall subgroup of `Γ` (encoded by
`H.Normal` + `Nat.Coprime (Nat.card ↥H) H.index`), `R` a complement of `H`, and `R₀ ≤ R` a
subgroup of prime order such that the centralizer `C_H(R₀)` is a `Z`-group. Then for every prime
`p`, the commutator `⁅H, R⁆` has `p`-length one.

This is the engine of the `r_p(M) ≥ 3` branch of BG Theorem 10.6. Its BG proof is a
minimal-counterexample argument (~4 pages, equations (3.6)–(3.38)) resting on BG Theorem 3.4/3.5
(algebraically-closed extraspecial representation theory), which lane `a-keystone` is building.

**Provisional axiom.** Resolution condition: lane `a-keystone` lands BG Theorem 3.6 with this
statement; replace this axiom by that theorem. -/
axiom pLengthOne_commutator_of_zgroupCentralizer
    {Γ : Type*} [Group Γ] [Finite Γ]
    (hsolv : IsSolvable Γ) (hodd : Odd (Nat.card Γ))
    {H R : Subgroup Γ} (hHnormal : H.Normal)
    (hHall : Nat.Coprime (Nat.card ↥H) H.index)
    (hcompl : H.IsComplement' R)
    {R₀ : Subgroup Γ} (hR₀ : R₀ ≤ R) (hR₀prime : (Nat.card ↥R₀).Prime)
    (hZ : IsZGroup ↥(Subgroup.centralizer (R₀ : Set Γ) ⊓ H))
    (p : ℕ) [Fact p.Prime] :
    Ch1.hasPLengthOne p ↥⁅H, R⁆

/-! ## BG Lemma 10.4(b) — the `Z`-group element (forward axiom, specialized) -/

/-- **BG Lemma 10.4(b)** (mmd p.87), specialized to the BG Theorem 10.6 application, as a
provisional forward axiom (**grounded, deferred** — not keystone-gated).

Setup: `G` minimal simple of odd order, `M ∈ ℳ` with `M_α ≠ 1`, `K` a complement to `M_α` in
`M` (inside `↥M`), and `q ∈ π(K/K')` a prime divisor of the abelianization of `K`. Then there is
an element `x ∈ K` of order `q` whose centralizer in `M_α` is a `Z`-group.

In BG: `q ∈ π(K/K')` forces `q ∣ |M/M'|` (the surjection `M/M' ↠ K/K'`), hence `q ∉ σ(M)` by
Lemma 10.4(a) (`alpha_criterion`); a Sylow `q`-subgroup `Q` of `K` is then a Sylow `q`-subgroup
of `M` (as `K` is an `α(M)'`-group), and Lemma 10.4(b) supplies `x ∈ Ω₁(Z(Q))^#` of order `q`
with `C_{M_α}(x)` a `Z`-group.

`q ∈ π(K/K')` is encoded as `q ∈ ((commutator ↥K).index).primeFactors` (the index `[K : K']`
equals `|K/K'|`). The centralizer is stated for the cyclic subgroup `⟨x⟩ = zpowers x`, matching
the `R₀ = ⟨x⟩` of `pLengthOne_commutator_of_zgroupCentralizer` (BG Theorem 3.6); since `R₀`
is generated by `x`, `C_{M_α}(⟨x⟩) = C_{M_α}(x)`.

**Provisional axiom.** Resolution condition: lane `a1` lands the general BG Lemma 10.4(b) in
`S10_LocalLemmas` (`Ω₁(Z(P))` machinery + Lemma 10.3); together with the
`q ∈ π(K/K') ⟹ q ∉ σ(M)` reduction above, this specialized form follows. -/
axiom exists_prime_orderOf_zgroupCentralizer_of_complement
    {G : Type*} [Group G] [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMα : Malpha M ≠ ⊥)
    {K : Subgroup ↥M} (hK : ((Malpha M).subgroupOf M).IsComplement' K)
    {q : ℕ} (hq : q.Prime) (hqK' : q ∈ ((commutator ↥K).index).primeFactors) :
    ∃ x : ↥M, x ∈ K ∧ orderOf x = q ∧
      IsZGroup ↥(Subgroup.centralizer (↑(Subgroup.zpowers x) : Set ↥M) ⊓
        (Malpha M).subgroupOf M)

end OddOrder.BG.Ch3.S10
