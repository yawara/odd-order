# Adversarial review — ZIrr keystone → Dade-map (2.8)/(2.9) frontier (2026-05-30b)

**Reviewer**: adversarial pass (read/build only; markdown is the only artifact).
**Run boundary**: `d3c5201..HEAD`, 7 commits (`7613fcd … 7aad765`), authored
2026-05-30 09:22 → 10:04. Theme: the **virtual-character keystone**
(`character_mem_ZIrr`: the character of *any* f.d. complex representation lies in
`ℤ[Irr G]`) and the chain it unblocks — `restrict`/`induce`/`compHom` preserve `ℤ[Irr]`,
the Peterfalvi (2.8) semidirect structure `M(B) = H(B) ⋊ N_L(B)`, and the (2.9) quotient
hom `f_B : M(B) →* L` with `α_B = α ∘ f_B`.

## Commits this run

```
7613fcd RepTheory: KEYSTONE — every f.d. rep character ∈ ℤ[Irr G]
6fd5b3a issues/0040: (2.6.b) 前提 — restrict_mem_ZIrr + induce_mem_ZIrr (sorry-free)
527053b issues/0040: ZIrr pullback compHom_mem_ZIrr — (2.9) α_B = α ∘ f_B ∈ ℤ[Irr]
527d486 issues/0040: Peterfalvi (2.8) — M(B) = H(B) ⋊ N_L(B) の構造補題 (sorry-free)
a6dd522 issues/0040: Peterfalvi (2.9) — f_B : M(B) →* L + α_B = α∘f_B ∈ ℤ[Irr] (sorry-free)
6b4a7da notes/issues 0040: (2.8)/(2.9) 完了記録 + 先行調査の誤ブロッカー評価を訂正  (markdown only)
7aad765 issues/0026: Clifford restriction-multiplicity の整数性を sorry-free 着地
```

Touched `.lean`: `CharacterCompleteness.lean`, `ClassFunction.lean`, `InducedCharacter.lean`,
`Clifford.lean`, `Peterfalvi/S04_DadeIsometry.lean`, `AxiomsCheck.lean`.

## Verification performed

- `lake build` on the four RepTheory leaf modules + `S04_DadeIsometry` — **green**
  (3128 / 3131 jobs; only `linter.style.show` and a `push_neg` deprecation warning,
  cosmetic, no errors).
- `lake build OddOrder.AxiomsCheck` — **green** (3319 jobs); each new headline result
  passes `#assert_only_allowed_axioms` with exactly the 3-axiom allowlist
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`, no project-axiom:
  `character_mem_ZIrr`, `restrict_mem_ZIrr`, `induce_mem_ZIrr`, `compHom_mem_ZIrr`,
  `card_mBSubgroup`, `ker_dadeQuotientHom`, `alphaB_mem_ZIrr`.
- `grep -nE '\b(sorry|admit)\b'` on every touched `.lean` — **no occurrences** (the only
  `sorry` hits are documentation comments in `AxiomsCheck.lean`, pre-existing).
- No new `axiom` declarations in any touched file.
- Statement-faithfulness audit of every new/changed theorem (below).

## What landed (sorry-free + axiom-clean + faithful)

### KEYSTONE — `RepresentationTheory.character_mem_ZIrr` (CharacterCompleteness.lean)

```lean
theorem character_mem_ZIrr {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {G : Type*} [Group G] [Finite G] (ρ : Representation ℂ G V) :
    (⟨ρ.character, fun g h => ρ.char_conj g h⟩ : ClassFunction G ℂ) ∈ ZIrr G
```

**Faithful, fully general, no hidden hypotheses.** Carrier `V` is universe-general; `ρ`
need *not* be irreducible. Proof = strong `finrank` induction: `finrank 0 ⇒ χ = 0`;
irreducible ⇒ `exists_isIrreducibleCharacter_eq` + `IsIrreducibleCharacter.mem_ZIrr`;
reducible nonzero ⇒ Maschke (`ComplementedLattice.exists_isCompl` on `Subrepresentation ρ`)
splits `V = U ⊕ U'` into smaller invariant submodules and `character_add_of_isCompl`
(new; `trace_conj' + trace_prodMap'` over `Submodule.prodEquivOfIsCompl`) gives
`χ_ρ = χ_U + χ_{U'}`, then IH + `Submodule.add_mem`. The declaration carries
`set_option backward.isDefEq.respectTransparency false` — the documented `asModule`
type-synonym gotcha (issues/closed/0048), used legitimately, not masking content.

This is the genuine unblock the prior frontier notes were waiting on: the earlier
"critical blocker" framing (that `Res ρ` is reducible so `repCharacterClassFunction_mem_ZIrr`
— irreducible-only — could not apply, requiring a char-of-restriction module decomposition)
was **wrong**. Since the keystone needs no irreducibility, `restrict`/`compHom` follow by a
one-line span-induction base case. The run's commit messages and issue 0040 correctly record
this self-correction.

### (2.6.b) prerequisites — `restrict_mem_ZIrr` / `induce_mem_ZIrr` (InducedCharacter.lean)

- `restrict_mem_ZIrr (H : Subgroup G) [Finite G] (hφ : φ ∈ ZIrr G) : restrict H φ ∈ ZIrr H`.
  Span induction; base case rewrites `restrict H χ_ρ = χ_{ρ.comp H.subtype}` (via
  `restrict_repCharacterClassFunction`) and applies the keystone to the *restricted* rep.
- `inner_mem_ZIrr_int (hφ : φ ∈ ZIrr) (hψ : ψ ∈ ZIrr) : ∃ m : ℤ, ⟨φ,ψ⟩ = m`.
- `induce_mem_ZIrr (H : Subgroup G) [Fintype G] [Invertible (Nat.card G:ℂ)] [Fintype H]
  [Invertible (Nat.card H:ℂ)] (hθ : θ ∈ ZIrr H) : induce H θ ∈ ZIrr G`. Span induction;
  base case: each Fourier coefficient `⟨Ind θ, χ⟩_G = ⟨θ, Res χ⟩_H` is an integer (numerical
  Frobenius `inner_induce_eq_inner_restrict` + `restrict_mem_ZIrr` + `inner_mem_ZIrr_int`),
  build `Φ = ∑_χ (fχ)•χ`, show `Ind θ − Φ ⟂ all irreducibles ⇒ = 0` by completeness
  (`classFunction_eq_zero_of_orthogonal`).

  **Hypothesis check**: the two `Invertible (Nat.card · : ℂ)` instances are *constructible*
  for any finite group (Nat.card > 0, ℂ char 0) — standard, not smuggled content. Confirmed
  usable: downstream `alphaB_mem_ZIrr` discharges its analogue with only `[Finite …]`, and
  AxiomsCheck (which transitively elaborates the consumers) is green.

### (2.9) ZIrr pullback — `compHom_mem_ZIrr` (ClassFunction.lean + InducedCharacter.lean)

`ClassFunction.compHom (f : H →* G) φ := φ ∘ f` (the `f = H.subtype` generalization of
`restrict`), with `compHom_{zero,add,neg,sub,smul}`. `compHom_mem_ZIrr [Finite H]
(f : H →* G) (hφ : φ ∈ ZIrr G) : compHom f φ ∈ ZIrr H` — same span induction via
`character_mem_ZIrr (ρ.comp f)`; `f` need not be surjective and `ρ.comp f` need not be
irreducible. Correctly noted: the prior "(2.9) needs IsIrreducible-inflation preservation"
blocker evaluation was a false alarm.

### Peterfalvi (2.8) — `M(B) = H(B) ⋊ N_L(B)` (S04_DadeIsometry.lean, SemidirectStructure)

Genuine structural layer, all real proofs:
- `conjA` (L-action on A by conjugation, subtype-valued) + group laws.
- `hIntersection B = H(B) = ⨅_{a∈B} H(a)` (`Finset.inf'`), `mem_hIntersection`.
- `setLStabilizer B : Subgroup L = N_L(B)` — hand-built (mathlib `Subgroup.setNormalizer`
  is the subgroup normalizer, not a Finset set-stabilizer). `inv_mem'` via
  "conjugation is an injective self-map of finite B ⇒ surjective".
- `nLStabilizerIn` (= N_L(B) as a subgroup of G), `mem_H_conjA_iff` (via (2.4.a)
  `HConjInvariant`), `nLStabilizerIn_le_normalizer` (N_L(B) normalizes H(B)),
  `hIntersection_disjoint_nLStabilizerIn` (`H(B) ∩ N_L(B) = 1` via `commute_of_mem_H` +
  `centralizer_disjoint`), `mBSubgroup`/`coe_mBSubgroup`, and
  **`card_mBSubgroup`** `|M(B)| = |H(B)|·|N_L(B)|` (internal-product bijection).

### Peterfalvi (2.9) — `f_B : M(B) →* L`, `α_B` (S04_DadeIsometry.lean)

- `hIntersection_subgroupOf_normal` (H(B) ◁ M(B)), `isComplement'_subgroupOf`
  (N_L(B), H(B) complementary in M(B)).
- **`dadeQuotientHom = f_B`** = composite `M(B) → M(B)/H(B) ≅ N_L(B) ↪ L`
  (`IsComplement'.QuotientMulEquiv` + `Subgroup.inclusion`). This is a *constructed* map,
  not an interface assumption.
- **`ker_dadeQuotientHom`** `ker f_B = H(B).subgroupOf M(B)` — faithfully certifies the
  textbook "(2.9) natural hom with kernel H(B)" (post-`mk'` part injective ⇒ ker = ker mk').
- `alphaB B α = α ∘ f_B`, **`alphaB_mem_ZIrr`** `α ∈ ℤ[Irr L] ⇒ α_B ∈ ℤ[Irr M(B)]`
  (immediate from `compHom_mem_ZIrr`).

### issue 0026 — Clifford restriction-multiplicity integrality (Clifford.lean)

- `ClassFunction.restrictionMultiplicity_int [Finite G] (hχ : χ ∈ ZIrr G) (hθ : θ ∈ ZIrr H)
  : ∃ m : ℤ, restrictionMultiplicity H χ θ = m` — composition of `restrict_mem_ZIrr` +
  `inner_mem_ZIrr_int`. Hypothesis (ZIrr membership) and conclusion (integrality) are
  distinct propositions; the implication has real content (NOT a tautology).
- `IrreducibleCharacter.restrictionMultiplicity_int` — irreducible-character specialization.

This resolves the **integer half** of Clifford gap #5 (multiplicity ∈ ℤ⁺).

## Quality concerns / honest scaffolds (NOT fake progress, but flagged)

- **`Clifford.clifford_decomposition` (lines ~627-640) remains a tautological conditional
  scaffold** — its conclusion is literally `⟨t, h_pos, e, he_pos, θ, h_inj, h_irr, h_orbit,
  h_decomp⟩`, the conjunction of its own hypotheses (the `scaffold-sorry-free-not-done`
  anti-pattern). This run **did not touch it** and the commit message + issue 0026 say so
  explicitly. Correct disposition: it is sorry-free but not "proved", and is not claimed as
  the real Clifford theorem. Replacing it needs the module layer (below).
- Cosmetic only: `linter.style.show` (`CharacterCompleteness.lean:147,356`, `ClassFunction.lean:163`)
  and a `push_neg` deprecation (`CharacterCompleteness.lean:309`, inside the keystone). No
  behavioral impact; a future janitorial pass could switch `show ⟶ change` and `push_neg ⟶
  push Not`.
- `induce_mem_ZIrr` uses `[Invertible (Nat.card · : ℂ)]` rather than deriving it from
  `[Finite]` inline. Harmless (constructible), but a one-line `haveI` derivation would make
  the lemma require only `[Finite]` at call sites, matching `restrict_mem_ZIrr`/`compHom_mem_ZIrr`.

## What is blocked (pointers to findings)

The Dade-map construction (issue 0040) and the Clifford module core (issue 0026) are the two
open fronts; neither was over-claimed.

- **issue 0040 — remaining (2.10)/(2.11) + τ construction** (`issues/0040-…md`,
  「残作業」/「進捗 (3)」): (2.10.1)-(2.10.3) Ind-value sub-lemmas + the Möbius
  inclusion-exclusion `γ = −∑_B (−1)^|B| Ind_{M(B)} α_B` (the B↔B∪{a} pairwise cancellation,
  hardest, ~150-200 LOC), then wiring `dadeSumMap → IsDadeMap → (2.6.a via existing
  isDadeIsometry_of_isDadeMap) + (2.6.b via induce_mem_ZIrr/alphaB_mem_ZIrr) →
  FullDadeIsometryData`. Also needs an **induced-character pointwise-value lemma** (not just
  the inner-product Frobenius reciprocity) in `InducedCharacter.lean`.
- **issue 0026 — module-theoretic Clifford core** (`issues/0026-…md`, BLOCKER A/B):
  (A) for `H ⊴ G`, `N ↦ N.map (ρ g)` sends a simple `ℂ[H]`-submodule of `Res ρ.asModule`
  to a simple one (needs the `ℂ[H]`-module structure on `N.map (ρ g)` from normality;
  `asModule` instance management per the issues/closed/0048 gotcha; ~50-80 LOC); (B)
  orbit transitivity (G-orbit-sum of a simple submodule is a `ℂ[G]`-submodule ⇒ = ⊤ by
  irreducibility ⇒ single orbit; ~80 LOC). The non-negativity half of gap #5 reduces to the
  same decomposition. Est. 3-5 sessions; mathlib lacks BLOCKER A specifically.

## Prioritized next steps

1. **(2.10.2) `C_{H(B)}(a) = H(B∪{a})`** — small, self-contained, and the algebraic hinge of
   the Möbius cancellation. Good first leaf to land before the heavy combinatorics.
2. **Induced-character pointwise value lemma** in `InducedCharacter.lean` ((2.10.1)/(2.10.3)
   need `(Ind_{M(B)} α_B)(g)` explicitly, not just `⟨·,·⟩`). Independent prerequisite.
3. **(2.10) inclusion-exclusion body** (`Finset.sum_powerset_*`) → wire to
   `FullDadeIsometryData` (closes the constructive half of issue 0040; the isometry +
   virtual-char-preservation halves are already in place via this run + issue 0039).
4. **issue 0026 BLOCKER A** (G-action on `ℂ[H]`-simples) — the one piece mathlib lacks;
   unblocks both single-orbit transitivity and the non-negativity half of gap #5, after which
   `clifford_decomposition`'s scaffold can be replaced by a real proof.
5. Janitorial (low priority): `show → change`, `push_neg → push Not`; derive the `Invertible`
   instance inside `induce_mem_ZIrr`.

## Issue status

- **issue 0040** (open): (2.8) and (2.9) checkboxes now `[x]`; (2.6.b) prerequisite
  `restrict_mem_ZIrr`/`induce_mem_ZIrr` `[x]`. Remaining open: (2.10.1)-(2.10.3), the (2.10)
  body, (2.11), and the induced-value lemma. Issue body already records progress (1)/(2)/(3)
  for this run — accurate, no edit needed.
- **issue 0026** (open): integer half of gap #5 `[x]` (`restrictionMultiplicity_int`).
  Non-negativity, orbit-sum, and single-orbit-hypothesis removal remain open (module layer).
  Issue body already records the 2026-05-30 (2) update — accurate, no edit needed.

**Confirmed keystone unblock**: both `character_mem_ZIrr` (the f.d.-rep-character keystone)
and `induce_mem_ZIrr` landed sorry-free, axiom-clean, with faithful statements and passing
`#assert_only_allowed_axioms`.
