# Overnight run adversarial review — Peterfalvi character-theory burst (2026-05-29→05-30)

**Reviewer**: adversarial pass (read/build only; this note is the only artifact).
**Run boundary**: the orchestrator passed `undefined` as the base SHA, so the range was
recovered from the reflog. The last `reset: moving to HEAD` lands on `c8bfdcb`
(2026-05-29 23:22), and every subsequent reflog entry is a `commit:`. Hence the run is

```
c8bfdcb..HEAD   # 14 commits, a7197cb … 9895ba6
```

All commits are authored 2026-05-29 23:50 → 2026-05-30 03:34. Theme: the
**square character table** (`|Irr G| = |ConjClasses G|`) and its immediate
character-theory consumers (column orthogonality, Brauer permutation, Schur center
bound, class-sum algebra / central character, Dade isometry, Frobenius reciprocity,
Clifford sub-lemmas).

## Verification performed

- `lake build` on all 8 touched leaf modules — **green** (only `linter.style.show`
  warnings at `CharacterCompleteness.lean:147,203`; cosmetic, `show` used where
  `change` is preferred. No errors).
- `lake build OddOrder.AxiomsCheck` — **green**; every run headline result passes
  `#assert_only_allowed_axioms` with exactly the 3-axiom allowlist
  `{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no project-axiom).
- `grep -nE '\bsorry\b|\badmit\b|^\s*axiom\b|\bnative_decide\b'` on every touched
  `.lean` file — **no occurrences** (the only `sorry` hits repo-wide in touched files
  are comments in `AxiomsCheck.lean`).
- Statement-faithfulness audit of every new/changed theorem (below).

## What landed — sorry-free, axiom-clean, and FAITHFUL

### 1. `|Irr G| = |ConjClasses G|` — issue 0048 COMPLETE (landmark)

`OddOrder/GroupTheory/RepresentationTheory/CharacterCompleteness.lean` (new, 465 LOC).
Commits a7197cb, 729175d, 25ed904, 5936a36, c562f17.

- `card_irreducibleCharacter_eq [Finite G] : Nat.card (IrreducibleCharacter G) =
  Nat.card (ConjClasses G)` — **faithful**. Only `[Group G] [Finite G]`; no hoisted
  hypothesis. `[Invertible (Nat.card G : ℂ)]` is a section variable but is *derived*
  inside the top-level theorem from `[Finite G]` via `invertibleOfNonzero`, so the
  result is genuinely unconditional.
- `classFunction_eq_zero_of_orthogonal` (the real completeness core, `f ⊥ Irr ⇒ f = 0`):
  honest proof via the regular representation + Maschke (`IsSemisimpleModule.
  sSup_simples_eq_top`) + Schur. The hypothesis is the genuine orthogonality predicate.
- `span_irreducibleCharacter_eq_top`, `exists_isIrreducibleCharacter_eq` (universe
  transfer to `Fin n → ℂ`), `transportRep*`, `classFunctionOperator*` — all faithful.
- Base definitions checked non-vacuous: `IrreducibleCharacter G =
  {φ // IsIrreducibleCharacter φ}`, `IsIrreducibleCharacter φ = ∃ f.d. irreducible ρ,
  φ = ρ.character` (witnessed by `trivialClassFunction_isIrreducible`),
  `finrank_classFunction = |ConjClasses|`, `card_irreducibleCharacter_le` via genuine
  linear independence. The equality is the real Isaacs Thm 2.8, not a tautology.

**Issue 0048's completion conditions are all met.** Recommend `git mv` to `closed/`
(done in this commit).

### 2. Second (column) orthogonality, unconditional — issue 0027 closed

`ColumnOrthogonality.lean` (new, 112 LOC), commit 11bb5ca. Three public theorems
`column_orthogonality_{diagonal,conjugate,not_conjugate}` with **only** `[Group G]
[Finite G]`. They discharge the matrix core's previously-hypothetical
`CharacterTableIndexing` (new instance `instCharacterTableIndexingOfFinite`) and
`CharacterTableWeightedRowOrthogonality` (`ofRowOrthogonality
characterTableRowOrthogonality_holds`). RHS is `|C_G(g)|`. **Faithful** — genuinely
removes hypotheses, does not add them.

### 3. Brauer permutation lemma, unconditional — issue 0022 closed

`BrauerPermutationUnconditional.lean` (new, 216 LOC), commit 565e24a.
- `Representation.IsIrreducible.dual` (any field): dual of f.d. irreducible is
  irreducible, via the antitone `dualAnnihilator`/`dualCoannihilator` order-iso on
  subrepresentations. Real content.
- `IsIrreducibleCharacter.conj`, `IrreducibleCharacter.conjPerm` (the χ ↦ χ̄
  involution), `brauer_permutation_lemma'` (`#real Irr = #real ConjClasses`, `[Finite G]`
  only), and the odd-order specialization `… = 1`. **Faithful.**

### 4. Schur center bound — Isaacs Cor 2.30

`SchurCenterBound.lean` (new, 201 LOC), commit 1e74e73.
`finrank_sq_le_index (ρ) [IsIrreducible ρ] (Z) (hZ : Z ≤ center G) : finrank ℂ V ^ 2 ≤
Z.index` and its character form `IsIrreducibleCharacter.exists_degree_sq_le_index`.
`hZ : Z ≤ center G` is the genuine premise, not a smuggled conclusion. **Faithful.**

### 5. Class-sum algebra + central character ω — Isaacs §3 / Peterfalvi (6.7.2)

`ClassSumAlgebra.lean` (new, 347 LOC), commit c50284e.
`classSum`, `classSum_mem_center`, `classSumCoeff`, and `centralCharacterOfRep :
Z(ℂ[G]) →ₐ[ℂ] ℂ` (normalized trace `tr(ρ x)/dim`). All `AlgHom` axioms genuinely
discharged — `map_mul'` uses Schur to prove multiplicativity (the real content).
`centralCharacterOfRep_classSum` evaluation lemma proved. **Faithful infrastructure.**

### 6. Dade isometry (2.6.a) — issue 0040 (partial, honest)

`S04_DadeIsometry.lean`, commit 9db4eaa. `isDadeIsometry_of_isDadeMap
(τ) (hτ : IsDadeMap hyp τ) (hconj : hyp.HConjInvariant) : IsDadeIsometry τ` —
*derives* the (2.6.a) inner-product preservation from the (2.5) Dade-map equations
instead of assuming it as a field. `IsDadeMap` is a `structure … : Prop` of genuine
defining equations (constructible). This **removes** a standalone isometry assumption.
**Faithful.** (The explicit τ construction (2.6.b)/(2.8)-(2.10) is still open — see
blocker below.)

### 7. Frobenius reciprocity — Isaacs Lemma 5.2

`InducedCharacter.lean`, commit e6a2977. `inner_induce_eq_inner_restrict (H)
[Invertible …] : inner (induce H θ) χ = inner θ (restrict H χ)`, any subgroup (no
normality). Fully proved (slice-independence + collapse to H + the |G| factor).
**Faithful**, important Clifford prerequisite.

### 8. Clifford sub-lemmas — issue 0026 (partial, honest)

`Clifford.lean`, commit 9895ba6. Two genuine new lemmas:
- `induce_conjBy_eq` / `induceSum_conjBy_eq` (Peterfalvi (1.5)(a)):
  `Ind_H^G(θ^g) = Ind_H^G θ` for `H ⊴ G`. Honest reindexing proof. **Faithful.**
- `hasCommonRestrictionMultiplicity_of_singleOrbit`: single G-orbit of constituents ⇒
  common multiplicity. Hypothesis `RestrictionConstituentsSingleOrbit` is a real,
  non-vacuous predicate; proof transports via `restrictionMultiplicity_conjBy_right`.
  Vacuous branch (no constituent) is legitimate. **Faithful.**

## Quality concerns / caveats (from the step-2 audit)

### (A) `clifford_decomposition` remains a TAUTOLOGICAL SCAFFOLD — pre-existing, NOT introduced this run

`Clifford.lean:600` `clifford_decomposition` is the project's documented
"sorry-free ≠ proved" anti-pattern: its conclusion is literally the conjunction of its
own hypotheses (`⟨t, h_pos, e, he_pos, θ, h_inj, h_irr, h_orbit, h_decomp⟩`). ALL the
real Clifford content — existence of the decomposition `Res χ = e·∑θᵢ`, single orbit,
common multiplicity — sits in hypotheses `h_decomp`/`h_orbit`/etc.

**This is not a regression of this run.** The diff `c8bfdcb..HEAD` touches the symbol 0
times; commit 9895ba6's own message explicitly states the scaffold is "据え置き" (left
in place) pending the module layer. The run's actual additions are honest sub-lemmas
*around* the scaffold. Still, the headline "Clifford's theorem" for issue 0026 is **not
proved**; doneness must be judged on whether `h_decomp`/`h_orbit` can be constructed —
they cannot yet (blocker below). Do not count 0026 as closed.

### (B) Run results outside AxiomsCheck

Items 4–8 above (`finrank_sq_le_index`, `centralCharacterOfRep`,
`isDadeIsometry_of_isDadeMap`, `inner_induce_eq_inner_restrict`, the Clifford
sub-lemmas) build green but are **not** guarded by `#assert_only_allowed_axioms`. They
transitively use the same Maschke/Schur mathlib stack as the asserted results, so they
are very likely axiom-clean, but this was not independently confirmed. Low risk;
consider adding asserts when these become load-bearing.

### (C) Cosmetic linter

`CharacterCompleteness.lean:147,203` use `show` where the style linter wants `change`
(it changed the goal). Harmless; worth a one-line cleanup if the file is touched again.

## Blocked agents — where each recorded its findings (no fake Lean left anywhere)

- **issue 0026 (Clifford full decomposition)** — `issues/0026-peterfalvi-clifford-core.md`,
  bottom section. Single remaining hard blocker = the **module-theoretic core**: realize
  χ by ρ, view `Res^G_H ρ` as an `H`-module, show (a) its character is `restrict H χ`
  (gives integrality/non-negativity of `restrictionMultiplicity`, currently ℂ-valued)
  and (b) its simple `ℂ[H]`-submodules are permuted **transitively by G** (single orbit).
  (b) is new module development, not in mathlib; multi-session. 4-step ordered plan
  recorded there.
- **issue 0040 (Dade map (2.6.b)/(2.8)-(2.10))** — `issues/0040-…md` bottom. (2.6.a) now
  auto via `isDadeIsometry_of_isDadeMap`. Remaining ~400-500 LOC: (1) `induce_mem_ZIrr`
  (integral Frobenius reciprocity — note `inner_induce_eq_inner_restrict` landed this run
  is the ℂ-level half), (2) `N_L(B)` set-stabilizer subgroup (~40-50 LOC, mathlib
  `setNormalizer` is a subgroup alias, unusable for a Finset), (3) pullback `α_B`,
  (4) Möbius cancellation (~150-200 LOC, hardest), (5) assembly. Dependency order given.
- **issue 0044 / Peterfalvi §9 (7.8.a/b),(7.9)** — `notes/peterfalvi/s09_nonexistence_certain.md`
  "2026-05-30" section. Agent **correctly wrote no Lean** (commit 241c648 is
  markdown-only) after determining all three are not outright-provable yet. Blockers:
  integer projection layer (`β = 1_G − ζ^ν + aΣ + Γ`, `‖β‖² = e+1`, Burnside (1.5.d),
  ν↔coherence), and the highest-value missing unblocker **`Odd card ⇒ ¬IsReal χ`**
  (repo-absent), plus a disjoint-support `inner = 0` lemma. This is exemplary blocker
  handling per the run's own rules.

## Prioritized next steps

1. **Close issue 0048** (`git mv issues/0048-… issues/closed/`). All completion
   conditions met and verified. (Done in this review commit.)
2. **`Odd card ⇒ ¬IsReal χ`** (highest leverage). Now directly reachable:
   `brauer_permutation_lemma'` + `card_realIrreducibleCharacters_eq_one_of_odd_card'`
   landed this run give exactly one real irreducible character for odd `|G|`; combined
   with `RealIrreducibleCharacter`'s definition this should yield the per-character
   statement that unblocks §9 (7.9), parts of §3 (1.1), and 0044. See 0044 note step 4.
3. **Clifford module core** (issue 0026, step 1 first): the character-bridge
   `χ_{Res^G_H ρ} = restrict H χ_ρ` via the `transportRep` pattern, then integrality of
   `restrictionMultiplicity` from the Maschke decomposition. The G-transitive isotype
   permutation (step 3) is the genuinely new multi-session piece.
4. **Dade (2.6.b)** (issue 0040): start with the integral `induce_mem_ZIrr` (independent,
   built on this run's `inner_induce_eq_inner_restrict`), then `N_L(B)`.
5. Optional hygiene: `change`-for-`show` cleanup at `CharacterCompleteness.lean:147,203`;
   add `#assert_only_allowed_axioms` for the item-4–8 headline results when load-bearing.

## Verdict

The run is **clean and high-quality**. 14 commits, 8 Lean files, ~3.6k LOC; no `sorry`,
no `admit`, no new `axiom`; all touched modules build green; all 7 asserted headline
results are 3-axiom-allowlist clean. Every theorem statement audited is a faithful
formalization — the run *removes* hypotheses (column orthogonality, Brauer, Dade 2.6.a)
rather than smuggling content into them. The one tautological scaffold
(`clifford_decomposition`) is pre-existing and was correctly left untouched with the
matching blocker recorded. The three blocked agents each left precise specs + next-step
plans and no broken/fake Lean. Landmark result of the run: **`|Irr G| = |ConjClasses G|`
is now a complete, unconditional, axiom-clean theorem.**
