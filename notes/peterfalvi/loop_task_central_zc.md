# Autonomous loop task — Peterfalvi (6.8) central-Zc redesign (2026-06-07)

You are an autonomous Ralph loop continuing the Peterfalvi (6.8) coherence redesign.
Work **only** in this worktree `/home/ywr/odd-order-peterfalvi` (branch `peterfalvi`).
**Read `notes/peterfalvi/s08_6_8_blocker_central_Z.md` first** — it is the source of truth
(findings #1–#6 + the precise plan + the L2 field map). This file is the action queue.

## State at loop start (commit `d788674`, build-green)
L1 ✅ central-`Zc` facts. L4 ✅ `false_of_coherentXunionYset_of_not_coherentS`.
L2-linchpin ✅ `exists_source_primePow_centralBound_of_mem_Xset`.
hXne ✅ `Xset_centralCommutator_nonempty` (264966a). Zc-shell ✅
`Xset_centralCommutator_isCoherent_from_pairUnionBaseAnchorCommonIndexPrimePowerData_of_frobenius`
(a9054c4). (6.7) is already formalized = `peterfalvi_67_of_odd` (`SylowTICongruence.lean:140`).

## Ordered plan (each item = one or more build-green commits; do in order)

### Step 1 — finding-#6 contract fix (the true L2 unblock)
The StepData producer callback lacks Xset-cover completeness `hcover`, needed for `htail_le`/`hsum`.
**Prefer the ADDITIVE approach** (new defs only; never change an existing signature, so S09 cannot
break):
- Write `Xset_isCoherent_from_adjoinSteps_withCover_of_irreducible_X` = a copy of
  `Xset_isCoherent_from_adjoinSteps_of_irreducible_X` (S08, search for the name; ~line 6651) whose
  `hstep` callback gains the extra hypothesis
  `hcover : ∀ φ ∈ hyp.Xset Z, φ ∈ hyp.xBaseBlock Z ∨ ∃ j, j < N ∧ φ ∈ S07.pairSet pair j`.
  The engine already derives this internally (search `have hcover` in that def); pass it at the final
  `hstep ...` call.
- Write an additive base-anchor consumer variant `..._withCover_of_irreducible_X` that uses the new
  engine and threads `hcover` into its `hstepData` hypothesis.
- Write a Zc wrapper variant using it.
Each new def must build leaf-green. Commit as one unit.
(If the additive copy proves too large, the alternative is to thread `hcover` through the existing
defs + S09 — ~7 defs, mechanical — but only if you can keep every intermediate build green.)

### Step 2 — the L2 `hstepData` monolith at `Z = centralCommutator`

**✅ DONE (2026-06-07, `d21d788`, sorry-free + axiom-clean).**
`Xset_centralCommutator_isCoherent_of_frobenius` builds the StepData for every chain step and feeds
the `…withCover…` Zc shell → `IsCoherent (Xset Zc)`. The `κ : Type` (Type 0) constraint was met by
`Fin tailF.card`-indexing the tail (`Finset.equivFin` + `Equiv.sum_comp` + `Finset.sum_coe_sort`);
∃→data via the `choose` tactic. Sub-lemmas: `exists_xBaseBlock_anchor_index` (1f2148a),
`characterDegree_re_le_of_not_mem_pairUnion` (c8ddb62), `natSum_partition_of_realSum` (ab01c92).
**⟹ L2 is complete. Next: Step 3 (L3 ν-glue, then CertainType case B, then capstone wiring).**

Original field-map sketch (for reference):
- p-group: `H` is a `p`-group via `isPGroup_of_not_coherent` (or take `{p} (hp) (hHp)` as inputs).
- enum: `exists_pairUnion_memberFamily_of_irreducible_X` → `k, χmem, hχinj, hrange`; anchor `i₁` =
  a base-block element (use `two_le_xBaseBlock_ncard` for nonemptiness + membership in the pairUnion).
- numerics: `idx = H.index` (coprime to `p`); `dχ/θχ/mχ` and `hθsq_le_qtot` via
  `exists_source_primePow_centralBound_of_mem_Xset`; `dmem/θmem/mmem` via `exists_memberDegreeData`;
  `qtot = |H:Zc| = p^mq` via `exists_primePow_card_quotient_of_isPGroup`;
  `total = |H:Zc|·c` via `index_mul_card_sub_factor`.
- `tailSet = Xfin ∖ members`, `θtail` = source p-degree (choose via the linchpin over `Xfin`);
  `htail_le` uses `hcover` + `hmono`; `hsum` = `Finset.sum_sdiff` with the ℝ value pinned by
  `sum_re_sq_Xset_eq` cast to ℕ.
- package the record; feed the Step-1 consumer → `IsCoherent (Xset Zc)`. Define
  `Xset_centralCommutator_isCoherent_of_frobenius`.

### Step 3+ — later (only after 1–2 land)
L3 ν-glue (wire `peterfalvi_67_of_odd` into `coherentUnion_of_glued`); CertainType case (B); capstone
wiring. Per the note. Focus 1→2 first.

## HARD RULES — never violate
1. **Never commit a broken build.** Before EVERY commit:
   `lake build OddOrder.Peterfalvi.S08_CoherenceTheorems` (leaf, ~2s) must be green. Before
   declaring a major unit done: `lake build OddOrder` (full, ~75s) green.
2. **Never commit `sorry`.** sorry is allowed only while developing one def. A commit's new
   declarations must be sorry-free. If you cannot finish a sorry-free unit, **revert uncommitted Lean
   changes** and instead commit a precise note update on where you got stuck.
3. **Removing temp `#print axioms` lines: use the Edit tool, NEVER `git checkout -- <file>`** — that
   wipes uncommitted work (it ate the hXne edit earlier today). Commit before any temp-check.
4. Commit per logical unit; message ends with the exact line:
   `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
5. **Do not push** (local-first; origin not configured). Do not touch other worktrees or `main`.
6. Update the progress log in `s08_6_8_blocker_central_Z.md` (and the memory file
   `peterfalvi-s6-coherence-reduction.md`) when a frontier actually changes.
7. Lean API lookup: write the natural name, let the fast build correct it; do not grep-thrash mathlib.
8. **If genuinely blocked** (needs a design decision, or a missing theorem you cannot derive in a few
   attempts): document it precisely in the note, commit the note, and **stop the loop** — do not
   thrash. Likewise stop once Steps 1–2 are done and committed (leave 3+ for an attended session).
   **To stop the loop, output the exact text** `<promise>RALPHDONE</promise>` — but ONLY when either
   (a) Steps 1 and 2 are committed and `lake build OddOrder` is green, or (b) you are genuinely
   blocked and the blocker is documented + committed to the note. Never emit it just to escape; the
   loop also hard-stops on its own after 25 iterations.

## Each iteration
Read the note, identify the smallest build-green committable increment toward the next unfinished
plan item, do it, build-verify, commit. Then continue or stop per the rules.
