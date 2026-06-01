# BG §7--§16 interface audit (Lane C, 2026-06-02)

Scope: `/home/ywr/odd-order-bg-s07-s16-interface`, branch
`codex/bg-s07-s16-interface`. This note records the interface-only audit of the BG
local-analysis spine from §7 through §16. It is not a proof-completion report.

## Verification snapshot

Build command used after the latest interface edits:

```bash
lake build OddOrder.BG.Ch3_MaximalSubgroups.S10_MalphaMsigma \
  OddOrder.BG.Ch3_MaximalSubgroups.S12_E \
  OddOrder.BG.Ch4_FamilyOfMaximal.S16_MainResults
```

Result: build succeeded. Existing `sorry` and pre-existing long-line/style warnings remain.

Import boundary checks:

- `S16_MainResults` imports `S15_MF` and shared `GroupTheory.MaximalSubgroupType`, not
  Peterfalvi modules.
- `S15_MF` imports §14 only; §10--§13 gates flow through the BG local-analysis spine.
- `S14_TypePCounting` imports §13 and shared type predicates; it does not import
  Peterfalvi.
- `S13_PrimeAction` imports §12; `S12_E` imports §11 explicitly, keeping the exceptional
  maximal-subgroup spine visible.

## Current interface status

- §7--§9 have explicit §4/§5 gate maps. §7 itself does not consume BG Theorem 4.16 or
  narrow-p-group classification; §8 uses §5 Lemma 5.1 only for nonemptiness of
  `SCN3(P)`; §9 records its direct §5 Lemma 5.1 gate at the Uniqueness Theorem.
- §10 now has source-line-stable references for Theorem 10.2 and Proposition 10.14.
  Lemma 10.13 remains a missing-page interface near mmd L2885--L2892, not a hidden
  assumption.
- §11 has explicit proof gates from Proposition 7.5, Lemma 7.1, Theorem 10.1(d),
  Proposition 1.5, Theorem 3.7, Lemma 10.12(b), Proposition 1.16, Lemma 10.13(c),
  Theorem 4.20, Lemma 10.4(c), Propositions 10.10(c)/10.11(d), and Proposition 1.6(d).
- §12 has explicit proof gates for Lemma 12.1, Lemma 12.2, Proposition 12.4,
  Theorem 12.5, Theorem 12.12, Proposition 12.15, Corollary 12.16, Lemma 12.17,
  Lemma 12.18, and Lemma 12.19. Deferred clauses are called out instead of being
  folded into structure fields.
- §13 records the §12/§10 gates for prime-action transition and keeps
  Proposition 10.14(d) as a deferred upstream proof gate.
- §14--§16 record the endpoint gate table from the BG mmd source. §16 treats
  Theorems A--E as BG-local packages and Proposition 16.1 as a bridge to shared
  Type I--V predicates consumed downstream by Peterfalvi.

## Remaining mathematical proof gates

These are not Lane C interface blockers; they are proof obligations that the scaffold now
exposes rather than hides.

- BG §4: Theorem 4.16 / Blackburn rank-two classification remains a real upstream gate
  for later local analysis.
- BG §5: narrow-p-group lemmas, especially Lemma 5.1, remain proof gates for §8/§9.
- BG §10: Lemma 10.13 is a missing-page recovery item; Proposition 10.14(d) is deferred.
- BG §11: Theorems 11.3, 11.5, 11.7 and their corollaries are still `sorry` proofs.
- BG §12: several original subclauses are deferred, especially Lemma 12.2(b),
  Proposition 12.4(b), Corollary 12.16(b), and the cyclic `β(M)'` intersection tail of
  Lemma 12.17.
- BG §13--§16: proof terms remain `sorry`; endpoint statements are interface surfaces, not
  completed local-analysis proofs.

Conclusion: after this pass, no Peterfalvi-driven assumption or hidden §4/§5 obligation was
found in the BG §7--§16 interface. The remaining work is the exposed BG mathematical proof
closure listed above.
