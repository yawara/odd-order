# Peterfalvi (9.1) Wielandt fixed-point formula — proof design (lane-f, 2026-06-17)

## Status

- ✅ **Faithful redesign + corollaries DONE** (`CoprimeAction.lean`, commit `c55f6db2`,
  build-green + AxiomsCheck OK). 3 sorries → 1.
  - `CoprimeFrobeniusAction` now carries a real action `φ : L →* MulAut H`; the three
    fixed subgroups are *derived* (`fixedByUE/E/U = fixedSubgroup φ ⊤/E/U`), so the
    statements are genuine.
  - Both corollaries proved from the main formula (antitone fixed points +
    `Subgroup.eq_top_of_card_eq`).
- ❌ **Main `wielandt_fixedPoint_frobenius` = the sole remaining sorry.**

## Decision (2026-06-17, user): NO axioms — build everything bottom-up

The full (9.1) splits into a **qualitative** half (corollary (i)) and a **counting**
half (full formula + corollary (ii)):

- **Corollary (i)** `C_H(E)=1 ⇒ U central`: Brauer-free, via the repo's sorry-free
  module-level Wielandt (BG Lemma 3.3) + chief series.  No char-0 input.
- **Full formula + corollary (ii)**: need the elementary-abelian **counting** (†),
  which reduces to "`E` acts freely on the nontrivial irreducible `𝔽_p[U]`-modules".
  ⚠ This is a **modular** Brauer permutation lemma (over `𝔽̄_p`, for the `p′`-group `U`);
  the repo's `BrauerPermutation*.lean` is **ℂ-character only** and does not bridge to
  `𝔽_p`-modules.  A char-0 bridge (Brauer characters / `p′`-lifting, or a `Z(𝔽̄_p[U])`
  trace-lift) is genuinely required and is **absent from repo + mathlib**.

**User directive (2026-06-17): build this missing infrastructure bottom-up, no axioms.**
FT-path confirmed ((9.1) → Pf §11→§12/13→§14→§15→§16 → S16.Hypothesis → `feitThompson`);
no lane interference (F owns `CoprimeAction` + new `GroupTheory/RepresentationTheory/*`;
lanes b/g/h touch none of these).

### Existing foundations to reuse (cite, read-only)

- `OddOrder/BG/Ch1_Preliminary/S03b_Lemma33.lean` (sorry-free): module-level Wielandt
  (BG Lemma 3.3) via `groupSumMap ρ H = ∑_{h∈H} ρ h`; gives
  `kernel_acts_trivially_of_centralizer_eq_bot` (C_V(R)=0 ⇒ kernel trivial) — for cor (i).
- `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean` — operator Maschke (projection).
- `Representation.invariants` + `averageMap`/`isProj_averageMap` (mathlib) — used in
  `WielandtCounting.lean` for the coprime decomposition `V = V^G ⊕ [V,G]`.
- `IsFrobeniusGroup` + `SubgroupPartition`/`frobeniusGroup h`: set-partition
  `L = U ⊔ ⨆_{u∈U} (E^u)#`, parts pairwise-TI, card `|U|+1`.
- ⚠ repo `BrauerPermutation*.lean` is **ℂ only** — NOT directly usable for (†); the
  modular analogue must be built (the `Z(𝔽̄_p[U])` slick proof needs a char-0 trace lift).

## Route B (the planned proof)

`L = UE` Frobenius (kernel `U`, complement `E`), coprime action on finite solvable `H`.
Goal: `|C_H(UE)|^|E| · |H| = |C_H(E)|^|E| · |C_H(U)|`.

1. **Solvable → elementary-abelian reduction.** Take an `L`-invariant series of `H` with
   el-ab `p`-group factors `V_i` (solvable + coprime). For coprime action,
   `C_{H/N}(X) = C_H(X)N/N`, hence `|C_H(X)| = ∏_i |C_{V_i}(X)|` for every `X ≤ L`.
   The product formula multiplies over factors, so (9.1) reduces to the el-ab identity
   on each `V_i`.
2. **El-ab identity (⋆).** For `V` an `𝔽_p[L]`-module (`p ∤ |L|`):
   `|E|·dim V^L + dim V = |E|·dim V^E + dim V^U`  (this is `log_p` of (9.1) on `V`).
   Proof: coprime split `V = V^U ⊕ [V,U]` (both `L`-invariant since `U ◁ L`). With
   `V^{UE} = (V^U)^E` and `[V,U]^U = 0`, (⋆) collapses to the kernel-FPF fact (†) on
   `W := [V,U]`.
3. **Kernel-FPF dim fact (†).** `W` an `𝔽̄_p[L]`-module, `W^U = 0` (`U` acts FPF). Then
   `dim W = |E|·dim W^E`.
   Proof: Maschke-decompose `W` into nontrivial `U`-isotypic components; `E` (Frobenius
   complement, every non-id element FPF on `U`) acts **freely** on the nontrivial
   irreducible `U`-modules — by a **modular** Brauer permutation lemma the only `H'`-fixed
   irreducible (for `1 ≠ H' ≤ E`) is trivial. Hence `E`-orbits on components have size
   `|E|`, and `W^E` picks one representative dimension per orbit ⇒ `dim W = |E|·dim W^E`.
   ⚠ **The modular Brauer permutation lemma is the new infra to build** (§ below).
   Work over `𝔽̄_p` (alg. closed, split); descend to `𝔽_p` via base change
   (`dim_{𝔽_p} V^X = dim_{𝔽̄_p} (V ⊗ 𝔽̄_p)^X`).

### New infrastructure (bottom-up, no axioms) — sub-pieces / sub-issues

- **(I-1) modular Brauer permutation lemma** over `𝔽̄_p` for a `p′`-group `U`:
  for an automorphism action, `#(fixed irreducible 𝔽̄_p[U]-modules) = #(fixed classes)`.
  Slick route: `Z(𝔽̄_p[U])` has two bases (class sums ↔ classes; primitive idempotents ↔
  simples), both permuted by the automorphism; equate the **char-0 trace lift** of the
  permutation operator.  ⇒ needs a char-0 trace of a permutation of a `𝔽̄_p`-basis
  (integer #fixed, not mod p) — the genuine new content.
- **(I-2) isotypic decomposition** of a semisimple `𝔽̄_p[U]`-module (mathlib
  `IsSemisimpleModule` + `Maschke`; isotypic components may need building).
- **(I-3) regular-orbit fixed-space count**: `E` permutes summands `{W_S}` regularly ⇒
  `dim ⊕_S W_S = |E|·dim (⊕_S W_S)^E` (abstract, Brauer-free).
- **(I-4) base change** `𝔽_p → 𝔽̄_p` for fixed-point dimensions (flat).
- **(I-5) chief-series coprime machinery**: `C_{H/N}(X)=C_H(X)N/N`, `L`-invariant el-ab
  series of solvable `H`, multiplicativity `|C_H(X)|=∏|C_{V_i}(X)|`.

Build order (least → most dependent): I-3 (abstract) → step 2 (⋆, Brauer-free) →
cor (i) via BG 3.3 + I-5 → I-2 → I-1 → (†) → I-4 → assembly.

## Effort (no-axiom, revised 2026-06-17)

Larger than the earlier (over-optimistic) ~3–5 estimate, because (I-1) the **modular
Brauer permutation lemma** (char-0 trace-lift of a `𝔽̄_p`-basis permutation) is genuine
new infrastructure, not a reuse of the repo's ℂ lemma:
- I-3 regular-orbit count (abstract): ~0.5–1
- step 2 (⋆) Brauer-free: ~0.5–1
- cor (i) via BG 3.3 + I-5 chief-series: ~1–2
- I-2 isotypic + I-1 modular Brauer + (†): ~2–4 (the hard core)
- I-4 base change + assembly: ~1
**Estimate ~6–9 sessions.** Each leaf is sorry-free and committable independently
(robust if F is pivoted back to §16 when H lands `typeP_duality`).  If I-1 balloons
(e.g. forces full `p`-adic lifting), re-flag to user.

## Not on the immediate critical path

(9.1) is consumed by (9.3) → §11, which is Lane-B character-API-gated and far downstream;
finishing (9.1) closes the local `CoprimeAction.lean` sorry but unblocks nothing now.
