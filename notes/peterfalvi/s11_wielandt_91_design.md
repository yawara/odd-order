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

## Key finding: feasible, NOT blocked on Brauer characters

My first fear (Peterfalvi's group-ring proof needs char-0 / Brauer-character lifting,
absent from mathlib) is avoidable. **Route B** below reduces (9.1) to elementary pieces,
all with existing repo foundations:

- `OddOrder/BG/Ch1_Preliminary/S03b_Lemma33.lean` (sorry-free): the **module-level
  Wielandt** (BG Lemma 3.3) via the averaging operator `groupSumMap ρ H = ∑_{h∈H} ρ h`.
  Gives `kernel_acts_trivially_of_centralizer_eq_bot` (C_V(R)=0 ⇒ kernel trivial on V).
- `OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean` — operator Maschke (projection).
- `OddOrder/GroupTheory/RepresentationTheory/BrauerPermutation*.lean` (sorry-free) —
  Brauer's permutation lemma (#fixed irreducibles = #fixed classes).
- `IsFrobeniusGroup` + `SubgroupPartition`/`frobeniusGroup h` (FrobeniusGroup.lean):
  the set-partition `L = U ⊔ ⨆_{u∈U} (E^u)#`, parts pairwise-TI, card `|U|+1`.

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
3. **Kernel-FPF dim fact (†).** `W` an `𝔽_p[L]`-module, `W^U = 0` (`U` acts FPF). Then
   `dim W = |E|·dim W^E`.
   Proof: Maschke-decompose `W` into nontrivial `U`-isotypic components; `E` (Frobenius
   complement, every non-id element FPF on `U`) acts **freely** on the nontrivial
   irreducible `U`-modules — by Brauer's permutation lemma the only `H'`-fixed
   irreducible (for `1 ≠ H' ≤ E`) is trivial. Hence `E`-orbits on components have size
   `|E|`, and `W^E` picks one representative dimension per orbit ⇒ `dim W = |E|·dim W^E`.

## Effort

~3–5 sessions: step 1 (coprime chief-series machinery — `C_{H/N}(X)=C_H(X)N/N`,
existence of `L`-invariant el-ab series) 1–2; step 3 (Brauer + orbit counting) 1–2;
step 2 + assembly ~1. Each leaf is sorry-free and committable independently
(robust if F is pivoted back to §16 when H lands `typeP_duality`).

## Not on the immediate critical path

(9.1) is consumed by (9.3) → §11, which is Lane-B character-API-gated and far downstream;
finishing (9.1) closes the local `CoprimeAction.lean` sorry but unblocks nothing now.
