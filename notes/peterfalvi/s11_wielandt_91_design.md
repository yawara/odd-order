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

## 2026-06-17 (loop) — I-1 confirmed as the char-0 wall; mathlib status

Step 2 (⋆ `finrank_elab_identity`) DONE. Drilling into I-1 (the (†) core) confirmed it
genuinely needs **char-0 / Brauer-character** infrastructure — no char-p bypass:

- (†) ⟸ "**E acts freely on the nontrivial 𝔽̄_p[U]-simple modules**" ⟸ Brauer permutation
  lemma in **FIXED-POINT form** over 𝔽̄_p: `#(e-fixed simples) = #(e-fixed classes)` for `e∈E`.
- The char-p trace of the conjugation permutation on `Z(𝔽̄_p[U])` gives `#fixed ≡ #fixed (mod p)`
  only. `dim ker(σ_e − 1)` gives **#orbits**, not #fixed-points. So the linear-algebra /
  cycle-type route yields #orbits, not the #fixed-points the free-action argument needs.
- Genuine fixed-point equality needs the **char-0 trace** ⇒ Brauer characters / the `p′`
  decomposition-map bijection (`𝔽̄_p`-simples ↔ ℂ-irreducibles, equivariant). This is the
  classical content and is **absent from mathlib**.
- **mathlib DOES have** (helps I-2/I-3, Brauer-free): `RingTheory/SimpleModule/Isotypic.lean`
  (`isotypicComponent`, `IsIsotypic`, `linearEquiv_fun`), `SimpleModule/WedderburnArtin.lean`,
  `finrank_directSum`. **mathlib does NOT have**: Brauer characters, `p′` root-of-unity lift
  `𝔽̄_p→ℂ`, decomposition map.
- ⇒ Building I-1 bottom-up = building (a chunk of) **Brauer-character theory for `p′`-groups**
  from scratch (Teichmüller-style lift of `p′`-roots of unity, Brauer char as char-0 class
  function, the permutation lemma). Estimate **several sessions** on its own.

This is the loop's designated stop-point ("I-1 requires full Brauer-character theory").
Surfaced to user 2026-06-17 for a scope decision.

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

## 2026-06-17 (resume) — source proof confirmed + reusable-infra map + cor (i) plan

**I-3 COMPLETE** (`WielandtCounting.lean`, commit `b95fcc6b`): reverse half
`finrank_invariants_le_finrank_A1` + capstone `finrank_eq_card_mul_finrank_invariants`
(`dim V = |G|·dim V^G` for a regular `G`-orbit). Abstract Brauer-free; feeds (†) per `E`-orbit.

**Source proof read** (`04.11_…mmd` (9.1)): Peterfalvi cites **Wielandt ([HB] XI.12.4)** as a black
box and applies it to the Frobenius group-ring identity `U·E + |U|·1 = ∑_{u∈U} E^u + U` (= `L + |U|·1
= ∑_u E^u + U` since `underline U · underline E = underline L`), giving
`|C_H(UE)|^{|UE|}|H|^{|U|} = (∏_u |C_H(E^u)|^{|E|})|C_H(U)|^{|U|}`; `|U|`-th root + `E^u` conjugate ⟹
(9.1). **So the crux IS Wielandt's theorem** (not in mathlib).

**Route B reaffirmed over a "cleaner" Brauer-character route.** The uniform route
"`dim V^S = (1/|S|)∑_{s∈S} β_V(s)` (β = char-0 Brauer char) + group-ring linearity" needs the FULL
Brauer character ring. Route B's slice = the **permutation fixed-point lemma** (`#e-fixed simples =
#e-fixed classes`, integer form via Teichmüller) — a SMALLER Brauer slice. ⟹ keep Route B; I-3 + (⋆)
`finrank_elab_identity` stay on-path.

### 🎯 Reusable infrastructure FOUND (the I-5 chief-series machinery already exists)
- **keystone** `OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient` (+ `_of_coprime_normal`),
  `ForwardFromCh03.lean:794/808` = **Isaacs Cor 3.28** in EXACTLY the `φ : A →* MulAut G` form:
  coprime + (A or G solvable) + `IsAInvariant φ N` + A-fixed coset `∀a, φ a g ∈ gN` ⟹ ∃ fixed rep
  `c` (`∀a, φ a c = c`) with `c ∈ gN`. This is "`C_{G/N}(A) = image C_G(A)`" — the I-5 hard direction.
- **BG 3.3** `S03b.kernel_acts_trivially_of_centralizer_eq_bot`: Frobenius `G=KR` + `C_V(R)=0` +
  `(|K|:F)≠0` ⟹ `K` trivial on `V`. (qualitative module Wielandt.)
- **el-ab bridge** `GroupTheory.ElementaryAbelianRepresentation`: `MulDistribMulAction G M` (M el-ab
  p) ⟹ `Representation (ZMod p) G (Additive M)` via `ofDistribMulAction` (+ the `SMulCommClass`
  instance). `φ : L →* MulAut H` gives `MulDistribMulAction L H` by `compHom`.
- **chief series** `GroupTheory.ChiefFactor`: `chiefSeriesInside`, `IsChiefFactor`,
  `chiefFactorCentralizer`, `chiefFactor_isElementaryAbelian` (S03c).
- **stability (Frattini case)** `Ch04.aFixed_quotient_frattini` = Isaacs Cor 3.29: A trivial on
  `G/Φ(G)` ⟹ A trivial on `G`. (Pattern for the general stability step.)
- BG 3.7 internal machinery (`S03c_Thm37.lean`) is all tied to `chiefFactorConjAction` (internal
  conjugation) — NOT directly reusable for the external `φ`, but the same induction shape.

### cor (i) assembly plan (Brauer-free, achievable NOW)
`C_H(E)=1 ⟹ U trivial on H`, strong induction on `Nat.card H`:
1. `H=1` trivial; else take **N = minimal `φ(L)`-invariant normal ≤ H** (el-ab, exists in nontrivial
   solvable `φ(L)`-group). [new piece — minimal invariant normal]
2. **N**: `C_N(E) ≤ C_H(E)=1` ⟹ `C_N(E)=0`; el-ab bridge + **BG 3.3** ⟹ `U` trivial on `N`.
3. **H/N**: keystone (`coprime_fixedPoints_quotient`) ⟹ `C_{H/N}(E)=1`; descend `φ` to `φ̄ : L →*
   MulAut(H/N)` (needs `IsAInvariant φ N`); induction ⟹ `U` trivial on `H/N`.
4. **stability (el-ab N)**: `α := φ u` fixes `N` pointwise and `h⁻¹·α h ∈ N` ∀h ⟹ `α^k h = h·(h⁻¹ α
   h)^k` (clean computation, `α|_N=id` kills the cross terms) ⟹ `α^p = id` (el-ab N exponent p);
   `α^{|u|}=id`, `gcd(p,|u|)=1` ⟹ `α=id`. [new piece — self-contained helper]
New pieces = (1) minimal invariant normal + (4) el-ab stability + the `φ`-descent wiring. Everything
else cites the found infra. ⟹ makes `wielandt_fixedPoint_trivial_E_fixed` unconditional (de-gates it
from the sorried main formula). Does NOT drop sorry count (main formula `wielandt_fixedPoint_frobenius`
still sorried, needs I-1 wall) but is genuine on-path progress (I-5 application validated).

## Not on the immediate critical path

(9.1) is consumed by (9.3) → §11, which is Lane-B character-API-gated and far downstream;
finishing (9.1) closes the local `CoprimeAction.lean` sorry but unblocks nothing now.
