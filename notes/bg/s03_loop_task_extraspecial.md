# Autonomous loop task — A2 lane: BG §3 Thm 3.4 via alg-closed extraspecial rep theory (2026-06-07)

You are an autonomous **Ralph loop** on the **A2 lane**. Goal: drive BG **Theorem 3.4** to
completion by building the missing **algebraically-closed extraspecial representation theory**
(BG §2 Thm 2.5 core), bottom-up, in **build-green + axiom-clean** commits.

## Hard rules (read every iteration)

- **Worktree**: work **ONLY** in `/home/ywr/odd-order-bg-s10-spine` (branch `bg-s10-spine`).
  The shell cwd **resets to `/home/ywr/odd-order` (main) every command** — so **`cd /home/ywr/odd-order-bg-s10-spine && <cmd>`** every time. Commit to `bg-s10-spine`. **Do NOT merge to main** (the integrator does that; main gets concurrent background merges).
- **Do NOT `lake update`**. Do NOT touch other lanes' files.
- **Build discipline**: develop with leaf builds `cd … && lake build OddOrder.GroupTheory.RepresentationTheory.X`; **before every commit run a leaf build of the changed file (and a full `lake build OddOrder` before a commit that is imported widely)**. **Commit only when green. NEVER commit a `sorry`.** If a leaf needs an unproven sub-fact, prove it or defer the whole leaf.
- **Don't break Peterfalvi**: `Clifford.lean`, `SchurCenterBound.lean` are **ℂ-pinned and shared with the Peterfalvi lane**. Do **not** edit them destructively. Add algebraically-closed / general-field results as **new defs/sections or new files**.
- **Verify, don't assume** (this project's recurring traps): (1) confirm mathlib lemma names by building, not memory; (2) **sorry-free ≠ done** — an empty skeleton builds green; check real content; (3) before declaring any dependency "missing", grep repo + mathlib (default assumption = already covered); Gorenstein FT-critical results are **already formalized** (e.g. Gor 5.3.7 = `S04e_GorThm37`).
- **Axiom-clean**: append a temporary `#print axioms <name>` for each new top-level result, confirm `[propext, Classical.choice, Quot.sound]` only, then remove it.
- **One coherent unit per commit** (`Pf (RepresentationTheory): …` or `Pf (BG 3.4 …): …`). Update `notes/bg/s03_thm36_plan.md` when the frontier changes.

## State at loop start (worktree synced to main `dfcbfac`, build-green)

**✅ Already done (do NOT redo):**
- base-change infra `OddOrder/GroupTheory/RepresentationTheory/BaseChange.lean`:
  `baseChangeRepresentation` (+`_apply_tmul`,`_faithful`), `invariants_baseChangeRepresentation_eq_bot`
  (= BG (2.9) `C_V(R)=0 ⇒ C_{K⊗V}(R)=0`), `baseChangeRepresentation_comp` (subgroup form).
- **Gor 5.3.7** (coprime minimal ⇒ special + irred on K/K') = `OddOrder.BG.Ch1.S04.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality` (`S04e_GorThm37.lean`, sorry-free).
- **Lem 3.1** (Frobenius criterion), **Lem 3.3** (Wielandt, `S03b_Lemma33`) — sorry-free.
- **Prop 2.4** (eigenspace under cyclic action) = `EigenspaceUnderCyclicAction.lean` (general field, sorry-free).
- **Thm 2.6**, **Gor 3.2.2** machinery (`SchurCenterBound`, ℂ) — see plan note.

**Source of truth** = `notes/bg/s03_thm36_plan.md` (read the "base-change レイヤ確立 + Thm 3.4 の真の bottleneck" + "§2 ↔ Peterfalvi 棚卸し" sections). This file is the action queue.

## Ordered plan (each item = one or more build-green commits; do in order)

### Step 0 — design (iteration 1)
Read `RingTheory/SimpleModule/IsAlgClosed.lean` + `WedderburnArtin.lean` + `RepresentationTheory/FDRep.lean` (Schur) + `RepresentationTheory/Irreducible.lean`. Figure out the bridge `Representation.IsIrreducible ρ` (faithful, alg-closed, fin-dim) → `IsSimpleModule (MonoidAlgebra F G) ρ.asModule` → Wedderburn-Artin → image of `F[G]` in `End_F V` is **all of `End_F V`** (Burnside / Prop 2.1). Write the proof sketch (exact lemma chain) into `notes/bg/s03_prop21_design.md`. Commit the note.

### Step 1 — Prop 2.1 (Burnside / `E(P) = End_F(V)`)
Fill `AbsolutelyIrreducible.lean` (currently an empty skeleton): for `V` a faithful absolutely-irreducible `FG`-module over an alg-closed field, the `F`-span of the image of `G` is `End_F(V)`; equivalently `End_{FG}(V) = F` (Schur) and the image generates. State the version Thm 2.5 needs (E(P) = Hom_F(V,V)). Build-green, axiom-clean, commit.

### Step 2 — Gor 5.5.5 (extraspecial faithful irreducible has dim `qⁿ`)
Fill `ExtraspecialFaithful.lean` (empty skeleton, issue #34): for an extraspecial `q`-group `P` of order `q^{1+2n}` over alg-closed `F` (`char ∤ q`), a faithful irreducible module has dimension `qⁿ` (the non-linear irreducibles; from the irreducible-degree sum of squares `q^{2n}·1 + (q-1)(qⁿ)² = |P|`, or via Wedderburn + the central character). Use `IsExtraspecial` (`GroupTheory/IsExtraspecial.lean`). Commit.

### Step 3 — Prop 2.2(a) over alg-closed (Clifford `V_P = M`)
Restriction of a faithful irreducible to the normal extraspecial subgroup is isotypic (`V_P = M^k`, here `= M`). `Clifford.lean` is ℂ-only — build the **alg-closed** facts needed in a new section/file (do not edit the ℂ module). Commit.

### Step 4 — Thm 2.5 (the form Thm 3.4 needs)
`P` extraspecial order `q^{1+2n}`, `G = P ⋊ ⟨x⟩` cyclic `H` order `h` coprime to `q`, `C_P(x)=Z(P) ∀x∈H#`, `V` faithful over `F` (`char ∤ |G|`). Conclude: **`h | qⁿ−1` or `h | qⁿ+1`**, and **`C_V(H)=0 ⇒ h = qⁿ+1`**. Proof: base-change to `F̄` (Steps 1–3 give E(P)=End, dim=qⁿ, `V_P=M`); `H` acts on `E(P)` by conjugation; **Prop 2.4(j)(k)** (eigenspace counting, ✅) gives `h | qⁿ±1` and the `C_V(H)=0 ⇒ h=qⁿ+1`; descend `C_V(H)=0 ⇒ C_{V̄}(H)=0` via **(2.9)** (`invariants_baseChangeRepresentation_eq_bot` + `baseChangeRepresentation_comp`). **(2.8) is NOT needed** for this direction. Commit.

### Step 5 — Thm 3.4 body
`OddOrder/BG/Ch1_Preliminary/S03d_Thm34.lean` (new). Minimal-counterexample: Maschke (`Mathlib.RepresentationTheory.Maschke`) → faithful irreducible `M`; reduce `N=C_G(M)=1`; `|K|=qⁿ` (Prop 1.5(a), `S01_Solvable`); **Gor 5.3.7 = S04e** gives `K` elem-abelian or special + irred on `K/K'`; elem-abelian case → Frobenius (Lem 3.1) → Lem 3.3 → `C_V(R)≠0` contradiction; special case → `K` extraspecial → **Thm 2.5** → `h=qⁿ+1` even vs `h` odd contradiction. Conclude `[R,K] ⊆ C_K(V)`. Encoding: `C_V(R)` / `[R,K]⊆C_K(V)` as in `S03b_Lemma33` (`∀ v, (∀ r:R, ρ r v = v) → v = 0` / kernel-of-action). Commit. Update plan note → Thm 3.4 ✅.

## Stop / blocker discipline (avoid flailing)

- Work **one leaf at a time**. If a leaf resists after **~4–5 substantive attempts** (a genuine math/API obstacle, not a typo), **STOP**: write `notes/bg/s03_extraspecial_blocker.md` (the precise obstacle, what was tried, the exact mathlib gap, recommended next move), commit it, and emit `<promise>EXTRASPECIAL LOOP STOP</promise>`.
- Emit the same promise when the queue (Steps 1–5) is exhausted, or when no build-green progress is achievable.
- If an iteration makes **no** build-green progress, reassess scope (smaller leaf) rather than repeating the same failing approach.
