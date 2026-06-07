# A2-lane loop blocker/handoff — alg-closed extraspecial rep theory (BG Thm 3.4) — 2026-06-07

The autonomous A2 loop **stopped** here: BG Thm 3.4's remaining core (Thm 2.5 = alg-closed
extraspecial representation theory) is a **large, expert, multi-session build whose foundational
results are absent from mathlib** — past the point where autonomous grinding is productive. Needs a
human decision on investment. Below is the full handoff.

## Done / ready (do NOT redo)
- **base-change infra** `RepresentationTheory/BaseChange.lean` (sorry-free): `baseChangeRepresentation`
  (+`_apply_tmul`,`_faithful`), `invariants_baseChangeRepresentation_eq_bot` (= BG (2.9)),
  `baseChangeRepresentation_comp` (subgroup form). [(2.8) deliberately skipped — not on the 3.4 path.]
- **Gor 5.3.7** = `S04e_GorThm37.exists_minimal_aInvariant_isExpPSpecial_of_pprimeAction_with_minimality`.
- **Lem 3.1**, **Lem 3.3** (`S03b_Lemma33`), **Prop 2.4** (`EigenspaceUnderCyclicAction`, general field).
- Designs: `s03_prop21_design.md` (Prop 2.1/Burnside route), `s03_thm36_plan.md` (§2 inventory + bottleneck).

## Why blocked (what the loop hit, 3 substantive attempts on the first leaf)
1. **Schur leaf** `End_{F[G]} V = F` over alg-closed (`bijective_algebraMap_end_asModule`): the raw
   `Module.End (MonoidAlgebra F G) ρ.asModule` route fights mathlib's `asModule` **synonym instances** —
   no `AddCommGroup ρ.asModule` found (so `Module.End` resolves as a *Semiring*, not Ring/DivisionRing,
   blocking the integral-domain ⇒ algebraMap-bijective argument), and `Module.Finite F (End_F asModule)`
   needs Noetherian/Free on the synonym. `Algebra F (End_{F[G]} asModule)` IS found; only these block.
   **→ RECOMMENDED FIX: the FDRep route** — `FDRep.finrank_hom_simple_simple [IsAlgClosed F]`
   (`RepresentationTheory/FDRep.lean:160`) gives `finrank F (W ⟶ W) = 1` for `Simple W` directly; work in
   the FDRep category (clean, no synonym), bridge `Representation ⇝ FDRep`. ALTERNATIVELY transport the
   synonym instances via `ρ.asModuleEquiv` (provide `AddCommGroup`/`Module F`/`Free`/`Finite` on `asModule`).
2. **Burnside** (`E(P) = End_F V`, the actual Prop 2.1): ~150-line Wedderburn structural proof. Key
   sub-step **"semisimple ring + faithful simple module ⟹ simple ring" is NOT in mathlib**. Route:
   `A := asAlgebraHom.range`; `A` semisimple (Maschke image, `RingHom.isSemisimpleRing_of_surjective`);
   `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed F A` (∏ matrices); faithful simple ⟹ single
   factor ⟹ `A ≅ Matrix(n,F)`; dim count `n² = (dim V)²` ⟹ `A = End_F V`.
3. **Gor 5.5.5** (extraspecial faithful irreducible dim = qⁿ): not in mathlib; via irreducible-degree
   sum-of-squares `q^{2n}·1+(q-1)(qⁿ)²=|P|` or Wedderburn + central character.
4. **Prop 2.2 alg-closed** (Clifford `V_K=M`): `Clifford.lean` is ℂ-only — needs an alg-closed version.

## Recommendation (human decision)
This tower (Prop 2.1 Burnside + Gor 5.5.5 + Prop 2.2 alg-closed + Thm 2.5 + Thm 3.4) is **several
dedicated expert sessions**, building representation theory that mathlib lacks. Options:
- **(A) Commit to it**: start with Schur via FDRep, then Burnside via the semisimple-Wedderburn route
  above. Each is a real multi-hour proof.
- **(B) Reprioritize**: park Thm 3.4/3.6 and pursue more tractable FT-spine frontiers (e.g. §10 lane A1
  Lem 10.4b, or §11+ once their blockers clear) while this rep-theory tower waits for dedicated effort.

The base-change groundwork is banked either way. Resume Schur from the FDRep route.
