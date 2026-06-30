# Free-orbit (Peterfalvi 9.8.c) — ChatGPT consult prompt

## Context for the consult

I am formalizing Peterfalvi's *Character Theory for the Odd Order Theorem* in Lean 4. I have
reduced the M-level irreducibility step of (9.8.c) to a single group/character-theory fact about a
**regular character of an abelian chief factor**, and I want the cleanest self-contained proof
strategy (to then formalize). The Coq math-comp proof establishes the analogous inertia via
`inertia_bigdprod_irr`, but I want to confirm the cleanest *abstract* argument before formalizing.

## Setup (abstract group theory)

- `M` is a finite group. `U ⋊ W₁` is a Frobenius group inside `M` with complement `W₁` of **prime
  order q** and kernel `U` (so `U` and `W₁` have coprime orders, and `W₁` acts fixed-point-freely
  on `U`).
- `H̄` is a finite **elementary abelian** group (the chief factor `H/H₀`), on which `U ⋊ W₁` acts
  (call the action `φ : (U ⋊ W₁) → Aut(H̄)`).
- `H̄` decomposes as an **internal direct product** `H̄ = ⊕_{w ∈ W₁} S_w` of the W₁-conjugate
  subgroups `S_w = φ(w)·S₀`, each of **prime order p** (`p ≥ 3`). `W₁` permutes the factors as a
  single **q-cycle** (`φ(w₀)·S_w = S_{w₀w}`), and `U` **preserves each factor** `S_w` (acts within
  it), because `S₀` is `U`-invariant and `U ◁ U⋊W₁`.
- `θ̄ : H̄ → ℂˣ` is a **regular** linear character: nontrivial on every factor `S_w`.

## What I know (already formalized in Lean)

1. `I_U(θ̄) = C` — the stabilizer of `θ̄` in `U` is exactly `C := C_U(...)` (the U-part inertia).
2. `θ̄ ∘ φ(w₀) ≠ θ̄` for a chosen nontrivial `w₀ ∈ W₁` — i.e. `θ̄` is **not fixed by W₁** (the
   regular character was constructed with non-constant factor-data so the q-cycle moves it).

## What I need

Prove **`θ̄ ∘ φ(w₀) ∉ U-orbit(θ̄)`**, i.e. `∀ u ∈ U, θ̄ ∘ φ(w₀) ≠ θ̄ ∘ φ(u)`. Equivalently
**`Stab_{U⋊W₁}(θ̄) ≤ U`** (the full stabilizer has trivial W₁-projection), equivalently the
W₁-inertia of `θ̄` (mod U) is trivial.

NOTE: this is **strictly stronger** than fact 2 (`θ̄^{w₀} ≠ θ̄`). If `U` acted transitively on the
nontrivial characters of each factor, naively `θ̄^{w₀}` could land in the U-orbit. So the argument
must use the **factor-permutation structure**, not just `θ̄^{w₀} ≠ θ̄`.

## Questions

1. **Cleanest argument**: Is the cleanest route (a) the **factor-permutation / direct-product
   inertia** argument (the inertia of a direct-product character is the product of per-factor
   inertias, and the q-cycle moves the "factor-support pattern" outside any U-twist), or (b) a
   **Frobenius-subgroup** argument (`Stab(θ̄) ≤ U⋊W₁` with `Stab ∩ U = C`; if `Stab ⊄ U` then by the
   Frobenius structure `Stab` contains a W₁-conjugate complement, forcing some U-conjugate of `θ̄` to
   be W₁-fixed — contradiction), or (c) something cleaner?
2. For route (b): does `θ̄^{w₀} ≠ θ̄` (fact 2) actually suffice, or do I need the **stronger**
   "no U-conjugate of `θ̄` is W₁-fixed"? If the latter, what is the cleanest way to get it from the
   regular/non-constant-factor-data construction?
3. Is there a clean way to **choose `θ̄`** (the per-factor characters) at construction time so that
   `θ̄^{w₀} ∉ U-orbit` is immediate — e.g. making the factor-characters pairwise distinct up to
   U-twist, or putting a single "marked" factor whose character is in a different U-orbit?
4. State the key intermediate lemma(s) precisely (as abstract group/character statements) so I can
   formalize them directly.

Please give a rigorous, self-contained argument with the precise intermediate statements.
