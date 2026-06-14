# ChatGPT prompt — reconstruct the elided steps in Bender–Glauberman **Theorem 13.10**

> 用途: 下記プロンプトをそのまま ChatGPT (o3/GPT-5 級) に渡し、回答を厳密検証してから Lean 化する。
> 背景: Lane F /loop で Thm 13.9 完了後、13.10 の 3 つの elision (GAP A/B/C) で詰まった。
> 自己完結プロンプト + 回答検証が条件 (memory `feedback-ask-chatgpt-for-elided-gaps`)。

---

I am formalizing the Feit–Thompson Odd Order Theorem in Lean 4, following **Bender & Glauberman,
_Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994)**. I need you to expand several
*elided* steps in the proof of **Theorem 13.10** (§13, p. 102) into fully rigorous, step-by-step
reasoning. For each inference, state **exactly which result of the book is used and how its
hypotheses are met**. I will translate your reasoning line-by-line into Lean, so I need every
nontrivial implication justified.

## Setup / standing notation (BG §10–§13)

- `G` is a minimal simple group of odd order; `M` is a maximal subgroup.
- `σ(M) = {p ∈ π(M) : some Sylow p-subgroup P of M has N_G(P) ⊆ M}`.
- `α(M) = {p ∈ π(M) : r_p(M) ≥ 3}` (p-rank ≥ 3); `β(M) = {p ∈ α(M) : p "ideal"}`; `α(M) ⊆ σ(M)`.
- `M_σ = O_{σ(M)}(M)`, `M_α = O_{α(M)}(M)`, `M_β = O_{β(M)}(M)`. **`M_σ ≠ 1` always**, but
  `M_α` may be trivial (when `α(M) = ∅`).
- `E` is a fixed Hall complement to `M_σ` in `M` (`M = M_σ E`, `M_σ ∩ E = 1`), with Hall
  `τ_i(M)`-pieces `E₁, E₂, E₃` (`τ₁/τ₂/τ₃` partition `π(E)`). `E₃` is **cyclic** and normal in `E`.
- `τ₃(M) ∩ σ(M) = ∅` (so a prime `q ∈ τ₃(M)` is **not** in `σ(M)`, hence not in `α(M)`).
- "X acts in a prime manner on N" means `C_N(g) = C_N(X)` for all `g ∈ X#`.
  "X acts regularly on N" means `C_N(g) = 1` for all `g ∈ X#`.

## Results I already have formalized (cite freely)

- **Lemma 12.18**: given `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E₁)`, `q ≠ p`, a nontrivial `q`-subgroup `Q ≤ M`
  with `P ≤ N_G(Q)`, `C_Q(P) = 1`, and `ℳ(N_G(Q)) ≠ {M}` (i.e. some maximal `M* ⊇ N_G(Q)`,
  `M* ≠ M`): **(branch 1)** *if `M_α ≠ 1` and `q ∉ α(M)`* then `C_{M_α}(P) ≠ 1` and
  `C_{M_α}(PQ) = 1`; **(branch 2)** *if `Q` is a Sylow `q`-subgroup of `M`* then additionally
  `α(M) = β(M)` and `M_α ≠ 1` (and the same two centralizer conclusions). My Lean port literally
  has these two branches; branch 1 **requires `M_α ≠ 1` as a hypothesis**.
- **Lemma 13.1(a)**: roughly, if `[M_σ ∩ M*, P] ≠ 1` (with `p ∈ τ₁(M)`, `P ∈ ℰ_p¹`, `M* ≠ M`
  appropriate) then `p ∈ τ₁(M*)`.
- **Corollary 13.2(a)**: a `p`-subgroup of `M ∩ M*` (`p ∈ τ₁∪τ₃`) centralizes `M_σ ∩ M*`.
- **Corollary 13.3(b)**: `E₃` acts in a prime manner on `M_σ`.
- **Lemma 13.6**: if `ℳ(Q*) ≠ {M}` (and the standing rank/Sylow hypotheses) then `C_{Q*}(P) = 1`.
- **Lemma 13.7**: if `E₁ ≠ 1` and `E₁` does **not** act regularly on `E₃`, then `E₁E₃` acts in a
  prime manner on `M_σ`.
- **Lemma 13.8**: a certain symmetric configuration with **two** subgroups `Q, Q*` that are
  **maximal `q`- resp. `q*`-subgroups of `M ∩ M*`** is impossible.
- **Proposition 10.14(d)**: a nontrivial `β(M)`-subgroup `Y ≤ M` has `N_G(Y) ⊆ M`.
- **Lemma 12.19**: (β-complement / Sylow-of-derived statement; q, q* ∉ β(M)).
- **Theorem 13.5**: `E₁ ≠ 1 ⟹ E₁` prime on `M_σ`.

## The book's proof of Theorem 13.10 (verbatim, with my GAP markers)

> **Theorem 13.10.** Suppose some `P ∈ ℰ_p¹(E₁)` does not centralize `E₃`. Then (a) `E₁` acts
> regularly on `E₃`, (b) `E₃` acts regularly on `M_σ`, and (c) `C_{M_σ}(P) ≠ 1`.
>
> *Proof.* Since `E₃` is a cyclic normal Hall subgroup of `E`, there exists `q ∈ τ₃(M)` such that
> `P` acts regularly on the Sylow `q`-subgroup `Q` of `E₃`. Thus `Q = C_Q(P)[Q,P] = [Q,P] ⊆ E′`.
> Take `M* ∈ ℳ(N_G(Q))`. By Lemma 12.2(b), `M*` is not conjugate to `M` in `G`. In particular,
> `M* ≠ M`. Consequently, by Lemma 12.18, **[GAP A]** `C_{M_α}(P) ≠ 1` and `C_{M_α}(PQ) = 1`.
> Since `M_α ⊆ M_σ`, this proves (c) and **[GAP B]** shows that `E₁E₃` is not prime on `M_σ`.
> Therefore (a) follows from Lemma 13.7.
>
> Now assume that (b) is false. Then `C_{M_σ}(E₃) ≠ 1` because `E₃` is prime on `M_σ` by Cor
> 13.3(b). Take `q* ∈ π(C_{M_σ}(E₃))` and let `Q*` be an `E`-invariant Sylow `q*`-subgroup of
> `C_{M_σ}(E₃) = C_{M_σ}(Q)`. Since `Q` centralizes `M_σ ∩ M*` by Cor 13.2(a), `Q*` is a Sylow
> `q*`-subgroup of `M_σ ∩ M*` and hence of `M ∩ M*`. By (13.5) and Lemma 12.19, `q* ∈ β(M)` or
> `Q*` is a Sylow `q*`-subgroup of `M_σ`. Hence, by Prop 10.14(d) and the definition of `σ(M)`,
> `N_G(Q*) ⊆ M`. If `q* ∈ β(M)`, then `C_{Q*}(P) ⊆ C_{M_α}(PQ) = 1`, and if `q* ∉ β(M)`, then
> `C_{Q*}(P) = 1` by Lemma 13.6 because `ℳ(Q*) ≠ {M}`. In particular, `[M_σ ∩ M*, P] ≠ 1`.
> Therefore, by Lemma 13.1(a), `p ∈ τ₁(M*)`. Now Lemma 13.8 **[GAP C]** yields a contradiction. □

## What I need you to reconstruct (be explicit and rigorous)

**GAP A — Why is `C_{M_α}(P) ≠ 1` (in particular `M_α ≠ 1`)?**
My Lean Lemma 12.18 branch 1 *requires* `M_α ≠ 1`. Here `Q` is a Sylow `q`-subgroup of **`E₃`**,
*not* of `M`, so branch 2 (which would output `M_α ≠ 1`) does not directly apply. Questions:
(1) Is `M_α ≠ 1` automatic in this context, and if so from what? (e.g. does the existence of
`P ∈ ℰ_p¹(E₁)` not centralizing `E₃` force `α(M) ≠ ∅`, or is there a standing §11/§12 fact that
`M_α ≠ 1` for the maximal subgroups under consideration here?)
(2) If `M_α = 1` is genuinely possible, how does the book's conclusion `C_{M_α}(P) ≠ 1` survive —
is there a separate argument, or is the intended Lean route to first build a Sylow `q`-subgroup of
`M` (so that branch 2 fires) and transfer? Please give the precise justification.

**GAP B — Why does `C_{M_α}(P) ≠ 1` together with `C_{M_α}(PQ) = 1` show `E₁E₃` is not prime on
`M_σ`?** Spell out, with `x` a generator of `P` and `y` a generator of `Q ≤ E₃`: which two
elements of `(E₁E₃)#` witness `C_{M_σ}(·)` taking two different values (so that the prime-action
equality `C_{M_σ}(g) = C_{M_σ}(E₁E₃)` fails)? Justify `⟨xy⟩ = ⟨x,y⟩` (commuting, coprime orders)
and that `C_{M_σ}(xy) = C_{M_σ}(PQ)` while `C_{M_σ}(x) = C_{M_σ}(P) ≠ C_{M_σ}(PQ)`.

**GAP C — The final Lemma 13.8 contradiction.** Lemma 13.8 needs **two** subgroups, both
**maximal `q`-/`q*`-subgroups of `M ∩ M*`**: one (`Q*`) with `N_G(Q*) ⊆ M`, and another with
`N_G(·) ⊆ M*`. The proof produced `Q*` (a Sylow `q*` of `M ∩ M*`, with `N_G(Q*) ⊆ M`). What plays
the role of the **second** subgroup (the one with normalizer in `M*`), and why is it a *maximal*
`q`-subgroup of `M ∩ M*`? Is it the original `Q` (Sylow `q` of `E₃`, with `M* ∈ ℳ(N_G(Q))` so
`N_G(Q) ⊆ M*`) — and if so, why is that `Q` a *maximal* `q`-subgroup of `M ∩ M*` here? Also: is
"(13.5)" the displayed equation (13.5) or **Theorem 13.5**? Give the exact statement used and how
"q* ∈ β(M) or Q* is a Sylow q*-subgroup of M_σ" follows from it together with Lemma 12.19.

Please answer GAP A, GAP B, GAP C separately, citing exact book results and verifying each
hypothesis. Where a step is a coprime-action / Hall / Sylow fact, name the precise standard
statement.
