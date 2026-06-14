# ChatGPT prompt — reconstruct two elided steps in Bender–Glauberman **Lemma 13.8**

> Lane F が ChatGPT へ渡す自己完結プロンプト。回答は私が厳密検証してから Lean 形式化する。
> 下の `---- PROMPT ----` から `---- END ----` までをそのまま ChatGPT (GPT-5 / o3 級) に貼る。

---- PROMPT ----

I am formalizing the Feit–Thompson Odd Order Theorem in Lean 4, following **Bender & Glauberman, _Local Analysis for the Odd Order Theorem_ (LMS LNS 188, 1994)**. I need you to expand two *elided* steps in the proof of **Lemma 13.8** (§13, p. 101) into fully rigorous, step-by-step reasoning. For each inference, state **exactly which result of the book is used and how its hypotheses are met**. Do not skip steps; I will translate your reasoning line-by-line into Lean, so I need every nontrivial implication justified.

## Standing setup and notation (BG conventions)

`G` is a minimal simple group of odd order (every proper subgroup is solvable). `M`, `M*` denote maximal subgroups of `G`. For a maximal subgroup `M`:

- `σ(M) ⊇ α(M) ⊇ β(M)` are sets of primes attached to `M`. `M_σ = O_{σ(M)}(M)` is the **σ-radical**, a normal Hall `σ(M)`-subgroup of `M`; similarly `M_α = O_{α(M)}(M)`, `M_β = O_{β(M)}(M)`, with `M_β ⊆ M_α ⊆ M_σ ⊴ M`.
- `E` is a complement to `M_σ` in `M` (`M = M_σ ⋊ E`, so `E` is a `σ(M)'`-group); `π(E) = σ(M)' ∩ π(M)` is partitioned into `τ₁(M), τ₂(M), τ₃(M)` (by `p`-rank of `M` and membership in `π(M')`). `ℰ_p¹(X)` = subgroups of `X` of order `p`.
- For `p ∈ π(M)`, `C_{M_α}(P)` etc. denote centralizers inside `M_α`.

Relevant cited results (use these as black boxes):

- **Uniqueness Theorem (Thm 9.6).** A subgroup `K < G` with `r(K) ≥ 2` and (`r(K) ≥ 3` or `r(C_G(K)) ≥ 3`) is "uniquely maximal": it lies in a unique maximal subgroup. (More generally the §9–§10 uniqueness machinery controls which maximal subgroups contain a given local subgroup.)
- **Theorem 10.1.** (a),(b): conjugacy/uniqueness of maximal subgroups sharing a suitable subgroup. In particular **10.1(b)**: if `Y ⊆ M ∩ M^g` and `M ⊇ N_G(Y) ⊇ C_G(Y)` (so `Y` is "large enough"), then `M^g = M^h` for some `h ∈ C_G(Y)`.
- **Theorem 10.2.** `M'/M_α` is nilpotent; `M_α ≠ 1` when `M'` is non-nilpotent; etc.
- **Lemma 10.12.** If `M*` is **not** conjugate to `M` in `G`, then `M_α ∩ M*_α = 1` and `σ(M) ∩ σ(M*) = ∅`. (a): a prime `r` dividing `|C_M(P)|` for suitable `P` lies outside `σ(M)`.
- **Lemma 12.18.** With `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(M)`, `q ∈ p'`, `Q` a nonidentity `P`-invariant `q`-subgroup of `M` with `C_Q(P)=1` and `ℳ(N_G(Q)) ≠ {M}`: if `M_α ≠ 1` and `q ∉ α(M)`, then `C_{M_α}(P) ≠ 1` and `C_{M_α}(PQ) = 1`.
- **Proposition 10.14(d).** `N_G(X) ⊆ M` for every nonidentity `β(M)`-subgroup `X` of `C_M(P)` (and similarly for conjugates `M^g`).
- **Theorem 13.4.** If `p ∈ τ₁(M)`, `P ∈ ℰ_p¹(E)`, `r ∈ π(E)`, `R ∈ ℰ_r¹(C_E(P))`, then `C_{M_σ}(P) ⊆ C_{M_σ}(R)`.

## Lemma 13.8 (statement)

The following configuration is **impossible**:
1. `M* ∈ ℳ` and `M*` is not conjugate to `M` in `G`;
2. `p ∈ τ₁(M) ∩ τ₁(M*)` and `P ∈ ℰ_p¹(M ∩ M*)`;
3. `Q` and `Q*` are `P`-invariant Sylow subgroups (possibly for different primes) of `M ∩ M*`;
4. `C_Q(P) = 1` and `C_{Q*}(P) = 1`;
5. `N_G(Q) ⊆ M*` and `N_G(Q*) ⊆ M`.

## Full textbook proof (verbatim)

> Assume this configuration and note the symmetry between `M` and `M*`.
> By (3), (5), and the Uniqueness Theorem, `Q` is a nonidentity Sylow subgroup of `M` for a prime `q ∉ α(M)`. Since `P ⊆ M ∩ M*` and `C_Q(P)=1`, `Q = [Q,P] ⊆ M' ∩ M*'`.
> Thus `Q M_α ⊴ M`, and `M = N_M(Q) M_α` because `M'/M_α` is nilpotent by Theorem 10.2.
> By Lemma 12.18, `C_{M_β}(P) ≠ 1` and `C_{M*_β}(P) ≠ 1`. Furthermore, by Proposition 10.14(d), `N_G(X) ⊆ M` for every nonidentity `β(M)`-subgroup `X` of `C_M(P)`, and similarly for `M*` and every conjugate `M^g` of `M`.
> Let `H` be a Hall `(β(M) ∪ β(M*))`-subgroup of `C_G(P)` and take any `s ∈ π(F(H))` and `t ∈ π(F(C_{M_β}(P)))`. By the symmetry between `M` and `M*`, we can assume that `s ∈ β(M)` and then that `H ⊇ C_{M_β}(P)`. Let `X = O_s(H)` and `Y = O_t(C_{M_β}(P))`. Then `X ⊆ M^g` for some `g ∈ G`. It follows that `M^g ⊇ N_G(X) ⊇ H ⊇ Y` and `M ⊇ N_G(Y) ⊇ C_G(Y)`. Since `Y ⊆ M ∩ M^g`, Theorem 10.1(b) yields `M^g = M^h` for some `h ∈ C_G(Y) ⊆ M`.
> Thus `M = M^g ⊇ H`.
> Take `r ∈ β(M*) ∩ π(H)`. Then `r` divides `|C_M(P)|`. By Lemma 10.12(a), `r ∉ σ(M)`.
> Since `M = N_M(Q) M_α` and `r ∈ π(C_M(P))`, some subgroup `R ⊆ N_M(Q)` of order `r` is centralized by `P`. Then `R ⊆ N_G(Q) ⊆ M*` and consequently `N_G(R) ⊆ M*` by Proposition 10.14(d). Now, since `PR` is conjugate in `M` to an abelian subgroup of `E`, Theorem 13.4 yields `1 ⊂ X ⊆ C_{M_σ}(P) ⊆ C_{M_σ}(R) ⊆ M*`.
> Then `[X,Q] ⊆ [M_α ∩ M*, Q] ⊆ M*_α` because `Q ⊆ M*'`, `M*'/M*_α` is nilpotent and `M_α ∩ M*` is a `Q`-invariant `q'`-subgroup of `M*`. On the other hand, `[X,Q] ⊆ M_α` and `M_α ∩ M*_α = 1` by Lemma 10.12. Thus `[X,Q] = 1` and `X ⊆ C_{M_α}(PQ)`, contrary to the fact that `C_{M_α}(PQ)=1` by Lemma 12.18. □

## GAP 1 — step 1 (the Uniqueness step)

> "By (3), (5), and the Uniqueness Theorem, `Q` is a nonidentity Sylow subgroup of `M` for a prime `q ∉ α(M)`."

Here `Q` is given (by (3)) only as a `P`-invariant **Sylow subgroup of `M ∩ M*`**, and (5) gives `N_G(Q) ⊆ M*`. Expand rigorously:
(1a) Why is `Q` nonidentity?
(1b) Why is `Q` a Sylow subgroup of the **whole** `M` (not merely of `M ∩ M*`)? Which exact statement (Uniqueness Theorem or a §10 corollary) is invoked, and how do hypotheses (3),(5) and `M* ≁ M` feed it? (I suspect the argument shows `ℳ(N_G(Q)) ≠ {M}` and then a Sylow/uniqueness comparison, but I need the precise chain.)
(1c) Why `q ∉ α(M)` (where `q` is the prime of `Q`)?

## GAP 2 — step 3 (the Hall `H` / `F(H)` / Theorem 10.1(b) paragraph)

Expand the entire paragraph from "Let `H` be a Hall `(β(M) ∪ β(M*))`-subgroup of `C_G(P)`…" through "…`r ∉ σ(M)`." In particular:
(2a) Why, by the `M ↔ M*` symmetry, may we assume `s ∈ β(M)`, and why does `s ∈ π(F(H)) ∩ β(M)` then let us assume `H ⊇ C_{M_β}(P)`? (What does choosing `H` to contain a particular `β(M)`-subgroup use — a conjugacy of Hall subgroups of `C_G(P)`?)
(2b) Why is `X = O_s(H) ⊆ M^g` for some `g ∈ G`? (Which result places this `s`-subgroup, `s ∈ β(M)`, into a conjugate of `M`?)
(2c) Justify the chain `M^g ⊇ N_G(X) ⊇ H ⊇ Y` and `M ⊇ N_G(Y) ⊇ C_G(Y)`, and how Theorem 10.1(b) with `Y ⊆ M ∩ M^g` gives `M^g = M^h`, `h ∈ C_G(Y) ⊆ M`, hence `M = M^g ⊇ H`.
(2d) Why does `β(M*) ∩ π(H) ≠ ∅` (so that `r` exists)? And why does `r ∈ π(H)` imply `r` divides `|C_M(P)|` (now that `H ⊆ M` and `H ⊆ C_G(P)`)?

Please answer GAP 1 and GAP 2 separately, each as a numbered rigorous argument citing the exact results used.

---- END ----
