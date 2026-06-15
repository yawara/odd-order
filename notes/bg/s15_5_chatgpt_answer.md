# ChatGPT (Pro 拡張) answer — BG Corollary 15.5 + my verification

(Lane G, 2026-06-15. odd-order project, thinking 14m18s. **Verified — solid except 2 Case-II fixes below.**)

## Solid (verified rigorous), formalize as-is

- **Lemma 0**: M_F ≤ F(M) (nilpotent normal ⊆ Fitting), M_F ≤ M_σ (Lemma 15.1).
- **Lemma 1**: O_σ(F(M)) = F(M_σ). char-in-normal both directions: F(M_σ) char M_σ◁M ⟹ ◁M, nilpotent ⟹ ≤F(M), σ ⟹ ≤O_σ(F(M)); conversely O_σ(F(M)) char F(M)◁M ⟹ ◁M, normal σ ⟹ ≤M_σ, nilpotent normal in M_σ ⟹ ≤F(M_σ). Case-independent.
- **Lemma 2**: F(M) nilpotent ⟹ F(M)=O_σ(F(M))×O_{σ'}(F(M))=F(M_σ)×Y. Unpack: F(M)=F(M_σ)Y, F(M_σ)⊓Y=1 (σ vs σ'), [F(M_σ),Y]=1 (distinct Hall components of nilpotent group commute).
- **Lemma 3**: C_M(F(M))≤F(M) (Prop 1.3, solvable M).
- **Case I (H=M_σ, M_σ nilpotent)**: F(M_σ)=M_σ=M_F=H, F(M)=H×Y, Y≤C_M(H). Cor 15.3(a) at H=M_σ: C_M(H)=C_{M_σ}(H)X=Z(H)X, X cyclic τ₂. F(M)=C_M(H)·H=HX (X centralizes H, |X| coprime |H| ⟹ HX nilpotent normal ⟹ ≤F(M); reverse from F=H×Y, Y≤C_M(H)). Y↪C_M(H)H/H≅X/(X∩H)≅X (X∩H=1) ⟹ Y cyclic, π(Y)⊆τ₂. M''≤M_σ=H≤F(M) (Lemma 15.1(a) M'/M_σ abelian). M_σ≤M', M'/M_σ abelian⟹nilpotent.

## ⚠ Case II (H≠M_σ, M_σ NOT nilpotent) — 2 FIXES to the answer

The answer claims "Thm 15.2(g) gives F(M) ≤ M_F, forcing F(M)=M_F". **This overreads Thm 15.2(g)**, which (mmd) gives **F(M) = QC_M(Q) = … ⊂ M_σ** (i.e. F(M) ⊆ M_σ), NOT F(M) ⊆ M_F. Correct route:

- **FIX 1 (conjuncts 1,4): use F(M) ⊆ M_σ, not F(M)=M_F.** F(M) ⊆ M_σ ⟹ F(M) is a σ-group ⟹ Y = O_{σ'}(F(M)) = 1 (conjunct 1 trivial). And F(M)=F(M_σ): F(M)◁M nilpotent ⊆ M_σ ⟹ ◁M_σ nilpotent ⟹ ⊆F(M_σ); F(M_σ)⊆F(M) by Lemma 1. So F(M)=F(M_σ)=F(M_σ)×1=F(M_σ)×Y (conjunct 4, Y=1). M''≤F(M): Thm 15.2(g) `M'' ≤ F(M)` (already exposed). M_F≤M': M_F≤M_σ=M'.
  - **REQUIRES strengthening Lean Thm 15.2** (`mf_ne_msigma_typeP1_structure`) to expose **`fittingInAmbient M ≤ Msigma M`** (faithful — mmd 15.2(g) "F(M) ⊂ M_σ"; currently only `M'' ≤ F(M)` + `M_σ=M'` exposed). Thm 15.2 stays sorried; just add the conjunct.
- **FIX 2 (conjunct 7): avoid circular Cor 15.6.** The answer excludes Case II for "M_F cyclic → F(M) cyclic" via Cor 15.6 — but **15.6 cites 15.5 (circular!)**. Correct: in Case II, Thm 15.2 gives a normal subgroup `Q ≤ M_F` with section `|Q.subgroupOf(Q⊔Q0)| = q^p` (p odd prime ≥3). q^p-order elementary-abelian-ish section of rank p≥3 ⟹ **Q non-cyclic ⟹ M_F non-cyclic** (no 15.6). So "M_F cyclic" ⟹ ¬Case II ⟹ Case I (direct: F(M)=M_F×Y both cyclic coprime ⟹ cyclic).
  - Lean: Thm 15.2 exposes `Q ≤ MF M` and `Nat.card ↥(Q.subgroupOf (Q⊔Q0)) = q^p`. Derive M_F non-cyclic from a rank≥2 (or ≥3) section. (Need: a quotient/subgroup of order q^p with p≥2 in a cyclic group is impossible — cyclic q-group has cyclic sections; q^p with the section being Q/Q0 elementary abelian rank p contradicts cyclic.)

## Direct answers (verified): F(M)=C_M(M_F)·M_F (Case I via Cor15.3a HX≤F(M) + reverse; Case II via F(M)=M_F-ish, but really F(M)=F(M_σ) and C_M(F(M))≤F(M)); M''⊆F(M)/M_F⊆M' as above; (d) Y is τ₂, K is τ₂', M/M'≅K ⟹ Y↦triv ⟹ Y≤M', plus F(M_σ)≤M_σ≤M'.

## Formalization plan
1. **Strengthen Thm 15.2** (`mf_ne_msigma_typeP1_structure`): add TWO conjuncts to its conclusion (both sorried/faithful, the sorry covers them — mmd 15.2(f),(g) imply them):
   - `fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M`  (mmd "F(M) ⊂ M_σ") — for FIX 1.
   - `¬ IsCyclic ↥(MF M)`  (M_F ⊇ Q̄ elementary abelian order q^p, rank p≥3 ⟹ non-cyclic) — for FIX 2 / conjunct 7, breaking the 15.5↔15.6 circularity cleanly.
2. Helper lemmas: `O_σ(F(M))=F(M_σ)` (Lemma 1), F nilpotent Hall decomposition (Lemma 2). Check repo for existing `fittingInAmbient` / `opiCoreInG` API.
3. Case split on `MF M = Msigma M` (= M_σ nilpotent ⟺ Case I).
4. Case I: Cor 15.3(a) cite + the embedding/decomposition. Case II: strengthened Thm 15.2 ⟹ F(M)⊆M_σ ⟹ Y=1, F(M)=F(M_σ); conjunct 7 via M_F non-cyclic from q^p.
5. Cite (sorried): Lemma 15.1 (`typeP_auxiliary_structure`), Thm 15.2, Cor 15.3 (`mf_hall_centralizer_control`). Cor 15.5 becomes sorry-free gated on those.
