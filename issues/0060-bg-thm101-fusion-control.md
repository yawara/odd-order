---
id: 60
slug: bg-thm101-fusion-control
title: "BG Thm 10.1 fusion control (§10 keystone)"
created: 2026-06-05
---

# BG Thm 10.1 fusion control (§10 keystone)

## 背景

§9 (Uniqueness Thm 9.6) 完成 (commit 12ae441) で §10 解禁。§10 = 18 scaffold sorry の大型節で、
**Thm 10.1 が keystone** (Thm 10.2 / Cor 10.7 等がすべて依存)。
依存検証 = `notes/bg/s10_malpha_msigma.md`「✅ 2026-06-05 着手」節。
旧ノートの「Thm 10.1 が Thm 10.6 (p-length-1) を要し循環?」は **red herring** — 実際は Thm 4.18(e) を使う。

**Target**: `OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma`
([S10_MalphaMsigma.lean:256](OddOrder/BG/Ch3_MaximalSubgroups/S10_MalphaMsigma.lean)). mmd L2657-2711。

## Statement (5 parts, p ∈ σ(M), X 非自明 p-subgroup of G)

- (a) `X⊆M, X^g⊆M ⇒ g=cm` (c∈C_G(X), m∈M).
- (b) `C_G(X)` は `{M^g | X⊆M^g}` 上 conjugation 推移的.
- (c) `X⊆M ⇒ N_G(X)=N_M(X)·C_G(X)`.
- (d) `X∈Syl_p(M), X^g⊆M ⇒ g∈M`.
- (e) `C_G(X)⊆M, X^g⊆M ⇒ g∈M`.

## やること / 証明構造 (BG 忠実, mmd L2665-2711)

- [ ] **(d)**: X, X^g とも Syl_p(M) ⟹ Sylow 共役で `(X^g)^h=X` (h∈M) ⟹ `gh∈N_G(X)⊆M` ⟹ `g∈M`.
  `N_G(X)⊆M`: p∈σ(M) で N_G(P)⊆M の Sylow P, X=P^m → N_G(X)=N_G(P)^m⊆M.
- [ ] **(b)⟹(a)**: X⊆M^{g⁻¹}=M^c (c∈C_G(X)) ⟹ cg∈N_G(M)=M ⟹ g=c⁻¹(cg).
- [ ] **(a)⟹(c), (b)⟹(e)**: corollary.
- [ ] **(b) by contradiction (maximal-order counterexample X)**:
  - L=N_G(X), M₁,M₂∈{M^g|X⊆M^g} with `M₁^c≠M₂ ∀c∈C_G(X)` (10.1).
  - M₂^g=M₁ ⟹ X,X^g⊆M₁. X∉Syl_p(M₁) (else (d)⟹矛盾) ⟹ X⊂X₁∈Syl_p(L∩M₁), X⊂X₂∈Syl_p(L∩M₂).
  - P=Syl_p(L)⊇X₁, t∈L with X₂⊆P^t. p∈σ(M) で M⊇Syl_p(G) → 共役で P⊆M と仮定可.
  - X の maximal choice ⟹ M₁,M は C_G(X) 共役; M^t,M₂ も ⟹ (10.2) `M,M^t は C_G(X) で非共役`.
  - **r(P)≥3**: Thm 9.6 で P∈𝒰, P⊆L∩M ⟹ L⊆M, t∈L ⟹ (10.2) 矛盾 ⟹ **r(P)≤2**.
  - **r(P)≤2**: Thm 4.18(e) で P=Syl_p(O_{p',p}(L)) ⟹ `L=N_L(P)·O_{p'}(L)`. t=uv (u∈N_L(P), v∈O_{p'}(L)).
    O_{p'}(L)∩X=1 ⟹ v∈C_G(X). X⊂P, maximal choice ⟹ (c) for P ⟹ `N_G(P)=N_M(P)C_G(P)` ⟹
    u=wx (w∈N_M(P)⊆M, x∈C_G(P)⊆C_G(X)). t=wxv, M^t=M^{xv}, xv∈C_G(X) ⟹ (10.2) 矛盾. □

## prerequisite (全 repo 内に存在, 検証済 2026-06-05)

- Thm 9.6 = `Ch2.S09.uniquenessTheorem`.
- Thm 4.18(e) = `S04.solvable_structure_of_pRank_le_two` (S04g:878) 第5連言 `hasPLengthOne p L`.
- Frattini: `hasPLengthOne` + `S06.oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow` + `Sylow.normalizer_sup_eq_top'`.
- L=N_G(X) solvable: proper⊆min-simple ⟹ solvable (要 `hG.solvable_of_*` の確認).
- σ 基本 (mmd L2655): `mem_sigma_iff` (S10:149) の「∃ Sylow」→「∀ Sylow」拡張小補題。

## Lean 設計メモ

- 共役 = `MulAut.conj g • X` (scaffold 規約)。
- maximal-order counterexample = `Nat.card X` の strong induction (downward) / `Finset.exists_max`。IH は X⊊X' で (b)(c).
- private helper 分割: `fusion_d` / `fusion_b` (帰納, 最重) / `fusion_b_imp_others` → capstone で 5 連言。

## 完了条件

`fusion_control_of_mem_sigma` の sorry が消え、build-green + axiom-clean ([propext,choice,Quot.sound])。
→ Thm 10.2 (`isHall_Msigma_Malpha`) 解禁。

## 参照

- notes: `notes/bg/s10_malpha_msigma.md` (依存 DAG)。
- §9 完成: commit 12ae441。
- mmd: `references/bg/local-analysis.mmd` L2657-2711。
