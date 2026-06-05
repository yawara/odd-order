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

## 進捗 (2026-06-05)

build-green helper を S10_MalphaMsigma.lean に積み上げ済 (main 直接, commits 7706aba/6201617/2c52936):
- ✅ `map_subtype_conj_smul`: `(c•K).map subtype = ↑c • (K.map subtype)` (conj⇄subtype 同変, §10 全般で再利用)。
- ✅ `normalizer_sylow_map_le_of_mem_sigma` (σ basic, mmd L2655): `p∈σ(M) ⟹ ∀ Sylow-p Q of M, N_G(Q̄)≤M`。
- ✅ **part (d)** `fusion_d_of_mem_sigma`: `Sylow.ofCard` で `(conj g•X).subgroupOf M` を Sylow 化 →
  M-共役 c → `↑c⁻¹g∈N_G(X)≤M` → `g∈M`。
- ✅ `maximal_normalizer_le_self`: `N_G(M)≤M` (maximal=coatom + simple; M=⊥ は cyclic⟹solvable で除外)。
- ✅ 既存 `mem_normalizer_of_conj_smul_eq_self` (GroupTheory) を再利用 (重複削除)。

**残り** = part (b) (最重・maximal-counterexample 帰納) + (b)⟹(a)(c)(e) 還元 + capstone wiring。
main 定理 `fusion_control_of_mem_sigma` の bundled sorry は未解消 (part b 完成で一気に閉じる)。

### 🔴 scaffold 規約バグ発見 (要修正): part (a)/(c) の積の順序

scaffold (a) は `∃ c∈C_G(X), ∃ m∈M, g = c*m` (C·M 順) だが、**scaffold の left-conj 規約
`conj g • X = gXg⁻¹` の下では BG の議論は `g = m*c` (M·C 順) を与える** (BG は `X^g=g⁻¹Xg`、
scaffold `conj g•X≤M` = BG `X^{g⁻¹}⊆M` ⟹ 共役子が逆 ⟹ 積順反転)。検証: (b) を g₁=1,g₂=g⁻¹ で
適用 → `cMc⁻¹=g⁻¹Mg` → `gc∈N_G(M)≤M`=:m → `g = m·c⁻¹` (M·C)。両 (b)-instance とも M·C。
**⟹ 主定理 (a) の `g = c*m` を `∃ m∈M, ∃ c∈C, g = m*c` に修正必要** (capstone wiring 前に)。
(c) も同様に order 要確認。これは placeholder scaffold の不正確さで、修正は合法。

### (b)⟹(a)⟹(c), (b)⟹(e) 還元 plan (prerequisite 確認済)

- (b)⟹(a): X≤M & conj g•X≤M ⟹ X≤conj 1•M ∧ X≤conj g⁻¹•M ⟹ (b)(g₁=1,g₂=g⁻¹) で `cMc⁻¹=g⁻¹Mg`
  ⟹ `gc∈N_G(M)` (`mem_normalizer_of_conj_smul_eq_self` + `maximal_normalizer_le_self`) ⟹ `g=m·c⁻¹`。
- (a)⟹(c): n∈N_G(X) ⟹ conj n⁻¹•X=X≤M ⟹ (a)(g=n⁻¹) で `n⁻¹=...` ⟹ n=a·c (a∈N_G(X)⊓M, c∈C)。
- (b)⟹(e): `centralizer X≤M` + conj g•X≤M。**X≤M の導出が要** (BG 暗黙; C_G(X)⊆M から?要精査)。
- L=N_G(X) solvable = `hG.solvable_of_lt_top L (hL:L<⊤)`; L<⊤ は L=⊤⟹X⊴G⟹X∈{⊥,⊤} で除外。

### part (b) 帰納の追加メモ

- 反例 X の maximal-order 帰納 = `Nat.card G - Nat.card ↥X` の `Nat.strong_induction_on` (generalizing X);
  IH は `|X'|>|X|` (= measure 減少) で (b)。X⊂P で (b)-for-P を IH から、(c)-for-P を (a)-of-(b) 経由。
- prerequisite 全確認済: Thm 9.6=`S09.uniquenessTheorem`, Thm 4.18(e)=`S04.solvable_structure_of_pRank_le_two`,
  Frattini=§6 Lem6.6, self-normalizing ✅, L solvable ✅, part(d) ✅, σ basic ✅。

## やること / 証明構造 (BG 忠実, mmd L2665-2711)

- [x] **(d)**: X, X^g とも Syl_p(M) ⟹ Sylow 共役で `(X^g)^h=X` (h∈M) ⟹ `gh∈N_G(X)⊆M` ⟹ `g∈M`. (`fusion_d_of_mem_sigma`)
- [ ] **(b)⟹(a)**: X⊆M^{g⁻¹}=M^c (c∈C_G(X)) ⟹ cg∈N_G(M)=M ⟹ g=c⁻¹(cg).
- [ ] **(a)⟹(c), (b)⟹(e)**: corollary.
- [ ] **(b) by contradiction (maximal-order counterexample X)** [最重・残りの本体]:
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
