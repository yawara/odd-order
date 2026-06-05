# 引き継ぎ — BG §9 Lemma 9.5 closure (package-interface 再構成) — 2026-06-05

## 状況

- **✅ L2 = BG Thm 4.20(c) 存在 完成** (commit 4475477, `S05.exists_characteristicSylowSeriesPackage_of_rank_fitting_le_two`, axiom-clean, full build 3580)。
- **🔴 §9 Lemma 9.5 (`scn3_isUniquelyMaximal`, S09_Lemma95:2407 の bare sorry) は L2 単独では閉じない**。§9 helper 鎖が
  `CharacteristicSylowSeriesPackage` を**無条件外部仮説**として thread するが、package(=L2)は `rank F(M)≤2`(全素数)を要し、
  §9 で得るのは `r_p(F(M))≤2`(素数 p のみ)だけ。`r(F(M))` は q≠p で ≥3 になり得る(BG 原文 (9.6)-(9.8)(9.12) が r(F)≥3 を明示処理)。
  ⟹ package を `.some` で無条件供給する道は塞がれている。詳細 = `notes/bg/s09_uniqueness.md`「✅🔴 2026-06-05 (続)」。
- **✅ Phase A 基盤完成**: package bridge `exists_characteristicSylowSeriesPackage_of_maximal_of_rank_fittingInG_le_two`
  (S09_Lemma95, lowRank helper の直前, build-green) = 「M maximal + `Nontrivial ↥M` + `rank (fittingInG M)≤2` ⟹
  `Nonempty (CharacteristicSylowSeriesPackage ↥M)`」。M solvable=`hG.solvable_of_mem_maximalSubgroups`,
  odd=`|M|∣|G|`, `rank F(↥M)=rank(fittingInG M)`(M.subtype iso=`Subgroup.equivMapOfInjective`)経由で L2 を呼ぶ。

## 残作業 = Phase A 残 (propagation) + Phase B (body assembly)

### Phase A 残: package 仮説の撤去を鎖全体へ伝播

**鍵**: `normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases` は **既に
`by_cases hrank : rank (fittingInG M) ≤ 2` を持ち、series S は low-rank 分岐 (lowRank helper) でのみ消費**。
⟹ low-rank 分岐で bridge を呼んで package を**内部生成**し (この分岐では `hrank` が in scope, `Nontrivial ↥M` は
`A ≤ R ≤ M` + A nontrivial から), `(S, hpos, hterminal_mem)` 引数を撤去。high-rank 分岐は Lemma 9.4 (package 不要, 既存)。

その後、撤去を caller へ伝播 (全 `private`, S09_Lemma95)。**全 14 helper が package 引数 (S/SP/SP_L/hSP) を thread**:

M-chain (series S 三つ組 `(S, hpos, hterminal_mem)` を撤去):
1. `normalizer_le_maximal_of_scn3Global_characteristicSylowSeries_rankCases` ← **内部生成に変更 (FIX point)**
2. `normalizer_scn3_self_le_maximal_of_rankCases` (calls 1)
3. `normalizer_scn3_sylowNormalizer_le_maximal_of_rankCases` (calls 1,2)
4. `normalizer_scn3_self_le_maximal_of_not_scn3` (calls 2)
5. `normalizer_scn3_pSubgroup_le_maximal_of_not_scn3` (calls 3)
6. `normalizer_scn3_pSubgroup_le_witness_maximal_of_not_scn3` (~1228, SP_L 消費, calls 5 で M:=L)
7. `exists_pSubgroup_normalizer_package_of_not_scn3` (calls 5)
8. `exists_pSubgroup_normalizer_package_of_not_scn3_of_sylowSeriesPackage` (SP → 撤去ごと不要)

L-chain (9.10) + (9.12) (`SP_L`/`hSP` を撤去):
9. `p0_le_derivedInG_inf_of_scn3_witness_maximal` (~1319, SP_L, calls 6)
10. `false_of_not_le_centralizer_inf_centralizer_opiCoreFitting_witness` (~1989+, SP_L, calls 9)
11. `p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package` (~2024+, hSP, calls 10 via `exists_nonU_..._witness`)
12. `normalizer_p0_le_maximal_of_high_rank_opiCoreFitting_package` (hSP, calls 11)
13. `normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package` (hSP, calls 11)
14. `rank_opiCoreFitting_le_two_of_pSubgroup_normalizer_package` (hSP, calls 12)

各 helper: signature から package 引数を削除 + 内側呼び出しの該当 arg を削除。`hSP` を取る helper (11-14) は
`hSP` 連言を削除 (witness L 用 package は 6 が内部生成するため不要)。全て **mechanical** だが行番号シフトに注意。
leaf build (`lake build OddOrder.BG.Ch2_Uniqueness.S09_Lemma95`) で逐次検証。

### Phase B: `scn3_isUniquelyMaximal` の body assembly (BG mmd L2559-2625, 67 行)

package-free 化した helper を使い本体を書く。BG 反証構造:
1. `by_contra hAnot`。`exists_maximal_centralizer_and_pRank_fittingInG_le_two_of_not_scn3` で M∈𝓜(C_G(A)) + r_p(F(M))≤2 (9.6)。
2. `exists_pSubgroup_between_scn3_and_normalizer` で P (A≤P≤N_G(A), p-群)。
3. `normalizer_scn3_pSubgroup_le_maximal_of_not_scn3` (package-free 後) で P≤M ∧ N_G(P)≤M (9.9)。R=A 版で P⊆N_G(A)⊆M。
4. P0=[P,N_G(P)]=`derivedInG`? — `P0 ≠ ⊥` は Thm 1.18 (G に normal p-complement 無 ← simple nonabelian)。helper 要確認。
5. (9.11) `p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package` (package-free 後) で P0 が O_{p'}(F(M)) 中心化。
6. (9.12) `normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package` (r(F)≥3) / 低 rank 版 + `rank_opiCoreFitting_le_two_of_pSubgroup_normalizer_package` で {M}=𝓜(N_G(P0))。
7. 最終矛盾 (L2621-2625): Ω₁(A)∉𝒰 → Thm 9.1 で x∈Ω₁(A)^# with C_G(x)⊄M → M*∈𝓜(C_G(x)) → (9.12) で M*=M = 矛盾。

P0 の定義 (`[P,N_G(P)]` = `derivedInG (N_G(P))` の像? or commutator)・Thm 1.18 (Frobenius normal p-complement)
helper の所在は要確認 (`derivedInG`/`Thm 1.18`/Ω₁(A) の §9 helper を grep)。

## 規模

Phase A propagation ~14 edit (mechanical) + Phase B ~60-100 行 (helper composition)。**dedicated workflow 1 本相当**。
foreground 逐次 (leaf build 駆動) 推奨; 重い proof でなく helper 合成ゆえ tractable だが量がある。
