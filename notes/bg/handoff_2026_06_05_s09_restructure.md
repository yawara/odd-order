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

## ✅ Phase A 完了 (commit 3879b87, leaf build 2480 green)

package 仮説 (`S`/`SP`/`SP_L`/`hSP`) を §9 normalizer 鎖 全 13 helper から撤去済。`rankCases` adapter の
low-rank 分岐で bridge (L2) により package を内部生成。`ne_bot_of_mem_scn3Global` を un-private 化、
`_of_sylowSeriesPackage` 変種を削除。**`scn3_isUniquelyMaximal` (S09_Lemma95:2380 の bare sorry) は
package なしで helper を呼べる状態 = Phase B 解禁**。

## 残作業 = Phase B (`scn3_isUniquelyMaximal` body assembly)

BG mmd L2559-2625 (67 行) を package-free helper で組む。**注意: 単純な helper 合成でなく、3 つの
sub-assembly を新規に書く必要がある** (helper が無い):

1. **P0 = [P, N_G(P)] の setup + P0 ≠ ⊥**: `exists_pSubgroup_between_scn3_and_normalizer` の P は
   **N_G(A) の Sylow-p であって G の Sylow-p ではない** (helper は Sylow-of-G を主張しない)。BG (9.9) 後の
   `P0 ≠ 1` は **Thm 1.18 (Burnside, `Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer`)** を
   使い「P0=⊥ ⟹ N_G(P)≤C_G(P) ⟹ G に normal p-complement ⟹ G simple nonabelian と矛盾」。
   ⟹ **P を G の Sylow-p に取り直す** (A ⊴ G の Sylow-p ⊆ N_G(A) ゆえ N_G(A) の Sylow-p = G の Sylow-p)
   + Burnside + `hG.simple` で no-normal-p-complement。**この sub-assembly が要新規実装**。
   P0 := ⁅P, N_G(P)⁆ (= `derivedInG (N_G(P))` 以下、`Subgroup.commutator_mono` で hP0N; ⁅P,N_G(P)⁆≤P で hP0p)。
2. **(9.11)+(9.12) 合成**: `p0_le_centralizer_opiCoreFitting_of_pSubgroup_normalizer_package` (package-free 後)
   で P0 が O_{p'}(F(M)) 中心化 (9.11)。(9.12) は r(F)≤2/≥3 で場合分け:
   - r(F)≥3: `normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package` (package-free 後)。
   - r(F)≤2: `rank_opiCoreFitting_le_two_of_pSubgroup_normalizer_package` の対偶 + 低 rank で M≤N_G(P0)
     (BG L2615-2619, M=O_{p'}(F)·N_M(P), P0⊴M) → `normalizer_isUniquelyMaximal_and_eq_maximal_of_maximal_le_normalizer`。
     **M≤N_G(P0) の低 rank 議論が要新規実装** (Thm 4.20 M'≤F + Frattini)。
3. **最終矛盾 (L2621-2625)**: Ω₁(A)∉𝒰 → Thm 9.1 (`noncyclic_isUniquelyMaximal_of_centralizer_le`, 済) で
   x∈Ω₁(A)^# with C_G(x)⊄M → M*∈𝓜(C_G(x)) → (9.12) を M* に適用し {M*}=𝓜(N_G(P0))={M} → M*=M だが
   C_G(x)⊄M=M* 矛盾。**この最終 step も要新規実装** (Ω₁(A) の helper `omega1OfAbelian` はあるが最終合成は無)。

**規模感**: Phase B は ~80-120 行 + sub-assembly 3 つ (P0≠⊥ Burnside / 低rank M≤N_G(P0) / 最終矛盾)。
helper 合成だけでなく新規 proof を含むため genuine な作業量。foreground 逐次 (leaf build 駆動) 推奨。

## Phase B 実装レシピ (hooks 確定済, 2026-06-05)

**✅ sub-assembly 1 完成** (commit 8aa7cc4): `commutator_normalizer_ne_bot_of_isSylow hG (P:Sylow p G) (hp_dvd : p∣|G|) : ⁅P, N_G(P)⁆ ≠ ⊥`。

**body 骨格** (`scn3_isUniquelyMaximal`, `by_contra hAnot`):
```
-- setup
have hAcomm_set : ∀ x∈A,∀ y∈A, x*y=y*x := fun x hx y hy =>
  congrArg Subtype.val (isMulCommutative_iff.mp (isMulCommutative_of_mem_scn3Global hA) ⟨x,hx⟩ ⟨y,hy⟩)
have hAp := isPGroup_of_mem_scn3Global hA;  have hAne := ne_bot_of_mem_scn3Global hA
have hp_dvd : p ∣ Nat.card G := ... (hAp.exists_card_eq + hAne → p∣|A|; card_subgroup_dvd_card)
obtain ⟨PG, hAPG, hSCN⟩ := S07.exists_sylow_of_mem_scn3Global hA   -- PG : Sylow p G
set P : Subgroup G := (PG:Subgroup G)
have hPp : IsPGroup p P := PG.isPGroup'
have hPnormA : P ≤ Subgroup.normalizer (A:Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hAPG).mp hSCN.1.normal  -- ⚠ normalizer Set/Subgroup coercion 注意
have hAP : A ≤ P := hAPG
set P0 : Subgroup G := ⁅P, Subgroup.normalizer (P:Set G)⁆
have hP0_le_P : P0 ≤ P := ... (⁅P,N_G(P)⁆≤P: P⊴N_G(P); `Subgroup.commutator_le`? or normal)
have hP0p : IsPGroup p ↥P0 := hPp.to_le hP0_le_P  -- IsPGroup of subgroup
have hP0N : P0 ≤ derivedInG (Subgroup.normalizer (P:Set G)) := by
  rw [derivedInG_eq_commutator]; exact Subgroup.commutator_mono Subgroup.le_normalizer le_rfl
have hP0ne : P0 ≠ ⊥ := commutator_normalizer_ne_bot_of_isSylow hG PG hp_dvd
-- key (9.6→9.12): ∀ M'∈𝓜(C_G(A)), IsUniquelyMaximal(N_G(P0)) ∧ N_G(P0)≤M'
have key : ∀ M', M' ∈ maximalSubgroupsContaining (Subgroup.centralizer (A:Set G)) →
    IsUniquelyMaximal (Subgroup.normalizer (P0:Set G)) ∧ Subgroup.normalizer (P0:Set G)≤M' := by
  intro M' hM'
  have hNPM' := (normalizer_scn3_pSubgroup_le_maximal_of_not_scn3 hG hM' hA hAnot hPp hAP hPnormA).2
  by_cases h3D : 3 ≤ rank ↥(opiCoreInG ({p}:Set ℕ)ᶜ (S08.fittingInG M'))
  · exact normalizer_p0_isUniquelyMaximal_and_le_maximal_of_high_rank_package
      hG hAcomm_set hM' hA hAnot hPp hAP hPnormA hNPM' hP0p hP0N hP0ne h3D
  · have hP0M' : P0 ≤ M' := hP0_le_P.trans (hPnormA.trans ... )  -- P≤N_G(A)≤M' via hNPM'? いや P≤M': P≤N_G(P)≤M' (hNPM'); P0≤P
    have hMN0 : M' ≤ Subgroup.normalizer (P0:Set G) := <SUB-ASSEMBLY 2: Frattini 低rank>
    exact (fun h => ⟨h.1, le_of_eq h.2⟩)
      (normalizer_isUniquelyMaximal_and_eq_maximal_of_maximal_le_normalizer hG hM'.1 hP0M' hP0ne hMN0)
obtain ⟨M, hM⟩ := exists_maximalSubgroupsContaining_centralizer_of_mem_scn3Global hG hA
obtain ⟨hUniq, hN0M⟩ := key M hM
-- 最終矛盾: Ω₁(A)∉𝒰 → Thm 9.1 contrapositive → x∈Ω₁(A)^# with C_G(x)⊄M → M*∈𝓜(C_G(x))⊆𝓜(C_G(A)), M*≠M
set W := omega1OfAbelian G A p hAcomm_set
have hWnot : ¬ IsUniquelyMaximal W := not_isUniquelyMaximal_of_le_scn3_counterexample hG hAcomm_set hA (omega1OfAbelian_le ...) hAnot
have hWea := omega1OfAbelian_isElementaryAbelian (hH := hAcomm_set)
have hWnc := not_isCyclic_omega1OfAbelian_of_three_le_pRank ...  -- needs 3≤pRank A p
have hWleM : W ≤ M := (omega1OfAbelian_le).trans (A≤C_G(A)≤M = hM.2 via hA_le_C)
have hncase := mt (noncyclic_isUniquelyMaximal_of_centralizer_le hG hM.1 hWea hWleM hWnc) hWnot  -- ¬hcase
-- ¬hcase → ¬first → ∃ x∈W, x≠1, ¬(C_G({x})≤M)
push_neg at hncase / rcases not_or ... → obtain ⟨x, hxW, hx1, hxnotM⟩
have hCxlt : Subgroup.centralizer ({x}:Set G) < ⊤ := ...  (x≠1, minimal simple)
obtain ⟨Mstar, hMstar⟩ := <∃ maximal containing C_G({x})>  -- exists_maximalSubgroupsContaining? or coatom
have hMstarA : Mstar ∈ 𝓜(C_G(A)) := maximalSubgroupsContaining_centralizer_of_mem_centralizer_singleton (x∈A: hxW→W≤A) hMstar
have hne : Mstar ≠ M := fun h => hxnotM (h ▸ hMstar.2)   -- C_G({x})≤Mstar=M contra
obtain ⟨_, hN0Mstar⟩ := key Mstar hMstarA
exact hne (hUniq.eq_of_isCoatom_of_le (mem_maximalSubgroups.mp hMstar.1) hN0Mstar (mem_maximalSubgroups.mp hM.1) hN0M).symm
   -- ⚠ eq_of_isCoatom_of_le (h)(hM:Coatom)(hHM:H≤M)(hN:Coatom)(hHN:H≤N) : M=N
```

**要解決 hook 詳細**:
- `Subgroup.normal_subgroupOf_iff_le_normalizer (h:H≤K) : (H.subgroupOf K).Normal ↔ K≤normalizer H` (mathlib Basic:412)。
  `Subgroup.normalizer` の Set/Subgroup coercion が §9 の `Subgroup.normalizer (A:Set G)` と合うか要確認 (合わなければ `by simpa`/`Subgroup.le_normalizer` 経由)。
- `⁅P, N_G(P)⁆ ≤ P` (P⊴N_G(P)): mathlib `Subgroup.commutator_le_...` か normal 経由。
- `IsPGroup.to_le`/部分群版: `IsPGroup p P → P0≤P → IsPGroup p ↥P0` (`IsPGroup.to_subgroup`/`.of_le` 要確認)。
- `∃ M*∈𝓜(C_G({x}))`: C_G({x})<⊤ から maximal を取る (`exists_maximalSubgroupsContaining`? なければ coatom 存在 `IsCoatom` via Zorn/Finite)。`omega1OfAbelian_le : W≤A`。`not_isCyclic_omega1OfAbelian_of_three_le_pRank` は `3≤pRank A p` (= `three_le_rank` + `three_le_pRank_of_isPGroup_of_three_le_rank`) 要。
- **SUB-ASSEMBLY 2 (Frattini 低rank `M'≤N_G(P0)`, BG L2617)**: `M'=O_{p'}(F(M'))·N_{M'}(P)`。Thm 4.20a (`derived_le_fitting_of_rank_fitting_le_two`, 私の新補題; 低rank ⟹ rank F(M')≤2 full) で M''≤F(M'); M'/M'' abelian で FP⊴M'; Frattini (`Sylow.normalizer_sup_eq_top'` 系) で M'=FP·N_{M'}(P); F=O_p(F)·O_{p'}(F), O_p(F)≤P ⟹ M'=O_{p'}(F)·N_{M'}(P); (9.11) で O_{p'}(F)≤C_G(P0)≤N_G(P0), N_{M'}(P)≤N_G(P)≤N_G(P0) (P0⊴N_G(P)) ⟹ M'≤N_G(P0)。**~50-70 行・最重・要 Fitting nilpotent decomposition + Frattini**。これが Phase B の本丸残件。

---

## (旧) Phase A propagation 手順 — 記録 (完了済)

### Phase A: package 仮説の撤去を鎖全体へ伝播

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
