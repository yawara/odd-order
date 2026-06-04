# 引き継ぎ (→ codex): BG §8 Theorem 8.1 (The Fitting Subgroup of a Maximal Subgroup)

> 作成 2026-06-04 (Claude/Opus, §6→§7 close-out 直後)。**§6→§7 は 100% 完了済**
> (Lem 6.5/6.6 + Cor 1.12 + Thm 6.7 + §7 Prop 7.5 case1, §7 完全 sorry-free)。
> 次 spine step = **§8 Thm 8.1**。本ノートは codex が §8 を着手するための自己完結 brief。
> live 全体像 = memory `ft-master-roadmap` + `notes/bg/s08_fitting_max.md` (詳細 mini-roadmap)。

## 0. タスク

`OddOrder/BG/Ch2_Uniqueness/S08_FittingOfMaximal.lean` の **残り 1 sorry を埋める** (§8 唯一の結果 Thm 8.1):
- **(a)** `cFitting_isUniquelyMaximal_of_not_pGroup` (completed 2026-06-04; sorry-free and AxiomsCheck-registered): `M∈ℳ`, `p∈π(F(M))`,
  `A₀∈ℰ*_p(F(M))` (`isMaxElemAbelianIn`), `m(A₀)≥3`, `F(M)` が p-群でない ⟹ `C_{F(M)}(A₀)∈𝒰`。
- **remaining (b)** `sylow_isSylow_and_scn3_isUniquelyMaximal_of_pGroup` (L97-106, sorry @L106): 同仮定で `F(M)` が
  p-群 ⟹ `M` の Sylow p `P` は `G` の Sylow p、かつ `SCN₃(P)` の各元 ⊆ `F(M)` ∧ ∈ `𝒰`。

statement は faithful・変更不可 (`isMaxElemAbelianIn` 述語 + accessor は既存)。mmd 出典 = `references/bg/local-analysis.mmd` **L2315-2485** (§8 全文。proof (a)=L2326-2438, proof (b)=L2440-2482)。
**規模 = §6→§7 連鎖全体に匹敵する大型単一定理** (mini-roadmap 評価「高・3-4 週」)。内部式 (8.1)-(8.13) を helper 群に分解して攻める。

## 1. ⚠️ 最重要 subtlety: Thm 6.2 は Puig L(S) 形のみ

BG §8 proof (b) は **「Z(J(P)) ⊴ M」(Thm 6.2)** を 3 箇所 (mmd L2456/L2478/L2482) で使うが、repo に **Z(J) 一般形は無い**。あるのは:
- **`OddOrder.BG.AppB.zCenter_lOdd_sup_oPiCore_normal`** (AppB_Thm62.lean:22) = **Thm 6.2 一般形だが Puig `L(S)` 版** `Z(L(S))·O_{p'}(G) ⊴ G`。
- S06 `normalJ_normal_of_odd` は Z(J) だが **reduced case** (`O_{p'}=⊥` ∧ `P=C_G(Z(P))`) — §8 では使えない。

**方針**: §8 part (b) は **L(S) 形で論証を適応**せよ (`Z(J(P))` → `Z(L(P))`)。理由・依存閉包・ゲート (A.4(b)+A.4(c)) は **`notes/meta/bg_s6_appAB_route_2026_05_28.md`** に集約済 (J→L 大域置換の検証込み)。
`zCenter_lOdd_sup_oPiCore_normal` の正確な statement / `L(S)` 定義 (`lOddIn` 等) を AppB_Thm62.lean で確認してから part (b) を設計すること。**N_G(Z(L(P)))=M を回す論法は Z(J) と同型** (L(S) も characteristic in S ⟹ ⊴ M ⟹ N_G ⊇ M)。

## 2. 利用可能な依存 (EXACT 名、全て build 済・大半 axiom-clean)

### §7 transitivity (本セッション以前+本セッションで全完成)
| BG | Lean 名 (ns `OddOrder.BG.Ch2.S07`) | 用途 (§8) |
|---|---|---|
| Thm 7.2 | `transitive_of_three_le_rank_center` (Hyp71, q∈π', m(Z(A))≥3 ⟹ K 推移的) | (a) (8.6): ℋ*(A;q) 単元化 |
| Thm 7.4 | `transitivity_propagates` | (a): ℋ*(F;q)⊆ℋ*(A;q) (下記出力形) |
| Thm 7.6 | `thompsonTransitivity` (A∈SCN₃(p), q∈p' ⟹ O_{p'}(C_G(A)) 推移的) | (b) (8.12) |
| Hyp 7.1 | `Hypothesis71` (structure: ne_bot/proper/generated_eq) + `hypothesis71_of_scn2` | (a): A=C_F(A₀) で verify |

**Thm 7.4 出力形** (重要、(a) (8.6) で使う):
```
transitivity_propagates (hG) (hA : Hypothesis71 A) (hq : q∈(primesOf A)ᶜ) (P) (hPproper : P<⊤)
  (hPpi : IsPiSubgroup (primesOf A) P) (hAP : A≤P) (hAsub : IsSubnormal (A.subgroupOf P))
  (htrans : ConjTransitiveOn (kSubgroup A) (hInvariantStar ⊤ A {q})) :
  (C_G(P)⊓kSubgroup A = opiCoreInG (primesOf A)ᶜ C_G(P)) ∧
  ConjTransitiveOn (opiCoreInG (primesOf A)ᶜ C_G(P)) (hInvariantStar ⊤ P {q}) ∧
  hInvariantStar ⊤ P {q} ⊆ hInvariantStar ⊤ A {q} ∧ (∀ Q∈ℋ*(P;q), ...(d)...)
```
ℋ_G*(A;q) = `hInvariantStar ⊤ A {q}`; ℋ_G(A;q) = `hInvariant ⊤ A {q}` (`mem_hInvariant`: `Q≤⊤ ∧ A≤N(Q) ∧ IsPiSubgroup {q} Q`)。`kSubgroup A` = O_{π'}(C_G(A))。`ConjTransitiveOn`/`primesOf`/`opiCoreInG`/`kSubgroup` は S07 + `GroupTheory/{AInvariantPiSubgroups,SubgroupInAmbient}.lean`。

### §6 (本セッション完成分も含む)
| BG | Lean 名 | ns |
|---|---|---|
| Thm 6.1 (一般形, A abelian normal in Syl ⟹ A⊆O_{p',p}) | `thmA4b` (AppA_PStability.lean:1915; `(hp_odd)(hsolv)(hodd)...`) | `OddOrder.BG.AppA` (要確認) |
| Thm 6.2 (一般形, **L(S)版**) | `zCenter_lOdd_sup_oPiCore_normal` | `OddOrder.BG.AppB` |
| Lem 6.5(a)(b)(c) | `inf_commutator_eq_of_coprime`/`normalizer_eq_centralizerK_mul_normalizerU`/`exists_mem_centralizerK_mul_of_conj_le` | `OddOrder.BG.Ch1.S06` |
| Lem 6.6 (5 定理) | `oPiPrimePiCore_eq_oPiPrimeCore_sup_sylow` 他 | `S06` (§8 では不要・§10 で必要) |
| Thm 6.7 | `le_oPiPrimeCore_of_normalized_by_maximalElementaryAbelian` | `S06` (§8 では不要) |

### §1 prelim
| BG | Lean 名 (ns `OddOrder.BG.Ch1.S01` 等) | 用途 |
|---|---|---|
| Prop 1.3 | `centralizer_fitting_le_fitting` (C_G(F(G))⊆F(G), solvable) | (a)(b): C_M(F)⊆F |
| Prop 1.6(a) | `OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top` (G=C_G(A)⊔[G,A]) | (a) (8.4): Y=C_Y(A_q)[Y,A_q] |
| Prop 1.10 | `coprime_nilpotent_acts_trivially_of_centralizer_self` (S01:1770) | (a)(b): C_F(C)⊆C ⟹ x∈C_M(F) |
| Prop 1.15(b) | `oPiPrimeCore_centralizer_le_oPiPrimeCore` (S01:2568) | (a) (8.5): A_r⊆O_{q'}(C_X(Z(F)_q))⊆O_{q'}(X) |
| Cor 1.12 | `corollary_1_12` (S01, 本セッション完成) | (汎用 coprime, 必要なら) |

### setup / 群論 infra
- `IsMinimalSimpleOdd` (Setup.lean): `.odd/.simple/.notSolvable/.solvable_of_lt_top/.nontrivial`。固定 G を各定理に thread。
- `maximalSubgroups G` / `mem_maximalSubgroups` (= IsCoatom) / `IsUniquelyMaximal` (=𝒰) / `maximalSubgroupsContaining` — `GroupTheory/{MaximalSubgroup,MaximalSubgroupType}.lean`。
- `fittingInG M = (Ch01.fitting ↥M).map M.subtype` + `fittingInG_le` (S08 既存)。`Ch01.fitting` = Isaacs Fitting。
- `IsSCN₃` / `IsSCN_n` / `rank` / `pRank` — `GroupTheory/{SCN,PRank}.lean`。

## 3. 先に作るべき gap helper (§8 本体の前に)

1. **単純性 fact `N_G(L)=M`** (mmd L2317「L⊴M 非自明 ⟹ N_G(L)=M」, §8 全体で多用): repo に既存無し。新 helper:
   ```
   theorem normalizer_eq_of_normal_of_mem_maximal (hG : IsMinimalSimpleOdd G)
     {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {L : Subgroup G}
     (hLM : (L.subgroupOf M).Normal) (hLne : L ≠ ⊥) (hLleM : L ≤ M) :
     Subgroup.normalizer (L:Set G) = M
   ```
   pf: `M ≤ N_G(L)` (L⊴M); `N_G(L)≠⊤` (=⊤なら L⊴G, simple+L≠⊥⟹L=⊤, but L≤M<⊤ 矛盾);
   N_G(L) proper ⊇ M maximal (IsCoatom) ⟹ N_G(L)=M。(`normalizer (Set G)` 規約注意 = §6 罠参照)。
   **S08 冒頭の private helper 推奨** (S12 に `maximal_eq_normalizer_of_M_normalizes` 系の類似があるので参照可)。

2. **Prop 1.4** (mmd で「Prop 1.4」: A_p が `F(O_{p'}(H))=O_{p'}(D)` を中心化 ⟹ A_p が `O_{p'}(H)` を中心化): repo に named 形が**見当たらない** (grep 空)。**Prop 1.3 (`centralizer_fitting_le_fitting`) + coprime action** から導出見込み (N=O_{p'}(H) p'-群、A_p は p-元で N に coprime 作用、F(N) 中心化 ⟹ C_N(A_p)⊇F(N)⊇C_N(C_N(A_p))... Prop 1.10 流)。**まず S01/Ch04 を grep で再確認**、無ければ自前補題化 (中規模)。これは (a) (8.7-8.8) と (b) で使う。

3. **fittingInG の O_q 分解 / Z(F) / π(F)**: `K_q=O_q(K)` (K nilpotent), `Z(F)`, `π(F)=primeFactors|F|` の ambient-G API。`F(M)` は `↥M` の Fitting を map したものなので、`O_q(F(M))`/`Z(F(M))` を G 内でどう書くか (subgroupOf/map 往復) を最初に固めると後段が楽。nilpotent ⟹ `F = ∏ O_q(F)` (direct product of Sylows) の形も要 (mmd「F nilpotent ⟹ A⊴⊴F」「A_r⊆F_r」)。

## 4. 証明分解 (mini-roadmap §「証明構造」+ mmd 準拠)

**part (a)** (F not p-群, π=π(F), A=C_F(A₀)):
- (8.1) `Z(F)⊆A⊆F` ⟹ π(A)=π。 (8.2) `C_G(A)⊆N_G(Z(F)_q)=M` (各 q∈π; 単純性 fact)。
- (8.3) `C_G(A)` は π-群 (π'-元 x: (8.2)で x∈M, C_F(C_F(x))⊆A⊆C_F(x), Prop 1.10+1.3 ⟹ x∈C_M(F)⊆F, π'⟹x=1)。
- (8.4) A-不変 π'-群 Y: `C_Y(A_q)=1` (∵[C_Y(A_q),A]⊆Y∩F=1 + (8.3)) ⟹ Prop 1.6(a) で `Y=[Y,A_q]`。
- (8.5) `A_r⊆O_{q'}(C_X(Z(F)_q))⊆O_{q'}(X)` (Prop 1.15(b); r≠q∈π, |π|≥2)。⟹ Y=[Y,A_r]⊆O_{q'}(X) 全 q ⟹ Y⊆O_{π'}(X) = **Hyp 7.1 verify**。
- (8.6) Thm 7.2 (m(Z(A))≥m(A₀)≥3) + (8.3) (O_{π'}(C_G(A))=1) ⟹ ℋ*(A;q)={Q}; Thm 7.4 ⟹ ℋ*(F;q)⊆{Q}; Q⊴M⊆F, q∈π' ⟹ Q=1 ⟹ ℋ*(A;q)={1} 全 q∈π'。
- H∈ℳ(A): D=F(H), σ=π(D)⊆π (8.6から)。σ=π を示し、(8.7) Sylow 整合 ⟹ D⊆M、O_{p'}(H)=O_{p'}(M) ⟹ H=N_G(O_{p'}(M))=M ⟹ A∈𝒰。

**part (b)** (F=p-群 ⟹ F=O_p(M), O_{p'}(M)=1; A∈SCN₃(P)):
- (8.9) Thm 6.1 (`thmA4b`) で A⊆F; Z(F)⊆C_P(A)=A; C_G(A)⊆N_G(Z(F))=M。**Thm 6.2 (L(S)形)** で Z(L(P))⊴M ⟹ N_G(P)⊆N_G(Z(L(P)))=M ⟹ **P は G の Sylow p** ∧ A∈SCN₃(p)。
- (8.10)(8.11) A*=O_{p'}(C_G(A))⊆M, C_F(C_F(A*))⊆A⊆C_F(A*), Prop1.10+1.3 ⟹ A*⊆C_M(F)⊆F, F p-群 ⟹ A*=1。
- (8.12) q∈p', Thm 7.6 + (8.11) ⟹ ℋ*(A;q)={Q}, F normalizes Q, Q⊴M, Q⊆O_q(M)=1 ⟹ ℋ(A;p')={1} (Y∈ℋ(A;p') ⟹ F(Y)=1 ⟹ Y=1 solvable)。
- A∉𝒰 と仮定 ⟹ H∈ℳ(A), H≠M で |H∩M|_p 最大。R=Syl_p(H∩M)⊇A。|R|<|P| なら N_M(R) で増大 ⟹ R は Syl_p(H)。**Thm 6.2 (L(S))** で (8.13) O_{p'}(H)=1 ∧ Z(L(R))⊴H ⟹ N_G(R)⊆N_G(Z(L(R)))=H ⟹ R は Syl_p(G)・Syl_p(M)。(8.9)+(8.13)+Thm 6.2 で M=N_G(Z(L(R)))=H 矛盾。

各 (8.x) を private helper に切り出すこと (anti-scaffold: 仮説に hoist せず本体で閉じる)。

## 5. codex 運用規約 (CLAUDE.md 準拠)

- **worktree 推奨**: `git worktree` で `/home/ywr/odd-order-bg-s08` (branch `bg-s08`), `.lake/packages`+`references` は main から symlink 共有 (手順 = `notes/meta/worktree_setup.md`)。`lake update` は worktree で走らせない。合流は main へ `--no-ff` merge。
- **issue 採番**: worktree では `export ODD_ISSUE_BASE=2000` (並行レンジ)。main では 0057(8.1a) は closed, 0058(8.1b) を open tracker として使用。
- **anti-scaffold gate** (memory `scaffold-sorry-free-not-done`): statement は faithful 固定 (extra 仮説で hard content を hoist しない)。各 helper は完全証明 (no sorry, no 仮説=結論)。
- **完了判定**: `lake build OddOrder` green + `#print axioms <thm>` = `[propext, Classical.choice, Quot.sound]` (sorryAx 無) + `OddOrder/AxiomsCheck.lean` に `#assert_only_allowed_axioms` 登録。本セッションの §6→§7 登録例 (L1137-1159 付近) を踏襲。
- **commit 粒度**: feature/subsection 単位 (Thm 8.1(a) + helper 群で 1 commit, (b) で 1 commit 等)。message 末尾に `Co-Authored-By: ...`。
- **build**: `lake build OddOrder.BG.Ch2_Uniqueness.S08_FittingOfMaximal` (leaf, ~30-60s) で iterate、最後に full `lake build OddOrder`。
- **mmd 参照**: PDF 直読でなく `references/bg/local-analysis.mmd` を grep/Read (L2315-2485)。

## 6. Lean 罠 (本セッション §6→§7 で記録、§8 でも有効)

- `Subgroup.normalizer` は **Set G を取る** → `normalizer (L:Set G)` 明示。`< ⊤`/inf 位置で coercion 失敗時 `SetLike.coe`/型 ascription。
- 共役作用 `↥A →* MulAut ↥H` = `H.normalizerMonoidHom.comp (Subgroup.inclusion (hA:A≤normalizer H))` (S01 `mem_centralizer_opCore_...` L2350 が precedent)。
- `IsCoherent`/Type-値述語は `noncomputable def`、enum は `choose`。
- **Unicode 識別子回避**: `ḡ` 等 extended-Latin を束縛変数にすると lexer 誤認 → 誤誘導 parse error (Cor 1.12 で踏んだ)。ASCII を使う。
- `omit [Finite G] in` は **docstring の前**。set-型レベル変数は rw せず defeq (`have ... : ...NQ... := term`)。
- subgroupOf↔map subtype 往復: `Subgroup.map_subgroupOf_eq_of_le (h:Y≤X)`/`subgroupOf_map_subtype`/`subgroupOfEquivOfLe`/`comap_map_eq_self_of_injective`。
- E*_p 系: BG の「ℰ*_p = 包含極大」は `OddOrder.GroupTheory.IsMaximalElementaryAbelian` (max-order の `maxElemAbelianIn` と別物)。S08 の `isMaxElemAbelianIn` は §8 専用述語 (F(M) 内包含極大)。

## 7. 参照
- mmd: `references/bg/local-analysis.mmd` L2315-2485 (§8)。
- `notes/bg/s08_fitting_max.md` (詳細 mini-roadmap: (8.1)-(8.13) 全式、Thm 6.2 引用 3 箇所の精密文脈)。
- `notes/meta/bg_s6_appAB_route_2026_05_28.md` (**Thm 6.2 = L(S) 形を使う理由・ゲート**, part (b) 必読)。
- `notes/bg/s06_67_chain_design.md` (本セッション §6→§7 設計、§7 API 規約)。
- memory `ft-master-roadmap` (全体現在地)。issue 0058 (§8(b) tracker; 0057 is closed)。
- 次 (§8 後) = §9 Uniqueness Thm 9.1/9.6 (Thm 8.1 を r(F(H))≤2 で使用, mmd L2533)。
