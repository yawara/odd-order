# Peterfalvi Appendices A–E — Lane H 計画 + AUDIT

> Lane H = worktree `pf-s10` / branch `pf-s10` / issue base **2000** / model Opus 4.8 (1M)。
> §10–13 が BG §14/§15 (Lane F/G) に gate されて STANDBY の間、LAUNCH.md の指示で
> BG spine とも character API とも独立な **Peterfalvi Appendices** を形式化する。

## 0. AUDIT 結論 (session 1, 2026-06-14)

5 ファイル (`OddOrder/Peterfalvi/Appendices/{Huppert,NearFields,Suzuki2Groups,FeitSibley,Suzuki}.lean`)
は **すべて opaque-`Prop` scaffold** (`foo : Prop` + `foo_holds : foo`、結論は `∃ data, data.foo ∧ …`
で rider が vacuous)。LAUNCH の「難度低め・今すぐ実証明できる」は**楽観**で、実体は全 appendix が
**研究級の古典定理**に bottom-out する:

- **B (Huppert)**: 可解 2-重可移群の Huppert 分類の特殊版。Lemma は **Huppert V.8.15 (FPF p-群 ⟹ cyclic)**
  + Huppert III.7.5 + Schur (F_q 上) に依存。
- **C (NearFields)**: 有限 near-field の Zassenhaus 分類。
- **D (Suzuki2Groups)**: Higman の Suzuki 2-群分類。
- **E (FeitSibley)**: Feit–Sibley coherence (S07 coherence API 依存 = Lane B 領域)。
- **A (Suzuki)**: 最難 (PSU₃(q) 特徴付け)。後回し。

これらは **FT 最短経路外** (Peterfalvi Part II = Suzuki 特徴付け; FT 定理本体は Part I + BG §7-16)。
⟹ off-critical-path の self-contained 群論。空 scaffold 量産はしない ([[scaffold-sorry-free-not-done]])。
**正攻法 = opaque を faithful 型に置換し、citeable な上流があるものは完全証明、無いものは gap を
精密に局所化** (scaffold_opaque_prop_convention.md の cleanup path)。

## 1. ⭐ 唯一の citeable shortcut: BG Prop 3.9 (Appendix B 用)

`OddOrder.BG.Ch3.S12.isCyclic_of_coprime_fpf_pgroup_action`
([S12_Theorem1212.lean:55](../../OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1212.lean)) =
**Huppert V.8.15 = Gorenstein 5.3.14**: 有限 p-群 R (p odd) が非自明 H に coprime かつ FPF 作用 ⟹
`IsCyclic R`。**proved・axiom-clean** (AxiomsCheck:4115)。Appendix B Lemma の核 (FPF⟹cyclic) を cite 可。
他の appendix には同等の citeable 上流が repo に**無い**。

## 2. Appendix B de-opaque 進捗 (session 1)

`Huppert.lean` を opaque scaffold → **faithful 型**に全面書換 (build-green, sorry 2→2 不変)。

**完全証明 (0 sorry, axiom-clean = propext/choice/Quot のみ; #print axioms で確認):**
- `smul_eq_of_sq_smul_eq_of_odd_orderOf` — part (1) の「奇位数元は 2 点を入れ替えられない」
  (`g²•a=a ∧ Odd(orderOf g) ⟹ g•a=a`; `exists_pow_eq_self_of_coprime` で `⟨g⟩=⟨g²⟩`)。
- `isCyclic_of_faithful_fpf_pgroup_on_elementaryAbelian` — **Lemma の cyclic 結論**。
  ⚠ thin wrapper ではない: **coprimality `q ≠ p` を FPF から導出** (q=p なら p-群 P が非自明
  p-群 E に作用 ⟹ `card_modEq_card_fixedPoints` で非零共通不動点 ⟹ FPF と矛盾) してから Prop 3.9 を cite。

**faithful statement + 局所化 sorry (×2):**
- `pGroup_cyclic_fixedPointFree` (Lemma) — sorry = **part (1)-(2) reduction** (定 point-stabilizer
  位数 ⟹ FPF; Clifford 分解 `E=⊕Eᵢ` + 既約ケース via Schur)。cyclic は keystone を cite 済。
- `fitting_cyclic_fixedPointFree` (Prop 1) — sorry = F(D) 構造 (F(D) cyclic ∧ FPF ∧ `commutator D ≤ F(D)`)。

`pointStabilizer φ a := (stabilizer (MulAut E) a).comap φ` (faithful な `P_a`)。

### session 2 (2026-06-14): p.136 復元 + Prop 1 bridge

**✅ mmd p.136 MISSING_PAGE 復元** (PDF 画像読み, [[nougat-missing-page-recovery]]):
- **Lemma part (2) 末尾**: P 既約・非 cyclic 仮定 → R⊴P type-(p,p), Schur で End(E)=有限体 → Z(P) cyclic →
  |R∩Z(P)|=p, P は R の他の位数 p 部分群 {T_i} を置換, `C_E(R∩Z(P))=0`, `E_i:=C_E(T_i)`,
  `E=⊕E_i` (直和は帰納法; t∈T_k は E_i=C_E(T_i) を中心化 → R=⟨T_k,T_i⟩ 中心化 → x_i=0) を P が置換
  → part (1) で P cyclic, 矛盾。
- **Prop 1 証明**: 各奇素数 p で `P=O_p(F)⊴D`, D transitive on E^# → `P_a,P_b` は D-共役 (∵ d·a=b, P正規) →
  定 stabilizer → Lemma で O_p(F) cyclic+FPF。`F=∏_p O_p(F)` → F cyclic+FPF。`C_D(F)=F`
  (Feit-Thompson+Fitting [H]III.4.2, D 可解) → `D/F ↪ Aut(F)` cyclic ゆえ abelian。

**✅ bridge lemma landed** (complete, axiom-clean): `card_pointStabilizer_comp_eq_of_normal_of_transitive`
= Prop 1 の「P_a,P_b 共役」step (N⊴D + transitive ⟹ N-stabilizer 位数一定; 共役 `N_b=dN_ad⁻¹` を
conjugation Equiv で). sorry 不変 (2→2)。

### 残 TODO (Appendix B)
- [ ] **part (1) imprimitive case** (`E=⊕Eᵢ` r≥2 を P が置換 + 定 stabilizer ⟹ FPF): swap補題(済)+
      `P_{a+b}=P_a∩P_b`(直和一意性) で実証明可。⚠ vector-space/DirectSum setup (E を F_q-加群 via
      `IsElementaryAbelian.zmodModule`, 部分空間の P-置換) が要 = 中規模。
- [ ] **part (2) irreducible case**: Schur over F_q (`IsSimpleModule.End`=division ring) + type-(p,p)
      (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`) + `E=⊕C_E(T_i)` → part(1)。
- [ ] **Prop 1 残**: bridge は済。残 = `F=∏O_p`(nilpotent 分解) + O_p cyclic⟹F cyclic + `C_D(F)=F`
      (D 可解; repo に `Ch01` Fitting API 在) + `D/F↪Aut(F)`。各々中規模。
- [ ] file が sorry-free 化したら keystone+bridge を AxiomsCheck の **新 Appendices section** に登録
      (LAUNCH rule #4; 現状 file に 2 sorry 残ゆえ未登録; 完成済 3 本は #print axioms で clean 確認済)。

## 3. 攻略順 (LAUNCH 準拠)
B → (C/D 並行) → E → A (最難・最後)。各々 opaque→faithful 化 + citeable 部の完全証明。
C/D/E は citeable shortcut 無 ⟹ faithful-statement + 精密 gap 局所化が現実的着地点。
**司令塔への flag**: appendices は off-critical-path (Part II)。FT 本線進展ではない旨ユーザー認識済。
