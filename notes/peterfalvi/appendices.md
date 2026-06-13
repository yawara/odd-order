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

### 残 TODO (Appendix B)
- [ ] **part (1)-(2) reduction** = Lemma の sorry。⚠ **mmd p.136 が MISSING_PAGE** (06.0 の (2) 結論欠落)
      → PDF 画像読みで復元要 ([[nougat-missing-page-recovery]])。part (1) 分解ケースは復元済テキストで可。
- [ ] **Prop 1** = transitive ⟹ 定 stabilizer ⟹ 各 Sylow に Lemma 適用 ⟹ F(D) 構造。
- [ ] file が sorry-free 化したら keystone 2 本を AxiomsCheck の **新 Appendices section** に登録
      (LAUNCH rule #4; 現状は file に 2 sorry 残ゆえ未登録)。

## 3. 攻略順 (LAUNCH 準拠)
B → (C/D 並行) → E → A (最難・最後)。各々 opaque→faithful 化 + citeable 部の完全証明。
C/D/E は citeable shortcut 無 ⟹ faithful-statement + 精密 gap 局所化が現実的着地点。
**司令塔への flag**: appendices は off-critical-path (Part II)。FT 本線進展ではない旨ユーザー認識済。
