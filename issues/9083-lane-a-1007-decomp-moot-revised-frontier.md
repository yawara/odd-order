
## 再訂正 (同日 survey #2): coherent_Sset_diff_SHCSet も DEAD — claim 差し替え

precision survey の断定:
- **coherent_Sset_diff_SHCSet は dead** — call site 0 (def + docstring 2 件のみ)、
  consumer 連鎖は「coherent_Sset_of_glued (未適用)」→「coherent_Sset_of_column_identities
  (未定義の幻)」、AxiomsCheck 不在、**issue 1019 で deprecated** (wide route は
  non-Galois type III/IV で false → narrow 𝒮(H₀C) route に置換済)。port 不実施。
- (9.11) の book 原文 = full family 𝒮(H₀C′) coherent; 「difference」は (11.8.6) での
  isCoherent_of_subset + (11.7) H₀=1 collapse という応用に過ぎない。

## 改訂² frontier claim (lane a): honest (9.11) Ptype_core_coherence induction

- **対象**: `sibleyTarget_H0C` (S11_MaximalII_III_IV/Coherence911.lean:48) の置換 —
  **7001 監査で UNSOUND と開示済みの「do NOT fill」sorry** ((6.8) SibleyTarget の
  TI 仮説が nilpotent-Hall kernel HC で false)。live 参照あり
  (coherent_H0C_commutator :63 → S15 HypothesisBasics:422/435)。
- **本物の新規 math** = Coq PFsection9.v:1484-1571 の (9.11.1)–(9.11.8)
  maximal-subfamily refutation を、landed 済の S07 skeleton
  (exists_maximal_coherent_between :648 / coherent_of_maximal_coherent_pair_refuted)
  + S13 base cases (sOf_degreeSubfamily_isCoherent :588 /
  coherent_sOf_H0Cprime_of_allReducible :409) の上に組む。
- **境界注意**: S07 skeleton は b の carve-out 産 (family-agnostic infra、追加変更
  なしで消費のみ) — §9/§11 family での assembly は S13-側 consumer work = a 領域。
- **hub へ 2 点**: (i) この claim の重複チェック (S11/Coherence911 の所有)。
  (ii) liveness trace 依頼: coherent_H0C track (S15 tau1S_ofHonest 系) が S16
  非存在証明に現に配線されているか (survey は未確認と報告 — S16 は
  S07.irrSubcoherent + Rdatum 経由の別 route を使用中の模様)。配線されていなくても
  UNSOUND stand-in の置換は正当 (unsound scaffold は STOP-級の問題対象) だが、
  wiring の実態は §15/§16 側 (b/c) の設計に影響する。
