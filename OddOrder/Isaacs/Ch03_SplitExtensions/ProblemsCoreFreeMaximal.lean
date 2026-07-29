/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Isaacs.Ch03_SplitExtensions.ProblemsMinimalNormal

/-!
# Isaacs Problem 3C.5 (書籍 p. 91) — 核が自明な極大部分群

Isaacs, *Finite Group Theory* (AMS GSM 92, 2008), Problem 3C.5 の形式化
(campaign issue 1055)。

**3C.5**: `H` が有限可解群 `G` の極大部分群で `core_G(H) = 1` とする。このとき `G` は
一意の極小正規部分群 `M` をもち, `H` は `M` の補元で `M = C_G(M)`。さらに `K` も核自明な
極大部分群なら `H` と `K` は `G` で共役。

## 証明

`M` を任意の極小正規部分群とする (有限非自明群に存在)。`G` 可解なので `M` は可換
(Thm 3.11 前半 `solvable_minimal_normal_isAbelian`)。

* **`M ⊔ H = ⊤`**: `M ⊴ G` かつ `M ≠ ⊥` なので `M ≤ H` なら `M ≤ core_G(H) = ⊥` で矛盾。
  ゆえに `H < M ⊔ H` で, `H` の極大性から `M ⊔ H = ⊤`。
* **`M` は `H` の補元**: `M ⊓ H` は `H` に正規化され, `M` 可換ゆえ `M` にも中心化される。
  `M ⊔ H = ⊤` だから `M ⊓ H ⊴ G` (`normal_of_sup_eq_top`), よって
  `M ⊓ H ≤ core_G(H) = ⊥`。
* **`C_G(M) = M`**: `C := C_G(M)` は `M ⊴ G` より正規で `M ≤ C` (`M` 可換)。
  `C ⊓ H` も同じ論法で `G`-正規 (`C` の元は `M` の元と可換) ゆえ `⊥`。部分群束の
  modular 律 (`sup_inf_assoc_of_le`) から `C = (M ⊔ H) ⊓ C = M ⊔ (C ⊓ H) = M`。
* **一意性**: `N` を別の極小正規部分群とすると `N ⊓ M` は `M` の中の正規部分群で,
  `N ⊓ M = M` なら `M ≤ N` から `N` の極小性で `N = M`。よって `N ⊓ M = ⊥`,
  すると `⁅N, M⁆ ≤ N ⊓ M = ⊥` で `N ≤ C_G(M) = M`, ゆえに `N = N ⊓ M = ⊥` で矛盾。
* **共役性**: `K` も核自明な極大部分群なら, 一意性から同じ `M` について `K` も `M` の補元。
  Problem 3C.4 (`isComplement'_conj_of_isMinimalNormal_centralizer_eq`) で `H` と `K` は共役。

## Main results

- `normal_of_sup_eq_top` — `M ⊔ H = ⊤` で `M` に中心化され `H` に正規化される部分群は `G`-正規。
- `exists_isMinimalNormal_isComplement'_of_isCoatom_normalCore_eq_bot` —
  **Problem 3C.5 前半** (極小正規 `M` の存在・一意性 + 補元 + 自己中心化)。
- `existsUnique_isMinimalNormal_of_isCoatom_normalCore_eq_bot` — 極小正規部分群の一意性。
- `conj_of_isCoatom_normalCore_eq_bot` — **Problem 3C.5 後半** (核自明な極大部分群は共役)。
-/

namespace OddOrder.Isaacs.Ch03

open Subgroup Pointwise

section /- 3C: Problem 3C.5 (p. 91) -/

variable {G : Type*} [Group G]

/-- `M ⊔ H = ⊤` のとき, `M` の各元に中心化され `H` に正規化される部分群 `X` は `G` で正規。

`M` は正規なので `G = MH` (集合積) であり, `g = mh` に対して
`g x g⁻¹ = m (h x h⁻¹) m⁻¹ = h x h⁻¹ ∈ X`。

3C.5 では `X = M ⊓ H` (`M` 可換) と `X = C_G(M) ⊓ H` (`C_G(M)` の元は `M` と可換) の
2 か所で使う。 -/
theorem normal_of_sup_eq_top {M H X : Subgroup G} [M.Normal] (hsup : M ⊔ H = ⊤)
    (hMX : ∀ m ∈ M, ∀ x ∈ X, m * x * m⁻¹ = x)
    (hHX : ∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) : X.Normal := by
  constructor
  intro x hx g
  have hg : g ∈ (M : Set G) * (H : Set G) := by
    rw [← Subgroup.normal_mul M H, hsup]
    exact Subgroup.mem_top g
  obtain ⟨m, hm, h, hh, hmh⟩ := hg
  have hmh' : m * h = g := hmh
  subst hmh'
  have hkey : m * h * x * (m * h)⁻¹ = m * (h * x * h⁻¹) * m⁻¹ := by group
  rw [hkey, hMX m hm _ (hHX h hh x hx)]
  exact hHX h hh x hx

variable [Finite G]

/-- **Isaacs Problem 3C.5, 前半** (書籍 p. 91)。`H` が有限可解群 `G` の極大部分群で
`core_G(H) = 1` なら, `G` は極小正規部分群 `M` を**ただ一つ**もち, `H` は `M` の補元で
`M = C_G(M)`。 -/
theorem exists_isMinimalNormal_isComplement'_of_isCoatom_normalCore_eq_bot [IsSolvable G]
    {H : Subgroup G} (hH : IsCoatom H) (hcore : H.normalCore = ⊥) :
    ∃ M : Subgroup G, Ch02.IsMinimalNormal M ∧ Subgroup.IsComplement' M H ∧
      Subgroup.centralizer (M : Set G) = M ∧
      ∀ N : Subgroup G, Ch02.IsMinimalNormal N → N = M := by
  -- `G` は非自明 (自明なら `H = ⊤` で極大性に矛盾)
  haveI hGnt : Nontrivial G := by
    rcases subsingleton_or_nontrivial G with _ | hn
    · refine absurd (le_antisymm le_top fun x _ => ?_) hH.1
      rw [Subsingleton.elim x 1]
      exact H.one_mem
    · exact hn
  have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    intro h
    exact hx (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top x))
  -- 極小正規部分群 `M` を取り, 可解性から可換 (Thm 3.11 前半)
  obtain ⟨M, hmin, -⟩ := Ch02.exists_isMinimalNormal_le_of_normal (⊤ : Subgroup G) htop_ne_bot
  haveI := hmin.1
  have habel : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := solvable_minimal_normal_isAbelian hmin
  -- `M ≰ H` (さもなくば `M ≤ core_G(H) = ⊥`)
  have hMnotle : ¬ M ≤ H := fun hle =>
    hmin.2.1 (le_bot_iff.mp (hcore ▸ Subgroup.normal_le_normalCore.mpr hle))
  -- `H` の極大性から `M ⊔ H = ⊤`
  have hsup : M ⊔ H = ⊤ := by
    refine hH.2 _ (lt_of_le_of_ne le_sup_right fun heq => hMnotle ?_)
    exact le_sup_left.trans heq.ge
  -- `M ⊓ H` は `G`-正規 (`M` 可換 + `H` が正規化) ゆえ `core_G(H) = ⊥` に落ちる
  have hMHbot : M ⊓ H = ⊥ := by
    haveI : (M ⊓ H).Normal := by
      refine normal_of_sup_eq_top hsup (fun m hm x hx => ?_) (fun h hh x hx => ?_)
      · calc m * x * m⁻¹ = x * m * m⁻¹ := by rw [habel m hm x hx.1]
          _ = x := by group
      · exact ⟨hmin.1.conj_mem x hx.1 h, H.mul_mem (H.mul_mem hh hx.2) (H.inv_mem hh)⟩
    exact le_bot_iff.mp (hcore ▸ Subgroup.normal_le_normalCore.mpr inf_le_right)
  have hcompl : Subgroup.IsComplement' M H := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hMHbot)
    rw [← Subgroup.normal_mul M H, hsup, Subgroup.coe_top]
  -- `C := C_G(M)` は正規で `M ≤ C`
  haveI hCnormal : (Subgroup.centralizer (M : Set G)).Normal := Subgroup.normal_centralizer
  have hMC : M ≤ Subgroup.centralizer (M : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => habel y hy x hx
  -- `C ⊓ H` も同じ論法で `G`-正規 ゆえ `⊥`
  have hCHbot : Subgroup.centralizer (M : Set G) ⊓ H = ⊥ := by
    haveI : (Subgroup.centralizer (M : Set G) ⊓ H).Normal := by
      refine normal_of_sup_eq_top hsup (fun m hm x hx => ?_) (fun h hh x hx => ?_)
      · have hxm : m * x = x * m := Subgroup.mem_centralizer_iff.mp hx.1 m hm
        calc m * x * m⁻¹ = x * m * m⁻¹ := by rw [hxm]
          _ = x := by group
      · exact ⟨hCnormal.conj_mem x hx.1 h, H.mul_mem (H.mul_mem hh hx.2) (H.inv_mem hh)⟩
    exact le_bot_iff.mp (hcore ▸ Subgroup.normal_le_normalCore.mpr inf_le_right)
  -- Dedekind: `c ∈ C` を `c = m h` (`m ∈ M ≤ C`, `h ∈ H`) と書くと `h = m⁻¹c ∈ C ⊓ H = ⊥`
  have hcent : Subgroup.centralizer (M : Set G) = M := by
    refine le_antisymm (fun c hc => ?_) hMC
    have hg : c ∈ (M : Set G) * (H : Set G) := by
      rw [← Subgroup.normal_mul M H, hsup]
      exact Subgroup.mem_top c
    obtain ⟨m, hm, h, hh, hmh⟩ := hg
    have hmh' : m * h = c := hmh
    have hhC : h ∈ Subgroup.centralizer (M : Set G) := by
      have hhe : h = m⁻¹ * c := by rw [← hmh']; group
      rw [hhe]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hMC hm)) hc
    have hhbot : h ∈ (⊥ : Subgroup G) := hCHbot ▸ Subgroup.mem_inf.mpr ⟨hhC, hh⟩
    rw [Subgroup.mem_bot] at hhbot
    rw [← hmh', hhbot, mul_one]
    exact hm
  refine ⟨M, hmin, hcompl, hcent, fun N hN => ?_⟩
  -- 一意性: `N ⊓ M = ⊥` から `⁅N, M⁆ = ⊥`, つまり `N ≤ C_G(M) = M`, ゆえに `N = ⊥` で矛盾
  haveI := hN.1
  by_contra hne
  have hNM : N ⊓ M = ⊥ := by
    rcases hmin.2.2 (N ⊓ M) inferInstance inf_le_right with h | h
    · exact h
    · exact absurd ((hN.2.2 M inferInstance (inf_eq_right.mp h)).resolve_left hmin.2.1).symm hne
  have hNcent : N ≤ Subgroup.centralizer (M : Set G) := by
    intro n hn
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 : n * m * n⁻¹ * m⁻¹ ∈ M := M.mul_mem (hmin.1.conj_mem m hm n) (M.inv_mem hm)
    have h2 : n * m * n⁻¹ * m⁻¹ ∈ N := by
      have hcon : m * n⁻¹ * m⁻¹ ∈ N := hN.1.conj_mem n⁻¹ (N.inv_mem hn) m
      have h3 : n * (m * n⁻¹ * m⁻¹) ∈ N := N.mul_mem hn hcon
      simpa [mul_assoc] using h3
    have h4 : n * m * n⁻¹ * m⁻¹ ∈ N ⊓ M := ⟨h2, h1⟩
    rw [hNM, Subgroup.mem_bot] at h4
    have hnm : n * m = m * n := by
      calc n * m = (n * m * n⁻¹ * m⁻¹) * (m * n) := by group
        _ = m * n := by rw [h4, one_mul]
    exact hnm.symm
  exact hN.2.1 (le_bot_iff.mp (hNM ▸ le_inf le_rfl (hcent ▸ hNcent)))

/-- **Isaacs Problem 3C.5** (書籍 p. 91)。核が自明な極大部分群をもつ有限可解群は
極小正規部分群を**ただ一つ**もつ。 -/
theorem existsUnique_isMinimalNormal_of_isCoatom_normalCore_eq_bot [IsSolvable G]
    {H : Subgroup G} (hH : IsCoatom H) (hcore : H.normalCore = ⊥) :
    ∃! M : Subgroup G, Ch02.IsMinimalNormal M := by
  obtain ⟨M, hmin, -, -, huniq⟩ :=
    exists_isMinimalNormal_isComplement'_of_isCoatom_normalCore_eq_bot hH hcore
  exact ⟨M, hmin, huniq⟩

/-- **Isaacs Problem 3C.5, 後半** (書籍 p. 91)。`H`, `K` がともに有限可解群 `G` の
核自明な極大部分群なら, `H` と `K` は `G` で共役。

一意性から両者は**同じ**極小正規部分群 `M` の補元であり, `M = C_G(M)` なので
Problem 3C.4 の補元共役性が使える。 -/
theorem conj_of_isCoatom_normalCore_eq_bot [IsSolvable G] {H K : Subgroup G}
    (hH : IsCoatom H) (hHcore : H.normalCore = ⊥)
    (hK : IsCoatom K) (hKcore : K.normalCore = ⊥) :
    ∃ g : G, H.map (MulAut.conj g).toMonoidHom = K := by
  obtain ⟨M, hmin, hcomplH, hcent, -⟩ :=
    exists_isMinimalNormal_isComplement'_of_isCoatom_normalCore_eq_bot hH hHcore
  obtain ⟨M', -, hcomplK, -, huniq'⟩ :=
    exists_isMinimalNormal_isComplement'_of_isCoatom_normalCore_eq_bot hK hKcore
  have hcomplK' : Subgroup.IsComplement' M K := by
    rw [huniq' M hmin]; exact hcomplK
  exact isComplement'_conj_of_isMinimalNormal_centralizer_eq hmin hcent hcomplH hcomplK'

end -- Problem 3C.5

end OddOrder.Isaacs.Ch03
