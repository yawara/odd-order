/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddOrder.Peterfalvi.S06_DadeIsometryCertain
import OddOrder.Peterfalvi.S05_TICyclic
import OddOrder.GroupTheory.ConjClassSet

/-!
# Peterfalvi Hypothesis (4.6): the certain-type Dade configuration in an ambient `G`

**Peterfalvi**, _Character Theory for the Odd Order Theorem_ (LMS LNS 272, 2000), §4, pp. 21-24.

Hypothesis (4.6) is the running hypothesis for Theorems (4.7)-(4.9) and for the §8 coherence
capstone (6.8)(c2).  It layers, on top of the certain-type structure (4.2) for `L` and the §4 Dade
datum on `A` (`CertainTypeHypothesis`):

* **(4.6.b)** the TI-cyclic Hypothesis (3.1) for the *ambient* group `G` (so the σ-isometry lands in
  `Irr(G)`, not just `Irr(L)`), with `W₁, W₂` matching the certain-type `W₁, W₂ ≤ ↥L` via `L ↪ G`;
* **(4.6.c)** a normal subgroup `H ⊴ L` with `W₂ ⊆ H ⊆ K`;
* **(4.6.d)** the covering `⋃_{h∈H^#} C_K(h)^# ⊆ A`, the enlarged set `A₀ = A ∪ V^L`, and the §4 Dade
  datum on `A₀`;
* **(4.6.e)** the Dade isometry `τ` relative to `A₀` (`FullDadeIsometryData`).

The Dade data (`dade`, `dade0`, `tau`) are *assumed* here as fields; their construction (combining
the `K`-local and `V`-TI Dade maps) is the responsibility of the instantiator (the §8 (6.8)
application).
-/

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- **Peterfalvi Hypothesis (4.6).**  See the module docstring.  Extends the certain-type Dade
hypothesis `CertainTypeHypothesis A L` (= (4.2) for `↥L` + §4 Dade on `A`) with the ambient TI-cyclic
data (3.1), the normal subgroup `H` with `W₂ ⊆ H ⊆ K`, the covering condition on `A`, and the Dade
isometry `τ` relative to `A₀ = A ∪ V^L`. -/
structure Hypothesis46 (A : Set G) (L : Subgroup G) [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    extends CertainTypeHypothesis A L where
  /-- (4.6.b): the ambient TI-cyclic Hypothesis (3.1) for `(G, W)`. -/
  tic : OddOrder.Peterfalvi.S05.TICyclicHypothesis G
  /-- `W₁` of (3.1) is the image of the certain-type `W₁ ≤ ↥L` under `L ↪ G`. -/
  tic_W1 : tic.W1 = (toCertainTypeHypothesis.W1).map L.subtype
  /-- `W₂` of (3.1) is the image of the certain-type `W₂ ≤ ↥L` under `L ↪ G`. -/
  tic_W2 : tic.W2 = (toCertainTypeHypothesis.W2).map L.subtype
  /-- (4.6.b): the TI-subset `V` of the ambient Hypothesis (3.1) is `W − (W₁ ∪ W₂)` (viewed in `G`
  via `L ↪ G`) — the (3.1) exceptional set (Coq `cyclicTIset`).  Note this is *smaller* than the
  (4.3.a) `L`-side TI-subset `W − W₂`: only `W − (W₁ ∪ W₂)` is TI in the ambient `G` (in the §8/§10
  instantiations the `W₁^#`-elements have centralizers reaching outside `N_G(A)`, cf. (8.10)/(8.15)
  where `A₀(M) = A(M) ∪ V^M` with this `V`; issue 9004). -/
  tic_V : tic.V = (↑tic.W : Set G) \ ((↑tic.W1 : Set G) ∪ (↑tic.W2 : Set G))
  /-- (4.6.c): a normal subgroup `H ⊴ L`. -/
  subH : Subgroup ↥L
  subH_normal : subH.Normal
  /-- (4.6.c): `W₂ ⊆ H`. -/
  W2_le_subH : toCertainTypeHypothesis.W2 ≤ subH
  /-- (4.6.c): `H ⊆ K`. -/
  subH_le_K : subH ≤ toCertainTypeHypothesis.K
  /-- (4.6.d): every nontrivial element of every `C_K(h)` (`h ∈ H^#`) lies in `A`
  (the covering `⋃_{h∈H^#} C_K(h)^# ⊆ A`). -/
  A_covers : ∀ (hh : ↥L), hh ∈ subH → hh ≠ 1 →
    ∀ (x : ↥L), x ∈ Subgroup.centralizer ({hh} : Set ↥L) ⊓ toCertainTypeHypothesis.K →
      x ≠ 1 → (L.subtype x) ∈ A
  /-- (4.6.d): the §4 Dade datum on the enlarged set `A₀ = A ∪ V^L`, where
  `V^L = conjClassSetIn L tic.V` is the set of `L`-conjugates of the TI-subset `V` of (3.1)
  (Coq `class_support`; the same closure the (8.10) `typePA0` uses, so the §10 instantiation
  aligns definitionally). -/
  dade0 : OddOrder.Peterfalvi.S04.Hypothesis G
    (A ∪ OddOrder.GroupTheory.conjClassSetIn L tic.V) L
  /-- (4.6.e): the Dade isometry `τ` relative to `A₀`. -/
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) dade0

end OddOrder.Peterfalvi.S06
