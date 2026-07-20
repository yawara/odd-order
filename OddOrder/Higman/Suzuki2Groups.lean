/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.GroupTheory.SpecificGroups.Suzuki2Group.Basic
import OddOrder.Higman.Suzuki2Groups.AgemoLayers
import OddOrder.Higman.Suzuki2Groups.HigmanAbelian
import OddOrder.Higman.Suzuki2Groups.HigmanNormalAbelian
import OddOrder.Higman.Suzuki2Groups.HigmanNormalCover
import OddOrder.Higman.Suzuki2Groups.HigmanFrattiniConsequences
import OddOrder.Higman.Suzuki2Groups.HigmanEndomorphismLift
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotents
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentAction
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentFamily
import OddOrder.Higman.Suzuki2Groups.HigmanIdempotentCovariance
import OddOrder.Higman.Suzuki2Groups.HigmanKernel
import OddOrder.Higman.Suzuki2Groups.HigmanImageOrder
import OddOrder.Higman.Suzuki2Groups.HigmanFinalCase
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralGraded
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralSpectrum
import OddOrder.Higman.Suzuki2Groups.HigmanSquareMap
import OddOrder.Higman.Suzuki2Groups.HigmanLowerCentralDegreeThree
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaSix
import OddOrder.Higman.Suzuki2Groups.HigmanTripleBracketContradiction
import OddOrder.Higman.Suzuki2Groups.HigmanCoverAbelian
import OddOrder.Higman.Suzuki2Groups.HigmanCoverPowerOverlap
import OddOrder.Higman.Suzuki2Groups.HigmanCoverDerivedSeries
import OddOrder.Higman.Suzuki2Groups.HigmanMaximalNormalAbelian
import OddOrder.Higman.Suzuki2Groups.HigmanFiniteFieldTrace
import OddOrder.Higman.Suzuki2Groups.HigmanXiLengthTwo
import OddOrder.Higman.Suzuki2Groups.HigmanLemmaEleven
import OddOrder.Higman.Suzuki2Groups.CenterInvolutions
import OddOrder.Higman.Suzuki2Groups.CenterHomocyclic

/-!
# Higman: Suzuki 2-groups

Graham Higman, “Suzuki 2-groups,” *Illinois Journal of Mathematics* 7 (1963),
79--96.

This module contains the proof from Higman’s original paper. Peterfalvi,
Appendix III, restates the resulting classification theorem but explicitly
takes its proof from Higman; Peterfalvi-specific restatement and application
data remain under `OddOrder.Peterfalvi.Appendices.Suzuki2Groups`.

Source-neutral definitions and reusable group/representation APIs live under
`OddOrder.GroupTheory` or `OddOrder.Algebra`; paper-specific Lemmas 1--13 and
the classification argument live here.
-/
