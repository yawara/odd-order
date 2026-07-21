/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
import OddOrder.Peterfalvi.Appendices.Suzuki.Basic
import OddOrder.Peterfalvi.Appendices.Suzuki.InvolutionClass
import OddOrder.Peterfalvi.Appendices.Suzuki.CanonicalForm
import OddOrder.Peterfalvi.Appendices.Suzuki.DistinguishedInvolution
import OddOrder.Peterfalvi.Appendices.Suzuki.InvertedProduct
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerStructure
import OddOrder.Peterfalvi.Appendices.Suzuki.FixedPointCentralizer
import OddOrder.Peterfalvi.Appendices.Suzuki.QStructure
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowDecomposition
import OddOrder.Peterfalvi.Appendices.Suzuki.KCyclic
import OddOrder.Peterfalvi.Appendices.Suzuki.SylowTwo
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualKActor
import OddOrder.Peterfalvi.Appendices.Suzuki.ActualCenter
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearModel
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearIdentification
import OddOrder.Peterfalvi.Appendices.Suzuki.SemidirectReassociation
import OddOrder.Peterfalvi.Appendices.Suzuki.SemilinearRealization
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesis
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisPSL
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisSuzuki
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionHypothesisPSU
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInduction
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerNormalizer
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerResidual
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerQuotient
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerInductionBridge
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerDistinguishedBridge
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSLRoot
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSLDistinguished
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerSuzukiRoot
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerSuzukiDistinguished
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSURoot
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerPSUDistinguished
import OddOrder.Peterfalvi.Appendices.Suzuki.CentralizerTrichotomy
import OddOrder.Peterfalvi.Appendices.Suzuki.InductionNonSimple
import OddOrder.Peterfalvi.Appendices.Suzuki.ConjugacyInV
import OddOrder.Peterfalvi.Appendices.Suzuki.StronglyReal
import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreePSL
import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreePSLInduction
import OddOrder.Peterfalvi.Appendices.Suzuki.OrderThreeSuzukiCentralizer
import OddOrder.Peterfalvi.Appendices.Suzuki.TypeBFromW
import OddOrder.Peterfalvi.Appendices.Suzuki.WCyclicDivides
import OddOrder.Peterfalvi.Appendices.Suzuki.FirstCase.Basic

/-!
# Peterfalvi Part II: A Theorem of Suzuki (hub)

Pure re-export hub for the Part II formalization (pp. 97–134): the
topic leaves live in `OddOrder/Peterfalvi/Appendices/Suzuki/`.
-/
