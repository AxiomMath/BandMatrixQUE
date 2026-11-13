module

public import BlockBand.Native.PSSS.BlockBand.External.PSSS.Proof.Wegner
public import BlockBand.Native.PSSS.BlockBand.Analysis.PSSSPoissonAveraging

/-!
# Sharp one-block Poisson averaging from the proved single-block DOS bound

This module supplies the analytic estimate needed after conditioning the
exterior blocks in the multiblock Wegner proof.  It works directly with the
public normalized law `GUE_N(1/N)`: every deterministic Hermitian background
has expected Poisson trace at most `π C N` whenever `SingleBlockDOS C` holds.
No factorial-moment input is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section

namespace PSSSNative.BlockBand.PSSS

open Matrix MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexOrder

/-- Expected unnormalised spectral measure of one public normalized GUE block
with deterministic Hermitian deformation. -/
def publicGUEExpectedSpectralMeasure {N : ℕ}
    (A : HermitianMatrix (Fin N)) : Measure ℝ :=
  ∑ i : Fin (Fintype.card (Fin N)),
    (PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
      Measure (HermitianMatrix (Fin N))).map
      (fun V => orderedEigenvalue (addHermitian A V) i)

/-- Integration against the public expected spectral measure equals expectation
of the finite ordered-eigenvalue sum. -/
theorem lintegral_publicGUEExpectedSpectralMeasure {N : ℕ}
    (A : HermitianMatrix (Fin N)) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂publicGUEExpectedSpectralMeasure A) =
      ∫⁻ V, ∑ i : Fin (Fintype.card (Fin N)),
        f (orderedEigenvalue (addHermitian A V) i)
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N))) := by
  rw [publicGUEExpectedSpectralMeasure, lintegral_finsetSum_measure]
  have heig (i : Fin (Fintype.card (Fin N))) :
      Measurable (fun V : HermitianMatrix (Fin N) =>
        orderedEigenvalue (addHermitian A V) i) :=
    (measurable_orderedEigenvalue i).comp (measurable_addHermitian A)
  simp_rw [lintegral_map hf (heig _)]
  rw [lintegral_finsetSum]
  intro i _hi
  exact hf.comp (heig i)

/-- On a Borel set the public expected spectral measure is exactly the expected
multiplicity-counted spectral count. -/
theorem publicGUEExpectedSpectralMeasure_apply {N : ℕ}
    (A : HermitianMatrix (Fin N)) (s : Set ℝ) (hs : MeasurableSet s) :
    publicGUEExpectedSpectralMeasure A s =
      ∫⁻ V, (eigenCount (addHermitian A V) s : ℝ≥0∞)
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N))) := by
  rw [← lintegral_indicator_one hs]
  change (∫⁻ x, s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) x
      ∂publicGUEExpectedSpectralMeasure A) = _
  rw [lintegral_publicGUEExpectedSpectralMeasure A
    (s.indicator (fun _ : ℝ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hs)]
  apply lintegral_congr
  intro V
  rw [eigenCount_def]
  simp [Set.indicator, Finset.sum_boole]

/-- `SingleBlockDOS C` is precisely the closed-interval domination of the
public expected spectral measure, with unchanged constant and normalization. -/
theorem publicGUEExpectedSpectralMeasure_Icc_le_of_singleBlockDOS {C : ℝ}
    (h : SingleBlockDOS C) {N : ℕ} (hN : 0 < N)
    (A : HermitianMatrix (Fin N)) (a b : ℝ) (hab : a ≤ b) :
    publicGUEExpectedSpectralMeasure A (Set.Icc a b) ≤
      ENNReal.ofReal (C * N * (b - a)) := by
  rw [publicGUEExpectedSpectralMeasure_apply A _ measurableSet_Icc]
  exact h N hN A a b hab

/-- **Sharp conditioned one-block Poisson estimate.**  For every deterministic
Hermitian deformation, energy and positive regulator, the public
`GUE_N(1/N)` expected unnormalised Poisson trace is at most `π C N`.
This is the exact analytic estimate used for each real Schur–Cauchy
background after the exterior blocks have been fixed. -/
theorem lintegral_publicGUE_orderedPoisson_le_of_singleBlockDOS {C : ℝ}
    (hC : 1 ≤ C) (h : SingleBlockDOS C) {N : ℕ} (hN : 0 < N)
    (A : HermitianMatrix (Fin N)) (e : ℝ) {eta : ℝ} (heta : 0 < eta) :
    (∫⁻ V, ENNReal.ofReal
      (∑ i : Fin (Fintype.card (Fin N)),
        centeredPoissonKernel e eta
          (orderedEigenvalue (addHermitian A V) i))
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) ≤
      ENNReal.ofReal (Real.pi * C * N) := by
  let nu := publicGUEExpectedSpectralMeasure A
  let K : ℝ := C * N
  have hK : 0 ≤ K := mul_nonneg (le_trans (by norm_num) hC) (Nat.cast_nonneg N)
  have hIcc : ∀ r : ℝ, 0 ≤ r →
      nu (Set.Icc (e - r) (e + r)) ≤ ENNReal.ofReal (2 * K * r) := by
    intro r hr
    have hb := publicGUEExpectedSpectralMeasure_Icc_le_of_singleBlockDOS
      h hN A (e - r) (e + r) (by linarith)
    simpa only [nu, K] using (show
      ENNReal.ofReal (C * (N : ℝ) * (e + r - (e - r))) =
        ENNReal.ofReal (2 * (C * (N : ℝ)) * r) by
      congr 1
      ring) ▸ hb
  let _ : IsFiniteMeasure nu := by
    unfold nu publicGUEExpectedSpectralMeasure
    infer_instance
  have hkernel := lintegral_centeredPoissonKernel_le_of_Icc
    nu e eta K heta hK hIcc
  have hmeas : Measurable
      (fun x => ENNReal.ofReal (centeredPoissonKernel e eta x)) := by
    unfold centeredPoissonKernel
    fun_prop
  have hspectral := lintegral_publicGUEExpectedSpectralMeasure A
    (fun x => ENNReal.ofReal (centeredPoissonKernel e eta x)) hmeas
  calc
    (∫⁻ V, ENNReal.ofReal
      (∑ i : Fin (Fintype.card (Fin N)), centeredPoissonKernel e eta
        (orderedEigenvalue (addHermitian A V) i))
      ∂(PSSSNative.BlockBand.GUE N (1 / (N : ℝ)) :
        Measure (HermitianMatrix (Fin N)))) =
        ∫⁻ x, ENNReal.ofReal (centeredPoissonKernel e eta x) ∂nu := by
      rw [show (fun V : HermitianMatrix (Fin N) => ENNReal.ofReal
          (∑ i : Fin (Fintype.card (Fin N)), centeredPoissonKernel e eta
            (orderedEigenvalue (addHermitian A V) i))) =
          (fun V => ∑ i : Fin (Fintype.card (Fin N)),
            ENNReal.ofReal (centeredPoissonKernel e eta
              (orderedEigenvalue (addHermitian A V) i))) by
        funext V
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro i _hi
        exact centeredPoissonKernel_nonneg heta]
      exact hspectral.symm
    _ ≤ ENNReal.ofReal (Real.pi * K) := hkernel
    _ = ENNReal.ofReal (Real.pi * C * N) := by
      congr 1
      dsimp [K]
      ring

end PSSSNative.BlockBand.PSSS
