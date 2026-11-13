module

public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventObservables
public import BlockBand.Native.CEH.ETH.BlockBand.External.CEH.TwoResolventGaussianIBPReplicatedWardGradient
public import BlockBand.Native.CEH.BlockBand.Published.LocalETHInput
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Deterministic spectral and grid infrastructure for CEH ETH extraction

This module isolates the deterministic part of the extraction of the CEH local
ETH estimate from the two-resolvent law.  It proves the finite spectral decomposition of the
positive two-resolvent observable, continuity of every fixed-observable word,
a grid-to-random-spectral-point event inclusion, and the exact `N^2` ordered
pair union bound.

No two-resolvent law or stochastic estimate is assumed or constructed here.
A probabilistic argument may apply a fixed-point law to the finite grid and
then use the inclusions below.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace CEHNative.BlockBand.External.CEH

open Matrix MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal Matrix.Norms.L2Operator

/-- The positive scalar spectral weight in `Im (H-(x+iη))⁻¹`. -/
def cehSpectralWeight (lambda x eta : ℝ) : ℝ :=
  eta / ((lambda - x) ^ 2 + eta ^ 2)

/-- Rank-one eigenvector projector, without an orthonormality assumption. -/
def spectralProjector {N : ℕ} (u : Fin N → Fin N → ℂ) (i : Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.vecMulVec (u i) (star (u i))

/-- The spectral expansion of the positive imaginary part of a resolvent.
The vectors are columns: `u i a` is coordinate `a` of eigenvector `i`. -/
def spectralImaginaryKernel {N : ℕ} (lam : Fin N → ℝ)
    (u : Fin N → Fin N → ℂ) (x eta : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  ∑ i, (cehSpectralWeight (lam i) x eta : ℂ) • spectralProjector u i

/-- Matrix element of a fixed observable in the supplied eigenfamily. -/
def spectralMatrixElement {N : ℕ} (u : Fin N → Fin N → ℂ)
    (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) : ℂ :=
  (star (u i) ᵥ* A) ⬝ᵥ u j

/-- Positive spectral weights at positive height. -/
theorem cehSpectralWeight_nonneg (lambda x : ℝ) {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ cehSpectralWeight lambda x eta := by
  unfold cehSpectralWeight
  positivity

/-- Spectral weights vary continuously in both energy and positive height. -/
theorem continuous_cehSpectralWeight (lambda : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => cehSpectralWeight lambda p.1 p.2)
      (Set.univ ×ˢ Set.Ioi 0) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  unfold cehSpectralWeight
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · have hp2 : 0 < p.2 := hp.2
    have : 0 < (lambda - p.1) ^ 2 + p.2 ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hp2)
    exact this.ne'

/-- One rank-one summand of the spectral decomposition. -/
theorem trace_spectralProjector_chain {N : ℕ}
    (u : Fin N → Fin N → ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    Matrix.trace (spectralProjector u i * A * spectralProjector u j * Aᴴ) =
      spectralMatrixElement u A i j * star (spectralMatrixElement u A i j) := by
  classical
  rw [spectralProjector, spectralProjector, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.trace_vecMulVec]
  rw [Matrix.smul_vecMul, dotProduct_smul, Matrix.vecMul_conjTranspose]
  simp only [spectralMatrixElement, star_star]
  have hinner :
      (A *ᵥ u j) ⬝ᵥ star (u i) = (star (u i) ᵥ* A) ⬝ᵥ u j := by
    calc
      (A *ᵥ u j) ⬝ᵥ star (u i) =
          star (u i) ⬝ᵥ (A *ᵥ u j) := dotProduct_comm _ _
      _ = (star (u i) ᵥ* A) ⬝ᵥ u j := Matrix.dotProduct_mulVec _ _ _
  rw [Matrix.dotProduct_star, hinner]
  simp

/-- Exact finite spectral decomposition of the positive two-resolvent trace.
The factor is the repository's normalized trace `N⁻¹ Tr`; no probability or
asymptotic estimate occurs in the identity. -/
theorem normalizedTrace_spectralImaginaryKernel_mul
    {N : ℕ} (lam : Fin N → ℝ) (u : Fin N → Fin N → ℂ)
    (x₁ eta₁ x₂ eta₂ : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) :
    NTrace (spectralImaginaryKernel lam u x₁ eta₁ * A *
        spectralImaginaryKernel lam u x₂ eta₂ * Aᴴ) =
      ((N : ℂ)⁻¹) * ∑ i : Fin N, ∑ j : Fin N,
        ((cehSpectralWeight (lam i) x₁ eta₁ *
          cehSpectralWeight (lam j) x₂ eta₂ : ℝ) : ℂ) *
          spectralMatrixElement u A i j * star (spectralMatrixElement u A i j) := by
  classical
  simp only [NTrace, CEHNative.BlockBand.Conventions.normalizedTrace,
    spectralImaginaryKernel, Finset.sum_mul, Matrix.mul_sum,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul,
    trace_spectralProjector_chain]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- A fixed two-resolvent observable is continuous when both resolvent inputs
are continuous.  This is the continuity fact used after choosing a deterministic
spectral grid; it asserts no uniformity in the observable `A`. -/
theorem continuous_twoResolventObservable_fixed
    {N : ℕ} {X : Type*} [TopologicalSpace X]
    (c₁ c₂ : AdjointChoice) (A : Matrix (Fin N) (Fin N) ℂ)
    (G₁ G₂ : X → Matrix (Fin N) (Fin N) ℂ)
    (hG₁ : Continuous G₁) (hG₂ : Continuous G₂) :
    Continuous (fun x => twoResolventObservable c₁ c₂ (G₁ x) A (G₂ x)) := by
  unfold twoResolventObservable twoResolventWord NTrace
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro i _
  exact (continuous_apply_apply i i).comp <| by
    cases c₁ <;> cases c₂ <;> simp only [chooseAdjoint] <;> fun_prop

/-!
## A concrete regular-window grid
-/

/-- The `a`-th point of the closed regular-window grid
`[E₀-R,E₀+R]`, with exactly `meshCount + 1` points.  The endpoints are
included.  This is a deterministic grid: it depends on no matrix sample or
eigenvalue. -/
def localETHRealGridPoint (E₀ R : ℝ) (meshCount : ℕ)
    (a : Fin (meshCount + 1)) : ℝ :=
  E₀ - R + (2 * R / meshCount) * a

/-- The index type of the concrete real grid has exactly `meshCount + 1`
elements. -/
theorem card_localETHRealGridIndex (meshCount : ℕ) :
    Fintype.card (Fin (meshCount + 1)) = meshCount + 1 := by
  simp

/-- Every concrete real-grid point remains in the closed regular window. -/
theorem localETHRealGridPoint_mem_Icc
    {E₀ R : ℝ} {meshCount : ℕ} (hR : 0 ≤ R) (hm : 0 < meshCount)
    (a : Fin (meshCount + 1)) :
    localETHRealGridPoint E₀ R meshCount a ∈ Set.Icc (E₀ - R) (E₀ + R) := by
  have hmR : (0 : ℝ) < meshCount := by exact_mod_cast hm
  have ha : (a : ℕ) ≤ meshCount := by omega
  have haR : (a : ℝ) ≤ meshCount := by exact_mod_cast ha
  unfold localETHRealGridPoint
  constructor
  · have hstep : 0 ≤ 2 * R / (meshCount : ℝ) := div_nonneg (by positivity) hmR.le
    have ha0 : 0 ≤ (a : ℝ) := by positivity
    exact le_add_of_nonneg_right (mul_nonneg hstep ha0)
  · have hmul :
        (2 * R / (meshCount : ℝ)) * (a : ℝ) ≤ 2 * R := by
      calc
        (2 * R / (meshCount : ℝ)) * (a : ℝ) ≤
            (2 * R / (meshCount : ℝ)) * (meshCount : ℝ) := by
          gcongr
        _ = 2 * R := by field_simp [hmR.ne']
    linarith

/-- Every point of the closed regular window is within one mesh step
of a concrete grid point. -/
theorem exists_localETHRealGridPoint_near
    {E₀ R x : ℝ} {meshCount : ℕ} (hR : 0 < R) (hm : 0 < meshCount)
    (hx : x ∈ Set.Icc (E₀ - R) (E₀ + R)) :
    ∃ a : Fin (meshCount + 1),
      |x - localETHRealGridPoint E₀ R meshCount a| ≤
        2 * R / meshCount := by
  let step : ℝ := 2 * R / meshCount
  let t : ℝ := (x - (E₀ - R)) / step
  have hmR : (0 : ℝ) < meshCount := by exact_mod_cast hm
  have hstep : 0 < step := by
    dsimp [step]
    positivity
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr hx.1) hstep.le
  have htM : t ≤ meshCount := by
    dsimp [t, step]
    apply (div_le_iff₀ (by positivity : 0 < 2 * R / (meshCount : ℝ))).2
    calc
      x - (E₀ - R) ≤ 2 * R := by linarith [hx.2]
      _ = (meshCount : ℝ) * (2 * R / (meshCount : ℝ)) := by
        field_simp [hmR.ne']
  let k : ℕ := ⌊t⌋₊
  have hkM : k ≤ meshCount := by
    exact Nat.floor_le_of_le htM
  let a : Fin (meshCount + 1) := ⟨k, by omega⟩
  refine ⟨a, ?_⟩
  have hkt : (k : ℝ) ≤ t := by
    exact Nat.floor_le ht0
  have htk : t < (k : ℝ) + 1 := by
    simpa [k] using Nat.lt_succ_floor t
  have hrepr : x = E₀ - R + step * t := by
    dsimp [t]
    field_simp [hstep.ne']
    ring
  have hgrid :
      localETHRealGridPoint E₀ R meshCount a =
        E₀ - R + step * (k : ℝ) := by
    simp [localETHRealGridPoint, step, a, k]
  rw [hrepr, hgrid]
  have hdiff0 : 0 ≤ step * t - step * (k : ℝ) := by
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left hkt hstep.le)
  rw [abs_of_nonneg (by linarith)]
  dsimp [step]
  have : step * t - step * (k : ℝ) ≤ step := by
    nlinarith
  simpa [step] using this

/-- The exact CEH spectral lift of the concrete real grid.  The imaginary
height is `N^ξ η_f(x)` at the same real grid point `x`; no constant-height
replacement is made. -/
def localETHSpectralGridPoint (N : ℕ) (etaF : ℝ → ℝ) (ξ E₀ R : ℝ)
    (meshCount : ℕ) (a : Fin (meshCount + 1)) : ℂ :=
  CEHNative.BlockBand.localETHSpectralPoint N etaF ξ
    (localETHRealGridPoint E₀ R meshCount a)

/-- Positivity of the CEH spacing function puts every lifted grid point in the
upper half-plane, at the exact height `N^ξ η_f(x)`. -/
theorem localETHSpectralGridPoint_im_pos
    {N meshCount : ℕ} {etaF : ℝ → ℝ} {ξ E₀ R : ℝ}
    (hN : 0 < N) (hetaF : ∀ x, 0 < etaF x)
    (a : Fin (meshCount + 1)) :
    0 < (localETHSpectralGridPoint N etaF ξ E₀ R meshCount a).im := by
  simp only [localETHSpectralGridPoint,
    CEHNative.BlockBand.localETHSpectralPoint]
  simp
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) ξ)
    (hetaF (localETHRealGridPoint E₀ R meshCount a))

/-- The real coordinate of every lifted grid point remains in the source
regular window. -/
theorem localETHSpectralGridPoint_re_mem_Icc
    {N meshCount : ℕ} {etaF : ℝ → ℝ} {ξ E₀ R : ℝ}
    (hR : 0 ≤ R) (hm : 0 < meshCount)
    (a : Fin (meshCount + 1)) :
    (localETHSpectralGridPoint N etaF ξ E₀ R meshCount a).re ∈
      Set.Icc (E₀ - R) (E₀ + R) := by
  simpa [localETHSpectralGridPoint,
    CEHNative.BlockBand.localETHSpectralPoint] using
    localETHRealGridPoint_mem_Icc hR hm a

/-- Exact spectral-point continuity inequality.  If the typical-spacing
function has modulus `L` on the regular window, lifting a real displacement
`d` to the CEH height `N^ξ η_f` costs at most
`(1 + N^ξ L)d`. -/
theorem norm_localETHSpectralPoint_sub_le
    {N : ℕ} {etaF : ℝ → ℝ} {ξ L x y : ℝ}
    (hN : 0 < N)
    (heta : |etaF x - etaF y| ≤ L * |x - y|) :
    ‖CEHNative.BlockBand.localETHSpectralPoint N etaF ξ x -
        CEHNative.BlockBand.localETHSpectralPoint N etaF ξ y‖ ≤
      (1 + (N : ℝ) ^ ξ * L) * |x - y| := by
  rw [show
      CEHNative.BlockBand.localETHSpectralPoint N etaF ξ x -
          CEHNative.BlockBand.localETHSpectralPoint N etaF ξ y =
        ((x - y : ℝ) : ℂ) +
          ((((N : ℝ) ^ ξ * (etaF x - etaF y) : ℝ) : ℂ) * Complex.I) by
    simp [CEHNative.BlockBand.localETHSpectralPoint]
    ring]
  calc
    ‖((x - y : ℝ) : ℂ) +
        ((((N : ℝ) ^ ξ * (etaF x - etaF y) : ℝ) : ℂ) * Complex.I)‖ ≤
      ‖((x - y : ℝ) : ℂ)‖ +
        ‖((((N : ℝ) ^ ξ * (etaF x - etaF y) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_add_le _ _
    _ = |x - y| + (N : ℝ) ^ ξ * |etaF x - etaF y| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs]
      rw [abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) ξ)]
    _ ≤ |x - y| + (N : ℝ) ^ ξ * (L * |x - y|) := by
      gcongr
    _ = (1 + (N : ℝ) ^ ξ * L) * |x - y| := by ring

/-- Concrete coverage of the random CEH spectral points by the deterministic
lifted grid.  The right side displays both the exact real mesh and the exact
height-modulus factor. -/
theorem exists_localETHSpectralGridPoint_near
    {N meshCount : ℕ} {etaF : ℝ → ℝ} {ξ L E₀ R x : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hm : 0 < meshCount) (hL : 0 ≤ L)
    (hx : x ∈ Set.Icc (E₀ - R) (E₀ + R))
    (heta : ∀ y ∈ Set.Icc (E₀ - R) (E₀ + R),
      |etaF x - etaF y| ≤ L * |x - y|) :
    ∃ a : Fin (meshCount + 1),
      ‖CEHNative.BlockBand.localETHSpectralPoint N etaF ξ x -
          localETHSpectralGridPoint N etaF ξ E₀ R meshCount a‖ ≤
        (1 + (N : ℝ) ^ ξ * L) * (2 * R / meshCount) := by
  obtain ⟨a, ha⟩ := exists_localETHRealGridPoint_near hR hm hx
  refine ⟨a, ?_⟩
  apply (norm_localETHSpectralPoint_sub_le hN
    (heta _ (localETHRealGridPoint_mem_Icc hR.le hm a))).trans
  gcongr

/-!
## Explicit resolvent moduli
-/

/-- The CEH resolvent convention `(H-z)⁻¹`. -/
def cehHermitianResolvent {N : ℕ}
    (H : Matrix (Fin N) (Fin N) ℂ) (z : ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (H - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹

/-- The deterministic Hermitian-resolvent norm inequality. -/
theorem norm_cehHermitianResolvent_le
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z : ℂ} (hz : z.im ≠ 0) :
    ‖cehHermitianResolvent H z‖ ≤ |z.im|⁻¹ := by
  exact ReplicatedGUEEuclidean.norm_hermitian_resolvent_l2_opNorm_le H hH hz

/-- First resolvent identity in the CEH convention. -/
theorem cehHermitianResolvent_sub
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    cehHermitianResolvent H z - cehHermitianResolvent H w =
      (z - w) • (cehHermitianResolvent H z * cehHermitianResolvent H w) := by
  unfold cehHermitianResolvent
  rw [Matrix.inv_sub_inv]
  · rw [show H - w • (1 : Matrix (Fin N) (Fin N) ℂ) -
        (H - z • (1 : Matrix (Fin N) (Fin N) ℂ)) =
      (z - w) • (1 : Matrix (Fin N) (Fin N) ℂ) by
        ext i j
        simp
        ring]
    simp
  · constructor
    · intro _
      simpa only [neg_sub] using
        (CEHNative.BlockBand.isUnit_resolventPencil H hH hw).neg
    · intro _
      simpa only [neg_sub] using
        (CEHNative.BlockBand.isUnit_resolventPencil H hH hz).neg

/-- The exact one-resolvent spectral modulus above a common CEH height. -/
theorem norm_cehHermitianResolvent_sub_le
    {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    {z w : ℂ} {eta r : ℝ} (heta : 0 < eta)
    (hz : eta ≤ |z.im|) (hw : eta ≤ |w.im|)
    (hzw : ‖z - w‖ ≤ r) :
    ‖cehHermitianResolvent H z - cehHermitianResolvent H w‖ ≤
      r * eta⁻¹ ^ 2 := by
  have hzne : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz
    linarith
  have hwne : w.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    linarith
  have hiz : |z.im|⁻¹ ≤ eta⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le heta hz
  have hiw : |w.im|⁻¹ ≤ eta⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le heta hw
  have hr : 0 ≤ r := (norm_nonneg (z - w)).trans hzw
  have hGz : ‖cehHermitianResolvent H z‖ ≤ eta⁻¹ :=
    (norm_cehHermitianResolvent_le H hH hzne).trans hiz
  have hGw : ‖cehHermitianResolvent H w‖ ≤ eta⁻¹ :=
    (norm_cehHermitianResolvent_le H hH hwne).trans hiw
  rw [cehHermitianResolvent_sub H hH hzne hwne, norm_smul]
  calc
    ‖z - w‖ * ‖cehHermitianResolvent H z *
        cehHermitianResolvent H w‖ ≤
      ‖z - w‖ * (‖cehHermitianResolvent H z‖ *
        ‖cehHermitianResolvent H w‖) := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ r * (eta⁻¹ * eta⁻¹) := by
      have hetaInv : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
      have hzNorm : 0 ≤ ‖cehHermitianResolvent H z‖ := norm_nonneg _
      have hwNorm : 0 ≤ ‖cehHermitianResolvent H w‖ := norm_nonneg _
      have hprod :
          ‖cehHermitianResolvent H z‖ * ‖cehHermitianResolvent H w‖ ≤
            eta⁻¹ * eta⁻¹ :=
        mul_le_mul hGz hGw hwNorm hetaInv
      exact mul_le_mul hzw hprod (mul_nonneg hzNorm hwNorm) hr
    _ = r * eta⁻¹ ^ 2 := by ring

/-- Every diagonal entry is bounded by the matrix `L²` operator norm. -/
theorem norm_diagonal_entry_le_l2_opNorm {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) :
    ‖M i i‖ ≤ ‖M‖ := by
  let e : EuclideanSpace ℂ (Fin N) := WithLp.toLp 2 (Pi.single i 1)
  let y : EuclideanSpace ℂ (Fin N) :=
    Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M e
  have hcoord : ‖y.ofLp i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop := (Matrix.toEuclideanCLM
    (n := Fin N) (𝕜 := ℂ) M).le_opNorm e
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hyi : y.ofLp i = M i i := by simp [y, e]
  calc
    ‖M i i‖ = ‖y.ofLp i‖ := congrArg norm hyi.symm
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin N) (𝕜 := ℂ) M‖ * ‖e‖ := hop
    _ = ‖M‖ := by rw [Matrix.l2_opNorm_toEuclideanCLM, he, mul_one]

/-- The normalized trace is contractive for the matrix `L²` operator norm.
The factor `N⁻¹` exactly cancels the `N` diagonal summands. -/
theorem norm_NTrace_le_l2_opNorm {N : ℕ} (hN : 0 < N)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖NTrace M‖ ≤ ‖M‖ := by
  unfold NTrace CEHNative.BlockBand.Conventions.normalizedTrace
  change ‖(N : ℂ)⁻¹ * ∑ i : Fin N, M i i‖ ≤ ‖M‖
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  have hentry : ∀ i : Fin N, ‖M i i‖ ≤ ‖M‖ := by
    intro i
    exact norm_diagonal_entry_le_l2_opNorm M i
  have hsum : ‖∑ i : Fin N, M i i‖ ≤ (N : ℝ) * ‖M‖ := by
    calc
      ‖∑ i : Fin N, M i i‖ ≤ ∑ i : Fin N, ‖M i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, ‖M‖ := Finset.sum_le_sum fun i _ => hentry i
      _ = (N : ℝ) * ‖M‖ := by simp
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  calc
    (N : ℝ)⁻¹ * ‖∑ i : Fin N, M i i‖ ≤
        (N : ℝ)⁻¹ * ((N : ℝ) * ‖M‖) := by
      gcongr
    _ = ‖M‖ := by field_simp [hNR]

@[simp] theorem norm_chooseAdjoint {N : ℕ} (c : AdjointChoice)
    (M : Matrix (Fin N) (Fin N) ℂ) :
    ‖chooseAdjoint c M‖ = ‖M‖ := by
  cases c <;> simp [chooseAdjoint, Matrix.l2_opNorm_conjTranspose]

/-- Taking the adjoint does not change the operator-norm displacement. -/
theorem norm_chooseAdjoint_sub_chooseAdjoint {N : ℕ}
    (c : AdjointChoice) (M K : Matrix (Fin N) (Fin N) ℂ) :
    ‖chooseAdjoint c M - chooseAdjoint c K‖ = ‖M - K‖ := by
  cases c
  · simp [chooseAdjoint]
  · simp only [chooseAdjoint]
    rw [show Mᴴ - Kᴴ = (M - K)ᴴ by simp]
    exact Matrix.l2_opNorm_conjTranspose _

/-- Explicit two-resolvent modulus obtained by adding and subtracting one
mixed word.  This lemma is deterministic and uses the exact normalized trace. -/
theorem norm_twoResolventObservable_sub_le
    {N : ℕ} (hN : 0 < N) (c₁ c₂ : AdjointChoice)
    (G₁ K₁ A G₂ K₂ : Matrix (Fin N) (Fin N) ℂ) :
    ‖twoResolventObservable c₁ c₂ G₁ A G₂ -
        twoResolventObservable c₁ c₂ K₁ A K₂‖ ≤
      ‖G₁ - K₁‖ * ‖A‖ * ‖G₂‖ +
        ‖K₁‖ * ‖A‖ * ‖G₂ - K₂‖ := by
  unfold twoResolventObservable
  rw [← NTrace_sub]
  have hsplit :
      twoResolventWord c₁ c₂ G₁ A G₂ -
          twoResolventWord c₁ c₂ K₁ A K₂ =
        (chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁) * A *
            chooseAdjoint c₂ G₂ +
          chooseAdjoint c₁ K₁ * A *
            (chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂) := by
    unfold twoResolventWord
    noncomm_ring
  rw [hsplit]
  apply (norm_NTrace_le_l2_opNorm hN _).trans
  calc
    ‖(chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁) * A *
          chooseAdjoint c₂ G₂ +
        chooseAdjoint c₁ K₁ * A *
          (chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂)‖ ≤
      ‖(chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁) * A *
          chooseAdjoint c₂ G₂‖ +
        ‖chooseAdjoint c₁ K₁ * A *
          (chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂)‖ := norm_add_le _ _
    _ ≤ (‖chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁‖ * ‖A‖) *
          ‖chooseAdjoint c₂ G₂‖ +
        (‖chooseAdjoint c₁ K₁‖ * ‖A‖) *
          ‖chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂‖ := by
      apply add_le_add
      · calc
          ‖(chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁) * A *
              chooseAdjoint c₂ G₂‖ ≤
            ‖(chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁) * A‖ *
              ‖chooseAdjoint c₂ G₂‖ := norm_mul_le _ _
          _ ≤ (‖chooseAdjoint c₁ G₁ - chooseAdjoint c₁ K₁‖ * ‖A‖) *
              ‖chooseAdjoint c₂ G₂‖ := by
            gcongr
            exact norm_mul_le _ _
      · calc
          ‖chooseAdjoint c₁ K₁ * A *
              (chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂)‖ ≤
            ‖chooseAdjoint c₁ K₁ * A‖ *
              ‖chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂‖ := norm_mul_le _ _
          _ ≤ (‖chooseAdjoint c₁ K₁‖ * ‖A‖) *
              ‖chooseAdjoint c₂ G₂ - chooseAdjoint c₂ K₂‖ := by
            gcongr
            exact norm_mul_le _ _
    _ = ‖G₁ - K₁‖ * ‖A‖ * ‖G₂‖ +
        ‖K₁‖ * ‖A‖ * ‖G₂ - K₂‖ := by
      rw [norm_chooseAdjoint_sub_chooseAdjoint,
        norm_chooseAdjoint, norm_chooseAdjoint,
        norm_chooseAdjoint_sub_chooseAdjoint]

/-- Two CEH resolvents above height `eta` have the explicit joint modulus
`2 r eta⁻³ ‖A‖`.  Thus a fixed-grid estimate with this deterministic margin
controls evaluation at random spectral points, with no further modulus hypothesis. -/
theorem norm_twoResolventObservable_cehHermitianResolvent_sub_le
    {N : ℕ} (hN : 0 < N)
    (H : Matrix (Fin N) (Fin N) ℂ) (hH : H.IsHermitian)
    (c₁ c₂ : AdjointChoice) (A : Matrix (Fin N) (Fin N) ℂ)
    {z₁ w₁ z₂ w₂ : ℂ} {eta r : ℝ} (heta : 0 < eta)
    (hz₁ : eta ≤ |z₁.im|) (hw₁ : eta ≤ |w₁.im|)
    (hz₂ : eta ≤ |z₂.im|) (hw₂ : eta ≤ |w₂.im|)
    (hzw₁ : ‖z₁ - w₁‖ ≤ r) (hzw₂ : ‖z₂ - w₂‖ ≤ r) :
    ‖twoResolventObservable c₁ c₂
          (cehHermitianResolvent H z₁) A (cehHermitianResolvent H z₂) -
        twoResolventObservable c₁ c₂
          (cehHermitianResolvent H w₁) A (cehHermitianResolvent H w₂)‖ ≤
      2 * r * eta⁻¹ ^ 3 * ‖A‖ := by
  have hz₂ne : z₂.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hz₂
    linarith
  have hw₁ne : w₁.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw₁
    linarith
  have hinvz₂ : ‖cehHermitianResolvent H z₂‖ ≤ eta⁻¹ :=
    (norm_cehHermitianResolvent_le H hH hz₂ne).trans <| by
      simpa [one_div] using one_div_le_one_div_of_le heta hz₂
  have hinvw₁ : ‖cehHermitianResolvent H w₁‖ ≤ eta⁻¹ :=
    (norm_cehHermitianResolvent_le H hH hw₁ne).trans <| by
      simpa [one_div] using one_div_le_one_div_of_le heta hw₁
  apply (norm_twoResolventObservable_sub_le hN c₁ c₂
    (cehHermitianResolvent H z₁) (cehHermitianResolvent H w₁) A
    (cehHermitianResolvent H z₂) (cehHermitianResolvent H w₂)).trans
  have hdiff₁ := norm_cehHermitianResolvent_sub_le
    H hH heta hz₁ hw₁ hzw₁
  have hdiff₂ := norm_cehHermitianResolvent_sub_le
    H hH heta hz₂ hw₂ hzw₂
  have hr : 0 ≤ r := (norm_nonneg (z₁ - w₁)).trans hzw₁
  calc
    ‖cehHermitianResolvent H z₁ - cehHermitianResolvent H w₁‖ * ‖A‖ *
          ‖cehHermitianResolvent H z₂‖ +
        ‖cehHermitianResolvent H w₁‖ * ‖A‖ *
          ‖cehHermitianResolvent H z₂ - cehHermitianResolvent H w₂‖ ≤
      (r * eta⁻¹ ^ 2) * ‖A‖ * eta⁻¹ +
        eta⁻¹ * ‖A‖ * (r * eta⁻¹ ^ 2) := by
      gcongr
    _ = 2 * r * eta⁻¹ ^ 3 * ‖A‖ := by ring

/-- A modulus formulation convenient for deterministic grids. -/
def HasTwoResolventGridModulus {X : Type*} [PseudoMetricSpace X]
    (f : X → X → ℂ) (omega : ℝ → ℝ) : Prop :=
  ∀ {z₁ z₂ w₁ w₂ : X} {r : ℝ},
    dist z₁ w₁ ≤ r → dist z₂ w₂ ≤ r →
      ‖f z₁ z₂ - f w₁ w₂‖ ≤ omega r

/-- Failure of a fixed two-resolvent estimate at some ordered pair of random
spectral points. -/
def randomSpectralPairBadEvent {Ω X : Type*} [PseudoMetricSpace X]
    {N : ℕ} (f : Ω → X → X → ℂ) (z : Ω → Fin N → X)
    (threshold : Fin N → Fin N → ℝ) : Set Ω :=
  {ω | ∃ i j, threshold i j ≤ ‖f ω (z ω i) (z ω j)‖}

/-- Failure of the same fixed-observable estimate at some point of a finite
ordered grid. -/
def fixedTwoResolventGridBadEvent {Ω X ι : Type*}
    (f : Ω → X → X → ℂ) (grid : ι → X) (threshold : ℝ) : Set Ω :=
  {ω | ∃ a b, threshold ≤ ‖f ω (grid a) (grid b)‖}

/-- Deterministic continuity/grid inclusion.  Each random CEH spectral point
is assigned a nearby deterministic grid point.  A modulus budget `margin`
then lowers the grid threshold and contains the random-point bad event.
This is exactly the reduction needed before invoking a fixed-parameter law. -/
theorem randomSpectralPairBadEvent_subset_fixedGrid
    {Ω X ι : Type*} [PseudoMetricSpace X] {N : ℕ}
    (f : Ω → X → X → ℂ) (z : Ω → Fin N → X)
    (grid : ι → X) (snap : Ω → Fin N → ι)
    (threshold : Fin N → Fin N → ℝ) (gridThreshold radius margin : ℝ)
    (hclose : ∀ ω i, dist (z ω i) (grid (snap ω i)) ≤ radius)
    (hmod : ∀ ω, HasTwoResolventGridModulus (f ω) (fun _ => margin))
    (hbudget : ∀ i j, gridThreshold + margin ≤ threshold i j) :
    randomSpectralPairBadEvent f z threshold ⊆
      fixedTwoResolventGridBadEvent f grid gridThreshold := by
  intro ω hω
  rcases hω with ⟨i, j, hij⟩
  refine ⟨snap ω i, snap ω j, ?_⟩
  have hdiff := hmod ω (hclose ω i) (hclose ω j)
  have hnorm := norm_le_norm_add_norm_sub'
    (f ω (z ω i) (z ω j))
    (f ω (grid (snap ω i)) (grid (snap ω j)))
  calc
    gridThreshold ≤ threshold i j - margin := by linarith [hbudget i j]
    _ ≤ ‖f ω (z ω i) (z ω j)‖ - margin := by linarith
    _ ≤ ‖f ω (grid (snap ω i)) (grid (snap ω j))‖ := by
      linarith [hdiff, hnorm]

/-- The generic random-point event specialized to the CEH points
`λ_i + i N^ξ η_f(λ_i)`.  The eigenvalues may be random; the spacing function
and the observable remain fixed exactly as in the CEH application. -/
def localETHTwoResolventRandomBadEvent {Ω : Type*} {N : ℕ}
    (f : Ω → ℂ → ℂ → ℂ) (etaF : ℝ → ℝ) (ξ : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ) : Set Ω :=
  randomSpectralPairBadEvent f
    (fun ω i =>
      CEHNative.BlockBand.localETHSpectralPoint
        N etaF ξ (lam ω i)) threshold

/-- CEH-facing form of the grid inclusion.  It performs no probabilistic
step: after a deterministic snapping map and a continuity budget are supplied,
every failure at random CEH spectral points already fails on the fixed grid. -/
theorem localETHTwoResolventRandomBadEvent_subset_fixedGrid
    {Ω ι : Type*} {N : ℕ}
    (f : Ω → ℂ → ℂ → ℂ) (etaF : ℝ → ℝ) (ξ : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ)
    (grid : ι → ℂ) (snap : Ω → Fin N → ι)
    (gridThreshold radius margin : ℝ)
    (hclose : ∀ ω i,
      dist (CEHNative.BlockBand.localETHSpectralPoint
          N etaF ξ (lam ω i)) (grid (snap ω i)) ≤ radius)
    (hmod : ∀ ω, HasTwoResolventGridModulus (f ω) (fun _ => margin))
    (hbudget : ∀ i j, gridThreshold + margin ≤ threshold i j) :
    localETHTwoResolventRandomBadEvent f etaF ξ lam threshold ⊆
      fixedTwoResolventGridBadEvent f grid gridThreshold :=
  randomSpectralPairBadEvent_subset_fixedGrid
    f _ grid snap threshold gridThreshold radius margin hclose hmod hbudget

/-- Fully concrete CEH grid passage for the Hermitian two-resolvent
observable.  The grid has `meshCount + 1` points, is lifted at the exact
heights `N^ξ η_f`, and the displayed margin is the proved resolvent modulus
`2 radius eta⁻³ ‖A‖`.  The only hypotheses are deterministic window,
spacing-modulus, height, and Hermiticity facts; no two-resolvent law,
probability bound, snapping map, or continuity hypothesis is assumed. -/
theorem localETHTwoResolventRandomBadEvent_subset_concreteGrid
    {Ω : Type*} {N meshCount : ℕ} (hN : 0 < N)
    (H : Ω → Matrix (Fin N) (Fin N) ℂ)
    (hH : ∀ ω, (H ω).IsHermitian)
    (c₁ c₂ : AdjointChoice) (A : Matrix (Fin N) (Fin N) ℂ)
    (etaF : ℝ → ℝ) (ξ E₀ R L eta : ℝ)
    (hR : 0 < R) (hm : 0 < meshCount) (hL : 0 ≤ L) (heta : 0 < eta)
    (hetaMod : ∀ x ∈ Set.Icc (E₀ - R) (E₀ + R),
      ∀ y ∈ Set.Icc (E₀ - R) (E₀ + R),
        |etaF x - etaF y| ≤ L * |x - y|)
    (hheight : ∀ x ∈ Set.Icc (E₀ - R) (E₀ + R),
      eta ≤ (N : ℝ) ^ ξ * etaF x)
    (lam : Ω → Fin N → ℝ)
    (hlam : ∀ ω i, lam ω i ∈ Set.Icc (E₀ - R) (E₀ + R))
    (threshold : Fin N → Fin N → ℝ) (gridThreshold : ℝ)
    (hbudget : ∀ i j,
      gridThreshold +
          2 * ((1 + (N : ℝ) ^ ξ * L) * (2 * R / meshCount)) *
            eta⁻¹ ^ 3 * ‖A‖ ≤ threshold i j) :
    localETHTwoResolventRandomBadEvent
        (fun ω z₁ z₂ =>
          twoResolventObservable c₁ c₂
            (cehHermitianResolvent (H ω) z₁) A
            (cehHermitianResolvent (H ω) z₂))
        etaF ξ lam threshold ⊆
      fixedTwoResolventGridBadEvent
        (fun ω z₁ z₂ =>
          twoResolventObservable c₁ c₂
            (cehHermitianResolvent (H ω) z₁) A
            (cehHermitianResolvent (H ω) z₂))
        (localETHSpectralGridPoint N etaF ξ E₀ R meshCount)
        gridThreshold := by
  intro ω hω
  rcases hω with ⟨i, j, hij⟩
  obtain ⟨a, ha⟩ := exists_localETHSpectralGridPoint_near
    hN hR hm hL (hlam ω i) (hetaMod _ (hlam ω i))
  obtain ⟨b, hb⟩ := exists_localETHSpectralGridPoint_near
    hN hR hm hL (hlam ω j) (hetaMod _ (hlam ω j))
  refine ⟨a, b, ?_⟩
  have hspecHeight (x : ℝ) (hx : x ∈ Set.Icc (E₀ - R) (E₀ + R)) :
      eta ≤
        |(CEHNative.BlockBand.localETHSpectralPoint
          N etaF ξ x).im| := by
    have hh := hheight x hx
    have hp : 0 < (N : ℝ) ^ ξ * etaF x := heta.trans_le hh
    simpa [CEHNative.BlockBand.localETHSpectralPoint,
      abs_of_pos hp] using hh
  have hdiff :=
    norm_twoResolventObservable_cehHermitianResolvent_sub_le
      hN (H ω) (hH ω) c₁ c₂ A heta
      (hspecHeight _ (hlam ω i))
      (hspecHeight _ (localETHRealGridPoint_mem_Icc hR.le hm a))
      (hspecHeight _ (hlam ω j))
      (hspecHeight _ (localETHRealGridPoint_mem_Icc hR.le hm b))
      ha hb
  have hdiff' :
      ‖twoResolventObservable c₁ c₂
          (cehHermitianResolvent (H ω)
            (CEHNative.BlockBand.localETHSpectralPoint
              N etaF ξ (lam ω i))) A
          (cehHermitianResolvent (H ω)
            (CEHNative.BlockBand.localETHSpectralPoint
              N etaF ξ (lam ω j))) -
        twoResolventObservable c₁ c₂
          (cehHermitianResolvent (H ω)
            (localETHSpectralGridPoint N etaF ξ E₀ R meshCount a)) A
          (cehHermitianResolvent (H ω)
            (localETHSpectralGridPoint N etaF ξ E₀ R meshCount b))‖ ≤
        2 * ((1 + (N : ℝ) ^ ξ * L) * (2 * R / meshCount)) *
          eta⁻¹ ^ 3 * ‖A‖ := by
    simpa [localETHSpectralGridPoint] using hdiff
  have hnorm := norm_le_norm_add_norm_sub'
    (twoResolventObservable c₁ c₂
      (cehHermitianResolvent (H ω)
        (CEHNative.BlockBand.localETHSpectralPoint
          N etaF ξ (lam ω i))) A
      (cehHermitianResolvent (H ω)
        (CEHNative.BlockBand.localETHSpectralPoint
          N etaF ξ (lam ω j))))
    (twoResolventObservable c₁ c₂
      (cehHermitianResolvent (H ω)
        (localETHSpectralGridPoint N etaF ξ E₀ R meshCount a)) A
      (cehHermitianResolvent (H ω)
        (localETHSpectralGridPoint N etaF ξ E₀ R meshCount b)))
  calc
    gridThreshold ≤ threshold i j -
        2 * ((1 + (N : ℝ) ^ ξ * L) * (2 * R / meshCount)) *
          eta⁻¹ ^ 3 * ‖A‖ := by linarith [hbudget i j]
    _ ≤ ‖twoResolventObservable c₁ c₂
        (cehHermitianResolvent (H ω)
          (CEHNative.BlockBand.localETHSpectralPoint
            N etaF ξ (lam ω i))) A
        (cehHermitianResolvent (H ω)
          (CEHNative.BlockBand.localETHSpectralPoint
            N etaF ξ (lam ω j)))‖ -
        2 * ((1 + (N : ℝ) ^ ξ * L) * (2 * R / meshCount)) *
          eta⁻¹ ^ 3 * ‖A‖ := by linarith
    _ ≤ ‖twoResolventObservable c₁ c₂
        (cehHermitianResolvent (H ω)
          (localETHSpectralGridPoint N etaF ξ E₀ R meshCount a)) A
        (cehHermitianResolvent (H ω)
          (localETHSpectralGridPoint N etaF ξ E₀ R meshCount b))‖ := by
      linarith [hdiff', hnorm]

/-- Failure of at least one event indexed by an ordered pair. -/
def orderedPairBadEvent {Ω : Type*} (N : ℕ)
    (bad : Fin N → Fin N → Set Ω) : Set Ω :=
  ⋃ i, ⋃ j, bad i j

/-- The exact finite union bound over `N^2` ordered pairs. -/
theorem measureReal_orderedPairBadEvent_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (bad : Fin N → Fin N → Set Ω) :
    μ.real (orderedPairBadEvent N bad) ≤
      ∑ i : Fin N, ∑ j : Fin N, μ.real (bad i j) := by
  unfold orderedPairBadEvent
  exact (measureReal_iUnion_fintype_le (μ := μ) _).trans
    (Finset.sum_le_sum fun i _ => measureReal_iUnion_fintype_le (μ := μ) _)

/-- Uniform pointwise tails cost exactly the cardinality `N^2`. -/
theorem measureReal_orderedPairBadEvent_le_sq_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (N : ℕ)
    (bad : Fin N → Fin N → Set Ω) (p : ℝ)
    (hbad : ∀ i j, μ.real (bad i j) ≤ p) :
    μ.real (orderedPairBadEvent N bad) ≤ (N ^ 2 : ℕ) * p := by
  refine (measureReal_orderedPairBadEvent_le_sum μ N bad).trans ?_
  calc
    (∑ i : Fin N, ∑ j : Fin N, μ.real (bad i j)) ≤
        ∑ _i : Fin N, ∑ _j : Fin N, p := by
      gcongr with i j
      exact hbad i j
    _ = (N ^ 2 : ℕ) * p := by
      simp [pow_two, mul_assoc]

/-- Pairwise form of the CEH spectral-point bad event. -/
def localETHTwoResolventPairBadEvent {Ω : Type*} {N : ℕ}
    (f : Ω → ℂ → ℂ → ℂ) (etaF : ℝ → ℝ) (ξ : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ)
    (i j : Fin N) : Set Ω :=
  {ω | threshold i j ≤
    ‖f ω
      (CEHNative.BlockBand.localETHSpectralPoint
        N etaF ξ (lam ω i))
      (CEHNative.BlockBand.localETHSpectralPoint
        N etaF ξ (lam ω j))‖}

/-- The CEH simultaneous event is the union over all `N^2`
ordered eigenvalue pairs. -/
theorem localETHTwoResolventRandomBadEvent_eq_orderedPairBadEvent
    {Ω : Type*} {N : ℕ}
    (f : Ω → ℂ → ℂ → ℂ) (etaF : ℝ → ℝ) (ξ : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ) :
    localETHTwoResolventRandomBadEvent f etaF ξ lam threshold =
      orderedPairBadEvent N
        (localETHTwoResolventPairBadEvent f etaF ξ lam threshold) := by
  ext ω
  simp [localETHTwoResolventRandomBadEvent, randomSpectralPairBadEvent,
    orderedPairBadEvent, localETHTwoResolventPairBadEvent]

/-- Fixed-pair tail bounds at the CEH random spectral points union-bound with
the exact `N^2` cost.  This theorem does not provide those fixed-pair bounds. -/
theorem measureReal_localETHTwoResolventRandomBadEvent_le_sq_mul
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {N : ℕ}
    (f : Ω → ℂ → ℂ → ℂ) (etaF : ℝ → ℝ) (ξ : ℝ)
    (lam : Ω → Fin N → ℝ) (threshold : Fin N → Fin N → ℝ) (p : ℝ)
    (hpair : ∀ i j,
      μ.real (localETHTwoResolventPairBadEvent
        f etaF ξ lam threshold i j) ≤ p) :
    μ.real (localETHTwoResolventRandomBadEvent
      f etaF ξ lam threshold) ≤ (N ^ 2 : ℕ) * p := by
  rw [localETHTwoResolventRandomBadEvent_eq_orderedPairBadEvent]
  exact measureReal_orderedPairBadEvent_le_sq_mul μ N _ p hpair

end CEHNative.BlockBand.External.CEH
